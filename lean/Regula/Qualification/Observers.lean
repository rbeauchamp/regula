import Regula.Checker.Lake
import Regula.Removal
import Regula.TaskManagerCheck
import Lean.Util.FoldConsts

/-! # The removal check and the task-manager check of every program of the package

Each program of the package runs the check that every removal its compiled code reaches goes
through the filesystem observer (`Regula.Removal.checkProgram`) when its root module, or a module
that imports it, is built, and the module records the program (`Regula.Removal.reached`). Each
compiled program, the root module of an executable, also runs the check that it starts through the
guard of Lean's task manager when its compiled code needs one
(`Regula.TaskManagerCheck.checkProgram`), and the module records it
(`Regula.TaskManagerCheck.checked`). This campaign reads the compiled modules of the root package as
Lake resolves them (`Regula.Checker.Lake.rootSurfaceInventory`) and refuses unless each program is
recorded: by both checks the root module of each executable, and by the removal check each module
of a library that declares `main`, which a script runs with `lean --run`. The `lean` executable
starts its own task manager before it elaborates such a module, so that program needs no guard
(`Regula.TaskManagerCheck`). The `Fixtures` library is not read: it holds the inputs of the
checker's controls, which no script runs and the acceptance build does not build.

A root module outside every library, which no library module can import (`auditApp`'s `Main`), is
checked here: its environment is imported and checked as each `checkProgram` checks it
(`Regula.Removal.rawRemovals`, `Regula.Removal.programRefusal`,
`Regula.TaskManagerCheck.refusal`).

The campaign also refuses each declaration of these modules, and of `auditApp`'s `Main`, that
refers to `System.FilePath.readDir` or `System.FilePath.walkDir` (`readerReferences`). Lean v4.34.1
cannot tell the end of a directory from a failed read there, so each program of the package lists a
directory through `Regula.Filesystem.Construction.listNames`. The check reads the constants of each
module, not its source text. It does not follow a call into Lean's or Lake's library, so
`IO.FS.removeDirAll` and Lake's module globs still read directories with `readDir`. -/

namespace Regula.Qualification.Observers

open Lean System

/-- The programs of `programs` that `recorded` does not record. -/
def unrecorded (programs : Array Name) (recorded : Name → Bool) : Array Name :=
  programs.filter (!recorded ·)

/-- A program is unrecorded exactly when it is one of `programs` and `recorded` does not record
it. -/
theorem mem_unrecorded_iff (programs : Array Name) (recorded : Name → Bool) (program : Name) :
    program ∈ unrecorded programs recorded ↔
      program ∈ programs ∧ recorded program = false := by
  simp [unrecorded, Array.mem_filter]

/-- The library whose modules are not programs of the package. -/
def fixtures : String := "Fixtures"

/-- The names of the programs that the markers with the prefix `marker` among `names` record:
each name `marker ++ root` records the program whose root module is `root`. -/
def recordedBy (marker : Name) (names : Array Name) : Array Name :=
  names.filterMap fun name =>
    if marker.isPrefixOf name && name != marker then some (name.replacePrefix marker .anonymous)
    else none

/-- The directory readers of Lean's library that cannot tell the end of a directory from a failed
read, which no declaration of the package refers to. -/
def directoryReaders : List Name := [``System.FilePath.readDir, ``System.FilePath.walkDir]

/-- Each declaration of `constants` that refers to a directory reader, in its type or its value,
with those readers (`ConstantInfo.getUsedConstantsAsSet`, which also reads the value of a theorem
and of an opaque constant). -/
def readerReferences (constants : List ConstantInfo) : List (Name × List Name) :=
  constants.filterMap fun constant =>
    let readers := directoryReaders.filter (constant.getUsedConstantsAsSet.contains ·)
    if readers.isEmpty then none else some (constant.name, readers)

/-- No declaration is reported exactly when no declaration of `constants` refers to a directory
reader. -/
theorem readerReferences_eq_nil_iff (constants : List ConstantInfo) :
    readerReferences constants = [] ↔
      ∀ constant ∈ constants, ∀ reader ∈ directoryReaders,
        constant.getUsedConstantsAsSet.contains reader = false := by
  simp [readerReferences, List.filterMap_eq_nil_iff, List.filter_eq_nil_iff]

/-- A declaration named `name` whose value calls `reader`, or calls nothing when `reader` is `none`:
the planted declaration of the reader check's positive control, and the plain one of its negative
control. -/
def readerProbe (name : Name) (reader : Option Name) : ConstantInfo :=
  let value := match reader with
    | some reader => .app (.const reader []) (.const ``Unit.unit [])
    | none => .const ``Unit.unit []
  .defnInfo
    { name, levelParams := [], type := .const ``Unit [], value, hints := .opaque, safety := .safe }

/-- Refuse unless `readerReferences` reports a planted reference to each directory reader and
reports no declaration without one. -/
def controlReaders : IO Unit := do
  for reader in directoryReaders do
    unless readerReferences [readerProbe `planted (some reader)] == [(`planted, [reader])] do
      throw <| IO.userError s!"observers: the reader check misses a planted reference to {reader}"
  unless (readerReferences [readerProbe `plain none]).isEmpty do
    throw <| IO.userError "observers: the reader check reports a declaration with no reference"

/-- Import the environment of the root module `root`, and check it as `checkProgram` checks a
program (`Regula.Removal.rawRemovals`), and as `Regula.TaskManagerCheck.checkProgram` checks a
compiled one (`Regula.TaskManagerCheck.refusal`). -/
def checkOutside (root : Name) : IO Unit := do
  let env ← importModules #[{ module := root }] {} 0
  let reach := Regula.Removal.rawRemovals env root
  if let some refused := Regula.Removal.programRefusal root reach then
    throw <| IO.userError s!"observers: {refused}"
  if let some refused := Regula.TaskManagerCheck.refusal env root then
    throw <| IO.userError s!"observers: {refused}"

/-- Refuse unless every program of the root package is recorded as checked, each compiled one by
the task-manager check too, and check each root module outside every library. Refuse each
declaration of these modules that refers to a directory reader, after the reader check's controls
(`controlReaders`). -/
def check : IO Unit := do
  controlReaders
  let repo ← Regula.Checker.repoRoot
  let inventory ← Regula.Checker.Lake.rootSurfaceInventory repo
  Regula.Checker.initializeLeanSearchPath
  let inLibraries := (inventory.libraries.filter (·.library != fixtures)).flatMap (·.modules)
  let outside := (inventory.executables.map (·.root)).filter (!inLibraries.contains ·)
  let compiled := inventory.executables.map (·.root)
  let mut programs := compiled
  let mut records : Std.HashSet Name := {}
  let mut taskRecords : Std.HashSet Name := {}
  let mut references : Array (Name × List Name) := #[]
  let mut declarations := 0
  for module in inLibraries do
    -- Every part of a `module` file, whose exported part omits a constant it does not export.
    let constants := (← Regula.Checker.readModuleCensus (← findOLean module)).2
    let names := constants.map (·.name)
    references := references ++ (readerReferences constants.toList).toArray
    declarations := declarations + constants.size
    if names.contains `main && !programs.contains module then
      programs := programs.push module
    records := records.insertMany (recordedBy Regula.Removal.reached names)
    taskRecords := taskRecords.insertMany (recordedBy Regula.TaskManagerCheck.checked names)
  for root in outside do
    checkOutside root
    let constants := (← Regula.Checker.readModuleCensus (← findOLean root)).2
    references := references ++ (readerReferences constants.toList).toArray
    declarations := declarations + constants.size
    records := records.insert root
    taskRecords := taskRecords.insert root
  let missing := unrecorded programs records.contains
  unless missing.isEmpty do
    throw <| IO.userError s!"observers: no module records the removal check of the programs \
      {missing.toList}: each runs `Regula.Removal.checkProgram` in its root module or in a \
      module that imports it"
  let unguarded := unrecorded compiled taskRecords.contains
  unless unguarded.isEmpty do
    throw <| IO.userError s!"observers: no module records the task-manager check of the \
      compiled programs {unguarded.toList}: each runs `Regula.TaskManagerCheck.checkProgram` at \
      the end of its root module"
  unless references.isEmpty do
    throw <| IO.userError s!"observers: these declarations refer to Lean's readDir or walkDir, \
      which cannot tell the end of a directory from a failed read: {references.toList}. List a \
      directory through Regula.Filesystem.Construction.listNames, listDirectory or walkDirectory"
  for program in programs do
    let task := if compiled.contains program then ", task-manager check recorded" else ""
    IO.println s!"observers: {program}: removal check recorded{task}"
  IO.println s!"observers: no declaration refers to readDir or walkDir ({declarations} \
    declarations)"
  IO.println s!"observers: PASS ({programs.size} programs, {compiled.size} compiled)"

end Regula.Qualification.Observers
