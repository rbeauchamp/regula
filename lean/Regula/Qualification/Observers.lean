import Regula.Checker.Lake
import Regula.Removal
import Regula.TaskManagerCheck

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
`Regula.TaskManagerCheck.refusal`). -/

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

/-- Import the environment of the root module `root`, and check it as `checkProgram` checks a
program (`Regula.Removal.rawRemovals`), and as `Regula.TaskManagerCheck.checkProgram` checks a
compiled one (`Regula.TaskManagerCheck.refusal`). -/
def checkOutside (root : Name) : IO Unit := do
  let env ← importModules #[{ module := root }] {} 0
  let reach := Regula.Removal.rawRemovals env root
  if let some refused := Regula.Removal.programRefusal env root reach then
    throw <| IO.userError s!"observers: {refused}"
  if let some refused := Regula.TaskManagerCheck.refusal env root then
    throw <| IO.userError s!"observers: {refused}"

/-- Refuse unless every program of the root package is recorded as checked, each compiled one by
the task-manager check too, and check each root module outside every library. -/
def check : IO Unit := do
  let repo ← Regula.Checker.repoRoot
  let inventory ← Regula.Checker.Lake.rootSurfaceInventory repo
  Regula.Checker.initializeLeanSearchPath
  let inLibraries := (inventory.libraries.filter (·.library != fixtures)).flatMap (·.modules)
  let outside := (inventory.executables.map (·.root)).filter (!inLibraries.contains ·)
  let compiled := inventory.executables.map (·.root)
  let mut programs := compiled
  let mut records : Std.HashSet Name := {}
  let mut taskRecords : Std.HashSet Name := {}
  for module in inLibraries do
    -- Every part of a `module` file, whose exported part omits a constant it does not export.
    let names := (← Regula.Checker.readModuleCensus (← findOLean module)).2.map (·.name)
    if names.contains `main && !programs.contains module then
      programs := programs.push module
    records := records.insertMany (recordedBy Regula.Removal.reached names)
    taskRecords := taskRecords.insertMany (recordedBy Regula.TaskManagerCheck.checked names)
  for root in outside do
    checkOutside root
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
  for program in programs do
    let task := if compiled.contains program then ", task-manager check recorded" else ""
    IO.println s!"observers: {program}: removal check recorded{task}"
  IO.println s!"observers: PASS ({programs.size} programs, {compiled.size} compiled)"

end Regula.Qualification.Observers
