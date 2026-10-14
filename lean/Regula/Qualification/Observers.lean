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

The guard starts a program again under Git isolation only in the executable that Lake builds for it
(`Regula.GitIsolation.runsAs`), which it finds by the string literal that `main` passes to it. So
this campaign also refuses an executable whose literal (`Regula.TaskManagerCheck.named`) names
another file than the one that Lake's loaded workspace builds for it (`misnamed`), or the file of a
program in the binary directory of the pinned toolchain (`toolchainNamed`). The executables
of the `website` and `markdown` packages are outside this inventory, and no check compares their
literals: a wrong one makes the program refuse without isolation, and never start again.

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

/-- The root module and the executable name of each program that the markers with the prefix
`Regula.TaskManagerCheck.named` among `names` record: each name `named ++ root ++ program`, whose
last component is the string `program`. -/
def namedBy (names : Array Name) : Array (Name × String) :=
  names.filterMap fun name =>
    if Regula.TaskManagerCheck.named.isPrefixOf name && name != Regula.TaskManagerCheck.named then
      match name.replacePrefix Regula.TaskManagerCheck.named .anonymous with
      | .str root program => some (root, program)
      | _ => none
    else none

/-- The executables of `executables`, each a root module and the file name of the binary that Lake
builds for it, whose program passes the guard an executable name (`names`) for which the guard
expects another file (`Regula.GitIsolation.executableFile`): each with that name and Lake's file
name. -/
def misnamed (executables : Array (Name × String)) (names : Name → Option String) :
    Array (Name × String × String) :=
  executables.filterMap fun (root, file) => match names root with
    | some program =>
      if Regula.GitIsolation.executableFile program == file then none
      else some (root, program, file)
    | none => none

/-- An executable is misnamed exactly when it is one of `executables`, its program passes the guard
an executable name, and the file that the guard expects for that name is not the file that Lake
builds. -/
theorem mem_misnamed_iff (executables : Array (Name × String)) (names : Name → Option String)
    (root : Name) (program file : String) :
    (root, program, file) ∈ misnamed executables names ↔
      (root, file) ∈ executables ∧ names root = some program ∧
        Regula.GitIsolation.executableFile program ≠ file := by
  simp only [misnamed, Array.mem_filterMap]
  constructor
  · rintro ⟨⟨root', file'⟩, member, found⟩
    split at found
    · rename_i program' hNames
      split at found
      · cases found
      · rename_i hFile
        cases found
        exact ⟨member, hNames, by simpa using hFile⟩
    · cases found
  · rintro ⟨member, hNames, hFile⟩
    refine ⟨(root, file), member, ?_⟩
    simp [hNames, hFile]

/-- The programs of `names`, each a root module and the executable name that its `main` passes to
the guard, for which the guard expects the file of a program of the toolchain (`programs`, the file
names of its binary directory). -/
def toolchainNamed (names : Array (Name × String)) (programs : Array String) :
    Array (Name × String) :=
  names.filter fun (_, program) => programs.contains (Regula.GitIsolation.executableFile program)

/-- A program is toolchain-named exactly when it is one of `names` and the file that the guard
expects for its executable name is one of `programs`. -/
theorem mem_toolchainNamed_iff (names : Array (Name × String)) (programs : Array String)
    (root : Name) (program : String) :
    (root, program) ∈ toolchainNamed names programs ↔
      (root, program) ∈ names ∧ Regula.GitIsolation.executableFile program ∈ programs := by
  simp [toolchainNamed, Array.mem_filter]

/-- Import the environment of the root module `root`, and check it as `checkProgram` checks a
program (`Regula.Removal.rawRemovals`), and as `Regula.TaskManagerCheck.checkProgram` checks a
compiled one (`Regula.TaskManagerCheck.refusal`). The result is the executable name that its `main`
passes to the guard, when `main` has the closed form of the guard
(`Regula.TaskManagerCheck.guarded`). -/
def checkOutside (root : Name) : IO (Option String) := do
  let env ← importModules #[{ module := root }] {} 0
  let reach := Regula.Removal.rawRemovals env root
  if let some refused := Regula.Removal.programRefusal root reach then
    throw <| IO.userError s!"observers: {refused}"
  if let some refused := Regula.TaskManagerCheck.refusal env root then
    throw <| IO.userError s!"observers: {refused}"
  return (Regula.TaskManagerCheck.guarded env).map (·.1)

/-- Refuse unless every program of the root package is recorded as checked, each compiled one by
the task-manager check too, and check each root module outside every library. Refuse an executable
whose `main` passes the guard an executable name for which the guard expects another file than the
one Lake builds for it (`misnamed`): started without isolation, that program would refuse instead
of starting again under it (`Regula.GitIsolation.runsAs`). Refuse an executable whose `main` passes
the guard the name of a program of the toolchain (`toolchainNamed`), such as `lean`, under which a
program that the Lean frontend runs would pass `runsAs`. -/
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
  let mut names : Std.HashMap Name String := {}
  for module in inLibraries do
    -- Every part of a `module` file, whose exported part omits a constant it does not export.
    let declared := (← Regula.Checker.readModuleCensus (← findOLean module)).2.map (·.name)
    if declared.contains `main && !programs.contains module then
      programs := programs.push module
    records := records.insertMany (recordedBy Regula.Removal.reached declared)
    taskRecords := taskRecords.insertMany (recordedBy Regula.TaskManagerCheck.checked declared)
    names := names.insertMany (namedBy declared)
  for root in outside do
    if let some program ← checkOutside root then names := names.insert root program
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
  -- The file name of the binary that Lake builds for each executable (`Lake.LeanExe.fileName`).
  let files ← Regula.Checker.Workspace.withRootPackage repo fun ws =>
    pure (ws.root.leanExes.map fun exe => (exe.root.name, exe.fileName.toString))
  let wrong := misnamed files names.get?
  unless wrong.isEmpty do
    let described := wrong.toList.map fun (root, program, file) =>
      s!"{root} passes \"{program}\" to the guard, which expects the file \
        `{Regula.GitIsolation.executableFile program}`, and Lake builds `{file}`"
    throw <| IO.userError s!"observers: the guard of each executable names the executable that \
      Lake builds for it, so that it can start again under Git isolation: \
      {"; ".intercalate described}"
  -- The file names of the binary directory of the pinned toolchain's installation.
  let toolchain := (← Regula.Filesystem.Construction.listDirectory
    ((← Regula.Toolchain.sysroot) / "bin")).map (·.fileName)
  let frontends := toolchainNamed names.toArray toolchain
  unless frontends.isEmpty do
    let described := frontends.toList.map fun (root, program) =>
      s!"{root} passes \"{program}\", whose file `{Regula.GitIsolation.executableFile program}` \
        is a program of the toolchain"
    throw <| IO.userError s!"observers: the guard of an executable names no program of the Lean \
      toolchain, so that a frontend such as `lean --run` never starts again as the program: \
      {"; ".intercalate described}"
  for program in programs do
    let task := if compiled.contains program then ", task-manager check recorded" else ""
    let name := match names.get? program with
      | some name => s!", guard names {name}"
      | none => ""
    IO.println s!"observers: {program}: removal check recorded{task}{name}"
  IO.println s!"observers: PASS ({programs.size} programs, {compiled.size} compiled)"

end Regula.Qualification.Observers
