import Regula.Checker.Lake
import Regula.Removal

/-! # The removal check of every program of the package

Each program of the package runs the check that every removal its compiled code reaches goes
through the filesystem observer (`Regula.Removal.checkProgram`) when its root module, or a module
that imports it, is built, and the module records the program (`Regula.Removal.reached`). This
campaign reads the compiled modules of the root package as Lake resolves them
(`Regula.Checker.Lake.rootSurfaceInventory`) and refuses unless each program is recorded: the root
module of each executable, and each module of a library that declares `main`, which a script runs
with `lean --run`. The `Fixtures` library is not read: it holds the inputs of the checker's
controls, which no script runs and the acceptance build does not build.

A root module outside every library, which no library module can import (`auditApp`'s `Main`), is
checked here: its environment is imported and checked as `checkProgram` checks it
(`Regula.Removal.rawRemovals`, `Regula.Removal.programRefusal`).

It prints, for each program, the number of its writes that are not yet routed through the
observer (`Regula.Removal.pendingWrites`). -/

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

/-- The number that the record `info` holds, when it is a definition whose value is a numeral,
`OfNat.ofNat` of a natural number literal, as `checkProgram` adds it (`mkNatLit`). -/
def recordValue : ConstantInfo → Option Nat
  | .defnInfo { value, .. } => value.nat?
  | _ => none

/-- Import the environment of the root module `root`, check it as `checkProgram` checks a program
(`Regula.Removal.rawRemovals`), and give the number of its writes outside the observer. -/
def checkOutside (root : Name) : IO Nat := do
  let env ← importModules #[{ module := root }] {} 0
  let reach := Regula.Removal.rawRemovals env root
  if let some refused := Regula.Removal.programRefusal root reach then
    throw <| IO.userError s!"observers: {refused}"
  return (← Regula.Removal.pendingWrites env reach).size

/-- Refuse unless every program of the root package is recorded as checked, and check each root
module outside every library; print the writes outside the observer of each program. -/
def check : IO Unit := do
  let repo ← Regula.Checker.repoRoot
  let inventory ← Regula.Checker.Lake.rootSurfaceInventory repo
  Regula.Checker.initializeLeanSearchPath
  let inLibraries := (inventory.libraries.filter (·.library != fixtures)).flatMap (·.modules)
  let outside := (inventory.executables.map (·.root)).filter (!inLibraries.contains ·)
  let mut programs := inventory.executables.map (·.root)
  let mut records : Std.HashMap Name Nat := {}
  for module in inLibraries do
    let (data, _) ← readModuleData (← findOLean module)
    if data.constNames.contains `main && !programs.contains module then
      programs := programs.push module
    for info in data.constants do
      if Regula.Removal.reached.isPrefixOf info.name && info.name != Regula.Removal.reached then
        let some count := recordValue info
          | throw <| IO.userError s!"observers: the record {info.name} in {module} is not a \
              count"
        records := records.insert (info.name.replacePrefix Regula.Removal.reached .anonymous)
          count
  for root in outside do
    records := records.insert root (← checkOutside root)
  let missing := unrecorded programs records.contains
  unless missing.isEmpty do
    throw <| IO.userError s!"observers: no module records the removal check of the programs \
      {missing.toList}: each runs `Regula.Removal.checkProgram` in its root module or in a \
      module that imports it"
  for program in programs do
    IO.println s!"observers: {program}: removal check recorded; \
      {records.getD program 0} writes outside the observer"
  IO.println s!"observers: PASS ({programs.size} programs)"

end Regula.Qualification.Observers
