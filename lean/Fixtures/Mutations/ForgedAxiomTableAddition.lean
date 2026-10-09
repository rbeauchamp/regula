module

public meta import Lean.Elab.Command
meta import all Lean.Util.CollectAxioms

/-!
Mutation: before it declares its definition, the module adds `propext` to every axiom-table entry
it imported (`exportedAxiomsExt`, through `import all`). The table Lean writes for the module then
records `propext` for a definition that reaches no axiom in the replayed kernel, so admission
refuses the table as one not computed from the constants the kernel checked.
-/

open Lean in
run_cmd modifyEnv fun env => exportedAxiomsExt.modifyState env fun s =>
  { s with importedModuleEntries :=
      s.importedModuleEntries.map (·.map fun (name, axioms) => (name, axioms.push ``propext)) }

public def fixtures_forged_addition : Nat := Nat.succ 0
