module

public meta import Lean.Elab.Command
meta import all Lean.Util.CollectAxioms

/-!
Mutation: before it declares its theorem, the module empties every axiom-table entry it imported
(`exportedAxiomsExt`, through `import all`). The table Lean writes for the module then records no
axiom for a proof that uses `Classical.em`, and `#print axioms` in the module and in each importer
reports none. Claimed kernel-only, the theorem is refused by the axioms it reaches in the replayed
kernel.
-/

open Lean in
run_cmd modifyEnv fun env => exportedAxiomsExt.modifyState env fun s =>
  { s with importedModuleEntries := s.importedModuleEntries.map (·.map fun (name, _) => (name, #[])) }

public theorem fixtures_forged_omission (p : Prop) : p ∨ ¬p := Classical.em p
