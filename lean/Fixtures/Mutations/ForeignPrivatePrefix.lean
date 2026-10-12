/-
Mutation: a module that adds a theorem under the module-private form of the name of a theorem
of `ModuleNativeProof`, the prefix of that theorem's generated native-proof axiom. The added
theorem is of this module, not of the axiom's; `ImportedForeignPrivatePrefix` imports it.

-/
import Fixtures.Mutations.ModuleNativeProof
import Lean

open Lean Elab Command in
run_cmd liftCoreM <| addDecl (.thmDecl {
  name := mkPrivateNameCore `Fixtures.Mutations.ModuleNativeProof `fixtures_module_native_proof
  levelParams := []
  type := mkConst ``True
  value := mkConst ``True.intro
  all := [mkPrivateNameCore `Fixtures.Mutations.ModuleNativeProof `fixtures_module_native_proof] })
