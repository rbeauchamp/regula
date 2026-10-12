/-
Mutation: a theorem that rests on the `native_decide` axiom of an imported `module` file, whose
generated prefix is the module-private form of the theorem's name. It must be reported as
compiler-trusting, not as an unknown axiom.

-/
import Fixtures.Mutations.ModuleNativeProof

theorem fixtures_imported_module_native_proof : (List.range 101).sum = 5050 :=
  fixtures_module_native_proof
