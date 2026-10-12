/-
Mutation: a theorem that rests on the `native_decide` axiom of `ModuleNativeProof` where another
imported module declares a constant named by the axiom's private prefix. The prefix's record
must be the declaration of the axiom's own module, so the theorem must still be reported as
compiler-trusting, not as an unknown axiom.

-/
import Fixtures.Mutations.ForeignPrivatePrefix

theorem fixtures_imported_foreign_private_prefix : (List.range 101).sum = 5050 :=
  fixtures_module_native_proof
