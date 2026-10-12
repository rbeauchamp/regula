/-
Mutation: a theorem that rests on a `decide +native` axiom of an imported module. It must
be reported as compiler-trusting, not as an unknown axiom, and rejected on a
standard-logical surface.

-/
import Fixtures.Mutations.DecideNativeProof

theorem fixtures_imported_decide_native_proof : (List.range 1001).sum = 500500 :=
  fixtures_decide_native_proof
