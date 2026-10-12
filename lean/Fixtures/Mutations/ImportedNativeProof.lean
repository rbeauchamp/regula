/-
Mutation: a theorem that rests on a `native_decide` axiom of an imported module. The
axiom's name is one Lean generates under a declaration of its own module and its statement
replays true natively, so it must be reported as compiler-trusting, not as an unknown
axiom, and rejected on a standard-logical surface.

-/
import Fixtures.Mutations.NativeProof

theorem fixtures_imported_native_proof : (List.range 1001).sum = 500500 :=
  fixtures_native_proof
