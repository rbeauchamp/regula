/-
Mutation: a theorem that rests on a `bv_decide` axiom of an imported module. It must be
reported as compiler-trusting, not as an unknown axiom, and rejected on a standard-logical
surface.

-/
import Fixtures.Mutations.BvDecideProof

theorem fixtures_imported_bv_decide_proof (x y : BitVec 8) : x * y = y * x :=
  fixtures_bv_decide_proof x y
