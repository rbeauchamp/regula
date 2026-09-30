/-
Mutation (issue #125): a recursive definition whose decreasing proof rests on a
project axiom. Its helper is exactly what Lean generates, but exact match elides
decreasing proofs and relies on the base's own kernel-checked ones, so a base
whose axioms leave Standard-Logical does not admit its helper.
-/
axiom fixtures_shrinks : ∀ n : Nat, n + 1 < n

def fixtures_axiom_loop (n : Nat) : Nat := fixtures_axiom_loop (n + 1)
termination_by n
decreasing_by exact fixtures_shrinks n
