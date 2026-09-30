/-
Mutation (issue #125): a project `wf_preprocess` rule that removes a recursive
call. Lean compiles `fixtures_dropped` to a base that never recurses
(`fun n => 0`, no axioms), while its generated helper, which the compiled code
runs, still makes the call and recurses without bound. The helper is exactly
what Lean generates, but the regeneration uses only the toolchain's own
`wf_preprocess` rules, so it keeps the call, does not reproduce the base, and
the helper is not admitted.
-/
def fixtures_keep_first (a b : Nat) : Nat := if b < 0 then b else a

@[wf_preprocess] theorem fixtures_keep_first_eq (a b : Nat) :
    fixtures_keep_first a b = a := by
  unfold fixtures_keep_first
  exact ite_eq_right (Nat.not_lt_zero b)

def fixtures_dropped (n : Nat) : Nat := fixtures_keep_first 0 (fixtures_dropped (n + 1))
termination_by n
