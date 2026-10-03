/-
Positive control (issue #210): recursive definitions whose type is a
proposition. Lean compiles a helper for each, as for any `def`, and states no
unfolding theorem for them: it leaves `eq_def` out where the definition's type
is a proposition, under structural and under well-founded recursion alike.

Each helper is admitted on the recursion equation the checker states itself,
`f n = body`, whose two sides are proofs of one proposition: Lean's kernel
accepts `Eq.refl (f n)` for it by proof irrelevance, so no theorem of Lean's
is needed. Lean's code generator erases a proof, so the equation says as much
about the helper's result as the compiled code has.
-/

set_option linter.defProp false in
def fixtures_proof_structural : (n : Nat) → 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (fixtures_proof_structural n)

set_option linter.defProp false in
def fixtures_proof_measured (n : Nat) : 0 + n = n :=
  if h : n = 0 then by omega else
    have _ := fixtures_proof_measured (n - 1)
    by omega
termination_by n
decreasing_by omega
