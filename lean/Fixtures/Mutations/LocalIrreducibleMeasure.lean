/-
Checker limit (found in review of issue #183), not a forgery: a safe
definition whose compiled value depends on a reducibility attribute that is
local to the section it is compiled in. `fixtures_local_irreducible` is
measured through `fixtures_second`, which ignores its first argument and is
`irreducible` only inside the section. There Lean cannot see that the measure
ignores `a`, so it passes the recursive-call function through the `match` on
`a`. The regeneration runs at the end of the module, where `fixtures_second`
unfolds, sees that the `match` on `a` leaves the measure unchanged and does
not pass the function through it. The regenerated functional differs from the
observed one and the helper, although exactly what Lean generates, is not
admitted. Standard §7.4 lists this form.
-/
def fixtures_second (_ n : Nat) : Nat := n

theorem fixtures_second_eq (a n : Nat) : fixtures_second a n = n := rfl

section
attribute [local irreducible] fixtures_second

def fixtures_local_irreducible (a n : Nat) : Nat :=
  match a with
  | 0 =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_local_irreducible 1 k
  | a' + 1 =>
    match n with
    | 0 => a' + 1
    | k + 1 => fixtures_local_irreducible (a' + 2) k
termination_by fixtures_second a n
decreasing_by
  all_goals
    rw [fixtures_second_eq, fixtures_second_eq]
    exact Nat.lt_succ_self _
end
