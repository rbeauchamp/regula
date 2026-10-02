/-
Known checker limit, tracked by issue #188
(https://github.com/rbeauchamp/regula/issues/188), not a forgery and not
intended behaviour. Both definitions are safe, Lean accepts them by
well-founded recursion, and each helper is exactly what Lean generated. The
rejection this fixture expects is a false rejection. Invert the expectation
(both helpers admitted) when issue #188 is fixed.

The helper is rejected when the reducibility in force at the end of the audit
differs from the reducibility in force where Lean elaborated the definition,
so that the regeneration passes the recursive-call function through a `match`
differently. Lean's `MatcherApp.addArg` decides that threading by `isDefEq` on
the function's refined type, which holds the measure. Standard §7.4 states the
limit. Both forms are observed rejections on Lean 4.34.0.

* An attribute local to the definition's section.
  `fixtures_local_irreducible` is measured through `fixtures_second`, which
  ignores its first argument and is `irreducible` only inside the section.
  There Lean cannot see that the measure ignores `a`, so it passes the function
  through the `match` on `a`. At the end of the module `fixtures_second`
  unfolds and the regeneration does not.
* A global attribute applied after the definition. `fixtures_later_irreducible`
  is measured through `fixtures_later_second`, which unfolds where the
  definition is elaborated, so Lean does not pass the function through the
  `match` on `a`. `fixtures_later_second` is made `irreducible` afterwards and
  the regeneration does.
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

def fixtures_later_second (_ n : Nat) : Nat := n

def fixtures_later_irreducible (a n : Nat) : Nat :=
  match a with
  | 0 =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_later_irreducible 1 k
  | a' + 1 =>
    match n with
    | 0 => a' + 1
    | k + 1 => fixtures_later_irreducible (a' + 2) k
termination_by fixtures_later_second a n
decreasing_by all_goals exact Nat.lt_succ_self _

attribute [irreducible] fixtures_later_second
