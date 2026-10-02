/-
Positive control (issue #188) at the compiler boundary: safe recursive
definitions for which the reducibility in force at the end of the audit
differs from the reducibility in force where Lean elaborated them. Lean
accepts each, and each helper is exactly what Lean generated. Lean does not
record the reducibility a definition was elaborated under, so the checker
regenerates in the environment it inspects, and where that reproduces nothing
again with no definition irreducible, and compares a `match` that passes a
variable through as the `match` that uses the variable directly.

Lean's recursion compilers pass the function that stands for the recursive
calls through a `match` where an alternative changes that function's type,
which holds the measure. `MatcherApp.addArg` decides that by `isDefEq` on the
refined type, so the answer depends on what unfolds.

- `fixtures_local_irreducible` is measured through `fixtures_second`, which
  ignores its first argument and is `irreducible` only inside the section.
  There Lean cannot see that the measure ignores `a` and passes the function
  through the `match` on `a`; at the end of the module `fixtures_second`
  unfolds and the regeneration does not.
- `fixtures_later_irreducible` is the other direction: `fixtures_later_second`
  unfolds where the definition is elaborated and is made `irreducible`
  afterwards, so the regeneration passes the function through a `match` Lean
  did not.
- `fixtures_unsealed` is measured through a function that is `irreducible`
  from its declaration and unsealed for the definition alone.
- `fixtures_alias_sum` recurses structurally on an argument whose type is a
  definition made `irreducible` afterwards. In the inspected environment Lean
  no longer sees the inductive type behind it, and the regeneration with no
  definition irreducible reproduces the base.
- `fixtures_remaining_call` applies a `match` to a recursive call. Lean
  compiles it only where it does not pass the function through that `match`;
  with `fixtures_remaining_second` `irreducible` at the end of the module, its
  own compiler rejects the definition, and the regeneration with no definition
  irreducible reproduces the base.

`fixtures_match_passes_variable` states, for the `match` on `a` above, the law
the comparison applies: passing a variable through the `match` and binding it
in each alternative equals using it directly, for every result type, pair of
alternatives and variable. The kernel checks it for this `match`; that it
holds of every matcher is argued in standard §7.4, not proved.
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

@[irreducible] def fixtures_sealed_second (_ n : Nat) : Nat := n

unseal fixtures_sealed_second in
def fixtures_unsealed (a n : Nat) : Nat :=
  match a with
  | 0 =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_unsealed 1 k
  | a' + 1 =>
    match n with
    | 0 => a' + 1
    | k + 1 => fixtures_unsealed (a' + 2) k
termination_by fixtures_sealed_second a n
decreasing_by all_goals exact Nat.lt_succ_self _

def FixturesAlias := List Nat

def fixtures_alias_sum (xs : FixturesAlias) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => x + fixtures_alias_sum rest

attribute [irreducible] FixturesAlias

def fixtures_remaining_second (_ n : Nat) : Nat := n

def fixtures_remaining_call (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 =>
    (match a with
     | 0 => fun (x : Nat) => x
     | _ + 1 => fun (x : Nat) => x + 1) (fixtures_remaining_call (a + 1) k)
termination_by fixtures_remaining_second a n
decreasing_by all_goals exact Nat.lt_succ_self _

attribute [irreducible] fixtures_remaining_second

theorem fixtures_match_passes_variable {T : Sort u} {R : Nat → Sort v} (a : Nat) (passed : T)
    (zero : T → R 0) (succ : (a' : Nat) → T → R (a' + 1)) :
    (match (motive := (a : Nat) → T → R a) a with
      | 0 => fun bound => zero bound
      | a' + 1 => fun bound => succ a' bound) passed
    = (match (motive := (a : Nat) → R a) a with
      | 0 => zero passed
      | a' + 1 => succ a' passed) := by
  cases a <;> rfl
