/-
Positive control (issue #188) at the compiler boundary: safe recursive
definitions for which the reducibility in force at the end of the audit
differs from the reducibility in force where Lean elaborated them. Lean
accepts each, and each helper is exactly what Lean generated. Lean does not
record the reducibility a definition was elaborated under, so the checker
regenerates in the environment it inspects, and where that reproduces nothing
again with no definition irreducible, and compares a `match` that passes a
variable through as the `match` that uses the variable directly, where the
kernel checks that the two are equal for that matcher.

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
- `fixtures_alias_binary` has a type that is a definition made `irreducible`
  afterwards and recurses on its second argument, selected by
  `termination_by structural`. The inspected environment shows no parameter in
  its type, and with no definition irreducible Lean's automatic choice takes
  the first argument, so the base is reproduced only on the position Lean
  recorded, read against the parameters its helper binds (found in review).
- `fixtures_abbrev_irreducible` passes a parameter through an `abbrev`, so Lean
  finds the parameter fixed, and the `abbrev` is made `irreducible` afterwards
  (which needs `allowUnsafeReducibility`). The regeneration with no definition
  irreducible gives an `abbrev` back its `reducible` status, read from the
  kernel's reducibility hint (found in review).
- `fixtures_cases_on_irreducible`, `fixtures_overlapping_irreducible`,
  `fixtures_equation_irreducible` and `fixtures_literal_irreducible` are
  `fixtures_local_irreducible` over other eliminators: a `casesOn` applied
  directly, two discriminants with overlapping alternatives, a `match` that
  names the equation with its discriminant, and numeric literals. The kernel
  check of the two forms has to succeed for each kind.
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

def FixturesBinary := Nat → Nat → Nat

def fixtures_alias_binary : FixturesBinary
  | a, 0 => a
  | 0, b => b
  | a + 1, b + 1 => fixtures_alias_binary a b + 1
termination_by structural _ b => b

attribute [irreducible] FixturesBinary

abbrev fixtures_abbrev_keep (a : Nat) : Nat := a

def fixtures_abbrev_irreducible (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_abbrev_irreducible (fixtures_abbrev_keep a) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [irreducible] fixtures_abbrev_keep

def fixtures_last (_ _ n : Nat) : Nat := n

theorem fixtures_last_eq (a b n : Nat) : fixtures_last a b n = n := rfl

def fixtures_last_option (_ : Option Nat) (n : Nat) : Nat := n

theorem fixtures_last_option_eq (o : Option Nat) (n : Nat) : fixtures_last_option o n = n := rfl

section
attribute [local irreducible] fixtures_last fixtures_last_option

def fixtures_cases_on_irreducible (a b n : Nat) : Nat :=
  Nat.casesOn (motive := fun _ => Nat) a
    (match n with
     | 0 => b
     | k + 1 => fixtures_cases_on_irreducible 1 b k)
    (fun a' =>
      match n with
      | 0 => a' + 1
      | k + 1 => fixtures_cases_on_irreducible (a' + 2) b k)
termination_by fixtures_last a b n
decreasing_by all_goals (simp only [fixtures_last_eq]; exact Nat.lt_succ_self _)

def fixtures_overlapping_irreducible (a b n : Nat) : Nat :=
  match a, b with
  | 0, _ =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_overlapping_irreducible 1 b k
  | _, 0 =>
    match n with
    | 0 => 1
    | k + 1 => fixtures_overlapping_irreducible a 1 k
  | a' + 1, b' + 1 =>
    match n with
    | 0 => a' + b'
    | k + 1 => fixtures_overlapping_irreducible a' b' k
termination_by fixtures_last a b n
decreasing_by all_goals (simp only [fixtures_last_eq]; exact Nat.lt_succ_self _)

def fixtures_equation_irreducible (o : Option Nat) (n : Nat) : Nat :=
  match _h : o with
  | none =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_equation_irreducible (some k) k
  | some x =>
    match n with
    | 0 => x
    | k + 1 => fixtures_equation_irreducible none k
termination_by fixtures_last_option o n
decreasing_by all_goals (simp only [fixtures_last_option_eq]; exact Nat.lt_succ_self _)

def fixtures_literal_irreducible (a b n : Nat) : Nat :=
  match a with
  | 5 =>
    match n with
    | 0 => b
    | k + 1 => fixtures_literal_irreducible 7 b k
  | 7 =>
    match n with
    | 0 => b + 1
    | k + 1 => fixtures_literal_irreducible 0 b k
  | _ =>
    match n with
    | 0 => a
    | k + 1 => fixtures_literal_irreducible 5 b k
termination_by fixtures_last a b n
decreasing_by all_goals (simp only [fixtures_last_eq]; exact Nat.lt_succ_self _)
end
