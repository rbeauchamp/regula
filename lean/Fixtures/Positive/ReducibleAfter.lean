/-
Positive control (issue #196) at the compiler boundary: safe recursive
definitions that call a function whose reducibility status a later global
attribute changes. Lean accepts each, and each helper is exactly what Lean
generated.

Lean's recursion compilers take two decisions at reducible transparency, and
at implicit transparency where they compare an instance-implicit argument:
which parameters are fixed (`getFixedParamPerms`), under well-founded and
under structural recursion, and which `wf_preprocess` rule of the toolchain
rewrites the body. Lean keeps no record of the status a definition was
compiled under, so the regeneration in the environment the audit inspects, and
the one with no definition irreducible, take those decisions differently. The
checker then searches the statuses a later global attribute can have replaced,
for the definitions of the helper's module that the helper reaches, and admits
the helper under the first assignment whose regeneration equals the observed
base. Without that search `fixtures_reducible_fixed`,
`fixtures_reducible_structural`, `FixturesReducibleTree.count` and
`fixtures_reducible_then_not` were observed rejections on Lean 4.34.0; the
other forms were not run without it.

- `fixtures_reducible_fixed` passes `fixtures_reducible_keep a` for `a`. Where
  the definition is compiled that is another argument, so `a` varies and Lean
  packs it with `n`; with `fixtures_reducible_keep` reducible the regeneration
  finds `a` fixed. `fixtures_reducible_structural` is the same under structural
  recursion, whose compiler takes the same decision.
- `FixturesReducibleTree.count` maps over its children through
  `fixtures_reducible_map`. Where the definition is compiled the toolchain's
  `List.map` rule does not see through it; with `fixtures_reducible_map`
  reducible it does, and the regeneration rewrites the body.
- `fixtures_reducible_mixed` passes one parameter through
  `fixtures_reducible_declared`, `@[reducible]` from its declaration, and
  another through `fixtures_reducible_later`, made reducible afterwards.
  Nothing in the final environment tells the two functions apart, and only the
  assignment that changes the second alone reproduces the base.
- `fixtures_reducible_limit` passes each of two parameters through a function
  made reducible afterwards, and its leaf calls four functions that are
  `@[reducible]` from their declaration. Six definitions with one earlier
  status each allow 63 assignments, the most the search tries exhaustively,
  and only the one that changes the first two together reproduces the base.
  `Fixtures.Mutations.KnownLimitReducibilitySearchBound` is this shape with
  one function more.
- `fixtures_reducible_decoyed` is that pair of changes alone, beside an
  authored `fixtures_reducible_decoyed._unsafe_rec._sunfold` that mentions five
  functions `@[reducible]` from their declaration (found in review). No
  observation reads a `_sunfold` declaration, so the search does not reach
  them: two candidates, three assignments. Were it to follow that declaration,
  seven candidates would exceed the bound, the pair would never be tried and
  the helper would be undecided.
- `fixtures_reducible_proved` is that pair of changes again, with a leaf that
  cites `fixtures_proved_bound`, a theorem whose statement mentions no
  definition of this module and whose proof mentions five functions
  `@[reducible]` from their declaration (found in review). Lean unfolds a
  theorem only at `.all` transparency, where a status changes nothing, so the
  search follows no theorem's value: two candidates, three assignments.
  Following it, as the search did before, seven candidates exceeded the bound
  and the helper was undecided.
- `fixtures_reducible_then_not` is the other way round:
  `fixtures_reducible_before` is `@[reducible]` from its declaration, so Lean
  finds the parameter fixed, and is made `irreducible` afterwards, which Lean
  allows only under `allowUnsafeReducibility`.
- `fixtures_instance_later` passes `g` through a function whose instance
  argument goes through `fixtures_instance_keep`. Lean compares that argument
  at implicit transparency, where an `instance_reducible` definition unfolds:
  `g` varies where the definition is compiled and is fixed once
  `fixtures_instance_keep` is `instance_reducible`. `fixtures_implicit_later`
  is the same with `implicit_reducible`.
- `fixtures_instance_then_not` is that form the other way round:
  `fixtures_instance_before` is `instance_reducible` where the definition is
  compiled and made `irreducible` afterwards, which Lean allows without
  `allowUnsafeReducibility`.
- `fixtures_abbrev_both` passes a parameter through an `abbrev` that is
  irreducible at both points, so the parameter varies, and recurses
  structurally on an argument whose type is a definition made `irreducible`
  afterwards. In the inspected environment Lean does not see the inductive
  type, and the regeneration with no definition irreducible gives the `abbrev`
  back as `reducible` and finds the parameter fixed; the assignment that keeps
  the `abbrev` irreducible there reproduces the base.
-/
def fixtures_reducible_keep (a : Nat) : Nat := a

def fixtures_reducible_fixed (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_reducible_fixed (fixtures_reducible_keep a) k
termination_by n

def fixtures_reducible_structural (a : Nat) : List Nat → Nat
  | [] => a
  | _ :: xs => fixtures_reducible_structural (fixtures_reducible_keep a) xs

attribute [reducible] fixtures_reducible_keep

inductive FixturesReducibleTree where
  | node : List FixturesReducibleTree → FixturesReducibleTree

def fixtures_reducible_map {α β : Type} (f : α → β) (xs : List α) : List β := List.map f xs

def FixturesReducibleTree.count : FixturesReducibleTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 => 1 + (fixtures_reducible_map (fun child => child.count fuel) children).sum
termination_by _ fuel => fuel

attribute [reducible] fixtures_reducible_map

@[reducible] def fixtures_reducible_declared (a : Nat) : Nat := a

def fixtures_reducible_later (a : Nat) : Nat := a

def fixtures_reducible_mixed (a b n : Nat) : Nat :=
  match n with
  | 0 => a + b
  | k + 1 =>
    fixtures_reducible_mixed (fixtures_reducible_later a) (fixtures_reducible_declared b) k
termination_by n

attribute [reducible] fixtures_reducible_later

def fixtures_limit_first (a : Nat) : Nat := a

def fixtures_limit_second (a : Nat) : Nat := a

@[reducible] def fixtures_limit_one (a : Nat) : Nat := a

@[reducible] def fixtures_limit_two (a : Nat) : Nat := a

@[reducible] def fixtures_limit_three (a : Nat) : Nat := a

@[reducible] def fixtures_limit_four (a : Nat) : Nat := a

def fixtures_reducible_limit (a b n : Nat) : Nat :=
  match n with
  | 0 =>
    fixtures_limit_one (fixtures_limit_two (fixtures_limit_three (fixtures_limit_four (a + b))))
  | k + 1 => fixtures_reducible_limit (fixtures_limit_first a) (fixtures_limit_second b) k
termination_by n

attribute [reducible] fixtures_limit_first fixtures_limit_second

def fixtures_decoyed_first (a : Nat) : Nat := a

def fixtures_decoyed_second (a : Nat) : Nat := a

def fixtures_reducible_decoyed (a b n : Nat) : Nat :=
  match n with
  | 0 => a + b
  | k + 1 => fixtures_reducible_decoyed (fixtures_decoyed_first a) (fixtures_decoyed_second b) k
termination_by n

attribute [reducible] fixtures_decoyed_first fixtures_decoyed_second

@[reducible] def fixtures_decoy_one (a : Nat) : Nat := a

@[reducible] def fixtures_decoy_two (a : Nat) : Nat := a

@[reducible] def fixtures_decoy_three (a : Nat) : Nat := a

@[reducible] def fixtures_decoy_four (a : Nat) : Nat := a

@[reducible] def fixtures_decoy_five (a : Nat) : Nat := a

/-- Authored, not generated: named as Lean names a smart-unfolding definition. -/
def fixtures_reducible_decoyed._unsafe_rec._sunfold (a b n : Nat) : Nat :=
  fixtures_decoy_one (fixtures_decoy_two (fixtures_decoy_three (fixtures_decoy_four
    (fixtures_decoy_five (a + b + n)))))

def fixtures_proved_first (a : Nat) : Nat := a

def fixtures_proved_second (a : Nat) : Nat := a

@[reducible] def fixtures_proved_one (a : Nat) : Nat := a

@[reducible] def fixtures_proved_two (a : Nat) : Nat := a

@[reducible] def fixtures_proved_three (a : Nat) : Nat := a

@[reducible] def fixtures_proved_four (a : Nat) : Nat := a

@[reducible] def fixtures_proved_five (a : Nat) : Nat := a

theorem fixtures_proved_bound (a : Nat) : a ≤ a + 0 :=
  Nat.le_refl (fixtures_proved_one (fixtures_proved_two (fixtures_proved_three
    (fixtures_proved_four (fixtures_proved_five a)))))

def fixtures_proved_keep (a : Nat) (_ : a ≤ a + 0) : Nat := a

def fixtures_reducible_proved (a b n : Nat) : Nat :=
  match n with
  | 0 => fixtures_proved_keep (a + b) (fixtures_proved_bound (a + b))
  | k + 1 => fixtures_reducible_proved (fixtures_proved_first a) (fixtures_proved_second b) k
termination_by n

attribute [reducible] fixtures_proved_first fixtures_proved_second

@[reducible] def fixtures_reducible_before (a : Nat) : Nat := a

def fixtures_reducible_then_not (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_reducible_then_not (fixtures_reducible_before a) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [irreducible] fixtures_reducible_before

class FixturesInstanceWrap where
  get : Nat → Nat

instance fixtures_instance_wrap : FixturesInstanceWrap := ⟨fun x => x⟩

set_option warn.classDefReducibility false in
def fixtures_instance_keep (w : FixturesInstanceWrap) : FixturesInstanceWrap := w

def fixtures_instance_later (g : [FixturesInstanceWrap] → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => @g fixtures_instance_wrap
  | k + 1 =>
    fixtures_instance_later (fun [w : FixturesInstanceWrap] => @g (fixtures_instance_keep w)) k
termination_by n

attribute [instance_reducible] fixtures_instance_keep

set_option warn.classDefReducibility false in
def fixtures_implicit_keep (w : FixturesInstanceWrap) : FixturesInstanceWrap := w

def fixtures_implicit_later (g : [FixturesInstanceWrap] → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => @g fixtures_instance_wrap
  | k + 1 =>
    fixtures_implicit_later (fun [w : FixturesInstanceWrap] => @g (fixtures_implicit_keep w)) k
termination_by n

attribute [implicit_reducible] fixtures_implicit_keep

@[instance_reducible] def fixtures_instance_before (w : FixturesInstanceWrap) :
    FixturesInstanceWrap := w

def fixtures_instance_then_not (g : [FixturesInstanceWrap] → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => @g fixtures_instance_wrap
  | k + 1 =>
    fixtures_instance_then_not
      (fun [w : FixturesInstanceWrap] => @g (fixtures_instance_before w)) k
termination_by n

attribute [irreducible] fixtures_instance_before

abbrev fixtures_abbrev_both_keep (a : Nat) : Nat := a

set_option allowUnsafeReducibility true in
attribute [irreducible] fixtures_abbrev_both_keep

def FixturesAbbrevBothAlias := List Nat

def fixtures_abbrev_both (a : Nat) (xs : FixturesAbbrevBothAlias) : Nat :=
  match xs with
  | [] => a
  | x :: rest => x + fixtures_abbrev_both (fixtures_abbrev_both_keep a) rest

attribute [irreducible] FixturesAbbrevBothAlias

/-- Semireducible in this module. `Fixtures.Mutations.KnownLimitReducibleWhereCompiled` makes it
`reducible` from another module, a change the search does not cover. -/
def fixtures_reducible_elsewhere (a : Nat) : Nat := a
