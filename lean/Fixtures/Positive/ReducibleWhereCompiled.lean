import Fixtures.Positive.ReducibleAfter

/-
Positive control (issue #196) at the compiler boundary: safe recursive
definitions that call a function whose reducibility status, where the
definition is compiled, is one that nothing at the end of the audit shows.
Lean accepts each, and each helper is exactly what Lean generated.

Lean's recursion compilers take two decisions at reducible transparency, and
at implicit transparency where they compare an instance-implicit argument:
which parameters are fixed, and which `wf_preprocess` rule of the toolchain
rewrites the body. The checker runs those two decisions as Lean's own
functions, records which definitions they ask about, of any module, and
finds for each the statuses under which a decision comes out differently.
From the observed base it reads which parameters Lean kept fixed and how many
mentions of a function it kept, which select one assignment directly, tried
before any other. Before that search each form below was an observed
rejection, or an audit that stopped without a verdict, on Lean 4.34.0, except
those marked as new, which were not run before it.

All but `fixtures_where_instance` and `fixtures_where_implicit` need
`set_option allowUnsafeReducibility true`.

* `fixtures_where_local` passes a parameter through
  `fixtures_where_local_keep`, `reducible` only for that definition
  (`attribute [local reducible]`), so Lean finds the parameter fixed. At the
  end of the audit the function is semireducible.
* `fixtures_where_unreduced` is the same with a function that is
  `@[reducible]` from its declaration and made semireducible afterwards.
* `fixtures_where_sealed` passes a parameter through an `abbrev` that is
  irreducible only for that definition, so the parameter varies. The `abbrev`
  is `reducible` at the end of the audit.
* `fixtures_where_instance` passes a function through an instance argument
  that goes through `fixtures_where_instance_keep`, `instance_reducible` only
  for that definition (`attribute [local instance_reducible]`, which Lean
  allows without `allowUnsafeReducibility`), so Lean finds the function fixed.
  `fixtures_where_implicit` is the same with
  `attribute [local implicit_reducible]` (new).
* `fixtures_where_elsewhere` passes a parameter through
  `fixtures_reducible_elsewhere`, a function of another module that is made
  `reducible` after the definition.
* `fixtures_where_upgraded` passes an explicit argument and an instance
  argument through `fixtures_where_upgraded_keep`, `instance_reducible` where
  the definition is compiled, so the first parameter varies and the second is
  fixed, and made `reducible` afterwards, so both are fixed.
* `fixtures_bound_searched` passes each of two parameters through a function
  made `reducible` afterwards, and its leaf calls five more functions that are
  `@[reducible]` from their declaration. The search once enumerated every
  definition of the module the helper reaches: seven of them allow 127
  assignments, more than the 63 it tries, and the audit stopped without a
  verdict. Only the two functions in the recursive call change a decision.
* `fixtures_where_seven` passes each of seven parameters through its own
  function made `reducible` afterwards (new). Seven definitions that each
  change a decision allow 127 assignments, more than the enumeration tries;
  the observed base, which keeps no parameter fixed, selects the one that
  gives all seven back as semireducible.
* `fixtures_where_twice` passes one parameter through two functions, one in
  each of two recursive calls, both `reducible` only for that definition
  (new). Lean finds the parameter fixed only where both unfold, so no change
  of one status alone changes a decision.
* `fixtures_where_structural` is `fixtures_where_local` under structural
  recursion (new).
* `FixturesWhereTree.count` maps over its children through
  `fixtures_where_map`, `reducible` only for that definition, so the
  toolchain's `List.map` rule sees through it and rewrites the body (new). At
  the end of the audit the function is semireducible and the rule does not
  apply. `FixturesWhereTree.depth` maps through `fixtures_where_outer`, which
  unfolds to `fixtures_where_inner`, which unfolds to `List.map`, both
  `reducible` only for that definition (new): the rule applies only where both
  unfold. `FixturesWhereTree.shared` is that definition with a leaf that calls
  `fixtures_where_inner` directly, on a list the rule does not rewrite (new;
  found in review, traced from the source as a rejection and not run before
  the search changed): the preprocessing asks about the inner function before
  any change, so the search did not take it for a function the outer one
  unfolds to; it now tries the two together.
  `FixturesWhereTree.chained` maps through `fixtures_chain_one`, the first of
  six functions of which each unfolds to the next and the last to `List.map`,
  all `reducible` only for that definition (new; found in review): the search
  once followed such a chain through five runs only and left this helper
  undecided (observed), and before that reported it as a violation; it now
  follows the chain to its end.
  `FixturesWhereTree.total` maps through `fixtures_where_map` over
  `fixtures_where_pick children`, two functions that do not unfold to one
  another, both `reducible` only for that definition (new): the rule matches
  only where both unfold, so no change of one status alone changes the
  preprocessed body, and the mentions the observed base keeps select both.
  `FixturesWhereTree.hidden` maps through `fixtures_where_hidden_outer`,
  `@[reducible]` from its declaration, which unfolds to
  `fixtures_where_hidden_inner`, `reducible` only for that definition (found in
  review): the helper mentions only the outer function, whose status is the
  same at both points, and the function whose status differs is one Lean asks
  about only because the outer one unfolds to it.
* `fixtures_where_discriminant` passes a parameter through a `match` on
  `fixtures_where_flag`, `reducible` only for that definition, so the `match`
  reduces and Lean finds the parameter fixed (new). `fixtures_where_matched`
  passes it through a function that unfolds to that `match`, both `reducible`
  only for that definition (new). Lean reduces such a discriminant with its
  unfolding predicate put aside, where the search records nothing; it reaches
  the discriminant again once the matcher itself unfolds, which is recorded.
* `fixtures_where_accessible` recurses structurally over `Acc`, an inductive
  predicate, and passes a parameter through a function made `reducible`
  afterwards (new). The checker reads no fixed parameters from a base of that
  shape, so no assignment is selected and the enumeration finds the one that
  reproduces it. The search this one replaces admitted it too (observed).
-/
def fixtures_where_local_keep (a : Nat) : Nat := a

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_local_keep in
def fixtures_where_local (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_where_local (fixtures_where_local_keep a) k
termination_by n

@[reducible] def fixtures_where_unreduced_keep (a : Nat) : Nat := a

def fixtures_where_unreduced (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_where_unreduced (fixtures_where_unreduced_keep a) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [semireducible] fixtures_where_unreduced_keep

abbrev fixtures_where_sealed_keep (a : Nat) : Nat := a

set_option allowUnsafeReducibility true in
attribute [local irreducible] fixtures_where_sealed_keep in
def fixtures_where_sealed (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_where_sealed (fixtures_where_sealed_keep a) k
termination_by n

set_option warn.classDefReducibility false in
def fixtures_where_instance_keep (w : FixturesInstanceWrap) : FixturesInstanceWrap := w

attribute [local instance_reducible] fixtures_where_instance_keep in
def fixtures_where_instance (g : [FixturesInstanceWrap] → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => @g fixtures_instance_wrap
  | k + 1 =>
    fixtures_where_instance
      (fun [w : FixturesInstanceWrap] => @g (fixtures_where_instance_keep w)) k
termination_by n

set_option warn.classDefReducibility false in
def fixtures_where_implicit_keep (w : FixturesInstanceWrap) : FixturesInstanceWrap := w

attribute [local implicit_reducible] fixtures_where_implicit_keep in
def fixtures_where_implicit (g : [FixturesInstanceWrap] → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => @g fixtures_instance_wrap
  | k + 1 =>
    fixtures_where_implicit
      (fun [w : FixturesInstanceWrap] => @g (fixtures_where_implicit_keep w)) k
termination_by n

def fixtures_where_elsewhere (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_where_elsewhere (fixtures_reducible_elsewhere a) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [reducible] fixtures_reducible_elsewhere

@[instance_reducible] def fixtures_where_upgraded_keep (w : FixturesInstanceWrap) :
    FixturesInstanceWrap := w

def fixtures_where_upgraded (w : FixturesInstanceWrap) (g : [FixturesInstanceWrap] → Nat)
    (n : Nat) : Nat :=
  match n with
  | 0 => @g w
  | k + 1 =>
    fixtures_where_upgraded (fixtures_where_upgraded_keep w)
      (fun [x : FixturesInstanceWrap] => @g (fixtures_where_upgraded_keep x)) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [reducible] fixtures_where_upgraded_keep

def fixtures_bound_first (a : Nat) : Nat := a

def fixtures_bound_second (a : Nat) : Nat := a

@[reducible] def fixtures_bound_one (a : Nat) : Nat := a

@[reducible] def fixtures_bound_two (a : Nat) : Nat := a

@[reducible] def fixtures_bound_three (a : Nat) : Nat := a

@[reducible] def fixtures_bound_four (a : Nat) : Nat := a

@[reducible] def fixtures_bound_five (a : Nat) : Nat := a

def fixtures_bound_searched (a b n : Nat) : Nat :=
  match n with
  | 0 =>
    fixtures_bound_one (fixtures_bound_two (fixtures_bound_three
      (fixtures_bound_four (fixtures_bound_five (a + b)))))
  | k + 1 => fixtures_bound_searched (fixtures_bound_first a) (fixtures_bound_second b) k
termination_by n

attribute [reducible] fixtures_bound_first fixtures_bound_second

def fixtures_seven_first (a : Nat) : Nat := a

def fixtures_seven_second (a : Nat) : Nat := a

def fixtures_seven_third (a : Nat) : Nat := a

def fixtures_seven_fourth (a : Nat) : Nat := a

def fixtures_seven_fifth (a : Nat) : Nat := a

def fixtures_seven_sixth (a : Nat) : Nat := a

def fixtures_seven_seventh (a : Nat) : Nat := a

def fixtures_where_seven (a b c d e f g n : Nat) : Nat :=
  match n with
  | 0 => a + b + c + d + e + f + g
  | k + 1 =>
    fixtures_where_seven (fixtures_seven_first a) (fixtures_seven_second b)
      (fixtures_seven_third c) (fixtures_seven_fourth d) (fixtures_seven_fifth e)
      (fixtures_seven_sixth f) (fixtures_seven_seventh g) k
termination_by n

attribute [reducible] fixtures_seven_first fixtures_seven_second fixtures_seven_third
  fixtures_seven_fourth fixtures_seven_fifth fixtures_seven_sixth fixtures_seven_seventh

def fixtures_where_twice_first (a : Nat) : Nat := a

def fixtures_where_twice_second (a : Nat) : Nat := a

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_twice_first fixtures_where_twice_second in
def fixtures_where_twice (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 =>
    fixtures_where_twice (fixtures_where_twice_first a) k
      + fixtures_where_twice (fixtures_where_twice_second a) (k / 2)
termination_by n

def fixtures_where_structural_keep (a : Nat) : Nat := a

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_structural_keep in
def fixtures_where_structural (a : Nat) : List Nat → Nat
  | [] => a
  | _ :: xs => fixtures_where_structural (fixtures_where_structural_keep a) xs

inductive FixturesWhereTree where
  | node : List FixturesWhereTree → FixturesWhereTree

def fixtures_where_map {α β : Type} (f : α → β) (xs : List α) : List β := List.map f xs

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_map in
def FixturesWhereTree.count : FixturesWhereTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 => 1 + (fixtures_where_map (fun child => child.count fuel) children).sum
termination_by _ fuel => fuel

def fixtures_where_inner {α β : Type} (f : α → β) (xs : List α) : List β := List.map f xs

def fixtures_where_outer {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_where_inner f xs

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_inner fixtures_where_outer in
def FixturesWhereTree.depth : FixturesWhereTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 => 1 + (fixtures_where_outer (fun child => child.depth fuel) children).sum
termination_by _ fuel => fuel

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_inner fixtures_where_outer in
def FixturesWhereTree.shared : FixturesWhereTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => (fixtures_where_inner (· + 1) (List.range 3)).sum
    | fuel + 1 => 1 + (fixtures_where_outer (fun child => child.shared fuel) children).sum
termination_by _ fuel => fuel

def fixtures_chain_six {α β : Type} (f : α → β) (xs : List α) : List β := List.map f xs

def fixtures_chain_five {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_chain_six f xs

def fixtures_chain_four {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_chain_five f xs

def fixtures_chain_three {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_chain_four f xs

def fixtures_chain_two {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_chain_three f xs

def fixtures_chain_one {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_chain_two f xs

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_chain_one fixtures_chain_two fixtures_chain_three
  fixtures_chain_four fixtures_chain_five fixtures_chain_six in
def FixturesWhereTree.chained : FixturesWhereTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 => 1 + (fixtures_chain_one (fun child => child.chained fuel) children).sum
termination_by _ fuel => fuel


def fixtures_where_pick {α : Type} (xs : List α) : List α := xs

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_map fixtures_where_pick in
def FixturesWhereTree.total : FixturesWhereTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 =>
      1 + (fixtures_where_map (fun child => child.total fuel) (fixtures_where_pick children)).sum
termination_by _ fuel => fuel

def fixtures_where_hidden_inner {α β : Type} (f : α → β) (xs : List α) : List β := List.map f xs

@[reducible] def fixtures_where_hidden_outer {α β : Type} (f : α → β) (xs : List α) : List β :=
  fixtures_where_hidden_inner f xs

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_hidden_inner in
def FixturesWhereTree.hidden : FixturesWhereTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 => 1 + (fixtures_where_hidden_outer (fun child => child.hidden fuel) children).sum
termination_by _ fuel => fuel

def fixtures_where_flag : Bool := true

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_flag in
def fixtures_where_discriminant (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 =>
    fixtures_where_discriminant (match fixtures_where_flag with | true => a | false => a) k
termination_by n

def fixtures_where_matched_keep (a : Nat) : Nat :=
  match fixtures_where_flag with
  | true => a
  | false => a

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_where_flag fixtures_where_matched_keep in
def fixtures_where_matched (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_where_matched (fixtures_where_matched_keep a) k
termination_by n

def fixtures_where_accessible_keep (a : Nat) : Nat := a

def fixtures_where_accessible (a : Nat) : (n : Nat) → Acc (· < ·) n → Nat
  | n, .intro _ h =>
    if hn : n = 0 then a
    else fixtures_where_accessible (fixtures_where_accessible_keep a) (n - 1) (h _ (by omega))

attribute [reducible] fixtures_where_accessible_keep
