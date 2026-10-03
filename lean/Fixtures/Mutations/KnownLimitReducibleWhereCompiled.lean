import Fixtures.Positive.ReducibleAfter

/-
Known checker limit (standard §7.4), not a forgery and not intended
behaviour. Each definition is safe, Lean accepts it, and each helper is
exactly what Lean generated. The rejection this fixture expects is a false
rejection. Invert the expectation (every helper admitted) for a form once the
checker covers it.

A function each definition calls has, where the definition is compiled, a
reducibility status that the checker's search does not try. The search gives
the definitions of the helper's own module that are not an `abbrev` the
statuses a later global attribute Lean's validation admits can have replaced,
and `reducible` to one that is irreducible at the end of the audit. Each form
below is outside that: the status holds only where the definition is compiled
and nothing at the end of the audit shows it, or the function is an `abbrev`
or belongs to another module, or the change is one Lean's validation of a
global attribute does not admit. All but the fourth need
`set_option allowUnsafeReducibility true`.

* `fixtures_where_local` passes a parameter through
  `fixtures_where_local_keep`, `reducible` only for that definition
  (`attribute [local reducible]`), so Lean finds the parameter fixed. At the
  end of the audit the function is semireducible, which no global attribute
  gives, so the search tries nothing for it.
* `fixtures_where_unreduced` is the same with a function that is
  `@[reducible]` from its declaration and made semireducible afterwards.
* `fixtures_where_sealed` passes a parameter through an `abbrev` that is
  irreducible only for that definition, so the parameter varies. The `abbrev`
  is `reducible` at the end of the audit, and the search leaves an `abbrev`
  out, since it is `reducible` from its declaration.
* `fixtures_where_instance` passes a function through an instance argument
  that goes through `fixtures_where_instance_keep`, `instance_reducible` only
  for that definition (`attribute [local instance_reducible]`, which Lean
  allows without `allowUnsafeReducibility`), so Lean finds the function fixed.
* `fixtures_where_elsewhere` passes a parameter through
  `fixtures_reducible_elsewhere`, a function of another module that is made
  `reducible` after the definition. The search covers only the helper's own
  module.
* `fixtures_where_upgraded` passes an explicit argument and an instance
  argument through `fixtures_where_upgraded_keep`, `instance_reducible` where
  the definition is compiled, so the first parameter varies and the second is
  fixed, and made `reducible` afterwards, so both are fixed. For a `reducible`
  definition the search tries semireducible alone, the status from which
  Lean's validation admits `reducible`, and under it both vary.
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
