/-
Known checker limit (standard §7.4), not a forgery and not intended
behaviour: the definition is safe, Lean accepts it, and its helper is exactly
what Lean generated. The audit this fixture expects is incomplete: the checker
reports the helper as undecided, neither admitted nor rejected. That is the
verdict the checker has, not a violation: a helper no attempt within the bound
reproduces may be what Lean generated, and it is not admitted either way. A
forged helper over the bound ends the same way.

`fixtures_bound_searched` passes each of two parameters through a function
made `reducible` afterwards, so its base packs both and only the assignment
that gives both functions back as semireducible reproduces it. Its leaf calls
five more functions that are `@[reducible]` from their declaration, which
nothing in the final environment tells from the first two. Seven definitions
with one earlier status each allow 127 assignments, more than the 63 the
checker searches, so it tries the seven single changes, none of which
reproduces the base, and stops without a verdict. With four such functions in
place of five, six definitions allow 63 assignments, the search is exhaustive
and the helper is admitted (`fixtures_reducible_limit` of
`Fixtures.Positive.ReducibleAfter` is that shape).
-/
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
