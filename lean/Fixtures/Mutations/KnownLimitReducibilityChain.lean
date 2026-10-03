/-
Known checker limit (standard §7.4), not a forgery and not intended
behaviour: the definition is safe, Lean accepts it, and its helper is exactly
what Lean generated. The audit this fixture expects is incomplete: the checker
reports the helper as undecided, neither admitted nor rejected (found in
review; before that, the search took a chain it had not followed to its end
for a change with no effect, and reported a violation).

`FixturesChainTree.chained` maps over its children through
`fixtures_chain_one`, the first of six functions of which each unfolds to the
next and the last to `List.map`, all `reducible` only for that definition. The
toolchain's `List.map` rule sees through them where the definition is
compiled and rewrites the body; at the end of the audit all six are
semireducible and the rule does not apply. The search makes the first function
`reducible`, finds that Lean's preprocessing then asks about the second, and
follows such a chain through four further functions: five runs, after which
the sixth function still does not unfold. It has then not decided that change,
so it does not report the helper as rejected: the audit is incomplete, with no
violation reported for it. `FixturesWhereTree.depth` of
`Fixtures.Positive.ReducibleWhereCompiled` is this shape with two functions,
admitted.
-/
inductive FixturesChainTree where
  | node : List FixturesChainTree → FixturesChainTree

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
def FixturesChainTree.chained : FixturesChainTree → Nat → Nat
  | .node children, fuel =>
    match fuel with
    | 0 => 0
    | fuel + 1 => 1 + (fixtures_chain_one (fun child => child.chained fuel) children).sum
termination_by _ fuel => fuel
