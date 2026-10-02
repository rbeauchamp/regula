/-
Known checker limit, tracked by issue #196
(https://github.com/rbeauchamp/regula/issues/196), not a forgery and not
intended behaviour. Each definition is safe, Lean accepts it, and each helper
is exactly what Lean generated. The rejection this fixture expects is a false
rejection. Invert the expectation (every helper admitted) when issue #196 is
fixed.

A function each definition calls is `reducible` at only one of the two points:
where the definition is compiled, and at the end of the audit. Lean's
recursion compilers take two decisions at reducible transparency, and the
regeneration, which runs in the environment the audit inspects, takes them
differently. Standard §7.4 states the limit. All four forms are observed
rejections on Lean 4.34.0. In the first three the function is made `reducible`
after the definition. `attribute [instance_reducible]` and
`attribute [implicit_reducible]` in place of `[reducible]` were observed not
to change either decision.

* Which parameters are fixed. `fixtures_reducible_fixed` passes
  `fixtures_reducible_keep a` for `a`. Where the definition is elaborated that
  is another argument, so `a` varies and Lean packs it with `n`. With
  `fixtures_reducible_keep` reducible the regeneration finds `a` fixed.
  `fixtures_reducible_structural` is the same under structural recursion,
  whose compiler takes the same decision.
* Which `wf_preprocess` rule of the toolchain applies.
  `FixturesReducibleTree.count` maps over its children through
  `fixtures_reducible_map`. Where the definition is elaborated the
  toolchain's `List.map` rule does not see through it; with
  `fixtures_reducible_map` reducible it does, and the regeneration rewrites
  the body.
* The other way round. `fixtures_reducible_before` is `@[reducible]` from its
  declaration, so Lean finds the parameter of `fixtures_reducible_then_not`
  fixed, and is made `irreducible` afterwards, which Lean allows only under
  `allowUnsafeReducibility`. Nothing in the final environment tells it from an
  ordinary definition made irreducible (an `abbrev` is told apart by its kernel
  hint, and is admitted), so the regeneration gives it back as semireducible
  and finds the parameter varying.
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

@[reducible] def fixtures_reducible_before (a : Nat) : Nat := a

def fixtures_reducible_then_not (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_reducible_then_not (fixtures_reducible_before a) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [irreducible] fixtures_reducible_before
