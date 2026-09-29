/-
Mutation (issue #125): `deriving BEq` on a nested inductive makes Lean's
deriving handler generate a `partial def`: an opaque comparison that the
compiler runs through its partial `_unsafe_rec` helper. It is a real escape
hatch, and the finding names the generated opaque declaration rather than its
helper.
-/

inductive FixturesTree where
  | node (children : List FixturesTree)
  deriving BEq
