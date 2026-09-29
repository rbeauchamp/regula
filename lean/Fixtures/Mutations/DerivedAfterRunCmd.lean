import Lean

/-
Mutation (issue #125): `Positive.DerivedRecursion` plus one earlier `run_cmd`.
Audited-source code that ran in the elaborator could have rewritten the
registries attribution relies on (elaborator tables, attributes, the deriving
handlers), so no later helper of the module is admitted.
-/

run_cmd pure ()

inductive FixturesRan where
  | leaf
  | wrap (inner : FixturesRan)
  | pair (left right : FixturesRan)
  deriving DecidableEq, BEq, Hashable, Repr
