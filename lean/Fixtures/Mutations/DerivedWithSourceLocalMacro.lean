import Lean

/-
Mutation (issue #125): `Positive.DerivedRecursion` plus one module-local macro
for a built-in tactic kind. Lean may dispatch it where it elaborates generated
definitions with information trees disabled, so no helper of the module is
admitted, although each derived function is safe.
-/

macro_rules
  | `(tactic| trivial) => `(tactic| rfl)

inductive FixturesMarked where
  | leaf
  | wrap (inner : FixturesMarked)
  | pair (left right : FixturesMarked)
  deriving DecidableEq, BEq, Hashable, Repr
