import Lean

/-
Mutation (issue #125): `Positive.DerivedRecursion` plus one local registration
of an imported elaborator for the built-in `match` syntax. The entry is not one
the module's post-import environment registered, so Lean may dispatch code the
module chose where it elaborates generated definitions with information trees
disabled, and no helper of the module is admitted.
-/

attribute [local term_elab Lean.Parser.Term.match] Lean.Elab.Term.elabMatch

inductive FixturesRegistered where
  | leaf
  | wrap (inner : FixturesRegistered)
  | pair (left right : FixturesRegistered)
  deriving DecidableEq, BEq, Hashable, Repr
