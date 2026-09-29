/-
Positive control (issue #125): deriving `DecidableEq`, `BEq`, `Hashable` and
`Repr` on a recursive inductive generates structurally recursive functions with
Lean's `_unsafe_rec` helpers inside the inductive's own declaration command, the
`DecidableEq` comparison elaborated with information trees disabled. Exact match
admits each helper: Lean's structural recursion compiler, rerun on the helper,
regenerates the observed derived function.
-/

inductive FixturesShape where
  | leaf
  | wrap (inner : FixturesShape)
  | pair (left right : FixturesShape)
  deriving DecidableEq, BEq, Hashable, Repr
