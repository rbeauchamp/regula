import Lean

/-
Positive control (issue #125): deriving `DecidableEq`, `BEq`, `Hashable` and
`Repr` on a recursive inductive generates structurally recursive functions with
Lean's `_unsafe_rec` helpers inside the inductive's own declaration command.
Lean elaborates the generated syntax with no source positions (the
`DecidableEq` comparison with information trees disabled), so the helpers are
admitted without a positioned binder record; no audited-source code ran or is
registered in this module. The stored predefinitions abstract nested proofs
into auxiliary theorems that the helpers keep inline; they are compared up to
proofs. The mutations `DerivedWithSourceLocalMacro` and `DerivedAfterRunCmd`
each add one fault to this control.
-/

inductive FixturesShape where
  | leaf
  | wrap (inner : FixturesShape)
  | pair (left right : FixturesShape)
  deriving DecidableEq, BEq, Hashable, Repr
