import Regula.Decision
/-! # Zero test

A decision that a natural number is zero, with no contract. -/
/-- Whether `n` is zero. -/
@[regula_decision] def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false
