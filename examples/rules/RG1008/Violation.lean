import Regula.Decision
/-! # Zero test

A decision that a natural number is zero, with no contract. -/
/-- Whether `n` is zero. -/
def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false

theorem isZero_registered : Regula.RegisteredDecision @isZero := ⟨⟩
