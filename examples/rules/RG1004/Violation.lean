import Init
/-! # Concrete equality

The concrete equality uses native proof evaluation. -/
theorem equal : (2 : Nat) = 2 := by native_decide
