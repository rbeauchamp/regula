import Std.Tactic.BVDecide
/-! # Concrete facts

The concrete facts use native proof evaluation. -/
theorem equal : (2 : Nat) = 2 := by native_decide
theorem gcdValue : Nat.gcd 1071 462 = 21 := by decide +native
theorem commute (x y : BitVec 8) : x * y = y * x := by bv_decide
