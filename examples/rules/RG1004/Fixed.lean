import Init
/-! # Concrete facts

The same concrete facts have kernel proofs. -/
theorem equal : (2 : Nat) = 2 := rfl
theorem gcdValue : Nat.gcd 1071 462 = 21 := by decide
theorem commute (x y : BitVec 8) : x * y = y * x := BitVec.mul_comm x y
