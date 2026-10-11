/-! # Shortcut

A theorem that depends on an axiom, and a fact that compiled code checks. -/

/-- A shortcut that nobody proved. -/
axiom add_swap (a b : Nat) : a + b = b + a

/-- Addition commutes. -/
theorem swap (a b : Nat) : a + b = b + a := add_swap a b

/-- A fact that compiled code checks, not Lean's kernel. -/
theorem big : 2 ^ 20 = 1048576 := by native_decide
