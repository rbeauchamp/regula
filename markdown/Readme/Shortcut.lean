/-! # Shortcut

Theorems that depend on an axiom and on a `sorry`, and a fact that compiled code checks. -/

/-- A shortcut that nobody proved. -/
axiom add_swap (a b : Nat) : a + b = b + a

/-- Addition commutes. -/
theorem swap (a b : Nat) : a + b = b + a := add_swap a b

/-- A lemma that nobody proved yet. -/
theorem double (n : Nat) : n + n = 2 * n := by sorry

/-- A theorem that uses the lemma. -/
theorem twice (n : Nat) : 2 * n = n + n := (double n).symm

/-- A fact that compiled code checks, not Lean's kernel. -/
theorem big : 2 ^ 20 = 1048576 := by native_decide
