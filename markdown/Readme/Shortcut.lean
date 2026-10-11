/-! A theorem that depends on an unfinished proof. -/

/-- A lemma that nobody proved yet. -/
theorem double (n : Nat) : n + n = 2 * n := by sorry

/-- A theorem that uses the lemma. -/
theorem twice (n : Nat) : 2 * n = n + n := (double n).symm
