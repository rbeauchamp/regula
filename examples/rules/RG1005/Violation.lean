/-! # Reflexivity

Reflexivity proved through propositional extensionality. -/
theorem reflexive (n : Nat) : n = n := Eq.mp (propext (Iff.rfl : (n = n) ↔ (n = n))) rfl
