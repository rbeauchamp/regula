import Regula.MaterialClaim
/-! # Reflexivity

Reflexivity for every natural number; `reflexive` supplies its evidence. -/
/-- Every natural number equals itself, without additional hypotheses.

# Intent
Equality on natural numbers must be reflexive for every value, with no side condition.-/
@[regula_material] theorem reflexive (n : Nat) : n = n := rfl
