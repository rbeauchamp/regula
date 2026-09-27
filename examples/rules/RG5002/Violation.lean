import Regula.MaterialClaim
/-! # Reflexivity

Reflexivity for every natural number; `reflexive` supplies its evidence. -/
@[regula_material] theorem reflexive (n : Nat) : n = n := rfl
