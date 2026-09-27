import Regula.MaterialClaim
/-! # Reflexivity

Reflexivity for every natural number; `reflexive` supplies its evidence. -/
/-- Every natural number equals itself, without additional hypotheses. -/
@[regula_material] theorem reflexive (n : Nat) : n = n := rfl
