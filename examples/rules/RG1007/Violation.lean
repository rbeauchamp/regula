import Regula.Contract
/-! # Identity

Identity on natural numbers, with its full-domain contract. -/
/-- The identity function on natural numbers. -/
def identity (n : Nat) : Nat := n
theorem contract (n : Nat) :
    Regula.ExecutableContract (identity n) (fun value => value = n) := ⟨rfl⟩
