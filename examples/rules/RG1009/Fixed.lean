import Regula.Contract
import Regula.Decision
/-! # Bound test

A bound stated as a proposition. -/
/-- `n` is below four. -/
def Small (n : Nat) : Prop := n < 4
instance (n : Nat) : Decidable (Small n) := n.decLt 4
/-- Whether `n` is below four. -/
@[regula_decision] def check (n : Nat) : Bool := decide (Small n)
theorem contract : Regula.ExecutableContract check (Regula.Decides (· = true) Small) :=
  ⟨.of_iff (fun _ => ⟨of_decide_eq_true, decide_eq_true⟩) ⟨0, rfl⟩ ⟨4, by decide⟩⟩
