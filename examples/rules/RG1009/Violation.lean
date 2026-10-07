import Regula.Contract
import Regula.Decision
/-! # Bound test

A decision of a bound whose specification calls the test that the function runs. -/
/-- Whether `n` is below four. -/
def small (n : Nat) : Bool := decide (n < 4)
/-- Whether `n` is below four. -/
@[regula_decision] def check (n : Nat) : Bool := small n
theorem contract : Regula.ExecutableContract check (Regula.Decides (· = true) (small · = true)) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, rfl⟩ ⟨4, by decide⟩⟩
