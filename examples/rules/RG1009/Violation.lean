import Regula.Contract
import Regula.Decision
/-! # Bound test -/
/-- Whether `n` is below 4. -/
def small (n : Nat) : Bool := decide (n < 4)
/-- Whether `n` is below 4. -/
def check (n : Nat) : Bool := small n
theorem check_registered : Regula.RegisteredDecision @check := ⟨⟩
theorem contract : Regula.ExecutableContract check (Regula.Decides (· = true) (small · = true)) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨0, rfl⟩ ⟨4, by decide⟩⟩
