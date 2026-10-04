import Regula.Contract
import Regula.Decision
/-! # Zero test

A decision that a natural number is zero, with its two-way contract. -/
/-- Whether `n` is zero. -/
@[regula_decision] def isZero : Nat → Bool
  | 0 => true
  | _ + 1 => false
theorem contract : Regula.ExecutableContract isZero (Regula.Decides (· = true) (· = 0)) :=
  ⟨.of_iff (fun | 0 => ⟨fun _ => rfl, fun _ => rfl⟩ | _ + 1 => ⟨nofun, nofun⟩) ⟨0, rfl⟩ ⟨1, nofun⟩⟩
