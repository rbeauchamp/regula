/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary: the kind is
stated about the implementation applied to the first field of a pair twice, so it says nothing of
an input whose two arguments differ. Lean accepts the proof; the checker must refuse the
registration under RG1007 and name the function the kind decides.
-/
import Regula.Contract

def bothBelow (first second : Nat) : Bool := decide (first < 3) && decide (second < 3)

theorem bothBelow_decides :
    Regula.ExecutableContract bothBelow (fun check =>
      Regula.Decides (· = true) (fun input => input.1 < 3)
        (fun input : Nat × Nat => check input.1 input.1)) :=
  ⟨.of_iff (fun input => by simp [bothBelow]) ⟨(0, 5), by decide⟩ ⟨(3, 0), by decide⟩⟩
