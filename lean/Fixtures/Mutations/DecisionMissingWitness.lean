/-
Mutation of `Fixtures.Positive.DecisionKinds`: the sound kind is given its direction and no
`accepted` witness. Lean must refuse the structure for the missing field, so a soundness theorem
alone cannot be registered as a sound decision.
-/
import Regula.Contract

def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_decidesSoundly :
    Regula.ExecutableContract positive (Regula.DecidesSoundly (· = true) fun n => 0 < n) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted }⟩
