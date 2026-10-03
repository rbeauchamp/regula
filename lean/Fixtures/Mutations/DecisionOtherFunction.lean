/-
Mutation of `Fixtures.Positive.DecisionKinds`: the kind is stated about a second function, not
about the registered implementation, so it says nothing of the constant callers run. The checker
must refuse the registration under RG1007 and name the function the kind decides.
-/
import Regula.Contract

def positive (n : Nat) : Bool := decide (0 < n)

/-- Not the registered implementation. -/
def model (n : Nat) : Bool := decide (0 < n)

theorem positive_decides :
    Regula.ExecutableContract positive
      (fun _ => Regula.Decides (· = true) (fun n => 0 < n) model) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨1, by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨0, by decide⟩ }⟩
