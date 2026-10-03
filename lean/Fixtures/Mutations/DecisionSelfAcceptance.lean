/-
Mutation of `Fixtures.Positive.DecisionKinds`: the acceptance predicate compares a result with
the implementation's own result at a fixed input. The checker must refuse the registration under
RG1007 and say that the acceptance predicate mentions the implementation.
-/
import Regula.Contract

def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_decides :
    Regula.ExecutableContract positive (Regula.Decides (· = positive 1) fun n => 0 < n) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨1, rfl⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨0, by decide⟩ }⟩
