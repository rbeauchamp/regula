/-
Mutation of `Fixtures.Positive.DecisionKinds`: the two-way kind is given soundness, both
witnesses and no `complete` field. Lean must refuse the structure for the missing field, so a
one-way guarantee cannot be registered as `Regula.Decides`.
-/
import Regula.Contract

def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_decides :
    Regula.ExecutableContract positive (Regula.Decides (· = true) fun n => 0 < n) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨1, by decide⟩
     refused := ⟨0, by decide⟩ }⟩
