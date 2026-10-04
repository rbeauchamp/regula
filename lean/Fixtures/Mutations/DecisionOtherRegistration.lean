/-
Mutation of `Fixtures.Positive.DecisionRegistration`: a decision contract exists, but it decides
another function. The registered decision `positive` is the implementation of no contract, so the
checker must reject it under RG1008; the contract of `model` is accepted.
-/
import Regula.Contract
import Regula.Decision

@[regula_decision] def positive (n : Nat) : Bool := decide (0 < n)

def model (n : Nat) : Bool := decide (0 < n)

theorem model_decides :
    Regula.ExecutableContract model (Regula.Decides (· = true) fun n => 0 < n) :=
  ⟨{ sound := fun _ accepted => of_decide_eq_true accepted
     accepted := ⟨1, by decide⟩
     complete := fun _ holds => decide_eq_true holds
     refused := ⟨0, by decide⟩ }⟩
