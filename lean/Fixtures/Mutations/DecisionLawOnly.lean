/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the registered decision has a law
(`Regula.DecisionEquivalence`) and no decision kind. The law states both directions and no
outcome, so it is not a kind: the registration is accepted under RG1007 and reported, linked, by the
law observer, and the checker must reject the function under RG1008, as it would with no contract.
-/
import Regula.Contract
import Regula.Decision

@[regula_decision] def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_law :
    Regula.ExecutableContract positive (Regula.DecisionEquivalence (· = true) fun n => 0 < n) :=
  ⟨⟨fun _ => decide_eq_true_iff⟩⟩
