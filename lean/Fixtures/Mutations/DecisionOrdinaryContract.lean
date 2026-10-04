/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the registered decision has a contract,
but its requirement states no decision kind, so nothing says which direction is proved. The
registration itself is accepted under RG1007 and recorded with no kind; the checker must reject
the function under RG1008.
-/
import Regula.Contract
import Regula.Decision

@[regula_decision] def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_contract :
    Regula.ExecutableContract positive (fun check => ∀ n, check n = decide (0 < n)) :=
  ⟨fun _ => rfl⟩
