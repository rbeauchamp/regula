/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the function is registered as a decision
with `@[regula_decision]`, its result type is not `Decidable _`, and no contract decides it. The
file elaborates; the checker must reject the function under RG1008.
-/
import Regula.Decision

@[regula_decision] def positive (n : Nat) : Bool := decide (0 < n)
