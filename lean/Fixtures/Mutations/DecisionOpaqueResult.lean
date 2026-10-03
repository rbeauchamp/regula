/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the registered decision's result type is an
irreducible alias of `Decidable`, which Lean's reduction does not unfold, so the checker does not
read it as a `Decidable` result. With no contract, the checker must reject the function under
RG1008: an unrecognized result form fails closed.
-/
import Regula.Decision

@[irreducible] def Verdict (p : Prop) : Type := Decidable p

@[regula_decision] def positiveVerdict (n : Nat) : Verdict (0 < n) := by
  unfold Verdict
  infer_instance
