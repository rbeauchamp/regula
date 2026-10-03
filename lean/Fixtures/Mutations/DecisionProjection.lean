/-
Mutation of `Fixtures.Positive.DecisionRegistration`: a structure projection is registered as a
decision explicitly, and no contract decides it. Lean generates a projection from the structure's
constructor, and the checker records that relation for a finding's location; it does not waive
the requirement. The checker must reject `Holder.check` under RG1008.
-/
import Regula.Decision

structure Holder where
  check : Nat → Bool

attribute [regula_decision] Holder.check
