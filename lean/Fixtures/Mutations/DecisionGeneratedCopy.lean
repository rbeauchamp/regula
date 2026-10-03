/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the registered decision is defined by
well-founded recursion, so Lean generates `equalCount._unary` and copies the registration to it,
and no contract decides `equalCount`. The checker must reject `equalCount` under RG1008, once:
the generated copy has no requirement of its own and is accepted.
-/
import Regula.Decision

@[regula_decision] def equalCount (a b : Nat) : Bool :=
  if a = 0 then decide (b = 0) else if b = 0 then false else equalCount (a - 1) (b - 1)
termination_by a
