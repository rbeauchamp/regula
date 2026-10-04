/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the registered decision is defined by
well-founded recursion, so Lean compiles it through the generated `equalCount._unary`, and no
contract decides `equalCount`. The checker must reject `equalCount` under RG1008, once. The
registration is applied after compilation, so Lean does not copy it to `equalCount._unary`, which
is accepted with no decision record.
-/
import Regula.Decision

@[regula_decision] def equalCount (a b : Nat) : Bool :=
  if a = 0 then decide (b = 0) else if b = 0 then false else equalCount (a - 1) (b - 1)
termination_by a
