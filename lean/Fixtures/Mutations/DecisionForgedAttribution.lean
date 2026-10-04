/-
Mutation of `Fixtures.Positive.DecisionRegistration`: an authored function is registered as a
decision with no contract, and the file then marks it as an auxiliary recursor of the declaration
it is named under (`Lean.markAuxRecursor`), state an audited project can write. The checker reads
that mark as "Lean generated `holder.check` from `holder`" when it locates a finding; the mark
must not waive the requirement. The checker must reject `holder.check` under RG1008.
-/
import Lean.AuxRecursor
import Lean.Elab.Command
import Regula.Decision

def holder : Nat := 0

@[regula_decision] def holder.check (n : Nat) : Bool := n == 0

run_cmd Lean.modifyEnv (Lean.markAuxRecursor · `holder.check)
