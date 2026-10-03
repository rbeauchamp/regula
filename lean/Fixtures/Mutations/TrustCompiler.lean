import Lean

/-! Exercise the legacy compiler axiom where Core declares it. On a compiler that removed
the family, an authored declaration with its old name must remain a project axiom (#192). -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `Lean.trustCompiler then
    elabCommand (← `(set_option linter.deprecated false in
      theorem $(mkIdent `fixtures_direct_trust_compiler) : True := Lean.trustCompiler))
  else
    if env.contains `Lean.ofReduceBool || env.contains `Lean.ofReduceNat then
      throwError "partial legacy compiler-axiom family"
    elabCommand (← `(axiom $(mkIdent `Lean.trustCompiler) : True))
