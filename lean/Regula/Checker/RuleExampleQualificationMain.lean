import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.RuleExampleQualification

/-! # Rule-example qualification executable

`ruleExampleQualification`: command-line admission of exported rule-example evidence.
With a corpus path it runs `RuleExampleQualification.qualifyCorpus`; with `--record` it
qualifies each in-progress record against unchanged checker sources, with no corpus claim. -/

/-- Validate a whole exported corpus, or one in-progress record without a corpus claim. -/
def qualifyEvidence (args : List String) : IO Unit := do
  let (path, single) ← match args with
    | ["--record", path] => pure (path, true)
    | [path] => pure (path, false)
    | _ => throw <| IO.userError "usage: RuleExampleQualification [--record] EVIDENCE.json"
  let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile path)
  if single then
    let before ← IO.ofExcept (json.getObjVal? "checkerBefore")
    let after ← IO.ofExcept (json.getObjVal? "checkerAfter")
    unless Regula.JsonAgreement.conforms before after do
      throw <| IO.userError "checker sources changed"
    for record in ← IO.ofExcept ((json.getObjVal? "records").bind Lean.Json.getArr?) do
      IO.ofExcept
          (Regula.Checker.RuleExampleQualification.qualify
              (record.setObjVal! "checkerSources" before))
  else IO.ofExcept (Regula.Checker.RuleExampleQualification.qualifyCorpus json)
  IO.println "rule example evidence: PASS (scoped diagnostic qualification; no Accepted claim)"

/-- The `ruleExampleQualification` executable: `qualifyEvidence` on the command-line arguments,
returning 0 when it returns; an error that escapes it ends the process with exit code 1. A process
without Lean's task manager is refused before the qualification starts, with exit code 1
(`Regula.TaskManager.guard`). -/
def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "ruleExampleQualification" 1 fun args => do
    qualifyEvidence args
    return 0

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`):
-- the build of this module fails otherwise (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
