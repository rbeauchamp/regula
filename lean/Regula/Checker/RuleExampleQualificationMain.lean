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

/-- `qualifyEvidence` on the arguments `args`, returning 0 when it returns. -/
def ruleExampleQualificationMain (args : List String) : IO UInt32 := do
  qualifyEvidence args
  return 0

/-- The refusal of the qualification in a process without Lean's task manager
(`Regula.TaskManager.guard`): it reads its evidence and writes no result, so it marks nothing, and
it returns 1. -/
def refuseRuleExampleQualification (_reason : String) (_args : List String) : IO UInt32 :=
  pure 1

/-- The `ruleExampleQualification` executable: `ruleExampleQualificationMain` on the command-line
arguments; an error that escapes it ends the process with exit code 1. A process without Lean's
task manager is refused before the qualification starts, with exit code 1
(`Regula.TaskManager.guard`). -/
def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "ruleExampleQualification" refuseRuleExampleQualification
    ruleExampleQualificationMain

-- The removals and the writes that the compiled code of `main`, and of the initializers of the
-- modules it links, reaches are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists: the build of this module fails otherwise
-- (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
