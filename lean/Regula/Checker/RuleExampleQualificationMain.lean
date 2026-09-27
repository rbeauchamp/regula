import Regula.Checker.RuleExampleQualification

/-! # Rule-example qualification executable

`ruleExampleQualification`: command-line admission of exported rule-example evidence.
With a corpus path it runs `RuleExampleQualification.qualifyCorpus`; with `--record` it
qualifies each in-progress record against unchanged checker sources, with no corpus claim. -/

/-- Validate a whole exported corpus, or one in-progress record without a corpus claim. -/
def main (args : List String) : IO Unit := do
  let (path, single) ← match args with
    | ["--record", path] => pure (path, true)
    | [path] => pure (path, false)
    | _ => throw <| IO.userError "usage: RuleExampleQualification [--record] EVIDENCE.json"
  let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile path)
  if single then
    let before ← IO.ofExcept (json.getObjVal? "checkerBefore")
    let after ← IO.ofExcept (json.getObjVal? "checkerAfter")
    unless before == after do throw <| IO.userError "checker sources changed"
    for record in ← IO.ofExcept ((json.getObjVal? "records").bind Lean.Json.getArr?) do
      IO.ofExcept
          (Regula.Checker.RuleExampleQualification.qualify
              (record.setObjVal! "checkerSources" before))
  else IO.ofExcept (Regula.Checker.RuleExampleQualification.qualifyCorpus json)
  IO.println "rule example evidence: PASS (scoped diagnostic qualification; no Accepted claim)"
