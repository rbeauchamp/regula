import Regula.Qualification.RegistryCli
import Regula.Qualification.NativeLinter
import Regula.Qualification.Producer
import Regula.Qualification.History
import Regula.Qualification.DocumentationSource
import Regula.Qualification.FrozenExit
import Regula.Qualification.RuleExamples
import Regula.Qualification.EnvironmentCensus
import Regula.Qualification.Acceptance
import Regula.Qualification.ReceiptBoundary
import Regula.Qualification.Preparation
import Regula.Qualification.SelfAudit

/-! # Qualification executable dispatcher

One Lake executable for operational qualification, with independently selectable
campaigns. Each oracle is proved on the positive `RegulaQualification` surface;
this process dispatcher and its IO adapters remain operational tooling. -/

/-- Explicit commands; unknown or extra arguments refuse instead of silently skipping
work. The acceptance shell owns the overall deadline, not this dispatcher. -/
private unsafe def dispatch (args : List String) (attempt : Option String := none) : IO Unit := do
  match args with
  | ["registry"] => Regula.Qualification.RegistryCli.check
  | ["native"] => Regula.Qualification.NativeLinter.checkAll
  | ["combined"] => do
      Regula.Qualification.RegistryCli.check
      Regula.Qualification.NativeLinter.checkAll
  | ["native-launcher"] => Regula.Qualification.NativeLinter.paired
  | ["rule-examples", "--evidence", path] => Regula.Qualification.RuleExamples.check
                                              ⟨path⟩ none attempt
  | "rule-examples" :: "--evidence" :: path :: "--rules" :: rules =>
      Regula.Qualification.RuleExamples.check ⟨path⟩ (some rules.toArray) attempt
  | ["rule-examples", "--evidence", path, "--shard", spec] => do
      let shard ← match (spec.splitOn "/").map String.toNat? with
        | [some index, some count] =>
          if 1 ≤ index && index ≤ count then pure (index, count)
          else throw <| IO.userError s!"invalid rule-example shard: {spec}"
        | _ => throw <| IO.userError s!"invalid rule-example shard: {spec}"
      Regula.Qualification.RuleExamples.check ⟨path⟩ none attempt (some shard)
  | ["producers"] => Regula.Qualification.Producer.check none
  | ["producers", "--evidence", path] => Regula.Qualification.Producer.check (some ⟨path⟩)
  | ["producers-combined"] => do
      Regula.Qualification.Producer.check none
      Regula.Qualification.History.check
  | ["history"] => Regula.Qualification.History.check
  | ["self-audit"] => Regula.Qualification.SelfAudit.check
  | ["self-audit-module", m, source] => Regula.Qualification.SelfAudit.worker m source
  | ["environments", "--evidence", path] => Regula.Qualification.EnvironmentCensus.check
                                             ⟨path⟩ attempt
  | ["acceptance", group, "--evidence", path] => Regula.Qualification.Acceptance.check group
                                                  ⟨path⟩ attempt
  | ["acceptance-snapshots", group] => Regula.Qualification.DependencySnapshot.check group
  | ["prep-measure"] => Regula.Qualification.Preparation.check
  | ["documentation-dependencies"] => Regula.Qualification.Acceptance.documentationDependencies
  | ["input-inventory"] => Regula.Qualification.InputInventory.check
  | ["receipt-boundaries"] => Regula.Qualification.ReceiptBoundary.check
  | ["closure-evidence"] => Regula.Qualification.SourceEvidence.closure
  | ["configuration-capture"] => Regula.Qualification.SourceEvidence.configuration
  | ["fence-evidence"] => Regula.Qualification.SourceEvidence.fences
  | ["frozen-exits"] => Regula.Qualification.FrozenExit.check
  | ["documentation-source"] => Regula.Qualification.DocumentationSource.check false
  | ["documentation-source", "--source-read-only"] =>
      Regula.Qualification.DocumentationSource.check true
  | _ => throw <| IO.userError "usage: lake exe qualify \
    registry|native|combined|native-launcher|producers [--evidence PATH]|environments --evidence \
    PATH|acceptance GROUP --evidence PATH|acceptance-snapshots \
    dependencies|history|self-audit|git-status|all|documentation-dependencies|input-inventory|histo\
    ry|closure-evidence|configuration-capture|fence-evidence|frozen-exits|documentation-source \
    [--source-read-only]|rule-examples --evidence PATH [--rules RULE ... | --shard K/N]"

/-- Standalone commands get one group-wide 420-second bound. The private protocol flag
is supplied by this wrapper or the already timed acceptance driver, never documented
as a bounded standalone command. Nested commands do not create escaping groups. -/
unsafe def main (args : List String) : IO UInt32 := do
  if (← IO.getEnv "REGULA_RECEIPT_TIMER") == some "1" && args == ["--version"] then
    return ← Regula.Qualification.ReceiptBoundary.worker args
  match ← IO.getEnv "REGULA_QUALIFICATION_WRAPPER" with
  | some "acceptance" => return ← Regula.Qualification.Acceptance.worker args
  | some "inventory" => return ← Regula.Qualification.InputInventory.worker args
  | some _ => throw <| IO.userError "unknown qualification wrapper mode"
  | none => pure ()
  match args with
  | "--under-deadline" :: "--attempt" :: attempt :: rest => dispatch rest (some attempt); return 0
  | "--under-deadline" :: rest => dispatch rest; return 0
  | _ =>
    -- Recognize evidence destinations even when later argument validation refuses.
    -- This must precede timeout selection and spawning, both of which can fail.
    let attempt ← Regula.Qualification.freshAttempt
    match args with
    | "acceptance" :: group :: "--evidence" :: path :: _ =>
      let _ ← Regula.Qualification.Acceptance.beginAttempt group ⟨path⟩ attempt
    | "environments" :: "--evidence" :: path :: _ =>
      Regula.Qualification.EnvironmentCensus.beginAttempt ⟨path⟩ attempt
    | "rule-examples" :: "--evidence" :: path :: _ =>
      Regula.Qualification.RuleExamples.beginAttempt ⟨path⟩ attempt
    | _ => pure ()
    Regula.Qualification.runBounded (← IO.currentDir) 420 (← IO.appPath).toString
      (#["--under-deadline", "--attempt", attempt] ++ args.toArray)
