import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Qualification.RegistryCli
import Regula.Qualification.NativeLinter
import Regula.Qualification.Producer
import Regula.Qualification.History
import Regula.Qualification.DocumentationSource
import Regula.Qualification.FrozenExit
import Regula.Qualification.RuleExamples
import Regula.Qualification.EnvironmentCensus
import Regula.Qualification.Acceptance
import Regula.Qualification.InputInventory
import Regula.Qualification.ReceiptBoundary
import Regula.Qualification.Preparation
import Regula.Qualification.SelfAudit
import Regula.Qualification.UniqueConstants
import Regula.Qualification.Command
import Regula.Qualification.Observers

/-! # Qualification executable dispatcher

One Lake executable for operational qualification, with independently selectable
campaigns. Each oracle is proved on the positive `RegulaQualification` surface;
this process dispatcher and its IO adapters remain operational tooling. -/

open Regula.Qualification

/-- Run one selection. The acceptance shell owns the overall deadline, not this dispatcher. -/
private unsafe def runCommand (attempt : Option String) : Command → IO Unit
  | .registry => Regula.Qualification.RegistryCli.check
  | .native => Regula.Qualification.NativeLinter.checkAll
  | .combined => do
      Regula.Qualification.RegistryCli.check
      -- Beside the native controls; both must pass.
      let unique ← IO.asTask Regula.Qualification.UniqueConstants.check
      Regula.Qualification.NativeLinter.checkAll
      IO.ofExcept (← IO.wait unique)
  | .uniqueConstants => Regula.Qualification.UniqueConstants.check
  | .nativeLauncher => Regula.Qualification.NativeLinter.paired
  | .ruleExamples path => Regula.Qualification.RuleExamples.check ⟨path⟩ none attempt
  | .ruleExamplesRules path rules =>
      Regula.Qualification.RuleExamples.check ⟨path⟩ (some rules.toArray) attempt
  | .ruleExamplesShard path spec => do
      let shard ← match (spec.splitOn "/").map String.toNat? with
        | [some index, some count] =>
          if 1 ≤ index && index ≤ count then pure (index, count)
          else throw <| IO.userError s!"invalid rule-example shard: {spec}"
        | _ => throw <| IO.userError s!"invalid rule-example shard: {spec}"
      Regula.Qualification.RuleExamples.check ⟨path⟩ none attempt (some shard)
  | .producers => Regula.Qualification.Producer.check none
  | .producersExport path => Regula.Qualification.Producer.check (some ⟨path⟩)
  | .producersCombined => do
      Regula.Qualification.Producer.check none
      Regula.Qualification.History.check
  | .history => Regula.Qualification.History.check
  | .selfAudit => Regula.Qualification.SelfAudit.check
  | .selfAuditShard spec => do
      let some shard := Regula.Qualification.SelfAudit.shardOf? spec
        | throw <| IO.userError s!"invalid self-audit shard: {spec}"
      Regula.Qualification.SelfAudit.check (some shard)
  | .selfAuditModule m source => Regula.Qualification.SelfAudit.worker m source
  | .selfAuditJsonModule m => Regula.Qualification.SelfAudit.jsonWorker m
  | .environments path => Regula.Qualification.EnvironmentCensus.check ⟨path⟩ attempt
  | .acceptance group path => Regula.Qualification.Acceptance.check group.spelling ⟨path⟩ attempt
  | .acceptanceSnapshots group => Regula.Qualification.DependencySnapshot.check group.spelling
  | .prepMeasure => Regula.Qualification.Preparation.check
  | .documentationDependencies => Regula.Qualification.Acceptance.documentationDependencies
  | .inputInventory => Regula.Qualification.InputInventory.check
  | .receiptBoundaries => Regula.Qualification.ReceiptBoundary.check
  | .observers => Regula.Qualification.Observers.check
  | .closureEvidence => Regula.Qualification.SourceEvidence.closure
  | .configurationCapture => Regula.Qualification.SourceEvidence.configuration
  | .fenceEvidence => Regula.Qualification.SourceEvidence.fences
  | .frozenExits => Regula.Qualification.FrozenExit.check
  | .documentationSource => Regula.Qualification.DocumentationSource.check false
  | .documentationSourceReadOnly => Regula.Qualification.DocumentationSource.check true

/-- Explicit commands, parsed by `Command.parse`; unknown or extra arguments refuse instead of
silently skipping work. -/
private unsafe def dispatch (args : List String) (attempt : Option String := none) : IO Unit := do
  match Command.parse args with
  | some command => runCommand attempt command
  | none => throw <| IO.userError "usage: lake exe qualify \
    registry|native|combined|unique-constants|native-launcher|producers [--evidence PATH]|\
    producers-combined|\
    environments --evidence PATH|acceptance fences --evidence PATH|acceptance-snapshots \
    dependencies|history|git-status|all|history|self-audit [--shard K/4]|\
    documentation-dependencies|input-inventory|receipt-boundaries|observers|prep-measure|\
    closure-evidence|\
    configuration-capture|fence-evidence|frozen-exits|documentation-source [--source-read-only]|\
    rule-examples --evidence PATH [--rules RULE ... | --shard K/N]"

/-- Standalone commands get one group-wide 420-second bound. The private protocol flag
is supplied by this wrapper or the already timed acceptance driver, never documented
as a bounded standalone command. Nested commands do not create escaping groups. -/
unsafe def qualifyMain (args : List String) : IO UInt32 := do
  if (← IO.getEnv "REGULA_RECEIPT_TIMER") == some "1" && args == ["--version"] then
    return ← Regula.Qualification.ReceiptBoundary.worker args
  match ← IO.getEnv "REGULA_QUALIFICATION_WRAPPER" with
  | some "acceptance" => return ← Regula.Qualification.Acceptance.worker args
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

/-- The `qualify` executable: `qualifyMain` on the command-line arguments. A process without
Lean's task manager is refused before any command starts, with exit code 1
(`Regula.TaskManager.guard`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "qualify" 1 qualifyMain

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`):
-- the build of this module fails otherwise (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
