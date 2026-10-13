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
import Regula.Checker.AxiomGate

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

/-- Mark the evidence document that `args` names incomplete for the attempt `attempt`, through the
writer that its campaign runs before it starts (`beginAttempt`), before anything else of the
command runs; with `reason`, the evidence records why the attempt stops there. The document is the
one that the leading arguments name (`Evidence.named`), so one that the parser refuses for a later
argument is still marked, and for an accepted command it is the command's own
(`Evidence.named_of_parse`). Arguments that name no evidence document mark nothing. -/
private def markEvidence (args : List String) (attempt : String) (reason : Option String := none) :
    IO Unit := do
  match Evidence.named args with
  | some (.acceptance group path) =>
    let _ ← Regula.Qualification.Acceptance.beginAttempt group ⟨path⟩ attempt reason
  | some (.environments path) =>
    Regula.Qualification.EnvironmentCensus.beginAttempt ⟨path⟩ attempt reason
  | some (.ruleExamples path) =>
    Regula.Qualification.RuleExamples.beginAttempt ⟨path⟩ attempt reason
  | some (.producers path) => Regula.Qualification.Producer.beginAttempt ⟨path⟩ attempt reason
  | some .launcherReport => Regula.Qualification.NativeLinter.beginReport reason
  | none => pure ()

/-- The form of one `qualify` invocation, read from its arguments and the two variables of its
environment that select a mode (`Invocation.of`). -/
private inductive Invocation where
  /-- `REGULA_RECEIPT_TIMER=1` with `--version`: the receipt boundary's worker. -/
  | receiptTimer
  /-- `REGULA_QUALIFICATION_WRAPPER=acceptance`: the test-only proxy of `axiomGate`, with the
  gate's arguments. -/
  | acceptanceProxy
  /-- Another value of `REGULA_QUALIFICATION_WRAPPER`, which is refused. -/
  | unknownWrapper
  /-- `--under-deadline [--attempt ATTEMPT] REST`: the command `REST`, run under the deadline that
  the wrapper set. -/
  | underDeadline (attempt : Option String) (rest : List String)
  /-- Any other arguments: a command, run under its own 420-second deadline. -/
  | bounded (args : List String)

/-- The form of the invocation with the arguments `args`, read from them and the environment. -/
private def Invocation.of (args : List String) : BaseIO Invocation := do
  if (← IO.getEnv "REGULA_RECEIPT_TIMER") == some "1" && args == ["--version"] then
    return .receiptTimer
  match ← IO.getEnv "REGULA_QUALIFICATION_WRAPPER" with
  | some "acceptance" => return .acceptanceProxy
  | some _ => return .unknownWrapper
  | none => return match args with
    | "--under-deadline" :: "--attempt" :: attempt :: rest => .underDeadline (some attempt) rest
    | "--under-deadline" :: rest => .underDeadline none rest
    | _ => .bounded args

/-- Standalone commands get one group-wide 420-second bound. The private protocol flag
is supplied by this wrapper or the already timed acceptance driver, never documented
as a bounded standalone command. Nested commands do not create escaping groups. The form of the
invocation is read once (`Invocation.of`). -/
unsafe def qualifyMain (args : List String) : IO UInt32 := do
  match ← Invocation.of args with
  | .receiptTimer => Regula.Qualification.ReceiptBoundary.worker args
  | .acceptanceProxy => Regula.Qualification.Acceptance.worker args
  | .unknownWrapper => throw <| IO.userError "unknown qualification wrapper mode"
  | .underDeadline attempt rest => dispatch rest attempt; return 0
  | .bounded args =>
    -- Recognize evidence destinations even when later argument validation refuses.
    -- This must precede timeout selection and spawning, both of which can fail.
    let attempt ← Regula.Qualification.freshAttempt
    markEvidence args attempt
    Regula.Qualification.runBounded (← IO.currentDir) 420 (← IO.appPath).toString
      (#["--under-deadline", "--attempt", attempt] ++ args.toArray)

/-- The refusal of an invocation in a process without Lean's task manager, which the guard of the
executable runs (`Regula.TaskManager.guard`). It reads the invocation as `qualifyMain` does
(`Invocation.of`) and marks its destinations incomplete with `reason` through the writers that a
run uses. The proxy of `axiomGate` is refused as the gate refuses, with the gate's exit code
(`AxiomGate.refuseWithoutTaskManager`). A command marks its evidence document (`markEvidence`),
for the attempt that the wrapper's arguments give or otherwise for a fresh one, printing a line
when it cannot, and returns 1, as do the receipt boundary's worker and an unknown wrapper mode,
which write no file. No command
runs. -/
private def refuseQualification (reason : String) (args : List String) : IO UInt32 := do
  let mark (rest : List String) (attempt : Option String) : IO Unit := do
    try markEvidence rest (← attempt.getDM Regula.Qualification.freshAttempt) reason
    catch error =>
      IO.eprintln s!"qualify: could not mark the evidence of {rest} incomplete: {error}"
  match ← Invocation.of args with
  | .acceptanceProxy =>
    return ← Regula.Checker.AxiomGate.refuseWithoutTaskManager reason args
  | .receiptTimer | .unknownWrapper => pure ()
  | .underDeadline attempt rest => mark rest attempt
  | .bounded rest => mark rest none
  return 1

/-- The `qualify` executable: `qualifyMain` on the command-line arguments. A process without
Lean's task manager is refused before any command starts: the destinations of the invocation are
marked incomplete with the reason, and the exit code is 1, or the gate's for the proxy of
`axiomGate` (`Regula.TaskManager.guard`, `refuseQualification`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "qualify" refuseQualification qualifyMain

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
