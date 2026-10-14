import Regula.Removal
import Regula.TaskManagerCheck
import Regula.CopyControls
import Regula.Qualification.CopySelection
import Regula.Qualification.RegistryCli
import Regula.Qualification.NativeLinter
import Regula.Qualification.Producer
import Regula.Qualification.History
import Regula.Qualification.DocumentationSource
import Regula.Qualification.VersoPaths
import Regula.Qualification.CopyRelocation
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
import Regula.Qualification.Enumeration
import Regula.Qualification.Readers
import Regula.Checker.AxiomGate

/-! # Qualification executable dispatcher

One Lake executable for operational qualification, with independently selectable
campaigns. Each oracle is proved on the positive `RegulaQualification` surface;
this process dispatcher and its IO adapters remain operational tooling. -/

open Regula.Qualification

/-- The shard of the rule-example corpus that `spec` names, `K/N` with `1 ≤ K ≤ N`, or the error
that refuses it. -/
private def ruleExampleShard (spec : String) : Except String (Nat × Nat) :=
  match (spec.splitOn "/").map String.toNat? with
  | [some index, some count] =>
    if 1 ≤ index && index ≤ count then .ok (index, count)
    else .error s!"invalid rule-example shard: {spec}"
  | _ => .error s!"invalid rule-example shard: {spec}"

/-- Run one selection. The acceptance shell owns the overall deadline, not this dispatcher. -/
private unsafe def runCommand (attempt : Option String) : Command → IO Unit
  | .registry => Regula.Qualification.RegistryCli.check
  | .native => Regula.Qualification.NativeLinter.checkAll
  | .combined => do
      Regula.Qualification.RegistryCli.check
      Regula.CopyControls.checkWorkspace
      Regula.Qualification.CopySelection.check
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
      let shard ← IO.ofExcept ((ruleExampleShard spec).mapError IO.userError)
      Regula.Qualification.RuleExamples.check ⟨path⟩ none attempt (some shard)
  | .producers => Regula.Qualification.Producer.check none
  | .producersExport path => Regula.Qualification.Producer.check (some ⟨path⟩) attempt
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
  | .configurationCapture => do
      Regula.Qualification.SourceEvidence.configuration
      Regula.Qualification.SourceEvidence.selectedPolicy
  | .versoRecordedPaths => Regula.Qualification.VersoPaths.check
  | .copyRelocation => Regula.Qualification.CopyRelocation.check
  | .copyRelocationLoad project copies =>
      Regula.Qualification.CopyRelocation.loadWorker project copies
  | .copyRelocationGit scratch => Regula.Qualification.CopyRelocation.gitSteps scratch
  | .fenceEvidence => Regula.Qualification.SourceEvidence.fences
  | .frozenExits => Regula.Qualification.FrozenExit.check
  | .documentationSource => Regula.Qualification.DocumentationSource.check false
  | .documentationSourceReadOnly => Regula.Qualification.DocumentationSource.check true
  | .enumeration => Regula.Qualification.Enumeration.check
  | .enumerationCopy source target => Regula.Qualification.Enumeration.copyChild source target
  | .enumerationFailure => Regula.Qualification.Enumeration.failure
  | .readers => Regula.Qualification.Readers.check

/-- The command that `args` name (`Command.parse`), or the error that refuses them before any
campaign begins: the usage text for unknown or extra arguments, which refuse instead of silently
skipping work, and the refusal of a rule-example shard (`ruleExampleShard`). -/
private def commandOf (args : List String) : Except String Command :=
  match Command.parse args with
  | some command@(.ruleExamplesShard _ spec) => (ruleExampleShard spec).map fun _ => command
  | some command => .ok command
  | none => .error "usage: lake exe qualify \
    registry|native|combined|unique-constants|native-launcher|producers [--evidence PATH]|\
    producers-combined|\
    environments --evidence PATH|acceptance fences --evidence PATH|acceptance-snapshots \
    dependencies|history|git-status|all|history|self-audit [--shard K/4]|\
    documentation-dependencies|input-inventory|receipt-boundaries|observers|prep-measure|\
    closure-evidence|\
    configuration-capture|verso-recorded-paths|copy-relocation|fence-evidence|frozen-exits|\
    documentation-source [--source-read-only]|enumeration|enumeration-failure|readers|\
    rule-examples --evidence PATH [--rules RULE ... | --shard K/N]"

/-- The file of the evidence document `evidence`. The launcher's report is at
`NativeLinter.reportPath` of the package root, and a run outside that root has none here, as its
mark then fails (`NativeLinter.beginReport`). -/
private def evidenceDestination : Evidence → IO (Option System.FilePath)
  | .ruleExamples path | .producers path | .environments path | .acceptance _ path =>
    pure (some ⟨path⟩)
  | .launcherReport => do
    match ← Regula.Qualification.rootDirectory.toBaseIO with
    | .ok root => pure (some (NativeLinter.reportPath root))
    | .error _ => pure none

/-- The reason to refuse the evidence document that `args` name from their leading arguments
(`Evidence.named`, `evidenceDestination`), if it holds something that the command may not replace
(`Regula.Destination.refusal`): the command marks it before it reads an input. -/
private def evidenceRefusal (args : List String) : IO (Option String) := do
  let named ← match Evidence.named args with
    | some evidence => evidenceDestination evidence
    | none => pure none
  Regula.Destination.refusal named.toList

/-- Mark the evidence document that `args` names incomplete for the attempt `attempt`, through the
writer that its campaign runs before it starts (`beginAttempt`), before anything else of the
command runs; with `reason`, the evidence records why the attempt stops there. The document is the
one that the leading arguments name (`Evidence.named`), so one that the parser refuses for a later
argument is still marked, and for an accepted command it is the command's own
(`Evidence.named_of_parse`). Arguments that name no evidence document mark nothing. A document
that `evidenceRefusal` refuses is not marked: the marker stops with the reason. -/
private def markEvidence (args : List String) (attempt : String) (reason : Option String := none) :
    IO Unit := do
  if let some refusal ← evidenceRefusal args then throw <| IO.userError s!"refused: {refusal}"
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

/-- The form of one `qualify` invocation, read from its arguments, the three variables of its
environment that select a mode and the name of the running program (`Invocation.of`). -/
private inductive Invocation where
  /-- `REGULA_RECEIPT_TIMER=1` with `--version`: the receipt boundary's worker. -/
  | receiptTimer
  /-- `REGULA_LISTING_STANDIN=MODE` in a copy of `qualify` named as `Construction.locate` looks
  for GNU `ls`: the stand-in listing program of the enumeration control (`Enumeration.standin`). -/
  | listingStandin (mode : String)
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
  if let some mode := ← IO.getEnv Regula.Qualification.Enumeration.standinVariable then
    if let .ok path := ← IO.appPath.toBaseIO then
      if path.fileName == some Regula.Qualification.Enumeration.standinName then
        return .listingStandin mode
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
invocation is read once (`Invocation.of`). A bounded command marks its evidence before the
selection of the timeout, and again with the error's text when that selection or the spawn fails,
or when the start ends without running the command (`runBounded`, `markEvidence`). A command under
the deadline that its arguments refuse before a campaign begins (`commandOf`) marks the evidence
that its leading arguments name with the error's text, for the attempt that the wrapper gives or
otherwise for one fresh attempt that the campaign then uses too. -/
unsafe def qualifyMain (args : List String) : IO UInt32 := do
  match ← Invocation.of args with
  | .receiptTimer => Regula.Qualification.ReceiptBoundary.worker args
  | .listingStandin mode => Regula.Qualification.Enumeration.standin mode args
  | .acceptanceProxy => Regula.Qualification.Acceptance.worker args
  | .unknownWrapper => throw <| IO.userError "unknown qualification wrapper mode"
  | .underDeadline attempt rest =>
    if let some reason ← evidenceRefusal rest then throw <| IO.userError s!"refused: {reason}"
    let attempt ← attempt.getDM Regula.Qualification.freshAttempt
    match commandOf rest with
    | .ok command => runCommand (some attempt) command; return 0
    | .error error =>
      discard <| (markEvidence rest attempt (some error)).toBaseIO
      throw <| IO.userError error
  | .bounded args =>
    -- Recognize evidence destinations even when later argument validation refuses.
    -- This must precede timeout selection and spawning, both of which can fail.
    let attempt ← Regula.Qualification.freshAttempt
    markEvidence args attempt
    -- A start that fails, or that ends without running the command, ends the attempt before the
    -- command runs, so no record of the command's own replaces the mark: mark it with the error's
    -- text.
    let fail {α : Type} (error : IO.Error) : IO α := do
      discard <| (markEvidence args attempt (some error.toString)).toBaseIO
      throw error
    let started ← try
        Regula.Qualification.runBounded (← IO.currentDir) 420 (← IO.appPath).toString
          (#["--under-deadline", "--attempt", attempt] ++ args.toArray)
      catch error => fail error
    match started with
    | .ok status => return status
    | .error reason => fail (IO.userError reason)

/-- The refusal of an invocation in a process without Lean's task manager, which the guard of the
executable runs (`Regula.TaskManager.guard`). It reads the invocation as `qualifyMain` does
(`Invocation.of`) and marks its destinations incomplete with `reason` through the writers that a
run uses. The proxy of `axiomGate` is refused as the gate refuses, with the gate's exit code
(`AxiomGate.refuseWithoutTaskManager`). A command marks its evidence document (`markEvidence`),
for the attempt that the wrapper's arguments give or otherwise for a fresh one, printing a line
when it cannot, and returns 1, as do the receipt boundary's worker, the stand-in listing program
and an unknown wrapper mode, which write no file. No command runs. -/
private def refuseQualification (reason : String) (args : List String) : IO UInt32 := do
  let mark (rest : List String) (attempt : Option String) : IO Unit := do
    try markEvidence rest (← attempt.getDM Regula.Qualification.freshAttempt) reason
    catch error =>
      IO.eprintln s!"qualify: could not mark the evidence of {rest} incomplete: {error}"
  match ← Invocation.of args with
  | .acceptanceProxy =>
    return ← Regula.Checker.AxiomGate.refuseWithoutTaskManager reason args
  | .receiptTimer | .listingStandin _ | .unknownWrapper => pure ()
  | .underDeadline attempt rest => mark rest attempt
  | .bounded rest => mark rest none
  return 1

/-- The `qualify` executable: `qualifyMain` on the command-line arguments. A process without
Lean's task manager is refused before any command starts: the destinations of the invocation are
marked incomplete with the reason, and the exit code is 1, or the gate's for the proxy of
`axiomGate` (`Regula.TaskManager.guard`, `refuseQualification`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "qualify" refuseQualification qualifyMain

-- The removals and the writes that the compiled code of the program reaches from its roots
-- (`Regula.Removal.rawRemovals`) are those of the filesystem observer and those that
-- `Regula.Removal.sharedPairs` lists, and those named here, each by the declaration of a source
-- that makes it: the build of this module fails otherwise, and when a name here admits no call
-- (`Regula.Removal.checkProgram`). The program elaborates Lean source, so its check states it.
run_cmd Regula.Removal.checkProgram (elaborates := true) (named := [
  -- The projects, slots and fixtures of the campaigns, in the scratch and slot directories that
  -- they make, and the raw observations of a rule-example production in the raw directory beside
  -- its evidence (`Regula.Qualification.RuleExamples`).
  (``Regula.Qualification.Acceptance.documentationDependencies, ``IO.FS.createDirAll),
  (``Regula.Qualification.Acceptance.documentationDependencies, ``IO.FS.writeFile),
  (``Regula.CopyControls.checkWorkspace, ``IO.FS.writeFile),
  (``Regula.Qualification.CopyRelocation.check, ``IO.FS.createDirAll),
  (`Regula.Qualification.CopyRelocation.copied, ``IO.FS.createDirAll),
  (`Regula.Qualification.CopyRelocation.refusedCopy, ``IO.FS.createDirAll),
  (``Regula.Qualification.CopySelection.checkAt, ``IO.FS.writeFile),
  (`Regula.Qualification.CopySelection.sourceLink, ``IO.FS.writeFile),
  (`Regula.Qualification.DependencySnapshot.control, ``IO.FS.writeFile),
  (`Regula.Qualification.DependencySnapshot.gitStatusControls, ``IO.FS.createDirAll),
  (`Regula.Qualification.DependencySnapshot.gitStatusControls, ``IO.FS.writeFile),
  (``Regula.Qualification.DependencySnapshot.check, ``IO.FS.createDirAll),
  (``Regula.Qualification.DependencySnapshot.check, ``IO.FS.writeBinFile),
  (``Regula.Qualification.DependencySnapshot.check, ``IO.FS.writeFile),
  (``Regula.Qualification.DocumentationSource.check, ``IO.FS.writeFile),
  (``Regula.Qualification.Enumeration.check, ``IO.FS.createDir),
  (``Regula.Qualification.Enumeration.check, ``IO.FS.writeFile),
  (``Regula.Qualification.Enumeration.failure, ``IO.FS.Handle.mk),
  (``Regula.Qualification.Enumeration.failure, ``IO.FS.createDir),
  (``Regula.Qualification.Enumeration.failure, ``IO.FS.createDirAll),
  (``Regula.Qualification.Enumeration.failure, ``IO.FS.writeFile),
  (`Regula.Qualification.FrozenExit.runCase, ``IO.FS.writeFile),
  (`Regula.Qualification.History.control, ``IO.FS.createDir),
  (`Regula.Qualification.History.control, ``IO.FS.writeFile),
  (``Regula.Qualification.InputInventory.check, ``IO.FS.createDirAll),
  (``Regula.Qualification.InputInventory.check, ``IO.FS.writeFile),
  (`Regula.Qualification.NativeLinter.check, ``IO.FS.writeFile),
  (`Regula.Qualification.NativeLinter.forgedPrelude, ``IO.FS.createDirAll),
  (`Regula.Qualification.NativeLinter.forgedPrelude, ``IO.FS.writeFile),
  (``Regula.Qualification.NativeLinter.paired, ``IO.FS.createDir),
  (``Regula.Qualification.Preparation.check, ``IO.FS.createDirAll),
  (`Regula.Qualification.Producer.chain, ``IO.FS.writeBinFile),
  (`Regula.Qualification.Producer.checkControls, ``IO.FS.createDir),
  (`Regula.Qualification.Producer.standalone, ``IO.FS.writeFile),
  (``Regula.Qualification.prepareCoreProject, ``IO.FS.createDirAll),
  (``Regula.Qualification.rootImportsGuardControl, ``IO.FS.writeFile),
  (``Regula.Qualification.Readers.writePackage, ``IO.FS.createDirAll),
  (``Regula.Qualification.ReceiptBoundary.check, ``IO.FS.createDir),
  (``Regula.Qualification.ReceiptBoundary.check, ``IO.FS.writeFile),
  (`Regula.Qualification.RuleExamples.observe, ``IO.FS.Handle.mk),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.createDir),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.createDirAll),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.writeBinFile),
  (`Regula.Qualification.RuleExamples.produce, ``IO.FS.writeFile),
  (``Regula.Qualification.RuleExamples.check, ``IO.FS.createDirAll),
  (``Regula.Qualification.Slot.prepareSlot, ``IO.FS.writeFile),
  (``Regula.Qualification.SourceEvidence.closure, ``IO.FS.writeFile),
  (``Regula.Qualification.SourceEvidence.configuration, ``IO.FS.createDir),
  (``Regula.Qualification.SourceEvidence.configuration, ``IO.FS.writeFile),
  (``Regula.Qualification.SourceEvidence.fences, ``IO.FS.writeFile),
  (``Regula.Qualification.SourceEvidence.selectedPolicy, ``IO.FS.writeFile),
  (``Regula.Qualification.SourceEvidence.writeFence, ``IO.FS.writeFile),
  (`Regula.Qualification.VersoPaths.withChanged, ``IO.FS.writeFile),
  (`Regula.Qualification.VersoPaths.withRemoved, ``IO.FS.writeBinFile),
  (`Regula.Qualification.VersoPaths.withWritten, ``IO.FS.createDirAll),
  (`Regula.Qualification.VersoPaths.withWritten, ``IO.FS.writeFile)])

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
