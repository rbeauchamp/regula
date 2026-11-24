module

public import LeanIntent.Required
public import RegulaSpecification.Rules
public import RegulaSpecification.Proofs.Verdict
public import RegulaSpecification.Proofs.Language
public import RegulaSpecification.Proofs.Owner
public import RegulaSpecification.Proofs.Program
public import RegulaSpecification.Proofs.Owed
public import RegulaSpecification.Proofs.OwedModel
public import RegulaSpecification.Proofs.Standing
public import RegulaSpecification.Proofs.Preparation
public import RegulaSpecification.Proofs.Behaviour
public import RegulaSpecification.Meaning

@[expose] public section

namespace RegulaSpecification.Required

open Lean (Name Environment)
open LeanIntent

def plainGloss (req rulesOut allows freedom : String) : Gloss where
  requires := req
  rulesOut := rulesOut
  allows := allows
  freedom := freedom

def ruleExplanation (rule : String) (V : Input → Name → Prop) (summary : String) :
    Explanation (ruleRecord rule V) where
  shape := plainGloss
    s!"Pure rule checker from admitted closed inputs to reported {rule} subjects."
    "Impure checks or reading outside the admitted closed input."
    "Any total list of subjects per admitted closed input."
    "Order and multiplicity of reported subjects."
  dom := []
  props := [plainGloss
    s!"Reports a subject on an admitted closed input iff {summary}."
    s!"Missing a {rule} violation or reporting a non-violating subject."
    "Different orderings or duplicate entries of the same violating subjects."
    "Order and multiplicity of reported subjects (SameReports)."]
  vocab := [
    plainGloss "Well-formed closed input." "Open mentions or empty claims." "Any closed non-empty claim." "Representation of closed inputs.",
    plainGloss s!"{rule} violation predicate." "Unviolated subjects." "Any violating subject." "None beyond predicate extension."]
  restatement := .unconfirmed
  consequences := []

def rg1001Explanation : Explanation rg1001 :=
  ruleExplanation "RG1001" Violates1001 "it is an axiom declared in a claimed module"

def rg1002Explanation : Explanation rg1002 :=
  ruleExplanation "RG1002" Violates1002 "it is a claimed constant reaching sorryAx"

def rg1003Explanation : Explanation rg1003 :=
  ruleExplanation "RG1003" Violates1003 "it is a claimed constant reaching a non-standard non-sorry non-native axiom"

def rg1004Explanation : Explanation rg1004 :=
  ruleExplanation "RG1004" Violates1004 "it is a claimed constant reaching a native-proof axiom"

def rg1005Explanation : Explanation rg1005 :=
  ruleExplanation "RG1005" Violates1005 "it is a claimed constant reaching an axiom outside the configured profile"

def rg1006Explanation : Explanation rg1006 :=
  ruleExplanation "RG1006" Violates1006 "it is a claimed unsafe, partial, helper-named, loop-mentioning, or Lean.Order.fix-mentioning constant without an exempted form"

def rg1011Explanation : Explanation rg1011 :=
  ruleExplanation "RG1011" Violates1011 "it is a claimed constant with unexempted replacement or init attributes or a claimed foreign exported csimp entry"

def rg1012Explanation : Explanation rg1012 :=
  ruleExplanation "RG1012" Violates1012 "it is a claimed definition or opaque constant whose value mentions a panic form"

def rg1013Explanation : Explanation rg1013 :=
  ruleExplanation "RG1013" Violates1013 "it is a claimed module whose source file is not a module file"

def gateExplanation : Explanation gateRecord where
  shape := plainGloss
    "Total verdict function from an optional closed input to pass, fail, or incomplete."
    "Partial or effectful verdict computation."
    "Three-valued verdict classification."
    "None."
  dom := []
  props := [
    plainGloss "An unloadable build yields incomplete (RG2001)." "Passing or failing an unloadable build." "None." "None.",
    plainGloss "An ill-formed input yields incomplete." "Passing or failing an ill-formed input." "None." "None.",
    plainGloss "A well-formed input is complete and passes iff every registered rule holds." "Returning incomplete or disagreeing with AllHold." "None." "None."]
  vocab := [
    plainGloss "Well-formed closed input." "Open mentions or empty claims." "Any closed non-empty claim." "None."]
  restatement := .unconfirmed
  consequences := []

def languageExplanation : Explanation Language.languageRecord where
  shape := plainGloss
    "Total pre-build language decision from a Reading to Outcome."
    "Compiling before deciding or partial decision."
    "Four-valued Outcome classification."
    "None."
  dom := []
  props := [
    plainGloss "Unclosed configuration is refused." "Admitting unclosed toolchain, lakefile.lean, open paths, or disallowed keys." "None." "None.",
    plainGloss "Closed configuration with unread files is incomplete." "Admitting or refusing an incomplete read." "None." "None.",
    plainGloss "Closed full reading with require dependency yields proofOnly." "Running full gate on a package with require." "None." "None.",
    plainGloss "Closed full reading without require reaching Mathlib yields proofOnly." "Running full gate on Mathlib imports." "None." "None.",
    plainGloss "Uncovered reading without dependencies yields incomplete." "Admitting empty claims or unclosed module names." "None." "None.",
    plainGloss "Covered reading with disallowed syntax is refused." "Admitting disallowed syntax or attributes." "None." "None.",
    plainGloss "Reading wholly inside the closed language is admitted." "Refusing an inside reading." "None." "None."]
  vocab := [
    plainGloss "Closed configuration." "Unclosed keys, toolchain, lakefile.lean, or open paths." "Closed TOML packages." "None.",
    plainGloss "Complete reading." "Failed or partial reads." "All needed reads complete." "None.",
    plainGloss "Dependency requirement." "Zero-dependency packages." "Packages with require keys." "None.",
    plainGloss "Mathlib import reachability." "Non-Mathlib imports." "Imports rooted at Mathlib." "None.",
    plainGloss "Covered module graph." "Missing roots, unread reached modules, or unclosed module names." "Fully covered closed module graphs." "None.",
    plainGloss "All files admitted." "Any file outside the closed language." "All files in the closed language." "None.",
    plainGloss "Single file admitted." "Disallowed syntax, non-module headers, or truncated parses." "Admitted module files." "None.",
    plainGloss "Closed module name." "Path traversal or non-ASCII components." "ASCII module names." "None."]
  restatement := .unconfirmed
  consequences := []

def fullGateExplanation : Explanation Language.fullGateRecord where
  shape := plainGloss
    "Total full-gate sequencer mapping language outcome, build exit status, and rule verdict to report and step trace."
    "Running build or rules on non-admitted outcomes."
    "Exact report and step trace per case."
    "None."
  dom := []
  props := [
    plainGloss "Refused reading compiles nothing." "Running build or rules after refusal." "None." "None.",
    plainGloss "Incomplete reading compiles nothing." "Running build or rules after incomplete reading." "None." "None.",
    plainGloss "Proof-only reading compiles nothing." "Running build or rules when only proof verdict applies." "None." "None.",
    plainGloss "Admitted reading with passing build reports the rules verdict after read, build, and rules." "Skipping build or rules." "Any rules verdict." "None.",
    plainGloss "Admitted reading with failing build reports full failure after read and build." "Running rules or passing after failed build." "None." "None."]
  vocab := []
  restatement := .unconfirmed
  consequences := []

def programRecordUnitEnv : IntentRecord (List String → Regula.Effect.Prog Unit Environment UInt32) :=
  Effects.programRecord Unit Environment

def programExplanation : Explanation programRecordUnitEnv where
  shape := plainGloss
    "Pure effect-tree checker program from CLI arguments to exit code."
    "Unmodeled IO decisions outside the closed Op set."
    "Any Prog trace satisfying RunMeets."
    "Independent read order and non-verdict detail wording."
  dom := []
  props := [
    plainGloss "Every trace over every external response follows the pinned-Lean route, preparation, read-back, replay, refusal, and verdict-line contract (RunMeets)."
    "Unprepared operations, unjudged writes, missing replay, forged verdict lines, or untrue refusals."
    "Independent read order and detail-line wording."
    "Widest freedom between compliant traces."]
  vocab := [
    plainGloss "Non-verdict two-space detail line." "Lines that can forge a verdict line." "Any escaped detail line." "Exact wording.",
    plainGloss "Reading wholly inside the closed language." "Readings outside the closed set." "Admitted closed-language readings." "None."]
  restatement := .unconfirmed
  consequences := []

def rg1001Deliverable : Deliverable (Checker Input Name) where
  record := rg1001
  explanation := rg1001Explanation
  answers := []
  keeps := trivial

def rg1002Deliverable : Deliverable (Checker Input Name) where
  record := rg1002
  explanation := rg1002Explanation
  answers := []
  keeps := trivial

def rg1003Deliverable : Deliverable (Checker Input Name) where
  record := rg1003
  explanation := rg1003Explanation
  answers := []
  keeps := trivial

def rg1004Deliverable : Deliverable (Checker Input Name) where
  record := rg1004
  explanation := rg1004Explanation
  answers := []
  keeps := trivial

def rg1005Deliverable : Deliverable (Checker Input Name) where
  record := rg1005
  explanation := rg1005Explanation
  answers := []
  keeps := trivial

def rg1006Deliverable : Deliverable (Checker Input Name) where
  record := rg1006
  explanation := rg1006Explanation
  answers := []
  keeps := trivial

def rg1011Deliverable : Deliverable (Checker Input Name) where
  record := rg1011
  explanation := rg1011Explanation
  answers := []
  keeps := trivial

def rg1012Deliverable : Deliverable (Checker Input Name) where
  record := rg1012
  explanation := rg1012Explanation
  answers := []
  keeps := trivial

def rg1013Deliverable : Deliverable (Checker Input Name) where
  record := rg1013
  explanation := rg1013Explanation
  answers := []
  keeps := trivial

def gateDeliverable : Deliverable (Option Input → Verdict) where
  record := gateRecord
  explanation := gateExplanation
  answers := []
  keeps := trivial

def languageDeliverable : Deliverable (Regula.Language.Reading → Regula.Language.Outcome) where
  record := Language.languageRecord
  explanation := languageExplanation
  answers := []
  keeps := trivial

def fullGateDeliverable : Deliverable Language.GateRun where
  record := Language.fullGateRecord
  explanation := fullGateExplanation
  answers := []
  keeps := trivial

def programDeliverable : Deliverable (List String → Regula.Effect.Prog Unit Environment UInt32) where
  record := programRecordUnitEnv
  explanation := programExplanation
  answers := []
  keeps := trivial

def runProgram : List String → Regula.Effect.Prog Unit Environment UInt32 :=
  Regula.Shell.run

def rg1001Implementation : Implementation rg1001Deliverable where
  subject := rg1001Checker
  fulfils := fun _ => rg1001_meets.2

def rg1002Implementation : Implementation rg1002Deliverable where
  subject := rg1002Checker
  fulfils := fun _ => rg1002_meets.2

def rg1003Implementation : Implementation rg1003Deliverable where
  subject := rg1003Checker
  fulfils := fun _ => rg1003_meets.2

def rg1004Implementation : Implementation rg1004Deliverable where
  subject := rg1004Checker
  fulfils := fun _ => rg1004_meets.2

def rg1005Implementation : Implementation rg1005Deliverable where
  subject := rg1005Checker
  fulfils := fun _ => rg1005_meets.2

def rg1006Implementation : Implementation rg1006Deliverable where
  subject := rg1006Checker
  fulfils := fun _ => rg1006_meets.2

def rg1011Implementation : Implementation rg1011Deliverable where
  subject := rg1011Checker
  fulfils := fun _ => rg1011_meets.2

def rg1012Implementation : Implementation rg1012Deliverable where
  subject := rg1012Checker
  fulfils := fun _ => rg1012_meets.2

def rg1013Implementation : Implementation rg1013Deliverable where
  subject := rg1013Checker
  fulfils := fun _ => rg1013_meets.2

def gateImplementation : Implementation gateDeliverable where
  subject := runChecker
  fulfils := fun _ => run_meets.2

def languageImplementation : Implementation languageDeliverable where
  subject := Regula.Language.decision
  fulfils := fun _ => Language.decision_meets.2

def fullGateImplementation : Implementation fullGateDeliverable where
  subject := Language.traced
  fulfils := fun _ => Language.gate_meets.2

def programImplementation : Implementation programDeliverable where
  subject := runProgram
  fulfils := fun _ => (Effects.run_meets_record (L := Unit) (E := Environment)).2

def ruleDeliverableRecords : List (IntentRecord (Checker Input Name)) :=
  [rg1001Deliverable.record, rg1002Deliverable.record, rg1003Deliverable.record,
    rg1004Deliverable.record, rg1005Deliverable.record, rg1006Deliverable.record,
    rg1011Deliverable.record, rg1012Deliverable.record, rg1013Deliverable.record]

theorem ruleDeliverables_cover_registry :
    ruleDeliverableRecords = registry.map (fun p => ruleRecord p.rule.spelling p.Violates) := by
  rfl

def rg1001Required : LeanIntent.Required rg1001Deliverable where
  theorems := [
    ⟨Witnesses.rg1001_adequate⟩,
    ⟨Witnesses.rg1001_noisy⟩,
    ⟨@Link.rg1001_exact⟩,
    ⟨@Link.rg1001_subject⟩,
    ⟨rg1001_meets⟩,
    ⟨rg1001_cases⟩]

def rg1002Required : LeanIntent.Required rg1002Deliverable where
  theorems := [
    ⟨Witnesses.rg1002_adequate⟩,
    ⟨Witnesses.rg1002_noisy⟩,
    ⟨@Link.rg1002_exact⟩,
    ⟨@Link.rg1002_subject⟩,
    ⟨rg1002_meets⟩,
    ⟨rg1002_cases⟩]

def rg1003Required : LeanIntent.Required rg1003Deliverable where
  theorems := [
    ⟨Witnesses.rg1003_adequate⟩,
    ⟨Witnesses.rg1003_noisy⟩,
    ⟨@Link.rg1003_exact⟩,
    ⟨@Link.rg1003_subject⟩,
    ⟨rg1003_meets⟩,
    ⟨rg1003_cases⟩]

def rg1004Required : LeanIntent.Required rg1004Deliverable where
  theorems := [
    ⟨Witnesses.rg1004_adequate⟩,
    ⟨Witnesses.rg1004_noisy⟩,
    ⟨@Link.rg1004_exact⟩,
    ⟨@Link.rg1004_subject⟩,
    ⟨rg1004_meets⟩,
    ⟨rg1004_cases⟩]

def rg1005Required : LeanIntent.Required rg1005Deliverable where
  theorems := [
    ⟨Witnesses.rg1005_adequate⟩,
    ⟨Witnesses.rg1005_noisy⟩,
    ⟨@Link.rg1005_exact⟩,
    ⟨@Link.rg1005_subject⟩,
    ⟨rg1005_meets⟩,
    ⟨rg1005_cases⟩]

def rg1006Required : LeanIntent.Required rg1006Deliverable where
  theorems := [
    ⟨Witnesses.rg1006_adequate⟩,
    ⟨Witnesses.rg1006_noisy⟩,
    ⟨@Link.rg1006_exact⟩,
    ⟨@Link.rg1006_subject⟩,
    ⟨rg1006_meets⟩,
    ⟨rg1006_cases⟩,
    ⟨@safe_reach_safe⟩,
    ⟨@helperForm_unreached⟩,
    ⟨@ctorIdxImpl_unreached⟩,
    ⟨Witnesses.base_safeMentionsSafe⟩,
    ⟨Witnesses.safeMentionsSafe_refutable⟩,
    ⟨@Link.rg1006_reports_named_not_partial⟩,
    ⟨@Link.rg1006_admits_helper⟩,
    ⟨@Link.rg1006_admits_ctorIdxImpl⟩,
    ⟨@rg1006_checker_refuses_loop⟩,
    ⟨rg1006_checker_refuses_forged_name⟩,
    ⟨rg1006_checker_refuses_partial_fixpoint⟩,
    ⟨rg1006_checker_admits_fix_theorem_and_lfp⟩,
    ⟨rg1006_checker_ctorIdx⟩]

def rg1011Required : LeanIntent.Required rg1011Deliverable where
  theorems := [
    ⟨Witnesses.rg1011_adequate⟩,
    ⟨Witnesses.rg1011_noisy⟩,
    ⟨@Link.rg1011_exact⟩,
    ⟨@Link.rg1011_subject⟩,
    ⟨@Link.rg1011_attributed⟩,
    ⟨@Link.check_eq_replaced⟩,
    ⟨@Link.rg1011_admits_neither⟩,
    ⟨@Link.rg1011_admits_ctorIdxDef⟩,
    ⟨rg1011_meets⟩,
    ⟨rg1011_cases⟩,
    ⟨rg1011_checker_refuses_extern⟩,
    ⟨rg1011_checker_reads_definitions⟩,
    ⟨rg1011_checker_refuses_foreign_csimp⟩,
    ⟨rg1011_checker_admits_claimed_csimp⟩,
    ⟨rg1011_checker_ctorIdx⟩]

def rg1012Required : LeanIntent.Required rg1012Deliverable where
  theorems := [
    ⟨Witnesses.rg1012_adequate⟩,
    ⟨Witnesses.rg1012_noisy⟩,
    ⟨@Link.rg1012_exact⟩,
    ⟨@Link.rg1012_subject⟩,
    ⟨rg1012_meets⟩,
    ⟨rg1012_cases⟩,
    ⟨Witnesses.rg1012_admits_theorems⟩,
    ⟨Witnesses.bangNamed_hygienic⟩,
    ⟨Witnesses.not_bangNamed_query⟩,
    ⟨rg1012_checker_refuses_panic⟩]

def rg1013Required : LeanIntent.Required rg1013Deliverable where
  theorems := [
    ⟨Witnesses.rg1013_adequate⟩,
    ⟨Witnesses.rg1013_noisy⟩,
    ⟨@Witnesses.rg1013_reads_modules⟩,
    ⟨@Link.rg1013_exact⟩,
    ⟨@Link.rg1013_subject⟩,
    ⟨rg1013_meets⟩,
    ⟨rg1013_cases⟩]

def gateRequired : LeanIntent.Required gateDeliverable where
  theorems := [
    ⟨Witnesses.gate_adequate⟩,
    ⟨gate_o4⟩,
    ⟨gate_o5⟩,
    ⟨Witnesses.no_claim_refused⟩,
    ⟨Witnesses.open_mention_refused⟩,
    ⟨Witnesses.always_pass_fails⟩,
    ⟨Witnesses.always_incomplete_fails⟩,
    ⟨@admit_ok_iff⟩,
    ⟨@admit_error_iff⟩,
    ⟨@run_refused⟩,
    ⟨@run_complete⟩,
    ⟨@run_pass_iff⟩,
    ⟨run_meets⟩,
    ⟨registry_rules⟩,
    ⟨@findings_nil_iff⟩,
    ⟨@registered_found⟩,
    ⟨rule_spellings⟩,
    ⟨@finding_guidance_nonblank⟩,
    ⟨ruleDeliverables_cover_registry⟩]

def languageRequired : LeanIntent.Required languageDeliverable where
  theorems := [
    ⟨Language.language_o2⟩,
    ⟨Language.language_o2Run⟩,
    ⟨Language.language_o3⟩,
    ⟨Language.language_o4⟩,
    ⟨Language.language_o5⟩,
    ⟨@Language.constant_fails⟩,
    ⟨@Language.admitted_iff⟩,
    ⟨Language.decision_meets⟩,
    ⟨@Language.decision_admitted_iff⟩,
    ⟨@Language.mem_offenders_iff⟩,
    ⟨@Language.mem_positions_iff⟩,
    ⟨@Language.dependency_not_admitted⟩,
    ⟨@Language.mathlib_not_admitted⟩,
    ⟨@Language.admitted_runs_no_project_code⟩,
    ⟨@Owner.refuses_named_kinds⟩,
    ⟨@Owner.refuses_decide_native⟩,
    ⟨@Owner.refuses_lakefile_lean⟩,
    ⟨@Owner.refuses_plugin_key⟩,
    ⟨Owner.admits_library_code⟩,
    ⟨Owner.admits_configuration_keys⟩]

def fullGateRequired : LeanIntent.Required fullGateDeliverable where
  theorems := [
    ⟨Language.fullGate_o2⟩,
    ⟨Language.fullGate_o2Run⟩,
    ⟨Language.fullGate_o3⟩,
    ⟨Language.fullGate_o4⟩,
    ⟨Language.fullGate_o5⟩,
    ⟨@Language.build_only_after_check⟩,
    ⟨@Language.full_needs_no_mathlib⟩,
    ⟨Language.gate_meets⟩,
    ⟨@Language.gate_exit_zero_iff⟩]

def programRequired : LeanIntent.Required programDeliverable where
  theorems := [
    ⟨@Effects.program_o2⟩,
    ⟨@Effects.program_o2Run⟩,
    ⟨@Effects.program_o3⟩,
    ⟨@Effects.program_o4⟩,
    ⟨@Effects.program_o5⟩,
    ⟨@Effects.constant_program_fails⟩,
    ⟨@Effects.refuser_fails⟩,
    ⟨@Effects.manufacturer_fails⟩,
    ⟨@Effects.misjudge_fails⟩,
    ⟨@Effects.manufacturedCopy_fails⟩,
    ⟨@Effects.manufacturedCopyAnswered_fails⟩,
    ⟨@Effects.uncheckedCopy_fails⟩,
    ⟨@Effects.uncheckedCopy_build_fails⟩,
    ⟨@Effects.act_after_readBack_fails⟩,
    ⟨@Effects.judgedCopy_stands⟩,
    ⟨@Effects.rewritten_stands⟩,
    ⟨@Effects.run_meets⟩,
    ⟨@Effects.run_meets_record⟩,
    ⟨@Effects.executed_meets⟩,
    ⟨@Effects.table_rows⟩,
    ⟨@Effects.run_plain_owed⟩,
    ⟨@Effects.run_outProof_owed⟩,
    ⟨@Effects.run_full_owed⟩,
    ⟨@Effects.plain_exit_zero⟩,
    ⟨@Effects.outProof_exit_zero⟩,
    ⟨@Effects.full_exit_zero⟩,
    ⟨@Effects.outProof_empty_refused⟩,
    ⟨@Effects.outProof_both_vars_refused⟩,
    ⟨@Effects.outProof_verdict_distinct_from_full⟩,
    ⟨@Effects.outProof_emptyTarget_witness⟩,
    ⟨@Effects.outProof_noSysroot_witness⟩,
    ⟨@Effects.read_what_lake_compiles⟩,
    ⟨@Effects.lake_takes_judged⟩,
    ⟨@Effects.read_no_link⟩,
    ⟨@Meaning.run_route⟩,
    ⟨Meaning.meaning⟩]

end RegulaSpecification.Required
