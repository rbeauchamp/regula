import RegulaPolicy.Acceptance
import RegulaCore.Account
import RegulaCore.Lint
import Regula.Website
import Regula.Checker.Producer
import Regula.Checker.RuleDiagnostics
import Regula.DiagnosticCodec
import Regula.SourceTexts
import Regula.ExecutionShare
import Regula.Checker.Common

/-! # Versioned result protocol

Versioned observation output and accepted-report rendering. JSON is display/transport
of scoped evidence, never a deserializable proof or whole-standard conformance certificate.
The accepted constructor requires the executed con-leche-inspired indexed finalization. -/
namespace Regula.Checker.ResultProtocol
open Lean
open RegulaPolicy.Guards (bind_eq_ok)

/-- This checker build's producer identity, written into every result envelope. -/
abbrev producer := Regula.Checker.Producer.identity

/-- Result schema 18 lists a toolchain `partial def` and the `_unsafe_rec` helper Lean compiles it
through as one trusted step: each `scope.toolchainBase` entry carries `implementations`, the
`partial` implementations its boundary carries that have no entry of their own because every root
that reaches one holds a boundary that carries it there (`RegulaPolicy.checked_toolchainBase`).
The coverage counts of `executionSummary` count such a pair once, as they already counted a pair
the project or a dependency owns. Earlier schemas gave the helper an entry and a count of its own.
Schema 17 records the assumptions about external systems that each declaration rests on:
a declaration record carries `assumptions` and `checkedOperations`, the declarations with the role
`assumption` or `checked` (`Regula.Assumption`) that the walk of the constants it uses, proofs
included, reaches from it in the replayed kernel (`RegulaPolicy.Assumptions.RestsOn`). Earlier
schemas wrote neither member.
Schema 16 adds the acceptance account's `contractEvidence`, the law observer's report
of each registration whose requirement reduces to a decision carrier (`accountJson`), and each
execution boundary's `exact`: the proof and the required proposition of its checked
correspondence, each as its exact term beside a display (`RegulaPolicy.CorrespondenceTerms`),
or `null`.
Schema 15 records the relation between surfaces that the manifest declares for RG1008:
each `surfaces` entry of an accepted project, and each surface of the manifest a project result
renders in `scope`, carries `decides`, the claimed surfaces whose registered decisions its
recorded contracts count toward, and the acceptance account carries
`countedContracts`, each recorded contract that an environment counts from another surface and
that decides a function it registers as a decision, with the surface of the function (`surface`)
and the surface the contract comes from (`source`). Earlier schemas wrote neither member.
Schema 14 records which dependencies the audit owns: each dependency of a rendered
snapshot carries `owned`, `true` for a path dependency in the root package's Git work tree, each
module of which the audit replays where a requested module imports it, except modules under the
checker's reserved prefixes, which are the checker's own code (`snapshotJson`), and the
acceptance account carries `trustedDependencies`, the packages of the dependencies that are not
owned or that provide a module under those prefixes, which the audit trusts (`accountJson`), and
each environment of the acceptance carries
`dependencyModules`, the modules of owned dependencies whose declarations it inspects
(`environmentJson`). Earlier schemas wrote none of these members, and the audit then owned no
dependency.
Schema 13 records the functions with a result of `Bool` or `BEq` that the two sides of
each decision registration share only through the declaration of the input type of the kind
(`RegulaPolicy.SharedNames.throughTypes`, `RegulaPolicy.StatementReading`): the
`shared` object of a declaration's `executableContract` and the `sharedDefinitions` object of each
`contracts` entry of the acceptance account carry the member `throughTypes`. Earlier schemas did
not write the member.
Schema 12 records the axioms that Lean's `collectAxioms` omits for each declaration: a
declaration record carries `tableOmissions`, the axioms that the declaration reaches in the
replayed kernel and `collectAxioms` does not report. Earlier schemas did not write the member.
Schema 11 records the functions that the specification of each decision registration
shares with its implementation or its acceptance predicate: a declaration's `executableContract`
carries `shared`, an object with the members `booleans` and `others`, each the names of the
shared functions of that class, sorted and without duplicates
(`RegulaPolicy.ExecutableContract.shared`, `RegulaPolicy.SharedNames`), and each `contracts`
entry of the acceptance account carries the same two lists as `sharedDefinitions`
(`accountJson`). Earlier schemas wrote neither member.
Schema 10 records the decision registration of each declaration: its `decisionResult`
is `decidable` or `other` for a declaration registered with `@[regula_decision]`, by whether its
result type is `Decidable _` (`RegulaPolicy.DecisionResult.spelling`), and `null` for any other.
Earlier schemas did not write the member.
Schema 9 records the decision kind of each registered contract: a declaration's
`executableContract` carries `kind` (`sound`, `complete`, `sound-and-complete`, or `null` for a
requirement that states none, `RegulaPolicy.DecisionKind.spelling`), and each `contracts` entry
of the acceptance account carries that spelling as `decisionKind` with `notEstablished`, the
direction a one-way kind leaves open (`accountJson`). Schemas before 9 wrote neither member.
Schema 8 can store what the roots of an environment's execution account share once,
and omits kernel-expression text. In a result file, the `execution` member of an environment
report is what `SharedExecution.internValue` writes for its roots' accounts: the shared form when
the reader returns the accounts from it (the `names` its roots reach, their `modules` and
`nameModules`, each edge channel as pairs of name indices, the `boundaries` records and
`unavailableCode`, each once, and `roots`, one entry per root), and otherwise the accounts in
full (`SharedExecution.restore?` states what each written value stands for); every observation
of each root is recoverable either way. Readers of this checker take the document through
`SharedExecution.read`, which rebuilds each root's account, so the document they see holds an
array of complete root accounts as before. `SharedExecution.read_write` proves that `read` of
the `Json` value the writer wrote is the document the writer was given. A reader holds the parse
of the file instead, which has that value's members but in general not its object trees; that
`read` of it returns a document with the members of the writer's is observed (`RegistryChecks`,
the `history` qualification), not proved. The writer treats every member named `execution` this
way, so the acceptance account's per-environment counts, which earlier schemas also named
`execution`, are `executionSummary` (`accountJson`); every other member of that name is a string
or `null`, which the writer leaves as it is. A declaration of a report and a declaration a
frontend transcript records carry `type`, the `repr` of the kernel type expression, only when the
audit was asked for it (`axiomGate --kernel-types`); `prettyType` is the declaration's type as
Lean prints it (`ProducerReport.declarationResultJson`, `Frontend.transcriptResultJson`). Earlier
schemas wrote each root's account in full, so a name, edge or boundary that several roots reach
was repeated for each, and always wrote that `repr`.
Schema 7 stores each source text once. A result file's top-level `sourceTexts` lists
every distinct source text of the document, and each `sourceText` member, wherever it occurs (a
source location of `diagnostics`, the `sourceAccount`, the sources, frontend transcripts, source
bindings and histories of `scope`, and the snapshots of `acceptance`), is the index of its text
in that list (`SourceTexts.intern`, `SourceTexts.intern_table`). Readers of this checker take the
document through `SourceTexts.expand`, which puts each text back in its member and leaves
`sourceTexts` `null` (`SourceTexts.expand_intern`); every other definition here concerns that
expanded document. Earlier schemas wrote the text in each member (`source`, `content`,
`sourceContent`, `before` and `after`), so a source location repeated its file's text.
Schema 6 writes every Lean name of the document, in `diagnostics`, `scope` and
`acceptance` alike, in one encoding (`RegistryCodec.printedNameJson`): the string Lean prints for
it, and, only for a name whose printed text Lean's parser does not read back as the name, its
structural components, an array of `["str", s]` and `["num", n]` innermost first
(`printedNameJson_roundtrip`, `printedNameJson_eq_str_iff`). In a declaration-policy finding of a
project audit, a file audit or a rule example (the rules `Policy.ruleForMember` decides),
`arguments.sourceDeclaration` is `null`, or, for a declaration Lean generated, the declaration
at the end of the chain it generated it from (`Findings.sourceName?`); such a finding keeps the
range of its own declaration when it has one, and otherwise is located at that declaration's range
when it has one and its module has a snapshot (`Findings.findingLocation`), and its `related` then
names its own module. Other declaration findings carry no attribution: a documentation
example's, a material-documentation one and the editor linter's record `null` and their
declaration's own location (`Findings.declarationLocation`).
Schema 5 attributes the toolchain's own boundaries to it: a boundary a toolchain
module (`Init`, `Std`, `Lean` or `Lake`, loaded from the toolchain's library) owns carries its
`toolchainOrigin` (formerly `nativeOrigin`, which only native-runtime boundaries carried), and
each `axiomGate` project and file result's `scope.toolchainBase` lists every such boundary once
for the whole audit, with the environments and roots that reach it (until schema 18 named a
folded `partial` implementation in the entries that carry it instead). Schema 4 inspected each
claimed executable's root in an environment of its own: a project `scope.surfaces[*]` entry's
`modules` and `report` cover only its library's environment (the library's modules other than
its claimed executables' roots), and each claimed executable has its own `executables[*]` entry
with its own `modules` and `report`. A report's `admission` also lists as `reused` the modules
its environment did not replay because a library's environment admitted them over the identical
import closure; a library's own report lists the modules of the claimed libraries it imports
there. The environment that replayed a module with at least one safe, total constant (neither
`unsafe` nor `partial`) is one whose `required` holds a key of that module and whose `reused`
does not list it. A module with no such constant has no key, so the result does not identify the
environment that replayed it. `modules` does not identify it either, since it lists every owned
module the environment did not reuse, loaded or not.
Where claimed libraries import one another, `reused` can hold one of the report's own claimed
modules, which an earlier environment replayed; `required` and `admitted` then keep that module's
keys, admitted by that earlier environment.
Schema 3 added, for agents, each diagnostic's `remedy`, the top-level `rules` (the
guidance of every rule that fired, once each), the stage evidence `stages` (the run's required
stages) and `stagesCompleted` (those that completed), and their derivation `complete` (every
stage of the run completed) and `stagesNotRun` (the stages that did not). Schema 2 omitted the
frozen configuration and dependency text from the snapshot (`snapshotJson`: a clean
dependency is identified by its pinned revision, a dirty one only by package and `dirty`
status) and imported-environment module lists (`acceptedJson`,
`ProducerReport.Environment.resultJson`); schema 1 embedded them. -/
def schemaVersion : Nat := 18

/-- Envelope identity of every result file. -/
def identityFields : List (String × Json) := RegistryCodec.identityFields producer schemaVersion

/-- `Account.Status`: `completed` carries an accepted account, so it cannot be written from
missing or incomplete evidence (`Account.Status.completed_accepted`). -/
abbrev Status := Regula.Checker.Account.Status

/-- The text of a result status in the result JSON. -/
def statusText (status : Status) : String := status.spelling

/-- A stage of a run (`RegulaPolicy.Stage`). -/
abbrev Stage := RegulaPolicy.Stage

/-- The name of each stage in the result JSON's stage lists. -/
def stageName : Stage → String
  | .configuration => "configuration" | .discovery => "discovery" | .build => "build"
  | .admission => "admission" | .declarationPolicy => "declarationPolicy"
  | .execution => "execution" | .transcript => "transcript" | .history => "history"
  | .origin => "origin" | .documentationPresence => "documentationPresence"
  | .documentScan => "documentScan" | .example => "example" | .graph => "graph"

/-- Every stage. -/
def allStages : List Stage :=
  [.configuration, .discovery, .build, .admission, .declarationPolicy, .execution, .transcript,
   .history, .origin, .documentationPresence, .documentScan, .example, .graph]

theorem mem_allStages (s : Stage) : s ∈ allStages := by
  cases s <;> simp [allStages]

/-- The stages a run in `mode` performs: exactly those `RegulaPolicy.requiredStages` requires
of every claim in that mode (`stagesOf_required`). -/
def stagesOf : EvidenceMode → List Stage
  | .freshProject | .incrementalProject =>
      [.configuration, .discovery, .build, .admission, .declarationPolicy, .execution,
       .transcript, .history, .origin, .documentationPresence]
  | .freshFile => [.discovery, .build, .admission, .declarationPolicy, .execution,
      .transcript, .history, .origin]
  | .documentationExample => [.discovery, .build, .documentScan, .example]
  | .serializedGraph => [.configuration, .discovery, .build, .graph]
  | .editorSnapshot => [.discovery, .admission, .declarationPolicy, .execution,
      .transcript, .history, .origin, .documentationPresence]

theorem stagesOf_required (c : RegulaPolicy.Claim) :
    RegulaPolicy.requiredStages c = stagesOf c.val.mode := by
  unfold RegulaPolicy.requiredStages stagesOf
  cases c.val.mode <;> rfl

/-- The stages a `--with-docs` project audit adds after the project stages. -/
def documentationStages : List Stage := [.documentScan, .example]

/-- The position of a stage in every run: each mode's stages, and the documentation stages
after the project stages, occur in this order (`stagesOf_ordered`, `withDocs_ordered`). -/
def stageRank : Stage → Nat
  | .configuration => 0 | .discovery => 1 | .build => 2 | .admission => 3
  | .declarationPolicy => 4 | .execution => 5 | .transcript => 6 | .history => 7
  | .origin => 8 | .documentationPresence => 9 | .documentScan => 10 | .example => 11
  | .graph => 12

theorem stagesOf_ordered (mode : EvidenceMode) :
    (stagesOf mode).Pairwise (fun a b => stageRank a < stageRank b) := by
  cases mode <;> decide

theorem withDocs_ordered :
    (stagesOf .freshProject ++ documentationStages).Pairwise
      (fun a b => stageRank a < stageRank b) := by
  decide

/-- The earliest stage every finding of `id` in `mode` that stops its run (`stops`) leaves
unfinished for the evidence it concerns; that stage and every later one cannot have completed.
RG2001 blocks admission: an environment the audit cannot run in fails discovery, the build or the
loading of the built environment for inspection, and the writer records only the earlier stages
that completed. RG3001 has none: its verdict comes from the execution stage, which completed. -/
def blockedStage (mode : EvidenceMode) : RuleId → Option Stage
  | .environment => some .admission
  | .configuration | .communityConfiguration => some .configuration
  | .sourceBuild => some .build
  | .coverage => some .admission
  | .admission => some (match mode with | .documentationExample => .example | _ => .admission)
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .decisionContract | .sharedTest =>
    some .declarationPolicy
  | .executionBoundary => some .execution
  | .executionUnresolved => none
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample => some .example
  | .moduleDocumentation | .materialDocumentation | .materialIntent => some .documentationPresence

/-- A finding that stops its run at its `blockedStage`: an incomplete finding, which leaves that
stage unfinished, and a workspace refusal of either impact (RG2002 configuration, RG2003 source
build), after which no later stage runs. -/
def stops (f : Finding) : Bool :=
  match f.1 with
  | .configuration | .sourceBuild => true
  | _ => f.2.impact == .incomplete

/-- Stage `s` is blocked: a finding among `findings` stops the run at `s` or an earlier stage, or
comes from an earlier phase of a composed run, every stage of the finding's mode preceding `s`:
a `--with-docs` run starts its documentation stages only after its project stages produced no
finding. -/
def blocked (findings : List Finding) (s : Stage) : Bool :=
  findings.any fun f =>
    (stagesOf f.2.mode).all (stageRank · < stageRank s) ||
    stops f && match blockedStage f.2.mode f.1 with
      | some b => stageRank b ≤ stageRank s
      | none => false

/-- The stages of `required` a result records as completed: every one for an accepted result,
whose account executed every stage its claim requires (`stagesOf_required`); otherwise those its
writer recorded in `completed` that no finding blocks. -/
def completedStages (accepted : Bool) (required completed : List Stage) (findings : List Finding) :
    List Stage :=
  if accepted then required else required.filter fun s => s ∈ completed && !blocked findings s

/-- The stages of `required` missing from `completed`, in run order. -/
def notRun (required completed : List Stage) : List Stage :=
  required.filter fun s => s ∉ completed

/-- An unaccepted result reports no stage as not run exactly when its writer recorded every
required stage as completed and no finding blocks one. -/
theorem notRun_completedStages_eq_nil_iff (required completed : List Stage)
    (findings : List Finding) :
    notRun required (completedStages false required completed findings) = [] ↔
      ∀ s ∈ required, s ∈ completed ∧ blocked findings s = false := by
  simp only [notRun, completedStages, Bool.false_eq_true, ↓reduceIte, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, not_and,
    Bool.not_eq_false, decide_implies, Bool.decide_eq_true, dite_eq_ite, Bool.ite_true_right,
    List.filter_eq_nil_iff, Bool.or_eq_true, decide_eq_false_iff_not, not_or, Decidable.not_not,
    Bool.not_eq_true]
  exact ⟨fun h s hs => (h s hs).2, fun h s hs => ⟨hs, h s hs⟩⟩

/-- Re-deriving from the recorded completed stages reproduces them. -/
theorem completedStages_idem (accepted : Bool) (required completed : List Stage)
    (findings : List Finding) :
    completedStages accepted required (completedStages accepted required completed findings)
        findings = completedStages accepted required completed findings := by
  cases accepted
  · simp only [completedStages, Bool.false_eq_true, ite_false]
    apply List.filter_congr
    intro s hs
    simp [List.mem_filter, hs]
  · rfl

/-- The accepted flag that the writer and admission both derive from a result's `status`
spelling, which reads `completed` exactly for an accepted account
(`Account.Status.spelling_eq_completed_iff`). -/
def acceptedStatus (status : String) : Bool := status == "completed"

/-- The agent guidance members of every result envelope, derived by this one function for the
writer and for admission: `stages` (the run's required stages), `stagesCompleted`
(`completedStages`), `complete` (every required stage completed,
`notRun_completedStages_eq_nil_iff`), `stagesNotRun` (the stages that did not, so fixing the
findings can reveal more) and `rules` (the guidance of every rule of the diagnostics). -/
def guidanceFields (accepted : Bool) (required completed : List Stage) (findings : List Finding) :
    List (String × Json) :=
  let done := completedStages accepted required completed findings
  let missing := notRun required done
  [("stages", toJson (required.map stageName)), ("stagesCompleted", toJson (done.map stageName)),
   ("complete", .bool missing.isEmpty), ("stagesNotRun", toJson (missing.map stageName)),
   ("rules", RegistryCodec.rulesJson (findings.map (·.1)))]

/-- Admission derives the members again from the `stagesCompleted` a writer recorded; that
re-derivation reproduces the writer's members, so every written result passes the check. -/
theorem guidanceFields_recorded (accepted : Bool) (required completed : List Stage)
    (findings : List Finding) :
    guidanceFields accepted required (completedStages accepted required completed findings)
        findings = guidanceFields accepted required completed findings := by
  unfold guidanceFields
  rw [completedStages_idem]

/-- The `sourceTexts` member of every result document a checker builds: `null`, which
`writeDocument` replaces by the document's distinct source texts (`SourceTexts.intern`). -/
def sourceTextsField : String × Json := (SourceTexts.tableKey, .null)

/-- Completed is scoped observation, never a synonym for whole-standard conformance. A
completed envelope takes its mode from the status's account, not from `mode`. `expected` are
the run's required stages and `completed` those its writer recorded as completed. The guidance
members are derived from the diagnostics exactly as written, in `sortFindings` order. This is the
document before its source texts are stored once (`sourceTextsField`). -/
def resultJson (scope : Json) (mode : EvidenceMode) (status : Status)
    (findings : Array Finding) (expected completed : List Stage) (unresolved : Array String) :
    Json :=
  let mode := match status with
    | .completed account => account.val.mode
    | _ => mode
  let findings := sortFindings findings.toList
  Json.mkObj (identityFields ++ [
    ("scope", scope), ("mode", .str (RegistryCodec.modeText mode)),
    ("status", .str (statusText status)),
    ("diagnostics", toJson (findings.map RegistryCodec.diagnosticJson)),
    ("unresolved", toJson unresolved), sourceTextsField] ++
    guidanceFields (acceptedStatus (statusText status)) expected completed findings)

/-- Every document `resultJson` builds has exactly one `sourceTexts` member, `null`, as
`SourceTexts.intern` requires, and keeps it when its execution accounts are written
(`SharedExecution.slots_intern`): by `SourceTexts.intern_isOk_iff`, `writeDocument` refuses such
a document only if a `sourceText` member of that written form is not a string. A member added to
the document afterwards (`request`, `effective`, `sourceAccount`, `acceptance`) is outside this
statement. -/
theorem resultJson_slots (scope : Json) (mode : EvidenceMode) (status : Status)
    (findings : Array Finding) (expected completed : List Stage) (unresolved : Array String) :
    SourceTexts.slots (resultJson scope mode status findings expected completed unresolved) =
      [.null] := by
  simp [resultJson, Json.mkObj, SourceTexts.slots, identityFields, RegistryCodec.identityFields,
    sourceTextsField, guidanceFields]
  rfl

/-- The stage named `name`. -/
def parseStage (name : String) : Except String Stage :=
  match allStages.find? (stageName · == name) with
  | some stage => .ok stage
  | none => .error s!"unknown stage {name}"

/-- Every stage name parses back to its stage, so admission decodes the stages a writer recorded. -/
theorem parseStage_stageName (s : Stage) : parseStage (stageName s) = .ok s := by
  cases s <;> rfl

/-- The required stage lists of a result in `mode`: the mode's stages (`stagesOf_required`),
for a fresh project also those of a `--with-docs` run, and with no mode (a destination
invalidated before its configuration was validated) every stage. -/
def runStages : Option EvidenceMode → List (List Stage)
  | some .freshProject => [stagesOf .freshProject, stagesOf .freshProject ++ documentationStages]
  | some mode => [stagesOf mode]
  | none => [allStages]

/-- The rule and impact of each finding, the form in which `Lint.Observation` records a run's
findings. -/
def impacts (findings : List Finding) : List (RuleId × Impact) :=
  findings.map fun f => (f.1, f.2.impact)

/-- Whether a result of `status` can carry `findings`: none for `completed` and `classified`, at
least one for `rejected` and every one a violation, any for `incomplete`, and no other status
(`statusAgrees_completed`). Every status `Lint.Observation.status` decides agrees with the
observation's findings (`statusAgrees_observation`), and apart from `completed`, whose observation
carries an accepted account, every status that agrees with them is one it decides from them
(`statusAgrees_iff`). -/
def statusAgrees (status : String) (findings : List Finding) : Bool :=
  match status with
  | "completed" | "classified" => findings.isEmpty
  | "rejected" => !findings.isEmpty && findings.all (·.2.impact == .violation)
  | "incomplete" => true
  | _ => false

/-- A `completed` result agrees with its findings exactly when it has none. -/
theorem statusAgrees_completed (findings : List Finding) :
    statusAgrees "completed" findings = true ↔ findings = [] := by
  simp [statusAgrees]

/-- The tally of a list of findings counts no incomplete finding and at least one violation
exactly when the list is not empty and every finding is a violation. -/
theorem tally_rejected_iff (findings : List Finding) :
    (Lint.tally ((impacts findings).map (·.2))).incomplete = 0 ∧
        0 < (Lint.tally ((impacts findings).map (·.2))).violations ↔
      findings ≠ [] ∧ ∀ f ∈ findings, f.2.impact = .violation := by
  have key : ∀ f : Finding, f.2.impact ≠ .incomplete ↔ f.2.impact = .violation := by
    intro f; cases f.2.impact <;> simp
  simp only [Lint.tally_eq, impacts, List.map_map, Function.comp_def, List.length_eq_zero_iff,
    List.filter_eq_nil_iff, List.mem_map, List.length_pos_iff, ne_eq]
  constructor
  · rintro ⟨hi, hv⟩
    refine ⟨fun h => by simp [h] at hv,
      fun f hf => (key f).mp fun h => by simpa [h] using hi _ ⟨f, hf, rfl⟩⟩
  · rintro ⟨hne, hall⟩
    refine ⟨fun i ⟨f, hf, he⟩ => by subst he; simp [hall f hf], fun h => ?_⟩
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil findings hne
    have := h _ ⟨f, hf, rfl⟩
    simp [hall f hf] at this

/-- The status an observation decides agrees with the findings it records: a result whose
writer writes an observation's status and the findings that observation records is never refused
for its status. -/
theorem statusAgrees_observation (o : Lint.Observation) (findings : List Finding)
    (h : o.findings = impacts findings) : statusAgrees o.status.spelling findings = true := by
  cases o with
  | accepted a =>
    simp only [Lint.Observation.findings, impacts] at h
    simp [Lint.Observation.status, Account.Status.spelling, statusAgrees,
      List.map_eq_nil_iff.mp h.symm]
  | classified =>
    simp only [Lint.Observation.findings, impacts] at h
    simp [Lint.Observation.status, Account.Status.spelling, statusAgrees,
      List.map_eq_nil_iff.mp h.symm]
  | refused fs u =>
    simp only [Lint.Observation.findings] at h
    subst h
    simp only [Lint.Observation.status, Lint.Observation.tally, Lint.Observation.findings]
    by_cases hc : u = false ∧ (Lint.tally ((impacts findings).map (·.2))).incomplete = 0 ∧
        0 < (Lint.tally ((impacts findings).map (·.2))).violations
    · simp only [hc, and_self, ↓reduceIte]
      have := (tally_rejected_iff findings).mp ⟨hc.2.1, hc.2.2⟩
      simp [Account.Status.spelling, statusAgrees, this.1, List.all_eq_true]
      exact fun f hf => this.2 f hf
    · simp only [hc, ↓reduceIte]
      simp [Account.Status.spelling, statusAgrees]

/-- For every status but `completed`, a result's status agrees with its findings exactly when an
observation that records those findings' rules and impacts decides that status. A `completed`
observation carries an accepted account, so `statusAgrees_completed` states that case instead. -/
theorem statusAgrees_iff (status : String) (findings : List Finding)
    (h : status ≠ "completed") :
    statusAgrees status findings = true ↔
      ∃ o : Lint.Observation, o.status.spelling = status ∧ o.findings = impacts findings := by
  constructor
  · intro ha
    unfold statusAgrees at ha
    split at ha
    · exact absurd rfl h
    · exact ⟨.classified, rfl, by simp_all [Lint.Observation.findings, impacts]⟩
    · refine ⟨.refused (impacts findings) false, ?_, rfl⟩
      have hr : findings ≠ [] ∧ ∀ f ∈ findings, f.2.impact = .violation := by
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          List.all_eq_true, beq_iff_eq] at ha
        exact ha
      have := (tally_rejected_iff findings).mpr hr
      simp only [Lint.Observation.status, Lint.Observation.tally, Lint.Observation.findings]
      simp [this, Account.Status.spelling]
    · refine ⟨.refused (impacts findings) true, ?_, rfl⟩
      simp [Lint.Observation.status, Account.Status.spelling]
    · exact absurd ha (by simp)
  · rintro ⟨o, rfl, ho⟩
    exact statusAgrees_observation o findings ho

/-- The stages a `classified` result of `mode` records as completed, one list for each writer
that writes `classified`: a file audit that found nothing without a conforming claim
(`AxiomGate`, every stage of `freshFile`), a policy example that elaborated without a finding
(`RuleExamples.inspectNegative`, discovery through declaration policy) and a documentation
example run whose fences classify (`RuleExamples.documentation`, every stage of
`documentationExample`). -/
def classifiedStages : Option EvidenceMode → List (List Stage)
  | some .freshFile => [stagesOf .freshFile, [.discovery, .build, .admission, .declarationPolicy]]
  | some .documentationExample => [stagesOf .documentationExample]
  | _ => []

/-- The keys of the members `guidanceFields` writes, in its order (`guidanceFields_keys`). -/
def guidanceKeys : List String := ["stages", "stagesCompleted", "complete", "stagesNotRun", "rules"]

theorem guidanceFields_keys (accepted : Bool) (required completed : List Stage)
    (findings : List Finding) :
    (guidanceFields accepted required completed findings).map (·.1) = guidanceKeys := rfl

/-- Whether each recorded member has the name of the expected member at its place and a value
that conforms to the expected value (`JsonAgreement.conforms`, the recorded value first), and the
two lists have the same length (`membersConform_iff`). -/
def membersConform : List (String × Json) → List (String × Json) → Bool
  | [], [] => true
  | (name, value) :: rest, (expectedName, expected) :: others =>
      name == expectedName && JsonAgreement.conforms value expected && membersConform rest others
  | _, _ => false

/-- Each recorded member has the name of the expected member at its place and a value that
conforms to the expected value, and the two lists have the same length. -/
def MembersConform (recorded expected : List (String × Json)) : Prop :=
  recorded.length = expected.length ∧
    ∀ pair ∈ recorded.zip expected,
      pair.1.1 = pair.2.1 ∧ JsonAgreement.Conforms pair.1.2 pair.2.2

theorem membersConform_iff (recorded expected : List (String × Json)) :
    membersConform recorded expected = true ↔
      MembersConform recorded expected := by
  unfold MembersConform
  induction recorded generalizing expected with
  | nil => cases expected <;> simp [membersConform]
  | cons member rest step =>
    cases expected with
    | nil => simp [membersConform]
    | cons want others =>
      obtain ⟨name, value⟩ := member
      obtain ⟨expectedName, expectedValue⟩ := want
      simp only [membersConform, Bool.and_eq_true, beq_iff_eq, step, JsonAgreement.conforms_iff,
        List.length_cons, Nat.add_right_cancel_iff, List.zip_cons_cons, List.forall_mem_cons]
      unfold JsonAgreement.Conforms
      constructor
      · rintro ⟨⟨same, conforming⟩, length, each⟩
        exact ⟨length, ⟨same, conforming⟩, each⟩
      · rintro ⟨length, ⟨same, conforming⟩, each⟩
        exact ⟨⟨same, conforming⟩, length, each⟩

/-- The members of a result envelope that `admitGuidance` decides on, as `readGuidance` decodes
them. -/
structure Guidance where
  /-- The `status` text. -/
  status : String
  /-- The `mode`, or `none` for `null`. -/
  mode : Option EvidenceMode
  /-- `request.kind` is `projectWithDocs`; read only for a result with a mode, else `false`. -/
  withDocs : Bool
  /-- The stages of `stages`. -/
  required : List Stage
  /-- The stages of `stagesCompleted`. -/
  completed : List Stage
  /-- The decoded `diagnostics`. -/
  findings : List Finding
  /-- The recorded value of each `guidanceKeys` member, under its key, in that order. -/
  members : List (String × Json)

/-- `ok`, or the refusal `problem`. -/
def requireThat (ok : Bool) (problem : String) : Except String Unit :=
  if ok then .ok () else .error problem

theorem requireThat_bind_eq_ok {α : Type} (ok : Bool) (problem : String)
    (rest : Except String α) (a : α) :
    (requireThat ok problem >>= fun _ => rest) = .ok a ↔ ok = true ∧ rest = .ok a := by
  cases ok <;> simp [requireThat, bind, Except.bind]

theorem requireThat_eq_ok (ok : Bool) (problem : String) :
    requireThat ok problem = .ok () ↔ ok = true := by
  cases ok <;> simp [requireThat]

/-- The schema version is this one (`JsonAgreement.conforms`, the received value first). -/
def readSchema (j : Json) : Except String Unit :=
  requireThat ((j.getObjVal? "schemaVersion").toOption.any
      (JsonAgreement.conforms · (toJson schemaVersion)))
    "unsupported result schema"

/-- The `status` text. -/
def readStatus (j : Json) : Except String String := do
  (← j.getObjVal? "status").getStr?

/-- The `mode`: `none` for `null`, else a mode (`RegistryCodec.parseMode`). -/
def readMode (j : Json) : Except String (Option EvidenceMode) := do
  match ← j.getObjVal? "mode" with
  | .null => pure none
  | mode => some <$> RegistryCodec.parseMode (← mode.getStr?)

/-- Whether a result with a mode records a `projectWithDocs` request; `false` without a mode. -/
def readWithDocs (j : Json) : Except String Bool := do
  if (← readMode j).isSome then
    pure ((← (← (← j.getObjVal? "request").getObjVal? "kind").getStr?) == "projectWithDocs")
  else pure false

/-- The stages of the member `key`, each entry a stage name (`parseStage`). -/
def readStages (j : Json) (key : String) : Except String (List Stage) := do
  (← (← j.getObjVal? key).getArr?).toList.mapM fun name => do parseStage (← name.getStr?)

/-- The findings of `diagnostics`, each decoded to its canonical indexed form
(`DiagnosticCodec.parseDiagnostic`, which includes the finding's `remedy` and `text`). -/
def readFindings (j : Json) : Except String (List Finding) := do
  (← (← j.getObjVal? "diagnostics").getArr?).toList.mapM DiagnosticCodec.parseDiagnostic

/-- The recorded value of each `guidanceKeys` member, under its key. -/
def readMembers (j : Json) : Except String (List (String × Json)) :=
  guidanceKeys.mapM fun key => do pure (key, ← j.getObjVal? key)

/-- Decode the members `admitGuidance` decides on, each by its own reader. -/
def readGuidance (j : Json) : Except String Guidance := do
  readSchema j
  let status ← readStatus j
  let mode ← readMode j
  let withDocs ← readWithDocs j
  let required ← readStages j "stages"
  let completed ← readStages j "stagesCompleted"
  let findings ← readFindings j
  let members ← readMembers j
  pure { status, mode, withDocs, required, completed, findings, members }

/-- What each reader returned for a decoded envelope. -/
theorem readGuidance_eq_ok {j : Json} {g : Guidance} (h : readGuidance j = .ok g) :
    readSchema j = .ok () ∧ readStatus j = .ok g.status ∧ readMode j = .ok g.mode ∧
      readWithDocs j = .ok g.withDocs ∧ readStages j "stages" = .ok g.required ∧
      readStages j "stagesCompleted" = .ok g.completed ∧ readFindings j = .ok g.findings ∧
      readMembers j = .ok g.members := by
  simp only [readGuidance, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨⟨⟩, schema, status, hs, mode, hm, docs, hd, required, hr, completed, hc, findings,
    hf, members, hmem, rfl⟩ := h
  exact ⟨schema, hs, hm, hd, hr, hc, hf, hmem⟩

/-- Whether findings are in run order: their entries (`Finding.entry`) are those
`Feedback.sortEntries` gives, the order of `sortFindings`, which every writer writes
(`sortFindings_entries`). -/
def inRunOrder (findings : List Finding) : Bool :=
  decide (findings.map Finding.entry = Feedback.sortEntries (findings.map Finding.entry))

/-- Findings are in run order exactly when each entry may precede every later one
(`Feedback.Entry.le`). -/
theorem inRunOrder_iff (findings : List Finding) :
    inRunOrder findings = true ↔
      (findings.map Finding.entry).Pairwise fun a b => Feedback.Entry.le a b = true := by
  unfold inRunOrder
  rw [decide_eq_true_iff]
  constructor
  · intro sorted
    rw [sorted]
    exact Feedback.sortEntries_sorted _
  · intro sorted
    apply List.Perm.eq_of_pairwise (le := fun a b => Feedback.Entry.le a b = true)
    · intro a b _ _ ab ba
      exact Feedback.Entry.eq_of_cmp (Std.OrientedCmp.isLE_antisymm ab ba)
    · exact sorted
    · exact Feedback.sortEntries_sorted _
    · exact (Feedback.sortEntries_perm _).symm

/-- The findings every writer writes are in run order. -/
theorem inRunOrder_sortFindings (findings : List Finding) :
    inRunOrder (sortFindings findings) = true := by
  rw [inRunOrder_iff, sortFindings_entries]
  exact Feedback.sortEntries_sorted _

/-- The decision of `admitGuidance` on decoded members, stated by `guidanceVerdict_eq_ok_iff`:
`stages` are the required stages of the result's `mode` (`runStages`), and for a result with a
mode its documentation stages are exactly those of a `projectWithDocs` request; a result without
a mode has exactly the form `invalidateResults` writes for a destination whose configuration was
not yet validated: `incomplete`, without a finding or a completed stage; the status agrees with
the findings (`statusAgrees`), so a `completed` or `classified` result has none; the findings are in
run order (`inRunOrder`), the order `sortFindings` gives every writer; a `classified`
result records the completed stages of one of its writers (`classifiedStages`); the guidance
members conform to their derivation by the writer's own `guidanceFields` (`membersConform`); and
an `incomplete` result without an incomplete finding reports a stage not run. -/
def guidanceVerdict (g : Guidance) : Except String Unit := do
  requireThat ((runStages g.mode).contains g.required)
    "stages are not the required stages of the result's mode"
  requireThat (g.mode.isNone ||
      g.withDocs == (g.required == stagesOf .freshProject ++ documentationStages))
    "stages are not the required stages of the result's request"
  requireThat
    (g.mode.isSome || g.status == "incomplete" && g.findings.isEmpty && g.completed.isEmpty)
    "a result without a mode is not the invalidated result of an unvalidated configuration"
  let incomplete := (g.findings.filter (·.2.impact == .incomplete)).length
  requireThat (statusAgrees g.status g.findings)
    s!"a {g.status} result cannot carry its {g.findings.length} findings ({incomplete} incomplete)"
  requireThat (inRunOrder g.findings) "result findings are not in run order"
  requireThat (g.status != "classified" || (classifiedStages g.mode).contains g.completed)
    "a classified result records completed stages that no classified result records"
  let expected := guidanceFields (acceptedStatus g.status) g.required g.completed g.findings
  let differing := (g.members.zip expected).find? fun (member, want) =>
    !(member.1 == want.1 && JsonAgreement.conforms member.2 want.2)
  let key := (differing.map (·.1.1)).getD "guidance"
  requireThat (membersConform g.members expected) s!"noncanonical result {key}"
  requireThat (g.status != "incomplete" || g.findings.any (·.2.impact == .incomplete) ||
      !(notRun g.required g.completed).isEmpty)
    "incomplete result without an incomplete finding reports every stage as run"

/-- The required stages are never missing from themselves. -/
theorem notRun_self (required : List Stage) : notRun required required = [] := by
  simp [notRun, List.filter_eq_nil_iff]

/-- What `guidanceVerdict` accepts, for every decoded envelope. -/
theorem guidanceVerdict_eq_ok_iff (g : Guidance) :
    guidanceVerdict g = .ok () ↔
      g.required ∈ runStages g.mode ∧
      (g.mode.isSome →
        g.withDocs = (g.required == stagesOf .freshProject ++ documentationStages)) ∧
      (g.mode = none → g.status = "incomplete" ∧ g.findings = [] ∧ g.completed = []) ∧
      statusAgrees g.status g.findings = true ∧
      (g.findings.map Finding.entry).Pairwise (fun a b => Feedback.Entry.le a b = true) ∧
      (g.status = "classified" → g.completed ∈ classifiedStages g.mode) ∧
      MembersConform g.members
        (guidanceFields (acceptedStatus g.status) g.required g.completed g.findings) ∧
      (g.status = "incomplete" → (∃ f ∈ g.findings, f.2.impact = .incomplete) ∨
        notRun g.required g.completed ≠ []) := by
  simp only [guidanceVerdict, requireThat_bind_eq_ok, requireThat_eq_ok, ← membersConform_iff,
    inRunOrder_iff]
  cases hm : g.mode <;>
    simp [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, List.any_eq_true,
      bne_iff_ne, ne_eq, and_assoc, Decidable.imp_iff_not_or, or_assoc]

/-- The guidance members of a run that completed every required stage, with no finding. -/
def completedMembers (required : List Stage) : List (String × Json) :=
  [("stages", toJson (required.map stageName)),
   ("stagesCompleted", toJson (required.map stageName)),
   ("complete", .bool true), ("stagesNotRun", toJson ([] : List String)),
   ("rules", RegistryCodec.rulesJson [])]

/-- A `completed` envelope is admitted exactly when it has a mode whose required stages its
`stages` are, with the documentation stages of its request, no finding, and members that conform
to those of a run that completed every one of those stages (`completedMembers`): `stagesCompleted`
the same stages, `complete` true, no stage in `stagesNotRun` and no rule guidance. -/
theorem guidanceVerdict_completed (g : Guidance) (h : g.status = "completed") :
    guidanceVerdict g = .ok () ↔
      (∃ mode, g.mode = some mode ∧ g.required ∈ runStages (some mode) ∧
        g.withDocs = (g.required == stagesOf .freshProject ++ documentationStages)) ∧
      g.findings = [] ∧
      MembersConform g.members (completedMembers g.required) := by
  have expected : ∀ completed,
      guidanceFields (acceptedStatus "completed") g.required completed [] =
        completedMembers g.required := by
    intro completed
    simp [guidanceFields, completedStages, acceptedStatus, notRun_self, completedMembers]
  rw [guidanceVerdict_eq_ok_iff, h, statusAgrees_completed]
  cases hm : g.mode with
  | none => simp
  | some mode =>
    constructor
    · rintro ⟨hr, hw, -, hf, -, -, hmem, -⟩
      rw [hf, expected] at hmem
      exact ⟨⟨mode, rfl, hr, hw rfl⟩, hf, hmem⟩
    · rintro ⟨⟨m, hm', hr, hw⟩, hf, hmem⟩
      cases hm'
      rw [hf, expected]
      exact ⟨hr, fun _ => hw, by simp, rfl, by simp, by simp, hmem, by simp⟩

/-- No stage that a finding of an admitted envelope blocks is among the stages whose names its
recorded `stagesCompleted` must conform to (`guidanceVerdict_eq_ok_iff`): a `completed` result has
no finding, and every other status records only stages no finding blocks. -/
theorem guidanceVerdict_unblocked (g : Guidance) (h : guidanceVerdict g = .ok ()) :
    ∀ s ∈ completedStages (acceptedStatus g.status) g.required g.completed g.findings,
      blocked g.findings s = false := by
  have agrees := ((guidanceVerdict_eq_ok_iff g).mp h).2.2.2.1
  intro s hs
  cases ha : acceptedStatus g.status
  · simp only [completedStages, ha, Bool.false_eq_true, ↓reduceIte, List.mem_filter,
      Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2.2
  · have : g.status = "completed" := by simpa [acceptedStatus] using ha
    rw [this, statusAgrees_completed] at agrees
    simp [blocked, agrees]

/-- Admit a result envelope's agent members in the registry-export style: its object trees are
search trees at each depth (`JsonAgreement.regular`), so each name is found once and no member is
hidden from a lookup; then decode them (`readGuidance`) and decide on them (`guidanceVerdict`).
`admitGuidance_eq_ok_iff` states what it admits of every `Json` value, `admitGuidance_completed`
what it admits of a `completed` result, `admitGuidance_completed_diagnostics` that such a result's
only `diagnostics` member is empty, and `guidanceVerdict_unblocked` that no stage a finding blocks
is reported as run. `statusAgrees_observation` states that a writer that writes an observation's
status with the findings that observation records passes the status check; that each writer
does so is read from its code, not proved. This is consistency against writer regressions and
omissions, not authenticity: a report deliberately edited to be self-consistent, such as a
rewritten `request.kind`, passes. -/
def admitGuidance (j : Json) : Except String Unit := do
  requireThat (JsonAgreement.regular j) "result object trees are not search trees"
  guidanceVerdict (← readGuidance j)

/-- What `admitGuidance` admits, for every `Json` value: one whose object trees are search
trees, whose members decode, and whose decoded members `guidanceVerdict` accepts
(`guidanceVerdict_eq_ok_iff`). -/
theorem admitGuidance_eq_ok_iff (j : Json) :
    admitGuidance j = .ok () ↔
      JsonAgreement.Regular j ∧ ∃ g, readGuidance j = .ok g ∧ guidanceVerdict g = .ok () := by
  unfold admitGuidance
  rw [requireThat_bind_eq_ok, bind_eq_ok, JsonAgreement.regular_iff]

/-- What `admitGuidance` admits of a `Json` value whose `status` is `completed`: search trees,
decoded members, a mode whose required stages its `stages` are (with the documentation stages
of its request), no finding, and the members of a run that completed every required stage
(`guidanceVerdict_completed`). -/
theorem admitGuidance_completed (j : Json) (h : readStatus j = .ok "completed") :
    admitGuidance j = .ok () ↔
      JsonAgreement.Regular j ∧ ∃ g, readGuidance j = .ok g ∧
        (∃ mode, g.mode = some mode ∧ g.required ∈ runStages (some mode) ∧
          g.withDocs = (g.required == stagesOf .freshProject ++ documentationStages)) ∧
        g.findings = [] ∧
        MembersConform g.members (completedMembers g.required) := by
  rw [admitGuidance_eq_ok_iff]
  constructor
  · rintro ⟨regular, g, read, verdict⟩
    have status : g.status = "completed" := by
      have := (readGuidance_eq_ok read).2.1
      rw [h] at this
      exact (Except.ok.inj this).symm
    exact ⟨regular, g, read, (guidanceVerdict_completed g status).mp verdict⟩
  · rintro ⟨regular, g, read, rest⟩
    have status : g.status = "completed" := by
      have := (readGuidance_eq_ok read).2.1
      rw [h] at this
      exact (Except.ok.inj this).symm
    exact ⟨regular, g, read, (guidanceVerdict_completed g status).mpr rest⟩

/-- The members of a result that `admitGuidance` reads: its schema, status, mode, request,
findings and guidance members. -/
def guidanceInputKeys : List String :=
  ["schemaVersion", "status", "mode", "request", "diagnostics"] ++ guidanceKeys

/-- The members of `j` that `admitGuidance` reads, as Lean's lookup finds them, in an object of
their own. A reader that decides on a result by its members alone admits this object, so its
decision is unchanged by the result's other members. -/
def guidanceInput (j : Json) : Json :=
  Json.mkObj (guidanceInputKeys.filterMap fun key => (j.getObjVal? key).toOption.map (key, ·))

theorem mapM_eq_ok_nil {α β : Type} {f : α → Except String β} {l : List α}
    (h : l.mapM f = .ok []) : l = [] := by
  cases l with
  | nil => rfl
  | cons head rest =>
    simp only [List.mapM_cons, bind_eq_ok, pure, Except.pure] at h
    obtain ⟨_, _, _, _, impossible⟩ := h
    exact nomatch impossible

/-- **No hidden finding.** An admitted `completed` result is an object whose tree has exactly
one member named `diagnostics`, and it is the empty array: each member of the tree with that name
is found by Lean's lookup (`JsonAgreement.get?_of_mem`), and the lookup reads no finding. -/
theorem admitGuidance_completed_diagnostics {j : Json} (h : admitGuidance j = .ok ())
    (completed : readStatus j = .ok "completed") :
    j.getObjVal? "diagnostics" = .ok (.arr #[]) ∧
      ∀ fields : Std.TreeMap.Raw String Json compare, j = .obj fields →
        ∀ member ∈ JsonAgreement.members fields.inner.inner, member.1 = "diagnostics" →
          member.2 = .arr #[] := by
  obtain ⟨regular, g, read, -, none, -⟩ := (admitGuidance_completed j completed).mp h
  have findings := (readGuidance_eq_ok read).2.2.2.2.2.2.1
  rw [none] at findings
  have lookup : j.getObjVal? "diagnostics" = .ok (.arr #[]) := by
    simp only [readFindings, bind_eq_ok] at findings
    obtain ⟨value, found, entries, array, decoded⟩ := findings
    have empty := mapM_eq_ok_nil decoded
    cases value <;> simp [Json.getArr?] at array
    subst array
    rw [found, Array.toList_eq_nil_iff.mp empty]
  refine ⟨lookup, fun fields shape member present named => ?_⟩
  subst shape
  obtain ⟨⟨tree⟩⟩ := fields
  cases regular with
  | obj ordered _ =>
    have found := JsonAgreement.get?_of_mem ordered present
    rw [named] at found
    simp only [Json.getObjVal?, found] at lookup
    exact Except.ok.inj lookup

/-- The JSON record of the request a result answers: its kind, project, subject, optional
claim and execution mode, and each configuration file path with its text, if read. -/
def requestJson (kind project subject : String) (claim execution : Option String)
    (configuration : Array (System.FilePath × Option String)) : Json :=
  toJson (⟨kind, project, subject, claim, execution,
    configuration.map fun (path, source) => (path.toString, source)⟩ : Website.ExampleRequest)

/-- Write a result document to `path` in its written form: the `SharedExecution.write` of
`document` (its `SharedExecution.intern` with the proposal of `ExecutionShare`, then
`SourceTexts.intern`) as compact JSON and a final newline, creating the parent directories.
`SharedExecution.read_write` proves a reader's `SharedExecution.read` of the written value is
`document` itself; that law is about `Json` values, not the file's text. A document
`SourceTexts.intern` refuses (one without the `null` `sourceTexts` member of `sourceTextsField`,
or with a `sourceText` member that is not a string) is an error and nothing is written. `span`
names the write in timing output (`timingSpan`). -/
def writeDocument (path : System.FilePath) (document : Json) (span : String := "writeDocument") :
    IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  let spanStart ← IO.monoMsNow
  let written ← IO.ofExcept (SharedExecution.write ExecutionShare.proposals document)
  let encoded := Json.compress written ++ "\n"
  timingSpan s!"diagnostic span: {span} encode: {(← IO.monoMsNow) - spanStart}ms"
  let writeStart ← IO.monoMsNow
  IO.FS.writeFile path encoded
  timingSpan s!"diagnostic span: {span} write: {(← IO.monoMsNow) - writeStart}ms"

/-- Applying `g` to the members named `key` of what applying `f` to them wrote is applying `g`
after `f` to them. -/
theorem mapMembers_mapMembers (key : String) (f g : Json → Json) (value : Json) :
    SharedExecution.mapMembers key g (SharedExecution.mapMembers key f value) =
      SharedExecution.mapMembers key (g ∘ f) value := by
  refine JsonAgreement.Cases.value
    (motive := fun value => SharedExecution.mapMembers key g
      (SharedExecution.mapMembers key f value) = SharedExecution.mapMembers key (g ∘ f) value)
    (fieldsMotive := fun fields => SharedExecution.mapMemberFields key g
      (SharedExecution.mapMemberFields key f fields) =
        SharedExecution.mapMemberFields key (g ∘ f) fields) ?_ value
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [SharedExecution.mapMembers]
  · intro b
    simp [SharedExecution.mapMembers]
  · intro n
    simp [SharedExecution.mapMembers]
  · intro s
    simp [SharedExecution.mapMembers]
  · intro elems elements
    simp only [SharedExecution.mapMembers, Array.map_map]
    exact congrArg Json.arr (Array.map_congr_left fun element member => elements element member)
  · intro fields step
    simp [SharedExecution.mapMembers, step]
  · simp [SharedExecution.mapMemberFields]
  · intro size name value left right valueStep leftStep rightStep
    by_cases named : (name == key) = true
    · simp [SharedExecution.mapMemberFields, named, leftStep, rightStep]
    · simp [SharedExecution.mapMemberFields, named, valueStep, leftStep, rightStep]

/-- The written form the result writers give the document a value with its source texts put back
(`expanded`) stands for, each execution account in the entry kinds `expanded` gives it: every
`execution` member replaced by its `ExecutionShare.formLike` for the value the reader restores
from it (`SharedExecution.restore?`). -/
def rewritten (expanded : Json) : Json :=
  SharedExecution.mapMembers SharedExecution.accountKey (fun written =>
    match SharedExecution.restore? written with
    | some value => ExecutionShare.formLike written value
    | none => written) expanded

/-- Admit a received result document: put its source texts back (`SourceTexts.expand`), restore
its execution accounts (`SharedExecution.expand`), write it again as the writers do with the kind
of each root entry of an execution account the received value has (`rewritten`, then
`SourceTexts.intern`), and require the received value to conform to that (`JsonAgreement.conforms`,
the received value first). It admits exactly the values `admitDocument_eq_ok_iff` states, and
each value a writer writes with search trees, at every entry kinds under which the reader takes
back its execution accounts (`admitDocument_of_forms`, `admitDocument_write`,
`admitDocument_writeAs`). So a source table with an entry that no `sourceText` member names, or an
execution account with a member a writer does not write, is refused. An account may be explicit
where its derived entry fits: the writer decides with `SharedExecution.same`, which compares
object trees node for node, and the document read from a file has the parser's trees. -/
def admitDocument (received : Json) : Except String Json := do
  let expanded ← SourceTexts.expand received
  let document ← SharedExecution.expand expanded
  let written ← SourceTexts.intern (rewritten expanded)
  requireThat (JsonAgreement.conforms received written)
    "result document: not a written form of the document it stands for"
  pure document

/-- What `admitDocument` admits, for every `Json` value: a value whose source texts and execution
accounts restore to `document`, and which conforms to the writers' form of what its source texts
restore to, with its own entry kinds. -/
theorem admitDocument_eq_ok_iff (received document : Json) :
    admitDocument received = .ok document ↔
      ∃ expanded, SourceTexts.expand received = .ok expanded ∧
        SharedExecution.expand expanded = .ok document ∧
        ∃ written, SourceTexts.intern (rewritten expanded) = .ok written ∧
          JsonAgreement.Conforms received written := by
  unfold admitDocument
  simp only [bind_eq_ok, pure, Except.pure, Except.ok.injEq]
  constructor
  · rintro ⟨expanded, he, restored, hr, written, hw, ⟨⟩, conforming, rfl⟩
    exact ⟨expanded, he, hr, written, hw,
      (JsonAgreement.conforms_iff _ _).mp ((requireThat_eq_ok _ _).mp conforming)⟩
  · rintro ⟨expanded, he, hr, written, hw, conforming⟩
    exact ⟨expanded, he, document, hr, written, hw, (),
      (requireThat_eq_ok _ _).mpr ((JsonAgreement.conforms_iff _ _).mpr conforming), rfl⟩

/-- An admitted value is read as the document `admitDocument` returns. -/
theorem admitDocument_read {received document : Json}
    (admitted : admitDocument received = .ok document) :
    SharedExecution.read received = .ok document := by
  obtain ⟨expanded, he, hr, -⟩ := (admitDocument_eq_ok_iff received document).mp admitted
  simp only [SharedExecution.read, he, bind, Except.bind]
  exact hr

/-- **Admission accepts what a writer writes.** For every list of proposals whose written form of
each value `ExecutionShare.formLike` returns, `admitDocument` admits each value
`SharedExecution.write` produces with them whose object trees are search trees, and returns the
document the writer was given (`SharedExecution.read_write`). -/
theorem admitDocument_of_forms {proposals : List (Json → Json)} {document written : Json}
    (forms : ∀ value, ExecutionShare.formLike (SharedExecution.internValue proposals value) value =
      SharedExecution.internValue proposals value)
    (wrote : SharedExecution.write proposals document = .ok written)
    (regular : JsonAgreement.Regular written) : admitDocument written = .ok document := by
  have texts : SourceTexts.expand written = .ok (SharedExecution.intern proposals document) :=
    SourceTexts.expand_intern wrote
  have same : rewritten (SharedExecution.intern proposals document) =
      SharedExecution.intern proposals document := by
    unfold rewritten SharedExecution.intern
    rw [mapMembers_mapMembers]
    congr 1
    funext value
    simp only [Function.comp_apply, SharedExecution.restore?_internValue, forms]
  refine (admitDocument_eq_ok_iff written document).mpr
    ⟨_, texts, SharedExecution.expand_intern proposals document, written, ?_,
      regular, regular.agree_self⟩
  rw [same]
  exact wrote

/-- `admitDocument` admits each value the result writers write (`ExecutionShare.proposals`) for a
document of any shape whose object trees are search trees, and returns that document
(`ExecutionShare.formLike_internValue`). -/
theorem admitDocument_write {document written : Json}
    (wrote : SharedExecution.write ExecutionShare.proposals document = .ok written)
    (regular : JsonAgreement.Regular written) : admitDocument written = .ok document :=
  admitDocument_of_forms ExecutionShare.formLike_internValue wrote regular

/-- `admitDocument` admits each value written with any kind of each root entry
(`ExecutionShare.sharedAs`, the kinds of a value's entries given by `explicit` of the value) under
which the reader takes back every value or `sharedAs` writes it as it is, when its object trees
are search trees (`ExecutionShare.formLike_sharedAs`). The writers' own choice, and the one a
document read back from its file has, are such kinds wherever the reader takes the shared form
back; that the writers' form is taken back is `SharedExecution.read_write`, and that the parse of
a written file is a value of this form is not proved: the qualification campaigns, which read
their result files with `admitDocument`, observe it. -/
theorem admitDocument_writeAs {explicit : Json → Nat → Bool} {document written : Json}
    (restores : ∀ value, ExecutionShare.sharedAs (explicit value) value = value ∨
      SharedExecution.recovers (ExecutionShare.sharedAs (explicit value) value) value = true)
    (wrote : SharedExecution.write [fun value => ExecutionShare.sharedAs (explicit value) value]
      document = .ok written)
    (regular : JsonAgreement.Regular written) : admitDocument written = .ok document :=
  admitDocument_of_forms (fun value => by
    have own : SharedExecution.internValue
        [fun value => ExecutionShare.sharedAs (explicit value) value] value =
        SharedExecution.internValue [ExecutionShare.sharedAs (explicit value)] value :=
      ExecutionShare.internValue_congr rfl
    rw [own]
    exact ExecutionShare.formLike_sharedAs (restores value)) wrote regular

/-- Read the result document `writeDocument` wrote at `path`: parsed strictly
(`PolicyCodec.parse`) and admitted (`admitDocument`), so every `sourceText` member holds its
text and every `execution` member its roots' accounts. A file that is not a written result
document is an error. -/
def readDocument (path : System.FilePath) : IO Json := do
  IO.ofExcept (admitDocument (← readJson path))

/-- Write the `resultJson` of these arguments to `path` (`writeDocument`). -/
def write (path : System.FilePath) (scope : Json) (mode : EvidenceMode) (status : Status)
    (findings : Array Finding) (expected completed : List Stage)
    (unresolved : Array String := #[]) :
    IO Unit :=
  writeDocument path (resultJson scope mode status findings expected completed unresolved)
    "ResultProtocol.write"

/-- A source snapshot's URI and text, the text as a `sourceText` member. -/
def sourceJson (source : RegulaPolicy.SourceSnapshot) : Json :=
  Json.mkObj [("uri", toJson source.uri), (SourceTexts.textKey, toJson source.source)]

private def declarationKeyJson (key : RegulaPolicy.DeclarationKey) : Json :=
  Json.mkObj [("module", RegistryCodec.printedNameJson key.moduleKey.name.name),
    ("name", RegistryCodec.printedNameJson key.name.name)]

private def localSubjectJson : RegulaPolicy.LocalJobSubject → Json
  | .scope => Json.mkObj [("kind", .str "scope")]
  | .module key =>
      Json.mkObj [("kind", .str "module"),
        ("module", RegistryCodec.printedNameJson key.name.name)]
  | .declaration key =>
      Json.mkObj [("kind", .str "declaration"), ("declaration", declarationKeyJson key)]
  | .root key => Json.mkObj [("kind", .str "root"), ("root", declarationKeyJson key)]
  | .boundary key => Json.mkObj [("kind", .str "boundary"), ("root", declarationKeyJson key.root),
      ("reached", declarationKeyJson key.reached), ("boundary", .str key.kind.spelling),
      ("occurrence", toJson key.occurrence),
      ("replacement", key.replacement.map declarationKeyJson |>.getD .null)]

private def subjectJson : RegulaPolicy.JobSubject → Json
  | .scope => Json.mkObj [("kind", .str "scope")]
  | .environment key subject => Json.mkObj [("kind", .str "environment"),
      ("environment", toJson key.index), ("subject", localSubjectJson subject)]
  | .fence key => Json.mkObj [("kind", .str "fence"), ("document", toJson key.document.uri),
      ("opening", toJson (key.opening.start, key.opening.stop)),
      ("body", toJson (key.body.start, key.body.stop)),
      ("closing", toJson (key.closing.start, key.closing.stop)),
      ("expectation", toJson (reprStr key.expectation))]

/-- Machine rendering of the report account (an unproved adapter): coverage, the acceptance
theorem and job count, contracts, execution counts (`executionSummary`), fence kinds, trusted
mechanisms and residual identifiers; mode, scope, surfaces and toolchain are rendered by
`acceptedJson`. Contract entries keep their rule, implementation and requirement with the review
they leave open; `unresolvedReview` names open obligations, never completed reviews. Since
schema 9 each entry also carries `decisionKind`, the spelling of the decision kind its
requirement states or `null` for a requirement that states none, and `notEstablished`, the
direction a one-way kind leaves open or `null` (`RegulaPolicy.DecisionKind.leavesOpen`). Since
schema 11 each entry carries `sharedDefinitions`, an object with the members `booleans` and
`others`, and since schema 13 also `throughTypes`: the functions that its specification shares
with its implementation or its acceptance predicate, by class. A registration is refused for a
function in `booleans`, which is named at any depth, so an accepted registration has none. A
function in `others` is named where the specification reaches it first. The kind does not
establish that it is the intended one, and no entry is refused for it. A function in
`throughTypes` has a result of `Bool` or `BEq` and is shared only through the declaration of the
input type; no entry is refused for it. Since schema 14 the account carries
`trustedDependencies`, the packages of the snapshot dependencies that are not owned, whose
declarations the audit does not replay, or that provide a module under the checker's reserved
prefixes, which the audit does not own (`RegulaPolicy.DependencyState.reserved`). Since schema 15 the account also carries
`countedContracts`: each decision registration an environment counts from another surface toward
a function it registers as a decision (`Account.CountedAccount`), with both surfaces. Since
schema 16 the account also carries `contractEvidence`: for each registration whose requirement
reduces to a decision carrier (`Account.EvidenceAccount`), its environment, module,
implementation and requirement, the carrier, each part of the relation as an object with its
exact term (`exact`: the tables of levels and subterms of `RegulaPolicy.Term`) and Lean's
`display` of it, the law observer's `linkage` (`linked` with the applications of
`Function.uncurry`, or `unsupported` or `mismatch` with the reason), and the `laws` and
`outcomes` the carrier establishes, each with its proposition as an object of the same form,
which are empty unless it is linked. -/
def accountJson (account : Regula.Checker.Account) : Json :=
  let a := account.val
  let residuals (rs : List Regula.Checker.Account.Residual) := toJson (rs.map (·.spelling))
  Json.mkObj [
    ("coverage", toJson a.coverage.spelling),
    ("checked", Json.mkObj
        [("theorem", RegistryCodec.printedNameJson Regula.Checker.Account.acceptanceTheorem),
      ("jobs", toJson a.jobs)]),
    ("contracts", toJson (a.contracts.map fun contract => Json.mkObj [
      ("rule", toJson Regula.RuleId.executableContract.spelling),
      ("registration", RegistryCodec.printedNameJson contract.registration),
      ("module", RegistryCodec.printedNameJson contract.module),
      ("implementation", RegistryCodec.printedNameJson contract.implementation),
      ("requirement", toJson contract.requirement),
      ("decisionKind", toJson (contract.kind.map (·.spelling))),
      ("notEstablished", toJson (contract.kind.bind (·.leavesOpen))),
      ("sharedDefinitions", Json.mkObj [
        ("booleans", toJson (contract.shared.booleans.map RegistryCodec.printedNameJson)),
        ("others", toJson (contract.shared.others.map RegistryCodec.printedNameJson)),
        ("throughTypes",
          toJson (contract.shared.throughTypes.map RegistryCodec.printedNameJson))]),
      ("unresolvedReview", residuals Regula.Checker.Account.ContractAccount.unresolved)])),
    ("countedContracts", toJson (a.counted.map fun counted => Json.mkObj [
      ("rule", toJson Regula.RuleId.decisionContract.spelling),
      ("surface", toJson counted.surface), ("source", toJson counted.source),
      ("registration", RegistryCodec.printedNameJson counted.registration),
      ("module", RegistryCodec.printedNameJson counted.module),
      ("implementation", RegistryCodec.printedNameJson counted.implementation)])),
    ("contractEvidence", toJson (a.evidence.map fun entry =>
      let e := entry.evidence
      let facts (law : Bool) := toJson <| (e.facts.filter (·.1.law == law)).map
        fun (fact, statement) =>
          Json.mkObj [("fact", toJson fact.spelling), ("proposition", toJson statement)]
      Json.mkObj [
        ("rule", toJson Regula.RuleId.executableContract.spelling),
        ("environment", toJson entry.environment),
        ("registration", RegistryCodec.printedNameJson entry.registration),
        ("module", RegistryCodec.printedNameJson entry.module),
        ("implementation", RegistryCodec.printedNameJson entry.implementation),
        ("requirement", toJson e.requirement), ("carrier", toJson e.carrier.spelling),
        ("implementationExpression", toJson e.implementation),
        ("universes", toJson (e.universes.map RegistryCodec.printedNameJson)),
        ("domain", toJson e.domain), ("result", toJson e.result), ("accepts", toJson e.accepts),
        ("spec", toJson e.spec), ("decided", toJson e.decided),
        ("linkage", match e.linkage with
          | .linked conclusion => Json.mkObj [("state", toJson "linked"),
              ("uncurries", toJson conclusion.uncurries)]
          | .unlinked (.unsupported reason) =>
              Json.mkObj [("state", toJson "unsupported"), ("reason", toJson reason)]
          | .unlinked (.mismatch reason) =>
              Json.mkObj [("state", toJson "mismatch"), ("reason", toJson reason)]),
        ("laws", facts true), ("outcomes", facts false)])),
    ("executionSummary", toJson (a.execution.mapIdx fun environment summary => Json.mkObj [
      ("environment", toJson environment), ("roots", toJson summary.roots),
      ("boundaries", toJson summary.boundaries), ("checked", toJson summary.checked),
      ("trusted", toJson summary.trusted), ("unresolved", toJson summary.unresolved)])),
    ("fences", Json.mkObj [("positive", toJson a.fences.positive),
      ("compilerRejection", toJson a.fences.compilerRejection),
      ("policyRejection", toJson a.fences.policyRejection),
      ("trustedTeaching", toJson a.fences.trustedTeaching)]),
    ("trusted", toJson (a.trusted.map fun boundary => Json.mkObj [
      ("boundary", toJson boundary.spelling), ("detail", toJson boundary.detail)])),
    ("trustedDependencies", toJson a.trustedDependencies),
    ("unresolvedReview", residuals a.unresolved)]

/-- Result rendering of a frozen snapshot: the audited sources in full, the configuration
by URI, and each dependency by package, nominal revision, input-scoped `dirty` status and
`owned` (since schema 14).
Each source's text is a `sourceText` member (`sourceJson`): a result file stores it once
(`writeDocument`), and the freshChecker serialized-graph output, which is not a result document,
keeps it in the member.
`configuration.source` serializes the project configuration and every Lake dependency's
captured source and configuration text, which for any Mathlib-dependent project is all of
Mathlib. Acceptance compares those exact bytes in memory (`RegulaPolicy.Snapshot`) and
rechecks them before success; they are not rendered here. The project configuration is
rendered in full as `scope.configuration` only by axiomGate and ruleExamples results; the
freshChecker serialized-graph output has no `scope`, so it carries no configuration text,
and no consumer reads it there. A clean dependency is identified by its pinned revision. A
dirty dependency, including any path dependency without its own Git revision, is rendered
only as package, revision, `dirty: true` and `owned`: it carries no content identity, and its
frozen text is not recorded. An owned dependency's module sources are among the audited
sources. -/
def snapshotJson (snapshot : RegulaPolicy.Snapshot) : Json :=
  Json.mkObj [("sources", toJson (snapshot.sources.map sourceJson)),
    ("configuration", Json.mkObj [("uri", toJson snapshot.configuration.uri)]),
    ("toolchain", toJson (reprStr snapshot.toolchain)),
    ("dependencies", toJson (snapshot.dependencies.map fun dependency => Json.mkObj [
      ("package", toJson dependency.package), ("revision", toJson dependency.nominalRevision),
      ("dirty", toJson dependency.dirty), ("owned", toJson dependency.owned)]))]

/-- The rendering is independent of the serialized configuration and dependency text, so
its size is independent of the dependencies' content (kernel-checked by `rfl`). -/
theorem snapshotJson_configuration_independent (snapshot : RegulaPolicy.Snapshot)
    (source : String) :
    snapshotJson { snapshot with configuration := { snapshot.configuration with source } } =
      snapshotJson snapshot := rfl

/-- One environment's assigned, infrastructure, admission, declaration and root inventory
and its file binding. Merely imported modules (`importedModules`, `origins`,
`importedSources`: the whole import closure) are decided in memory and not rendered. -/
def environmentJson (environment : RegulaPolicy.EnvironmentCensus) : Json :=
  Json.mkObj [
    ("index", toJson environment.request.key.index),
    ("modules", toJson
        (environment.request.modules.map fun key => RegistryCodec.printedNameJson key.name.name)),
    ("dependencyModules", toJson (environment.dependencyModules.map fun key =>
        RegistryCodec.printedNameJson key.name.name)),
    ("infrastructureModules", toJson (environment.infrastructureModules.map fun key =>
        RegistryCodec.printedNameJson key.name.name)),
    ("admissionModules", toJson
        (environment.admissionModules.map fun key => RegistryCodec.printedNameJson key.name.name)),
    ("admissionDeclarations", toJson (environment.admissionDeclarations.map declarationKeyJson)),
    ("declarations", toJson (environment.declarations.map declarationKeyJson)),
    ("roots", toJson (environment.roots.map declarationKeyJson)),
    ("fileSource", environment.fileSource.map (fun binding => Json.mkObj [
      ("requested", sourceJson binding.requested), ("compiled", sourceJson binding.compiled)])
          |>.getD .null)]

/-- The rendering is independent of the import closure (kernel-checked by `rfl`). -/
theorem environmentJson_imports_independent (environment : RegulaPolicy.EnvironmentCensus)
    (importedModules : Array RegulaPolicy.ModuleKey) (origins : Array RegulaPolicy.ModuleOrigin)
    (importedSources : Array (RegulaPolicy.ModuleKey × RegulaPolicy.SourceSnapshot)) :
    environmentJson { environment with importedModules, origins, importedSources } =
      environmentJson environment := rfl

/-- Renderer accepts only a proof-bearing run and projects its exact report. The common
snapshot is rendered once, by `snapshotJson`; each subject inherits it. Each environment
lists its assigned, admission, declaration, root and infrastructure inventory, not the
modules it merely imports. These rendered fields are observations, not serialized
authority, and consumers must never deserialize them into Accepted. -/
def acceptedJson {claim : RegulaPolicy.Claim} (accepted : RegulaPolicy.AcceptedRun claim) : Json :=
  let report := accepted.report
  let snapshot := report.claim.val.snapshot
  Json.mkObj [
    ("mode", toJson report.claim.val.mode.spelling),
    ("scope", toJson (reprStr report.claim.val.scope)),
    ("surfaces", toJson (report.claim.val.surfaces.map fun surface => Json.mkObj [
      ("target", toJson surface.target),
      ("modules", toJson (surface.modules.map fun n => RegistryCodec.printedNameJson n.name)),
      ("profile", toJson surface.profile.spelling),
      ("execution", toJson surface.execution.spelling),
      ("decides", toJson surface.decides)])),
    ("snapshot", snapshotJson snapshot),
    ("modules", toJson
        (report.census.modules.map fun key => RegistryCodec.printedNameJson key.name.name)),
    ("environments", toJson (report.census.environments.map environmentJson)),
    ("graphRoots", toJson
        (report.census.graphRoots.map fun key => RegistryCodec.printedNameJson key.name.name)),
    ("graphCoverage", toJson (report.census.graphCoverage.map fun (key, modules) => Json.mkObj [
      ("root", RegistryCodec.printedNameJson key.name.name),
      ("modules", toJson
          (modules.map fun (moduleKey : RegulaPolicy.ModuleKey) =>
              RegistryCodec.printedNameJson moduleKey.name.name))])),
    ("jobs", toJson (report.jobs.mapIdx fun slot key => Json.mkObj [
      ("slot", toJson slot), ("stage", toJson (reprStr key.stage)),
      ("subject", subjectJson key.subject)])),
    ("account", accountJson (Regula.Checker.Account.account accepted))]

/-- The wrapper's composed-publication decision: a composed success is
publishable only for a fully successful guarded action. Executed literally by
the run wrapper. -/
def composeDecision (code : UInt32) (composed : Option Json) : Option Json :=
  if code = 0 then composed else none

/-- Execution-linked state invariant: a failed guarded action cannot publish
composed success. -/
theorem failure_drops_composed (code : UInt32) (composed : Option Json)
    (h : ¬ code = 0) : composeDecision code composed = none := by
  simp [composeDecision, h]

/-- Public audit completion cannot be constructed from diagnostic counts or
worker exits. The composed accepted result value (pure): the historical
`writeAccepted` payload construction. -/
def acceptedValue {claim : RegulaPolicy.Claim}
    (accepted : RegulaPolicy.AcceptedRun claim) (scope : Json) : Json :=
  let stages := stagesOf accepted.report.claim.val.mode
  (resultJson scope accepted.report.claim.val.mode
    (.completed (Regula.Checker.Account.account accepted)) #[] stages stages #[]).setObjVal!
    "acceptance" (acceptedJson accepted)

/-- Write `acceptedValue accepted scope` to `path` (`writeDocument`). -/
def writeAccepted {claim : RegulaPolicy.Claim} (path : System.FilePath)
    (accepted : RegulaPolicy.AcceptedRun claim) (scope : Json) : IO Unit :=
  writeDocument path (acceptedValue accepted scope) "writeAccepted"

/-- The historical parse/compress normalization hop, retained verbatim:
roundtrip identity over arbitrary `Json`/`JsonNumber` is not assumed. The
re-parse consumes exactly the bytes `writeJson` historically produced
(`Json.compress` output plus the trailing newline) with the same
`PolicyCodec.parse`. -/
def normalize (value : Json) : Json :=
  match Regula.Checker.PolicyCodec.parse (Json.compress value ++ "\n") with
  | .ok parsed => parsed
  | .error _ => value

/-- Pure composition of the layered finalization in its executed order:
`sourceAccount` retention, then the run wrapper's conditional account
completion and `request`/`effective` additions, with both historical
normalization hops retained in memory. -/
def composedFinal (base account recovery request effective : Json) : Json :=
  let retained := (normalize base).setObjVal! "sourceAccount" account
  let readBack := normalize retained
  let completed := if (readBack.getObjVal? "sourceAccount").isOk then readBack
    else readBack.setObjVal! "sourceAccount" recovery
  (completed.setObjVal! "request" request).setObjVal! "effective" effective

/-- Definitional correspondence: `composedFinal` is exactly the historical
layered chain in executed order — normalize the accepted value (the re-read of
write 1), retain `sourceAccount` (write 2's transformation), normalize again
(the re-read of write 2), the wrapper's conditional account completion and
`request`/`effective` additions (write 3's transformation) — with both
intervening parse/compress normalization hops retained. -/
theorem composedFinal_eq (base account recovery request effective : Json) :
    composedFinal base account recovery request effective =
      let retained := (normalize base).setObjVal! "sourceAccount" account
      let readBack := normalize retained
      let completed := if (readBack.getObjVal? "sourceAccount").isOk then readBack
        else readBack.setObjVal! "sourceAccount" recovery
      (completed.setObjVal! "request" request).setObjVal! "effective" effective := rfl

end Regula.Checker.ResultProtocol
