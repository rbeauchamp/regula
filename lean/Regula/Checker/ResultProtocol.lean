import RegulaPolicy.Acceptance
import RegulaCore.Account
import Regula.Website
import Regula.Checker.Producer
import Regula.Checker.RuleDiagnostics
import Regula.DiagnosticCodec
import Regula.Checker.Common

/-! # Versioned result protocol

Versioned observation output and accepted-report rendering. JSON is display/transport
of scoped evidence, never a deserializable proof or whole-standard conformance certificate.
The accepted constructor requires the executed con-leche-inspired indexed finalization. -/
namespace Regula.Checker.ResultProtocol
open Lean

/-- This checker build's producer identity, written into every result envelope. -/
abbrev producer := Regula.Checker.Producer.identity

/-- Result schema 5 writes every Lean name of the document, in `diagnostics`, `scope` and
`acceptance` alike, in one encoding (`RegistryCodec.printedNameJson`): the string Lean prints for
it, and, only for a name whose printed text Lean's parser does not read back as the name, its
structural components, an array of `["str", s]` and `["num", n]` innermost first
(`printedNameJson_roundtrip`, `printedNameJson_eq_str_iff`). A declaration finding's
`arguments.sourceDeclaration` is `null`, or, for a declaration Lean generated, the declaration
at the end of the chain it generated it from (`Findings.sourceName?`); such a finding keeps the
range of its own declaration when it has one, and otherwise is located at that declaration's range
when it has one and its module has a snapshot (`Findings.findingLocation`), and its `related` then
names its own module.
Result schema 5 attributes the toolchain's own boundaries to it: a boundary a toolchain
module (`Init`, `Std` or `Lean`, loaded from the toolchain's library) owns carries its
`toolchainOrigin` (formerly `nativeOrigin`, which only native-runtime boundaries carried), and
each `axiomGate` project and file result's `scope.toolchainBase` lists every such boundary once
for the whole audit, with the environments and roots that reach it. Schema 4 inspected each
claimed executable's root in an environment of its own: a project `scope.surfaces[*]` entry's
`modules` and `report` cover only its library's environment (the library's modules other than
its claimed executables' roots), and each claimed executable has its own `executables[*]` entry
with its own `modules` and `report`. A report's `admission` also lists as `reused` the modules
its environment did not replay because a library's environment admitted them over the identical
import closure.
Schema 3 added, for agents, each diagnostic's `remedy`, the top-level `rules` (the
guidance of every rule that fired, once each), the stage evidence `stages` (the run's required
stages) and `stagesCompleted` (those that completed), and their derivation `complete` (every
stage of the run completed) and `stagesNotRun` (the stages that did not). Schema 2 omitted the
frozen configuration and dependency text from the snapshot (`snapshotJson`: a clean
dependency is identified by its pinned revision, a dirty one only by package and `dirty`
status) and imported-environment module lists (`acceptedJson`,
`ProducerReport.Environment.resultJson`); schema 1 embedded them. -/
def schemaVersion : Nat := 5

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
  | .escapeHatch | .executableContract => some .declarationPolicy
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

/-- Completed is scoped observation, never a synonym for whole-standard conformance. A
completed envelope takes its mode from the status's account, not from `mode`. `expected` are
the run's required stages and `completed` those its writer recorded as completed. The guidance
members are derived from the diagnostics exactly as written, in `sortFindings` order. -/
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
    ("unresolved", toJson unresolved)] ++
    guidanceFields (acceptedStatus (statusText status)) expected completed findings)

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

/-- Admit a result envelope's agent members in the registry-export style: it has this schema
version; every diagnostic decodes to its canonical indexed form (`DiagnosticCodec.parseDiagnostic`,
which includes the finding's `remedy` and `text`); every entry of `stages` and `stagesCompleted`
is a stage, and `stages` are the required stages of the result's `mode` (`runStages`); a result
with a `mode` records its `request`, whose documentation stages are exactly those of a
`projectWithDocs` request;
`stagesCompleted`, `complete`, `stagesNotRun` and `rules` equal their derivation by the writer's
own `guidanceFields` from the status, those stages and the diagnostics
(`guidanceFields_recorded`), so no stage a finding blocks is reported as run and a `completed`
result reports every stage as run; and an `incomplete` result without an incomplete finding
reports a stage not run, because only a stage that did not complete can have left it
incomplete. This is consistency against writer regressions and omissions, not authenticity: a
report deliberately edited to be self-consistent, such as a rewritten `request.kind`, passes. -/
def admitGuidance (j : Json) : Except String Unit := do
  unless (j.getObjVal? "schemaVersion").toOption == some (toJson schemaVersion) do
    throw "unsupported result schema"
  let findings := (← (← (← j.getObjVal? "diagnostics").getArr?).mapM
    DiagnosticCodec.parseDiagnostic).toList
  let stages (key : String) : Except String (List Stage) := do
    (← (← j.getObjVal? key).getArr?).toList.mapM fun name => do parseStage (← name.getStr?)
  let required ← stages "stages"
  let completed ← stages "stagesCompleted"
  let mode ← match ← j.getObjVal? "mode" with
    | .null => pure none
    | mode => some <$> RegistryCodec.parseMode (← mode.getStr?)
  unless (runStages mode).contains required do
    throw "stages are not the required stages of the result's mode"
  if mode.isSome then
    let withDocs := (← (← (← j.getObjVal? "request").getObjVal? "kind").getStr?) ==
        "projectWithDocs"
    unless withDocs == (required == stagesOf .freshProject ++ documentationStages) do
      throw "stages are not the required stages of the result's request"
  let status ← (← j.getObjVal? "status").getStr?
  for (key, value) in guidanceFields (acceptedStatus status) required completed findings do
    unless (← j.getObjVal? key) == value do throw s!"noncanonical result {key}"
  if status == "incomplete" && !findings.any (·.2.impact == .incomplete) &&
      (notRun required completed).isEmpty then
    throw "incomplete result without an incomplete finding reports every stage as run"

/-- The JSON record of the request a result answers: its kind, project, subject, optional
claim and execution mode, and each configuration file path with its text, if read. -/
def requestJson (kind project subject : String) (claim execution : Option String)
    (configuration : Array (System.FilePath × Option String)) : Json :=
  toJson (⟨kind, project, subject, claim, execution,
    configuration.map fun (path, source) => (path.toString, source)⟩ : Website.ExampleRequest)

/-- Write the `resultJson` of these arguments as compact JSON and a final newline to `path`,
creating its parent directories, and report how long encoding and writing took when timing output
is on (`timingSpan`). -/
def write (path : System.FilePath) (scope : Json) (mode : EvidenceMode) (status : Status)
    (findings : Array Finding) (expected completed : List Stage)
    (unresolved : Array String := #[]) :
    IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  let spanStart ← IO.monoMsNow
  let encoded := Json.compress
      (resultJson scope mode status findings expected completed unresolved) ++ "\n"
  timingSpan s!"diagnostic span: ResultProtocol.write encode: {(← IO.monoMsNow) - spanStart}ms"
  let writeStart ← IO.monoMsNow
  IO.FS.writeFile path encoded
  timingSpan s!"diagnostic span: ResultProtocol.write write: {(← IO.monoMsNow) - writeStart}ms"

private def sourceJson (source : RegulaPolicy.SourceSnapshot) : Json :=
  Json.mkObj [("uri", toJson source.uri), ("source", toJson source.source)]

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
theorem and job count, contracts, execution counts, fence kinds, trusted mechanisms and
residual identifiers; mode, scope, surfaces and toolchain are rendered by `acceptedJson`.
Contract entries keep their rule, implementation and requirement with the review they leave
open; `unresolvedReview` names open obligations, never completed reviews. -/
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
      ("unresolvedReview", residuals Regula.Checker.Account.ContractAccount.unresolved)])),
    ("execution", toJson (a.execution.mapIdx fun environment summary => Json.mkObj [
      ("environment", toJson environment), ("roots", toJson summary.roots),
      ("boundaries", toJson summary.boundaries), ("checked", toJson summary.checked),
      ("trusted", toJson summary.trusted), ("unresolved", toJson summary.unresolved)])),
    ("fences", Json.mkObj [("positive", toJson a.fences.positive),
      ("compilerRejection", toJson a.fences.compilerRejection),
      ("policyRejection", toJson a.fences.policyRejection),
      ("trustedTeaching", toJson a.fences.trustedTeaching)]),
    ("trusted", toJson (a.trusted.map fun boundary => Json.mkObj [
      ("boundary", toJson boundary.spelling), ("detail", toJson boundary.detail)])),
    ("unresolvedReview", residuals a.unresolved)]

/-- Result rendering of a frozen snapshot: the audited sources in full, the configuration
by URI, and each dependency by package, nominal revision and input-scoped `dirty` status.
`configuration.source` serializes the project configuration and every Lake dependency's
captured source and configuration text, which for any Mathlib-dependent project is all of
Mathlib. Acceptance compares those exact bytes in memory (`RegulaPolicy.Snapshot`) and
rechecks them before success; they are not rendered here. The project configuration is
rendered in full as `scope.configuration` only by axiomGate and ruleExamples results; the
freshChecker serialized-graph output has no `scope`, so it carries no configuration text,
and no consumer reads it there. A clean dependency is identified by its pinned revision. A
dirty dependency, including any path dependency without its own Git revision, is rendered
only as package, revision and `dirty: true`: it carries no content identity, and its frozen
text is not recorded. -/
def snapshotJson (snapshot : RegulaPolicy.Snapshot) : Json :=
  Json.mkObj [("sources", toJson (snapshot.sources.map sourceJson)),
    ("configuration", Json.mkObj [("uri", toJson snapshot.configuration.uri)]),
    ("toolchain", toJson (reprStr snapshot.toolchain)),
    ("dependencies", toJson (snapshot.dependencies.map fun dependency => Json.mkObj [
      ("package", toJson dependency.package), ("revision", toJson dependency.nominalRevision),
      ("dirty", toJson dependency.dirty)]))]

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
      ("execution", toJson surface.execution.spelling)])),
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

/-- Write `acceptedValue accepted scope` as compact JSON and a final newline to `path`,
creating its parent directories, and report how long encoding and writing took when timing output
is on (`timingSpan`). -/
def writeAccepted {claim : RegulaPolicy.Claim} (path : System.FilePath)
    (accepted : RegulaPolicy.AcceptedRun claim) (scope : Json) : IO Unit := do
  let spanStart ← IO.monoMsNow
  let value := acceptedValue accepted scope
  if let some parent := path.parent then IO.FS.createDirAll parent
  let encoded := Json.compress value ++ "\n"
  timingSpan s!"diagnostic span: writeAccepted encode: {(← IO.monoMsNow) - spanStart}ms"
  let writeStart ← IO.monoMsNow
  IO.FS.writeFile path encoded
  timingSpan s!"diagnostic span: writeAccepted write: {(← IO.monoMsNow) - writeStart}ms"

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
