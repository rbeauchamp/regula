import RegulaPolicy.Plan
import RegulaPolicy.Pattern
import RegulaPolicy.Intent

/-! Typed raw completion observations and independent policy predicates for the fixed plan.
Receipts are data, not serialized proofs: their truthful acquisition and the registry/location
bridge remain operational assumptions. Pure declaration, execution and expectation decisions
are recomputed over the supplied observations. -/
namespace RegulaPolicy
open Lean (Name)

inductive Completion where
  | completed | incomplete | cancelled | crashed | unsupported
  deriving Repr, DecidableEq

structure BuildObservation where
  exitCode : Nat
  warnings : Array String
  errors : Array String
  deriving Repr, DecidableEq

structure AdmissionObservation where
  modules : Array ModuleKey
  required : Array DeclarationKey
  admitted : Array DeclarationKey
  failures : Array String
  deriving Repr, DecidableEq

structure HistoryObservation where
  moduleName : Name
  before : SourceSnapshot
  after : SourceSnapshot
  replacements : Array (Name × Name)
  unsupported : Array String
  deriving Repr, DecidableEq

/-- A producer's terminal example outcome is distinct from transport/process completion.
Policy-negative diagnostics come from the real checker/sole-registry adapter, not invented
compiler errors. The pure matcher does not authenticate that operational production. -/
inductive ExampleOutcome where
  | elaborated (inventory : Inventory) (requiredReplay admittedReplay : Array (Name × Name))
      (admissionFailures : Array String)
  | compilerRejection (effectiveErrors : Array String)
  | policyRejection (diagnostics : List ExpectedDiagnostic)
  | incomplete (detail : String)

/-- Explicit temporary-unit mapping permits grouped inspection without conflating its
source units. Each unit retains the original fence identity and exact compiler source. -/
structure ExampleUnit where
  moduleName : Name
  fence : FenceKey
  source : SourceSnapshot
  deriving Repr, DecidableEq

structure ExampleObservation where
  fence : FenceKey
  unitName : Name
  units : Array ExampleUnit
  before : String
  after : String
  warnings : Array String
  declarationCensus : Array (Name × Name)
  outcome : ExampleOutcome

/-- Complete scan of the exact document domain, including no-fence files. -/
structure DocumentObservation where
  documents : Array SourceSnapshot
  fences : Array FenceKey
  structuralFailures : Array String

structure GraphObservation where
  selected : Array ModuleKey
  checked : Array ModuleKey
  covered : Array ModuleKey
  failures : Array String
  plannedOnly : Bool

/-- Evidence constructors constrain stage meaning. A mismatched constructor/subject cannot
satisfy StageOK. Completion alone never substitutes for the applicable field relations. -/
inductive JobEvidence where
  | configuration (assignments : Array TargetAssignment) (targets : Array DiscoveredTarget)
  | discovery (observation : Census)
  | build (observation : BuildObservation)
  | admission (observation : AdmissionObservation)
  | declaration (observation : Declaration)
  | execution (observation : ExecutionRoot)
  | transcript (observation : Frontend.Transcript)
  | history (observation : HistoryObservation)
  | origin (observation : NativeOrigin)
  | documentationPresence (docstring : Option String)
  | documentScan (observation : DocumentObservation)
  | example (observation : ExampleObservation)
  | graph (observation : GraphObservation)

structure JobObservation where
  key : JobKey
  snapshot : Snapshot
  completion : Completion
  evidence : JobEvidence

/-- Snapshot and target observations match the independently fixed configuration account. -/
def ScopeOK (c : Claim) (i : Census) (asgn : Array TargetAssignment)
    (targets : Array DiscoveredTarget) : Prop :=
  asgn = i.configuredTargets ∧ targets = i.discoveredTargets ∧ TargetPartitionOK c i
instance (c : Claim) (i : Census) (a : Array TargetAssignment) (t : Array DiscoveredTarget) :
    Decidable (ScopeOK c i a t) := by unfold ScopeOK; infer_instance

/-- Build source processing succeeded without any emitted warning or error. -/
def BuildOK (o : BuildObservation) : Prop := o.exitCode = 0 ∧ o.warnings = #[] ∧ o.errors = #[]
instance (o : BuildObservation) : Decidable (BuildOK o) := by unfold BuildOK; infer_instance

/-- Every frozen replay key is admitted exactly once, with no skipped/failed observations. -/
def AdmissionOK (i : EnvironmentCensus) (o : AdmissionObservation) : Prop :=
  o.modules = i.admissionModules ∧ o.required = i.admissionDeclarations ∧ o.admitted.toList.Pairwise (· ≠ ·) ∧
  (∀ d ∈ o.required, d ∈ o.admitted) ∧ (∀ d ∈ o.admitted, d ∈ o.required) ∧ o.failures = #[]
instance (i : EnvironmentCensus) (o : AdmissionObservation) : Decidable (AdmissionOK i o) := by
  unfold AdmissionOK
  -- Index both key arrays once instead of scanning them for every key.
  let admitted := Std.ExtHashSet.ofList o.admitted.toList
  let required := Std.ExtHashSet.ofList o.required.toList
  letI (d : DeclarationKey) : Decidable (d ∈ o.admitted) :=
    decidable_of_iff (d ∈ admitted) (by simp [admitted, Std.ExtHashSet.mem_ofList])
  letI (d : DeclarationKey) : Decidable (d ∈ o.required) :=
    decidable_of_iff (d ∈ required) (by simp [required, Std.ExtHashSet.mem_ofList])
  letI : Decidable (o.admitted.toList.Pairwise (· ≠ ·)) := distinctDecidable _
  infer_instance

/-- The indexed implementation decides the same proposition as the prior finite scan. -/
theorem admissionOK_decide_eq_previous (i : EnvironmentCensus) (o : AdmissionObservation) :
    decide (AdmissionOK i o) = @decide (AdmissionOK i o) (by unfold AdmissionOK; infer_instance) := by
  congr

/-- Source coordinates are checked against exact bytes; module/project locations remain
explicit rather than being converted to a fabricated line number. -/
def LocationOK (c : Claim) : PolicyLocation → Prop
  | .source source range => source ∈ snapshotSources c ∧ range.start ≤ range.stop ∧
      String.Pos.Raw.isValid source.source ⟨range.start⟩ = true ∧
      String.Pos.Raw.isValid source.source ⟨range.stop⟩ = true
  | .module key => key.snapshot.val = c.val.snapshot
  | .project snapshot => snapshot.val = c.val.snapshot
instance (c : Claim) (l : PolicyLocation) : Decidable (LocationOK c l) := by
  cases l <;> unfold LocationOK <;> infer_instance

/-- Optional subreason means it is unconstrained; locations and all listed related locations
are exact. List correspondence preserves the configured deterministic diagnostic order. -/
def DiagnosticMatches (c : Claim) (expected actual : ExpectedDiagnostic) : Prop :=
  expected.rule ≠ "" ∧ actual.rule = expected.rule ∧
  (∀ reason ∈ expected.subreason, reason ≠ "" ∧ actual.subreason = some reason) ∧
  actual.primary = expected.primary ∧ actual.related = expected.related ∧
  LocationOK c actual.primary ∧ ∀ location ∈ actual.related, LocationOK c location
instance (c : Claim) (e a : ExpectedDiagnostic) : Decidable (DiagnosticMatches c e a) := by
  unfold DiagnosticMatches; infer_instance

/-- Replay coverage for a fresh example includes every safe nonpartial reported declaration;
its independently supplied owned-dependency census must also be completely admitted. -/
def ExampleAdmissionOK (i : Inventory) (required admitted : Array (Name × Name))
    (failures : Array String) : Prop :=
  required.toList.Pairwise (· ≠ ·) ∧ admitted.toList.Pairwise (· ≠ ·) ∧
  canonicalEdges admitted = canonicalEdges required ∧ failures = #[] ∧
  ∀ d ∈ i.declarations, d.isUnsafe = false → d.isPartial = false → (d.module, d.name) ∈ required
instance (i : Inventory) (r a : Array (Name × Name)) (f : Array String) :
    Decidable (ExampleAdmissionOK i r a f) := by
  unfold ExampleAdmissionOK
  let required := Std.ExtHashSet.ofList r.toList
  letI : Decidable (r.toList.Pairwise (· ≠ ·)) := distinctDecidable r.toList
  letI : Decidable (a.toList.Pairwise (· ≠ ·)) := distinctDecidable a.toList
  letI (key : Name × Name) : Decidable (key ∈ r) :=
    decidable_of_iff (key ∈ required) (by simp [required, Std.ExtHashSet.mem_ofList])
  infer_instance

/-- Every role transcript is tied to an exact original source unit in the fixed fence
plan, including grouped environments. Policy assessment selects this fence's declarations
while role authentication still sees the whole reconciled group inventory. -/
def ExampleSourceOK (fences : Array FenceKey) (f : FenceKey) (o : ExampleObservation)
    (i : Inventory) : Prop :=
  o.unitName ≠ .anonymous ∧ o.units.toList.Pairwise (fun a b => a.moduleName ≠ b.moduleName) ∧
  o.units.toList.Pairwise (fun a b => a.fence ≠ b.fence) ∧
  (∃ unit ∈ o.units, unit.moduleName = o.unitName ∧ unit.fence = f) ∧
  (∀ unit ∈ o.units, unit.moduleName ≠ .anonymous ∧ unit.fence ∈ fences ∧ unit.source.uri ≠ "" ∧
    unit.source.source = String.Pos.Raw.extract unit.fence.document.source
      ⟨unit.fence.body.start⟩ ⟨unit.fence.body.stop⟩) ∧
  (∀ d ∈ i.declarations, ∃ unit ∈ o.units, unit.moduleName = d.module) ∧
  (∀ t ∈ i.transcripts, ∃ unit ∈ o.units, unit.moduleName = t.module ∧
    unit.source.uri = t.source ∧ unit.source.source = t.sourceContent)
set_option synthInstance.maxSize 1024 in
instance (fs : Array FenceKey) (f : FenceKey) (o : ExampleObservation) (i : Inventory) :
    Decidable (ExampleSourceOK fs f o i) := by unfold ExampleSourceOK; infer_instance

/-- Example expectation meaning: positive/teaching inspect actual pure policies; compiler
negatives match one effective error; policy negatives require exact completed rejection
observations. Negative/teaching results never supply conforming positive program evidence. -/
def ExampleExpectationOK (c : Claim) (fences : Array FenceKey) (f : FenceKey) (o : ExampleObservation) : Prop :=
  o.fence = f ∧ o.before = String.Pos.Raw.extract f.document.source ⟨f.body.start⟩ ⟨f.body.stop⟩ ∧
  o.after = o.before ∧
  match f.expectation, o.outcome with
  | .positive, .elaborated i required admitted failures =>
      let roles := authorize i
      o.warnings = #[] ∧ o.declarationCensus = i.declarations.map (fun d => (d.module, d.name)) ∧
      ExampleSourceOK fences f o i ∧ ExampleAdmissionOK i required admitted failures ∧
      ∀ d ∈ i.declarations, d.module = o.unitName → DeclarationOK d (.conforming .standardLogical) roles.native roles.helpers
  | .compilerRejection pattern _, .compilerRejection errors =>
      ∃ message ∈ errors, PatternMatch pattern message
  | .policyRejection expected _, .policyRejection actual =>
      expected.length = actual.length ∧
      ∀ pair ∈ expected.zip actual, DiagnosticMatches c pair.1 pair.2
  | .trustedTeaching, .elaborated i required admitted failures =>
      let roles := authorize i
      o.warnings = #[] ∧ o.declarationCensus = i.declarations.map (fun d => (d.module, d.name)) ∧
      ExampleSourceOK fences f o i ∧ ExampleAdmissionOK i required admitted failures ∧
      (∀ d ∈ i.declarations, d.module = o.unitName → DeclarationOK d .teaching roles.native roles.helpers) ∧
      ∃ d ∈ i.declarations, d.module = o.unitName ∧ ∃ n ∈ d.axioms, CompilerAxiom roles.native n
  | _, _ => False

/-- No incomplete terminal outcome satisfies any of the four accepted expectations.
A separately qualified unavailable-analysis demonstration cannot change this predicate. -/
theorem incomplete_example_refused (c : Claim) (fences : Array FenceKey) (f : FenceKey)
    (o : ExampleObservation) (detail : String) (h : o.outcome = .incomplete detail) :
    ¬ ExampleExpectationOK c fences f o := by
  cases f.expectation <;> simp [ExampleExpectationOK, h]

/-- Completed scan and exact frozen fence inventory, including structural failures. -/
def DocumentOK (c : Claim) (i : Census) (o : DocumentObservation) : Prop :=
  (match c.val.scope with | .documentation docs => o.documents = docs | _ => False) ∧
  o.fences = i.fences ∧ o.structuralFailures = #[]
instance (c : Claim) (i : Census) (o : DocumentObservation) : Decidable (DocumentOK c i o) := by
  unfold DocumentOK; cases c.val.scope <;> infer_instance

/-- Presence is the deliberately narrow metadata requirement; content fidelity and the
completeness of material-claim registration remain the separate R-DOC review obligation.
A registered material declaration additionally needs an Intent section
(`MaterialDocumentationOK`); its adequacy is the R-INTENT review obligation. -/
def DocumentationPresenceOK (docstring : Option String) : Prop := docstring ≠ none

/-- Native-runtime evidence must agree with every relevant boundary origin observation. -/
def OriginOK (i : EnvironmentCensus) (m : ModuleKey) (origin : NativeOrigin) : Prop :=
  origin.moduleName = m.name.name ∧
  ∀ r ∈ i.execution.roots, ∀ b ∈ r.boundaries,
    b.module = m.name.name → b.boundary = .nativeRuntime → b.account.nativeOrigin? = some origin
instance (i : EnvironmentCensus) (m : ModuleKey) (o : NativeOrigin) : Decidable (OriginOK i m o) := by
  unfold OriginOK; infer_instance

/-- History is bound to unchanged exact source, with no recorded unsupported evaluator,
missing replay, or current replacement absent from the observed history. -/
def HistoryOK (c : Claim) (i : EnvironmentCensus) (m : ModuleKey) (o : HistoryObservation) : Prop :=
  o.moduleName = m.name.name ∧ o.before ∈ snapshotSources c ∧
  (∃ entry ∈ i.allModuleSources, entry.1 = m ∧ entry.2 = o.before) ∧
  o.after = o.before ∧ o.unsupported = #[] ∧
  ∀ r ∈ i.execution.roots, ∀ b ∈ r.boundaries,
    b.module = m.name.name → b.boundary = .runtimeReplacement →
      ∃ target ∈ b.replacement, (b.name, target) ∈ o.replacements
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : EnvironmentCensus) (m : ModuleKey) (o : HistoryObservation) : Decidable (HistoryOK c i m o) := by
  unfold HistoryOK; infer_instance

/-- Every selected graph root was checked and the resulting closure covers all claimed
modules. Plan-only and missing roots cannot satisfy a serialized-graph expectation. -/
def GraphOK (i : Census) (o : GraphObservation) : Prop :=
  o.plannedOnly = false ∧ o.failures = #[] ∧ o.selected = i.graphRoots ∧
  o.covered = i.graphCoverage.flatMap (·.2) ∧ o.selected ≠ #[] ∧
  o.selected.toList.Pairwise (· ≠ ·) ∧ o.checked.toList.Pairwise (· ≠ ·) ∧
  (∀ m ∈ o.selected, m ∈ o.checked ∧ m ∈ i.modules) ∧
  (∀ m ∈ o.checked, m ∈ o.selected) ∧ (∀ m ∈ i.modules, m ∈ o.covered) ∧
  ∀ m ∈ o.covered, m ∈ i.allModules
instance (i : Census) (o : GraphObservation) : Decidable (GraphOK i o) := by unfold GraphOK; infer_instance

set_option synthInstance.maxSize 1024 in
instance (c : Claim) (fences : Array FenceKey) (f : FenceKey) (o : ExampleObservation) :
    Decidable (ExampleExpectationOK c fences f o) := by
  unfold ExampleExpectationOK
  cases f.expectation <;> cases o.outcome <;> dsimp <;> infer_instance

/-- Exact stage/subject/evidence correspondence and each applicable normative conjunction.
There is no success case for a mismatched payload constructor or an unrequested subject. -/
def LocalStageOK (c : Claim) (i : EnvironmentCensus) (roles : Roles i.policy)
    (stage : Stage) (subject : LocalJobSubject) : JobEvidence → Prop
  | evidence => match stage, subject, evidence with
    | .admission, .scope, .admission observed => AdmissionOK i observed
    | .declarationPolicy, .declaration k, .declaration d =>
        d ∈ i.policy.declarations ∧ d.name = k.name.name ∧ d.module = k.moduleKey.name.name ∧
        ∃ profile ∈ profileForModule c d.module,
          DeclarationOK d (.conforming profile) roles.native roles.helpers
    | .execution, .root k, .execution r =>
        r ∈ i.execution.roots ∧ r.name = k.name.name ∧ r.module = k.moduleKey.name.name ∧
        ∀ request ∈ rootRequests c i r.name,
          r.unresolved = #[] ∧ ∀ b ∈ r.boundaries, BoundaryOK request b
    | .transcript, .module m, .transcript t =>
        t ∈ i.policy.transcripts ∧ t.module = m.name.name ∧
        ∃ entry ∈ i.moduleSources, entry.1 = m ∧ entry.2.uri = t.source ∧ entry.2.source = t.sourceContent
    | .history, .module m, .history observed => HistoryOK c i m observed
    | .origin, .module m, .origin observed => OriginOK i m observed
    | .documentationPresence, .module _, .documentationPresence doc => DocumentationPresenceOK doc
    | .documentationPresence, .declaration _, .documentationPresence doc => MaterialDocumentationOK doc
    | _, _, _ => False

set_option synthInstance.maxSize 2048 in
instance (c : Claim) (i : EnvironmentCensus) (roles : Roles i.policy)
    (stage : Stage) (subject : LocalJobSubject) (e : JobEvidence) :
    Decidable (LocalStageOK c i roles stage subject e) := by
  dsimp only [LocalStageOK]
  split <;> (try dsimp only [DocumentationPresenceOK]) <;> infer_instance

/-- When a former combined inventory was valid and role authentication agrees, its
declaration judgment is preserved for the identical locally retained declaration.
Role agreement is an explicit hypothesis, not a consequence of bare-name uniqueness. -/
theorem localDeclaration_preserves_flattened (c : Claim)
    (localInventory flattened : EnvironmentCensus)
    (localRoles : Roles localInventory.policy) (flattenedRoles : Roles flattened.policy)
    (key : DeclarationKey) (declaration : Declaration)
    (retained : declaration ∈ localInventory.policy.declarations)
    (native : ∀ n ∈ declaration.axioms, n ∈ localRoles.native ↔ n ∈ flattenedRoles.native)
    (helpers : declaration.name ∈ flattenedRoles.helpers → declaration.name ∈ localRoles.helpers)
    (accepted : LocalStageOK c flattened flattenedRoles .declarationPolicy
      (.declaration key) (.declaration declaration)) :
    LocalStageOK c localInventory localRoles .declarationPolicy
      (.declaration key) (.declaration declaration) := by
  change declaration ∈ _ ∧ _ ∧ _ ∧ _ at accepted ⊢
  refine ⟨retained, accepted.2.1, accepted.2.2.1, ?_⟩
  obtain ⟨profile, hp, judgment⟩ := accepted.2.2.2
  refine ⟨profile, hp, ?_⟩
  have compiler (n : Name) (hn : n ∈ declaration.axioms) :
      CompilerAxiom localRoles.native n ↔ CompilerAxiom flattenedRoles.native n := by
    simp only [CompilerAxiom, native n hn]
  rcases judgment with ⟨_, _, impossible⟩ | ⟨kind, hole, known, safety, trust, contract, foundation⟩
  · cases impossible
  · refine Or.inr ⟨kind, hole, ?_, ?_, ?_, contract, ?_⟩
    · intro n hn
      exact (known n hn).imp_right (compiler n hn).mpr
    · exact safety.imp_right helpers
    · rcases trust with impossible | free
      · cases impossible
      · exact Or.inr (fun n hn h => free n hn ((compiler n hn).mp h))
    · intro n hn
      exact (foundation n hn).imp_left (compiler n hn).mpr

/-- A coherently shared root retains every locally requested execution obligation.
The hypothesis compares complete roots, not merely matching module/name pairs. -/
theorem localExecution_preserves_flattened (c : Claim)
    (localInventory flattened : EnvironmentCensus)
    (localRoles : Roles localInventory.policy) (flattenedRoles : Roles flattened.policy)
    (key : RootKey) (root : ExecutionRoot)
    (retained : root ∈ localInventory.execution.roots)
    (requests : ∀ request ∈ rootRequests c localInventory root.name,
      request ∈ rootRequests c flattened root.name)
    (accepted : LocalStageOK c flattened flattenedRoles .execution (.root key) (.execution root)) :
    LocalStageOK c localInventory localRoles .execution (.root key) (.execution root) := by
  change root ∈ _ ∧ _ ∧ _ ∧ _ at accepted ⊢
  exact ⟨retained, accepted.2.1, accepted.2.2.1,
    fun request membership => accepted.2.2.2 request (requests request membership)⟩

/-- Data-level correspondence for restricting a valid combined observation.
This is a proof relation, not another acceptance evaluator. Admission records may be
projected; every other constructor retains its exact evidence. Source/role coherence
is required only for the retained declaration or module. -/
inductive LocalEvidenceTransfer (c : Claim) (localInventory flattened : EnvironmentCensus)
    (localRoles : Roles localInventory.policy) (flattenedRoles : Roles flattened.policy) :
    Stage → LocalJobSubject → JobEvidence → JobEvidence → Prop where
  | admission (before after : AdmissionObservation)
      (modules : after.modules = localInventory.admissionModules)
      (required : after.required = localInventory.admissionDeclarations)
      (requested : ∀ d ∈ localInventory.admissionDeclarations, d ∈ flattened.admissionDeclarations)
      (subsequence : after.admitted.toList.Sublist before.admitted.toList)
      (retained : ∀ d, d ∈ after.admitted ↔ d ∈ before.admitted ∧ d ∈ after.required)
      (failures : after.failures = before.failures) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .admission .scope (.admission before) (.admission after)
  | declaration (key : DeclarationKey) (d : Declaration)
      (retained : d ∈ localInventory.policy.declarations)
      (native : ∀ n ∈ d.axioms, n ∈ localRoles.native ↔ n ∈ flattenedRoles.native)
      (helpers : d.name ∈ flattenedRoles.helpers → d.name ∈ localRoles.helpers) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .declarationPolicy (.declaration key) (.declaration d) (.declaration d)
  | execution (key : RootKey) (r : ExecutionRoot)
      (retained : r ∈ localInventory.execution.roots)
      (requests : ∀ request ∈ rootRequests c localInventory r.name,
        request ∈ rootRequests c flattened r.name) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .execution (.root key) (.execution r) (.execution r)
  | transcript (key : ModuleKey) (t : Frontend.Transcript)
      (retained : t ∈ localInventory.policy.transcripts)
      (sources : ∀ entry ∈ flattened.moduleSources, entry.1 = key → entry ∈ localInventory.moduleSources) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .transcript (.module key) (.transcript t) (.transcript t)
  | history (key : ModuleKey) (o : HistoryObservation)
      (roots : ∀ root ∈ localInventory.execution.roots, root ∈ flattened.execution.roots)
      (sources : ∀ entry ∈ flattened.allModuleSources, entry.1 = key → entry ∈ localInventory.allModuleSources) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .history (.module key) (.history o) (.history o)
  | origin (key : ModuleKey) (o : NativeOrigin)
      (roots : ∀ root ∈ localInventory.execution.roots, root ∈ flattened.execution.roots) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .origin (.module key) (.origin o) (.origin o)
  | moduleDocumentation (key : ModuleKey) (doc : Option String) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .documentationPresence (.module key) (.documentationPresence doc) (.documentationPresence doc)
  | declarationDocumentation (key : DeclarationKey) (doc : Option String) :
      LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles
        .documentationPresence (.declaration key) (.documentationPresence doc) (.documentationPresence doc)

/-- All local stages preserve the former obligations under the stated raw-data
correspondence. No hypothesis assumes the new LocalStageOK or PolicyOK judgment. -/
theorem LocalEvidenceTransfer.sound {c : Claim} {localInventory flattened : EnvironmentCensus}
    {localRoles : Roles localInventory.policy} {flattenedRoles : Roles flattened.policy}
    {stage : Stage} {subject : LocalJobSubject} {before after : JobEvidence}
    (transfer : LocalEvidenceTransfer c localInventory flattened localRoles flattenedRoles stage subject before after)
    (accepted : LocalStageOK c flattened flattenedRoles stage subject before) :
    LocalStageOK c localInventory localRoles stage subject after := by
  cases transfer with
  | admission before after modules required requested subsequence retained failures =>
    rcases accepted with ⟨oldModules, oldRequired, unique, forward, backward, clean⟩
    refine ⟨modules, required, unique.sublist subsequence, ?_, ?_, failures.trans clean⟩
    · intro d hd
      apply (retained d).mpr
      refine ⟨forward d ?_, hd⟩
      rw [oldRequired]
      exact requested d (required ▸ hd)
    · intro d hd
      exact ((retained d).mp hd).2
  | declaration key d retained native helpers =>
    exact localDeclaration_preserves_flattened c localInventory flattened localRoles flattenedRoles
      key d retained native helpers accepted
  | execution key r retained requests =>
    exact localExecution_preserves_flattened c localInventory flattened localRoles flattenedRoles
      key r retained requests accepted
  | transcript key t retained sources =>
    rcases accepted with ⟨_, name, entry, member, identity, uri, bytes⟩
    exact ⟨retained, name, entry, sources entry member identity, identity, uri, bytes⟩
  | history key o roots sources =>
    rcases accepted with ⟨name, snapshot, source, unchanged, supported, history⟩
    obtain ⟨entry, member, identity, bytes⟩ := source
    exact ⟨name, snapshot, ⟨entry, sources entry member identity, identity, bytes⟩,
      unchanged, supported, fun root member => history root (roots root member)⟩
  | origin key o roots =>
    exact ⟨accepted.1, fun root member => accepted.2 root (roots root member)⟩
  | moduleDocumentation => exact accepted
  | declarationDocumentation => exact accepted

/-- The identity correspondence covers every supported local stage. In particular a
singleton run needs no additional role/source restriction hypothesis. -/
theorem LocalEvidenceTransfer.refl {c : Claim} {inventory : EnvironmentCensus}
    {roles : Roles inventory.policy} {stage : Stage} {subject : LocalJobSubject} {evidence : JobEvidence}
    (accepted : LocalStageOK c inventory roles stage subject evidence) :
    LocalEvidenceTransfer c inventory inventory roles roles stage subject evidence evidence := by
  dsimp only [LocalStageOK] at accepted
  split at accepted <;> subst_vars
  · exact .admission _ _ accepted.1 accepted.2.1 (fun _ h => h) (.refl _)
      (fun d => ⟨fun h => ⟨h, accepted.2.2.2.2.1 d h⟩, And.left⟩) rfl
  · exact .declaration _ _ accepted.1 (fun _ _ => Iff.rfl) (fun h => h)
  · exact .execution _ _ accepted.1 (fun _ h => h)
  · exact .transcript _ _ accepted.1 (fun _ h _ => h)
  · exact .history _ _ (fun _ h => h) (fun _ h _ => h)
  · exact .origin _ _ (fun _ h => h)
  · exact .moduleDocumentation _ _
  · exact .declarationDocumentation _ _
  · exact False.elim accepted

/-- Lookup uses the coordinator's complete environment identity, including snapshot.
The dependent role family cannot be substituted from another environment. -/
def EnvironmentStageOK (c : Claim) (i : Census) (roles : CensusRoles i)
    (key : EnvironmentKey) (stage : Stage) (subject : LocalJobSubject) (e : JobEvidence) : Prop :=
  if h : key.index < i.environments.size then
    let slot : Fin i.environments.size := ⟨key.index, h⟩
    i.environments[slot].request.key = key ∧
      LocalStageOK c i.environments[slot] (roles slot) stage subject e
  else False

instance (c : Claim) (i : Census) (roles : CensusRoles i)
    (key : EnvironmentKey) (stage : Stage) (subject : LocalJobSubject) (e : JobEvidence) :
    Decidable (EnvironmentStageOK c i roles key stage subject e) := by
  unfold EnvironmentStageOK
  split <;> infer_instance

/-- Accepted local evidence resolves only at its requested position and complete key. -/
theorem environmentStageOK_resolves (c : Claim) (i : Census) (roles : CensusRoles i)
    (key : EnvironmentKey) (stage : Stage) (subject : LocalJobSubject) (e : JobEvidence)
    (h : EnvironmentStageOK c i roles key stage subject e) :
    ∃ slot : Fin i.environments.size, slot.val = key.index ∧
      i.environments[slot].request.key = key ∧
      LocalStageOK c i.environments[slot] (roles slot) stage subject e := by
  by_cases bound : key.index < i.environments.size
  · exact ⟨⟨key.index, bound⟩, rfl, by simpa [EnvironmentStageOK, bound] using h⟩
  · simp [EnvironmentStageOK, bound] at h

/-- Reindexing changes no local policy predicate, including every execution request. -/
theorem environmentStageOK_at (c : Claim) (i : Census) (roles : CensusRoles i)
    (slot : Fin i.environments.size)
    (index : i.environments[slot].request.key.index = slot.val)
    (stage : Stage) (subject : LocalJobSubject) (e : JobEvidence) :
    EnvironmentStageOK c i roles i.environments[slot].request.key stage subject e ↔
      LocalStageOK c i.environments[slot] (roles slot) stage subject e := by
  have bound : i.environments[slot].request.key.index < i.environments.size := by
    rw [index]
    exact slot.isLt
  unfold EnvironmentStageOK
  rw [dite_eq_left bound]
  have slots : (⟨i.environments[slot].request.key.index, bound⟩ : Fin i.environments.size) = slot :=
    Fin.ext index
  change (i.environments[(⟨i.environments[slot].request.key.index, bound⟩ : Fin i.environments.size)].request.key =
    i.environments[slot].request.key ∧
    LocalStageOK c i.environments[(⟨i.environments[slot].request.key.index, bound⟩ : Fin i.environments.size)]
      (roles ⟨i.environments[slot].request.key.index, bound⟩) stage subject e) ↔ _
  have transport (a b : Fin i.environments.size) (same : a = b) :
      (i.environments[a].request.key = i.environments[b].request.key ∧
        LocalStageOK c i.environments[a] (roles a) stage subject e) ↔
      LocalStageOK c i.environments[b] (roles b) stage subject e := by
    cases same
    exact ⟨And.right, fun h => ⟨rfl, h⟩⟩
  exact transport _ _ slots

theorem environmentStageOK_wrong_key (c : Claim) (i : Census) (roles : CensusRoles i)
    (key : EnvironmentKey) (stage : Stage) (subject : LocalJobSubject) (e : JobEvidence)
    (mismatch : ∀ slot : Fin i.environments.size,
      slot.val = key.index → i.environments[slot].request.key ≠ key) :
    ¬ EnvironmentStageOK c i roles key stage subject e := by
  intro h
  obtain ⟨slot, position, identity, _⟩ := environmentStageOK_resolves c i roles key stage subject e h
  exact mismatch slot position identity

theorem environmentExecution_foreign_root_refused (c : Claim) (i : Census) (roles : CensusRoles i)
    (environment : EnvironmentKey) (key : RootKey) (root : ExecutionRoot)
    (absent : ∀ slot : Fin i.environments.size, i.environments[slot].request.key = environment →
      root ∉ i.environments[slot].execution.roots) :
    ¬ EnvironmentStageOK c i roles environment .execution (.root key) (.execution root) := by
  intro accepted
  obtain ⟨slot, _, identity, policy⟩ := environmentStageOK_resolves c i roles environment
    .execution (.root key) (.execution root) accepted
  exact absent slot identity policy.1

theorem environmentExecution_request_refused (c : Claim) (i : Census) (roles : CensusRoles i)
    (environment : EnvironmentKey) (key : RootKey) (root : ExecutionRoot)
    (failure : ∀ slot : Fin i.environments.size, i.environments[slot].request.key = environment →
      ∃ request ∈ rootRequests c i.environments[slot] root.name,
        root.unresolved ≠ #[] ∨ ∃ boundary ∈ root.boundaries, ¬ BoundaryOK request boundary) :
    ¬ EnvironmentStageOK c i roles environment .execution (.root key) (.execution root) := by
  intro accepted
  obtain ⟨slot, _, identity, policy⟩ := environmentStageOK_resolves c i roles environment
    .execution (.root key) (.execution root) accepted
  obtain ⟨request, member, unresolved | boundaryFailure⟩ := failure slot identity
  · exact unresolved (policy.2.2.2 request member).1
  · obtain ⟨boundary, reached, denied⟩ := boundaryFailure
    exact denied ((policy.2.2.2 request member).2 boundary reached)

def StageOK (c : Claim) (i : Census) (roles : CensusRoles i) (key : JobKey) : JobEvidence → Prop
  | evidence => match key.stage, key.subject, evidence with
    | stage, .environment environment subject, e => EnvironmentStageOK c i roles environment stage subject e
    | .configuration, .scope, .configuration assignments targets => ScopeOK c i assignments targets
    | .discovery, .scope, .discovery observed => observed = i
    | .build, .scope, .build observed => BuildOK observed
    | .documentScan, .scope, .documentScan observed => DocumentOK c i observed
    | .example, .fence f, .example observed => ExampleExpectationOK c i.fences f observed
    | .graph, .scope, .graph observed => GraphOK i observed
    | _, _, _ => False

set_option synthInstance.maxSize 2048 in
instance (c : Claim) (i : Census) (roles : CensusRoles i) (k : JobKey) (e : JobEvidence) :
    Decidable (StageOK c i roles k e) := by
  dsimp only [StageOK]
  split <;> (try dsimp only [DocumentationPresenceOK]) <;> infer_instance

/-- Global evidence transfers by exact data correspondence. Discovery replaces the
former census observation with the complete newly admitted census; no success bit is
copied. Configuration, build, document and graph obligations keep their predicates. -/
inductive GlobalEvidenceTransfer (previous current : Census) :
    Stage → JobSubject → JobEvidence → JobEvidence → Prop where
  | configuration (assignments : Array TargetAssignment) (targets : Array DiscoveredTarget)
      (configured : current.configuredTargets = previous.configuredTargets)
      (discovered : current.discoveredTargets = previous.discoveredTargets) :
      GlobalEvidenceTransfer previous current .configuration .scope
        (.configuration assignments targets) (.configuration assignments targets)
  | discovery : GlobalEvidenceTransfer previous current .discovery .scope
      (.discovery previous) (.discovery current)
  | build (observation : BuildObservation) : GlobalEvidenceTransfer previous current .build .scope
      (.build observation) (.build observation)
  | documents (observation : DocumentObservation) (fences : current.fences = previous.fences) :
      GlobalEvidenceTransfer previous current .documentScan .scope
        (.documentScan observation) (.documentScan observation)
  | example (fence : FenceKey) (observation : ExampleObservation) (fences : current.fences = previous.fences) :
      GlobalEvidenceTransfer previous current .example (.fence fence) (.example observation) (.example observation)
  | graph (observation : GraphObservation)
      (roots : current.graphRoots = previous.graphRoots)
      (coverage : current.graphCoverage = previous.graphCoverage)
      (modules : current.modules = previous.modules)
      (allModules : current.allModules = previous.allModules) :
      GlobalEvidenceTransfer previous current .graph .scope (.graph observation) (.graph observation)

theorem GlobalEvidenceTransfer.sound {c : Claim} {previous current : Census}
    (oldRoles : CensusRoles previous) (newRoles : CensusRoles current)
    (key : JobKey) {before after : JobEvidence}
    (transfer : GlobalEvidenceTransfer previous current key.stage key.subject before after)
    (accepted : StageOK c previous oldRoles key before) : StageOK c current newRoles key after := by
  cases key
  cases transfer with
  | configuration assignments targets configured discovered =>
    rcases accepted with ⟨asgn, target, partition⟩
    refine ⟨asgn.trans configured.symm, target.trans discovered.symm, ?_⟩
    simpa only [TargetPartitionOK, configured, discovered] using partition
  | discovery => rfl
  | build => exact accepted
  | documents observation fences =>
    exact ⟨accepted.1, accepted.2.1.trans fences.symm, accepted.2.2⟩
  | «example» fence observation fences =>
    simpa only [StageOK, fences] using accepted
  | graph observation roots coverage modules allModules =>
    simpa only [StageOK, GraphOK, roots, coverage, modules, allModules] using accepted

theorem GlobalEvidenceTransfer.refl {c : Claim} {inventory : Census} (roles : CensusRoles inventory)
    (key : JobKey) (evidence : JobEvidence)
    (global : ∀ environment subject, key.subject ≠ .environment environment subject)
    (accepted : StageOK c inventory roles key evidence) :
    GlobalEvidenceTransfer inventory inventory key.stage key.subject evidence evidence := by
  cases key
  dsimp only [StageOK] at accepted
  split at accepted <;> subst_vars
  · exact False.elim (global _ _ rfl)
  · exact .configuration _ _ rfl rfl
  · exact .discovery
  · exact .build _
  · exact .documents _ rfl
  · exact .example _ _ rfl
  · exact .graph _ rfl rfl rfl rfl
  · exact False.elim accepted

/-- Policy acceptance recomputes the applicable field relation for this exact bound snapshot.
The completion tag is an observed terminal producer state, not proof of external execution. -/
def PolicyOK (c : Claim) (i : Census) (roles : CensusRoles i) (o : JobObservation) : Prop :=
  o.key.claim = c ∧ o.snapshot = c.val.snapshot ∧ o.completion = .completed ∧
  StageOK c i roles o.key o.evidence
instance (c : Claim) (i : Census) (roles : CensusRoles i) (o : JobObservation) :
    Decidable (PolicyOK c i roles o) := by unfold PolicyOK; infer_instance

end RegulaPolicy
