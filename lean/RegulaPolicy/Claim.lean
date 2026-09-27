import RegulaPolicy.Domain

/-! # Claims, snapshots and coverage keys

Claims, snapshots and coverage keys for policy consumers. Claims represent requested
mechanical scope, never an accepted result. Sources and dependency states are exact
observations; the IO collector remains responsible for their truthful acquisition. -/
namespace RegulaPolicy

/-- The toolchain and checker that produced an observation, as reported texts. -/
structure ToolchainIdentity where
  /-- The Lean version string (`Lean.versionString` of the producer). -/
  leanVersion : String
  /-- The Lean compiler's source commit (`Lean.githash` of the producer). -/
  compilerCommit : String
  /-- The source revision of the Regula checker that produced the observation. -/
  producerRevision : String
  deriving Repr, DecidableEq

/-- A pin alone cannot identify a modified or path dependency; retain its actual files. -/
structure DependencyState where
  /-- The dependency's Lake package name. -/
  package : String
  /-- The Git `HEAD` commit of the dependency's checkout, when the collector found one. -/
  nominalRevision : Option String
  /-- Whether the collector found no revision, or found the checkout changed from it (for the
  checker's own collector, `git status` reporting a declared source or configuration input). -/
  dirty : Bool
  /-- The dependency's captured files with their exact text. -/
  files : Array SourceSnapshot
  deriving Repr, DecidableEq

/-- The exact inputs a request is about: source texts, configuration, toolchain and
dependency states, as the collector captured them. -/
structure Snapshot where
  /-- The project's source files, each with its URI and exact text. -/
  sources : Array SourceSnapshot
  /-- The project's configuration inputs, as one text under the project's URI. -/
  configuration : SourceSnapshot
  /-- The toolchain and checker identity of the producer. -/
  toolchain : ToolchainIdentity
  /-- The state of each Lake dependency. -/
  dependencies : Array DependencyState
  deriving Repr, DecidableEq

/- Repeated jobs share one immutable snapshot. Lean's established pointer-equality
shortcut decides the same equality and otherwise runs full structural comparison;
no digest, identity token or assumed equality replaces source bytes. -/
attribute [-instance] instDecidableEqSnapshot
instance snapshotDecidableEq : DecidableEq Snapshot := fun left right =>
  withPtrEqDecEq left right (fun _ => instDecidableEqSnapshot left right)

/-- Structural validity of exact content maps; truthful acquisition stays operational. -/
def Snapshot.Valid (s : Snapshot) : Prop :=
  s.sources.toList.Pairwise (fun a b => a.uri ≠ b.uri) ∧
  (∀ f ∈ s.sources, f.uri ≠ "") ∧ s.configuration.uri ≠ "" ∧
  s.toolchain.leanVersion ≠ "" ∧ s.toolchain.compilerCommit ≠ "" ∧
  s.toolchain.producerRevision ≠ "" ∧
  s.dependencies.toList.Pairwise (fun a b => a.package ≠ b.package) ∧
  (∀ d ∈ s.dependencies, d.package ≠ "" ∧
    d.files.toList.Pairwise (fun a b => a.uri ≠ b.uri) ∧ ∀ f ∈ d.files, f.uri ≠ "")
instance instDecidableSnapshotValid (s : Snapshot) : Decidable s.Valid := by
    unfold Snapshot.Valid; infer_instance

/-- A snapshot that satisfies `Snapshot.Valid`. -/
abbrev AdmittedSnapshot := { s : Snapshot // s.Valid }

/-- Admit `s` unchanged when it satisfies `Snapshot.Valid`; otherwise an error.
`admitSnapshot_exact` shows every valid snapshot is admitted as itself. -/
def admitSnapshot (s : Snapshot) : Except String AdmittedSnapshot :=
  if h : s.Valid then .ok ⟨s, h⟩ else .error "invalid snapshot identity or content map"

theorem admitSnapshot_exact (s : Snapshot) (h : s.Valid) :
    admitSnapshot s = .ok ⟨s, h⟩ := by simp [admitSnapshot, h]

/-- Snapshot plus exact module identity. Filesystem provenance is not a proof field. -/
structure ModuleKey where
  /-- The snapshot the module belongs to. -/
  snapshot : AdmittedSnapshot
  /-- The module's name. -/
  name : Identity
  deriving Repr, DecidableEq

/-- A declaration identified by its module and its name. -/
structure DeclarationKey where
  /-- The module that owns the declaration. -/
  moduleKey : ModuleKey
  /-- The declaration's name. -/
  name : Identity
  deriving Repr, DecidableEq

/-- An executable root, identified as the declaration it names. -/
abbrev RootKey := DeclarationKey

/-- Distinct observed occurrences are legitimate even for one reached declaration. -/
structure BoundaryKey where
  /-- The executable root whose execution closure reaches the boundary. -/
  root : RootKey
  /-- The declaration at which the boundary is reached. -/
  reached : DeclarationKey
  /-- The kind of execution boundary. -/
  kind : BoundaryKind
  /-- The declaration that replaces `reached` at run time, for a replacement boundary. -/
  replacement : Option DeclarationKey
  /-- Distinguishes separately observed occurrences of the same boundary. -/
  occurrence : Nat
  /-- `reached` belongs to the root's snapshot. -/
  reachedSnapshot : reached.moduleKey.snapshot = root.moduleKey.snapshot
  /-- Any `replacement` belongs to the root's snapshot. -/
  replacementSnapshot : ∀ r ∈ replacement, r.moduleKey.snapshot = root.moduleKey.snapshot
  deriving Repr, DecidableEq

/-- Location tokens retain exact source bytes or an explicitly broader subject. They are
not reconstructed from a pretty name; correspondence with compiler diagnostics is operational. -/
inductive PolicyLocation where
  /-- A byte range of one source file's exact text. -/
  | source (snapshot : SourceSnapshot) (range : ByteRange)
  /-- A whole module. -/
  | module (key : ModuleKey)
  /-- The whole project of a snapshot. -/
  | project (snapshot : AdmittedSnapshot)
  deriving Repr, DecidableEq

/-- Transported stable identity from the sole registry adapter. The pure core compares
these values; it does not define a second RuleId vocabulary or prove the adapter's mapping. -/
structure ExpectedDiagnostic where
  /-- The rule ID text, such as `RG1001`. -/
  rule : String
  /-- The expected subreason (applicability), or `none` when any is accepted. -/
  subreason : Option String
  /-- The diagnostic's primary location. -/
  primary : PolicyLocation
  /-- The diagnostic's related locations, in order. -/
  related : Array PolicyLocation
  deriving Repr, DecidableEq

/-- What a documentation fence's example is declared to do. -/
inductive FenceExpectation where
  /-- The example elaborates and meets the Standard-Logical declaration policy. -/
  | positive
  /-- The compiler rejects the example with an error that matches `pattern`. -/
  | compilerRejection (pattern : String) (nonempty : pattern ≠ "")
  /-- The checker rejects the example with diagnostics that match `diagnostics` one for one, in
  order (`DiagnosticMatches`). -/
  | policyRejection (diagnostics : List ExpectedDiagnostic) (nonempty : diagnostics ≠ [])
  /-- The example elaborates and meets the teaching policy, and one of its declarations depends
  on a compiler-trusting axiom. -/
  | trustedTeaching
  deriving Repr, DecidableEq

/-- Rule identity tokens in policy-negative expectations must be validated by the sole
registry adapter. The policy library deliberately defines no second RuleId enumeration. -/
structure FenceKey where
  /-- The document that contains the fence, with its exact text. -/
  document : SourceSnapshot
  /-- The byte range of the fence's opening delimiter line. -/
  opening : ByteRange
  /-- The byte range of the fence's body, the example source. -/
  body : ByteRange
  /-- The byte range of the fence's closing delimiter line. -/
  closing : ByteRange
  /-- What the fence's example is declared to do. -/
  expectation : FenceExpectation
  /-- The document has a URI. -/
  nonemptyURI : document.uri ≠ ""
  /-- The opening line, body and closing line follow each other in the document. -/
  ordered : opening.start ≤ opening.stop ∧ opening.stop ≤ body.start ∧
    body.start ≤ body.stop ∧ body.stop ≤ closing.start ∧ closing.start ≤ closing.stop
  /-- Every range boundary is a valid UTF-8 position of the document's text. -/
  validPositions : ∀ n ∈
      [opening.start, opening.stop, body.start, body.stop, closing.start, closing.stop],
    (String.Pos.Raw.isValid document.source ⟨n⟩) = true
  deriving Repr, DecidableEq

/-- What a request covers. -/
inductive Scope where
  /-- Every claimed surface of the project's manifest. -/
  | project
  /-- One source file, under the claimed profile and execution claim. -/
  | file (source : SourceSnapshot) (profile : ConformingProfile) (execution : ExecutionClaim)
  /-- The Lean example fences of these documents. -/
  | documentation (documents : Array SourceSnapshot)
  /-- One module's editor buffer, under the claimed profile and execution claim. -/
  | editor (moduleName : Identity) (source : SourceSnapshot)
      (profile : ConformingProfile) (execution : ExecutionClaim)
  deriving Repr, DecidableEq

/-- The kind of work one job performs; `requiredStages` fixes which a request's mode needs. -/
inductive Stage where
  /-- Classify the Lake targets against the manifest's surfaces. -/
  | configuration
  /-- Discover the request's census. -/
  | discovery
  /-- Build the requested surface. -/
  | build
  /-- Replay one environment's owned declarations in the kernel. -/
  | admission
  /-- Decide one declaration against its profile. -/
  | declarationPolicy
  /-- Decide the execution closure of one executable root or boundary. -/
  | execution
  /-- Record one module's frontend transcript. -/
  | transcript
  /-- Record one module's elaboration history. -/
  | history
  /-- Check the native-code origin of one module. -/
  | origin
  /-- Look up the docstring of one module or declaration. -/
  | documentationPresence
  /-- Scan the requested documents for fences. -/
  | documentScan
  /-- Produce one documentation example. -/
  | example
  /-- Check the serialized module graph. -/
  | graph
  deriving Repr, DecidableEq

/-- Per-surface assignments preserve distinct selected maxima. -/
structure SurfaceAssignment where
  /-- The claimed Lake target's name. -/
  target : String
  /-- The target's modules. -/
  modules : Array Identity
  /-- The foundation profile claimed for the target. -/
  profile : ConformingProfile
  /-- The execution claim for the target. -/
  execution : ExecutionClaim
  deriving Repr, DecidableEq

/-- A requested claim before validation: `Claim` holds the ones that satisfy
`ClaimCandidate.Valid`. -/
structure ClaimCandidate where
  /-- What the request covers. -/
  scope : Scope
  /-- The evidence mode the request is audited in. -/
  mode : EvidenceMode
  /-- The exact inputs the request is about. -/
  snapshot : Snapshot
  /-- The claimed surfaces; `ClaimCandidate.Valid` requires some for a project scope and none
  for the other scopes. -/
  surfaces : Array SurfaceAssignment
  deriving Repr, DecidableEq

attribute [-instance] instDecidableEqClaimCandidate
/-- Preserve exact structural fallback when requests are not shared at runtime. -/
instance claimCandidateDecidableEq : DecidableEq ClaimCandidate := fun left right =>
  withPtrEqDecEq left right (fun _ => instDecidableEqClaimCandidate left right)

/-- Supported scope/mode combinations. Fresh files never acquire whole-project scope. -/
def scopeModeCompatible : Scope → EvidenceMode → Bool
  | .project, .freshProject | .project, .incrementalProject | .project, .serializedGraph => true
  | .file .., .freshFile => true
  | .documentation _, .documentationExample => true
  | .editor .., .editorSnapshot => true
  | _, _ => false

/-- Functional source maps and disjoint positive module ownership; empty project libraries
remain unsupported. This does not assert completeness of an external Lake inventory. -/
def ClaimCandidate.Valid (c : ClaimCandidate) : Prop :=
  scopeModeCompatible c.scope c.mode = true ∧
  c.snapshot.Valid ∧
  (∀ s ∈ c.surfaces, s.target ≠ "" ∧ s.modules.size > 0) ∧
  (c.surfaces.toList.flatMap (fun s => s.modules.toList)).Pairwise (fun a b => a.name ≠ b.name) ∧
  c.surfaces.toList.Pairwise (fun a b => a.target ≠ b.target) ∧
  (match c.scope with
   | .project => c.surfaces.size > 0 ∧ ∀ s ∈ c.surfaces, s.modules.size > 0
   | .file source .. | .editor _ source .. =>
                        source ∈ c.snapshot.sources ∧ c.surfaces.isEmpty = true
   | .documentation documents =>
       documents.size > 0 ∧ documents.toList.Pairwise (fun a b => a.uri ≠ b.uri) ∧
       (∀ d ∈ documents, d ∈ c.snapshot.sources) ∧ c.surfaces.isEmpty = true)
instance instDecidableClaimValid (c : ClaimCandidate) : Decidable c.Valid := by
  unfold ClaimCandidate.Valid
  cases c.scope <;> infer_instance

/-- Positive claim data has only conforming profile assignments. Teaching and no-profile
inspection are separate request constructors in Decision, not inhabitants of this type. -/
abbrev Claim := { c : ClaimCandidate // c.Valid }

/-- Admit `c` unchanged when it satisfies `ClaimCandidate.Valid`; otherwise an error. -/
def admitClaim (c : ClaimCandidate) : Except String Claim :=
  if h : c.Valid then .ok ⟨c, h⟩ else .error "unsupported or malformed policy claim"

/-- All and only valid candidates can be admitted, unchanged. -/
theorem admitClaim_exact (c : ClaimCandidate) (h : c.Valid) :
    admitClaim c = .ok ⟨c, h⟩ := by simp [admitClaim, h]

/-- Whole-project mandatory stages are derived; callers cannot select a shorter list. -/
def requiredStages (c : Claim) : List Stage :=
  match c.val.mode with
  | .freshProject | .incrementalProject =>
      [.configuration, .discovery, .build, .admission, .declarationPolicy, .execution,
       .transcript, .history, .origin, .documentationPresence]
  | .freshFile => [.discovery, .build, .admission, .declarationPolicy, .execution,
      .transcript, .history, .origin]
  | .documentationExample => [.discovery, .build, .documentScan, .example]
  | .serializedGraph => [.configuration, .discovery, .build, .graph]
  | .editorSnapshot => [.discovery, .admission, .declarationPolicy, .execution,
      .transcript, .history, .origin, .documentationPresence]

/-- One inspection environment of a request: its snapshot and its position among the census's
environments. -/
structure EnvironmentKey where
  /-- The snapshot the environment is built from. -/
  snapshot : AdmittedSnapshot
  /-- The environment's position in the census's environment list. -/
  index : Nat
  deriving Repr, DecidableEq

/-- Coordinator-selected identity and complete positive module assignment. -/
structure EnvironmentRequest where
  /-- The environment's identity. -/
  key : EnvironmentKey
  /-- The claimed modules assigned to the environment. -/
  modules : Array ModuleKey
  deriving Repr, DecidableEq

/-- What a job inside one environment is about. -/
inductive LocalJobSubject where
  /-- The whole environment. -/
  | scope
  /-- One module. -/
  | module (key : ModuleKey)
  /-- One declaration. -/
  | declaration (key : DeclarationKey)
  /-- One executable root. -/
  | root (key : RootKey)
  /-- One execution boundary reached from a root. -/
  | boundary (key : BoundaryKey)
  deriving Repr, DecidableEq

/-- What a job is about. -/
inductive JobSubject where
  /-- The whole request. -/
  | scope
  /-- A subject inside one environment of the request. -/
  | environment (key : EnvironmentKey) (subject : LocalJobSubject)
  /-- One documentation fence. -/
  | fence (key : FenceKey)
  deriving Repr, DecidableEq

/-- Stage tags restrict the kind of evidence subject they can request. -/
def stageSubjectCompatible : Stage → JobSubject → Bool
  | .configuration, .scope | .discovery, .scope | .build, .scope
  | .documentScan, .scope
  | .graph, .scope => true
  | .admission, .environment _ .scope => true
  | .transcript, .environment _ (.module _) | .history, .environment _ (.module _)
  | .origin, .environment _ (.module _) | .documentationPresence, .environment _ (.module _) => true
  | .declarationPolicy, .environment _ (.declaration _)
  | .documentationPresence, .environment _ (.declaration _) => true
  | .execution, .environment _ (.root _) | .execution, .environment _ (.boundary _) => true
  | .example, .fence _ => true
  | _, _ => false

/-- Every subject retains the exact snapshot of its requested claim. -/
def LocalSubjectSnapshotOK (claim : Claim) : LocalJobSubject → Prop
  | .scope => True
  | .module k => k.snapshot.val = claim.val.snapshot
  | .declaration k | .root k => k.moduleKey.snapshot.val = claim.val.snapshot
  | .boundary k => k.root.moduleKey.snapshot.val = claim.val.snapshot
instance (claim : Claim) (subject : LocalJobSubject) : Decidable
    (LocalSubjectSnapshotOK claim subject) := by
  cases subject <;> unfold LocalSubjectSnapshotOK <;> infer_instance

/-- A job subject belongs to the claim's snapshot: an environment subject's environment and
local subject use it (`LocalSubjectSnapshotOK`), a fence's document is one of its sources, and
the whole request always does. -/
def SubjectSnapshotOK (claim : Claim) : JobSubject → Prop
  | .scope => True
  | .environment key subject => key.snapshot.val = claim.val.snapshot ∧
                                 LocalSubjectSnapshotOK claim subject
  | .fence k => k.document ∈ claim.val.snapshot.sources
instance (claim : Claim) (subject : JobSubject) : Decidable (SubjectSnapshotOK claim subject) := by
  cases subject <;> unfold SubjectSnapshotOK <;> infer_instance

/-- An attempt identifier is transport metadata, never part of a required job key. -/
structure JobKey where
  /-- The claim the job serves. -/
  claim : Claim
  /-- The work the job performs. -/
  stage : Stage
  /-- What the job is about. -/
  subject : JobSubject
  /-- The claim's mode requires the stage. -/
  requiredStage : stage ∈ requiredStages claim
  /-- The stage accepts this kind of subject. -/
  compatibleSubject : stageSubjectCompatible stage subject = true
  /-- The subject belongs to the claim's snapshot. -/
  subjectSnapshot : SubjectSnapshotOK claim subject
  deriving Repr, DecidableEq
/-- Admit a requested stage/subject without inventing a compatible replacement. -/
def admitJobKey (claim : Claim) (stage : Stage) (subject : JobSubject) : Except String JobKey :=
  if hr : stage ∈ requiredStages claim then
    if hc : stageSubjectCompatible stage subject = true then
      if hs : SubjectSnapshotOK claim subject then
        .ok ⟨claim, stage, subject, hr, hc, hs⟩
      else .error "job subject snapshot differs from requested claim"
    else .error "job stage and subject are incompatible"
  else .error "job stage is not required by requested mode"

/-- Every valid exact job is reconstructed, with no default stage or subject. -/
theorem admitJobKey_exact (key : JobKey) :
    admitJobKey key.claim key.stage key.subject = .ok key := by
  unfold admitJobKey
  rw [dite_eq_left key.requiredStage, dite_eq_left key.compatibleSubject,
      dite_eq_left key.subjectSnapshot]

end RegulaPolicy
