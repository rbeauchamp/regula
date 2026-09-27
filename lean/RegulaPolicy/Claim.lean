import RegulaPolicy.Domain

/-! Claims, snapshots and coverage keys for policy consumers. Claims represent requested
mechanical scope, never an accepted result. Sources and dependency states are exact
observations; the IO collector remains responsible for their truthful acquisition. -/
namespace RegulaPolicy

structure ToolchainIdentity where
  leanVersion : String
  compilerCommit : String
  producerRevision : String
  deriving Repr, DecidableEq

/-- A pin alone cannot identify a modified or path dependency; retain its actual files. -/
structure DependencyState where
  package : String
  nominalRevision : Option String
  dirty : Bool
  files : Array SourceSnapshot
  deriving Repr, DecidableEq

structure Snapshot where
  sources : Array SourceSnapshot
  configuration : SourceSnapshot
  toolchain : ToolchainIdentity
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
instance instDecidableSnapshotValid (s : Snapshot) : Decidable s.Valid := by unfold Snapshot.Valid; infer_instance

abbrev AdmittedSnapshot := { s : Snapshot // s.Valid }

def admitSnapshot (s : Snapshot) : Except String AdmittedSnapshot :=
  if h : s.Valid then .ok ⟨s, h⟩ else .error "invalid snapshot identity or content map"

theorem admitSnapshot_exact (s : Snapshot) (h : s.Valid) :
    admitSnapshot s = .ok ⟨s, h⟩ := by simp [admitSnapshot, h]

/-- Snapshot plus exact module identity. Filesystem provenance is not a proof field. -/
structure ModuleKey where
  snapshot : AdmittedSnapshot
  name : Identity
  deriving Repr, DecidableEq

structure DeclarationKey where
  moduleKey : ModuleKey
  name : Identity
  deriving Repr, DecidableEq

abbrev RootKey := DeclarationKey

/-- Distinct observed occurrences are legitimate even for one reached declaration. -/
structure BoundaryKey where
  root : RootKey
  reached : DeclarationKey
  kind : BoundaryKind
  replacement : Option DeclarationKey
  occurrence : Nat
  reachedSnapshot : reached.moduleKey.snapshot = root.moduleKey.snapshot
  replacementSnapshot : ∀ r ∈ replacement, r.moduleKey.snapshot = root.moduleKey.snapshot
  deriving Repr, DecidableEq

/-- Location tokens retain exact source bytes or an explicitly broader subject. They are
not reconstructed from a pretty name; correspondence with compiler diagnostics is operational. -/
inductive PolicyLocation where
  | source (snapshot : SourceSnapshot) (range : ByteRange)
  | module (key : ModuleKey)
  | project (snapshot : AdmittedSnapshot)
  deriving Repr, DecidableEq

/-- Transported stable identity from the sole registry adapter. The pure core compares
these values; it does not define a second RuleId vocabulary or prove the adapter's mapping. -/
structure ExpectedDiagnostic where
  rule : String
  subreason : Option String
  primary : PolicyLocation
  related : Array PolicyLocation
  deriving Repr, DecidableEq

inductive FenceExpectation where
  | positive
  | compilerRejection (pattern : String) (nonempty : pattern ≠ "")
  | policyRejection (diagnostics : List ExpectedDiagnostic) (nonempty : diagnostics ≠ [])
  | trustedTeaching
  deriving Repr, DecidableEq

/-- Rule identity tokens in policy-negative expectations must be validated by the sole
registry adapter. The policy library deliberately defines no second RuleId enumeration. -/
structure FenceKey where
  document : SourceSnapshot
  opening : ByteRange
  body : ByteRange
  closing : ByteRange
  expectation : FenceExpectation
  nonemptyURI : document.uri ≠ ""
  ordered : opening.start ≤ opening.stop ∧ opening.stop ≤ body.start ∧
    body.start ≤ body.stop ∧ body.stop ≤ closing.start ∧ closing.start ≤ closing.stop
  validPositions : ∀ n ∈ [opening.start, opening.stop, body.start, body.stop, closing.start, closing.stop],
    (String.Pos.Raw.isValid document.source ⟨n⟩) = true
  deriving Repr, DecidableEq

inductive Scope where
  | project
  | file (source : SourceSnapshot) (profile : ConformingProfile) (execution : ExecutionClaim)
  | documentation (documents : Array SourceSnapshot)
  | editor (moduleName : Identity) (source : SourceSnapshot)
      (profile : ConformingProfile) (execution : ExecutionClaim)
  deriving Repr, DecidableEq

inductive Stage where
  | configuration | discovery | build | admission | declarationPolicy | execution
  | transcript | history | origin | documentationPresence | documentScan | example | graph
  deriving Repr, DecidableEq

/-- Per-surface assignments preserve distinct selected maxima. -/
structure SurfaceAssignment where
  target : String
  modules : Array Identity
  profile : ConformingProfile
  execution : ExecutionClaim
  deriving Repr, DecidableEq

structure ClaimCandidate where
  scope : Scope
  mode : EvidenceMode
  snapshot : Snapshot
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
   | .file source .. | .editor _ source .. => source ∈ c.snapshot.sources ∧ c.surfaces.isEmpty = true
   | .documentation documents =>
       documents.size > 0 ∧ documents.toList.Pairwise (fun a b => a.uri ≠ b.uri) ∧
       (∀ d ∈ documents, d ∈ c.snapshot.sources) ∧ c.surfaces.isEmpty = true)
instance instDecidableClaimValid (c : ClaimCandidate) : Decidable c.Valid := by
  unfold ClaimCandidate.Valid
  cases c.scope <;> infer_instance

/-- Positive claim data has only conforming profile assignments. Teaching and no-profile
inspection are separate request constructors in Decision, not inhabitants of this type. -/
abbrev Claim := { c : ClaimCandidate // c.Valid }

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

structure EnvironmentKey where
  snapshot : AdmittedSnapshot
  index : Nat
  deriving Repr, DecidableEq

/-- Coordinator-selected identity and complete positive module assignment. -/
structure EnvironmentRequest where
  key : EnvironmentKey
  modules : Array ModuleKey
  deriving Repr, DecidableEq

inductive LocalJobSubject where
  | scope | module (key : ModuleKey) | declaration (key : DeclarationKey)
  | root (key : RootKey) | boundary (key : BoundaryKey)
  deriving Repr, DecidableEq

inductive JobSubject where
  | scope | environment (key : EnvironmentKey) (subject : LocalJobSubject) | fence (key : FenceKey)
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
instance (claim : Claim) (subject : LocalJobSubject) : Decidable (LocalSubjectSnapshotOK claim subject) := by
  cases subject <;> unfold LocalSubjectSnapshotOK <;> infer_instance

def SubjectSnapshotOK (claim : Claim) : JobSubject → Prop
  | .scope => True
  | .environment key subject => key.snapshot.val = claim.val.snapshot ∧ LocalSubjectSnapshotOK claim subject
  | .fence k => k.document ∈ claim.val.snapshot.sources
instance (claim : Claim) (subject : JobSubject) : Decidable (SubjectSnapshotOK claim subject) := by
  cases subject <;> unfold SubjectSnapshotOK <;> infer_instance

/-- An attempt identifier is transport metadata, never part of a required job key. -/
structure JobKey where
  claim : Claim
  stage : Stage
  subject : JobSubject
  requiredStage : stage ∈ requiredStages claim
  compatibleSubject : stageSubjectCompatible stage subject = true
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
  rw [dite_eq_left key.requiredStage, dite_eq_left key.compatibleSubject, dite_eq_left key.subjectSnapshot]

end RegulaPolicy
