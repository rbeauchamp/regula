module

public import RegulaPolicy.Identity
public import RegulaPolicy.Collections

/-! Closed policy vocabulary and observation data. No operational Lean imports.
Canonical representation is informed by con-leche PropWhen; these are original domain
definitions, not imported con-leche proofs. Source observation authenticity remains
with the operational collector. -/

@[expose] public section

namespace RegulaPolicy
open scoped RegulaPolicy

/-- Supported DeclarationKind values; parsing cannot manufacture an unknown constructor. -/
inductive DeclarationKind where
  | «axiom»
  | «definition»
  | «theorem»
  | «opaque»
  | «constructor»
  | «inductive»
  | «recursor»
  | «quotient»
  deriving Repr, DecidableEq, Inhabited

def DeclarationKind.spelling : DeclarationKind → String
  | .«axiom» => "axiom"
  | .«definition» => "def"
  | .«theorem» => "theorem"
  | .«opaque» => "opaque"
  | .«constructor» => "ctor"
  | .«inductive» => "inductive"
  | .«recursor» => "recursor"
  | .«quotient» => "quot"

def DeclarationKind.parse? : String → Option DeclarationKind
  | "axiom" => some .«axiom»
  | "def" => some .«definition»
  | "theorem" => some .«theorem»
  | "opaque" => some .«opaque»
  | "ctor" => some .«constructor»
  | "inductive" => some .«inductive»
  | "recursor" => some .«recursor»
  | "quot" => some .«quotient»
  | _ => none

instance : ToString DeclarationKind := ⟨DeclarationKind.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem DeclarationKind.roundtrip (x : DeclarationKind) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem DeclarationKind.canonical (s : String) (x : DeclarationKind) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported BoundaryKind values; parsing cannot manufacture an unknown constructor. -/
inductive BoundaryKind where
  | «runtimeReplacement»
  | «compilerSimplification»
  | «nativeRuntime»
  | «external»
  | «unsafeComputation»
  | «partialComputation»
  | «opaqueComputation»
  | «compilerTrustedProof»
  deriving Repr, DecidableEq, Inhabited

def BoundaryKind.spelling : BoundaryKind → String
  | .«runtimeReplacement» => "runtime-replacement"
  | .«compilerSimplification» => "compiler-simplification"
  | .«nativeRuntime» => "native-runtime"
  | .«external» => "external"
  | .«unsafeComputation» => "unsafe-computation"
  | .«partialComputation» => "partial-computation"
  | .«opaqueComputation» => "opaque-computation"
  | .«compilerTrustedProof» => "compiler-trusted-proof"

def BoundaryKind.parse? : String → Option BoundaryKind
  | "runtime-replacement" => some .«runtimeReplacement»
  | "compiler-simplification" => some .«compilerSimplification»
  | "native-runtime" => some .«nativeRuntime»
  | "external" => some .«external»
  | "unsafe-computation" => some .«unsafeComputation»
  | "partial-computation" => some .«partialComputation»
  | "opaque-computation" => some .«opaqueComputation»
  | "compiler-trusted-proof" => some .«compilerTrustedProof»
  | _ => none

instance : ToString BoundaryKind := ⟨BoundaryKind.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem BoundaryKind.roundtrip (x : BoundaryKind) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem BoundaryKind.canonical (s : String) (x : BoundaryKind) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported Correspondence values; parsing cannot manufacture an unknown constructor. -/
inductive Correspondence where
  | «checked»
  | «trusted»
  | «unresolved»
  deriving Repr, DecidableEq, Inhabited

def Correspondence.spelling : Correspondence → String
  | .«checked» => "checked"
  | .«trusted» => "trusted"
  | .«unresolved» => "unresolved"

def Correspondence.parse? : String → Option Correspondence
  | "checked" => some .«checked»
  | "trusted" => some .«trusted»
  | "unresolved" => some .«unresolved»
  | _ => none

instance : ToString Correspondence := ⟨Correspondence.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem Correspondence.roundtrip (x : Correspondence) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem Correspondence.canonical (s : String) (x : Correspondence) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Outcome of the checker-initiated kernel-definitional comparison of a runtime replacement
with its reference. `completed (some detail)` is a completed positive comparison: the kernel
admitted the reflexivity proof within Standard-Logical foundations, recorded as `detail`.
`completed none` is a completed comparison without such evidence. `incomplete` means the
kernel stopped before deciding (resource exhaustion or interruption). -/
inductive DefeqComparison where
  | completed (admitted : Option String)
  | incomplete
  deriving Repr, DecidableEq

/-- Standard §8.6 classification, total over the comparison outcome: completed positive is
checked, completed negative leaves the replacement trusted, and a comparison that could not
complete is unresolved. -/
def DefeqComparison.classify : DefeqComparison → Correspondence × Option String
  | .completed (some detail) => (.checked, some s!"kernel-defeq; {detail}")
  | .completed none => (.trusted, some "no kernel-checked unconditional correspondence proof")
  | .incomplete => (.unresolved, some <| "no kernel-checked unconditional correspondence proof; " ++
      "kernel resources exhausted before deciding definitional correspondence")

/-- Only a completed negative comparison is trusted; no comparison that did not complete is. -/
theorem DefeqComparison.classify_trusted_iff (o : DefeqComparison) :
    o.classify.1 = .trusted ↔ o = .completed none := by
  rcases o with (_ | _) | _ <;> simp [classify]

/-- Only a completed comparison with admitted evidence is checked. -/
theorem DefeqComparison.classify_checked_iff (o : DefeqComparison) :
    o.classify.1 = .checked ↔ ∃ detail, o = .completed (some detail) := by
  rcases o with (_ | _) | _ <;> simp [classify]

/-- Exactly the comparisons that did not complete are unresolved. -/
theorem DefeqComparison.classify_unresolved_iff (o : DefeqComparison) :
    o.classify.1 = .unresolved ↔ o = .incomplete := by
  rcases o with (_ | _) | _ <;> simp [classify]

/-- Supported FoundationClass values; parsing cannot manufacture an unknown constructor. -/
inductive FoundationClass where
  | «kernelOnly»
  | «choiceFree»
  | «standardLogical»
  | «hole»
  | «unknownAxiom»
  | «compilerTrusting»
  deriving Repr, DecidableEq, Inhabited

def FoundationClass.spelling : FoundationClass → String
  | .«kernelOnly» => "kernel-only"
  | .«choiceFree» => "choice-free"
  | .«standardLogical» => "standard-logical"
  | .«hole» => "hole"
  | .«unknownAxiom» => "unknown-axiom"
  | .«compilerTrusting» => "compiler-trusting"

def FoundationClass.parse? : String → Option FoundationClass
  | "kernel-only" => some .«kernelOnly»
  | "choice-free" => some .«choiceFree»
  | "standard-logical" => some .«standardLogical»
  | "hole" => some .«hole»
  | "unknown-axiom" => some .«unknownAxiom»
  | "compiler-trusting" => some .«compilerTrusting»
  | _ => none

instance : ToString FoundationClass := ⟨FoundationClass.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem FoundationClass.roundtrip (x : FoundationClass) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem FoundationClass.canonical (s : String) (x : FoundationClass) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported ConformingProfile values; parsing cannot manufacture an unknown constructor. -/
inductive ConformingProfile where
  | «kernelOnly»
  | «choiceFree»
  | «standardLogical»
  deriving Repr, DecidableEq, Inhabited

def ConformingProfile.spelling : ConformingProfile → String
  | .«kernelOnly» => "kernel-only"
  | .«choiceFree» => "choice-free"
  | .«standardLogical» => "standard-logical"

def ConformingProfile.parse? : String → Option ConformingProfile
  | "kernel-only" => some .«kernelOnly»
  | "choice-free" => some .«choiceFree»
  | "standard-logical" => some .«standardLogical»
  | _ => none

instance : ToString ConformingProfile := ⟨ConformingProfile.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem ConformingProfile.roundtrip (x : ConformingProfile) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem ConformingProfile.canonical (s : String) (x : ConformingProfile) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported ExecutionClaim values; parsing cannot manufacture an unknown constructor. -/
inductive ExecutionClaim where
  | «report»
  | «checked»
  deriving Repr, DecidableEq, Inhabited

def ExecutionClaim.spelling : ExecutionClaim → String
  | .«report» => "report"
  | .«checked» => "checked"

def ExecutionClaim.parse? : String → Option ExecutionClaim
  | "report" => some .«report»
  | "checked" => some .«checked»
  | _ => none

instance : ToString ExecutionClaim := ⟨ExecutionClaim.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem ExecutionClaim.roundtrip (x : ExecutionClaim) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem ExecutionClaim.canonical (s : String) (x : ExecutionClaim) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported EvidenceMode values; parsing cannot manufacture an unknown constructor. -/
inductive EvidenceMode where
  | «editorSnapshot»
  | «incrementalProject»
  | «freshProject»
  | «freshFile»
  | «documentationExample»
  | «serializedGraph»
  deriving Repr, DecidableEq, Inhabited

def EvidenceMode.spelling : EvidenceMode → String
  | .«editorSnapshot» => "editorSnapshot"
  | .«incrementalProject» => "incrementalProject"
  | .«freshProject» => "freshProject"
  | .«freshFile» => "freshFile"
  | .«documentationExample» => "documentationExample"
  | .«serializedGraph» => "serializedGraph"

def EvidenceMode.parse? : String → Option EvidenceMode
  | "editorSnapshot" => some .«editorSnapshot»
  | "incrementalProject" => some .«incrementalProject»
  | "freshProject" => some .«freshProject»
  | "freshFile" => some .«freshFile»
  | "documentationExample" => some .«documentationExample»
  | "serializedGraph" => some .«serializedGraph»
  | _ => none

instance : ToString EvidenceMode := ⟨EvidenceMode.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem EvidenceMode.roundtrip (x : EvidenceMode) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem EvidenceMode.canonical (s : String) (x : EvidenceMode) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported Safety values; parsing cannot manufacture an unknown constructor. -/
inductive Safety where
  | «unsafe»
  | «partial»
  deriving Repr, DecidableEq, Inhabited

def Safety.spelling : Safety → String
  | .«unsafe» => "unsafe"
  | .«partial» => "partial"

def Safety.parse? : String → Option Safety
  | "unsafe" => some .«unsafe»
  | "partial" => some .«partial»
  | _ => none

instance : ToString Safety := ⟨Safety.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem Safety.roundtrip (x : Safety) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem Safety.canonical (s : String) (x : Safety) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported Reducibility values; parsing cannot manufacture an unknown constructor. -/
inductive Reducibility where
  | «opaque»
  | «abbrev»
  | «regular»
  deriving Repr, DecidableEq, Inhabited

def Reducibility.spelling : Reducibility → String
  | .«opaque» => "opaque"
  | .«abbrev» => "abbrev"
  | .«regular» => "regular"

def Reducibility.parse? : String → Option Reducibility
  | "opaque" => some .«opaque»
  | "abbrev" => some .«abbrev»
  | "regular" => some .«regular»
  | _ => none

instance : ToString Reducibility := ⟨Reducibility.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem Reducibility.roundtrip (x : Reducibility) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem Reducibility.canonical (s : String) (x : Reducibility) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported RecursionOrigin values; parsing cannot manufacture an unknown constructor. -/
inductive RecursionOrigin where
  | «structural»
  | «wellFounded»
  deriving Repr, DecidableEq, Inhabited

def RecursionOrigin.spelling : RecursionOrigin → String
  | .«structural» => "structural"
  | .«wellFounded» => "well-founded"

def RecursionOrigin.parse? : String → Option RecursionOrigin
  | "structural" => some .«structural»
  | "well-founded" => some .«wellFounded»
  | _ => none

instance : ToString RecursionOrigin := ⟨RecursionOrigin.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem RecursionOrigin.roundtrip (x : RecursionOrigin) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem RecursionOrigin.canonical (s : String) (x : RecursionOrigin) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Set-valued name observations have a single sorted, duplicate-free projection. -/
def canonicalNames (names : Array Lean.Name) : Array Lean.Name :=
  (CanonicalSet.normalize names.toList).toList.toArray

/-- Admission checks canonical order directly instead of rebuilding an ordered set. -/
instance (names : Array Lean.Name) : Decidable (canonicalNames names = names) := by
  letI := CanonicalSet.normalizedDecision names.toList
  exact decidable_of_iff ((CanonicalSet.normalize names.toList).toList = names.toList)
    (by simp only [canonicalNames, ← Array.toList_inj])

@[simp] theorem mem_canonicalNames (names : Array Lean.Name) (n : Lean.Name) :
    n ∈ canonicalNames names ↔ n ∈ names := by
  simp [canonicalNames, Std.ExtTreeSet.mem_toList]

theorem canonicalNames_idempotent (names : Array Lean.Name) :
    canonicalNames (canonicalNames names) = canonicalNames names := by
  simp [canonicalNames]

/-- Edge sets use the same structural ordering on each endpoint. -/
def canonicalEdges (edges : Array (Lean.Name × Lean.Name)) : Array (Lean.Name × Lean.Name) :=
  letI : Ord (Lean.Name × Lean.Name) := lexOrd
  (CanonicalSet.normalize edges.toList).toList.toArray

/-- Preserve exact edge normalization equality using the same lawful lexicographic order. -/
instance (edges : Array (Lean.Name × Lean.Name)) : Decidable (canonicalEdges edges = edges) := by
  letI : Ord (Lean.Name × Lean.Name) := lexOrd
  letI := CanonicalSet.normalizedDecision edges.toList
  exact decidable_of_iff ((CanonicalSet.normalize edges.toList).toList = edges.toList)
    (by simp only [canonicalEdges, ← Array.toList_inj])

@[simp] theorem mem_canonicalEdges (edges : Array (Lean.Name × Lean.Name)) (e : Lean.Name × Lean.Name) :
    e ∈ canonicalEdges edges ↔ e ∈ edges := by
  let : Ord (Lean.Name × Lean.Name) := lexOrd
  simp [canonicalEdges, Std.ExtTreeSet.mem_toList]

structure Position where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq

/-- Lean one-based lines and zero-based codepoint columns, with corresponding
zero-based UTF-16 columns (not absolute offsets). -/
structure Range where
  start : Position
  «end» : Position
  startUtf16 : Nat
  endUtf16 : Nat
  deriving Repr, DecidableEq

/-- Full and selection ranges recorded by Lean for a declaration. -/
structure Ranges where
  range : Range
  selectionRange : Range
  deriving Repr, DecidableEq

/-- The collector's observation of a registered proof-bearing executable contract.
The actual contract is checked during elaboration and admission; this record contains
its rendered requirement and any refusal, not a proof of the predicate. -/
structure ExecutableContract where
  root : Lean.Name
  requirement : String
  failure : Option String
  deriving Repr, DecidableEq

/-- Complete Lean-semantic report for one owned constant. -/
structure Declaration where
  name : Lean.Name
  /-- Structural original Name for new diagnostic transport; absent legacy records are unsupported. -/
  «module» : Lean.Name
  kind : DeclarationKind
  «type» : String
  prettyType : String
  isProp : Bool
  isUnsafe : Bool
  isPartial : Bool
  safety : Option Safety
  «instance» : Bool
  «noncomputable» : Bool
  implementedBy : Option Lean.Name
  «extern» : Bool
  internal : Bool
  «private» : Bool
  projection : Bool
  matcher : Bool
  recursive : Bool
  unsafeRecBase : Option Lean.Name
  levelParams : Array Lean.Name
  all : Array Lean.Name
  hints : Option Reducibility
  valueConstants : Array Lean.Name
  unsafeRecValueOrigin : Option RecursionOrigin
  unsafeRecValueExact : Option Bool
  unsafeRecValueDefeq : Option Bool
  unsafeRecEquationExact : Option Bool
  unsafeRecEquationDefeq : Option Bool
  unsafeRecEquationAxioms : Option (Array Lean.Name)
  nativeBoolShape : Bool
  nativeReplay : Option Bool
  nativeUseParents : Array Lean.Name
  ranges : Option Ranges
  axioms : Array Lean.Name
  executableContract : Option ExecutableContract := none
  deriving Repr, DecidableEq

/-- Origin observations are admitted only when the resolved and expected canonical
paths agree for an Init module. The filesystem meaning of those paths remains IO evidence. -/
structure NativeOrigin where
  moduleName : Lean.Name
  actual : String
  expected : String
  initModule : moduleName.getRoot = `Init
  nonempty : actual ≠ ""
  agrees : actual = expected
  deriving Repr, DecidableEq

def admitNativeOrigin (moduleName : Lean.Name) (actual expected : String) :
    Except String NativeOrigin :=
  if hm : moduleName.getRoot = `Init then
    if hn : actual ≠ "" then
      if he : actual = expected then .ok ⟨moduleName, actual, expected, hm, hn, he⟩
      else .error "native-runtime origin mismatch"
    else .error "empty native-runtime origin"
  else .error "native-runtime module is not Init"

/-- Checked replacement equality and an admitted opaque body have different meanings. -/
inductive CheckedEvidence : BoundaryKind → Type where
  | replacement (detail : String) : CheckedEvidence .runtimeReplacement
  | simplification (detail : String) : CheckedEvidence .compilerSimplification
  | opaqueBody : CheckedEvidence .opaqueComputation
  deriving Repr, DecidableEq

/-- Only the native-runtime kind needs this specific trusted origin observation. -/
def TrustedEvidence : BoundaryKind → Type
  | .nativeRuntime => NativeOrigin
  | _ => Unit

instance (k : BoundaryKind) : Repr (TrustedEvidence k) := by cases k <;> dsimp [TrustedEvidence] <;> infer_instance
instance (k : BoundaryKind) : DecidableEq (TrustedEvidence k) := by cases k <;> dsimp [TrustedEvidence] <;> infer_instance

/-- Invalid combinations such as checked external code are unrepresentable. -/
inductive BoundaryEvidence (kind : BoundaryKind) where
  | checked (evidence : CheckedEvidence kind)
  | trusted (detail : Option String) (origin : TrustedEvidence kind)
  | unresolved (detail : Option String)
  deriving Repr, DecidableEq

def BoundaryEvidence.correspondence {k : BoundaryKind} : BoundaryEvidence k → Correspondence
  | .checked _ => .checked | .trusted .. => .trusted | .unresolved _ => .unresolved

def BoundaryEvidence.detail {k : BoundaryKind} : BoundaryEvidence k → Option String
  | .checked evidence => match evidence with
    | .replacement s | .simplification s => some s
    | .opaqueBody => some "kernel-checked-body"
  | .trusted s _ | .unresolved s => s

def BoundaryEvidence.nativeOrigin? {k : BoundaryKind} (e : BoundaryEvidence k) : Option NativeOrigin :=
  match k, e with
  | .nativeRuntime, .trusted _ origin => some origin
  | _, _ => none

/-- Raw candidate construction may discard incompatible observation fields.
Operational/wire callers requiring field preservation must use `admitBoundaryEvidence`.
A candidate is an indexed value, not a receipt for the supplied raw fields. -/
def boundaryEvidenceCandidate (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option NativeOrigin) : Except String (BoundaryEvidence kind) :=
  match state with
  | .unresolved => .ok (.unresolved detail)
  | .trusted => match kind with
    | .nativeRuntime => match origin with
      | some o => .ok (.trusted detail o)
      | none => .error "missing native-runtime origin"
    | .runtimeReplacement | .compilerSimplification | .external | .unsafeComputation
    | .partialComputation | .opaqueComputation | .compilerTrustedProof => .ok (.trusted detail ())
  | .checked => match kind, detail with
    | .runtimeReplacement, some s => .ok (.checked (.replacement s))
    | .compilerSimplification, some s => .ok (.checked (.simplification s))
    | .opaqueComputation, some "kernel-checked-body" => .ok (.checked .opaqueBody)
    | _, _ => .error "invalid checked boundary evidence"

/-- Admission retains every supplied evidence field or refuses the observation. -/
def admitBoundaryEvidence (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option NativeOrigin) : Except String (BoundaryEvidence kind) :=
  match boundaryEvidenceCandidate kind state detail origin with
  | .error error => .error error
  | .ok e =>
    if e.correspondence = state ∧ e.detail = detail ∧ e.nativeOrigin? = origin then .ok e
    else .error "boundary evidence contains incompatible fields"

private theorem boundaryEvidenceCandidate_roundtrip {kind : BoundaryKind} (e : BoundaryEvidence kind) :
    boundaryEvidenceCandidate kind e.correspondence e.detail e.nativeOrigin? = .ok e := by
  cases e with
  | checked evidence => cases evidence <;> rfl
  | trusted detail origin => cases kind <;> rfl
  | unresolved detail => cases kind <;> rfl

/-- Successful admission preserves every evidence projection for all raw inputs. -/
theorem boundaryEvidence_admission_preserves (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option NativeOrigin) (e : BoundaryEvidence kind)
    (h : admitBoundaryEvidence kind state detail origin = .ok e) :
    e.correspondence = state ∧ e.detail = detail ∧ e.nativeOrigin? = origin := by
  unfold admitBoundaryEvidence at h
  split at h
  next => cases h
  next candidate _ =>
    split at h
    next valid => cases h; exact valid
    next => cases h

/-- Every inhabitant of the indexed evidence domain survives its actual admission API. -/
theorem boundaryEvidence_roundtrip {kind : BoundaryKind} (e : BoundaryEvidence kind) :
    admitBoundaryEvidence kind e.correspondence e.detail e.nativeOrigin? = .ok e := by
  unfold admitBoundaryEvidence
  rw [boundaryEvidenceCandidate_roundtrip]
  simp

/-- Canonical native-origin admission preserves its module and exact path observation. -/
theorem nativeOrigin_roundtrip (o : NativeOrigin) :
    admitNativeOrigin o.moduleName o.actual o.expected = .ok o := by
  cases o with
  | mk m a e hm hn he =>
    cases he
    simp [admitNativeOrigin, hm, hn]

/-- One boundary in the conservative compiler/source closure of an
executable root. `boundary` is one of `runtime-replacement`, `compiler-simplification`, `native-runtime`,
`external`, `unsafe-computation`, `partial-computation`, `opaque-computation`,
or `compiler-trusted-proof`; `correspondence` is `checked`, `trusted`, or
`unresolved`. -/
structure ExecutionBoundary where
  occurrence : Nat
  name : Lean.Name
  «module» : Lean.Name
  boundary : BoundaryKind
  account : BoundaryEvidence boundary
  owned : Bool
  replacement : Option Lean.Name
  compilerCallers : Array Lean.Name := #[]
  deriving Repr, DecidableEq

/-- Execution coverage for one owned executable root: every boundary its
conservative compiler/source closure reaches, plus every dependency path the
analysis could not resolve. -/
def ExecutionBoundary.correspondence (b : ExecutionBoundary) : Correspondence := b.account.correspondence

def ExecutionBoundary.evidence (b : ExecutionBoundary) : Option String := b.account.detail

/-- One first visit, recorded before inspecting its policy outcomes. A non-root visit
retains the earlier visit that queued it; IR-only names may lack module attribution. -/
structure ExecutionVisit where
  name : Lean.Name
  moduleName : Option Lean.Name
  parent : Option Nat
  deriving Repr, DecidableEq

/-- The walk's complete reached-name census and separately attributed edge sets.
These are observations of the pinned collector, not a minimal runtime call graph.
Current replacements remain distinct from successfully observed historical choices;
active simplifications are used for cycle detection, not claimed compiler calls. -/
structure ExecutionClosure where
  nodes : Array Lean.Name
  visits : Array ExecutionVisit
  logicalEdges : Array (Lean.Name × Lean.Name) := #[]
  candidateEdges : Array (Lean.Name × Lean.Name) := #[]
  historyEdges : Array (Lean.Name × Lean.Name) := #[]
  currentReplacementEdges : Array (Lean.Name × Lean.Name) := #[]
  activeSimplificationEdges : Array (Lean.Name × Lean.Name) := #[]
  helperEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- Names for which retained code is required, including the root when applicable. -/
  requiredCode : Array Lean.Name := #[]
  /-- Required names whose body is absent or an unauthenticated extern placeholder. -/
  unavailableCode : Array Lean.Name := #[]
  deriving Repr, DecidableEq

/-- Traversal edges, retaining the distinct acquisition channels in the stored fields. -/
def ExecutionClosure.edges (c : ExecutionClosure) (compilerEdges : Array (Lean.Name × Lean.Name)) :
    Array (Lean.Name × Lean.Name) :=
  compilerEdges ++ c.logicalEdges ++ c.candidateEdges ++ c.historyEdges ++
    c.currentReplacementEdges ++ c.helperEdges

structure ExecutionRoot where
  name : Lean.Name
  «module» : Lean.Name
  boundaries : Array ExecutionBoundary
  unresolved : Array String
  /-- Direct calls/closures/initializers retained in the pinned compiler IR;
  unlike the boundary candidate closure, these record compiled edges. -/
  compilerEdges : Array (Lean.Name × Lean.Name) := #[]
  closure : ExecutionClosure
  deriving Repr, DecidableEq

/-- Lean-resolved origin of one imported module, with its direct imports as
recorded in the loaded module header. -/
structure ModuleOrigin where
  name : Lean.Name
  olean : String
  imports : Array Lean.Name
  deriving Repr, DecidableEq

/-- Complete report for one exact requested module set. -/
structure Environment where
  toolchain : String
  modules : Array Lean.Name
  moduleOrigins : Array ModuleOrigin
  declarations : Array Declaration
  execution : Array ExecutionRoot
  deriving Repr, DecidableEq


/-- The three information-node roles emitted by Lean's frontend observer. -/
inductive EvaluatorRole where
  | command | tactic | term
  deriving Repr, DecidableEq

def EvaluatorRole.spelling : EvaluatorRole → String
  | .command => "command" | .tactic => "tactic" | .term => "term"
def EvaluatorRole.parse? : String → Option EvaluatorRole
  | "command" => some .command | "tactic" => some .tactic | "term" => some .term | _ => none
instance : ToString EvaluatorRole := ⟨EvaluatorRole.spelling⟩
@[simp] theorem EvaluatorRole.roundtrip (x : EvaluatorRole) : parse? x.spelling = some x := by
  cases x <;> rfl
theorem EvaluatorRole.canonical (s : String) (x : EvaluatorRole) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

namespace Frontend
structure ImportRecord where
  «module» : Lean.Name
  importAll : Bool
  isExported : Bool
  isMeta : Bool
  deriving Repr, DecidableEq

structure SyntaxRange where
  start : Position
  «end» : Position
  deriving Repr, DecidableEq

structure Evaluator where
  role : EvaluatorRole
  elaborator : Lean.Name
  kind : Lean.Name
  range : Option SyntaxRange
  pinned : Bool
  deriving Repr, DecidableEq

structure AddedDeclaration where
  name : Lean.Name
  kind : DeclarationKind
  «type» : String
  deriving Repr, DecidableEq

structure DeclarationBinding where
  name : Lean.Name
  range : Option SyntaxRange
  deriving Repr, DecidableEq

structure Command where
  commandElaborator : Lean.Name
  commandKind : Lean.Name
  commandRange : Option SyntaxRange
  added : Array Lean.Name
  addedDeclarations : Array AddedDeclaration
  evaluators : Array Evaluator
  bindings : Array DeclarationBinding := #[]
  deriving Repr, DecidableEq

structure Transcript where
  «module» : Lean.Name
  source : String
  sourceBytes : Nat
  sourceContent : String
  leanVersion : String
  leanGitHash : String
  imports : Array ImportRecord
  commands : Array Command
  runtimeReplacements : Array (Lean.Name × Lean.Name) := #[]
  replacementHistoryUnsupported : Array String := #[]
  deriving Repr, DecidableEq

end Frontend

end RegulaPolicy
