module

public import RegulaPolicy.Identity
public import RegulaPolicy.Collections

/-! # Policy vocabulary and observation data

Closed policy vocabulary and observation data. No operational Lean imports.
Canonical representation is informed by con-leche PropWhen; these are original domain
definitions, not imported con-leche proofs. Source observation authenticity remains
with the operational collector. -/

@[expose] public section

namespace RegulaPolicy
open scoped RegulaPolicy

/-- Supported DeclarationKind values; parsing cannot manufacture an unknown constructor. -/
inductive DeclarationKind where
  /-- An axiom: `ConstantInfo.axiomInfo`. -/
  | «axiom»
  /-- A definition: `ConstantInfo.defnInfo`. -/
  | «definition»
  /-- A theorem: `ConstantInfo.thmInfo`. -/
  | «theorem»
  /-- An opaque constant: `ConstantInfo.opaqueInfo`. -/
  | «opaque»
  /-- An inductive type's constructor: `ConstantInfo.ctorInfo`. -/
  | «constructor»
  /-- An inductive type: `ConstantInfo.inductInfo`. -/
  | «inductive»
  /-- An inductive type's recursor: `ConstantInfo.recInfo`. -/
  | «recursor»
  /-- One of Lean's built-in quotient constants: `ConstantInfo.quotInfo`. -/
  | «quotient»
  deriving Repr, DecidableEq, Inhabited

/-- The kind's text in reports (`axiom`, `def`, `theorem`, `opaque`, `ctor`, `inductive`,
`recursor` or `quot`); `parse?` reads it back (`DeclarationKind.roundtrip`). -/
def DeclarationKind.spelling : DeclarationKind → String
  | .«axiom» => "axiom"
  | .«definition» => "def"
  | .«theorem» => "theorem"
  | .«opaque» => "opaque"
  | .«constructor» => "ctor"
  | .«inductive» => "inductive"
  | .«recursor» => "recursor"
  | .«quotient» => "quot"

/-- The kind a report text names; `none` for any text that is not a `spelling`
(`DeclarationKind.canonical`). -/
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
  /-- The compiler runs another constant in place of this one (`@[implemented_by]`). -/
  | «runtimeReplacement»
  /-- A `@[csimp]`-shaped constant-equality lemma may let the compiler replace this constant
  with another. -/
  | «compilerSimplification»
  /-- An `@[extern]` constant of a Lean `Init` module whose origin was admitted, implemented by
  the Lean runtime. -/
  | «nativeRuntime»
  /-- Any other `@[extern]` constant, implemented outside Lean. -/
  | «external»
  /-- An `unsafe` constant. -/
  | «unsafeComputation»
  /-- A `partial` constant, or an opaque constant compiled through a partial `_unsafe_rec`
  helper. -/
  | «partialComputation»
  /-- Any other opaque constant; its body is checked only when no compiled helper replaces it. -/
  | «opaqueComputation»
  /-- An axiom that trusts the compiler, reached by execution: `Lean.trustCompiler`,
  `Lean.ofReduceBool`, `Lean.ofReduceNat` or a name the `nativeEqTrue` scheme generates for
  `native_decide`, `decide +native` or `bv_decide` (`compilerTrustingAxiomName`). -/
  | «compilerTrustedProof»
  deriving Repr, DecidableEq, Inhabited

/-- The kind's kebab-case text in reports and diagnostics, such as `runtime-replacement`;
`parse?` reads it back (`BoundaryKind.roundtrip`). -/
def BoundaryKind.spelling : BoundaryKind → String
  | .«runtimeReplacement» => "runtime-replacement"
  | .«compilerSimplification» => "compiler-simplification"
  | .«nativeRuntime» => "native-runtime"
  | .«external» => "external"
  | .«unsafeComputation» => "unsafe-computation"
  | .«partialComputation» => "partial-computation"
  | .«opaqueComputation» => "opaque-computation"
  | .«compilerTrustedProof» => "compiler-trusted-proof"

/-- The kind a report text names; `none` for any text that is not a `spelling`
(`BoundaryKind.canonical`). -/
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
  /-- Kernel-checked evidence relates the executed code to the logical definition. -/
  | «checked»
  /-- The boundary is resolved but its execution is trusted, without checked evidence. -/
  | «trusted»
  /-- The analysis could not resolve the boundary; this never passes. -/
  | «unresolved»
  deriving Repr, DecidableEq, Inhabited

/-- The account's text in reports (`checked`, `trusted` or `unresolved`); `parse?` reads it
back (`Correspondence.roundtrip`). -/
def Correspondence.spelling : Correspondence → String
  | .«checked» => "checked"
  | .«trusted» => "trusted"
  | .«unresolved» => "unresolved"

/-- The account a report text names; `none` for any text that is not a `spelling`
(`Correspondence.canonical`). -/
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
  /-- The kernel decided; `admitted` is the evidence detail when it admitted the proof. -/
  | completed (admitted : Option String)
  /-- The kernel stopped before deciding. -/
  | incomplete
  deriving Repr, DecidableEq

/-- Standard §7.6 classification, total over the comparison outcome: completed positive is
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
  /-- The declaration depends on no axiom. -/
  | «kernelOnly»
  /-- Its axioms are some of `propext` and `Quot.sound`, and there is at least one. -/
  | «choiceFree»
  /-- Its axioms are within `propext`, `Quot.sound` and `Classical.choice`, and include
  `Classical.choice`. -/
  | «standardLogical»
  /-- It depends on `sorryAx`. -/
  | «hole»
  /-- It depends on an axiom outside the Standard-Logical foundation and the compiler axioms. -/
  | «unknownAxiom»
  /-- It depends on a compiler axiom, and otherwise only on Standard-Logical axioms. -/
  | «compilerTrusting»
  deriving Repr, DecidableEq, Inhabited

/-- The class's kebab-case text in reports, such as `kernel-only`; `parse?` reads it back
(`FoundationClass.roundtrip`). -/
def FoundationClass.spelling : FoundationClass → String
  | .«kernelOnly» => "kernel-only"
  | .«choiceFree» => "choice-free"
  | .«standardLogical» => "standard-logical"
  | .«hole» => "hole"
  | .«unknownAxiom» => "unknown-axiom"
  | .«compilerTrusting» => "compiler-trusting"

/-- The class a report text names; `none` for any text that is not a `spelling`
(`FoundationClass.canonical`). -/
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
  /-- No axiom is permitted. -/
  | «kernelOnly»
  /-- `propext` and `Quot.sound` are permitted. -/
  | «choiceFree»
  /-- `propext`, `Quot.sound` and `Classical.choice` are permitted. -/
  | «standardLogical»
  deriving Repr, DecidableEq, Inhabited

/-- The profile's text in manifests and reports (`kernel-only`, `choice-free` or
`standard-logical`); `parse?` reads it back (`ConformingProfile.roundtrip`). -/
def ConformingProfile.spelling : ConformingProfile → String
  | .«kernelOnly» => "kernel-only"
  | .«choiceFree» => "choice-free"
  | .«standardLogical» => "standard-logical"

/-- The profile a text names; `none` for any text that is not a `spelling`
(`ConformingProfile.canonical`). -/
def ConformingProfile.parse? : String → Option ConformingProfile
  | "kernel-only" => some .«kernelOnly»
  | "choice-free" => some .«choiceFree»
  | "standard-logical" => some .«standardLogical»
  | _ => none

instance : ToString ConformingProfile := ⟨ConformingProfile.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem ConformingProfile.roundtrip (x : ConformingProfile) : parse? x.spelling =
    some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem ConformingProfile.canonical (s : String) (x : ConformingProfile) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- Supported ExecutionClaim values; parsing cannot manufacture an unknown constructor. -/
inductive ExecutionClaim where
  /-- Resolved execution boundaries pass whether checked or trusted; they are reported. -/
  | «report»
  /-- A resolved boundary passes only with checked evidence or as an admitted native-runtime
  boundary (`BoundaryOK`). -/
  | «checked»
  deriving Repr, DecidableEq, Inhabited

/-- The claim's text in manifests and reports (`report` or `checked`); `parse?` reads it back
(`ExecutionClaim.roundtrip`). -/
def ExecutionClaim.spelling : ExecutionClaim → String
  | .«report» => "report"
  | .«checked» => "checked"

/-- The claim a text names; `none` for any text that is not a `spelling`
(`ExecutionClaim.canonical`). -/
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
  /-- The editor linter's view of the current file: partial, not project acceptance. -/
  | «editorSnapshot»
  /-- A project audit over existing build state, not a fresh-source audit. -/
  | «incrementalProject»
  /-- A whole-project audit of the claimed Lake surfaces from fresh source. -/
  | «freshProject»
  /-- A fresh audit of one source file, not project acceptance. -/
  | «freshFile»
  /-- An audit of documentation code examples. -/
  | «documentationExample»
  /-- A recheck of the serialized declaration graph. -/
  | «serializedGraph»
  deriving Repr, DecidableEq, Inhabited

/-- The mode's camel-case text in the registry and results, such as `freshProject`; `parse?`
reads it back (`EvidenceMode.roundtrip`). -/
def EvidenceMode.spelling : EvidenceMode → String
  | .«editorSnapshot» => "editorSnapshot"
  | .«incrementalProject» => "incrementalProject"
  | .«freshProject» => "freshProject"
  | .«freshFile» => "freshFile"
  | .«documentationExample» => "documentationExample"
  | .«serializedGraph» => "serializedGraph"

/-- The mode a text names; `none` for any text that is not a `spelling`
(`EvidenceMode.canonical`). -/
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
  /-- The constant is `unsafe` (and not `partial`). -/
  | «unsafe»
  /-- The constant is `partial`. -/
  | «partial»
  deriving Repr, DecidableEq, Inhabited

/-- The Lean keyword, `unsafe` or `partial`; `parse?` reads it back (`Safety.roundtrip`). -/
def Safety.spelling : Safety → String
  | .«unsafe» => "unsafe"
  | .«partial» => "partial"

/-- The safety a text names; `none` for any text that is not a `spelling`
(`Safety.canonical`). -/
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
  /-- The definition's kernel hint is `ReducibilityHints.opaque`. -/
  | «opaque»
  /-- The definition's kernel hint is `ReducibilityHints.abbrev`. -/
  | «abbrev»
  /-- The definition's kernel hint is `ReducibilityHints.regular`; its height is not kept. -/
  | «regular»
  deriving Repr, DecidableEq, Inhabited

/-- The hint's text in reports (`opaque`, `abbrev` or `regular`); `parse?` reads it back
(`Reducibility.roundtrip`). -/
def Reducibility.spelling : Reducibility → String
  | .«opaque» => "opaque"
  | .«abbrev» => "abbrev"
  | .«regular» => "regular"

/-- The hint a text names; `none` for any text that is not a `spelling`
(`Reducibility.canonical`). -/
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
  /-- Lean's structural-recursion equation information holds the base's predefinition. -/
  | «structural»
  /-- Lean's well-founded-recursion equation information holds the base's predefinition. -/
  | «wellFounded»
  deriving Repr, DecidableEq, Inhabited

/-- The origin's text in reports (`structural` or `well-founded`); `parse?` reads it back
(`RecursionOrigin.roundtrip`). -/
def RecursionOrigin.spelling : RecursionOrigin → String
  | .«structural» => "structural"
  | .«wellFounded» => "well-founded"

/-- The origin a text names; `none` for any text that is not a `spelling`
(`RecursionOrigin.canonical`). -/
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

@[simp] theorem mem_canonicalEdges (edges : Array (Lean.Name × Lean.Name))
    (e : Lean.Name × Lean.Name) :
    e ∈ canonicalEdges edges ↔ e ∈ edges := by
  let : Ord (Lean.Name × Lean.Name) := lexOrd
  simp [canonicalEdges, Std.ExtTreeSet.mem_toList]

/-- A source position as `Lean.Position` records it. -/
structure Position where
  /-- The one-based line. -/
  line : Nat
  /-- The zero-based column, in codepoints. -/
  column : Nat
  deriving Repr, DecidableEq

/-- Lean one-based lines and zero-based codepoint columns, with corresponding
zero-based UTF-16 columns (not absolute offsets). -/
structure Range where
  /-- Where the range begins. -/
  start : Position
  /-- Where the range ends. -/
  «end» : Position
  /-- The zero-based UTF-16 column of `start`. -/
  startUtf16 : Nat
  /-- The zero-based UTF-16 column of `end`. -/
  endUtf16 : Nat
  deriving Repr, DecidableEq

/-- Full and selection ranges recorded by Lean for a declaration. -/
structure Ranges where
  /-- The range of the whole declaration. -/
  range : Range
  /-- The range of its name, which an editor selects. -/
  selectionRange : Range
  deriving Repr, DecidableEq

/-- The collector's observation of a registered proof-bearing executable contract.
The actual contract is checked during elaboration and admission; this record contains
its rendered requirement and any refusal, not a proof of the predicate. -/
structure ExecutableContract where
  /-- The promised implementation constant; anonymous when the implementation is not a
  constant. -/
  root : Lean.Name
  /-- The requirement applied to the implementation, pretty-printed. -/
  requirement : String
  /-- Why the registration is refused, such as a noncomputable, `unsafe` or `partial`
  implementation; `none` when the collector found no problem. -/
  failure : Option String
  deriving Repr, DecidableEq

/-- Complete Lean-semantic report for one owned constant. -/
structure Declaration where
  /-- The constant's name. -/
  name : Lean.Name
  /-- Structural original Name for new diagnostic transport; absent legacy records are
  unsupported. -/
  «module» : Lean.Name
  /-- The kind of its `ConstantInfo`. -/
  kind : DeclarationKind
  /-- The `repr` of its kernel type expression. -/
  «type» : String
  /-- Its type as Lean's pretty-printer shows it. -/
  prettyType : String
  /-- Its type is a proposition. -/
  isProp : Bool
  /-- The constant is `unsafe`. -/
  isUnsafe : Bool
  /-- The constant is `partial`. -/
  isPartial : Bool
  /-- `partial` if the constant is partial, else `unsafe` if it is unsafe, else `none`. -/
  safety : Option Safety
  /-- The constant is registered as a type-class instance. -/
  «instance» : Bool
  /-- Lean marks the constant `noncomputable`. -/
  «noncomputable» : Bool
  /-- The constant the compiler runs in its place, from `@[implemented_by]`. -/
  implementedBy : Option Lean.Name
  /-- The constant has an `@[extern]` implementation. -/
  «extern» : Bool
  /-- The name is internal: some component begins with `_`. -/
  internal : Bool
  /-- The name is a private name. -/
  «private» : Bool
  /-- The constant is a structure projection function. -/
  projection : Bool
  /-- The constant is a `match` auxiliary function (a matcher). -/
  matcher : Bool
  /-- Lean reports the definition as recursive (`Meta.isRecursiveDefinition`). -/
  recursive : Bool
  /-- For an `_unsafe_rec` helper, the name of the definition it implements. -/
  unsafeRecBase : Option Lean.Name
  /-- The constant's universe parameters. -/
  levelParams : Array Lean.Name
  /-- The mutual block of a definition, theorem or opaque constant; empty for other kinds. -/
  all : Array Lean.Name
  /-- A definition's kernel reducibility hint; `none` for other kinds. -/
  hints : Option Reducibility
  /-- The constants its value mentions, sorted and without duplicates; empty without a value. -/
  valueConstants : Array Lean.Name
  /-- For an `_unsafe_rec` helper inspected as a replay candidate: which recursion information
  holds its base's predefinition. -/
  unsafeRecValueOrigin : Option RecursionOrigin
  /-- For such a helper: its value is syntactically the compiler transformation reconstructed
  from that predefinition. -/
  unsafeRecValueExact : Option Bool
  /-- For such a helper: its value equals that reconstruction once every proof subterm of each,
  in a binder type too, is replaced by one fixed proof, the computational content Lean's compiler
  compiles after erasing proofs. It holds when `unsafeRecValueExact` does, and also where Lean
  abstracted a nested proof of the stored predefinition into an auxiliary theorem that the helper
  keeps inline. `false` also records a comparison that could not complete. -/
  unsafeRecValueUpToProofs : Option Bool
  /-- For such a helper: the base's unfolding equation has exactly the expected statement. -/
  unsafeRecEquationExact : Option Bool
  /-- For such a helper: the base's unfolding equation is definitionally equal to the expected
  statement, established by syntactic equality in the same way, so it equals
  `unsafeRecEquationExact`. -/
  unsafeRecEquationDefeq : Option Bool
  /-- For such a helper: the axioms of the base's unfolding equation, sorted and without
  duplicates. -/
  unsafeRecEquationAxioms : Option (Array Lean.Name)
  /-- For an axiom whose name the `nativeEqTrue` scheme generates for a native tactic
  (`nativeAxiomOrigin?`) and whose type is `e = true` with `e` in that tactic's asserted shape
  (`decide p` for `native_decide` and `decide +native`, `verifyBVExpr expr cert` over the run's
  own auxiliary definitions for `bv_decide`): the `repr` of `e`, naming each of those auxiliary
  definitions by its unindexed base. Otherwise `none`. -/
  nativeStatement : Option String
  /-- For a replay candidate with a statement: whether an independent native evaluation of
  `e` returned `true` (`false` also when the replay failed). -/
  nativeReplay : Option Bool
  /-- Lean's declaration ranges, when it recorded them. -/
  ranges : Option Ranges
  /-- The axioms the constant transitively depends on (`collectAxioms`), sorted and without
  duplicates. -/
  axioms : Array Lean.Name
  /-- The collector's observation when the constant registers an executable contract. -/
  executableContract : Option ExecutableContract := none
  deriving Repr, DecidableEq

/-- Origin observations are admitted only when the resolved and expected canonical
paths agree for an Init module. The filesystem meaning of those paths remains IO evidence. -/
structure NativeOrigin where
  /-- The module that declares the native-runtime constant. -/
  moduleName : Lean.Name
  /-- The canonical path of the `.olean` file the module was loaded from. -/
  actual : String
  /-- The canonical path of that module's `.olean` in the toolchain's library directory. -/
  expected : String
  /-- The module is under `Init`. -/
  initModule : moduleName.getRoot = `Init
  /-- The resolved path is not empty. -/
  nonempty : actual ≠ ""
  /-- The resolved and expected paths are the same text. -/
  agrees : actual = expected
  deriving Repr, DecidableEq

/-- Admit an origin observation: an error unless the module is under `Init` and `actual` is
nonempty and equal to `expected` (`nativeOrigin_roundtrip`). -/
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
  /-- A runtime replacement with checked correspondence, described by `detail`. -/
  | replacement (detail : String) : CheckedEvidence .runtimeReplacement
  /-- A compiler simplification with checked correspondence, described by `detail`. -/
  | simplification (detail : String) : CheckedEvidence .compilerSimplification
  /-- An opaque constant executed through its kernel-checked body. -/
  | opaqueBody : CheckedEvidence .opaqueComputation
  deriving Repr, DecidableEq

/-- Only the native-runtime kind needs this specific trusted origin observation. -/
def TrustedEvidence : BoundaryKind → Type
  | .nativeRuntime => NativeOrigin
  | _ => Unit

instance (k : BoundaryKind) : Repr (TrustedEvidence k) := by cases k <;> dsimp
    [TrustedEvidence] <;> infer_instance
instance (k : BoundaryKind) : DecidableEq (TrustedEvidence k) := by cases k <;> dsimp
    [TrustedEvidence] <;> infer_instance

/-- Invalid combinations such as checked external code are unrepresentable. -/
inductive BoundaryEvidence (kind : BoundaryKind) where
  /-- Checked evidence of a kind that admits it. -/
  | checked (evidence : CheckedEvidence kind)
  /-- A trusted boundary, with an optional detail and, for native runtime, its origin. -/
  | trusted (detail : Option String) (origin : TrustedEvidence kind)
  /-- An unresolved boundary, with an optional detail. -/
  | unresolved (detail : Option String)
  deriving Repr, DecidableEq

/-- The correspondence account the evidence gives. -/
def BoundaryEvidence.correspondence {k : BoundaryKind} : BoundaryEvidence k → Correspondence
  | .checked _ => .checked | .trusted .. => .trusted | .unresolved _ => .unresolved

/-- The evidence's detail text; `kernel-checked-body` for a checked opaque body. -/
def BoundaryEvidence.detail {k : BoundaryKind} : BoundaryEvidence k → Option String
  | .checked evidence => match evidence with
    | .replacement s | .simplification s => some s
    | .opaqueBody => some "kernel-checked-body"
  | .trusted s _ | .unresolved s => s

/-- The admitted origin of a trusted native-runtime boundary; `none` for any other evidence. -/
def BoundaryEvidence.nativeOrigin? {k : BoundaryKind} (e : BoundaryEvidence k) :
    Option NativeOrigin :=
  match k, e with
  | .nativeRuntime, .trusted _ origin => some origin
  | _, _ => none

/-- Raw candidate construction may discard incompatible observation fields.
Operational/wire callers requiring field preservation must use `admitBoundaryEvidence`.
A candidate is an indexed value, not a receipt for the supplied raw fields. -/
def boundaryEvidenceCandidate (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option NativeOrigin) : Except String
    (BoundaryEvidence kind) :=
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
    (detail : Option String) (origin : Option NativeOrigin) : Except String
    (BoundaryEvidence kind) :=
  match boundaryEvidenceCandidate kind state detail origin with
  | .error error => .error error
  | .ok e =>
    if e.correspondence = state ∧ e.detail = detail ∧ e.nativeOrigin? = origin then .ok e
    else .error "boundary evidence contains incompatible fields"

private theorem boundaryEvidenceCandidate_roundtrip {kind : BoundaryKind}
    (e : BoundaryEvidence kind) :
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
executable root. `boundary` is one of `runtime-replacement`, `compiler-simplification`,
`native-runtime`,
`external`, `unsafe-computation`, `partial-computation`, `opaque-computation`,
or `compiler-trusted-proof`; `correspondence` is `checked`, `trusted`, or
`unresolved`. -/
structure ExecutionBoundary where
  /-- The boundary's position in its root's boundary list. -/
  occurrence : Nat
  /-- The constant at the boundary. -/
  name : Lean.Name
  /-- The module that declares it. -/
  «module» : Lean.Name
  /-- What kind of boundary it is. -/
  boundary : BoundaryKind
  /-- The correspondence evidence, of a form the kind admits. -/
  account : BoundaryEvidence boundary
  /-- The constant's module is one of the audited, owned modules. -/
  owned : Bool
  /-- For a runtime replacement or compiler simplification, the constant run in its place. -/
  replacement : Option Lean.Name
  /-- The constants whose retained compiler IR calls this one directly. -/
  compilerCallers : Array Lean.Name := #[]
  deriving Repr, DecidableEq

/-- Execution coverage for one owned executable root: every boundary its
conservative compiler/source closure reaches, plus every dependency path the
analysis could not resolve. -/
def ExecutionBoundary.correspondence (b : ExecutionBoundary) : Correspondence :=
    b.account.correspondence

/-- The detail text of the boundary's evidence. -/
def ExecutionBoundary.evidence (b : ExecutionBoundary) : Option String := b.account.detail

/-- One first visit, recorded before inspecting its policy outcomes. A non-root visit
retains the earlier visit that queued it; IR-only names may lack module attribution. -/
structure ExecutionVisit where
  /-- The visited constant. -/
  name : Lean.Name
  /-- Its declaring module, when the environment attributes one. -/
  moduleName : Option Lean.Name
  /-- The index of the visit that queued this one; `none` for the root. -/
  parent : Option Nat
  deriving Repr, DecidableEq

/-- The walk's complete reached-name census and separately attributed edge sets.
These are observations of the pinned collector, not a minimal runtime call graph.
Current replacements remain distinct from successfully observed historical choices;
active simplifications are used for cycle detection, not claimed compiler calls. -/
structure ExecutionClosure where
  /-- Every name the walk reached, sorted and without duplicates. -/
  nodes : Array Lean.Name
  /-- Each name's first visit, in walk order. -/
  visits : Array ExecutionVisit
  /-- From a constant to each constant its value mentions, where the walk follows the value. -/
  logicalEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- From a constant to the target of each `@[csimp]`-shaped simplification candidate. -/
  candidateEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- From a constant to each replacement target its source replacement history records. -/
  historyEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- From a constant to its current `@[implemented_by]` target. -/
  currentReplacementEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- From a constant to the target of its active `@[csimp]` simplification. -/
  activeSimplificationEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- From an opaque constant to the partial `_unsafe_rec` helper it is compiled through. -/
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

/-- The execution account of one owned executable root: the boundaries and unresolved paths its
closure reaches, its compiled edges and the closure itself. -/
structure ExecutionRoot where
  /-- The root constant. -/
  name : Lean.Name
  /-- Its declaring module. -/
  «module» : Lean.Name
  /-- Every boundary the closure reaches, in the order the walk found them. -/
  boundaries : Array ExecutionBoundary
  /-- A description of each dependency path the analysis could not resolve. -/
  unresolved : Array String
  /-- Direct calls/closures/initializers retained in the pinned compiler IR;
  unlike the boundary candidate closure, these record compiled edges. -/
  compilerEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- The walk's reached names and attributed edge sets. -/
  closure : ExecutionClosure
  deriving Repr, DecidableEq

/-- Lean-resolved origin of one imported module, with its direct imports as
recorded in the loaded module header. -/
structure ModuleOrigin where
  /-- The module's name. -/
  name : Lean.Name
  /-- The canonical path of the `.olean` file it was loaded from. -/
  olean : String
  /-- Its direct imports, as its module header records them. -/
  imports : Array Lean.Name
  deriving Repr, DecidableEq

/-- Complete report for one exact requested module set. -/
structure Environment where
  /-- The Lean version string of the toolchain that loaded the environment. -/
  toolchain : String
  /-- Every module of the loaded environment, sorted and without duplicates. -/
  modules : Array Lean.Name
  /-- The origin of each loaded module; empty when the report omits origins. -/
  moduleOrigins : Array ModuleOrigin
  /-- A record for every constant of the requested owned modules. -/
  declarations : Array Declaration
  /-- The execution account of each owned executable root; empty when execution is not
  inspected. -/
  execution : Array ExecutionRoot
  deriving Repr, DecidableEq


/-- The three information-node roles emitted by Lean's frontend observer. -/
inductive EvaluatorRole where
  /-- A command elaboration node. -/
  | command
  /-- A tactic elaboration node. -/
  | tactic
  /-- A term elaboration node, including partial terms and elaboration choices. -/
  | term
  deriving Repr, DecidableEq

/-- The role's text in transcripts (`command`, `tactic` or `term`); `parse?` reads it back
(`EvaluatorRole.roundtrip`). -/
def EvaluatorRole.spelling : EvaluatorRole → String
  | .command => "command" | .tactic => "tactic" | .term => "term"
/-- The role a text names; `none` for any text that is not a `spelling`
(`EvaluatorRole.canonical`). -/
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
/-- One `import` of the source header, as Lean's frontend parsed it. -/
structure ImportRecord where
  /-- The imported module. -/
  «module» : Lean.Name
  /-- The import is `import all`. -/
  importAll : Bool
  /-- The import is re-exported (`public import`). -/
  isExported : Bool
  /-- The import is a `meta import`. -/
  isMeta : Bool
  deriving Repr, DecidableEq

/-- The source span of a syntax node: its start and stop positions. -/
structure SyntaxRange where
  /-- Where the node begins. -/
  start : Position
  /-- Where the node ends. -/
  «end» : Position
  deriving Repr, DecidableEq

/-- One elaboration node of a command's information tree that names its elaborator. -/
structure Evaluator where
  /-- Whether the node elaborated a command, a tactic or a term. -/
  role : EvaluatorRole
  /-- The elaborator that ran; anonymous for Lean's built-in scaffolding. -/
  elaborator : Lean.Name
  /-- The syntax kind it elaborated. -/
  kind : Lean.Name
  /-- The node's source span, when its syntax has one. -/
  range : Option SyntaxRange
  /-- The elaborator is Lean's scaffolding, a syntax macro, or registered for this kind by the
  toolchain or an imported library, not by the audited module itself. -/
  pinned : Bool
  deriving Repr, DecidableEq

/-- One constant a command added to the environment. -/
structure AddedDeclaration where
  /-- The constant's name. -/
  name : Lean.Name
  /-- The kind of its `ConstantInfo`. -/
  kind : DeclarationKind
  /-- The `repr` of its kernel type expression. -/
  «type» : String
  /-- The native statement of a generated native-proof axiom, computed as
  `Declaration.nativeStatement`; otherwise `none`. -/
  nativeStatement : Option String := none
  deriving Repr, DecidableEq

/-- A constant binder in a command's information tree: where a declared name is written. -/
structure DeclarationBinding where
  /-- The bound constant. -/
  name : Lean.Name
  /-- The source span of its identifier, when recorded. -/
  range : Option SyntaxRange
  deriving Repr, DecidableEq

/-- One command that added constants, with the elaboration that produced them. -/
structure Command where
  /-- The command's elaborator. -/
  commandElaborator : Lean.Name
  /-- The command's syntax kind. -/
  commandKind : Lean.Name
  /-- The command's source span, when recorded. -/
  commandRange : Option SyntaxRange
  /-- The names of the constants the command added. -/
  added : Array Lean.Name
  /-- A record of each added constant. -/
  addedDeclarations : Array AddedDeclaration
  /-- Every elaboration node of the command's information tree that names an elaborator. -/
  evaluators : Array Evaluator
  /-- The constant binders of the command's information tree. -/
  bindings : Array DeclarationBinding := #[]
  /-- Whether the command's syntax, a command its information tree records, or the output of a
  macro expansion there contains an `axiom` declaration node, quoted syntax included. It is read
  from syntax, so it holds even when elaborating that declaration failed. -/
  declaresAxiom : Bool
  /-- Audited-source code that could have run without an evaluator record, accumulated over the
  module up to and including this command: each recorded code runner (`#eval`, `#eval!`,
  `run_cmd`, `run_elab`, `run_meta`, `by_elab`, `run_tac`); each definition the module declares
  whose type, unfolded, receives a `Lean.Core.Context` (code that runs with Lean's elaborator state,
  such as an elaborator, simproc or deriving handler, but not a macro or an `IO` function); and, in
  the environment at every command boundary, under each syntax kind the module did not add, each
  term, tactic, command or `do`-element elaborator entry that is not an entry object of the
  module's post-import environment, each macro the module declares, and each attribute that is
  not the post-import object. -/
  sourceLocalCode : Array Lean.Name
  deriving Repr, DecidableEq

/-- The record of one fresh frontend elaboration of a module's exact source. -/
structure Transcript where
  /-- The elaborated module. -/
  «module» : Lean.Name
  /-- The path of its source file. -/
  source : String
  /-- The source's size in UTF-8 bytes. -/
  sourceBytes : Nat
  /-- The exact source text that was elaborated. -/
  sourceContent : String
  /-- The Lean version string of the elaborating toolchain. -/
  leanVersion : String
  /-- The Git commit of the elaborating toolchain. -/
  leanGitHash : String
  /-- The source header's imports. -/
  imports : Array ImportRecord
  /-- Each command that added constants, in source order. -/
  commands : Array Command
  /-- Every `@[implemented_by]` pair (reference, target) seen in any command's environment, when
  replacement history was requested. -/
  runtimeReplacements : Array (Lean.Name × Lean.Name) := #[]
  /-- Evaluators under which that replacement history cannot be certified, such as `run_cmd` or
  a source-local elaborator. -/
  replacementHistoryUnsupported : Array String := #[]
  deriving Repr, DecidableEq

end Frontend

end RegulaPolicy
