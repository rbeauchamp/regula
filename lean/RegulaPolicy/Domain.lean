module

public import RegulaPolicy.Identity
public import RegulaPolicy.Collections
public import RegulaPolicy.Compiler
public import Regula.Contract
meta import Regula.Decision

/-! # Policy vocabulary and observation data

Closed policy vocabulary and observation data. No operational Lean imports: `Regula.Decision`
is imported for elaboration only (`meta import`), for the `@[regula_decision]` registration of the
decisions below, so no definition here can run what it brings.
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
@[regula_decision]
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
  /-- An `@[extern]` constant of a toolchain module (`Init`, `Std` or `Lean`) whose origin was
  admitted, implemented by the toolchain's own native code. -/
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
  /-- An axiom that trusts the compiler, reached by execution: the enabled legacy
  compiler-trust family or a name the `nativeEqTrue` scheme generates for
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
@[regula_decision]
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

/-- The kind's position in declaration order (`BoundaryKind.index_injective`). -/
def BoundaryKind.index : BoundaryKind → Nat
  | .«runtimeReplacement» => 0
  | .«compilerSimplification» => 1
  | .«nativeRuntime» => 2
  | .«external» => 3
  | .«unsafeComputation» => 4
  | .«partialComputation» => 5
  | .«opaqueComputation» => 6
  | .«compilerTrustedProof» => 7

/-- Distinct kinds have distinct indices. -/
theorem BoundaryKind.index_injective : Function.Injective BoundaryKind.index := by
  intro a b h
  cases a <;> cases b <;> simp_all [BoundaryKind.index]

/-- Kinds ordered by `index`, for canonical keyed sets. -/
instance : Ord BoundaryKind := ⟨compareOn BoundaryKind.index⟩
instance : Std.TransOrd BoundaryKind :=
  inferInstanceAs (Std.TransCmp (compareOn BoundaryKind.index))
instance : Std.LawfulEqOrd BoundaryKind where
  eq_of_compare h := BoundaryKind.index_injective (Std.LawfulEqOrd.eq_of_compare h)

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
@[regula_decision]
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

/-- The kernel's answer to the theorem the checker declares, without adding it, to compare a
runtime replacement with its reference: a closed proof, checked against the exact required
proposition (`Probe.kernelAnswer`). Only the result of the kernel's own check selects the
constructor. -/
inductive KernelAnswer where
  /-- The kernel admitted the theorem. `axioms` are its transitive axioms, and `detail` prints
  its proof and the required proposition. -/
  | admitted (axioms : Array Lean.Name) (detail : String)
  /-- The kernel finished its check and refused the theorem. -/
  | refused
  /-- The kernel stopped before it decided: it exhausted its resources or was interrupted. -/
  | exhausted
  deriving Repr, DecidableEq

/-- Each axiom is one of the Standard-Logical foundations: `propext`, `Quot.sound` or
`Classical.choice`. -/
def KernelAnswer.withinStandardLogical (axioms : Array Lean.Name) : Bool :=
  axioms.all fun ax => ax == `propext || ax == `Quot.sound || ax == `Classical.choice

/-- Outcome of the checker's kernel check of one closed correspondence proof between a runtime
replacement and its reference: the reflexivity proof of the definitional comparison, or a proof
that a theorem candidate gives. Each value has one meaning, stated by the kernel's answer that
the attempt recorded (`KernelAnswer`); `ofAttempt` gives the value of an attempt, and its theorems
show that the value it gives has this meaning:

- `completed (some detail)`: the attempt recorded the kernel's admission of the proof, with its
  axioms within the Standard-Logical foundations. `detail` prints that proof and the required
  proposition (`ofAttempt_checked_iff`).
- `completed none`: the attempt recorded a decision of the kernel without such evidence: its
  refusal of the proof, or its admission of the proof with an axiom outside those foundations
  (`ofAttempt_negative_iff`).
- `incomplete reason`: the attempt recorded no decision of the kernel. The kernel stopped before
  it decided (resource exhaustion or interruption), or the attempt raised an error, whatever the
  error, before it recorded the kernel's answer, also after the kernel admitted the proof
  (`ofAttempt_incomplete_iff`). `reason` tells which. -/
inductive DefeqComparison where
  /-- The attempt recorded a decision of the kernel; `admitted` is the evidence detail when it
  recorded an admission of the proof within the Standard-Logical foundations. -/
  | completed (admitted : Option String)
  /-- The attempt recorded no decision of the kernel; `reason` tells why. -/
  | incomplete (reason : String)
  deriving Repr, DecidableEq

/-- The comparison that an attempt records. The attempt is the kernel's answer, or the text of
the error that the attempt raised before it recorded an answer. Only the answer of a kernel that
decided completes a comparison, so an attempt that raised an error is incomplete, whatever the
error (`ofAttempt_error`). -/
def DefeqComparison.ofAttempt : Except String KernelAnswer → DefeqComparison
  | .ok (.admitted axioms detail) =>
      .completed (if KernelAnswer.withinStandardLogical axioms then some detail else none)
  | .ok .refused => .completed none
  | .ok .exhausted =>
      .incomplete "kernel resources exhausted before deciding definitional correspondence"
  | .error error =>
      .incomplete s!"the comparison failed before it recorded the kernel's answer: {error}"

/-- Standard §7.6 classification, total over the comparison outcome: completed positive is
checked, completed negative leaves the replacement trusted, and a comparison that could not
complete is unresolved. -/
def DefeqComparison.classify : DefeqComparison → Correspondence × Option String
  | .completed (some detail) => (.checked, some s!"kernel-defeq; {detail}")
  | .completed none => (.trusted, some "no kernel-checked unconditional correspondence proof")
  | .incomplete reason =>
      (.unresolved, some s!"no kernel-checked unconditional correspondence proof; {reason}")

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
    o.classify.1 = .unresolved ↔ ∃ reason, o = .incomplete reason := by
  rcases o with (_ | _) | _ <;> simp [classify]

/-- An attempt records a completed positive comparison exactly when it recorded the kernel's
admission of the proof with its axioms within the Standard-Logical foundations; `detail` is the
admitted detail. -/
theorem DefeqComparison.ofAttempt_checked_iff (attempt : Except String KernelAnswer)
    (detail : String) :
    ofAttempt attempt = .completed (some detail) ↔
      ∃ axioms, attempt = .ok (.admitted axioms detail) ∧
        KernelAnswer.withinStandardLogical axioms = true := by
  rcases attempt with error | (⟨axioms, admitted⟩ | _ | _)
  · simp [ofAttempt]
  · cases h : KernelAnswer.withinStandardLogical axioms
    · simp [ofAttempt, h]
    · simp only [ofAttempt, h, ite_true, completed.injEq, Option.some.injEq, Except.ok.injEq,
        KernelAnswer.admitted.injEq]
      exact ⟨fun same => ⟨axioms, ⟨rfl, same⟩, h⟩, fun ⟨_, ⟨_, same⟩, _⟩ => same⟩
  · simp [ofAttempt]
  · simp [ofAttempt]

/-- An attempt records a completed negative comparison exactly when it recorded the kernel's
refusal of the proof, or its admission of the proof with an axiom outside the Standard-Logical
foundations. -/
theorem DefeqComparison.ofAttempt_negative_iff (attempt : Except String KernelAnswer) :
    ofAttempt attempt = .completed none ↔
      attempt = .ok .refused ∨ ∃ axioms detail, attempt = .ok (.admitted axioms detail) ∧
        KernelAnswer.withinStandardLogical axioms = false := by
  rcases attempt with error | (⟨axioms, detail⟩ | _ | _)
  · simp [ofAttempt]
  · cases h : KernelAnswer.withinStandardLogical axioms <;> simp [ofAttempt, h]
  · simp [ofAttempt]
  · simp [ofAttempt]

/-- An attempt records an incomplete comparison exactly when it recorded that the kernel stopped
before it decided, or it raised an error before it recorded an answer. -/
theorem DefeqComparison.ofAttempt_incomplete_iff (attempt : Except String KernelAnswer) :
    (∃ reason, ofAttempt attempt = .incomplete reason) ↔
      attempt = .ok .exhausted ∨ ∃ error, attempt = .error error := by
  rcases attempt with error | (⟨axioms, detail⟩ | _ | _) <;> simp [ofAttempt]

/-- No path leads from an error to a completed comparison: an attempt that raised an error is
unresolved, whatever the error. -/
theorem DefeqComparison.ofAttempt_error (error : String) :
    (ofAttempt (.error error)).classify.1 = .unresolved := rfl

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
@[regula_decision]
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
@[regula_decision]
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
  /-- A resolved boundary passes only with checked evidence or when its trusted evidence carries
  an admitted toolchain origin (`BoundaryOK`), which only a runtime replacement, native-runtime
  `extern`, or unsafe or partial computation can (`TrustedEvidence`). -/
  | «checked»
  deriving Repr, DecidableEq, Inhabited

/-- The claim's text in manifests and reports (`report` or `checked`); `parse?` reads it back
(`ExecutionClaim.roundtrip`). -/
def ExecutionClaim.spelling : ExecutionClaim → String
  | .«report» => "report"
  | .«checked» => "checked"

/-- The claim a text names; `none` for any text that is not a `spelling`
(`ExecutionClaim.canonical`). -/
@[regula_decision]
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
@[regula_decision]
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
@[regula_decision]
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
@[regula_decision]
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

/-- The route by which Lean's recursion compiler regenerated a helper's base
(`Declaration.unsafeRecRegenerated`); parsing cannot manufacture an unknown constructor. -/
inductive RecursionOrigin where
  /-- Structural recursion. -/
  | «structural»
  /-- Well-founded recursion. -/
  | «wellFounded»
  deriving Repr, DecidableEq, Inhabited

/-- The origin's text in reports (`structural` or `well-founded`); `parse?` reads it back
(`RecursionOrigin.roundtrip`). -/
def RecursionOrigin.spelling : RecursionOrigin → String
  | .«structural» => "structural"
  | .«wellFounded» => "well-founded"

/-- The origin a text names; `none` for any text that is not a `spelling`
(`RecursionOrigin.canonical`). -/
@[regula_decision]
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

/-- `a` is at or before `b`: lines compared first, then columns on the same line. -/
def positionLE (a b : Position) : Bool :=
  a.line < b.line || (a.line == b.line && a.column ≤ b.column)

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

/-- `a` is at or before `b`, as a proposition: lines compared first, then columns on the same
line. `positionLE` decides it (`positionLE_iff`). -/
def PositionLE (a b : Position) : Prop :=
  a.line < b.line ∨ (a.line = b.line ∧ a.column ≤ b.column)

instance (a b : Position) : Decidable (PositionLE a b) := by
  unfold PositionLE; infer_instance

/-- The executed comparison accepts exactly the positions that `PositionLE` relates. -/
theorem positionLE_iff (a b : Position) : positionLE a b = true ↔ PositionLE a b := by
  simp [positionLE, PositionLE]

/-- A position is at or before itself. -/
theorem PositionLE.refl (a : Position) : PositionLE a a := .inr ⟨rfl, Nat.le_refl _⟩

/-- The selection range lies within the full range, as a proposition: the full range starts at or
before the selection range, and the selection range ends at or before the full range. It is stated
with no test: `Ranges.admitted` decides it with the comparisons of Lean's natural numbers. -/
def Ranges.Nested (r : Ranges) : Prop :=
  PositionLE r.range.start r.selectionRange.start ∧ PositionLE r.selectionRange.end r.range.end

instance (r : Ranges) : Decidable r.Nested := by
  unfold Ranges.Nested; infer_instance

/-- The pair admission and finding locations use for a recorded pair: the recorded pair itself
when its selection range lies within its full range, and otherwise the full range as its own
selection range. Nothing is enlarged and nothing about the declaration is consulted. Lean records
the two ranges from two pieces of syntax (`Lean.Elab.addDeclarationRangesFromSyntax`) that it
does not relate: for a declaration it elaborates from the source as parsed the second is the
first or a part of it, but for a definition `aux_def` generates the first is the position of the
command that called `aux_def` and the second the positions of that caller's name suggestions, so
`macro_rules` over several syntax kinds gives a kind's definition a selection range that ends
after its range. -/
def Ranges.admitted (r : Ranges) : Ranges :=
  if r.Nested then r else { range := r.range, selectionRange := r.range }

/-- Which directions of a decision a registered contract's requirement states, one value for
each of the structures `Regula.DecidesSoundly`, `Regula.DecidesCompletely` and `Regula.Decides`
(`DecisionKind.structureName`); parsing cannot manufacture an unknown constructor. -/
inductive DecisionKind where
  /-- `Regula.DecidesSoundly`: the function accepts only inputs that satisfy the
  specification. -/
  | «sound»
  /-- `Regula.DecidesCompletely`: the function accepts every input that satisfies the
  specification. -/
  | «complete»
  /-- `Regula.Decides`: both directions. -/
  | «soundAndComplete»
  deriving Repr, DecidableEq, Inhabited

/-- The kind's text in reports (`sound`, `complete` or `sound-and-complete`); `parse?` reads it
back (`DecisionKind.roundtrip`). -/
def DecisionKind.spelling : DecisionKind → String
  | .«sound» => "sound"
  | .«complete» => "complete"
  | .«soundAndComplete» => "sound-and-complete"

/-- The kind a text names; `none` for any text that is not a `spelling`
(`DecisionKind.canonical`). -/
@[regula_decision]
def DecisionKind.parse? : String → Option DecisionKind
  | "sound" => some .«sound»
  | "complete" => some .«complete»
  | "sound-and-complete" => some .«soundAndComplete»
  | _ => none

instance : ToString DecisionKind := ⟨DecisionKind.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem DecisionKind.roundtrip (x : DecisionKind) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem DecisionKind.canonical (s : String) (x : DecisionKind) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- The structure of `Regula.Contract` whose proof a registration of each kind requires. -/
def DecisionKind.structureName : DecisionKind → Lean.Name
  | .«sound» => ``Regula.DecidesSoundly
  | .«complete» => ``Regula.DecidesCompletely
  | .«soundAndComplete» => ``Regula.Decides

/-- The kind whose structure `name` is; `none` for every other name
(`DecisionKind.ofStructureName?_eq_some_iff`). The collector applies it to the head constant of
a registration's reduced requirement. -/
@[regula_decision]
def DecisionKind.ofStructureName? : Lean.Name → Option DecisionKind
  | .str (.str .anonymous "Regula") "DecidesSoundly" => some .«sound»
  | .str (.str .anonymous "Regula") "DecidesCompletely" => some .«complete»
  | .str (.str .anonymous "Regula") "Decides" => some .«soundAndComplete»
  | _ => none

/-- A name is read as a kind exactly when it is that kind's structure. -/
theorem DecisionKind.ofStructureName?_eq_some_iff (name : Lean.Name) (kind : DecisionKind) :
    ofStructureName? name = some kind ↔ name = kind.structureName := by
  constructor
  · intro h
    unfold ofStructureName? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    cases kind <;> rfl

/-- Every decision kind (`DecisionKind.mem_all`). -/
def DecisionKind.all : Array DecisionKind := #[.«sound», .«complete», .«soundAndComplete»]

/-- Each kind is listed. A new kind is a new constructor, and this theorem fails until `all` lists
it. -/
theorem DecisionKind.mem_all (kind : DecisionKind) : kind ∈ all := by
  cases kind <;> simp [all]

/-- The structure of each decision kind, the constants to which a registration's requirement
reduces when it states a kind (`DecisionKind.mem_structureNames_iff`). -/
def DecisionKind.structureNames : Array Lean.Name := all.map structureName

/-- A name is listed exactly when it is read as a kind (`ofStructureName?`). -/
theorem DecisionKind.mem_structureNames_iff (name : Lean.Name) :
    name ∈ structureNames ↔ (ofStructureName? name).isSome := by
  simp only [structureNames, Array.mem_map, Option.isSome_iff_exists,
    ofStructureName?_eq_some_iff]
  constructor
  · rintro ⟨kind, -, rfl⟩
    exact ⟨kind, rfl⟩
  · rintro ⟨kind, rfl⟩
    exact ⟨kind, mem_all kind, rfl⟩

/-- What a registration of the kind establishes about the implementation, as the account
states it. -/
def DecisionKind.establishes : DecisionKind → String
  | .«sound» =>
      "accepts only inputs that satisfy the specification, and accepts at least one input"
  | .«complete» =>
      "accepts every input that satisfies the specification, and refuses at least one input"
  | .«soundAndComplete» =>
      "accepts exactly the inputs that satisfy the specification, and both outcomes occur"

/-- The direction a one-way kind does not establish, as the account states it; `none` exactly
for the two-way kind (`DecisionKind.leavesOpen_eq_none_iff`). -/
def DecisionKind.leavesOpen : DecisionKind → Option String
  | .«sound» => some "may refuse inputs that satisfy the specification"
  | .«complete» => some "may accept inputs that do not satisfy the specification"
  | .«soundAndComplete» => none

/-- Only the two-way kind leaves no direction open: each one-way kind states the direction it
does not establish. -/
theorem DecisionKind.leavesOpen_eq_none_iff (kind : DecisionKind) :
    kind.leavesOpen = none ↔ kind = .«soundAndComplete» := by
  cases kind <;> simp [leavesOpen]

/-- What the collector reads, from kernel-checked declarations, of a decided function that
applies the implementation to arguments under one binder (`fun input => f a₁ … aₙ`): the shape of
the inductive type of whose value the first argument is a field, and which field of the bound
variable each argument is. -/
structure FieldPacking where
  /-- The number of constructors of that type. -/
  constructors : Nat
  /-- The number of indices of that type. -/
  indices : Nat
  /-- The number of fields of its first constructor. -/
  fields : Nat
  /-- For each argument in order, the position of the field of the bound variable that it is;
  `none` for an argument that is not a field of the bound variable in that type. -/
  arguments : List (Option Nat)
  deriving Repr, DecidableEq

/-- The packing covers every argument of the implementation: the type has one constructor and no
index, and the arguments are its fields, each once and in the order of the fields.

With one constructor and no index, the constructor takes every tuple of fields to a value of the
binder's type, and Lean's kernel reduces each projection of that value to the field. So every
tuple of arguments is the fields of a packed value, which is the hypothesis of
`Regula.Decides.of_packing`. An index breaks this: the constructor's result has the index its
fields compute, so the binder's type holds only the tuples with that index. -/
def FieldPacking.Covers (packing : FieldPacking) : Prop :=
  packing.constructors = 1 ∧ packing.indices = 0 ∧
    packing.arguments = (List.range packing.fields).map some

/-- Whether the packing covers every argument of the implementation (`FieldPacking.covers_iff`).
The collector reads a decided function as a field application only when this holds. -/
@[regula_decision]
def FieldPacking.covers (packing : FieldPacking) : Bool :=
  packing.constructors == 1 && packing.indices == 0 &&
    packing.arguments == (List.range packing.fields).map some

/-- The executed decision accepts exactly the packings that cover every argument. -/
theorem FieldPacking.covers_iff (packing : FieldPacking) :
    packing.covers = true ↔ packing.Covers := by
  simp [covers, Covers, and_assoc]

/-- What the collector reads, from the kernel-checked statement, of the function that a decision
kind is stated about, when that function is the implementation's constant or a field application
of it, under any number of applications of `Function.uncurry` and of the erasures of
`Regula.Contract`. -/
structure DecidedFunction where
  /-- The field application at the core of the function (`FieldPacking`), or `none` when the
  core is the implementation's constant itself. -/
  packing : Option FieldPacking
  /-- The number of arguments that a result of the function takes: the leading binders of the
  kind's result type, with every definition unfolded. -/
  unsupplied : Nat
  deriving Repr, DecidableEq

/-- The decided function is the implementation on every argument: a field application covers
every field (`FieldPacking.Covers`), and no result of the function takes an argument.

A term can be applied only when its type reduces to a function type, so a result type with no
leading binder is the type of a result that takes no argument. The implementation then has no
argument after those that its constant, the field application and the surrounding
`Function.uncurry` applications supply.

The condition on the result is structural and conservative. With an argument left, an
acceptance predicate that reads the function-valued result at one fixed value of that argument
gives the kind of one slice of the implementation (`Regula.Decides.iff_slice`). One that
quantifies over the argument can constrain every value, and this decision, which does not read
the acceptance predicate, refuses it too. The remedy for both is to supply the argument. -/
def DecidedFunction.Covers (decided : DecidedFunction) : Prop :=
  (∀ packing, decided.packing = some packing → packing.Covers) ∧ decided.unsupplied = 0

/-- Whether the decided function is the implementation on every argument
(`DecidedFunction.covers_iff`). The collector refuses a decision registration unless this
holds. -/
@[regula_decision]
def DecidedFunction.covers (decided : DecidedFunction) : Bool :=
  decided.packing.all FieldPacking.covers && decided.unsupplied == 0

/-- The executed decision accepts exactly the decided functions that are the implementation on
every argument. -/
theorem DecidedFunction.covers_iff (decided : DecidedFunction) :
    decided.covers = true ↔ decided.Covers := by
  cases decided with
  | mk packing unsupplied =>
    cases packing <;> simp [covers, Covers, FieldPacking.covers_iff]

/-- The form of the result type of a constant, as the collector reads it: the constant's type
with every leading binder opened and every definition unfolded. The class of a definition that
the two sides of a decision registration share depends on this form (`SharedDefinition`). -/
inductive ResultForm where
  /-- A sort, or a structure with no index whose every field is a proof or has a sort as its
  result: a value is a type, a proposition or a record of propositions, as a value of `LT α`
  is. -/
  | «statement»
  /-- The type of the constant is itself a proposition, so each of its values is a proof. -/
  | «proof»
  /-- `Decidable p`: each value carries a proof of `p` or a proof of its negation. -/
  | «decidable»
  /-- `Bool`. -/
  | «bool»
  /-- `BEq _`, a structure of one function to `Bool`. -/
  | «beq»
  /-- Every other type. -/
  | «other»
  deriving Repr, DecidableEq, Inhabited

/-- The value of a definition with this result form is read as a part of a term that mentions
the definition. `specification` says that the term is a statement: the specification of a
decision registration, or its acceptance predicate, which is read by the same rule. Otherwise
the term is the implementation, a function. In each term this is no proof. In a statement it is
also no `Decidable` value, and in the implementation it is also no statement.

A proposition does not depend on which proof of a statement a term holds. A type `Decidable p`
has at most one value (`Subsingleton (Decidable p)`), so a statement does not depend on which
decision procedure of `p` it mentions, and the value of the procedure is not read there.

A function runs the procedure, so in the implementation the value of a `Decidable` definition
is read: with `P x := h x = true` and `f x := decide (P x)`, the instance that `f` runs calls
`h`, and a wrong `h` changes `f` and a specification that mentions `h` together. A function
does not run a statement, so the value of a statement is not read in the implementation: a
function that decides a proposition depends on the procedure that it runs, and not also on each
definition that the proposition mentions and the procedure does not call.

The acceptance predicate is a statement about the result of the function, so the value of a
statement that it mentions is read: with `Small n := h n = true`, the search reaches `h` from
the acceptance predicate `Small` as it does from `fun n => h n = true`. -/
def ResultForm.ValueRead (specification : Bool) (form : ResultForm) : Prop :=
  form ≠ .«proof» ∧ (specification = true → form ≠ .«decidable») ∧
    (specification = false → form ≠ .«statement»)

instance (specification : Bool) (form : ResultForm) :
    Decidable (form.ValueRead specification) := by
  unfold ResultForm.ValueRead; infer_instance

/-- What the collector reads of a constant that the specification of a decision registration
reaches and that the implementation, or the acceptance predicate, reaches too.

The kind, the projection and the result form are read from the constant's kernel-checked
declaration. Whether Lean generated the constant is read from Lean's records of the declarations
it generates, which are environment state that an audited project can write; that field takes a
definition out of the class `SharedClass.other` only, and never out of the class
`SharedClass.boolean` (`SharedDefinition.class`). -/
structure SharedDefinition where
  /-- The constant. -/
  name : Lean.Name
  /-- The kind of its `ConstantInfo`. -/
  kind : DeclarationKind
  /-- The value of the constant is a field's projection function: under its binders, the
  primitive projection of its last argument. -/
  projection : Bool
  /-- The constant is a function, by its type alone: the type, with every definition unfolded,
  has a leading binder, or its result is a structure type with a field that takes an argument
  and is neither a proof nor a statement, as `BEq α` and `Ord α` are. The form of its value has
  no part. A constant that is no function gives a name to a closed term, such as a number or a
  table, and the search reads the constants of that term. -/
  function : Bool
  /-- Lean's records say that Lean generated the constant for an inductive type or as a
  matcher: a parent projection, an auxiliary recursor such as `casesOn`, a `noConfusion`, a
  matcher, or a construction such as `ctorIdx`. -/
  generated : Bool
  /-- The form of its result type. -/
  result : ResultForm
  deriving Repr, DecidableEq

/-- The constant stands for a value that a term can depend on, and it is no field of data: it is
a definition, an opaque constant or an axiom, and it is no projection function. An inductive
type, a constructor and a recursor are data, a projection function reads a field of data, and a
theorem has no value that a term can depend on. An axiom is counted as an opaque constant is:
Lean's kernel unfolds neither, and a term depends on what each stands for. Lean gives a file with
a `module` header an imported definition as an axiom when its module does not export the value,
so the class of such a constant is read from its type alone (`SharedDefinition.class`). An axiom
that states a proposition has the result form of a proof, whose class this condition does not
decide. -/
def SharedDefinition.Defines (shared : SharedDefinition) : Prop :=
  (shared.kind = .«definition» ∨ shared.kind = .«opaque» ∨ shared.kind = .«axiom») ∧
    shared.projection = false

instance (shared : SharedDefinition) : Decidable shared.Defines := by
  unfold SharedDefinition.Defines; infer_instance

/-- The constant computes a result from an input: it has a value that a term can depend on
(`SharedDefinition.Defines`), and it is a function. A definition that is no function has no
input to be wrong about: it names a closed term, which a specification that mentions it
states. -/
def SharedDefinition.Computes (shared : SharedDefinition) : Prop :=
  shared.Defines ∧ shared.function = true

instance (shared : SharedDefinition) : Decidable shared.Computes := by
  unfold SharedDefinition.Computes; infer_instance

/-- The class of a constant that the two sides of a decision registration share
(`SharedDefinition.class`). The record of the registration names each constant of the class
`boolean` that its specification reaches at any depth, and each constant of the class `other`
that its specification reaches first (`SharedNames`). It names no constant of the other three
classes. A registration is refused for a constant of the class `boolean` (`sharedTestFailure`),
and for no other class. -/
inductive SharedClass where
  /-- A type, a statement or a proof: a constant whose value is a type, a proposition or a
  record of propositions, and a proof. An inductive type, a theorem and a definition of a
  proposition are in this class. -/
  | «statement»
  /-- A constant with a result of `Decidable p`. -/
  | decidable
  /-- Data, or a name for data: each constant of another result form that does not compute
  (`SharedDefinition.Computes`), such as a constructor, a recursor, a field's projection
  function and a constant that is no function, and a function with a result that is not `Bool`
  or `BEq _` that Lean's records say Lean generated. -/
  | data
  /-- A function with a result of `Bool`, and a definition with a result of `BEq _`, which is a
  record of one function to `Bool`. -/
  | boolean
  /-- Each other function: a function with a result of any other type. -/
  | other
  deriving Repr, DecidableEq, Inhabited

/-- The class of a shared constant, from what the collector read of it.

When the two sides of a decision kind share a function, a change of that function changes the
two sides together, and a proof of the kind that goes through the function on the two sides can
stay valid although the meaning changed. So the kind does not establish that the function is
the intended one. The classes `boolean` and `other` are those functions. A constant of the
class `statement` is no function that runs. A type `Decidable p` has at most one value, so a
statement does not depend on which value of it a term names. A constant of the class `data`
computes nothing from an input.

The result of a function of the class `boolean` is a truth value, or a test that gives one. A
proposition can take its place in a specification. No type tells a function of the class
`other` that a specification is about, such as an encoding or a state transition, from one that
only prepares the input. -/
def SharedDefinition.class (shared : SharedDefinition) : SharedClass :=
  match shared.result with
  | .«proof» | .«statement» => .«statement»
  | .«decidable» => .decidable
  | .«bool» => if shared.Computes then .boolean else .data
  | .«beq» => if shared.Defines then .boolean else .data
  | .«other» =>
    if shared.Computes ∧ shared.generated = false then .other else .data

/-- A constant is of the class `boolean` exactly when it computes and its result is `Bool`, or
it has a value and its result is `BEq _`. Lean's records of generated declarations have no
part in this class, and neither has the form of a value. -/
theorem SharedDefinition.class_eq_boolean_iff (shared : SharedDefinition) :
    shared.class = .boolean ↔
      (shared.Computes ∧ shared.result = .«bool») ∨
        (shared.Defines ∧ shared.result = .«beq») := by
  unfold SharedDefinition.class
  cases shared.result <;> by_cases computes : shared.Computes <;>
    by_cases defines : shared.Defines <;> simp [computes, defines] <;> split <;> simp

/-- A definition with a result of `BEq _` is of the class `boolean` whatever else the collector
read of it: whether it takes an argument, and whether Lean's records say that Lean generated
it. So a `BEq` record that is a name for another instance is named like one that is written
as a constructor application. -/
theorem SharedDefinition.class_of_beq (shared : SharedDefinition) (defines : shared.Defines)
    (result : shared.result = .«beq») : shared.class = .boolean :=
  shared.class_eq_boolean_iff.mpr (.inr ⟨defines, result⟩)

/-- A constant is of the class `other` exactly when it computes, Lean's records do not say that
Lean generated it, and its result is of a type with no other form. -/
theorem SharedDefinition.class_eq_other_iff (shared : SharedDefinition) :
    shared.class = .other ↔
      shared.Computes ∧ shared.generated = false ∧ shared.result = .«other» := by
  unfold SharedDefinition.class
  cases shared.result <;> by_cases computes : shared.Computes <;> simp [computes]
  all_goals split <;> simp

/-- Controls of the classes, each with the kind, the projection, the function, the generated
record and the result form that the collector reads. A function with a result of `Bool` is of
the class `boolean`, also where Lean's records say that Lean generated it, and also where the
environment has it as an axiom, as a file with a `module` header has an imported function with no
exported value. A function with a result of a list is of the class `other`, and of the class
`data` where Lean's records say that Lean generated it. A `BEq` record is of the class `boolean`
also where it takes no argument. A `Decidable` value, a proof, an axiom that states a
proposition, a constant that is no function and a field's projection function are of no named
class. -/
example :
    (⟨`test, .«definition», false, true, false, .«bool»⟩ : SharedDefinition).class = .boolean ∧
    (⟨`derived, .«definition», false, true, true, .«beq»⟩ : SharedDefinition).class = .boolean ∧
    (⟨`named, .«definition», false, false, false, .«beq»⟩ : SharedDefinition).class = .boolean ∧
    (⟨`marks, .«definition», false, true, false, .«other»⟩ : SharedDefinition).class = .other ∧
    (⟨`matcher, .«definition», false, true, true, .«other»⟩ : SharedDefinition).class = .data ∧
    (⟨`decides, .«definition», false, true, false, .«decidable»⟩ : SharedDefinition).class =
      .decidable ∧
    (⟨`proved, .«theorem», false, false, false, .«proof»⟩ : SharedDefinition).class =
      .«statement» ∧
    (⟨`limit, .«definition», false, false, false, .«other»⟩ : SharedDefinition).class = .data ∧
    (⟨`field, .«definition», true, true, false, .«bool»⟩ : SharedDefinition).class = .data ∧
    (⟨`hidden, .«axiom», false, true, false, .«bool»⟩ : SharedDefinition).class = .boolean ∧
    (⟨`assumed, .«axiom», false, false, false, .«proof»⟩ : SharedDefinition).class =
      .«statement» := by
  decide

/-- The constant is counted: its class is `boolean` or `other`. The search from the
specification does not read the value of a counted constant that the other side reaches: what
that value mentions is a part of the counted constant, which the record names. -/
def SharedDefinition.Counted (shared : SharedDefinition) : Prop :=
  shared.class = .boolean ∨ shared.class = .other

instance (shared : SharedDefinition) : Decidable shared.Counted := by
  unfold SharedDefinition.Counted; infer_instance

/-- The names that the record of a decision registration holds of the functions that its
specification shares with its implementation or its acceptance predicate, by class
(`sharedNames`). Each list is sorted and has no duplicate. The lists come from three searches:
a function of the class `boolean` is named at any depth, a function of the class `other` is
named where the specification reaches it first, and a function of the class `boolean` that the
two sides share only when the search also enters the declaration of the input type from the
input is named apart. -/
structure SharedNames where
  /-- The functions of the class `SharedClass.boolean` that the specification reaches at any
  depth, also below a function of the class `other`, and that the other side reaches too. -/
  booleans : Array Lean.Name := #[]
  /-- The functions of the class `SharedClass.other` that the specification reaches first, with
  no counted function between, and that the other side reaches too. -/
  others : Array Lean.Name := #[]
  /-- The functions of the class `SharedClass.boolean` that the two sides share when the
  specification is read by the rule of a statement, which also enters the declaration of the
  input type of the kind from the input, and that are not in `booleans`
  (`RegulaPolicy.StatementReading`). The other side is the same in the two readings. The
  specification reaches each of them only through a constant of the input type that its body
  does not name (`RegulaPolicy.StatementReading.through_input`). No registration is refused
  for them: the record names them so that a review sees, for example, an invariant of the input
  that names a test of the implementation. -/
  throughTypes : Array Lean.Name := #[]
  deriving Repr, DecidableEq, Inhabited

/-- No function is named. -/
def SharedNames.isEmpty (names : SharedNames) : Bool :=
  names.booleans.isEmpty && names.others.isEmpty && names.throughTypes.isEmpty

/-- The named functions of the class `boolean` as a finding and a classification line print
them: `shared-booleans=` and the list of the names as Lean prints them. -/
def SharedNames.booleansText (names : SharedNames) : String :=
  s!"shared-booleans={repr (names.booleans.toList.map (·.toString))}"

/-- The names of the constants of the class `boolean` in `definitions`. -/
def booleanNames (definitions : List SharedDefinition) : List Lean.Name :=
  (definitions.filter fun definition => decide (definition.class = .boolean)).map (·.name)

/-- A name is among `booleanNames` exactly when it is the name of a constant of the class
`boolean` in the list. -/
theorem mem_booleanNames (definitions : List SharedDefinition) (name : Lean.Name) :
    name ∈ booleanNames definitions ↔ ∃ definition ∈ definitions,
      definition.class = .boolean ∧ definition.name = name := by
  simp [booleanNames, and_assoc]

/-- The names that the record of a decision registration holds, from what the collector read of
three lists of shared constants. `first` has each counted constant that the specification reaches
first: that reading stops at each of them. `reached` has each constant that the specification
reaches at any depth and that the other side reaches too: that reading stops at no constant.
`widened` has each constant that the specification reaches at any depth by the rule of a
statement, which also enters the declaration of the input type from the input, and that the other
side reaches too, the same other side as for `reached`. The functions of the class `boolean` are
named from `reached`, those of the class `other` from `first`, and those of the class `boolean`
that `widened` has and `reached` does not are named apart (`mem_sharedNames_booleans`,
`mem_sharedNames_others`, `mem_sharedNames_throughTypes`). The class of each constant is
`SharedDefinition.class`, so the executed class is the stated one. -/
def sharedNames (first reached widened : List SharedDefinition) : SharedNames where
  booleans := canonicalNames (booleanNames reached).toArray
  others := canonicalNames
    ((first.filter fun definition => decide (definition.class = .other)).map (·.name)).toArray
  throughTypes := canonicalNames
    ((booleanNames widened).filter fun name => !(booleanNames reached).contains name).toArray

/-- A name is among the named functions of the class `boolean` exactly when it is the name of a
constant of that class that the search at any depth read. -/
theorem mem_sharedNames_booleans (first reached widened : List SharedDefinition)
    (name : Lean.Name) :
    name ∈ (sharedNames first reached widened).booleans ↔ ∃ definition ∈ reached,
      definition.class = .boolean ∧ definition.name = name := by
  simp [sharedNames, mem_canonicalNames, mem_booleanNames]

/-- A name is among the named functions of the class `other` exactly when it is the name of a
constant of that class that the specification reaches first. -/
theorem mem_sharedNames_others (first reached widened : List SharedDefinition)
    (name : Lean.Name) :
    name ∈ (sharedNames first reached widened).others ↔ ∃ definition ∈ first,
      definition.class = .other ∧ definition.name = name := by
  simp [sharedNames, mem_canonicalNames, and_assoc]

/-- A name is among the functions that the two sides share only through types exactly when it is
the name of a constant of the class `boolean` that the search with the types read, and no
constant of that class with that name is one that the search read. -/
theorem mem_sharedNames_throughTypes (first reached widened : List SharedDefinition)
    (name : Lean.Name) :
    name ∈ (sharedNames first reached widened).throughTypes ↔
      (∃ definition ∈ widened, definition.class = .boolean ∧ definition.name = name) ∧
        ¬ ∃ definition ∈ reached, definition.class = .boolean ∧ definition.name = name := by
  simp only [sharedNames, mem_canonicalNames, List.mem_toArray, List.mem_filter,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq, List.contains_iff_mem, mem_booleanNames]

/-- No function of the class `boolean` is named exactly when the search at any depth read no
constant of that class. -/
theorem sharedNames_booleans_eq_empty_iff (first reached widened : List SharedDefinition) :
    (sharedNames first reached widened).booleans = #[] ↔
      ∀ definition ∈ reached, definition.class ≠ .boolean := by
  simp only [Array.eq_empty_iff_forall_not_mem, mem_sharedNames_booleans]
  exact ⟨fun absent definition member boolean => absent _ ⟨definition, member, boolean, rfl⟩,
    fun absent _ ⟨definition, member, boolean, _⟩ => absent definition member boolean⟩

/-- No function of the class `other` is named exactly when the specification reaches no constant
of that class first. -/
theorem sharedNames_others_eq_empty_iff (first reached widened : List SharedDefinition) :
    (sharedNames first reached widened).others = #[] ↔
      ∀ definition ∈ first, definition.class ≠ .other := by
  simp only [Array.eq_empty_iff_forall_not_mem, mem_sharedNames_others]
  exact ⟨fun absent definition member other => absent _ ⟨definition, member, other, rfl⟩,
    fun absent _ ⟨definition, member, other, _⟩ => absent definition member other⟩

/-- No function is named only through types exactly when each constant of the class `boolean`
that the search with the types read has the name of one that the search read. -/
theorem sharedNames_throughTypes_eq_empty_iff (first reached widened : List SharedDefinition) :
    (sharedNames first reached widened).throughTypes = #[] ↔
      ∀ definition ∈ widened, definition.class = .boolean →
        ∃ other ∈ reached, other.class = .boolean ∧ other.name = definition.name := by
  simp only [Array.eq_empty_iff_forall_not_mem, mem_sharedNames_throughTypes, not_and,
    Classical.not_not]
  exact ⟨fun absent definition member boolean => absent _ ⟨definition, member, boolean, rfl⟩,
    fun absent _ ⟨definition, member, boolean, same⟩ => same ▸ absent definition member boolean⟩

/-- No function is named exactly when the search at any depth read no constant of the class
`boolean`, the specification reaches no constant of the class `other` first, and each constant
of the class `boolean` that the search with the types read has the name of one that the search
read. -/
theorem sharedNames_isEmpty_iff (first reached widened : List SharedDefinition) :
    (sharedNames first reached widened).isEmpty = true ↔
      ((∀ definition ∈ reached, definition.class ≠ .boolean) ∧
        ∀ definition ∈ first, definition.class ≠ .other) ∧
        ∀ definition ∈ widened, definition.class = .boolean →
          ∃ other ∈ reached, other.class = .boolean ∧ other.name = definition.name := by
  rw [SharedNames.isEmpty, Bool.and_eq_true, Bool.and_eq_true, Array.isEmpty_iff,
    Array.isEmpty_iff, Array.isEmpty_iff, sharedNames_booleans_eq_empty_iff,
    sharedNames_others_eq_empty_iff, sharedNames_throughTypes_eq_empty_iff]

/-- What the collector observes of a function registered with `@[regula_decision]`: whether its
result type is `Decidable _`, the form whose every result carries a proof of the decided
proposition or of its negation; parsing cannot manufacture an unknown constructor. -/
inductive DecisionResult where
  /-- The result type is `Decidable _`: both directions hold by construction. -/
  | «decidable»
  /-- Any other result type: which direction is proved needs a registered decision contract. -/
  | «other»
  deriving Repr, DecidableEq, Inhabited

/-- The observation's text in reports (`decidable` or `other`); `parse?` reads it back
(`DecisionResult.roundtrip`). -/
def DecisionResult.spelling : DecisionResult → String
  | .«decidable» => "decidable"
  | .«other» => "other"

/-- The observation a text names; `none` for any text that is not a `spelling`
(`DecisionResult.canonical`). -/
@[regula_decision]
def DecisionResult.parse? : String → Option DecisionResult
  | "decidable" => some .«decidable»
  | "other" => some .«other»
  | _ => none

instance : ToString DecisionResult := ⟨DecisionResult.spelling⟩

/-- Every value survives its actual spelling parser. -/
@[simp] theorem DecisionResult.roundtrip (x : DecisionResult) : parse? x.spelling = some x := by
  cases x <;> rfl

/-- The parser accepts only the canonical spelling of its result. -/
theorem DecisionResult.canonical (s : String) (x : DecisionResult) (h : parse? s = some x) :
    x.spelling = s := by
  unfold parse? at h
  split at h <;> cases h <;> rfl

/-- The collector's observation of a registered proof-bearing executable contract.
The actual contract is checked during elaboration and admission; this record contains
its rendered requirement, its decision kind, any refusal and the names of the functions that its
specification shares with its implementation, not a proof of the predicate. -/
structure ExecutableContract where
  /-- The promised implementation constant; anonymous when the implementation is not a
  constant. -/
  root : Lean.Name
  /-- The requirement applied to the implementation, pretty-printed. -/
  requirement : String
  /-- Why the registration is refused, such as a noncomputable, `unsafe` or `partial`
  implementation, or a decision whose specification mentions its implementation; `none` when
  the collector found no problem. -/
  failure : Option String
  /-- The decision kind, when the requirement reduces to an application of
  `Regula.DecidesSoundly`, `Regula.DecidesCompletely` or `Regula.Decides`; `none` for every
  other requirement. -/
  kind : Option DecisionKind := none
  /-- For a decision registration whose statement the collector searched: the names of the
  functions that its specification shares with its implementation or its acceptance predicate
  (`sharedNames`). A function of the class `boolean` is named at any depth, and the registration
  is refused for it (`sharedTestFailure`). A function of the class `other` is named where the
  specification reaches it first. The kind does not establish that such a function is the
  intended one, and no registration is refused for it. Empty for every other registration. -/
  shared : SharedNames := {}
  deriving Repr, DecidableEq

/-- The recorded contract of a declaration: the collector's observation of its executable-contract
registration (`Declaration.executableContract`), and `none` without one. A mark a project writes
decides one of its refusals: the collector reads whether Lean marks the implementation
`noncomputable`. The decisions of RG1007 and RG1009 take this and no other field of the record,
so they read what a project writes only through it. -/
abbrev RecordedContract := Option ExecutableContract

/-- The recorded contract refusing nothing: no refusal (`failure`) and no shared test (`shared`).
The narrowing theorems compare a decision's answer on a recorded contract with its answer on this
(`DeclarationOK.neutral`, `OperationalOK.neutral`, `decidedImplementations_neutral`). -/
def RecordedContract.neutral (contract : RecordedContract) : RecordedContract :=
  contract.map fun c => { c with failure := none, shared := {} }

/-- The part of a declaration's record that is kernel-checked declaration data: a field of the
constant's `ConstantInfo`, which Lean's kernel admitted with the declaration, or a value computed
from such fields alone by a pure function. The gate replays the owned declarations of an
inspected environment (standard §7.3), so these are the fields that rest on the kernel and on
reading the environment's constant map, and on nothing an audited project can write beside the
declaration itself. -/
structure Declaration.KernelChecked where
  /-- The constant's name. -/
  name : Lean.Name
  /-- The kind of its `ConstantInfo`. -/
  kind : DeclarationKind
  /-- The `repr` of its kernel type expression. -/
  «type» : String
  /-- The constant is `unsafe`. -/
  isUnsafe : Bool
  /-- The constant is `partial`. -/
  isPartial : Bool
  /-- `partial` if the constant is partial, else `unsafe` if it is unsafe, else `none`. -/
  safety : Option Safety
  /-- The name is internal: some component begins with `_`. A function of the name. -/
  internal : Bool
  /-- The name is a private name. A function of the name. -/
  «private» : Bool
  /-- For an `_unsafe_rec` helper, the name of the definition it implements
  (`Compiler.isUnsafeRecName?`). A function of the name: it selects a base and shows nothing
  about it. -/
  unsafeRecBase : Option Lean.Name
  /-- The constant's universe parameters. -/
  levelParams : Array Lean.Name
  /-- The mutual block of a definition, theorem or opaque constant; empty for other kinds. -/
  all : Array Lean.Name
  /-- A definition's kernel reducibility hint; `none` for other kinds. -/
  hints : Option Reducibility
  /-- The constants its value mentions, sorted and without duplicates; empty without a value. -/
  valueConstants : Array Lean.Name
  /-- For an axiom whose name the `nativeEqTrue` scheme generates for a native tactic
  (`nativeAxiomOrigin?`) and whose type is `e = true` with `e` in that tactic's asserted shape
  (`decide p` for `native_decide` and `decide +native`, `verifyBVExpr expr cert` over the run's
  own auxiliary definitions for `bv_decide`): the `repr` of `e`, naming each of those auxiliary
  definitions by its unindexed base. Otherwise `none`. A function of the name and the type: the
  pure decision `NativeStatement.recognize?` decides the shape and returns `e`. -/
  nativeStatement : Option String
  deriving Repr, DecidableEq

/-- The part of a declaration's record that is a toolchain observation: the answer of Lean's
elaborator, compiler or kernel, or of the checker's own observing code, run at inspection. Each
field is an answer computed at inspection, and none is decided by a mark an audited project
writes. State a project writes can still enter an observation, and each field says how:
`prettyType` and `isProp` are Lean's own answers, which read the notations and the reducibility
statuses in force; `nativeReplay` runs compiled code; and what a project writes selects which
regeneration `unsafeRecRegenerated` reports, while the pure comparison and the kernel decide it.
The two observations that a project-written mark does decide, `executableContract` and
`tableOmissions`, are fields of `Declaration.ProjectWritten`. No policy theorem proves an
observation truthful. -/
structure Declaration.ToolchainObserved where
  /-- The module that declares the constant, as Lean's import record of the inspected
  environment gives it. Structural original Name for new diagnostic transport; absent legacy
  records are unsupported. -/
  «module» : Lean.Name
  /-- Its type as Lean's pretty-printer shows it. The printer reads the notations and
  unexpanders in force, which a project declares; the text is shown and decides nothing. -/
  prettyType : String
  /-- Its type is a proposition (`Meta.isProp`). The reduction that decides it does not unfold
  an irreducible definition, so a project's reducibility attributes can make it answer `false`
  for a proposition, and cannot make it answer `true` for another type. -/
  isProp : Bool
  /-- For an `_unsafe_rec` helper inspected as a replay candidate: the route by which Lean's own
  recursion compiler, rerun on the values of the helper's group (each helper's calls to its group
  standing for the recursive calls), reproduced the observed base and every auxiliary definition it
  generated, up to compilation erasure (`Collect.unsafeRecRegeneration`): structural recursion, or
  well-founded recursion with every decreasing proof elided. It is recorded only where Lean's
  kernel also checked, for each helper of the group, the recursion equation of its base for the
  helper's value, with no axiom outside Standard-Logical (`Collect.recursionEquationChecked`).
  `none` when neither route did or an equation was not checked, and for every other declaration or
  inspection stage. What a project writes (termination arguments, reducibility statuses, matcher
  and equation records) selects which regeneration runs; the pure decision
  `Erasure.reproduces` and the kernel decide. -/
  unsafeRecRegenerated : Option RecursionOrigin
  /-- For a replay candidate with a statement: whether an independent native evaluation of
  `e` returned `true` (`false` also when the replay failed). The evaluation runs the compiled
  code of the definitions `e` mentions. The observing pass takes the recognition of the
  candidate (`NativeStatement.Recognition`): `e` with the proof that the decision returns it for
  that tactic, prefix and type. So it evaluates no other expression. -/
  nativeReplay : Option Bool
  /-- The axioms the constant transitively depends on, sorted and without duplicates: those it
  reaches in the kernel that replayed it (`KernelAxioms.axiomTable`), or, for an editor
  snapshot, which has no replayed kernel, those `collectAxioms` reports. -/
  axioms : Array Lean.Name
  deriving Repr, DecidableEq

/-- The text of the omissions of a declaration with the axioms `axioms`: the axioms Lean's
`collectAxioms` reports (`axioms` without the omitted ones), those the declaration reaches in the
replayed kernel, and the omitted ones. -/
def tableOmissionText (axioms omissions : Array Lean.Name) : String :=
  let (omitted, reported) := axioms.partition omissions.contains
  s!"collectAxioms {reported.toList}, replayed kernel {axioms.toList}; omitted: {omitted.toList}"

/-- The part of a declaration's record that is read from environment state an audited project
can write, or that such state decides: an environment extension's entry, an attribute, a
declaration range, and the two observations of the checker that read such marks directly
(`executableContract`, `tableOmissions`). Lean's own commands write this state for the
declarations they add, and a metaprogram of the audited project can write it for any
declaration. A decision that reads one of these fields rests on what the project recorded, so no
field here is evidence that a declaration is what the record says. -/
structure Declaration.ProjectWritten where
  /-- The constant is registered as a type-class instance. -/
  «instance» : Bool
  /-- Lean marks the constant `noncomputable`. -/
  «noncomputable» : Bool
  /-- The constant the compiler runs in its place, from `@[implemented_by]`. -/
  implementedBy : Option Lean.Name
  /-- The constant has an `@[extern]` implementation. -/
  «extern» : Bool
  /-- The constant is a structure projection function. -/
  projection : Bool
  /-- The constant is a `match` auxiliary function (a matcher). -/
  matcher : Bool
  /-- Lean reports the definition as recursive (`Meta.isRecursiveDefinition`, a tag Lean's
  recursion compilers write). -/
  recursive : Bool
  /-- Lean's declaration ranges as it recorded them, when it did: the raw evidence. Admission and
  finding locations read the admitted pair (`Declaration.ranges`), not this. -/
  recordedRanges : Option Ranges
  /-- The declaration Lean generated this one from, one step, as the environment records it
  (`Regula.Collect.generatedFrom?`): a constructor's inductive type, a projection's structure
  constructor, a recursor's or equation lemma's declaration, and so on; `none` when Lean did not
  generate it from another declaration. -/
  generatedFrom : Option Lean.Name
  /-- The collector's observation when the constant registers an executable contract: its type
  reduced to an `ExecutableContract`, with the refusals the collector finds. It is a field of this
  part because a mark a project writes decides one refusal: the collector reads whether Lean
  marks the implementation `noncomputable`. The requirement's text is pretty-printed with the
  notations in force. -/
  executableContract : Option ExecutableContract := none
  /-- For a constant registered with `@[regula_decision]`: whether its result type is
  `Decidable _`. `none` for a constant without that registration. The registration is the
  project's own statement that the function is a decision; the result type is read by
  reduction. -/
  decisionResult : Option DecisionResult := none
  /-- The axioms of `axioms` that Lean's `collectAxioms` does not report. Lean's module tables
  are environment state a project can write, and Lean's own computation of a table can omit an
  axiom. The checker reports these and decides on `axioms`; admission refuses a declaration for
  which `collectAxioms` reports an axiom outside `axioms`, so `axioms` without these is what
  `collectAxioms` reports. Empty for an editor snapshot. -/
  tableOmissions : Array Lean.Name := #[]
  deriving Repr, DecidableEq

/-- The part of a declaration's record that holds no field of `Declaration.ProjectWritten`: its
kernel-checked data and the toolchain's observations. A decision that takes this, and not the
whole `Declaration`, cannot name a field of `Declaration.ProjectWritten`: to read one it has to
change its signature. -/
structure Declaration.Inspected extends Declaration.KernelChecked, Declaration.ToolchainObserved
  deriving Repr, DecidableEq

/-- Complete Lean-semantic report for one owned constant. Each field is declared in the part
that says where its value comes from: kernel-checked declaration data
(`Declaration.KernelChecked`), a toolchain observation (`Declaration.ToolchainObserved`), or
environment state an audited project can write (`Declaration.ProjectWritten`). The classification
is of the source of each value. No theorem of this library proves an observation truthful. -/
structure Declaration extends Declaration.Inspected, Declaration.ProjectWritten
  deriving Repr, DecidableEq

/-- A declaration's record is read as its part without the project-written fields wherever a
decision takes only that part. Nothing is computed: the other part is dropped. -/
instance : Coe Declaration Declaration.Inspected := ⟨Declaration.toInspected⟩

/-- The inspected part is read as its kernel-checked data wherever a decision takes only that. -/
instance : Coe Declaration.Inspected Declaration.KernelChecked :=
  ⟨Declaration.Inspected.toKernelChecked⟩

/-- The inspected part is read as its toolchain observations wherever a decision takes only
those. -/
instance : Coe Declaration.Inspected Declaration.ToolchainObserved :=
  ⟨Declaration.Inspected.toToolchainObserved⟩

/-- What the decision requirement of RG1008 reads of a declaration's record, and nothing else: the
constant's name, kernel-checked declaration data, and the collector's observation of its
`@[regula_decision]` registration, which the project writes. -/
structure Declaration.Registration where
  /-- The constant's name (`Declaration.KernelChecked.name`). -/
  name : Lean.Name
  /-- For a constant registered with `@[regula_decision]`: whether its result type is
  `Decidable _`; `none` without the registration (`Declaration.ProjectWritten.decisionResult`). -/
  decisionResult : Option DecisionResult
  deriving Repr, DecidableEq

/-- The registration part of a declaration's record: its name and its registration, each read
through the part that declares it, so a move of either field to another part fails here. -/
def Declaration.registration (d : Declaration) : Declaration.Registration :=
  ⟨d.toInspected.toKernelChecked.name, d.toProjectWritten.decisionResult⟩

/-- The name of the registration part is the name of the record. -/
@[simp] theorem Declaration.registration_name (d : Declaration) :
    d.registration.name = d.name := rfl

/-- The registration of the registration part is the registration of the record. -/
@[simp] theorem Declaration.registration_decisionResult (d : Declaration) :
    d.registration.decisionResult = d.decisionResult := rfl

/-- A declaration's record is read as its registration part wherever a decision takes only that. -/
instance : Coe Declaration Declaration.Registration := ⟨Declaration.registration⟩

/-- What the role validators read of a declaration's record, and nothing else: the inspected part
(kernel-checked declaration data and toolchain observations), and the attribute and range marks
that the project writes: the replacement (`@[implemented_by]`), the `extern` mark and the recorded
declaration ranges. -/
structure Declaration.Role extends Declaration.Inspected where
  /-- The constant the compiler runs in its place (`Declaration.ProjectWritten.implementedBy`). -/
  implementedBy : Option Lean.Name
  /-- The constant has an `@[extern]` implementation (`Declaration.ProjectWritten.extern`). -/
  «extern» : Bool
  /-- Lean's declaration ranges as it recorded them (`Declaration.ProjectWritten.recordedRanges`).
  -/
  recordedRanges : Option Ranges
  deriving Repr, DecidableEq

/-- The role part of a declaration's record: the inspected part and the three marks, each read
through the part that declares it, so a move of a mark to another part fails here. -/
def Declaration.role (d : Declaration) : Declaration.Role :=
  { d.toInspected with
    implementedBy := d.toProjectWritten.implementedBy
    «extern» := d.toProjectWritten.extern
    recordedRanges := d.toProjectWritten.recordedRanges }

/-- The inspected part of the role part is the inspected part of the record. -/
@[simp] theorem Declaration.role_toInspected (d : Declaration) :
    d.role.toInspected = d.toInspected := rfl

/-- The replacement of the role part is the replacement of the record. -/
@[simp] theorem Declaration.role_implementedBy (d : Declaration) :
    d.role.implementedBy = d.implementedBy := rfl

/-- The `extern` mark of the role part is the mark of the record. -/
@[simp] theorem Declaration.role_extern (d : Declaration) : d.role.extern = d.extern := rfl

/-- The recorded ranges of the role part are the recorded ranges of the record. -/
@[simp] theorem Declaration.role_recordedRanges (d : Declaration) :
    d.role.recordedRanges = d.recordedRanges := rfl

/-- The role part with each project-written mark at its neutral value: no replacement, no `extern`
implementation and no recorded range. The narrowing theorems compare a validator's answer on a
record with its answer on this (`NativeTeachingOK.neutral`, `RecursiveHelperOK.neutral`). -/
def Declaration.Role.neutral (r : Declaration.Role) : Declaration.Role :=
  { r with implementedBy := none, «extern» := false, recordedRanges := none }

/-- The neutral form keeps the inspected part. -/
@[simp] theorem Declaration.Role.neutral_toInspected (r : Declaration.Role) :
    r.neutral.toInspected = r.toInspected := rfl

/-- The role parts of an inventory's records, in inventory order. -/
def roleRecords (ds : Array Declaration) : Array Declaration.Role :=
  ds.map (·.role)

/-- The role parts of an inventory are the role parts of its records. -/
theorem mem_roleRecords {ds : Array Declaration} {r : Declaration.Role} :
    r ∈ roleRecords ds ↔ ∃ d ∈ ds, d.role = r := by
  simp [roleRecords, Array.mem_map]

/-- The declaration's admitted ranges: the pair Lean recorded (`recordedRanges`) when its
selection range lies within its full range, and otherwise that full range as its own selection
range (`Ranges.admitted`). -/
def Declaration.ranges (d : Declaration) : Option Ranges := d.recordedRanges.map Ranges.admitted

/-- What the declaration decision reads of a declaration's record, and nothing else: the inspected
part (kernel-checked declaration data and toolchain observations) and the recorded contract,
whose refusals a mark the project writes can decide. -/
structure Declaration.Assessed extends Declaration.Inspected where
  /-- The recorded contract (`Declaration.ProjectWritten.executableContract`). -/
  executableContract : RecordedContract
  deriving Repr, DecidableEq

/-- The assessed part of a declaration's record: the inspected part and the recorded contract,
each read through the part that declares it, so a move of the contract to another part fails
here. -/
def Declaration.assessed (d : Declaration) : Declaration.Assessed :=
  { d.toInspected with executableContract := d.toProjectWritten.executableContract }

/-- The inspected part of the assessed part is the inspected part of the record. -/
@[simp] theorem Declaration.assessed_toInspected (d : Declaration) :
    d.assessed.toInspected = d.toInspected := rfl

/-- The recorded contract of the assessed part is the recorded contract of the record. -/
@[simp] theorem Declaration.assessed_executableContract (d : Declaration) :
    d.assessed.executableContract = d.executableContract := rfl

/-- A declaration's record is read as its assessed part wherever a decision takes only that. No
coercion leaves the assessed part: a requirement over a narrower part names the projection, so a
record reaches each narrower part along one path only. -/
instance : Coe Declaration Declaration.Assessed := ⟨Declaration.assessed⟩

/-- The assessed part with its recorded contract refusing nothing (`RecordedContract.neutral`).
The narrowing theorems compare a decision's answer on a record with its answer on this
(`DeclarationOK.neutral`, `OperationalOK.neutral`). -/
def Declaration.Assessed.neutral (d : Declaration.Assessed) : Declaration.Assessed :=
  { d with executableContract := RecordedContract.neutral d.executableContract }

/-- The neutral form keeps the inspected part. -/
@[simp] theorem Declaration.Assessed.neutral_toInspected (d : Declaration.Assessed) :
    d.neutral.toInspected = d.toInspected := rfl

/-- The roots of the library packages the Lean toolchain ships as its own code: `Init`, `Std`
and `Lean`. A module under one of them is toolchain code only with an admitted origin
(`ToolchainOrigin`); the name alone never makes it so. -/
def ToolchainRoot (root : Lean.Name) : Prop := root = `Init ∨ root = `Std ∨ root = `Lean

instance : DecidablePred ToolchainRoot := fun _ => by unfold ToolchainRoot; infer_instance

/-- Origin observations are admitted only when the resolved and expected canonical paths agree
for a module under a toolchain root (`ToolchainRoot`), whatever the module's name. That the
paths are the module's loaded `.olean` and its copy in the pinned toolchain's library, and so
identify the toolchain's own artifact, is the probe's filesystem observation, not a property
of this type. -/
structure ToolchainOrigin where
  /-- The module that declares the toolchain-owned boundary. -/
  moduleName : Lean.Name
  /-- The canonical path of the `.olean` file the module was loaded from. -/
  actual : String
  /-- The canonical path of that module's `.olean` in the toolchain's library directory. -/
  expected : String
  /-- The module is under `Init`, `Std` or `Lean`. -/
  toolchainModule : ToolchainRoot moduleName.getRoot
  /-- The resolved path is not empty. -/
  nonempty : actual ≠ ""
  /-- The resolved and expected paths are the same text. -/
  agrees : actual = expected
  deriving Repr, DecidableEq

/-- Admit an origin observation: an error unless the module is under `Init`, `Std` or `Lean`
and `actual` is nonempty and equal to `expected` (`toolchainOrigin_roundtrip`). -/
@[regula_decision]
def admitToolchainOrigin (moduleName : Lean.Name) (actual expected : String) :
    Except String ToolchainOrigin :=
  if hm : ToolchainRoot moduleName.getRoot then
    if hn : actual ≠ "" then
      if he : actual = expected then .ok ⟨moduleName, actual, expected, hm, hn, he⟩
      else .error "toolchain origin mismatch"
    else .error "empty toolchain origin"
  else .error "toolchain module is not under Init, Std or Lean"

/-- Checked replacement equality and an admitted opaque body have different meanings. -/
inductive CheckedEvidence : BoundaryKind → Type where
  /-- A runtime replacement with checked correspondence, described by `detail`. -/
  | replacement (detail : String) : CheckedEvidence .runtimeReplacement
  /-- A compiler simplification with checked correspondence, described by `detail`. -/
  | simplification (detail : String) : CheckedEvidence .compilerSimplification
  /-- An opaque constant executed through its kernel-checked body. -/
  | opaqueBody : CheckedEvidence .opaqueComputation
  deriving Repr, DecidableEq

/-- Trusted evidence by kind. A native-runtime `extern` always carries the admitted origin of
its toolchain module. A runtime replacement or an unsafe or partial computation may carry one,
which the probe attaches exactly when the declaring module has an admitted toolchain origin;
without one it is the project's or a dependency's. No other kind can carry one: a compiler
simplification is registered by its equality's module, an `external` is by definition outside
the toolchain, the probe reports an opaque constant as checked, unresolved, or through its
partial helper, and a compiler-trusting proof axiom is the project's use of the compiler. -/
def TrustedEvidence : BoundaryKind → Type
  | .nativeRuntime => ToolchainOrigin
  | .runtimeReplacement | .unsafeComputation | .partialComputation => Option ToolchainOrigin
  | .compilerSimplification | .external | .opaqueComputation | .compilerTrustedProof => Unit

/-- The kinds whose trusted evidence can carry a toolchain origin (`TrustedEvidence`): a
runtime replacement, a native-runtime `extern`, and unsafe or partial computation. -/
def BoundaryKind.toolchainOwnable : BoundaryKind → Bool
  | .runtimeReplacement | .nativeRuntime | .unsafeComputation | .partialComputation => true
  | .compilerSimplification | .external | .opaqueComputation | .compilerTrustedProof => false

instance (k : BoundaryKind) : Repr (TrustedEvidence k) := by cases k <;> dsimp
    [TrustedEvidence] <;> infer_instance
instance (k : BoundaryKind) : DecidableEq (TrustedEvidence k) := by cases k <;> dsimp
    [TrustedEvidence] <;> infer_instance

/-- Invalid combinations such as checked external code are unrepresentable. -/
inductive BoundaryEvidence (kind : BoundaryKind) where
  /-- Checked evidence of a kind that admits it. -/
  | checked (evidence : CheckedEvidence kind)
  /-- A trusted boundary, with an optional detail and the toolchain origin its kind admits. -/
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

/-- The admitted toolchain origin of a toolchain-owned trusted boundary; `none` for any other
evidence. Such a boundary is trusted (`correspondence_of_toolchainOrigin`). -/
def BoundaryEvidence.toolchainOrigin? {k : BoundaryKind} (e : BoundaryEvidence k) :
    Option ToolchainOrigin :=
  match k, e with
  | .nativeRuntime, .trusted _ origin => some origin
  | .runtimeReplacement, .trusted _ origin => origin
  | .unsafeComputation, .trusted _ origin => origin
  | .partialComputation, .trusted _ origin => origin
  | _, _ => none

/-- A toolchain-owned boundary is trusted: never checked, never unresolved. -/
theorem BoundaryEvidence.correspondence_of_toolchainOrigin {k : BoundaryKind}
    {e : BoundaryEvidence k} {o : ToolchainOrigin} (h : e.toolchainOrigin? = some o) :
    e.correspondence = .trusted := by
  cases e with
  | trusted => rfl
  | checked evidence => cases evidence <;> cases h
  | unresolved => cases k <;> cases h

/-- Only an ownable kind can be toolchain-owned. -/
theorem BoundaryEvidence.toolchainOwnable_of_toolchainOrigin {k : BoundaryKind}
    {e : BoundaryEvidence k} {o : ToolchainOrigin} (h : e.toolchainOrigin? = some o) :
    k.toolchainOwnable = true := by
  cases e with
  | trusted => cases k <;> first | rfl | cases h
  | checked evidence => cases evidence <;> cases h
  | unresolved => cases k <;> cases h

/-- A resolved native-runtime boundary is toolchain-owned. -/
theorem BoundaryEvidence.toolchainOrigin_of_nativeRuntime {e : BoundaryEvidence .nativeRuntime}
    (h : e.correspondence ≠ .unresolved) : e.toolchainOrigin?.isSome := by
  cases e with
  | checked evidence => cases evidence
  | trusted => rfl
  | unresolved => exact absurd rfl h

/-- Raw candidate construction may discard incompatible observation fields.
Operational/wire callers requiring field preservation must use `admitBoundaryEvidence`.
A candidate is an indexed value, not a receipt for the supplied raw fields. -/
def boundaryEvidenceCandidate (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option ToolchainOrigin) : Except String
    (BoundaryEvidence kind) :=
  match state with
  | .unresolved => .ok (.unresolved detail)
  | .trusted => match kind with
    | .nativeRuntime => match origin with
      | some o => .ok (.trusted detail o)
      | none => .error "missing native-runtime origin"
    | .runtimeReplacement => .ok (.trusted detail origin)
    | .unsafeComputation => .ok (.trusted detail origin)
    | .partialComputation => .ok (.trusted detail origin)
    | .compilerSimplification | .external | .opaqueComputation | .compilerTrustedProof =>
        .ok (.trusted detail ())
  | .checked => match kind, detail with
    | .runtimeReplacement, some s => .ok (.checked (.replacement s))
    | .compilerSimplification, some s => .ok (.checked (.simplification s))
    | .opaqueComputation, some "kernel-checked-body" => .ok (.checked .opaqueBody)
    | _, _ => .error "invalid checked boundary evidence"

/-- Admission retains every supplied evidence field or refuses the observation. -/
@[regula_decision]
def admitBoundaryEvidence (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option ToolchainOrigin) : Except String
    (BoundaryEvidence kind) :=
  match boundaryEvidenceCandidate kind state detail origin with
  | .error error => .error error
  | .ok e =>
    if e.correspondence = state ∧ e.detail = detail ∧ e.toolchainOrigin? = origin then .ok e
    else .error "boundary evidence contains incompatible fields"

private theorem boundaryEvidenceCandidate_roundtrip {kind : BoundaryKind}
    (e : BoundaryEvidence kind) :
    boundaryEvidenceCandidate kind e.correspondence e.detail e.toolchainOrigin? = .ok e := by
  cases e with
  | checked evidence => cases evidence <;> rfl
  | trusted detail origin => cases kind <;> rfl
  | unresolved detail => cases kind <;> rfl

/-- Successful admission preserves every evidence projection for all raw inputs. -/
theorem boundaryEvidence_admission_preserves (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option ToolchainOrigin) (e : BoundaryEvidence kind)
    (h : admitBoundaryEvidence kind state detail origin = .ok e) :
    e.correspondence = state ∧ e.detail = detail ∧ e.toolchainOrigin? = origin := by
  unfold admitBoundaryEvidence at h
  split at h
  next => cases h
  next candidate _ =>
    split at h
    next valid => cases h; exact valid
    next => cases h

/-- Every inhabitant of the indexed evidence domain survives its actual admission API. -/
theorem boundaryEvidence_roundtrip {kind : BoundaryKind} (e : BoundaryEvidence kind) :
    admitBoundaryEvidence kind e.correspondence e.detail e.toolchainOrigin? = .ok e := by
  unfold admitBoundaryEvidence
  rw [boundaryEvidenceCandidate_roundtrip]
  simp

/-- The raw fields `admitBoundaryEvidence` admits for a kind: they are the correspondence, detail
and toolchain origin of some evidence of that kind. It is stated without
`admitBoundaryEvidence`. -/
def BoundaryFieldsOK (kind : BoundaryKind) (state : Correspondence) (detail : Option String)
    (origin : Option ToolchainOrigin) : Prop :=
  ∃ e : BoundaryEvidence kind,
    e.correspondence = state ∧ e.detail = detail ∧ e.toolchainOrigin? = origin

/-- Boundary-evidence admission succeeds exactly for the fields of some evidence of the kind
(`boundaryEvidence_admission_preserves`, `boundaryEvidence_roundtrip`). -/
theorem admitBoundaryEvidence_isOk_iff (kind : BoundaryKind) (state : Correspondence)
    (detail : Option String) (origin : Option ToolchainOrigin) :
    (admitBoundaryEvidence kind state detail origin).isOk = true ↔
      BoundaryFieldsOK kind state detail origin := by
  constructor
  · intro accepted
    cases admitted : admitBoundaryEvidence kind state detail origin with
    | ok e => exact ⟨e, boundaryEvidence_admission_preserves kind state detail origin e admitted⟩
    | error _ => rw [admitted] at accepted; cases accepted
  · rintro ⟨e, rfl, rfl, rfl⟩
    rw [boundaryEvidence_roundtrip]
    rfl

/-- The arguments of `admitBoundaryEvidence`, as the fields of one structure, in the order of
the arguments. -/
structure BoundaryFields where
  /-- The kind of the boundary. -/
  kind : BoundaryKind
  /-- The observed correspondence. -/
  state : Correspondence
  /-- The observed detail. -/
  detail : Option String
  /-- The observed toolchain origin. -/
  origin : Option ToolchainOrigin

/-- `admitBoundaryEvidence` accepts exactly the fields of some evidence of the kind
(`admitBoundaryEvidence_isOk_iff`): it accepts an unresolved external boundary and refuses a
trusted native-runtime boundary with no origin. The result type depends on the kind, so the
decision is of whether the result is a success (`Regula.Dependent.isOk`), on the structure of
the four arguments; that the admitted evidence has the supplied fields is
`boundaryEvidence_admission_preserves`. -/
theorem checked_admitBoundaryEvidence :
    Regula.ExecutableContract admitBoundaryEvidence (fun admit =>
      Regula.Decides (· = true)
        (fun input : BoundaryFields =>
          BoundaryFieldsOK input.kind input.state input.detail input.origin)
        (Regula.Dependent.isOk fun input =>
          admit input.kind input.state input.detail input.origin)) :=
  ⟨.of_iff (fun input =>
      admitBoundaryEvidence_isOk_iff input.kind input.state input.detail input.origin)
    ⟨⟨.external, .unresolved, none, none⟩,
      (admitBoundaryEvidence_isOk_iff .external .unresolved none none).mpr
        ⟨.unresolved none, rfl, rfl, rfl⟩⟩
    ⟨⟨.nativeRuntime, .trusted, none, none⟩, by decide⟩⟩

/-- Canonical toolchain-origin admission preserves its module and exact path observation. -/
theorem toolchainOrigin_roundtrip (o : ToolchainOrigin) :
    admitToolchainOrigin o.moduleName o.actual o.expected = .ok o := by
  cases o with
  | mk m a e hm hn he =>
    cases he
    simp [admitToolchainOrigin, hm, hn]

/-- The observed part of a boundary's record: the fields whose value the environment fixes for the
constant the record is made at, which are that constant, its module and whether that module is
owned. Authored marks and traversal through project-written edges decide which records exist. A
field that the data of a mark enters is project-written (`ExecutionBoundary.ProjectWritten`).
`Probe.observeNode` sets the name to the observed constant, the module to the environment's
attribution of it, and ownership to membership in the claim's owned modules. -/
structure ExecutionBoundary.ToolchainObserved where
  /-- The constant at the boundary. -/
  name : Lean.Name
  /-- The module that declares it. -/
  «module» : Lean.Name
  /-- The constant's module is one of the audited, owned modules. -/
  owned : Bool
  deriving Repr, DecidableEq

/-- The part of a boundary's record that marks an audited project writes can decide: its kind, its
evidence and the constant run in its place. `@[implemented_by]` and `@[extern]` decide the kind
where the constant has one of them. A constant whose type is an equality of two constants with the
same list of distinct universe parameters makes a `compiler-simplification` boundary, registered
with `@[csimp]` or not, and an attribute such as `@[simp]` makes Lean generate equation lemmas of
that shape. The constant's safety and value decide the other kinds. -/
structure ExecutionBoundary.ProjectWritten where
  /-- What kind of boundary it is. -/
  boundary : BoundaryKind
  /-- The correspondence evidence, of a form the kind admits. -/
  account : BoundaryEvidence boundary
  /-- For a runtime replacement or compiler simplification, the constant run in its place. -/
  replacement : Option Lean.Name
  deriving Repr, DecidableEq

/-- One boundary in the conservative compiler/source closure of an
executable root. `boundary` is one of `runtime-replacement`, `compiler-simplification`,
`native-runtime`,
`external`, `unsafe-computation`, `partial-computation`, `opaque-computation`,
or `compiler-trusted-proof`; `correspondence` is `checked`, `trusted`, or
`unresolved`. Each field the pass sets at one constant is declared in the part that says where its
value comes from. Its position and its callers are computed over the walk of the root, through
edges of the two parts, so they are fields of the boundary itself. -/
structure ExecutionBoundary extends ExecutionBoundary.ToolchainObserved,
    ExecutionBoundary.ProjectWritten where
  /-- The boundary's position in its root's boundary list. -/
  occurrence : Nat
  /-- The constants whose retained compiler IR calls this one directly, or names it as an
  initializer. -/
  compilerCallers : Array Lean.Name := #[]
  deriving Repr, DecidableEq

/-- Execution coverage for one owned executable root: every boundary its
conservative compiler/source closure reaches, plus every dependency path the
analysis could not resolve. -/
def ExecutionBoundary.correspondence (b : ExecutionBoundary) : Correspondence :=
    b.account.correspondence

/-- The detail text of the boundary's evidence. -/
def ExecutionBoundary.evidence (b : ExecutionBoundary) : Option String := b.account.detail

/-- The admitted origin of the boundary's module when the toolchain owns the boundary, which
then belongs to the toolchain's trusted base rather than to the project or a dependency;
`none` otherwise (`BoundaryEvidence.toolchainOrigin?`). -/
def ExecutionBoundary.toolchainOrigin? (b : ExecutionBoundary) : Option ToolchainOrigin :=
  b.account.toolchainOrigin?

/-- The boundary claims toolchain ownership: it is a native-runtime `extern` or carries a
toolchain origin, so its module needs the origin observation (`OriginOK`). -/
def ExecutionBoundary.claimsToolchain (b : ExecutionBoundary) : Bool :=
  b.boundary == .nativeRuntime || b.toolchainOrigin?.isSome

/-- The boundary is a runtime replacement the toolchain does not own, so its module's source
history must record its replacement (`HistoryOK`). Which implementation a toolchain replacement
runs belongs to the toolchain's trusted base, with no history obligation. -/
def ExecutionBoundary.needsHistory (b : ExecutionBoundary) : Bool :=
  b.boundary == .runtimeReplacement && b.toolchainOrigin?.isNone

/-- The boundary claims toolchain ownership, as a proposition: it is a native-runtime `extern`
or carries a toolchain origin. `ExecutionBoundary.claimsToolchain` decides it
(`ExecutionBoundary.claimsToolchain_iff`). -/
def ExecutionBoundary.ClaimsToolchain (b : ExecutionBoundary) : Prop :=
  b.boundary = .nativeRuntime ∨ ∃ origin, b.toolchainOrigin? = some origin

/-- The executed test accepts exactly the boundaries that claim toolchain ownership. -/
theorem ExecutionBoundary.claimsToolchain_iff (b : ExecutionBoundary) :
    b.claimsToolchain = true ↔ b.ClaimsToolchain := by
  simp [ExecutionBoundary.claimsToolchain, ExecutionBoundary.ClaimsToolchain,
    Option.isSome_iff_exists]

instance (b : ExecutionBoundary) : Decidable b.ClaimsToolchain :=
  decidable_of_iff _ b.claimsToolchain_iff

/-- The boundary is a runtime replacement the toolchain does not own, as a proposition.
`ExecutionBoundary.needsHistory` decides it (`ExecutionBoundary.needsHistory_iff`). -/
def ExecutionBoundary.NeedsHistory (b : ExecutionBoundary) : Prop :=
  b.boundary = .runtimeReplacement ∧ b.toolchainOrigin? = none

/-- The executed test accepts exactly the replacements that the toolchain does not own. -/
theorem ExecutionBoundary.needsHistory_iff (b : ExecutionBoundary) :
    b.needsHistory = true ↔ b.NeedsHistory := by
  simp [ExecutionBoundary.needsHistory, ExecutionBoundary.NeedsHistory]

instance (b : ExecutionBoundary) : Decidable b.NeedsHistory :=
  decidable_of_iff _ b.needsHistory_iff

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
active simplifications are used for cycle detection, not claimed compiler calls. Every field is
computed over the names that the walk reached, through the edges of the two parts of their records
(`ExecutionWalk.NodeRecord`), so the closure has no observed or project-written part. Each edge set
is named for the record field whose targets it copies. -/
structure ExecutionClosure where
  /-- Every name the walk reached, sorted and without duplicates. -/
  nodes : Array Lean.Name
  /-- Each name's first visit, in walk order. -/
  visits : Array ExecutionVisit
  /-- From a constant to each constant its value mentions, where the walk follows the value. -/
  logicalEdges : Array (Lean.Name × Lean.Name) := #[]
  /-- From a constant to the target of each simplification candidate: a constant whose type is an
  equality of two constants with the same list of distinct universe parameters, registered with
  `@[csimp]` or not. -/
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

/-- The observed part of a root's account: the fields whose value the environment fixes for the
constant the account is made at, which are that constant and its module. Authored marks and
traversal through project-written edges decide which records exist. A field that the data of a mark
enters is project-written, as a boundary's kind and replacement. `Probe.environmentReport` makes a
root record for each name of `executableRoots` (each eligible owned definition and each `@[init]` or
`@[builtin_init]` action) and each root of a registered contract with no refusal, with the name set
to that constant and the module to the environment's attribution of it. -/
structure ExecutionRoot.ToolchainObserved where
  /-- The root constant. -/
  name : Lean.Name
  /-- Its declaring module. -/
  «module» : Lean.Name
  deriving Repr, DecidableEq

/-- The execution account of one owned executable root: the boundaries and unresolved paths its
closure reaches, its compiled edges and the closure itself. Its name and module are in the observed
part (`ExecutionRoot.ToolchainObserved`). The other fields are computed over the walk of the root,
through the edges of the two parts of the records it reads, so they are fields of the account
itself. -/
structure ExecutionRoot extends ExecutionRoot.ToolchainObserved where
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
  /-- The legacy compiler capability observed in an isolated, origin-checked Core environment. -/
  compilerCapability : Compiler.LegacyCompilerTrust
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
@[regula_decision]
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

/-- One constant a command added to the environment. Its fields are fields of the constant's
`ConstantInfo` in the fresh elaboration's environment, or a pure function of such fields. Lean's
kernel admitted that constant only if the source left kernel checking on, and the transcript does
not replay it. -/
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

/-- One command that added constants: what it added and whether it declares an axiom, the
provenance a native-proof axiom's authentication reads (`NativeTeachingOK`). Each field is the
frontend's observation of the fresh elaboration. -/
structure Command where
  /-- The names of the constants the command added. -/
  added : Array Lean.Name
  /-- A record of each added constant. -/
  addedDeclarations : Array AddedDeclaration
  /-- Whether the command's syntax, a command its information tree records, or the output of a
  macro expansion there contains an `axiom` declaration node, quoted syntax included. It is read
  from syntax, so it holds even when elaborating that declaration failed. -/
  declaresAxiom : Bool
  deriving Repr, DecidableEq

/-- The part of a transcript that the toolchain observes: the module and source file that Lake
resolves, the elaborating toolchain's identity, the header's imports as Lean's parser reads them,
and each command as the frontend records it. The project's configuration and source decide what
these observe, and no field here is a mark the project writes beside them. -/
structure Transcript.ToolchainObserved where
  /-- The elaborated module. -/
  «module» : Lean.Name
  /-- The path of its source file. -/
  source : String
  /-- The Lean version string of the elaborating toolchain. -/
  leanVersion : String
  /-- The Git commit of the elaborating toolchain. -/
  leanGitHash : String
  /-- The source header's imports. -/
  imports : Array ImportRecord
  /-- Each command that added constants, in source order. -/
  commands : Array Command
  /-- Evaluators under which the replacement history
  (`Transcript.ProjectWritten.runtimeReplacements`) cannot be certified, such as `run_cmd` or a
  source-local elaborator. -/
  replacementHistoryUnsupported : Array String := #[]
  deriving Repr, DecidableEq

/-- The part of a transcript that the project writes: the source text it elaborated, and the
runtime replacements (`@[implemented_by]`) that the source's commands recorded. A decision that
reads one of these fields rests on what the project wrote. -/
structure Transcript.ProjectWritten where
  /-- The source's size in UTF-8 bytes. -/
  sourceBytes : Nat
  /-- The exact source text that was elaborated. -/
  sourceContent : String
  /-- Every `@[implemented_by]` pair (reference, target) seen in any command's environment, when
  replacement history was requested. -/
  runtimeReplacements : Array (Lean.Name × Lean.Name) := #[]
  deriving Repr, DecidableEq

/-- The record of one fresh frontend elaboration of a module's exact source. Each field is declared
in the part that says where its value comes from. -/
structure Transcript extends Transcript.ToolchainObserved, Transcript.ProjectWritten
  deriving Repr, DecidableEq

/-- The observed parts of transcripts, in order: what the role validators read of them. -/
def observedTranscripts (ts : Array Transcript) : Array Transcript.ToolchainObserved :=
  ts.map (·.toToolchainObserved)

end Frontend

/-! ## Spelling parsers as decisions

Each closed vocabulary's parser accepts exactly the spellings of its values: its `roundtrip` and
`canonical` theorems, registered as a two-way decision (`Regula.Decides.of_roundtrip`) with one
value's spelling as the accepted input and the empty text as the refused one. Which value a
spelling is read as is the `roundtrip` theorem; the kind states only the accepted set. -/

/-- `DeclarationKind.parse?` accepts exactly the spellings. -/
theorem DeclarationKind.checked_parse : Regula.ExecutableContract DeclarationKind.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : DeclarationKind, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«axiom» (unwritten := "") rfl⟩

/-- `BoundaryKind.parse?` accepts exactly the spellings. -/
theorem BoundaryKind.checked_parse : Regula.ExecutableContract BoundaryKind.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : BoundaryKind, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«runtimeReplacement» (unwritten := "") rfl⟩

/-- `Correspondence.parse?` accepts exactly the spellings. -/
theorem Correspondence.checked_parse : Regula.ExecutableContract Correspondence.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : Correspondence, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«checked» (unwritten := "") rfl⟩

/-- `FoundationClass.parse?` accepts exactly the spellings. -/
theorem FoundationClass.checked_parse : Regula.ExecutableContract FoundationClass.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : FoundationClass, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«kernelOnly» (unwritten := "") rfl⟩

/-- `ConformingProfile.parse?` accepts exactly the spellings. -/
theorem ConformingProfile.checked_parse : Regula.ExecutableContract ConformingProfile.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : ConformingProfile, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«kernelOnly» (unwritten := "") rfl⟩

/-- `ExecutionClaim.parse?` accepts exactly the spellings. -/
theorem ExecutionClaim.checked_parse : Regula.ExecutableContract ExecutionClaim.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : ExecutionClaim, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«report» (unwritten := "") rfl⟩

/-- `EvidenceMode.parse?` accepts exactly the spellings. -/
theorem EvidenceMode.checked_parse : Regula.ExecutableContract EvidenceMode.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : EvidenceMode, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«editorSnapshot» (unwritten := "") rfl⟩

/-- `Safety.parse?` accepts exactly the spellings. -/
theorem Safety.checked_parse : Regula.ExecutableContract Safety.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : Safety, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«unsafe» (unwritten := "") rfl⟩

/-- `Reducibility.parse?` accepts exactly the spellings. -/
theorem Reducibility.checked_parse : Regula.ExecutableContract Reducibility.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : Reducibility, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«opaque» (unwritten := "") rfl⟩

/-- `RecursionOrigin.parse?` accepts exactly the spellings. -/
theorem RecursionOrigin.checked_parse : Regula.ExecutableContract RecursionOrigin.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : RecursionOrigin, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«structural» (unwritten := "") rfl⟩

/-- `DecisionKind.parse?` accepts exactly the spellings. -/
theorem DecisionKind.checked_parse : Regula.ExecutableContract DecisionKind.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : DecisionKind, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«sound» (unwritten := "") rfl⟩

/-- `DecisionResult.parse?` accepts exactly the spellings. -/
theorem DecisionResult.checked_parse : Regula.ExecutableContract DecisionResult.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : DecisionResult, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .«decidable» (unwritten := "") rfl⟩

/-- `EvaluatorRole.parse?` accepts exactly the spellings. -/
theorem EvaluatorRole.checked_parse : Regula.ExecutableContract EvaluatorRole.parse?
    (Regula.Decides (·.isSome = true) fun text => ∃ x : EvaluatorRole, text = x.spelling) :=
  ⟨.of_roundtrip roundtrip canonical .command (unwritten := "") rfl⟩

/-- `DecisionKind.ofStructureName?` accepts exactly the three structures' names
(`DecisionKind.ofStructureName?_eq_some_iff`): the collector reads a registration's kind with
it, so this is the registered decision behind "a head constant is read as a kind exactly when it
is that kind's structure". -/
theorem DecisionKind.checked_ofStructureName :
    Regula.ExecutableContract DecisionKind.ofStructureName?
      (Regula.Decides (·.isSome = true) fun name =>
        ∃ kind : DecisionKind, name = kind.structureName) :=
  ⟨.of_roundtrip (fun kind => (ofStructureName?_eq_some_iff _ kind).mpr rfl)
    (fun name kind read => ((ofStructureName?_eq_some_iff name kind).mp read).symm)
    .«sound» (unwritten := .anonymous) rfl⟩

/-- `FieldPacking.covers` accepts exactly the packings that cover every argument
(`FieldPacking.covers_iff`): the collector reads a field application with it. It accepts the two
fields, in order, of a type with one constructor and no index, and refuses the one field of a
type with one constructor and an index, whose values are only some of the field tuples. -/
theorem FieldPacking.checked_covers :
    Regula.ExecutableContract FieldPacking.covers
      (Regula.Decides (· = true) FieldPacking.Covers) :=
  ⟨.of_iff covers_iff ⟨⟨1, 0, 2, [some 0, some 1]⟩, by decide⟩
    ⟨⟨1, 1, 1, [some 0]⟩, by decide⟩⟩

/-- The decision the collector makes of a decided function is exact
(`DecidedFunction.covers_iff`): the collector refuses a decision registration unless it holds.
It accepts the implementation's constant itself when no result takes an argument, and refuses
that constant when a result takes one more argument, which is a kind about a partially applied
implementation. -/
theorem DecidedFunction.checked_covers :
    Regula.ExecutableContract DecidedFunction.covers
      (Regula.Decides (· = true) DecidedFunction.Covers) :=
  ⟨.of_iff covers_iff ⟨⟨none, 0⟩, by decide⟩ ⟨⟨none, 1⟩, by decide⟩⟩

end RegulaPolicy
