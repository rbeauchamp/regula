module

public import RegulaPolicy.Foundation

/-! Declaration-policy meaning over observations. These predicates state membership,
safety, and recorded contract obligations independently of decision outputs. Extraction
and the truth of the observed contract/replay fields remain operational boundaries. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)

/-- Compiler trust consists of the three pinned compiler axioms and inventory-validated
native proof roles. This is separate from the permitted logical foundations. -/
def CompilerAxiom (native : Array Name) (n : Name) : Prop :=
  n = `Lean.trustCompiler ∨ n = `Lean.ofReduceBool ∨ n = `Lean.ofReduceNat ∨ n ∈ native
instance (native : Array Name) (n : Name) : Decidable (CompilerAxiom native n) := by
  unfold CompilerAxiom; infer_instance

/-- Every transitive dependency has a known logical or compiler-trusting classification. -/
def KnownDependencies (d : Declaration) (native : Array Name) : Prop :=
  ∀ n ∈ d.axioms, Permitted .standardLogical n ∨ CompilerAxiom native n
instance (d : Declaration) (native : Array Name) : Decidable (KnownDependencies d native) := by
  unfold KnownDependencies; infer_instance

/-- Authored unsafe/partial code is refused; the only data-level exception is an
inventory-validated recursive helper. The public theorem substitutes authenticated roles. -/
def SafetyOK (d : Declaration) (helpers : Array Name) : Prop :=
  (d.isUnsafe = false ∧ d.isPartial = false) ∨ d.name ∈ helpers
instance (d : Declaration) (helpers : Array Name) : Decidable (SafetyOK d helpers) := by
  unfold SafetyOK; infer_instance

/-- Each recorded contract inspection completed without a failure. Its exact proposition
and implementation were checked by Probe and owned logical admission, not by these strings. -/
def ContractOK (d : Declaration) : Prop := ∀ c ∈ d.executableContract, c.failure = none
instance (d : Declaration) : Decidable (ContractOK d) := by
  unfold ContractOK; infer_instance

/-- Teaching may retain compiler trust; other inspections cannot. -/
def CompilerPolicyOK (d : Declaration) (request : InspectionRequest) (native : Array Name) : Prop :=
  request = .teaching ∨ ∀ n ∈ d.axioms, ¬ CompilerAxiom native n
instance (d : Declaration) (r : InspectionRequest) (native : Array Name) :
    Decidable (CompilerPolicyOK d r native) := by unfold CompilerPolicyOK; infer_instance

/-- Only an explicitly conforming request imposes a positive profile bound. Compiler
members are separately refused by CompilerPolicyOK for every conforming request. -/
def ProfileOK (d : Declaration) (request : InspectionRequest) (native : Array Name) : Prop :=
  match request with
  | .conforming p => ∀ n ∈ d.axioms, CompilerAxiom native n ∨ Permitted p n
  | _ => True
instance (d : Declaration) (r : InspectionRequest) (native : Array Name) :
    Decidable (ProfileOK d r native) := by cases r <;> unfold ProfileOK <;> infer_instance

/-- Inspection success. An owned axiom has only the independently authenticated teaching
case; positive conformance always requires a non-axiom and all remaining conjuncts. -/
def DeclarationOK (d : Declaration) (request : InspectionRequest)
    (native helpers : Array Name) : Prop :=
  (d.kind = .«axiom» ∧ d.name ∈ native ∧ request = .teaching) ∨
  (d.kind ≠ .«axiom» ∧ `sorryAx ∉ d.axioms ∧ KnownDependencies d native ∧
    SafetyOK d helpers ∧ CompilerPolicyOK d request native ∧ ContractOK d ∧
    ProfileOK d request native)

/-- Positive logical foundation: no project axiom, hole, unknown or compiler axiom;
the selected permitted set contains every observed transitive dependency. -/
def FoundationOK (d : Declaration) (p : ConformingProfile) : Prop :=
  d.kind ≠ .«axiom» ∧ ContainsFoundation p d.axioms

/-- Exact six-way classification. Forbidden classes precede logical profiles; logical
classes describe observed set containment, never alternative proofs. -/
def ClassificationOK (axioms native : Array Name) (label : FoundationClass) : Prop :=
  let hole := `sorryAx ∈ axioms
  let known := ∀ n ∈ axioms, Permitted .standardLogical n ∨ CompilerAxiom native n
  let compiler := ∃ n ∈ axioms, CompilerAxiom native n
  match label with
  | .hole => hole
  | .unknownAxiom => ¬ hole ∧ ¬ known
  | .compilerTrusting => ¬ hole ∧ known ∧ compiler
  | .kernelOnly => ¬ hole ∧ known ∧ ¬ compiler ∧ axioms = #[]
  | .choiceFree => ¬ hole ∧ known ∧ ¬ compiler ∧ axioms ≠ #[] ∧ ContainsFoundation .choiceFree axioms
  | .standardLogical => ¬ hole ∧ known ∧ ¬ compiler ∧ axioms ≠ #[] ∧ ¬ ContainsFoundation .choiceFree axioms

/-- An ordered requirement relation selects the first unsatisfied obligation. This is a
proposition about requirements and outcomes, not a second Boolean decision algorithm. -/
inductive OrderedDecision : List (DeclarationFailure × Prop) → Option DeclarationFailure → Prop where
  | done : OrderedDecision [] none
  | fail {reason requirement rest} : ¬ requirement → OrderedDecision ((reason, requirement) :: rest) (some reason)
  | next {reason requirement rest result} : requirement → OrderedDecision rest result →
      OrderedDecision ((reason, requirement) :: rest) result

@[simp] theorem orderedDecision_nil (result : Option DeclarationFailure) :
    OrderedDecision [] result ↔ result = none := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst result; exact .done

@[simp] theorem orderedDecision_cons (reason : DeclarationFailure) (requirement : Prop)
    (rest : List (DeclarationFailure × Prop)) (result : Option DeclarationFailure) :
    OrderedDecision ((reason, requirement) :: rest) result ↔
      (¬ requirement ∧ result = some reason) ∨ (requirement ∧ OrderedDecision rest result) := by
  constructor
  · intro h; cases h with
    | fail h => exact Or.inl ⟨h, rfl⟩
    | next h hr => exact Or.inr ⟨h, hr⟩
  · rintro (⟨h, rfl⟩ | ⟨h, hr⟩)
    · exact .fail h
    · exact .next h hr

/-- Ordered requirements have one outcome; no later failure can displace the first. -/
theorem OrderedDecision.unique {requirements : List (DeclarationFailure × Prop)}
    {a b : Option DeclarationFailure} (ha : OrderedDecision requirements a)
    (hb : OrderedDecision requirements b) : a = b := by
  induction ha with
  | done => cases hb; rfl
  | fail h =>
      cases hb with
      | fail _ => rfl
      | next hp _ => exact False.elim (h hp)
  | next h _ ih =>
      cases hb with
      | fail hn => exact False.elim (hn h)
      | next _ hr => exact ih hr

/-- Normative diagnostic priority. Owned axioms have only the authenticated teaching case;
other declarations must meet each obligation in this explicit order. -/
def declarationRequirements (d : Declaration) (r : InspectionRequest) (native helpers : Array Name) :
    List (DeclarationFailure × Prop) :=
  if d.kind = .«axiom» then
    [(.projectAxiom, d.name ∈ native), (.compilerTrusting, r = .teaching)]
  else
    [(.proofHole, `sorryAx ∉ d.axioms), (.unknownAxiom, KnownDependencies d native),
     (.escapeHatch, SafetyOK d helpers), (.compilerTrusting, CompilerPolicyOK d r native),
     (.executableContract, ContractOK d), (.profileExceeded, ProfileOK d r native)]

end RegulaPolicy
