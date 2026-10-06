module

public import RegulaPolicy.Foundation

/-! # Declaration-policy specification

Declaration-policy meaning over observations. These predicates state membership,
safety, and recorded contract obligations independently of decision outputs. Extraction
and the truth of the observed contract/replay fields remain operational boundaries.

The requirements of a declaration's own record (`DeclarationOK` and its conjuncts,
`FoundationOK`, `declarationRequirements`) take `Declaration.Inspected`, the part of the record
that holds no field of `Declaration.ProjectWritten`, so none of them can name a field an audited
project writes. One can still depend on project-written state through an observation, as the
fields of `Declaration.ToolchainObserved` say: `ContractOK` reads `executableContract.failure`.
The decision requirement (`DecisionOK`) reads the project's own registration and takes the whole
record. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)

/-- Compiler trust consists of the legacy family when the selected compiler declares it,
and inventory-validated native proof roles, separately from the logical foundations. -/
def CompilerAxiom (native : Array Name) (n : Name) : Prop :=
  (Compiler.legacyCompilerTrust = .present ∧
    (n = `Lean.trustCompiler ∨ n = `Lean.ofReduceBool ∨ n = `Lean.ofReduceNat)) ∨ n ∈ native
instance (native : Array Name) (n : Name) : Decidable (CompilerAxiom native n) := by
  unfold CompilerAxiom; infer_instance

/-- On a compiler without the legacy family, only authenticated native roles can confer trust. -/
theorem compilerAxiom_absent (h : Compiler.legacyCompilerTrust = .absent)
    (native : Array Name) (n : Name) : CompilerAxiom native n ↔ n ∈ native := by
  simp [CompilerAxiom, h]

/-- Every transitive dependency has a known logical or compiler-trusting classification. -/
def KnownDependencies (d : Declaration.Inspected) (native : Array Name) : Prop :=
  ∀ n ∈ d.axioms, Permitted .standardLogical n ∨ CompilerAxiom native n
instance (d : Declaration.Inspected) (native : Array Name) :
    Decidable (KnownDependencies d native) := by
  unfold KnownDependencies; infer_instance

/-- Authored unsafe/partial code is refused; the data-level exceptions are inventory-validated
recursion and constructor-index helpers. The public theorem substitutes authenticated roles. -/
def SafetyOK (d : Declaration.Inspected) (helpers : Array Name) : Prop :=
  (d.isUnsafe = false ∧ d.isPartial = false) ∨ d.name ∈ helpers
instance (d : Declaration.Inspected) (helpers : Array Name) : Decidable (SafetyOK d helpers) := by
  unfold SafetyOK; infer_instance

/-- Each recorded contract inspection completed without a failure. Its exact proposition
and implementation were checked by Probe and owned logical admission, not by these strings. -/
def ContractOK (d : Declaration.Inspected) : Prop :=
  ∀ c ∈ d.executableContract, c.failure = none
instance (d : Declaration.Inspected) : Decidable (ContractOK d) := by
  unfold ContractOK; infer_instance

/-- `n` is the implementation a decision contract of the inventory decides: some declaration of
`ds` records an executable contract that states a decision kind, was not refused, and names `n`
as its implementation. -/
def DecisionRegistered (ds : Array Declaration) (n : Name) : Prop :=
  ∃ r ∈ ds, ∃ c ∈ r.executableContract, c.root = n ∧ c.kind.isSome = true ∧ c.failure = none

/-- A function registered as a decision (`@[regula_decision]`) states the direction it proves: its
result type is `Decidable _`, or it is among `decided`, the implementations the inventory's
decision contracts decide. A declaration without the registration has no such requirement; every
registered declaration has it, whatever else the record says of the declaration, so no other
observation waives it. The registration and the result type are the collector's observation
(`Declaration.decisionResult`). -/
def DecisionOK (d : Declaration) (decided : Array Name) : Prop :=
  d.decisionResult = some .«other» → d.name ∈ decided
instance (d : Declaration) (decided : Array Name) : Decidable (DecisionOK d decided) := by
  unfold DecisionOK; infer_instance

/-- Teaching may retain compiler trust; other inspections cannot. -/
def CompilerPolicyOK (d : Declaration.Inspected) (request : InspectionRequest)
    (native : Array Name) : Prop :=
  request = .teaching ∨ ∀ n ∈ d.axioms, ¬ CompilerAxiom native n
instance (d : Declaration.Inspected) (r : InspectionRequest) (native : Array Name) :
    Decidable (CompilerPolicyOK d r native) := by unfold CompilerPolicyOK; infer_instance

/-- Only an explicitly conforming request imposes a positive profile bound. Compiler
members are separately refused by CompilerPolicyOK for every conforming request. -/
def ProfileOK (d : Declaration.Inspected) (request : InspectionRequest) (native : Array Name) :
    Prop :=
  match request with
  | .conforming p => ∀ n ∈ d.axioms, CompilerAxiom native n ∨ Permitted p n
  | _ => True
instance (d : Declaration.Inspected) (r : InspectionRequest) (native : Array Name) :
    Decidable (ProfileOK d r native) := by cases r <;> unfold ProfileOK <;> infer_instance

/-- Inspection success. An owned axiom has only the independently authenticated teaching
case; positive conformance always requires a non-axiom and all remaining conjuncts. -/
def DeclarationOK (d : Declaration.Inspected) (request : InspectionRequest)
    (native helpers : Array Name) : Prop :=
  (d.kind = .«axiom» ∧ d.name ∈ native ∧ request = .teaching) ∨
  (d.kind ≠ .«axiom» ∧ `sorryAx ∉ d.axioms ∧ KnownDependencies d native ∧
    SafetyOK d helpers ∧ CompilerPolicyOK d request native ∧ ContractOK d ∧
    ProfileOK d request native)

/-- Positive logical foundation: no project axiom, hole, unknown or compiler axiom;
the selected permitted set contains every observed transitive dependency. -/
def FoundationOK (d : Declaration.Inspected) (p : ConformingProfile) : Prop :=
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
  | .choiceFree => ¬ hole ∧ known ∧ ¬ compiler ∧ axioms ≠ #[] ∧
                    ContainsFoundation .choiceFree axioms
  | .standardLogical => ¬ hole ∧ known ∧ ¬ compiler ∧ axioms ≠ #[] ∧
                         ¬ ContainsFoundation .choiceFree axioms

/-- An ordered requirement relation selects the first unsatisfied obligation. This is a
proposition about requirements and outcomes, not a second Boolean decision algorithm. -/
inductive OrderedDecision : List (DeclarationFailure × Prop) → Option DeclarationFailure →
    Prop where
  /-- With no requirement left, no failure is selected. -/
  | done : OrderedDecision [] none
  /-- An unmet first requirement selects its own failure reason. -/
  | fail {reason requirement rest} : ¬ requirement → OrderedDecision ((reason, requirement) :: rest)
      (some reason)
  /-- A met first requirement defers to the decision on the remaining requirements. -/
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
def declarationRequirements (d : Declaration.Inspected) (r : InspectionRequest)
    (native helpers : Array Name) :
    List (DeclarationFailure × Prop) :=
  if d.kind = .«axiom» then
    [(.projectAxiom, d.name ∈ native), (.compilerTrusting, r = .teaching)]
  else
    [(.proofHole, `sorryAx ∉ d.axioms), (.unknownAxiom, KnownDependencies d native),
     (.escapeHatch, SafetyOK d helpers), (.compilerTrusting, CompilerPolicyOK d r native),
     (.executableContract, ContractOK d), (.profileExceeded, ProfileOK d r native)]

/-- A requirement appended to an ordered list is decided only where every earlier one is met:
an earlier failure is the outcome whatever the appended requirement, and otherwise the outcome is
the appended requirement's own. -/
theorem orderedDecision_append_singleton (requirements : List (DeclarationFailure × Prop))
    (reason : DeclarationFailure) (requirement : Prop) (result : Option DeclarationFailure) :
    OrderedDecision (requirements ++ [(reason, requirement)]) result ↔
      (∃ earlier, OrderedDecision requirements (some earlier) ∧ result = some earlier) ∨
      (OrderedDecision requirements none ∧
        ((¬ requirement ∧ result = some reason) ∨ (requirement ∧ result = none))) := by
  induction requirements with
  | nil => simp
  | cons head rest ih =>
    obtain ⟨headReason, headRequirement⟩ := head
    simp only [List.cons_append, orderedDecision_cons, ih]
    constructor
    · rintro (⟨unmet, rfl⟩ | ⟨met, ⟨earlier, failed, rfl⟩ | ⟨passed, outcome⟩⟩)
      · exact Or.inl ⟨headReason, Or.inl ⟨unmet, rfl⟩, rfl⟩
      · exact Or.inl ⟨earlier, Or.inr ⟨met, failed⟩, rfl⟩
      · exact Or.inr ⟨Or.inr ⟨met, passed⟩, outcome⟩
    · rintro (⟨earlier, ⟨unmet, same⟩ | ⟨met, failed⟩, rfl⟩ | ⟨⟨_, impossible⟩ | ⟨met, passed⟩,
        outcome⟩)
      · exact Or.inl ⟨unmet, same⟩
      · exact Or.inr ⟨met, Or.inl ⟨earlier, failed, rfl⟩⟩
      · cases impossible
      · exact Or.inr ⟨met, Or.inr ⟨passed, outcome⟩⟩

/-- The inventory-bound diagnostic priority: the declaration's own requirements in their order
(`declarationRequirements`), then the decision requirement, which reads the implementations the
inventory's decision contracts decide. -/
def policyRequirements (d : Declaration) (r : InspectionRequest)
    (native helpers decided : Array Name) : List (DeclarationFailure × Prop) :=
  declarationRequirements d r native helpers ++ [(.decisionContract, DecisionOK d decided)]

end RegulaPolicy
