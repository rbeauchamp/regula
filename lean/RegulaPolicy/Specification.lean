module

public import RegulaPolicy.Foundation

/-! # Declaration-policy specification

Declaration-policy meaning over observations. These predicates state membership,
safety, and recorded contract obligations independently of decision outputs. Extraction
and the truth of the observed contract/replay fields remain operational boundaries.

Each requirement takes the part of the record whose fields it reads, so its signature shows
where its inputs come from: `SafetyOK` takes `Declaration.KernelChecked`; `KnownDependencies`,
`CompilerPolicyOK` and `ProfileOK` take `Declaration.ToolchainObserved`; `FoundationOK` takes
`Declaration.Inspected`; and `ContractOK` takes the recorded contract (`RecordedContract`) and no
other field, because a mark a project writes decides one refusal of that contract, as does
`SharedTestOK`, which reads the names that the collector recorded with it, and as does
`DecisionRegistered`, which reads the recorded contracts of an inventory. `DeclarationOK` and
`declarationRequirements` join them and take the inspected part with the recorded contract
(`Declaration.Assessed`), the parts that those requirements take. The decision requirement
(`DecisionOK`) takes the registration part (`Declaration.Registration`): the name and the
project's own registration. -/

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
def KnownDependencies (d : Declaration.ToolchainObserved) (native : Array Name) : Prop :=
  ∀ n ∈ d.axioms, Permitted .standardLogical n ∨ CompilerAxiom native n
instance (d : Declaration.ToolchainObserved) (native : Array Name) :
    Decidable (KnownDependencies d native) := by
  unfold KnownDependencies; infer_instance

/-- Authored unsafe/partial code is refused; the data-level exception is the inventory-validated
recursion helpers. The public theorem substitutes authenticated roles. -/
def SafetyOK (d : Declaration.KernelChecked) (helpers : Array Name) : Prop :=
  (d.isUnsafe = false ∧ d.isPartial = false) ∨ d.name ∈ helpers
instance (d : Declaration.KernelChecked) (helpers : Array Name) :
    Decidable (SafetyOK d helpers) := by
  unfold SafetyOK; infer_instance

/-- Each recorded contract inspection completed without a failure. Its exact proposition
and implementation were checked by Probe and owned logical admission, not by these strings. -/
def ContractOK (contract : RecordedContract) : Prop :=
  ∀ c ∈ contract, c.failure = none
instance (contract : RecordedContract) : Decidable (ContractOK contract) := by
  unfold ContractOK; infer_instance

/-- No recorded decision registration shares a test: the record of each names no function with a
result of `Bool` or `BEq` that its specification and its other side both reach
(`SharedNames.booleans`). The names are the collector's observation: `sharedNames` gives them over
what its search read, at any depth below the specification. A record with a refused contract or
with no decision kind names none. A function that the two sides share under two names is two
constants, and this does not see it. -/
def SharedTestOK (contract : RecordedContract) : Prop :=
  ∀ c ∈ contract, c.shared.booleans = #[]
instance (contract : RecordedContract) : Decidable (SharedTestOK contract) := by
  unfold SharedTestOK; infer_instance

/-- The recorded contracts of an inventory's declarations, in inventory order. -/
def recordedContracts (ds : Array Declaration) : Array RecordedContract :=
  ds.map (·.executableContract)

/-- `n` is the implementation a decision contract of the inventory decides: one of the recorded
contracts `contracts` states a decision kind, was not refused, and names `n` as its
implementation. -/
def DecisionRegistered (contracts : Array RecordedContract) (n : Name) : Prop :=
  ∃ r ∈ contracts, ∃ c ∈ r, c.root = n ∧ c.kind.isSome = true ∧ c.failure = none

/-- A function registered as a decision (`@[regula_decision]`) states the direction it proves: its
result type is `Decidable _`, or it is among `decided`, the implementations the inventory's
decision contracts decide. A declaration without the registration has no such requirement; every
registered declaration has it, whatever else the record says of the declaration, so no other
observation waives it. It takes the registration part of the record (`Declaration.Registration`):
the name and the registration, which is the collector's observation, and no other field. -/
def DecisionOK (d : Declaration.Registration) (decided : Array Name) : Prop :=
  d.decisionResult = some .«other» → d.name ∈ decided
instance (d : Declaration.Registration) (decided : Array Name) :
    Decidable (DecisionOK d decided) := by
  unfold DecisionOK; infer_instance

/-- Teaching may retain compiler trust; other inspections cannot. -/
def CompilerPolicyOK (d : Declaration.ToolchainObserved) (request : InspectionRequest)
    (native : Array Name) : Prop :=
  request = .teaching ∨ ∀ n ∈ d.axioms, ¬ CompilerAxiom native n
instance (d : Declaration.ToolchainObserved) (r : InspectionRequest) (native : Array Name) :
    Decidable (CompilerPolicyOK d r native) := by unfold CompilerPolicyOK; infer_instance

/-- Only an explicitly conforming request imposes a positive profile bound. Compiler
members are separately refused by CompilerPolicyOK for every conforming request. -/
def ProfileOK (d : Declaration.ToolchainObserved) (request : InspectionRequest)
    (native : Array Name) : Prop :=
  match request with
  | .conforming p => ∀ n ∈ d.axioms, CompilerAxiom native n ∨ Permitted p n
  | _ => True
instance (d : Declaration.ToolchainObserved) (r : InspectionRequest) (native : Array Name) :
    Decidable (ProfileOK d r native) := by cases r <;> unfold ProfileOK <;> infer_instance

/-- Inspection success. An owned axiom has only the independently authenticated teaching
case; positive conformance always requires a non-axiom and all remaining conjuncts. It takes the
assessed part of the record (`Declaration.Assessed`). -/
def DeclarationOK (d : Declaration.Assessed) (request : InspectionRequest)
    (native helpers : Array Name) : Prop :=
  (d.kind = .«axiom» ∧ d.name ∈ native ∧ request = .teaching) ∨
  (d.kind ≠ .«axiom» ∧ `sorryAx ∉ d.axioms ∧ KnownDependencies d.toToolchainObserved native ∧
    SafetyOK d.toKernelChecked helpers ∧ CompilerPolicyOK d.toToolchainObserved request native ∧
    ContractOK d.executableContract ∧ SharedTestOK d.executableContract ∧
    ProfileOK d.toToolchainObserved request native)

/-- A recorded contract refusing nothing passes: no refusal and no shared test. -/
theorem ContractOK.neutral (contract : RecordedContract) :
    ContractOK (contract.map fun c => { c with failure := none, shared := {} }) := by
  cases contract <;> simp [ContractOK]

/-- A recorded contract refusing nothing shares no test. -/
theorem SharedTestOK.neutral (contract : RecordedContract) :
    SharedTestOK (contract.map fun c => { c with failure := none, shared := {} }) := by
  cases contract <;> simp [SharedTestOK]

/-- Compiler trust grows with the native set. -/
theorem CompilerAxiom.mono {native native' : Array Name} {n : Name}
    (sub : ∀ m ∈ native', m ∈ native) (hc : CompilerAxiom native' n) : CompilerAxiom native n :=
  Or.imp_right (sub n) hc

/-- A compiler-trusting axiom is no Standard-Logical axiom when the native set names none. -/
theorem CompilerAxiom.not_logical {native : Array Name} {n : Name}
    (logical : ∀ m ∈ native, ¬ Permitted .standardLogical m) (hc : CompilerAxiom native n) :
    ¬ Permitted .standardLogical n := by
  rcases hc with ⟨_, hc | hc | hc⟩ | hc
  · subst n; simp [Permitted]
  · subst n; simp [Permitted]
  · subst n; simp [Permitted]
  · exact logical n hc

/-- The refusals of the recorded contract can refuse a declaration but never admit one: whatever
`DeclarationOK` admits, it admits with the contract refusing nothing
(`Declaration.Assessed.neutral`). -/
theorem DeclarationOK.neutral {d : Declaration.Assessed} {request : InspectionRequest}
    {native helpers : Array Name} (ok : DeclarationOK d request native helpers) :
    DeclarationOK d.neutral request native helpers := by
  rcases ok with ⟨hk, hmem, hreq⟩ | ⟨hk, hsorry, hknown, hsafe, hcomp, -, -, hprofile⟩
  · exact Or.inl ⟨hk, hmem, hreq⟩
  · exact Or.inr ⟨hk, hsorry, hknown, hsafe, hcomp, ContractOK.neutral _, SharedTestOK.neutral _,
      hprofile⟩

/-- Smaller role sets admit nothing more: whatever `DeclarationOK` admits with `native'` and
`helpers'`, it admits with any larger sets, provided the larger native set names no
Standard-Logical axiom, as no authenticated native role does. A role a mark removes can therefore
only refuse. -/
theorem DeclarationOK.of_subset {d : Declaration.Assessed} {request : InspectionRequest}
    {native native' helpers helpers' : Array Name}
    (ok : DeclarationOK d request native' helpers') (hn : ∀ n ∈ native', n ∈ native)
    (hh : ∀ n ∈ helpers', n ∈ helpers) (logical : ∀ n ∈ native, ¬ Permitted .standardLogical n) :
    DeclarationOK d request native helpers := by
  rcases ok with ⟨hk, hmem, hreq⟩ | ⟨hk, hsorry, hknown, hsafe, hcomp, hcontract, hshared, hprofile⟩
  · exact Or.inl ⟨hk, hn _ hmem, hreq⟩
  · refine Or.inr ⟨hk, hsorry, fun n hax => (hknown n hax).imp_right (CompilerAxiom.mono hn),
      ?_, ?_, hcontract, hshared, ?_⟩
    · exact Or.imp_right (hh _) hsafe
    · rcases hcomp with teaching | free
      · exact Or.inl teaching
      · refine Or.inr fun n hax hc => ?_
        rcases hknown n hax with permitted | compiler
        · exact CompilerAxiom.not_logical logical hc permitted
        · exact free n hax compiler
    · cases request with
      | conforming p => exact fun n hax => (hprofile n hax).imp_left (CompilerAxiom.mono hn)
      | _ => trivial

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
other declarations must meet each obligation in this explicit order. It takes the assessed part
of the record (`Declaration.Assessed`). -/
def declarationRequirements (d : Declaration.Assessed) (r : InspectionRequest)
    (native helpers : Array Name) :
    List (DeclarationFailure × Prop) :=
  if d.kind = .«axiom» then
    [(.projectAxiom, d.name ∈ native), (.compilerTrusting, r = .teaching)]
  else
    [(.proofHole, `sorryAx ∉ d.axioms),
     (.unknownAxiom, KnownDependencies d.toToolchainObserved native),
     (.escapeHatch, SafetyOK d.toKernelChecked helpers),
     (.compilerTrusting, CompilerPolicyOK d.toToolchainObserved r native),
     (.executableContract, ContractOK d.executableContract),
     (.sharedTest, SharedTestOK d.executableContract),
     (.profileExceeded, ProfileOK d.toToolchainObserved r native)]

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
