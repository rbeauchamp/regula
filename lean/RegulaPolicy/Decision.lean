module

public import RegulaPolicy.Specification
public import RegulaPolicy.RoleSpecification
public import Regula.Contract

/-! # Role validators and declaration decisions

Actual generated-role validators and declaration decisions over admitted observations.
Role receipts carry equality to these executed validators for the exact inventory.
Theorems below connect the actual public policy functions to the independent relations. -/

@[expose] public section

namespace RegulaPolicy

universe u
open Lean (Name)
open Frontend

/-- Execute the finite independent native relation; preserve inventory order. -/
def authorizedNativeAxioms (ds : Array Declaration) (ts : Array Transcript := #[]) : Array Name :=
  (ds.filter (fun a => decide (NativeTeachingOK ds ts a))).map (·.name)

/-- Execute the finite independent recursive-helper relation; no caller whitelist. -/
def authorizedUnsafeRecHelpers (ds : Array Declaration) (ts : Array Transcript := #[]) :
    Array Name :=
  (ds.filter (fun h => decide (RecursiveHelperOK ds ts h))).map (·.name)

/-- Authorization is equivalent to existence of the complete native relation at this name. -/
theorem authorizedNativeAxioms_iff (ds : Array Declaration) (ts : Array Transcript) (n : Name) :
    n ∈ authorizedNativeAxioms ds ts ↔ ∃ a ∈ ds, a.name = n ∧ NativeTeachingOK ds ts a := by
  simp [authorizedNativeAxioms, Array.mem_map, Array.mem_filter, and_left_comm, and_comm]

/-- Authorization is equivalent to existence of the complete helper relation at this name. -/
theorem authorizedUnsafeRecHelpers_iff (ds : Array Declaration) (ts : Array Transcript) (n : Name) :
    n ∈ authorizedUnsafeRecHelpers ds ts ↔ ∃ h ∈ ds, h.name = n ∧ RecursiveHelperOK ds ts h := by
  simp [authorizedUnsafeRecHelpers, Array.mem_map, Array.mem_filter, and_left_comm, and_comm]

/-- Raw membership calculation over a caller-supplied set; it authorizes no role. -/
def compilerAxiom (native : Array Name) (name : Name) : Bool :=
  builtinCompilerAxiom name || native.contains name

/-- Raw classification over supplied axiom sets. Use `foundationFor` for an
inventory-bound classification with recomputed generated-role evidence. -/
def labelOf (axioms : Array Name) (native : Array Name := #[]) : FoundationClass :=
  if axioms.contains `sorryAx then .hole
  else if axioms.any fun name => !standardLogicalAxiom name && !compilerAxiom native name then
    .unknownAxiom
  else if axioms.any (compilerAxiom native) then .compilerTrusting
  else if axioms.isEmpty then .kernelOnly
  else if axioms.all (ConformingProfile.permits .choiceFree) then .choiceFree
  else .standardLogical

/-- Raw computational kernel over supplied role sets; callers can supply arbitrary
sets here. This is not an admission or authorization API. Production decisions
use `policyFor`, whose inventory and Roles arguments enforce the receipt boundary. -/
def declarationFailure (decl : Declaration) (claim : InspectionRequest)
    (native : Array Name := #[]) (unsafeHelpers : Array Name := #[]) :
    Option DeclarationFailure :=
  if decl.kind == .«axiom» then
    if native.contains decl.name then
      if claim == .teaching then none else some .compilerTrusting
    else some .projectAxiom
  else if decl.axioms.contains `sorryAx then some .proofHole
  else if decl.axioms.any fun name =>
      !standardLogicalAxiom name && !compilerAxiom native name then some .unknownAxiom
  else if (decl.isUnsafe || decl.isPartial) && !unsafeHelpers.contains decl.name then
    some .escapeHatch
  else if decl.axioms.any (compilerAxiom native) && claim != .teaching then
    some .compilerTrusting
  else if decl.executableContract.any (·.failure.isSome) then some .executableContract
  else match claim with
    | .conforming profile =>
        if decl.axioms.all fun name => compilerAxiom native name ||
                                        ConformingProfile.permits profile name
        then none else some .profileExceeded
    | .classification | .teaching => none


/-- Inventory-bound observations of the actual role validators. Supplying arbitrary
name arrays cannot authorize a role: both equations must be proved for this inventory. -/
structure Roles (inventory : Inventory) where
  /-- Names of the declarations that satisfy `NativeTeachingOK`: the `native_decide` axioms
  admitted as generated roles, in inventory order. -/
  native : Array Name
  /-- Names of the declarations that satisfy `RecursiveHelperOK`: the generated `_unsafe_rec`
  helpers admitted as generated roles, in inventory order. -/
  helpers : Array Name
  /-- `native` is what `authorizedNativeAxioms` computes from this inventory. -/
  native_exact : native = authorizedNativeAxioms inventory.declarations inventory.transcripts
  /-- `helpers` is what `authorizedUnsafeRecHelpers` computes from this inventory. -/
  helpers_exact : helpers = authorizedUnsafeRecHelpers inventory.declarations inventory.transcripts

/-- Recompute both validators from the admitted data; no serialized proof is trusted. -/
def authorize (i : Inventory) : Roles i :=
  ⟨authorizedNativeAxioms i.declarations i.transcripts,
   authorizedUnsafeRecHelpers i.declarations i.transcripts, rfl, rfl⟩

/-- Any role receipt for this exact inventory equals recomputation of both validators.
The equations in Roles determine the arrays; no producer verdict is assumed. -/
theorem Roles.eq_authorize {i : Inventory} (roles : Roles i) : roles = authorize i := by
  cases roles with
  | mk native helpers native_exact helpers_exact =>
    cases native_exact
    cases helpers_exact
    rfl

/-- Public policy checks exact inventory membership before using role evidence. -/
def policyFor (i : Inventory) (roles : Roles i) (d : Declaration)
    (request : InspectionRequest) : Option DeclarationFailure :=
  if d ∈ i.declarations then declarationFailure d request roles.native roles.helpers
  else some .invalidInventory

/-- Foundation rendering uses the same inventory-bound generated-role result. -/
def foundationFor (i : Inventory) (roles : Roles i) (d : Declaration) :
    Except String FoundationClass :=
  if d ∈ i.declarations then .ok (labelOf d.axioms roles.native)
  else .error "declaration is not a member of the authenticated inventory"

/-- Required relation for the member-indexed decision: for every declaration proved to be a
member of the admitted inventory, it is exactly `policyFor`. Non-members cannot be supplied,
so invalid-inventory precedence remains with `policyFor` for arbitrary input. -/
def MemberFailureContract
    (decide : (i : Inventory) → Roles i → (d : Declaration) → d ∈ i.declarations →
      InspectionRequest → Option DeclarationFailure) : Prop :=
  ∀ i roles d (member : d ∈ i.declarations) request,
    decide i roles d member request = policyFor i roles d request

/-- The membership proof, typically supplied by iterating `i.declarations`, replaces
`policyFor`'s linear scan; it is never inspected. Callers use `checked_memberFailure.run`. -/
def memberFailure (i : Inventory) (roles : Roles i) (d : Declaration)
    (_member : d ∈ i.declarations) (request : InspectionRequest) : Option DeclarationFailure :=
  declarationFailure d request roles.native roles.helpers

/-- Registers `MemberFailureContract` about `memberFailure`. -/
theorem checked_memberFailure : Regula.ExecutableContract memberFailure MemberFailureContract :=
  ⟨fun i roles d member request => by simp [memberFailure, policyFor, member]⟩

/-- Required relation for the member-indexed classification: for every inventory member,
`foundationFor` succeeds with exactly this class. The member form has no error case. -/
def MemberFoundationContract
    (classify : (i : Inventory) → Roles i → (d : Declaration) → d ∈ i.declarations →
      FoundationClass) : Prop :=
  ∀ i roles d (member : d ∈ i.declarations),
    foundationFor i roles d = .ok (classify i roles d member)

/-- Classification of a proved member; callers use `checked_memberFoundation.run`. -/
def memberFoundation (i : Inventory) (roles : Roles i) (d : Declaration)
    (_member : d ∈ i.declarations) : FoundationClass :=
  labelOf d.axioms roles.native

/-- Registers `MemberFoundationContract` about `memberFoundation`. -/
theorem checked_memberFoundation :
    Regula.ExecutableContract memberFoundation MemberFoundationContract :=
  ⟨fun i roles d member => by simp [memberFoundation, foundationFor, member]⟩

@[simp] theorem compilerAxiom_iff (native : Array Name) (n : Name) :
    compilerAxiom native n = true ↔ CompilerAxiom native n := by
  simp [compilerAxiom, builtinCompilerAxiom, CompilerAxiom, or_assoc]

@[simp] theorem permits_false_iff (p : ConformingProfile) (n : Name) :
    p.permits n = false ↔ ¬ Permitted p n := by
  simp only [Bool.eq_false_iff, ne_eq, permits_iff]

@[simp] theorem compilerAxiom_false_iff (native : Array Name) (n : Name) :
    compilerAxiom native n = false ↔ ¬ CompilerAxiom native n := by
  simp only [Bool.eq_false_iff, ne_eq, compilerAxiom_iff]

private theorem conditional_none {α : Type u} (p : Prop) [Decidable p] (a b : Option α) :
    (if p then a else b) = none ↔ (p ∧ a = none) ∨ (¬p ∧ b = none) := by
  by_cases h : p <;> simp [h]

/-- Exact success relation for the executable declaration decision, for every observation,
request and supplied role set. `policyFor` additionally requires inventory-bound Roles. Raw
computational helpers
do not establish that receipt or any whole-project acceptance claim. -/
theorem declarationFailure_none_iff (d : Declaration) (r : InspectionRequest)
    (native helpers : Array Name) :
    declarationFailure d r native helpers = none ↔ DeclarationOK d r native helpers := by
  simp only [declarationFailure, DeclarationOK, KnownDependencies, SafetyOK,
    CompilerPolicyOK, ContractOK, ProfileOK]
  cases r <;>
    simp [standardLogicalAxiom, permits_iff, compilerAxiom_iff,
      -Array.any_eq_true, -Array.any_eq_false, -Array.all_eq_true, -Array.all_eq_false,
      Array.any_eq_true', Array.all_eq_true', Option.any_eq_true,
      conditional_none, Option.isSome_iff_ne_none] <;>
    grind

/-- The actual public decision is sound and complete for the exact inventory member. -/
theorem policyFor_none_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (r : InspectionRequest) :
    policyFor i roles d r = none ↔
      d ∈ i.declarations ∧ DeclarationOK d r roles.native roles.helpers := by
  by_cases hd : d ∈ i.declarations
  · simp [policyFor, hd, declarationFailure_none_iff]
  · simp [policyFor, hd]

/-- Logical classification is an embedding of exactly the three conforming profiles. -/
def ConformingProfile.foundationClass : ConformingProfile → FoundationClass
  | .kernelOnly => .kernelOnly | .choiceFree => .choiceFree | .standardLogical => .standardLogical

/-- Authenticated native names cannot be any of the three standard logical axioms. -/
theorem native_not_logical (i : Inventory) (roles : Roles i) (n : Name)
    (hn : n ∈ roles.native) : ¬ Permitted .standardLogical n := by
  rw [roles.native_exact, authorizedNativeAxioms_iff] at hn
  rcases hn with ⟨a, _, ha, hrole⟩
  rcases hrole.2.2 with ⟨p, _, hparent, _⟩
  intro hp
  rcases hp with hp | hp | hp
  all_goals
    rw [ha, hp] at hparent
    simp [nativeParent?] at hparent

/-- The compiler-trusting and logical sets are disjoint for actual inventory-bound roles. -/
theorem compiler_not_logical (i : Inventory) (roles : Roles i) (n : Name)
    (hc : CompilerAxiom roles.native n) : ¬ Permitted .standardLogical n := by
  rcases hc with hc | hc | hc | hc
  · subst n; simp [Permitted]
  · subst n; simp [Permitted]
  · subst n; simp [Permitted]
  · exact native_not_logical i roles n hc

/-- For any logically admissible observed set, the actual diagnostic classifier returns
its least profile. The role argument is bound to the same admitted inventory. -/
theorem labelOf_logical (i : Inventory) (roles : Roles i) (a : Array Name)
    (ha : ContainsFoundation .standardLogical a) :
    labelOf a roles.native = (leastFoundation a).foundationClass := by
  have hole : `sorryAx ∉ a := by
    intro h
    have := ha _ h
    simp [Permitted] at this
  have known : (a.any fun n => !standardLogicalAxiom n && !compilerAxiom roles.native n) =
      false := by
    rw [Array.any_eq_false']
    intro n hn
    have hp := (permits_iff .standardLogical n).mpr (ha n hn)
    simp [standardLogicalAxiom, hp]
  have comp : (a.any (compilerAxiom roles.native)) = false := by
    rw [Array.any_eq_false']
    intro n hn hc
    exact compiler_not_logical i roles n ((compilerAxiom_iff _ _).mp hc) (ha n hn)
  have empty : ContainsFoundation .kernelOnly a ↔ a = #[] := by
    simp [ContainsFoundation, Permitted, Array.eq_empty_iff_forall_not_mem]
  simp only [labelOf, Array.contains_eq_mem, decide_eq_true_eq, hole, ↓reduceIte, known,
    Bool.false_eq_true, comp, leastFoundation, empty, Array.isEmpty_iff]
  split
  · rfl
  · simp only [Array.all_eq_true', permits_iff]
    change
        (if ContainsFoundation .choiceFree a then FoundationClass.choiceFree else
                                                   .standardLogical) = _
    split <;> rfl

/-- Foundation output is both the least containing profile and bound to the supplied record. -/
theorem foundationFor_least (i : Inventory) (roles : Roles i) (d : Declaration)
    (hd : d ∈ i.declarations) (ha : ContainsFoundation .standardLogical d.axioms) :
    foundationFor i roles d = .ok (leastFoundation d.axioms).foundationClass ∧
      LeastFoundation d.axioms (leastFoundation d.axioms) := by
  exact ⟨by simp [foundationFor, hd, labelOf_logical i roles _ ha], leastFoundation_spec _ ha⟩

/-- Decision instances used by acceptance execute the same proved checker function. -/
instance (d : Declaration) (r : InspectionRequest) (native helpers : Array Name) :
    Decidable (DeclarationOK d r native helpers) :=
  decidable_of_iff (declarationFailure d r native helpers = none)
    (declarationFailure_none_iff d r native helpers)


/-- Each conforming profile is contained in Standard-Logical. -/
theorem permitted_standard (p : ConformingProfile) (n : Name) (h : Permitted p n) :
    Permitted .standardLogical n := by
  cases p with
  | kernelOnly => exact False.elim h
  | choiceFree =>
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | standardLogical => exact h

/-- Positive inspection is exactly the permitted foundation, safety exception and recorded
contract requirements. Teaching authorization never relaxes a conforming profile. -/
theorem conforming_iff (i : Inventory) (roles : Roles i) (d : Declaration) (p : ConformingProfile) :
    DeclarationOK d (.conforming p) roles.native roles.helpers ↔
      FoundationOK d p ∧ SafetyOK d roles.helpers ∧ ContractOK d := by
  constructor
  · intro h
    rcases h with h | ⟨ha, _, _, hs, hc, ht, hp⟩
    · cases h.2.2
    · refine ⟨⟨ha, ?_⟩, hs, ht⟩
      have free : ∀ n ∈ d.axioms, ¬ CompilerAxiom roles.native n := by
        rcases hc with hc | hc
        · cases hc
        · exact hc
      intro n hn
      rcases hp n hn with hcomp | hperm
      · exact False.elim (free n hn hcomp)
      · exact hperm
  · rintro ⟨⟨ha, hp⟩, hs, ht⟩
    have logical : ContainsFoundation .standardLogical d.axioms :=
      fun n hn => permitted_standard p n (hp n hn)
    have free : ∀ n ∈ d.axioms, ¬ CompilerAxiom roles.native n :=
      fun n hn hc => compiler_not_logical i roles n hc (logical n hn)
    refine Or.inr ⟨ha, ?_, ?_, hs, Or.inr free, ht, ?_⟩
    · intro hh
      have := logical _ hh
      simp [Permitted] at this
    · exact fun n hn => Or.inl (logical n hn)
    · exact fun n hn => Or.inr (hp n hn)

/-- The actual public checker decision proves all positive declaration requirements and
refuses exactly when membership or one of those requirements fails. -/
theorem policyFor_conforming_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (p : ConformingProfile) :
    policyFor i roles d (.conforming p) = none ↔ d ∈ i.declarations ∧
      FoundationOK d p ∧ SafetyOK d roles.helpers ∧ ContractOK d := by
  rw [policyFor_none_iff, conforming_iff]

/-- Every actual classifier outcome has exactly its independent six-way meaning, including
hole-before-unknown-before-compiler precedence. This holds even for raw role-name arrays. -/
theorem labelOf_iff (axioms native : Array Name) (label : FoundationClass) :
    labelOf axioms native = label ↔ ClassificationOK axioms native label := by
  cases label <;>
    simp only [labelOf, Array.contains_eq_mem, decide_eq_true_eq, standardLogicalAxiom,
      Array.any_eq_true', Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      permits_false_iff, compilerAxiom_false_iff, compilerAxiom_iff, Array.isEmpty_iff,
      Array.all_eq_true', permits_iff, ClassificationOK, not_exists, not_and, ne_eq,
      ContainsFoundation, Classical.not_forall, ite_eq_left_iff, not_or] <;>
    (repeat' split) <;> (try simp_all) <;> grind

/-- Public foundation output retains exact classification and inventory membership for all
six outcomes, not only the three permitted logical profiles. -/
theorem foundationFor_iff (i : Inventory) (roles : Roles i) (d : Declaration)
    (label : FoundationClass) :
    foundationFor i roles d = .ok label ↔ d ∈ i.declarations ∧
        ClassificationOK d.axioms roles.native label := by
  by_cases hd : d ∈ i.declarations <;> simp [foundationFor, hd, labelOf_iff]

/-- The actual declaration diagnostic is the first failed independent requirement. All
success and refusal outputs, including their precedence, follow this same relation. -/
theorem declarationFailure_ordered (d : Declaration) (r : InspectionRequest)
    (native helpers : Array Name) :
    OrderedDecision (declarationRequirements d r native helpers)
        (declarationFailure d r native helpers) := by
  by_cases hd : d.kind = .«axiom» <;> cases r <;>
    simp only [declarationRequirements, hd, ↓reduceIte, reduceCtorEq, declarationFailure,
      BEq.rfl, Array.contains_eq_mem, decide_eq_true_eq, beq_iff_eq, orderedDecision_cons,
      ite_eq_right_iff, Option.some.injEq, imp_false, and_self, not_false_eq_true,
      ite_eq_left_iff, Decidable.not_not, true_and, orderedDecision_nil, false_and, or_false,
      not_true_eq_false, Option.ite_none_left_eq_some, and_false, false_or, KnownDependencies,
      SafetyOK, CompilerPolicyOK, ContractOK, Option.mem_def, ProfileOK, standardLogicalAxiom,
      Array.any_eq_true', Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
      permits_false_iff, compilerAxiom_false_iff, Bool.or_eq_true, decide_eq_false_iff_not,
      compilerAxiom_iff, bne_iff_ne, ne_eq, and_true, Option.any_eq_true,
      Option.isSome_iff_ne_none, Classical.not_forall, not_or, not_and,
      Bool.not_eq_false, true_or, bne_self_eq_false, Bool.and_false, Bool.false_eq_true,
      Array.all_eq_true', permits_iff] <;>
    (repeat' split) <;> (try simp_all) <;> grind

/-- Exact outcome equivalence follows from existence and uniqueness of the first failure. -/
theorem declarationFailure_iff (d : Declaration) (r : InspectionRequest)
    (native helpers : Array Name)
    (result : Option DeclarationFailure) :
    declarationFailure d r native helpers = result ↔
      OrderedDecision (declarationRequirements d r native helpers) result := by
  constructor
  · intro h; rw [← h]; exact declarationFailure_ordered d r native helpers
  · intro h; exact (declarationFailure_ordered d r native helpers).unique h

/-- Invalid inventory membership precedes all declaration-policy diagnostics. -/
theorem policyFor_ordered (i : Inventory) (roles : Roles i) (d : Declaration)
    (r : InspectionRequest) :
    (d ∉ i.declarations ∧ policyFor i roles d r = some .invalidInventory) ∨
    (d ∈ i.declarations ∧ OrderedDecision (declarationRequirements d r roles.native roles.helpers)
      (policyFor i roles d r)) := by
  by_cases hd : d ∈ i.declarations
  · exact Or.inr
      ⟨hd, by simpa [policyFor, hd] using declarationFailure_ordered d r roles.native roles.helpers⟩
  · exact Or.inl ⟨hd, by simp [policyFor, hd]⟩

end RegulaPolicy
