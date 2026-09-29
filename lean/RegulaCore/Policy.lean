import RegulaCore.Rule
import RegulaCore.EditorPolicy
import RegulaPolicy.Decision
import RegulaPolicy.Execution
import RegulaPolicy.Guards
import RegulaPolicy.Traversal
import Regula.Contract

/-! # Checker policy projections

Pure checker projections of the policy decisions: claim spelling and request,
scope admission, declaration rules and execution rules. Each requirement is a named
`Prop`; a closed `ExecutableContract` proves it about the executed definition, and the
operational adapter `Regula.Checker.Policy` runs these registrations. Scope admission
takes the transcript-coordinate check as a parameter, so `ScopeContract` holds for every
check; the adapter supplies `RegulaCore.Coordinates`'s `checked_coordinates`. These
contracts do not authenticate transcripts, sources or environment observations. -/

namespace Regula.Checker.Policy

open RegulaPolicy (Declaration FoundationClass)

/-- A foundation claim profile, as a surface manifest or `--claim` names it; `request` maps it to
the inspection the checker runs. -/
inductive Profile where
  /-- `kernel-only`: no axioms. -/
  | kernelOnly
  /-- `choice-free`: at most `propext` and `Quot.sound`. -/
  | choiceFree
  /-- `standard-logical`: additionally `Classical.choice`. -/
  | standardLogical
  /-- `compiler-trusting`: selects teaching inspection, not a conforming profile. -/
  | compilerTrusting
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Profile

/-- The profile a manifest or command-line spelling names; any other text is refused. -/
def parse? : String → Option Profile
  | "kernel-only" => some .kernelOnly
  | "choice-free" => some .choiceFree
  | "standard-logical" => some .standardLogical
  | "compiler-trusting" => some .compilerTrusting
  | _ => none

/-- The spelling of a profile, which `parse?` reads back (`Profile.parse?_eq_some_iff`). -/
def toString : Profile → String
  | .kernelOnly => "kernel-only"
  | .choiceFree => "choice-free"
  | .standardLogical => "standard-logical"
  | .compilerTrusting => "compiler-trusting"

instance : ToString Profile := ⟨toString⟩

end Profile

/-- Command-line and manifest spellings select exactly the profile rendered by `toString`. -/
theorem Profile.parse?_eq_some_iff (text : String) (profile : Profile) :
    Profile.parse? text = some profile ↔ profile.toString = text := by
  constructor
  · intro h
    unfold Profile.parse? at h
    split at h <;> cases h <;> rfl
  · rintro rfl
    cases profile <;> rfl

/-- Adapter groups one admitted inventory with its recomputed role evidence.
`RegulaPolicy.Roles.eq_authorize` determines `roles` from `inventory`. -/
structure PolicyScope where
  /-- The admitted declaration inventory. -/
  inventory : RegulaPolicy.Inventory
  /-- The generated-role evidence recomputed for `inventory`. -/
  roles : RegulaPolicy.Roles inventory

/-- The native-proof axioms admitted as generated roles (`Roles.native`). -/
def PolicyScope.native (s : PolicyScope) : Array Lean.Name := s.roles.native
/-- The `_unsafe_rec` helpers admitted as generated roles (`Roles.helpers`). -/
def PolicyScope.helpers (s : PolicyScope) : Array Lean.Name := s.roles.helpers

/-- A transcript-coordinate check over the declaration inventory. The operational
adapter supplies `Frontend.validateCoordinates`, which runs `checked_coordinates`. -/
abbrev CoordinateCheck :=
  Array Declaration → RegulaPolicy.Frontend.Transcript → Except String Unit

/-- Required admission relation, for every coordinate check. The check runs first, over
transcripts in order, and the first refusal is returned. Afterwards admission is exactly
inventory admission with recomputed roles. Success retains the exact declaration and
transcript arrays, and occurs exactly when every check and the inventory predicate hold. -/
def ScopeContract
    (admit : CoordinateCheck → Array Declaration → Array RegulaPolicy.Frontend.Transcript →
      Except String PolicyScope) : Prop :=
  ∀ check : CoordinateCheck,
    (∀ ds ts before t after e, ts.toList = before ++ t :: after →
        (∀ b ∈ before, check ds b = .ok ()) →
        check ds t = .error e → admit check ds ts = .error e) ∧
    (∀ ds ts, (∀ t ∈ ts, check ds t = .ok ()) →
        admit check ds ts = (RegulaPolicy.admitInventory ds ts).map
          fun inventory => ⟨inventory, RegulaPolicy.authorize inventory⟩) ∧
    (∀ ds ts, (∃ scope, admit check ds ts = .ok scope) ↔
        (∀ t ∈ ts, check ds t = .ok ()) ∧ RegulaPolicy.InventoryValid ds ts) ∧
    (∀ ds ts scope, admit check ds ts = .ok scope →
        scope.inventory.declarations = ds ∧ scope.inventory.transcripts = ts)

private def admitScopeImpl (check : CoordinateCheck) (ds : Array Declaration)
    (ts : Array RegulaPolicy.Frontend.Transcript) : Except String PolicyScope := do
  ts.toList.forM (check ds)
  let inventory ← RegulaPolicy.admitInventory ds ts
  return ⟨inventory, RegulaPolicy.authorize inventory⟩

private theorem admitScopeImpl_checked (check : CoordinateCheck) (ds : Array Declaration)
    (ts : Array RegulaPolicy.Frontend.Transcript) (h : ∀ t ∈ ts, check ds t = .ok ()) :
    admitScopeImpl check ds ts = (RegulaPolicy.admitInventory ds ts).map
      fun inventory => ⟨inventory, RegulaPolicy.authorize inventory⟩ := by
  have hts : ts.toList.forM (check ds) = .ok () :=
    RegulaPolicy.Guards.listForM_eq_ok.mpr fun t ht => h t (by simpa using ht)
  simp only [admitScopeImpl, hts, bind, Except.bind]
  cases RegulaPolicy.admitInventory ds ts <;> rfl

/-- Registers `ScopeContract` about the executed admission; the adapter's `admitScope`
runs it with the frontend coordinate check. -/
theorem checked_scope : Regula.ExecutableContract admitScopeImpl ScopeContract := by
  refine ⟨fun check => ⟨?first, admitScopeImpl_checked check, ?success, ?fidelity⟩⟩
  case first =>
    intro ds ts before t after e hts hb ht
    have refused := (RegulaPolicy.forM_eq_error _ _ e).mpr ⟨before, t, after, hts, hb, ht⟩
    simp only [admitScopeImpl, refused, bind, Except.bind]
  case success =>
    intro ds ts
    by_cases hc : ∀ t ∈ ts, check ds t = .ok ()
    · rw [admitScopeImpl_checked check ds ts hc]
      by_cases hv : RegulaPolicy.InventoryValid ds ts
      · simpa [RegulaPolicy.admitInventory_exact ds ts hv, Except.map, hv] using hc
      · simp [RegulaPolicy.admitInventory, hv, Except.map]
    · have hts : ts.toList.forM (check ds) ≠ .ok () :=
        fun h => hc fun t ht => RegulaPolicy.Guards.listForM_eq_ok.mp h t (by simpa using ht)
      simp only [hc, false_and, iff_false, not_exists]
      intro scope h
      apply hts
      cases h' : ts.toList.forM (check ds) with
      | error e => simp [admitScopeImpl, h', bind, Except.bind] at h
      | ok u => rfl
  case fidelity =>
    intro ds ts scope h
    cases hts : ts.toList.forM (check ds) with
    | error e => simp [admitScopeImpl, hts, bind, Except.bind] at h
    | ok u =>
      by_cases hv : RegulaPolicy.InventoryValid ds ts
      · simp only [admitScopeImpl, bind, Except.bind, hts,
          RegulaPolicy.admitInventory_exact ds ts hv, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨rfl, rfl⟩
      · simp [admitScopeImpl, hts, bind, Except.bind, RegulaPolicy.admitInventory, hv] at h

/-- Required meaning of a claim: no claim selects classification, compiler-trusting selects
teaching inspection, and every other profile selects the conforming profile of its spelling. -/
def RequestContract (request : Option Profile → RegulaPolicy.InspectionRequest) : Prop :=
  request none = .classification ∧
  ∀ profile, (request (some profile) = .teaching ↔ profile = .compilerTrusting) ∧
    ∀ conforming, request (some profile) = .conforming conforming ↔
      profile.toString = conforming.spelling

private def requestImpl : Option Profile → RegulaPolicy.InspectionRequest
  | none => .classification
  | some .compilerTrusting => .teaching
  | some .kernelOnly => .conforming .kernelOnly
  | some .choiceFree => .conforming .choiceFree
  | some .standardLogical => .conforming .standardLogical

/-- Registers `RequestContract` about the executed projection; callers use `request`. -/
theorem checked_request : Regula.ExecutableContract requestImpl RequestContract :=
  ⟨⟨rfl, fun profile => by
    cases profile <;> refine ⟨by simp [requestImpl], fun conforming => ?_⟩ <;>
      cases conforming <;> simp [requestImpl, Profile.toString,
        RegulaPolicy.ConformingProfile.spelling]⟩⟩

/-- The policy request selected by a claim, through `checked_request`. -/
def request (claim : Option Profile) : RegulaPolicy.InspectionRequest :=
  checked_request.run claim

/-- `RequestContract` stated about `request` itself, for reuse by its consumers. -/
theorem request_contract : RequestContract request :=
  checked_request.evidence

/-- Required declaration projection: no rule exactly when the inventory-bound policy decision
for the selected request succeeds, and otherwise the registry rule of that decision's failure.
With `ruleForFailure_injective`, the rule identifies the first failed requirement proved by
`RegulaPolicy.policyFor_ordered`. -/
def RuleContract (rule : Declaration → Option Profile → PolicyScope → Option RuleId) : Prop :=
  ∀ decl claim scope,
    (rule decl claim scope = none ↔
      RegulaPolicy.policyFor scope.inventory scope.roles decl (request claim) = none) ∧
    ∀ failure, rule decl claim scope = some (Regula.ruleForFailure failure) ↔
      RegulaPolicy.policyFor scope.inventory scope.roles decl (request claim) = some failure

private def ruleForImpl (decl : Declaration) (claim : Option Profile) (scope : PolicyScope) :
    Option RuleId :=
  (RegulaPolicy.policyFor scope.inventory scope.roles decl (request claim)).map
    Regula.ruleForFailure

/-- Registers `RuleContract` about the executed projection; callers use `ruleFor`. -/
theorem checked_rule : Regula.ExecutableContract ruleForImpl RuleContract :=
  ⟨fun decl claim scope => by
    unfold ruleForImpl
    cases RegulaPolicy.policyFor scope.inventory scope.roles decl (request claim) with
    | none => simp
    | some found =>
      refine ⟨by simp, fun failure => ?_⟩
      simp only [Option.map_some, Option.some.injEq]
      exact ⟨fun h => (Regula.ruleForFailure_injective h).symm ▸ rfl,
        fun h => h ▸ rfl⟩⟩

/-- The registry rule for a declaration's first policy failure, through `checked_rule`. -/
def ruleFor (decl : Declaration) (claim : Option Profile) (scope : PolicyScope) : Option RuleId :=
  checked_rule.run decl claim scope

/-- Required member projection: for every declaration proved to be a member of the scope's
admitted inventory, the rule is exactly `ruleFor`'s, and so satisfies `RuleContract`. -/
def MemberRuleContract
    (rule : (decl : Declaration) → Option Profile → (scope : PolicyScope) →
      decl ∈ scope.inventory.declarations → Option RuleId) : Prop :=
  ∀ decl claim scope (member : decl ∈ scope.inventory.declarations),
    rule decl claim scope member = ruleFor decl claim scope

private def ruleForMemberImpl (decl : Declaration) (claim : Option Profile) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) : Option RuleId :=
  (RegulaPolicy.checked_memberFailure.run scope.inventory scope.roles decl member
    (request claim)).map Regula.ruleForFailure

/-- Registers `MemberRuleContract`, reducing it to `MemberFailureContract`. -/
theorem checked_memberRule : Regula.ExecutableContract ruleForMemberImpl MemberRuleContract :=
  ⟨fun decl claim scope member => by
    simp only [ruleForMemberImpl, ruleFor, Regula.ExecutableContract.run_eq, ruleForImpl,
      RegulaPolicy.checked_memberFailure.evidence _ _ _ member]⟩

/-- `ruleFor` for a member, supplied by iterating `scope.inventory.declarations`: the
membership proof replaces the inventory scan. Through `checked_memberRule`. -/
def ruleForMember (decl : Declaration) (claim : Option Profile) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) : Option RuleId :=
  checked_memberRule.run decl claim scope member

/-- `MemberRuleContract` stated about `ruleForMember` itself. -/
theorem ruleForMember_eq (decl : Declaration) (claim : Option Profile) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) :
    ruleForMember decl claim scope member = ruleFor decl claim scope :=
  checked_memberRule.evidence decl claim scope member

/-- `RuleContract` stated about `ruleFor` itself. -/
theorem ruleFor_contract : RuleContract ruleFor :=
  checked_rule.evidence

/-- Required subject of a member's declaration finding: the member's partial parent in the scope's
inventory (`RegulaPolicy.PartialParent`), the `partial def` the author wrote or a deriving handler
generated, when it has one, and otherwise the member itself. -/
def SubjectContract
    (subject : (decl : Declaration) → (scope : PolicyScope) →
      decl ∈ scope.inventory.declarations → Declaration) : Prop :=
  ∀ decl scope (member : decl ∈ scope.inventory.declarations) p,
    subject decl scope member = p ↔
      (p ∈ scope.inventory.declarations ∧ RegulaPolicy.PartialParent decl p) ∨
      (p = decl ∧ ∀ q ∈ scope.inventory.declarations, ¬ RegulaPolicy.PartialParent decl q)

private def subjectImpl (decl : Declaration) (scope : PolicyScope)
    (_member : decl ∈ scope.inventory.declarations) : Declaration :=
  (RegulaPolicy.partialParent? scope.inventory.declarations decl).getD decl

/-- Registers `SubjectContract` about the executed projection; callers use `subject`. -/
theorem checked_subject : Regula.ExecutableContract subjectImpl SubjectContract :=
  ⟨fun decl scope _ p => by
    have unique := scope.inventory.valid.1
    have iff := RegulaPolicy.partialParent?_eq_some_iff unique decl
    unfold subjectImpl
    cases found : RegulaPolicy.partialParent? scope.inventory.declarations decl with
    | some q =>
      have hq := (iff q).mp found
      simp only [Option.getD_some]
      constructor
      · rintro rfl; exact Or.inl hq
      · rintro (parent | ⟨_, none⟩)
        · exact Option.some.inj (found.symm.trans ((iff p).mpr parent))
        · exact absurd hq.2 (none q hq.1)
    | none =>
      have none : ∀ q ∈ scope.inventory.declarations, ¬ RegulaPolicy.PartialParent decl q :=
        fun q hq parent => by simp [(iff q).mpr ⟨hq, parent⟩] at found
      simp only [Option.getD_none]
      constructor
      · rintro rfl; exact Or.inr ⟨rfl, none⟩
      · rintro (⟨hp, parent⟩ | ⟨rfl, _⟩)
        · exact absurd parent (none p hp)
        · rfl⟩

/-- The declaration a member's finding names, through `checked_subject`. -/
def subject (decl : Declaration) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) : Declaration :=
  checked_subject.run decl scope member

/-- `SubjectContract` stated about `subject` itself. -/
theorem subject_contract : SubjectContract subject :=
  checked_subject.evidence

/-- A member with a partial parent always has a finding, for every claim: it is `partial` and,
by `RegulaPolicy.partialParent_not_authorized`, not an authorized recursion helper, so
`SafetyOK` fails, and a native axiom (`NativeAxiomShape`) is never partial. Its finding names
that parent (`subject_contract`). -/
theorem partialParent_rule (decl : Declaration) (claim : Option Profile) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) {p : Declaration}
    (hp : p ∈ scope.inventory.declarations) (parent : RegulaPolicy.PartialParent decl p) :
    ruleForMember decl claim scope member ≠ none := by
  have unique := scope.inventory.valid.1
  rw [ruleForMember_eq, Ne, (ruleFor_contract decl claim scope).1,
    RegulaPolicy.policyFor_none_iff]
  rintro ⟨_, ok⟩
  have notHelper := RegulaPolicy.partialParent_not_authorized scope.inventory.transcripts unique
    member hp parent
  rw [← scope.roles.helpers_exact] at notHelper
  rcases ok with ⟨_, native, _⟩ | ⟨_, _, _, safety, _⟩
  · rw [scope.roles.native_exact] at native
    obtain ⟨a, ha, hname, shape, _⟩ :=
      (RegulaPolicy.authorizedNativeAxioms_iff _ _ _).mp native
    cases RegulaPolicy.eq_of_name_eq unique ha member hname
    exact absurd parent.1 (by simp [shape.2.2.2.2.1])
  · rcases safety with ⟨_, hpartial⟩ | helper
    · exact absurd parent.1 (by simp [hpartial])
    · exact notHelper helper

/-- The editor's request domain is the project request's without teaching: every value the
editor option accepts selects `request claim` for a claim other than compiler-trusting. -/
theorem editor_request_sound {value : String} {r : RegulaPolicy.InspectionRequest}
    (h : Regula.Linter.editorRequest value = some r) :
    ∃ claim, claim ≠ some .compilerTrusting ∧ request claim = r := by
  rcases (Regula.Linter.editorRequest_contract value r).mp h with ⟨_, rfl⟩ | ⟨p, _, rfl⟩
  · exact ⟨none, by simp, rfl⟩
  · cases p
    · exact ⟨some .kernelOnly, by simp, rfl⟩
    · exact ⟨some .choiceFree, by simp, rfl⟩
    · exact ⟨some .standardLogical, by simp, rfl⟩

/-- Every project request other than teaching is selectable by some editor option value. -/
theorem editor_request_complete (claim : Option Profile) (h : claim ≠ some .compilerTrusting) :
    ∃ value, Regula.Linter.editorRequest value = some (request claim) := by
  rcases claim with _ | ⟨_ | _ | _ | _⟩
  · exact ⟨"classification-only", by decide⟩
  · exact ⟨"kernel-only", by decide⟩
  · exact ⟨"choice-free", by decide⟩
  · exact ⟨"standard-logical", by decide⟩
  · exact absurd rfl h

/-- For the same member and request, the editor passes a declaration exactly when the
project rule projection selects no rule. -/
theorem editor_decision_none_iff (scope : PolicyScope) (decl : Declaration)
    (member : decl ∈ scope.inventory.declarations) (claim : Option Profile) :
    Regula.Linter.editorDecision scope.inventory scope.roles decl member (request claim) = none ↔
      ruleForMember decl claim scope member = none := by
  rw [(Regula.Linter.editorDecision_contract _ _ _ member _).1, ruleForMember_eq,
    (ruleFor_contract decl claim scope).1]

/-- A rule the editor renders is the project rule projection's rule for the same member and
request (`checked_memberRule`). -/
theorem editor_decision_rule (scope : PolicyScope) (decl : Declaration)
    (member : decl ∈ scope.inventory.declarations) (claim : Option Profile) (id : RuleId)
    (h : Regula.Linter.editorDecision scope.inventory scope.roles decl member (request claim) =
      some (.rule id)) :
    ruleForMember decl claim scope member = some id := by
  obtain ⟨f, hf, _, rfl⟩ :=
    ((Regula.Linter.editorDecision_contract _ _ _ member _).2.2 id).mp h
  rw [ruleForMember_eq]
  exact ((ruleFor_contract decl claim scope).2 f).mpr hf

/-- A pending editor decision withholds a rule the project projection selects; the failure
needs fresh generated-role evidence that only a project or fresh-file audit supplies. -/
theorem editor_decision_pending (scope : PolicyScope) (decl : Declaration)
    (member : decl ∈ scope.inventory.declarations) (claim : Option Profile)
    (h : Regula.Linter.editorDecision scope.inventory scope.roles decl member (request claim) =
      some .pending) :
    ∃ f, ruleForMember decl claim scope member = some (Regula.ruleForFailure f) ∧
      Regula.Linter.needsRoleEvidence decl f = true := by
  obtain ⟨f, hf, hn⟩ := ((Regula.Linter.editorDecision_contract _ _ _ member _).2.1).mp h
  refine ⟨f, ?_, hn⟩
  rw [ruleForMember_eq]
  exact ((ruleFor_contract decl claim scope).2 f).mpr hf

/-- Applicability text of the rule `ruleFor` selects. -/
def reasonFor (decl : Declaration) (claim : Option Profile) (scope : PolicyScope) : Option String :=
  (ruleFor decl claim scope).map (fun id => (descriptor id).applicability)

/-- Declaration-failure rules have pairwise distinct applicability text. -/
theorem applicability_ruleForFailure_injective (a b : RegulaPolicy.DeclarationFailure)
    (h : (descriptor (Regula.ruleForFailure a)).applicability =
      (descriptor (Regula.ruleForFailure b)).applicability) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [descriptor, Regula.ruleForFailure] at h)

/-- The rendered reason is the applicability of the decision's failure, and only of it. -/
theorem reasonFor_eq_some_iff (decl : Declaration) (claim : Option Profile) (scope : PolicyScope)
    (failure : RegulaPolicy.DeclarationFailure) :
    reasonFor decl claim scope =
        some (descriptor (Regula.ruleForFailure failure)).applicability ↔
      RegulaPolicy.policyFor scope.inventory scope.roles decl (request claim) =
        some failure := by
  have contract := checked_rule.evidence decl claim scope
  rw [← (contract.2 failure)]
  unfold reasonFor ruleFor
  rw [Regula.ExecutableContract.run_eq]
  cases hr : ruleForImpl decl claim scope with
  | none => simp
  | some id =>
    have found : ∃ found, id = Regula.ruleForFailure found := by
      cases hp : RegulaPolicy.policyFor scope.inventory scope.roles decl (request claim) with
      | none => rw [← contract.1, hr] at hp; cases hp
      | some found =>
        exact ⟨found, Option.some.inj (hr.symm.trans ((contract.2 found).mpr hp))⟩
    obtain ⟨found, rfl⟩ := found
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun h => applicability_ruleForFailure_injective _ _ h ▸ rfl, fun h => h ▸ rfl⟩

/-- Foundation class of any declaration, refusing a non-member of the scope's inventory. -/
def labelOf (decl : Declaration) (scope : PolicyScope) : Except String FoundationClass :=
  RegulaPolicy.foundationFor scope.inventory scope.roles decl

/-- Foundation class of a member of the scope's inventory, through
`RegulaPolicy.checked_memberFoundation`: `labelOf` succeeds with exactly this class. -/
def labelOfMember (decl : Declaration) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) : FoundationClass :=
  RegulaPolicy.checked_memberFoundation.run scope.inventory scope.roles decl member

theorem labelOf_member (decl : Declaration) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) :
    labelOf decl scope = .ok (labelOfMember decl scope member) :=
  RegulaPolicy.checked_memberFoundation.evidence _ _ _ member

/-- Total bridge from execution failure kinds to the single rule registry. -/
def executionRule : RegulaPolicy.ExecutionFailureKind → RuleId
  | .executionUnresolved => .executionUnresolved
  | .executionBoundary => .executionBoundary

theorem executionRule_injective : Function.Injective executionRule := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

/-- One failure's text: its registry rule's applicability and the decision's detail. -/
def executionFailureLine (failure : RegulaPolicy.ExecutionFailure) : String :=
  s!"{(descriptor (executionRule failure.id)).applicability}: {failure.detail}"

/-- Required meaning of the rendered execution failures: line `k` renders the decision's
record `k`, with no line added or dropped. The lines are therefore empty exactly when
`ExecutionOK` holds, so rendering cannot hide a failure. -/
def ExecutionFailuresContract
    (render : RegulaPolicy.ExecutionInventory → RegulaPolicy.ExecutionClaim → Array String) :
        Prop :=
  ∀ inventory claim,
    (render inventory claim).size = (RegulaPolicy.executionFailureRecords inventory claim).size ∧
    (∀ k (h : k < (render inventory claim).size)
        (h' : k < (RegulaPolicy.executionFailureRecords inventory claim).size),
      (render inventory claim)[k] =
        executionFailureLine (RegulaPolicy.executionFailureRecords inventory claim)[k]) ∧
    (render inventory claim = #[] ↔ RegulaPolicy.ExecutionOK inventory claim)

private def executionFailuresImpl (inventory : RegulaPolicy.ExecutionInventory)
    (claim : RegulaPolicy.ExecutionClaim) : Array String :=
  (RegulaPolicy.executionFailureRecords inventory claim).map executionFailureLine

/-- Registers `ExecutionFailuresContract` about the executed renderer. -/
theorem checked_executionFailures :
    Regula.ExecutableContract executionFailuresImpl ExecutionFailuresContract := by
  refine ⟨fun inventory claim => ⟨by simp [executionFailuresImpl], fun k _ _ => by
    simp [executionFailuresImpl], ?_⟩⟩
  rw [← RegulaPolicy.executionFailureRecords_empty_iff]
  simp [executionFailuresImpl]

/-- The gate's failure subreasons, through `checked_executionFailures`. -/
def executionFailures (inventory : RegulaPolicy.ExecutionInventory)
    (claim : RegulaPolicy.ExecutionClaim) : Array String :=
  checked_executionFailures.run inventory claim

end Regula.Checker.Policy
