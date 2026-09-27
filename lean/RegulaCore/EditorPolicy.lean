module

public import RegulaCore.Rule
public import RegulaPolicy.Decision

/-! # Editor linter decisions

Pure decisions of the native editor linter (`Regula.Linter.Rules`): the request selected
by the `regula.localFoundation` option and the per-declaration outcome. Each is a named `Prop`
with a closed `ExecutableContract` registration that the linter runs. `RegulaCore.Policy`
relates both to the project checker's `request` and `ruleForMember` (`editor_request_sound`,
`editor_decision_rule`): the editor's request domain is the project's without teaching, and a
rendered rule is the project rule for the same member and request. `checked_liveFeedback`
registers the switch that gates every local finding: an audit build's import-time marker
(`auditBuildOption`) turns it off whatever the source's `linter.regula` value
(`liveFeedback_auditBuild`). Collection, snapshots and message emission stay in the
operational linter. -/

@[expose] public section

namespace Regula.Linter

open RegulaPolicy

/-- Required meaning of the editor's local foundation option: `classification-only` selects
classification, each conforming profile spelling selects that profile, and every other value
is refused. No value selects teaching inspection. -/
def EditorRequestContract (parse : String → Option InspectionRequest) : Prop :=
  ∀ value request, parse value = some request ↔
    (value = "classification-only" ∧ request = .classification) ∨
    ∃ p, ConformingProfile.parse? value = some p ∧ request = .conforming p

def editorRequestImpl (value : String) : Option InspectionRequest :=
  if value = "classification-only" then some .classification
  else (ConformingProfile.parse? value).map .conforming

/-- Registers `EditorRequestContract` about the executed option parser. -/
theorem checked_editorRequest : Regula.ExecutableContract editorRequestImpl EditorRequestContract :=
  ⟨fun value request => by
    unfold editorRequestImpl
    by_cases h : value = "classification-only"
    · subst h
      have none : ConformingProfile.parse? "classification-only" = none := rfl
      simp [none, eq_comm]
    · simp only [h, ↓reduceIte]
      cases ConformingProfile.parse? value <;> simp [eq_comm]⟩

/-- The request selected by the editor option, through `checked_editorRequest`. -/
def editorRequest (value : String) : Option InspectionRequest :=
  checked_editorRequest.run value

/-- `EditorRequestContract` stated about `editorRequest` itself. -/
theorem editorRequest_contract : EditorRequestContract editorRequest :=
  checked_editorRequest.evidence

/-- A missing fresh transcript cannot turn a possible generated-role exception into either
authorization or a definitive role-related violation. Other failures retain the pure
policy's precedence. -/
def needsRoleEvidence (d : Declaration) : DeclarationFailure → Bool
  | .projectAxiom => (nativeParent? d.name).isSome
  | .unknownAxiom => d.axioms.any fun name => (nativeParent? name).isSome
  | .escapeHatch => d.unsafeRecBase.isSome
  | _ => false

/-- Local outcome of a failed declaration: pending fresh role evidence, or a rule. -/
inductive EditorDecision where
  | pending
  | rule (id : RuleId)
  deriving DecidableEq, Repr

/-- Required meaning of the per-declaration decision, for every inventory member and request:
none exactly when `policyFor` passes; pending exactly when its failure needs fresh role
evidence; otherwise the registry rule of that failure. -/
def EditorDecisionContract
    (decide : (i : Inventory) → Roles i → (d : Declaration) → d ∈ i.declarations →
      InspectionRequest → Option EditorDecision) : Prop :=
  ∀ i roles d (member : d ∈ i.declarations) request,
    (decide i roles d member request = none ↔ policyFor i roles d request = none) ∧
    (decide i roles d member request = some .pending ↔
      ∃ f, policyFor i roles d request = some f ∧ needsRoleEvidence d f = true) ∧
    ∀ id, decide i roles d member request = some (.rule id) ↔
      ∃ f, policyFor i roles d request = some f ∧ needsRoleEvidence d f = false ∧
        id = ruleForFailure f

def editorDecisionImpl (i : Inventory) (roles : Roles i) (d : Declaration)
    (member : d ∈ i.declarations) (request : InspectionRequest) : Option EditorDecision :=
  (checked_memberFailure.run i roles d member request).map fun f =>
    if needsRoleEvidence d f then .pending else .rule (ruleForFailure f)

/-- Registers `EditorDecisionContract`, reducing it to `MemberFailureContract`. -/
theorem checked_editorDecision :
    Regula.ExecutableContract editorDecisionImpl EditorDecisionContract :=
  ⟨fun i roles d member request => by
    simp only [editorDecisionImpl, Regula.ExecutableContract.run_eq,
      checked_memberFailure.evidence i roles d member request]
    cases policyFor i roles d request with
    | none => simp
    | some f =>
      cases hf : needsRoleEvidence d f
      · refine ⟨by simp, by simp [hf], fun id => ?_⟩
        simp only [hf, Option.map_some, Option.some.injEq, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun h => ⟨f, rfl, hf, (EditorDecision.rule.inj h).symm⟩,
          fun ⟨_, hg, _, h⟩ => by subst hg; rw [h]⟩
      · refine ⟨by simp, by simp [hf], fun id => ?_⟩
        simp [hf]⟩

/-- The decision for an inventory member, through `checked_editorDecision`. -/
def editorDecision (i : Inventory) (roles : Roles i) (d : Declaration)
    (member : d ∈ i.declarations) (request : InspectionRequest) : Option EditorDecision :=
  checked_editorDecision.run i roles d member request

/-- `EditorDecisionContract` stated about `editorDecision` itself. -/
theorem editorDecision_contract : EditorDecisionContract editorDecision :=
  checked_editorDecision.evidence

/-- Command-line Lean option marking a project audit's own build (`lake lint`'s claimed build
and the audit's fresh frontend elaboration). It is never registered, so its `weak.` form is
dropped from every command scope and no `set_option` can name it; the operational linter reads
it only from a module's import-time options, which precede every source command. -/
def auditBuildOption : Lean.Name := `weak.regula.auditBuild

/-- Required meaning of the live-feedback switch: a command's local findings are emitted
exactly when the module is not an audit build and the command scope's `linter.regula` value is
on. -/
def LiveFeedbackContract (live : Bool → Bool → Bool) : Prop :=
  ∀ auditBuild scopeValue, live auditBuild scopeValue = true ↔
    auditBuild = false ∧ scopeValue = true

def liveFeedbackImpl (auditBuild scopeValue : Bool) : Bool := !auditBuild && scopeValue

/-- Registers `LiveFeedbackContract` about the executed switch. -/
theorem checked_liveFeedback : Regula.ExecutableContract liveFeedbackImpl LiveFeedbackContract :=
  ⟨fun auditBuild scopeValue => by cases auditBuild <;> cases scopeValue <;> decide⟩

/-- Whether a command emits local findings, through `checked_liveFeedback`. -/
def liveFeedback (auditBuild scopeValue : Bool) : Bool :=
  checked_liveFeedback.run auditBuild scopeValue

/-- In an audit build no command scope's `linter.regula` value, including a source
`set_option linter.regula true`, turns local feedback on. -/
theorem liveFeedback_auditBuild (scopeValue : Bool) : liveFeedback true scopeValue = false :=
  Bool.eq_false_iff.mpr fun h => nomatch ((checked_liveFeedback.evidence true scopeValue).mp h).1

end Regula.Linter
