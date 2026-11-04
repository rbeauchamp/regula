import RegulaSpecification.Rules.RG1001
import RegulaSpecification.Rules.RG1002
import RegulaSpecification.Rules.RG1003
import RegulaSpecification.Rules.RG1004
import RegulaSpecification.Rules.RG1005
import RegulaSpecification.Rules.RG1006
import RegulaSpecification.Rules.RG1011
import RegulaSpecification.Rules.RG1012
import Regula.Rules

/-!
# The registry of the rules' statements

One line for each rule: the rule that the checker runs, with its statement, its proof and its cases
({name (full := RegulaSpecification.Proved)}`Proved`). {lit}`registry_rules` proves that this list and the checker's registry
({name}`Regula.Closed.registry`) are one, in their order, so a rule that one of them holds and the other does not
stops the build.

So the theorem that the checker proves once, that a run passes exactly when no registered rule reports a subject
({name}`Regula.Closed.report_pass_iff`), states here that a run passes exactly when every rule's statement
holds ({lit}`AllHold`, {lit}`findings_nil_iff`). Each registered rule's own refused case shows a finding of that rule
in the run's findings ({lit}`registered_found`), so a run that dropped one rule's findings would not be the run whose
findings these theorems state.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The rules' statements, in the order of the checker's registry. -/
def registry : List Proved :=
  [rg1001Proved, rg1002Proved, rg1003Proved, rg1004Proved, rg1005Proved, rg1006Proved, rg1011Proved,
    rg1012Proved]

/-- The specification's registry and the checker's are one list of rules, in one order. -/
theorem registry_rules : registry.map (·.rule) = Regula.Closed.registry := rfl

/-- Every rule that reads the input holds of it. -/
def AllHold (i : Input) : Prop := ∀ p ∈ registry, ∀ c, ¬ p.Violates i c

open Link in
theorem findings_nil_iff (i : Regula.Closed.Input) :
    i.findings = [] ↔ AllHold (toSpec i) := by
  rw [Regula.Closed.findings_eq_nil_iff, ← registry_rules]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, AllHold]
  refine forall₂_congr fun p _ => ?_
  rw [nil_iff_no_subject]
  exact forall_congr' fun c => not_congr (p.exact i.tables c)

theorem report_complete (i : Regula.Closed.Input) :
    i.report.verdict ≠ .incomplete ∧
      (i.report.verdict = .pass ↔ AllHold (Link.toSpec i)) :=
  ⟨Regula.Closed.report_not_incomplete i,
    (Regula.Closed.report_pass_iff i).trans ((Regula.Closed.findings_eq_nil_iff i).symm.trans (findings_nil_iff i))⟩

open Link in
/-- Each registered rule's refused case gives a finding of that rule, on its subject, among the run's findings. -/
theorem registered_found (p : Proved) (hp : p ∈ registry) :
    ∃ i : Regula.Closed.Input, ∃ f ∈ i.findings, f.rule = p.rule.spelling ∧ f.subject = p.cases.bad := by
  let i := ofAdmitted ⟨p.cases.refused, p.cases.refused_wf⟩
  have hv : p.Violates (toSpec i) p.cases.bad := by
    rw [toSpec_ofAdmitted]
    exact p.cases.bad_violates
  obtain ⟨v, hv, hs⟩ := List.mem_map.mp ((p.exact i.tables p.cases.bad).mpr hv)
  have hr : p.rule ∈ Regula.Closed.registry := registry_rules ▸ List.mem_map_of_mem hp
  exact ⟨i, _, Regula.Closed.mem_findings.mpr ⟨p.rule, hr, v, hv, rfl⟩, rfl, hs⟩

/-- The spellings of the registered rules. RG1010 and RG2001 are no rules of the registry: the language check
and the refusal of a build that the checker cannot read print them ({lit}`proof_verdict_lines`, {lit}`full_gate_lines`). -/
theorem rule_spellings :
    Regula.Closed.registry.map (·.spelling) =
      ["RG1001", "RG1002", "RG1003", "RG1004", "RG1005", "RG1006", "RG1011", "RG1012"] := rfl

end RegulaSpecification
