module

public import RegulaSpecification.Rules.RG1001
public import RegulaSpecification.Rules.RG1002
public import RegulaSpecification.Rules.RG1003
public import RegulaSpecification.Rules.RG1004
public import RegulaSpecification.Rules.RG1005
public import RegulaSpecification.Rules.RG1006
public import RegulaSpecification.Rules.RG1011
public import RegulaSpecification.Rules.RG1012
public import RegulaSpecification.Rules.RG1013
public import Regula.Rules
import all Regula.Rule
import all Regula.Rules

/-!
# The registry of the rules' statements

One line for each rule: the rule that the checker runs, with its statement, its proofs and its cases
({name (full := RegulaSpecification.Proved)}`Proved`). {lit}`registry_rules` proves that this list and the checker's registry
({name}`Regula.Closed.registry`) are one, in their order, so a rule that one of them holds and the other does not
stops the build.

So the theorem that the checker proves once, that a run passes exactly when no registered rule reports a subject
({name}`Regula.Closed.report_pass_iff`), states here that a run passes exactly when every rule's statement
holds ({lit}`AllHold`, {lit}`findings_nil_iff`). Each registered rule's own refused case shows a finding of that rule
in the run's findings ({lit}`registered_found`), so a run that dropped one rule's findings would not be the run whose
findings these theorems state.
-/

@[expose] public section

namespace RegulaSpecification

open Lean (Name)

/-- The rules' statements, in the order of the checker's registry. -/
def registry : List Proved :=
  [rg1001Proved, rg1002Proved, rg1003Proved, rg1004Proved, rg1005Proved, rg1006Proved, rg1011Proved,
    rg1012Proved, rg1013Proved]

/-- The specification's registry and the checker's are one list of rules, in one order. -/
theorem registry_rules : registry.map (·.rule) = Regula.Closed.registry := by rfl

/-- Every rule that reads the input holds of it. -/
def AllHold (i : Input) : Prop := ∀ p ∈ registry, ∀ c, ¬ p.Violates i c

open Link in
theorem tables_findings_nil_iff {i : Regula.Closed.Input} (t : Regula.Closed.Tables i) :
    t.findings = [] ↔ AllHold (toSpec i) := by
  rw [Regula.Closed.Tables.findings_eq_nil_iff, ← registry_rules]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, AllHold]
  refine forall₂_congr fun p _ => ?_
  rw [nil_iff_no_subject]
  exact forall_congr' fun c => not_congr (p.exact t c)

open Link in
theorem findings_nil_iff (i : Regula.Closed.Input) :
    i.findings = [] ↔ AllHold (toSpec i) :=
  tables_findings_nil_iff i.tables

theorem tables_report_complete {i : Regula.Closed.Input} (t : Regula.Closed.Tables i) :
    t.report.verdict ≠ .incomplete ∧
      (t.report.verdict = .pass ↔ AllHold (Link.toSpec i)) :=
  ⟨Regula.Closed.Tables.report_not_incomplete t,
    (Regula.Closed.Tables.report_pass_iff t).trans
      ((Regula.Closed.Tables.findings_eq_nil_iff t).symm.trans (tables_findings_nil_iff t))⟩

theorem report_complete (i : Regula.Closed.Input) :
    i.report.verdict ≠ .incomplete ∧
      (i.report.verdict = .pass ↔ AllHold (Link.toSpec i)) :=
  tables_report_complete i.tables

open Link in
/-- Each registered rule's refused case gives a finding of that rule, on its subject, among the run's findings. -/
theorem registered_found (p : Proved) (hp : p ∈ registry) :
    ∃ i : Regula.Closed.Input, ∃ f ∈ i.findings, f.rule = p.rule.spelling ∧ f.subject.name = p.cases.bad := by
  let i := ofAdmitted ⟨p.cases.refused, p.cases.refused_wf⟩
  have hv : p.Violates (toSpec i) p.cases.bad := by
    rw [toSpec_ofAdmitted]
    exact p.cases.bad_violates
  obtain ⟨v, hv, hs⟩ := List.mem_map.mp ((p.exact i.tables p.cases.bad).mpr hv)
  have hr : p.rule ∈ Regula.Closed.registry := registry_rules ▸ List.mem_map_of_mem hp
  exact ⟨i, _, Regula.Closed.mem_findings.mpr ⟨p.rule, hr, v, hv, rfl⟩, rfl, hs⟩

/-- Every finding of RG1013 has a module subject for a claimed module. Every finding of RG1011 has a constant
subject carrying the name and the module of a declaration of a claimed module or, for its {attr}`@[csimp]`
clause, the theorem of a claimed module's exported {attr}`@[csimp]` entry that no claimed module declares, with
that claimed module. Every finding of another registered rule has a constant subject carrying the declaration's
own name and module. -/
theorem finding_subject {i : Regula.Closed.Input} {f : Regula.Closed.Finding} (hf : f ∈ i.findings) :
    (f.rule ∉ ["RG1011", "RG1013"] ∧ ∃ d ∈ i.decls, f.subject = .constant d.name d.module) ∨
      (f.rule = "RG1013" ∧ ∃ m ∈ i.modules, f.subject = .module m) ∨
      (f.rule = "RG1011" ∧
        ((∃ d ∈ i.decls, d.module ∈ i.modules ∧ f.subject = .constant d.name d.module) ∨
          ∃ e ∈ i.csimps, e.module ∈ i.modules ∧ e.thm ∉ i.claimedConstants ∧
            f.subject = .constant e.thm e.module)) := by
  obtain ⟨r, hr, v, hv, rfl⟩ := Regula.Closed.mem_findings.mp hf
  rw [← registry_rules] at hr
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hr
  exact p.subject i.tables v hv

open Link in
/-- Each claimed module that registers an exported {attr}`@[csimp]` entry on a theorem that no claimed module
declares has a finding of RG1011 among the run's findings, on that theorem with that module. -/
theorem foreignCSimp_found {i : Regula.Closed.Input} {c m : Name} (h : ForeignCSimpIn (toSpec i) m c) :
    ∃ f ∈ i.findings, f.rule = "RG1011" ∧ f.subject = .constant c m := by
  obtain ⟨v, hv, hs⟩ := List.mem_map.mp ((rg1011_attributed i.tables c m).mpr (.inr h))
  exact ⟨_, Regula.Closed.mem_findings.mpr
    ⟨Regula.Rules.RG1011.rule, by simp [Regula.Closed.registry], v, hv, rfl⟩, rfl, hs⟩

/-- The spellings of the registered rules. RG1010 and RG2001 are no rules of the registry: the language check
and the refusal of a build that the checker cannot read print them ({lit}`proof_verdict_lines`, {lit}`full_gate_lines`). -/
theorem rule_spellings :
    Regula.Closed.registry.map (·.spelling) =
      ["RG1001", "RG1002", "RG1003", "RG1004", "RG1005", "RG1006", "RG1011", "RG1012", "RG1013"] := by rfl

/-- Every finding produced by the registered rules carries non-empty, non-blank fix guidance
(enforced intrinsically by {name}`Regula.Closed.Guidance`). -/
theorem finding_guidance_nonblank (i : Regula.Closed.Input) :
    ∀ f ∈ i.findings, f.guidance.text ≠ "" ∧ ∃ c ∈ f.guidance.text.toList, c.isWhitespace = false :=
  fun f _ => ⟨f.guidance.text_ne_empty, f.guidance.exists_nonwhitespace⟩

end RegulaSpecification
