module

public import RegulaSpecification.Rule
public import Regula.Rules.RG1013
import all Regula.Rule
import all Regula.Rules.RG1013

/-!
# RG1013: files that are not {lit}`module` files

A claimed module is not one of the loaded modules that Lean read as a {lit}`module` file. The subject is the
module, and the rule reads no constant, so it reports a claimed module that holds none.
{name (full := Regula.Rules.RG1013.check)}`Regula.Rules.RG1013.check` is the function that the checker runs.
-/

@[expose] public section

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- RG1013: Lean did not read the file of a claimed module as a {lit}`module` file. -/
def Violates1013 (i : Input) (m : Name) : Prop :=
  i.ClaimedModule m ∧ ¬ i.ModuleFile m

/-- The intent record of RG1013. -/
def rg1013 := ruleRecord "RG1013" Violates1013

namespace Witnesses

/-- The compliant project with one more claimed module, {lit}`Bad`, which holds no constant and is no
{lit}`module` file. -/
def withPlainModule : Input := { base with modules := [`Good, `Bad] }

/-- The cases of RG1013. -/
def w1013 : Witnessed Violates1013 where
  support i := i.modules
  support_complete _ _ h := h.1
  refused := withPlainModule
  refused_wf := ⟨fun d hd u hu => wf_base.closed d hd u hu, by simp [withPlainModule]⟩
  bad := `Bad
  bad_violates := ⟨by simp [withPlainModule, Input.ClaimedModule],
    by simp [withPlainModule, base, Input.ModuleFile]⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good
  fine_admitted := fun h => h.2 (by simp [base, Input.ModuleFile])

theorem rg1013_adequate : O2 rg1013 ∧ O2Run rg1013 ∧ O3 rg1013 ∧ O4 rg1013 ∧
    O5 rg1013 (.rel SameReports) := adequate w1013

theorem rg1013_noisy : ¬ rg1013.Meets w1013.candidates :=
  noisy_fails w1013 (by simp [w1013, base])

/-- The rule reads the claimed modules and the {lit}`module` files, and nothing else of the input: two inputs
that agree on both have the same violations, whatever their constants and their profiles. -/
theorem rg1013_reads_modules {i j : Input} (hm : i.modules = j.modules)
    (hf : i.moduleFiles = j.moduleFiles) (m : Name) : Violates1013 i m ↔ Violates1013 j m := by
  simp [Violates1013, Input.ClaimedModule, Input.ModuleFile, hm, hf]

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem rg1013_exact (s : Name) :
    s ∈ (Regula.Rules.RG1013.check t).map (·.subject.name) ↔ Violates1013 (toSpec i) s := by
  unfold Regula.Rules.RG1013.check
  rw [mem_report (sub := id) (fun _ => rfl)]
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Regula.Closed.mem_setOf]
  simp [Violates1013, Input.ClaimedModule, Input.ModuleFile, toSpec, toSpecDraft]

theorem rg1013_subject {v : Regula.Closed.Violation} (hv : v ∈ Regula.Rules.RG1013.check t) :
    ∃ m ∈ i.modules, v.subject = .module m := by
  unfold Regula.Rules.RG1013.check at hv
  obtain ⟨m, hm, -, rfl⟩ := mem_report_violation hv
  exact ⟨m, hm, rfl⟩

end Link

/-- RG1013 with its statement, its proofs and its cases, for the registry. -/
def rg1013Proved : Proved :=
  ⟨Regula.Rules.RG1013.rule, Violates1013, Link.rg1013_exact, Witnesses.w1013,
    fun t _ hv => .inr (.inl ⟨rfl, Link.rg1013_subject t hv⟩)⟩

/-- The function of RG1013 over the specification's input. -/
def rg1013Checker : Checker Input Name := rg1013Proved.checker

theorem rg1013_meets : rg1013.Meets rg1013Checker := rg1013Proved.meets "RG1013"

theorem rg1013_cases :
    Witnesses.w1013.bad ∈ rg1013Checker ⟨Witnesses.w1013.refused, Witnesses.w1013.refused_wf⟩ ∧
      Witnesses.w1013.fine ∉
        rg1013Checker ⟨Witnesses.w1013.admitted, Witnesses.w1013.admitted_wf⟩ :=
  rg1013Proved.cases_hold

end RegulaSpecification
