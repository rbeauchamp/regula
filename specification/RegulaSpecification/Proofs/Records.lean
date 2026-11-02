import RegulaSpecification.Proofs.Foundation

/-!
# Each rule function meets its intent record

`rgN_cases` applies the rule's witnesses (`Witnessed`) to the function the checker runs, so a function that reports
nothing, or everything, cannot be the one that runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

theorem cases_of_meets {α S : Type} [Admission α] {rule : String} {V : α → S → Prop}
    (w : Witnessed V) {f : Checker α S} (hf : (ruleRecord rule V).Meets f) :
    w.bad ∈ f ⟨w.refused, w.refused_wf⟩ ∧ w.fine ∉ f ⟨w.admitted, w.admitted_wf⟩ := by
  rw [meets_iff] at hf
  exact ⟨(hf _ _).mpr w.bad_violates, fun h => w.fine_admitted ((hf _ _).mp h)⟩

end Link

open Link

/-- The function of RG1001 over the specification's input. -/
def rg1001Checker : Checker Input Name := fun s =>
  (ofAdmitted s).tables.rg1001.map (·.subject)
/-- The function of RG1002 over the specification's input. -/
def rg1002Checker : Checker Input Name := fun s =>
  (ofAdmitted s).tables.rg1002.map (·.subject)
/-- The function of RG1003 over the specification's input. -/
def rg1003Checker : Checker Input Name := fun s =>
  (ofAdmitted s).tables.rg1003.map (·.subject)
/-- The function of RG1004 over the specification's input. -/
def rg1004Checker : Checker Input Name := fun s =>
  (ofAdmitted s).tables.rg1004.map (·.subject)
/-- The function of RG1005 over the specification's input. -/
def rg1005Checker : Checker Input Name := fun s =>
  (ofAdmitted s).tables.rg1005.map (·.subject)
/-- The function of RG1006 over the specification's input. -/
def rg1006Checker : Checker Input Name := fun s =>
  (ofAdmitted s).tables.rg1006.map (·.subject)

theorem rg1001_meets : rg1001.Meets rg1001Checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := rg1001_exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

theorem rg1002_meets : rg1002.Meets rg1002Checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := rg1002_exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

theorem rg1003_meets : rg1003.Meets rg1003Checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := rg1003_exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

theorem rg1004_meets : rg1004.Meets rg1004Checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := rg1004_exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

theorem rg1005_meets : rg1005.Meets rg1005Checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := rg1005_exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

theorem rg1006_meets : rg1006.Meets rg1006Checker := by
  refine (meets_iff _).mpr fun s c => ?_
  have := rg1006_exact (ofAdmitted s).tables c
  rwa [toSpec_ofAdmitted] at this

theorem rg1001_cases :
    Witnesses.w1001.bad ∈ rg1001Checker ⟨Witnesses.w1001.refused, Witnesses.w1001.refused_wf⟩ ∧
      Witnesses.w1001.fine ∉
        rg1001Checker ⟨Witnesses.w1001.admitted, Witnesses.w1001.admitted_wf⟩ :=
  cases_of_meets Witnesses.w1001 rg1001_meets
theorem rg1002_cases :
    Witnesses.w1002.bad ∈ rg1002Checker ⟨Witnesses.w1002.refused, Witnesses.w1002.refused_wf⟩ ∧
      Witnesses.w1002.fine ∉
        rg1002Checker ⟨Witnesses.w1002.admitted, Witnesses.w1002.admitted_wf⟩ :=
  cases_of_meets Witnesses.w1002 rg1002_meets
theorem rg1003_cases :
    Witnesses.w1003.bad ∈ rg1003Checker ⟨Witnesses.w1003.refused, Witnesses.w1003.refused_wf⟩ ∧
      Witnesses.w1003.fine ∉
        rg1003Checker ⟨Witnesses.w1003.admitted, Witnesses.w1003.admitted_wf⟩ :=
  cases_of_meets Witnesses.w1003 rg1003_meets
theorem rg1004_cases :
    Witnesses.w1004.bad ∈ rg1004Checker ⟨Witnesses.w1004.refused, Witnesses.w1004.refused_wf⟩ ∧
      Witnesses.w1004.fine ∉
        rg1004Checker ⟨Witnesses.w1004.admitted, Witnesses.w1004.admitted_wf⟩ :=
  cases_of_meets Witnesses.w1004 rg1004_meets
theorem rg1005_cases :
    Witnesses.w1005.bad ∈ rg1005Checker ⟨Witnesses.w1005.refused, Witnesses.w1005.refused_wf⟩ ∧
      Witnesses.w1005.fine ∉
        rg1005Checker ⟨Witnesses.w1005.admitted, Witnesses.w1005.admitted_wf⟩ :=
  cases_of_meets Witnesses.w1005 rg1005_meets
theorem rg1006_cases :
    Witnesses.w1006.bad ∈ rg1006Checker ⟨Witnesses.w1006.refused, Witnesses.w1006.refused_wf⟩ ∧
      Witnesses.w1006.fine ∉
        rg1006Checker ⟨Witnesses.w1006.admitted, Witnesses.w1006.admitted_wf⟩ :=
  cases_of_meets Witnesses.w1006 rg1006_meets

theorem rg1006_checker_refuses_loop {l : Name} (hl : l ∈ loopConstructs) :
    `Good.l ∈ rg1006Checker ⟨Witnesses.withLoop hl, Witnesses.wf_withLoop hl⟩ :=
  ((meets_iff _).mp rg1006_meets _ _).mpr (Witnesses.rg1006_refuses_loop hl)

theorem rg1006_checker_refuses_forged_name :
    `Good.g._unsafe_rec ∈ rg1006Checker ⟨Witnesses.withForged, Witnesses.wf_withForged⟩ :=
  ((meets_iff _).mp rg1006_meets _ _).mpr Witnesses.rg1006_refuses_forged_name

end RegulaSpecification
