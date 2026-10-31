import RegulaSpecification.Proofs.Foundation

/-!
# Each rule function meets its intent record

For each rule, `rgN_meets` proves that the function the checker runs meets the rule's intent record:
on each well-formed input of the specification, it reports a subject exactly when the subject
violates the rule. `rgN_cases` applies the rule's witnesses (`Witnessed`) to the function itself: it
reports the case that the rule must refuse, and it does not report the case that the rule must
admit. So a function that reports nothing, or everything, cannot be the one that runs.

The function runs over `Regula.Closed.Input`, so its record reads it through `ofSpec`. The theorems
`rgN_exact` state it for each input of the checker at `toSpec`.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

/-- The input of the checker made from a well-formed input of the specification has the closed
form. -/
theorem wf_ofSpec {s : Input} (h : s.WellFormed) : (toSpec (ofSpec s)).WellFormed := by
  rwa [toSpec_ofSpec]

/-- A function that meets a record reports the case that the record refuses, and it does not report
the case that the record admits. -/
theorem cases_of_meets {α S : Type} [Admission α] {rule : String} {V : α → S → Prop}
    (w : Witnessed V) {f : Checker α S} (hf : (ruleRecord rule V).Meets f) :
    w.bad ∈ f w.refused ∧ w.fine ∉ f w.admitted := by
  rw [meets_iff] at hf
  exact ⟨(hf _ w.refused_wf _).mpr w.bad_violates,
    fun h => w.fine_admitted ((hf _ w.admitted_wf _).mp h)⟩

end Link

open Link

/-- The function of RG1001 over the specification's input. -/
def rg1001Checker : Checker Input Name := fun s =>
  (ofSpec s).tables.rg1001.map (·.subject)
/-- The function of RG1002 over the specification's input. -/
def rg1002Checker : Checker Input Name := fun s =>
  (ofSpec s).tables.rg1002.map (·.subject)
/-- The function of RG1003 over the specification's input. -/
def rg1003Checker : Checker Input Name := fun s =>
  (ofSpec s).tables.rg1003.map (·.subject)
/-- The function of RG1004 over the specification's input. -/
def rg1004Checker : Checker Input Name := fun s =>
  (ofSpec s).tables.rg1004.map (·.subject)
/-- The function of RG1005 over the specification's input. -/
def rg1005Checker : Checker Input Name := fun s =>
  (ofSpec s).tables.rg1005.map (·.subject)
/-- The function of RG1006 over the specification's input. -/
def rg1006Checker : Checker Input Name := fun s =>
  (ofSpec s).tables.rg1006.map (·.subject)

theorem rg1001_meets : rg1001.Meets rg1001Checker := by
  unfold rg1001
  rw [meets_iff]
  intro s _ c
  have := rg1001_exact (ofSpec s) c
  rwa [toSpec_ofSpec] at this

theorem rg1002_meets : rg1002.Meets rg1002Checker := by
  unfold rg1002
  rw [meets_iff]
  intro s _ c
  have := rg1002_exact (ofSpec s) c
  rwa [toSpec_ofSpec] at this

theorem rg1003_meets : rg1003.Meets rg1003Checker := by
  unfold rg1003
  rw [meets_iff]
  intro s h c
  have := rg1003_exact (unique_of_wf (wf_ofSpec h)) c
  rwa [toSpec_ofSpec] at this

theorem rg1004_meets : rg1004.Meets rg1004Checker := by
  unfold rg1004
  rw [meets_iff]
  intro s _ c
  have := rg1004_exact (ofSpec s) c
  rwa [toSpec_ofSpec] at this

theorem rg1005_meets : rg1005.Meets rg1005Checker := by
  unfold rg1005
  rw [meets_iff]
  intro s h c
  have := rg1005_exact (unique_of_wf (wf_ofSpec h)) c
  rwa [toSpec_ofSpec] at this

theorem rg1006_meets : rg1006.Meets rg1006Checker := by
  unfold rg1006
  rw [meets_iff]
  intro s h c
  have := rg1006_exact (unique_of_wf (wf_ofSpec h)) c
  rwa [toSpec_ofSpec] at this

/-! ## The case each function must refuse, and the case it must admit -/

theorem rg1001_cases :
    Witnesses.w1001.bad ∈ rg1001Checker Witnesses.w1001.refused ∧
      Witnesses.w1001.fine ∉ rg1001Checker Witnesses.w1001.admitted :=
  cases_of_meets Witnesses.w1001 rg1001_meets
theorem rg1002_cases :
    Witnesses.w1002.bad ∈ rg1002Checker Witnesses.w1002.refused ∧
      Witnesses.w1002.fine ∉ rg1002Checker Witnesses.w1002.admitted :=
  cases_of_meets Witnesses.w1002 rg1002_meets
theorem rg1003_cases :
    Witnesses.w1003.bad ∈ rg1003Checker Witnesses.w1003.refused ∧
      Witnesses.w1003.fine ∉ rg1003Checker Witnesses.w1003.admitted :=
  cases_of_meets Witnesses.w1003 rg1003_meets
theorem rg1004_cases :
    Witnesses.w1004.bad ∈ rg1004Checker Witnesses.w1004.refused ∧
      Witnesses.w1004.fine ∉ rg1004Checker Witnesses.w1004.admitted :=
  cases_of_meets Witnesses.w1004 rg1004_meets
theorem rg1005_cases :
    Witnesses.w1005.bad ∈ rg1005Checker Witnesses.w1005.refused ∧
      Witnesses.w1005.fine ∉ rg1005Checker Witnesses.w1005.admitted :=
  cases_of_meets Witnesses.w1005 rg1005_meets
theorem rg1006_cases :
    Witnesses.w1006.bad ∈ rg1006Checker Witnesses.w1006.refused ∧
      Witnesses.w1006.fine ∉ rg1006Checker Witnesses.w1006.admitted :=
  cases_of_meets Witnesses.w1006 rg1006_meets

/-- The function that the checker runs reports a claimed constant whose value mentions a loop
construct. -/
theorem rg1006_checker_refuses_loop {l : Name} (hl : l ∈ loopConstructs) :
    `Good.l ∈ rg1006Checker (Witnesses.withLoop l) := by
  have hm := rg1006_meets
  unfold rg1006 at hm
  rw [meets_iff] at hm
  exact (hm _ (Witnesses.wf_withLoop hl) _).mpr (Witnesses.rg1006_refuses_loop hl)

end RegulaSpecification
