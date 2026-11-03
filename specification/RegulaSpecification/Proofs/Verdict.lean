import RegulaSpecification.CasesGate

/-!
# The verdict, against its statement
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

open Link

/-- The verdict of a reading, by the two functions that the checker runs on it: the admission, and the decision
on what the admission gives. -/
def run (d : Regula.Closed.Draft) : Regula.Closed.Report :=
  Regula.Closed.decision d.admit

theorem admit_toDraft {d : Regula.Closed.Draft} {i : Regula.Closed.Input}
    (h : d.admit = .ok i) : i.toDraft = d := by
  simp only [Regula.Closed.Draft.admit] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      exact h ▸ rfl

theorem admit_ok_iff (d : Regula.Closed.Draft) :
    (∃ i, d.admit = .ok i) ↔ (toSpecDraft d).WellFormed := by
  rw [wf_toSpecDraft_iff]
  constructor
  · rintro ⟨i, hi⟩
    have ht := admit_toDraft hi
    subst ht
    exact ⟨i.closed, i.claims⟩
  · rintro ⟨hc, hm⟩
    have hn := d.openMention?_eq_none.mpr hc
    simp only [Regula.Closed.Draft.admit]
    split
    · rename_i h
      rw [hn] at h
      cases h
    · split
      · exact absurd ‹_› hm
      · exact ⟨_, rfl⟩

theorem admit_error_iff (d : Regula.Closed.Draft) :
    (∃ why, d.admit = .error why) ↔ ¬ (toSpecDraft d).WellFormed := by
  rw [← admit_ok_iff]
  cases d.admit with
  | error why => simp
  | ok i => simp

theorem run_refused {d : Regula.Closed.Draft} (h : ¬ (toSpecDraft d).WellFormed) :
    (run d).verdict = .incomplete := by
  obtain ⟨why, hw⟩ := (admit_error_iff d).mpr h
  simp only [run, hw, Regula.Closed.decision, Regula.Closed.Report.verdict]

theorem run_complete {d : Regula.Closed.Draft} (h : (toSpecDraft d).WellFormed) :
    (run d).verdict ≠ .incomplete ∧
      ((run d).verdict = .pass ↔ AllHold (toSpecDraft d)) := by
  obtain ⟨i, hi⟩ := (admit_ok_iff d).mpr h
  have ht := admit_toDraft hi
  subst ht
  simp only [run, hi, Regula.Closed.decision]
  exact report_complete i

theorem run_pass_admitted {d : Regula.Closed.Draft}
    (hp : (run d).verdict = .pass) : (toSpecDraft d).WellFormed :=
  Classical.byContradiction fun hn => by
    rw [run_refused hn] at hp
    cases hp

theorem run_pass_iff {d : Regula.Closed.Draft} :
    (run d).verdict = .pass ↔
      (toSpecDraft d).WellFormed ∧ AllHold (toSpecDraft d) := by
  constructor
  · intro hp
    have hw := run_pass_admitted hp
    exact ⟨hw, (run_complete hw).2.mp hp⟩
  · rintro ⟨hw, ha⟩
    exact (run_complete hw).2.mpr ha

/-- The verdict of the checker in the specification. -/
def verdict : Regula.Closed.Verdict → Verdict
  | .pass => .pass
  | .fail => .fail
  | .incomplete => .incomplete

/-- The checker's verdict over the specification's input, with {name}`none` for a build that the shell
cannot load. -/
def runChecker : Option Input → Verdict
  | none => .incomplete
  | some s => verdict (run (ofSpec s)).verdict

theorem run_meets : gateRecord.Meets runChecker := by
  rw [gate_meets_iff]
  refine ⟨rfl, fun s hs => ?_, fun s hs => ?_⟩
  · have hr : ¬ (toSpecDraft (ofSpec s)).WellFormed := by rwa [toSpecDraft_ofSpec]
    simp [runChecker, run_refused hr, verdict]
  · have hs' : (toSpecDraft (ofSpec s)).WellFormed := by rwa [toSpecDraft_ofSpec]
    obtain ⟨hn, hp⟩ := run_complete hs'
    rw [toSpecDraft_ofSpec] at hp
    simp only [runChecker]
    constructor
    · cases hv : (run (ofSpec s)).verdict <;> simp_all [verdict]
    · rw [← hp]
      cases (run (ofSpec s)).verdict <;> simp [verdict]

end RegulaSpecification
