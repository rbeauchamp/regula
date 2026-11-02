import RegulaSpecification.Proofs.Records

/-!
# The verdict, against its statement
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

open Link

/-- The verdict of a reading, by the two functions that the checker runs on it: the admission, and the decision on
what the admission gives. -/
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

theorem nil_iff_no_subject (fs : List Regula.Closed.Finding) :
    fs = [] ↔ ∀ s, s ∉ fs.map (·.subject) := by
  cases fs with
  | nil => simp
  | cons f fs =>
    constructor
    · intro h
      cases h
    · intro h
      exact absurd (List.mem_cons_self ..) (h f.subject)

theorem findings_nil_iff (i : Regula.Closed.Input) :
    i.findings = [] ↔ AllHold (toSpec i) := by
  have hall : i.findings = [] ↔ ∀ r, i.tables.check r = [] := by
    simp only [Regula.Closed.Input.findings, List.flatMap_eq_nil_iff]
    exact ⟨fun h r => h r (Regula.RuleId.mem_all r), fun h r _ => h r⟩
  rw [hall]
  constructor
  · intro hn
    have at' : ∀ r s, s ∉ (i.tables.check r).map (·.subject) :=
      fun r => (nil_iff_no_subject _).mp (hn r)
    exact ⟨fun c hv => at' .projectAxiom c ((rg1001_exact i.tables c).mpr hv),
      fun c hv => at' .proofHole c ((rg1002_exact i.tables c).mpr hv),
      fun c hv => at' .unknownAxiom c ((rg1003_exact i.tables c).mpr hv),
      fun c hv => at' .nativeProof c ((rg1004_exact i.tables c).mpr hv),
      fun c hv => at' .profileExceeded c ((rg1005_exact i.tables c).mpr hv),
      fun c hv => at' .escapeHatch c ((rg1006_exact i.tables c).mpr hv)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩ r
    refine (nil_iff_no_subject _).mpr fun s hs => ?_
    cases r
    · exact h1 s ((rg1001_exact i.tables s).mp hs)
    · exact h2 s ((rg1002_exact i.tables s).mp hs)
    · exact h3 s ((rg1003_exact i.tables s).mp hs)
    · exact h4 s ((rg1004_exact i.tables s).mp hs)
    · exact h5 s ((rg1005_exact i.tables s).mp hs)
    · exact h6 s ((rg1006_exact i.tables s).mp hs)
    · simp [Regula.Closed.Tables.check] at hs
    · simp [Regula.Closed.Tables.check] at hs

theorem report_complete (i : Regula.Closed.Input) :
    i.report.verdict ≠ .incomplete ∧
      (i.report.verdict = .pass ↔ AllHold (toSpec i)) := by
  rw [← findings_nil_iff]
  simp only [Regula.Closed.Input.report]
  cases i.findings <;> simp [Regula.Closed.Report.verdict]

theorem report_findings (i : Regula.Closed.Input) : i.report.findings = i.findings := by
  simp only [Regula.Closed.Input.report]
  cases i.findings <;> rfl

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

/-- The checker's verdict over the specification's input, with `none` for a build that the shell
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

theorem rule_spellings :
    Regula.RuleId.all.map (·.spelling) =
      ["RG1001", "RG1002", "RG1003", "RG1004", "RG1005", "RG1006", "RG1010", "RG2001"] := rfl

end RegulaSpecification
