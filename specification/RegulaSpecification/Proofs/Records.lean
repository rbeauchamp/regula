import RegulaSpecification.Proofs.Contracts
import RegulaSpecification.Proofs.Project
import RegulaSpecification.ClosedSubset

/-!
# Each rule function meets its intent record

For each rule that leaf #487 implements, `rgN_meets` proves that the function the checker runs meets
the rule's intent record: on each well-formed input of the specification, it reports a subject exactly
when the subject violates the rule. `rgN_cases` applies the rule's witnesses (`Witnessed`) to the
function itself: it reports the case that the rule must refuse, and it does not report the case that
the rule must admit. So a function that reports nothing, or everything, cannot be the one that runs.

The function runs over `Regula.Closed.Input`, so its record reads it through `ofSpec`. The theorems
`rgN_exact` state it for each input of the checker at `toSpec`.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

/-- `Reaches` reads only the constants. -/
theorem reaches_congr {a b : Input} (h : a.decls = b.decls) {x y : Name} (hr : a.Reaches x y) :
    b.Reaches x y := by
  induction hr with
  | refl => exact .refl _
  | step d hd hn hu _ ih => exact .step d (h ▸ hd) hn hu ih

/-- `Executes` reads only the constants. -/
theorem executes_congr {a b : Input} (h : a.decls = b.decls) {x y : Name} (hr : a.Executes x y) :
    b.Executes x y := by
  induction hr with
  | root => exact .root _
  | step d _ hd hn hu ih => exact .step d ih (h ▸ hd) hn hu

/-- `DepartsTo` reads only the constants. -/
theorem departsTo_congr {a b : Input} (h : a.decls = b.decls) {x y : Name} (hr : a.DepartsTo x y) :
    b.DepartsTo x y := by
  induction hr with
  | one hd => exact .one (by simpa only [Input.Departs, h] using hd)
  | more hd _ ih => exact .more (by simpa only [Input.Departs, h] using hd) ih

theorem restrict_decls (s : Input) : (restrict s).decls = s.decls := rfl

theorem restrict_reaches (s : Input) (x y : Name) : (restrict s).Reaches x y ↔ s.Reaches x y :=
  ⟨reaches_congr (restrict_decls s), reaches_congr (restrict_decls s).symm⟩

theorem restrict_executes (s : Input) (x y : Name) : (restrict s).Executes x y ↔ s.Executes x y :=
  ⟨executes_congr (restrict_decls s), executes_congr (restrict_decls s).symm⟩

theorem restrict_departsTo (s : Input) (x y : Name) : (restrict s).DepartsTo x y ↔ s.DepartsTo x y :=
  ⟨departsTo_congr (restrict_decls s), departsTo_congr (restrict_decls s).symm⟩

theorem restrict_axiomOf (s : Input) (x y : Name) : (restrict s).AxiomOf x y ↔ s.AxiomOf x y :=
  and_congr (restrict_reaches s x y) Iff.rfl

theorem restrict_wf {s : Input} (h : s.WellFormed) : (restrict s).WellFormed :=
  ⟨h.unique, h.closed, h.loaded⟩

/-- The correspondences of the restriction are those of the input. -/
theorem restrict_corresponds (s : Input) (p : Profile) (x : Departure) :
    (restrict s).Corresponds p x ↔ s.Corresponds p x := by
  have hadm : ∀ t, (restrict s).AdmittedProof p t ↔ s.AdmittedProof p t := by
    intro t
    simp only [Input.AdmittedProof, restrict_axiomOf]
    exact Iff.rfl
  constructor
  · rintro ⟨q, hq, hs, ha⟩
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
    obtain ⟨q0, hq0, hg⟩ := List.mem_filterMap.mp hc
    unfold correspondence' at hg
    split at hg
    · rename_i r g hst
      simp only [Option.some.injEq] at hg
      subst hg
      simp only [proof, Goal.corresponds.injEq] at hs
      refine ⟨q0, hq0, ?_, (hadm _).mp ha⟩
      rw [hst, hs.1, hs.2]
    · simp at hg
  · rintro ⟨q, hq, hs, ha⟩
    refine ⟨⟨.corresponds x.reference x.runs, q.theorem_⟩,
      List.mem_map.mpr ⟨⟨x.reference, x.runs, q.theorem_⟩,
        List.mem_filterMap.mpr ⟨q, hq, by simp [correspondence', hs]⟩, rfl⟩, rfl, (hadm _).mpr ha⟩

/-- The input of the checker made from a well-formed input of the specification is admitted. -/
theorem admitted_ofSpec {s : Input} (h : s.WellFormed) : Admitted (ofSpec s) := by
  refine ⟨by rw [toSpec_ofSpec]; exact restrict_wf h, ?_, ?_⟩
  · intro d hd _
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    rfl
  · intro d hd as has a
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hd
    simp only [decl', Option.some.injEq] at has
    subst has
    rw [toSpec_ofSpec, restrict_axiomOf]
    simp only [axiomList, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · intro hax
      obtain ⟨y, hy, hn, -⟩ := hax.2
      exact ⟨List.mem_map.mpr ⟨y, hy, hn⟩, hax⟩

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
noncomputable def rg1001Checker : Checker Input Name := fun s => (ofSpec s).tables.rg1001.map (·.subject)
/-- The function of RG1002 over the specification's input. -/
noncomputable def rg1002Checker : Checker Input Name := fun s => (ofSpec s).tables.rg1002.map (·.subject)
/-- The function of RG1003 over the specification's input. -/
noncomputable def rg1003Checker : Checker Input Name := fun s => (ofSpec s).tables.rg1003.map (·.subject)
/-- The function of RG1004 over the specification's input. -/
noncomputable def rg1004Checker : Checker Input Name := fun s => (ofSpec s).tables.rg1004.map (·.subject)
/-- The function of RG1005 over the specification's input. -/
noncomputable def rg1005Checker : Checker Input Name := fun s => (ofSpec s).tables.rg1005.map (·.subject)
/-- The function of RG1006 over the specification's input. -/
noncomputable def rg1006Checker : Checker Input Name := fun s => (ofSpec s).tables.rg1006.map (·.subject)
/-- The function of RG1007 over the specification's input. -/
noncomputable def rg1007Checker : Checker Input Name := fun s =>
  ((ofSpec s).tables.rg1007 (ofSpec s).contracts).map (·.subject)
/-- The function of RG1008 over the specification's input. -/
noncomputable def rg1008Checker : Checker Input Name := fun s =>
  ((ofSpec s).tables.rg1008 (ofSpec s).contracts (ofSpec s).decisions
    (ofSpec s).decidableResults).map (·.subject)
/-- The function of RG1009 over the specification's input. -/
noncomputable def rg1009Checker : Checker Input Name := fun s =>
  ((ofSpec s).tables.rg1009 (ofSpec s).contracts).map (·.subject)
/-- The function of RG2002 over the specification's input. -/
noncomputable def rg2002Checker : Checker Input Name := fun s =>
  (ofSpec s).manifestFindings.map (·.subject)
/-- The function of RG2004 over the specification's input. -/
noncomputable def rg2004Checker : Checker Input Name := fun s =>
  (ofSpec s).coverageFindings.map (·.subject)
/-- The function of RG3001 over the specification's input. -/
noncomputable def rg3001Checker : Checker Input Name := fun s =>
  ((ofSpec s).rg3001 (ofSpec s).tables).map (·.subject)
/-- The function of RG3002 over the specification's input. -/
noncomputable def rg3002Checker : Checker Input Name := fun s =>
  ((ofSpec s).rg3002 (ofSpec s).tables).map (·.subject)

section Meets

variable {s : Input}

theorem unique_ofSpec (h : s.WellFormed) : ((ofSpec s).decls.map (·.name)).Nodup :=
  unique_of_wf (admitted_ofSpec h).wf

theorem rg1001_meets : rg1001.Meets rg1001Checker := by
  unfold rg1001
  rw [meets_iff]
  intro s _ c
  refine (rg1001_exact _ c).trans ?_
  rw [toSpec_ofSpec]
  exact Iff.rfl

theorem rg1002_meets : rg1002.Meets rg1002Checker := by
  unfold rg1002
  rw [meets_iff]
  intro s h c
  refine (rg1002_exact (admitted_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates1002, restrict_axiomOf]
  exact Iff.rfl

theorem rg1003_meets : rg1003.Meets rg1003Checker := by
  unfold rg1003
  rw [meets_iff]
  intro s h c
  refine (rg1003_exact (admitted_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates1003, restrict_axiomOf]
  exact Iff.rfl

theorem rg1004_meets : rg1004.Meets rg1004Checker := by
  unfold rg1004
  rw [meets_iff]
  intro s h c
  refine (rg1004_exact (admitted_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates1004, restrict_axiomOf]
  exact Iff.rfl

theorem rg1005_meets : rg1005.Meets rg1005Checker := by
  unfold rg1005
  rw [meets_iff]
  intro s h c
  refine (rg1005_exact (admitted_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates1005, restrict_axiomOf]
  exact Iff.rfl

theorem rg1006_meets : rg1006.Meets rg1006Checker := by
  unfold rg1006
  rw [meets_iff]
  intro s h c
  refine (rg1006_exact (unique_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  exact Iff.rfl

theorem rg1007_meets : rg1007.Meets rg1007Checker := by
  unfold rg1007
  rw [meets_iff]
  intro s h c
  refine (rg1007_exact (unique_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates1007, Input.SpecReachesImpl, restrict_reaches]
  exact Iff.rfl

theorem rg1008_meets : rg1008.Meets rg1008Checker := by
  unfold rg1008
  rw [meets_iff]
  intro s h c
  refine (rg1008_exact (unique_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  exact Iff.rfl

theorem rg1009_meets : rg1009.Meets rg1009Checker := by
  unfold rg1009
  rw [meets_iff]
  intro s h c
  refine (rg1009_exact (unique_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates1009, restrict_reaches]
  exact Iff.rfl

theorem rg2002_meets : rg2002.Meets rg2002Checker := by
  unfold rg2002
  rw [meets_iff]
  intro s _ c
  refine (rg2002_exact _ c).trans ?_
  rw [toSpec_ofSpec]
  exact Iff.rfl

theorem rg2004_meets : rg2004.Meets rg2004Checker := by
  unfold rg2004
  rw [meets_iff]
  intro s _ c
  refine (rg2004_exact _ c).trans ?_
  rw [toSpec_ofSpec]
  exact Iff.rfl

theorem rg3001_meets : rg3001.Meets rg3001Checker := by
  unfold rg3001
  rw [meets_iff]
  intro s h c
  refine (rg3001_exact (unique_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates3001, restrict_executes, restrict_departsTo]
  exact Iff.rfl

theorem rg3002_meets : rg3002.Meets rg3002Checker := by
  unfold rg3002
  rw [meets_iff]
  intro s h c
  refine (rg3002_exact (admitted_ofSpec h) c).trans ?_
  rw [toSpec_ofSpec]
  simp only [Violates3002, restrict_executes, restrict_corresponds]
  exact Iff.rfl

end Meets

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
theorem rg1007_cases :
    Witnesses.w1007.bad ∈ rg1007Checker Witnesses.w1007.refused ∧
      Witnesses.w1007.fine ∉ rg1007Checker Witnesses.w1007.admitted :=
  cases_of_meets Witnesses.w1007 rg1007_meets
theorem rg1008_cases :
    Witnesses.w1008.bad ∈ rg1008Checker Witnesses.w1008.refused ∧
      Witnesses.w1008.fine ∉ rg1008Checker Witnesses.w1008.admitted :=
  cases_of_meets Witnesses.w1008 rg1008_meets
theorem rg1009_cases :
    Witnesses.w1009.bad ∈ rg1009Checker Witnesses.w1009.refused ∧
      Witnesses.w1009.fine ∉ rg1009Checker Witnesses.w1009.admitted :=
  cases_of_meets Witnesses.w1009 rg1009_meets
theorem rg2002_cases :
    Witnesses.w2002.bad ∈ rg2002Checker Witnesses.w2002.refused ∧
      Witnesses.w2002.fine ∉ rg2002Checker Witnesses.w2002.admitted :=
  cases_of_meets Witnesses.w2002 rg2002_meets
theorem rg2004_cases :
    Witnesses.w2004.bad ∈ rg2004Checker Witnesses.w2004.refused ∧
      Witnesses.w2004.fine ∉ rg2004Checker Witnesses.w2004.admitted :=
  cases_of_meets Witnesses.w2004 rg2004_meets
theorem rg3001_cases :
    Witnesses.w3001.bad ∈ rg3001Checker Witnesses.w3001.refused ∧
      Witnesses.w3001.fine ∉ rg3001Checker Witnesses.w3001.admitted :=
  cases_of_meets Witnesses.w3001 rg3001_meets
theorem rg3002_cases :
    Witnesses.w3002.bad ∈ rg3002Checker Witnesses.w3002.refused ∧
      Witnesses.w3002.fine ∉ rg3002Checker Witnesses.w3002.admitted :=
  cases_of_meets Witnesses.w3002 rg3002_meets

end RegulaSpecification
