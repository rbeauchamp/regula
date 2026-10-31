import RegulaCore.Allowlist
import RegulaSpecification.Proofs.Project

/-!
# The link from the executable RG2006 and RG2007 to their statements

`Regula.Closed.Input.optionFindings` and `Regula.Closed.Input.extensionFindings` are the functions
that the checker runs. This module proves that they report a subject exactly when `Violates2006` and
`Violates2007` hold of it (`rg2006_exact`, `rg2007_exact`), so they meet the intent records `rg2006`
and `rg2007` (`rg2006_meets`, `rg2007_meets`), whose obligations `rg2006_adequate` and
`rg2007_adequate` discharge. It proves the same of the members that the checker runs with, the closed
lists of `Regula.Allowlist`, which admit none of `metaExtensions` (`allowlist_closed`).

The statements do not cover the shell's read of the build: that `Regula.Load` fills the targets and
the module records through Lake's and Lean's own interfaces is trusted.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

open Link

/-! ## RG2006 -/

/-- The findings of one target name that target. -/
theorem subject_of_targetOptionFindings {allowed : Name → Bool} {t : Regula.Closed.Target}
    {f : Regula.Closed.Finding} (h : f ∈ Regula.Closed.Input.targetOptionFindings allowed t) :
    f.subject = t.name := by
  simp only [Regula.Closed.Input.targetOptionFindings, List.mem_append, List.mem_map] at h
  rcases h with ((⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩) | h
  · rfl
  · rfl
  · rfl
  · split at h <;> simp_all

/-- One target has a finding exactly when its options and extras fail the condition of
`Violates2006`. -/
theorem targetOptionFindings_ne_nil (allowed : Name → Bool) (t : Regula.Closed.Target) :
    Regula.Closed.Input.targetOptionFindings allowed t ≠ [] ↔
      ((`autoImplicit, "false") ∉ t.options ∨ (`relaxedAutoImplicit, "false") ∉ t.options ∨
        (∃ o ∈ t.options, (o.1 = `autoImplicit ∨ o.1 = `relaxedAutoImplicit) ∧ o.2 ≠ "false") ∨
        (∃ o ∈ t.options, ¬ allowed o.1 = true) ∨ t.extras ≠ []) := by
  have hnil : Regula.Closed.Input.targetOptionFindings allowed t = [] ↔
      ((`autoImplicit, "false") ∈ t.options ∧ (`relaxedAutoImplicit, "false") ∈ t.options ∧
        (∀ o ∈ t.options, (o.1 = `autoImplicit ∨ o.1 = `relaxedAutoImplicit) → o.2 = "false") ∧
        (∀ o ∈ t.options, allowed o.1 = true) ∧ t.extras = []) := by
    cases hx : t.extras with
    | nil =>
      simp [Regula.Closed.Input.targetOptionFindings, hx, List.filter_eq_nil_iff, and_assoc]
    | cons x xs =>
      simp [Regula.Closed.Input.targetOptionFindings, hx]
  rw [ne_eq, hnil]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hn
    simp only [not_or, Classical.not_not, ne_eq] at hn
    obtain ⟨a, b, c, d, e⟩ := hn
    exact h ⟨a, b, fun o ho hk => Classical.byContradiction fun hne => c ⟨o, ho, hk, hne⟩,
      fun o ho => Classical.byContradiction fun hne => d ⟨o, ho, hne⟩, e⟩
  · rintro (h | h | ⟨o, ho, hk, hne⟩ | ⟨o, ho, hne⟩ | h) ⟨a, b, c, d, e⟩
    · exact h a
    · exact h b
    · exact hne (c o ho hk)
    · exact hne (d o ho)
    · exact h e

/-- The function that the checker runs reports a target exactly when it violates RG2006. -/
theorem rg2006_exact (allowed : Name → Bool) (i : Regula.Closed.Input) (t : Name) :
    t ∈ (i.optionFindings allowed).map (·.subject) ↔
      Violates2006 (fun n => allowed n = true) (toSpec i) t := by
  simp only [Regula.Closed.Input.optionFindings, List.mem_map, List.mem_flatMap, Violates2006]
  constructor
  · rintro ⟨f, ⟨tg, htg, hf⟩, rfl⟩
    by_cases hc : i.claimedTarget tg.name = true
    · rw [ite_eq_left hc] at hf
      rw [subject_of_targetOptionFindings hf]
      exact ⟨target tg, mem_targets.mpr ⟨tg, htg, rfl⟩, rfl, (claimedTarget_iff i _).mp hc,
        (targetOptionFindings_ne_nil allowed tg).mp (List.ne_nil_of_mem hf)⟩
    · rw [ite_eq_right hc] at hf
      simp at hf
  · rintro ⟨x, hx, rfl, hc, hv⟩
    obtain ⟨tg, htg, rfl⟩ := mem_targets.mp hx
    obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ ((targetOptionFindings_ne_nil allowed tg).mpr hv)
    refine ⟨f, ⟨tg, htg, ?_⟩, subject_of_targetOptionFindings hf⟩
    have hcb : i.claimedTarget tg.name = true := (claimedTarget_iff i _).mpr hc
    rw [ite_eq_left hcb]
    exact hf

/-- The checker refuses a claimed target with any extra argument of Lean, plugin or dynamic library,
which `Regula.Load.targetOf` puts in `extras`, whatever its allowlist. -/
theorem rg2006_refuses_extras (allowed : Name → Bool) {i : Regula.Closed.Input}
    {t : Regula.Closed.Target} (ht : t ∈ i.targets) (hc : i.claimedTarget t.name = true)
    (hx : t.extras ≠ []) : t.name ∈ (i.optionFindings allowed).map (·.subject) :=
  (rg2006_exact allowed i _).mpr ⟨target t, mem_targets.mpr ⟨t, ht, rfl⟩, rfl,
    (claimedTarget_iff i _).mp hc, Or.inr (Or.inr (Or.inr (Or.inr hx)))⟩

/-- RG2006's option allowlist, as the proposition that its record takes. -/
def allowedOption (n : Name) : Prop := Regula.Allowlist.admitsOption n = true

/-- The implementation of RG2006 over the specification's input. -/
noncomputable def rg2006Checker : Checker Input Name := fun s =>
  ((ofSpec s).optionFindings Regula.Allowlist.admitsOption).map (·.subject)

theorem violates2006_congr {P : Name → Prop} {a b : Input} (ht : a.targets = b.targets)
    (hm : a.manifest = b.manifest) (t : Name) : Violates2006 P a t ↔ Violates2006 P b t := by
  simp only [Violates2006, Input.ClaimedTarget, ht, hm]

/-- The function that the checker runs, at the members it runs with, meets the record `rg2006`. -/
theorem rg2006_meets : (rg2006 allowedOption).Meets rg2006Checker := by
  unfold rg2006
  rw [meets_iff]
  intro s _ t
  exact (rg2006_exact _ _ t).trans
    (violates2006_congr (toSpec_ofSpec_targets s) (toSpec_ofSpec_manifest s) t)

theorem autoImplicit_allowed : allowedOption `autoImplicit := by
  unfold allowedOption
  decide +kernel

theorem relaxedAutoImplicit_allowed : allowedOption `relaxedAutoImplicit := by
  unfold allowedOption
  decide +kernel

/-- The obligations of the record of RG2006, at the members that the checker runs with. -/
theorem rg2006_allowlist_adequate :
    O2 (rg2006 allowedOption) ∧ O2Run (rg2006 allowedOption) ∧ O3 (rg2006 allowedOption) ∧
      O4 (rg2006 allowedOption) ∧ O5 (rg2006 allowedOption) (.rel SameReports) :=
  Witnesses.rg2006_adequate allowedOption autoImplicit_allowed relaxedAutoImplicit_allowed

/-! ## RG2007 -/

/-- The function that the checker runs reports a module exactly when it violates RG2007. -/
theorem rg2007_exact (allowed : Name → Bool) (i : Regula.Closed.Input) (m : Name) :
    m ∈ (i.extensionFindings allowed).map (·.subject) ↔
      Violates2007 (fun n => allowed n = true) (toSpec i) m := by
  simp only [Regula.Closed.Input.extensionFindings, List.mem_map, List.mem_flatMap, Violates2007]
  constructor
  · rintro ⟨f, ⟨r, hr, hf⟩, rfl⟩
    by_cases hc : i.claimedModule r.name = true
    · rw [ite_eq_left hc] at hf
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hf
      obtain ⟨hxe, hna⟩ := List.mem_filter.mp hx
      exact ⟨(claimedModule_iff i _).mp hc, record r, mem_modules.mpr ⟨r, hr, rfl⟩, rfl, x, hxe,
        by simpa using hna⟩
    · rw [ite_eq_right hc] at hf
      simp at hf
  · rintro ⟨hc, y, hy, rfl, x, hx, hna⟩
    obtain ⟨r, hr, rfl⟩ := mem_modules.mp hy
    have hcb : i.claimedModule r.name = true := (claimedModule_iff i _).mpr hc
    refine ⟨{ rule := .closedSubset, subject := r.name, module := some r.name
              detail := s!"has entries of the environment extension {x}, outside the allowlist" },
      ⟨r, hr, ?_⟩, rfl⟩
    rw [ite_eq_left hcb]
    exact List.mem_map.mpr ⟨x, List.mem_filter.mpr ⟨hx, by simpa using hna⟩, rfl⟩

/-- RG2007's extension allowlist, as the proposition that its record takes. -/
def allowedExtension (n : Name) : Prop := Regula.Allowlist.admitsExtension n = true

/-- The implementation of RG2007 over the specification's input. -/
noncomputable def rg2007Checker : Checker Input Name := fun s =>
  ((ofSpec s).extensionFindings Regula.Allowlist.admitsExtension).map (·.subject)

theorem violates2007_congr {P : Name → Prop} {a b : Input} (ht : a.targets = b.targets)
    (hm : a.manifest = b.manifest) (hr : a.modules = b.modules) (m : Name) :
    Violates2007 P a m ↔ Violates2007 P b m := by
  simp only [Violates2007, Input.ClaimedModule, Input.Claimed, Input.InTarget, ht, hm, hr]

/-- The function that the checker runs, at the members it runs with, meets the record `rg2007`. -/
theorem rg2007_meets : (rg2007 allowedExtension).Meets rg2007Checker := by
  unfold rg2007
  rw [meets_iff]
  intro s _ m
  exact (rg2007_exact _ _ m).trans (violates2007_congr (toSpec_ofSpec_targets s)
    (toSpec_ofSpec_manifest s) (toSpec_ofSpec_modules s) m)

/-- The allowlist that the checker runs with admits none of `metaExtensions`. -/
theorem allowlist_closed : ClosedAllowlist allowedExtension := by
  intro x hx
  simp only [metaExtensions, List.mem_cons, List.not_mem_nil, or_false] at hx
  unfold allowedExtension
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem declRangeExt_allowed : allowedExtension `Lean.declRangeExt := by
  unfold allowedExtension
  decide +kernel

/-- The obligations of the record of RG2007, at the members that the checker runs with. -/
theorem rg2007_allowlist_adequate :
    O2 (rg2007 allowedExtension) ∧ O2Run (rg2007 allowedExtension) ∧ O3 (rg2007 allowedExtension) ∧
      O4 (rg2007 allowedExtension) ∧ O5 (rg2007 allowedExtension) (.rel SameReports) :=
  Witnesses.rg2007_adequate allowedExtension allowlist_closed declRangeExt_allowed

/-- The checker refuses a claimed module with a macro, an elaborator, syntax, an initializer or a
`meta` declaration: `rg2007_refuses_meta`, at the function it runs and the members it runs with. -/
theorem rg2007_checker_refuses_meta {i : Regula.Closed.Input} {r : Regula.Closed.ModuleRecord}
    (hr : r ∈ i.modules) (hc : i.claimedModule r.name = true) {x : Name} (hx : x ∈ r.extensions)
    (hmeta : x ∈ metaExtensions) :
    r.name ∈ (i.extensionFindings Regula.Allowlist.admitsExtension).map (·.subject) :=
  (rg2007_exact _ i _).mpr (rg2007_refuses_meta allowlist_closed ((claimedModule_iff i _).mp hc)
    (r := record r) (mem_modules.mpr ⟨r, hr, rfl⟩) rfl hx hmeta)

/-! ## A claimed module that imports a tool module -/

/-- The checker refuses a claimed module that imports a module of an excluded target, a tool
module: the second case of `Violates2004`. -/
theorem coverage_refuses_tool_import {i : Regula.Closed.Input} {r : Regula.Closed.ModuleRecord}
    (hr : r ∈ i.modules) (hc : (toSpec i).ClaimedModule r.name) {n : Name} (hn : n ∈ r.imports)
    (hx : (toSpec i).ExcludedModule n) : r.name ∈ i.coverageFindings.map (·.subject) := by
  have hcb := (claimedModule_iff i _).mpr hc
  have hxb := (excludedModule_iff i _).mpr hx
  simp only [Regula.Closed.Input.coverageFindings, List.mem_map, List.mem_flatMap]
  refine ⟨{ rule := .coverage, subject := r.name, module := some r.name
            detail := s!"is claimed and imports {n}, a module of an excluded target" },
    ⟨r, hr, ?_⟩, rfl⟩
  rw [ite_eq_left hcb]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, hxb⟩, rfl⟩)


end RegulaSpecification
