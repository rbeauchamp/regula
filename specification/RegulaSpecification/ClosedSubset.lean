import Regula.Rules
import RegulaCore.Allowlist
import RegulaSpecification.CasesProject

/-!
# The link from the executable RG2006 and RG2007 to their statements

`Regula.Closed.Input.optionFindings` and `Regula.Closed.Input.extensionFindings` are the functions
that the checker runs. This module proves that they report a subject exactly when `Violates2006` and
`Violates2007` hold of it (`rg2006_exact`, `rg2007_exact`), so they meet the intent records `rg2006`
and `rg2007` (`rg2006_meets`, `rg2007_meets`), whose obligations `rg2006_adequate` and
`rg2007_adequate` discharge. It proves the same of the members that the checker runs with, the closed
lists of `Regula.Allowlist`, which admit none of `metaExtensions` (`allowlist_closed`).

The implementation's input and the specification's are two types with the same fields, so `toSpec`
and `ofSpec` carry the fields that these two rules and RG2004 read: the targets, the claim and the
module records. The other fields stay empty, because no statement proved here reads them.

The statements do not cover the shell's read of the build: that `Regula.Load` fills the targets and
the module records through Lake's and Lean's own interfaces is trusted.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

/-- The implementation's kind of target in the specification. -/
def kind : Regula.Closed.TargetKind → TargetKind
  | .library => .library
  | .executable => .executable

/-- The specification's kind of target in the implementation. -/
def kind' : TargetKind → Regula.Closed.TargetKind
  | .library => .library
  | .executable => .executable

/-- The implementation's profile in the specification. -/
def profile : Regula.Closed.Profile → Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The specification's profile in the implementation. -/
def profile' : Profile → Regula.Closed.Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The implementation's execution mode in the specification. -/
def execution : Regula.Closed.Execution → Execution
  | .report => .report
  | .checked => .checked

/-- The specification's execution mode in the implementation. -/
def execution' : Execution → Regula.Closed.Execution
  | .report => .report
  | .checked => .checked

/-- The implementation's classification in the specification. -/
def classification : Regula.Closed.Classification → Classification
  | .claimed p e => .claimed (profile p) (execution e)
  | .excluded => .excluded

/-- The specification's classification in the implementation. -/
def classification' : Classification → Regula.Closed.Classification
  | .claimed p e => .claimed (profile' p) (execution' e)
  | .excluded => .excluded

/-- The implementation's entry of the claim in the specification. -/
def entry (e : Regula.Closed.Entry) : Entry := ⟨e.target, classification e.classification⟩

/-- The specification's entry of the claim in the implementation. -/
def entry' (e : Entry) : Regula.Closed.Entry := ⟨e.target, classification' e.classification⟩

/-- The implementation's target in the specification. -/
def target (t : Regula.Closed.Target) : Target :=
  ⟨t.name, kind t.kind, t.modules, t.options, t.extras, t.isDefault⟩

/-- The specification's target in the implementation. -/
def target' (t : Target) : Regula.Closed.Target :=
  ⟨t.name, kind' t.kind, t.modules, t.options, t.extras, t.isDefault⟩

/-- The implementation's module record in the specification. -/
def record (r : Regula.Closed.ModuleRecord) : ModuleRecord := ⟨r.name, r.imports, r.extensions⟩

/-- The specification's module record in the implementation. -/
def record' (r : ModuleRecord) : Regula.Closed.ModuleRecord := ⟨r.name, r.imports, r.extensions⟩

/-- The fields of the implementation's input that RG2004, RG2006 and RG2007 read, as the
specification's input. -/
def toSpec (i : Regula.Closed.Input) : Input where
  targets := i.targets.map target
  manifest := i.manifest.map entry
  modules := i.modules.map record
  decls := []
  loads := []
  contracts := []
  decisions := []
  decidableResults := []
  inventory := none
  proved := []
  confirmed := []

/-- The fields of the specification's input that RG2004, RG2006 and RG2007 read, as the
implementation's input. -/
def ofSpec (i : Input) : Regula.Closed.Input where
  targets := i.targets.map target'
  manifest := i.manifest.map entry'
  modules := i.modules.map record'
  decls := []
  loads := []
  contracts := []
  decisions := []
  decidableResults := []
  proved := []

theorem mem_targets {i : Regula.Closed.Input} {x : Target} :
    x ∈ (toSpec i).targets ↔ ∃ t ∈ i.targets, target t = x := by simp [toSpec]

theorem mem_manifest {i : Regula.Closed.Input} {x : Entry} :
    x ∈ (toSpec i).manifest ↔ ∃ e ∈ i.manifest, entry e = x := by simp [toSpec]

theorem mem_modules {i : Regula.Closed.Input} {x : ModuleRecord} :
    x ∈ (toSpec i).modules ↔ ∃ r ∈ i.modules, record r = x := by simp [toSpec]

theorem classification_inj {a b : Regula.Closed.Classification}
    (h : classification a = classification b) : a = b := by
  rcases a with ⟨p, e⟩ | _ <;> rcases b with ⟨q, x⟩ | _ <;> simp_all [classification]
  · rcases p <;> rcases q <;> rcases e <;> rcases x <;> simp_all [profile, execution]

theorem target_target' (t : Target) : target (target' t) = t := by
  rcases t with ⟨n, k, m, o, x, d⟩
  cases k <;> rfl

theorem entry_entry' (e : Entry) : entry (entry' e) = e := by
  rcases e with ⟨t, c⟩
  rcases c with ⟨p, x⟩ | _
  · rcases p <;> rcases x <;> rfl
  · rfl

theorem record_record' (r : ModuleRecord) : record (record' r) = r := by
  cases r; rfl

theorem toSpec_ofSpec_targets (i : Input) : (toSpec (ofSpec i)).targets = i.targets := by
  simp [toSpec, ofSpec, List.map_map, Function.comp_def, target_target']

theorem toSpec_ofSpec_manifest (i : Input) : (toSpec (ofSpec i)).manifest = i.manifest := by
  simp [toSpec, ofSpec, List.map_map, Function.comp_def, entry_entry']

theorem toSpec_ofSpec_modules (i : Input) : (toSpec (ofSpec i)).modules = i.modules := by
  simp [toSpec, ofSpec, List.map_map, Function.comp_def, record_record']

end Link

open Link

/-! ## Claimed and excluded modules -/

theorem claimedTarget_iff (i : Regula.Closed.Input) (t : Name) :
    i.claimedTarget t = true ↔ (toSpec i).ClaimedTarget t := by
  simp only [Regula.Closed.Input.claimedTarget, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Input.ClaimedTarget, toSpec, List.mem_map]
  constructor
  · rintro ⟨⟨target, c⟩, he, rfl, hc⟩
    cases c with
    | claimed p e => exact ⟨profile p, execution e, _, he, rfl⟩
    | excluded => simp at hc
  · rintro ⟨p, e, ⟨target, c⟩, he, hx⟩
    simp only [entry, Entry.mk.injEq] at hx
    obtain ⟨rfl, hc⟩ := hx
    cases c with
    | claimed q x => exact ⟨_, he, rfl, rfl⟩
    | excluded => simp [classification] at hc

theorem claimedModule_iff (i : Regula.Closed.Input) (m : Name) :
    i.claimedModule m = true ↔ (toSpec i).ClaimedModule m := by
  simp only [Regula.Closed.Input.claimedModule, Regula.Closed.Input.claimsOf, Bool.not_eq_true',
    List.isEmpty_eq_false_iff_exists_mem, List.mem_flatMap]
  constructor
  · rintro ⟨x, t, ht, hx⟩
    by_cases hm : t.modules.contains m = true
    · rw [ite_eq_left hm, List.mem_filterMap] at hx
      obtain ⟨⟨name, c⟩, he, hc⟩ := hx
      by_cases hn : name = t.name
      · subst hn
        cases c with
        | claimed p e =>
          exact ⟨profile p, execution e, target t, mem_targets.mpr ⟨t, ht, rfl⟩,
            (show m ∈ t.modules by simpa using hm), mem_manifest.mpr ⟨_, he, rfl⟩⟩
        | excluded => simp at hc
      · simp [hn] at hc
    · rw [ite_eq_right hm] at hx
      simp at hx
  · rintro ⟨p, e, x, hx, hm, hme⟩
    obtain ⟨t, ht, rfl⟩ := mem_targets.mp hx
    obtain ⟨⟨name, c⟩, he, hc⟩ := mem_manifest.mp hme
    simp only [entry, Entry.mk.injEq] at hc
    obtain ⟨hn, hcl⟩ := hc
    have hn' : name = t.name := hn
    subst hn'
    cases c with
    | claimed q y =>
      have hcon : t.modules.contains m = true := by simpa using (show m ∈ t.modules from hm)
      refine ⟨(q, y), t, ht, ?_⟩
      rw [ite_eq_left hcon, List.mem_filterMap]
      exact ⟨_, he, by simp⟩
    | excluded => simp [classification] at hcl

theorem excludedModule_iff (i : Regula.Closed.Input) (m : Name) :
    i.excludedModule m = true ↔ (toSpec i).ExcludedModule m := by
  simp only [Regula.Closed.Input.excludedModule, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Input.ExcludedModule, Input.InTarget, toSpec, List.mem_map, List.contains_iff_mem]
  constructor
  · rintro ⟨t, ht, hm, ⟨name, c⟩, he, rfl, hc⟩
    obtain rfl : c = .excluded := hc
    exact ⟨target t, ⟨t, ht, rfl⟩, hm, _, he, rfl⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, hm, ⟨name, c⟩, he, hx⟩
    simp only [entry, target, Entry.mk.injEq] at hx hm
    obtain ⟨rfl, hc⟩ := hx
    refine ⟨t, ht, hm, _, he, rfl, ?_⟩
    cases c with
    | claimed q y => simp [classification] at hc
    | excluded => rfl

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
def rg2006Checker : Checker Input Name := fun s =>
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
def rg2007Checker : Checker Input Name := fun s =>
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


/-! ## The verdict -/

/-- A list that `dedupe` leaves empty was empty. -/
theorem dedupe_eq_nil {fs : List Regula.Closed.Finding} (h : Regula.Closed.dedupe fs = []) :
    fs = [] := by
  cases fs with
  | nil => rfl
  | cons f fs =>
    exfalso
    have step : ∀ (l : List Regula.Closed.Finding) (s : Std.HashSet String)
        (acc : List Regula.Closed.Finding), acc ≠ [] →
        (l.foldl (init := (s, acc)) fun (seen, acc) f =>
          let key := s!"{f.rule.spelling}|{f.subject}|{f.module}|{f.detail}"
          if seen.contains key then (seen, acc) else (seen.insert key, f :: acc)).2 ≠ [] := by
      intro l
      induction l with
      | nil => intro _ _ h; exact h
      | cons g gs ih =>
        intro s acc hne
        simp only [List.foldl_cons]
        split
        · exact ih _ _ hne
        · exact ih _ _ (List.cons_ne_nil _ _)
    simp only [Regula.Closed.dedupe, List.foldl_cons, List.reverse_eq_nil_iff] at h
    revert h
    split
    · simp_all
    · exact step _ _ _ (List.cons_ne_nil _ _)

/-- A successful `mapM` in `Except` gives each element's result. -/
theorem mem_mapM_ok {α β ε : Type} (f : α → Except ε β) :
    ∀ (l : List α) (ys : List β), l.mapM f = .ok ys → ∀ x ∈ l, ∃ y ∈ ys, f x = .ok y := by
  intro l
  induction l with
  | nil => intro _ _ _ hx; simp at hx
  | cons a l ih =>
    intro ys h x hx
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error e => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error e => simp [ha, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨b, by simp, ha⟩
        · obtain ⟨y, hy, hfy⟩ := ih bs hl x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- Successful findings end with the project's findings. -/
theorem findings_ok {a : Regula.Closed.Allowlists} {i : Regula.Closed.Input}
    {gs : List Regula.Closed.Finding} (h : i.findings a = .ok gs) :
    ∃ pre, gs = pre ++ i.projectFindings a := by
  simp only [Regula.Closed.Input.findings, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        exact ⟨_, h.symm⟩

/-- A pass of the checker holds RG2006 and RG2007 of each environment, at the allowlists it ran
with: no target and no module of the environment violates either rule. -/
theorem run_pass_holds {a : Regula.Closed.Allowlists} {b : Regula.Closed.Bundle}
    (h : (Regula.Closed.run a b).1 = .pass) :
    ∀ i ∈ b.envs, (∀ t, ¬ Violates2006 (fun n => a.options n = true) (toSpec i) t) ∧
      ∀ m, ¬ Violates2007 (fun n => a.extensions n = true) (toSpec i) m := by
  intro i hi
  unfold Regula.Closed.run at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · next fs hfs =>
      have hempty : Regula.Closed.dedupe fs.flatten = [] := by
        cases he : Regula.Closed.dedupe fs.flatten with
        | nil => rfl
        | cons _ _ => simp [he] at h
      have hflat := dedupe_eq_nil hempty
      obtain ⟨gs, hgs, hfi⟩ := mem_mapM_ok _ _ _ hfs i hi
      obtain ⟨pre, rfl⟩ := findings_ok hfi
      have hnil : pre ++ i.projectFindings a = [] := List.flatten_eq_nil_iff.mp hflat _ hgs
      have hproject := (List.append_eq_nil_iff.mp hnil).2
      simp only [Regula.Closed.Input.projectFindings, Regula.Closed.Input.configurationFindings,
        List.append_eq_nil_iff] at hproject
      refine ⟨fun t hv => ?_, fun m hv => ?_⟩
      · have := (rg2006_exact a.options i t).mpr hv
        simp [hproject.1.1.2] at this
      · have := (rg2007_exact a.extensions i m).mpr hv
        simp [hproject.2] at this

end RegulaSpecification
