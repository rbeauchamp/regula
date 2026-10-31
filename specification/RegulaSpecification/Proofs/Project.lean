import RegulaSpecification.Proofs.Execution

/-!
# RG2002 and RG2004, against their statements

`Regula.Closed.Input.manifestFindings` and `coverageFindings` are the functions that the checker runs.
`rg2002_exact` and `rg2004_exact` prove that each reports a subject exactly when its violation
predicate holds of it at `toSpec i`. They read Lake's targets, the claim and the module records, and
each holds of every input, well-formed or not.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

variable {i : Regula.Closed.Input}

theorem entriesFor_eq (i : Regula.Closed.Input) (t : Name) :
    (toSpec i).entriesFor t = i.entriesFor t := by
  unfold Input.entriesFor Regula.Closed.Input.entriesFor
  simp [toSpec, List.filter_map, Function.comp_def, entry]

theorem kind_library (x : Regula.Closed.Target) :
    (x.kind == .library) = true ↔ (target x).kind = .library := by
  cases h : x.kind <;> simp [target, kind, h]

theorem classification_ne_iff (a b : Regula.Closed.Classification) :
    (a != b) = true ↔ classification a ≠ classification b := by
  simp only [bne_iff_ne, ne_eq]
  exact not_congr ⟨fun h => h ▸ rfl, classification_inj⟩

/-- The clause of RG2002 about an executable and a library that contains its root. -/
theorem differs_iff (i : Regula.Closed.Input) (x : Regula.Closed.Target) :
    (i.targets.any fun l =>
      l.kind == .library && x.modules.any l.modules.contains &&
        i.manifest.any fun a => a.target == x.name &&
          i.manifest.any fun b => b.target == l.name && a.classification != b.classification) = true ↔
    ∃ l ∈ (toSpec i).targets, l.kind = .library ∧ (∃ m ∈ (target x).modules, m ∈ l.modules) ∧
      ∃ cx cl, (⟨(target x).name, cx⟩ : Entry) ∈ (toSpec i).manifest ∧
        (⟨l.name, cl⟩ : Entry) ∈ (toSpec i).manifest ∧ cx ≠ cl := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem]
  constructor
  · rintro ⟨l, hl, ⟨hk, m, hm, hml⟩, a, ha, han, b, hb, hbn, hne⟩
    refine ⟨target l, mem_targets.mpr ⟨l, hl, rfl⟩, (beq_iff_eq.symm.trans (kind_library l)).mp hk, ⟨m, hm, hml⟩,
      classification a.classification, classification b.classification,
      mem_manifest.mpr ⟨a, ha, by simp [entry, han, target]⟩,
      mem_manifest.mpr ⟨b, hb, by simp [entry, hbn, target]⟩, (classification_ne_iff _ _).mp hne⟩
  · rintro ⟨l', hl', hk, ⟨m, hm, hml⟩, cx, cl, hcx, hcl, hne⟩
    obtain ⟨l, hl, rfl⟩ := mem_targets.mp hl'
    obtain ⟨a, ha, hae⟩ := mem_manifest.mp hcx
    obtain ⟨b, hb, hbe⟩ := mem_manifest.mp hcl
    simp only [entry, target, Entry.mk.injEq] at hae hbe
    refine ⟨l, hl, ⟨(beq_iff_eq.symm.trans (kind_library l)).mpr hk, m, hm, hml⟩, a, ha, hae.1, b, hb, hbe.1, ?_⟩
    rw [classification_ne_iff, hae.2, hbe.2]
    exact hne

/-- The function that the checker runs reports a target exactly when it violates RG2002. -/
theorem rg2002_exact (i : Regula.Closed.Input) (s : Name) :
    s ∈ i.manifestFindings.map (·.subject) ↔ Violates2002 (toSpec i) s := by
  unfold Regula.Closed.Input.manifestFindings
  simp only [List.map_append, List.mem_append]
  rw [mem_report (sub := (·.name)) (fun _ => rfl), mem_report (sub := (·.target)) (fun _ => rfl),
    mem_report (sub := (·.name)) (fun _ => rfl), mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro (((⟨t, ht, hc, rfl⟩ | ⟨e, he, hc, rfl⟩) | ⟨x, hx, hc, rfl⟩) | ⟨x, hx, hc, rfl⟩)
    · refine .inl ⟨⟨target t, mem_targets.mpr ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
      rw [entriesFor_eq]
      simpa using hc
    · refine .inr (.inl ⟨⟨entry e, mem_manifest.mpr ⟨e, he, rfl⟩, rfl⟩, ?_⟩)
      rintro ⟨tg, htg, hn⟩
      obtain ⟨t, ht, rfl⟩ := mem_targets.mp htg
      simp only [List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_map,
        not_exists, not_and] at hc
      exact hc t ht hn
    · simp only [Bool.and_eq_true] at hc
      exact .inr (.inr (.inl ⟨target x, mem_targets.mpr ⟨x, hx, rfl⟩, rfl,
        (kind_executable x).mp hc.1, (differs_iff i x).mp hc.2⟩))
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact .inr (.inr (.inr ⟨target x, mem_targets.mpr ⟨x, hx, rfl⟩, rfl,
        (claimedTarget_iff i _).mp hc.1, hc.2⟩))
  · rintro (⟨⟨tg, htg, rfl⟩, hne⟩ | ⟨⟨e, he, rfl⟩, hno⟩ | ⟨x', hx', rfl, hk, hl⟩ | ⟨x', hx', rfl, hc, hd⟩)
    · obtain ⟨t, ht, rfl⟩ := mem_targets.mp htg
      rw [entriesFor_eq] at hne
      have hne' : i.entriesFor t.name ≠ 1 := hne
      exact .inl (.inl (.inl ⟨t, ht, by simpa using hne', rfl⟩))
    · obtain ⟨e0, he0, rfl⟩ := mem_manifest.mp he
      refine .inl (.inl (.inr ⟨e0, he0, ?_, rfl⟩))
      simp only [List.contains_eq_mem, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_map,
        not_exists, not_and]
      intro t ht hn
      exact hno ⟨target t, mem_targets.mpr ⟨t, ht, rfl⟩, hn⟩
    · obtain ⟨x, hx, rfl⟩ := mem_targets.mp hx'
      refine .inl (.inr ⟨x, hx, ?_, rfl⟩)
      simp only [Bool.and_eq_true]
      exact ⟨(kind_executable x).mpr hk, (differs_iff i x).mpr hl⟩
    · obtain ⟨x, hx, rfl⟩ := mem_targets.mp hx'
      refine .inr ⟨x, hx, ?_, rfl⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨(claimedTarget_iff i _).mpr hc, hd⟩

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

theorem librariesOf_eq (i : Regula.Closed.Input) (m : Name) :
    (toSpec i).librariesOf m = (i.librariesOf m).map target := by
  unfold Input.librariesOf Regula.Closed.Input.librariesOf
  simp only [toSpec, List.filter_map]
  congr 2
  funext t
  simp only [Function.comp, target]
  cases t.kind <;> rfl

/-- Whether the function counts module `m` as covered. -/
theorem covered_iff (i : Regula.Closed.Input) (m : Name) :
    ((i.librariesOf m).length == 1 || ((i.librariesOf m).isEmpty &&
        i.targets.any fun t => t.kind == .executable && t.modules.contains m)) = true ↔
      (toSpec i).Covered m := by
  unfold Input.Covered
  rw [librariesOf_eq]
  simp only [Bool.or_eq_true, beq_iff_eq, List.length_map, Bool.and_eq_true, List.isEmpty_iff,
    List.map_eq_nil_iff, List.any_eq_true, List.contains_iff_mem]
  refine or_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · rintro ⟨t, ht, hk, hm⟩
    exact ⟨target t, mem_targets.mpr ⟨t, ht, rfl⟩,
      (beq_iff_eq.symm.trans (kind_executable t)).mp hk, hm⟩
  · rintro ⟨x, hx, hk, hm⟩
    obtain ⟨t, ht, rfl⟩ := mem_targets.mp hx
    exact ⟨t, ht, (beq_iff_eq.symm.trans (kind_executable t)).mpr hk, hm⟩

/-- The function that the checker runs reports a module exactly when it violates RG2004. -/
theorem rg2004_exact (i : Regula.Closed.Input) (s : Name) :
    s ∈ i.coverageFindings.map (·.subject) ↔ Violates2004 (toSpec i) s := by
  unfold Regula.Closed.Input.coverageFindings
  simp only [List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨f, ⟨r, hr, hf⟩, rfl⟩
    refine ⟨record r, mem_modules.mpr ⟨r, hr, rfl⟩, ?_⟩
    rcases List.mem_append.mp hf with hf | hf
    · split at hf
      · simp at hf
      · rename_i hc
        simp only [List.mem_singleton] at hf
        subst hf
        exact ⟨rfl, .inl fun hcov => hc ((covered_iff i _).mpr hcov)⟩
    · split at hf
      · rename_i hc
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hf
        obtain ⟨hn, hx⟩ := List.mem_filter.mp hn
        exact ⟨rfl, .inr ⟨(claimedModule_iff i _).mp hc, n, hn, (excludedModule_iff i n).mp hx⟩⟩
      · simp at hf
  · rintro ⟨x, hx, rfl, hv⟩
    obtain ⟨r, hr, rfl⟩ := mem_modules.mp hx
    rcases hv with hcov | ⟨hc, n, hn, he⟩
    · have hnot := fun hb => hcov ((covered_iff i r.name).mp hb)
      refine ⟨{ rule := .coverage, subject := r.name, module := some r.name
                detail := s!"is in {(i.librariesOf r.name).length} libraries" },
        ⟨r, hr, List.mem_append_left _ ?_⟩, rfl⟩
      rw [ite_eq_right hnot]
      exact List.mem_singleton.mpr rfl
    · refine ⟨{ rule := .coverage, subject := r.name, module := some r.name
                detail := s!"is claimed and imports {n}, a module of an excluded target" },
        ⟨r, hr, List.mem_append_right _ ?_⟩, rfl⟩
      have hc' : i.claimedModule r.name = true := (claimedModule_iff i _).mpr hc
      rw [ite_eq_left hc']
      exact List.mem_map.mpr ⟨n, List.mem_filter.mpr ⟨hn, (excludedModule_iff i n).mpr he⟩, rfl⟩

end Link

end RegulaSpecification
