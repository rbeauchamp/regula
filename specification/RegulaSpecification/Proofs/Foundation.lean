import RegulaSpecification.Proofs.Tables

/-!
# RG1001 to RG1006, against their statements

`Regula.Closed.Tables.rg1001` to `rg1006` are the functions that the checker runs. For each,
`rg100N_exact` proves that it reports a subject exactly when `Violates100N` holds of it at `toSpec i`.
RG1001 and RG1006 read no axiom set. The others read `Decl.axioms`, so they assume `AxiomsRead`.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

variable {i : Regula.Closed.Input}

/-- A rule that reports each member of a list that passes a test, once. -/
theorem mem_report {α : Type} {l : List α} {c : α → Bool} {g : α → Regula.Closed.Finding}
    {sub : α → Name} (hg : ∀ a, (g a).subject = sub a) (s : Name) :
    s ∈ (l.filterMap fun a => if c a then some (g a) else none).map (·.subject) ↔
      ∃ a ∈ l, c a = true ∧ sub a = s := by
  simp only [List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨f, ⟨a, ha, hf⟩, rfl⟩
    split at hf
    · rename_i hc
      simp only [Option.some.injEq] at hf
      exact ⟨a, ha, hc, by rw [← hf, hg]⟩
    · simp at hf
  · rintro ⟨a, ha, hc, rfl⟩
    exact ⟨g a, ⟨a, ha, by simp [hc]⟩, hg a⟩

theorem filter_nonempty {α : Type} {l : List α} {p : α → Bool} :
    (!(l.filter p).isEmpty) = true ↔ ∃ a ∈ l, p a = true := by
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, List.mem_filter]

theorem axiomSet_iff (h : AxiomsRead i) {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hr : (toSpec i).ClaimedModule d.module) (a : Name) :
    a ∈ d.axiomSet ↔ (toSpec i).AxiomOf d.name a := by
  have hp := h.present d hd hr
  cases hx : d.axioms with
  | none => simp [hx] at hp
  | some as => simpa [Regula.Closed.Decl.axiomSet, hx] using h.faithful d hd as hx a

theorem known_iff (hu : (i.decls.map (·.name)).Nodup) (a : Name) :
    i.tables.known a = true ↔ (toSpec i).Known a := by
  unfold Regula.Closed.Tables.known
  rw [Bool.and_eq_true, any_index_iff hu]
  have hl : (Regula.Closed.logicalAxioms.contains a = true) ↔ a ∈ logicalAxioms := by
    simp [Regula.Closed.logicalAxioms, logicalAxioms]
  rw [hl]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨d, hd, hn, ht⟩
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, hn, ht⟩
  · rintro ⟨x, hx, hn, ht⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, hd, hn, ht⟩

theorem admits_iff (hu : (i.decls.map (·.name)).Nodup) (p : Regula.Closed.Profile) (a : Name) :
    i.tables.admits p a = true ↔ (toSpec i).Admits (profile p) a := by
  cases p with
  | kernelOnly => simp [Regula.Closed.Tables.admits, profile, Input.Admits]
  | choiceFree =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, known_iff hu]
  | standardLogical =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, known_iff hu]

theorem native_iff (a : Name) : Regula.Closed.nativeProofAxiom a = true ↔ NativeProofAxiom a := by
  constructor
  · intro h
    unfold Regula.Closed.nativeProofAxiom at h
    split at h
    · exact ⟨_, _, _, rfl⟩
    · simp at h
  · rintro ⟨p, t, s, rfl⟩
    simp [Regula.Closed.nativeProofAxiom]

theorem compiler_contains (a : Name) : Regula.Closed.compilerAxioms.contains a = false := by
  simp [Regula.Closed.compilerAxioms]

theorem not_mem_compiler (a : Name) : a ∉ compilerAxioms := by simp [compilerAxioms]

/-- The function that the checker runs reports a constant exactly when it violates RG1001. -/
theorem rg1001_exact (i : Regula.Closed.Input) (s : Name) :
    s ∈ i.tables.rg1001.map (·.subject) ↔ Violates1001 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1001
  have hk : ∀ d : Regula.Closed.Decl, (d.kind == .axiom) = true ↔ (decl d).kind = .axiom := by
    intro d
    cases hd : d.kind <;> simp [decl, constKind, hd]
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed i).mp hd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, (hk d).mp hc⟩
  · rintro ⟨x, hx, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, (mem_claimed i).mpr ⟨hd, hm⟩, (hk d).mpr hc, rfl⟩

/-- The function that the checker runs reports a constant exactly when it violates RG1002. -/
theorem rg1002_exact (h : Admitted i) (s : Name) :
    s ∈ i.tables.rg1002.map (·.subject) ↔ Violates1002 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1002
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed i).mp hd
    exact ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩,
      (axiomSet_iff h.axioms hd hm _).mp (by simpa using hc)⟩
  · rintro ⟨hc, ha⟩
    obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
    exact ⟨d, (mem_claimed i).mpr ⟨hd, hm⟩,
      by simpa using (axiomSet_iff h.axioms hd hm _).mpr ha, rfl⟩

/-- The function that the checker runs reports a constant exactly when it violates RG1003. -/
theorem rg1003_exact (h : Admitted i) (s : Name) :
    s ∈ i.tables.rg1003.map (·.subject) ↔ Violates1003 (toSpec i) s := by
  have hu := unique_of_wf h.wf
  unfold Regula.Closed.Tables.rg1003
  dsimp only
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed i).mp hd
    obtain ⟨a, hax, hf⟩ := filter_nonempty.mp hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hf
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hf
    exact ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩, a,
      (axiomSet_iff h.axioms hd hm _).mp hax,
      fun hk => by simp [(known_iff hu a).mpr hk] at h1, h2,
      fun hn => by simp [(native_iff a).mpr hn] at h3, not_mem_compiler a⟩
  · rintro ⟨hc, a, ha, hk, hs, hn, -⟩
    obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
    refine ⟨d, (mem_claimed i).mpr ⟨hd, hm⟩, ?_, rfl⟩
    refine filter_nonempty.mpr ⟨a, (axiomSet_iff h.axioms hd hm _).mpr ha, ?_⟩
    have h1 : i.tables.known a = false := by
      cases hb : i.tables.known a with
      | false => rfl
      | true => exact absurd ((known_iff hu a).mp hb) hk
    have h3 : Regula.Closed.nativeProofAxiom a = false := by
      cases hb : Regula.Closed.nativeProofAxiom a with
      | false => rfl
      | true => exact absurd ((native_iff a).mp hb) hn
    simp [h1, h3, hs, Regula.Closed.compilerAxioms]

/-- The function that the checker runs reports a constant exactly when it violates RG1004. -/
theorem rg1004_exact (h : Admitted i) (s : Name) :
    s ∈ i.tables.rg1004.map (·.subject) ↔ Violates1004 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1004
  dsimp only
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed i).mp hd
    obtain ⟨a, hax, hf⟩ := filter_nonempty.mp hc
    simp only [compiler_contains, Bool.or_false] at hf
    exact ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩, a,
      (axiomSet_iff h.axioms hd hm _).mp hax, .inl ((native_iff a).mp hf)⟩
  · rintro ⟨hc, a, ha, hn | hn⟩
    · obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
      refine ⟨d, (mem_claimed i).mpr ⟨hd, hm⟩, ?_, rfl⟩
      exact filter_nonempty.mpr ⟨a, (axiomSet_iff h.axioms hd hm _).mpr ha,
        by simp [(native_iff a).mpr hn]⟩
    · exact absurd hn (not_mem_compiler a)

/-- The function that the checker runs reports a constant exactly when it violates RG1005. -/
theorem rg1005_exact (h : Admitted i) (s : Name) :
    s ∈ i.tables.rg1005.map (·.subject) ↔ Violates1005 (toSpec i) s := by
  have hu := unique_of_wf h.wf
  unfold Regula.Closed.Tables.rg1005
  dsimp only
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed i).mp hd
    obtain ⟨a, hax, hf⟩ := filter_nonempty.mp hc
    refine ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩, a,
      (axiomSet_iff h.axioms hd hm _).mp hax, fun hk => ?_⟩
    have ha : i.tables.admits i.tables.profile a = true := (admits_iff hu i.profile a).mpr hk
    simp [ha] at hf
  · rintro ⟨hc, a, ha, hn⟩
    obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
    refine ⟨d, (mem_claimed i).mpr ⟨hd, hm⟩, ?_, rfl⟩
    refine filter_nonempty.mpr ⟨a, (axiomSet_iff h.axioms hd hm _).mpr ha, ?_⟩
    cases hb : i.tables.admits i.tables.profile a with
    | false => rfl
    | true => exact absurd ((admits_iff hu i.profile a).mp hb) hn

theorem helperBase_eq (n b : Name) :
    Regula.Closed.Tables.helperBase? n = some b ↔ n = Name.str b "_unsafe_rec" := by
  constructor
  · intro h
    unfold Regula.Closed.Tables.helperBase? at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  · rintro rfl
    simp [Regula.Closed.Tables.helperBase?]

theorem kindDef_iff (b : Regula.Closed.Decl) :
    b.kind = .definition ↔ (decl b).kind = .definition := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

theorem recursionHelper_iff (hu : (i.decls.map (·.name)).Nodup) (d : Regula.Closed.Decl) :
    i.tables.recursionHelper d = true ↔ (toSpec i).RecursionHelper (decl d) := by
  unfold Regula.Closed.Tables.recursionHelper
  simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none]
  have htail : i.tables.helperBaseFits d = true ↔
      ∃ base ∈ (toSpec i).decls, (decl d).name = Name.str base.name "_unsafe_rec" ∧
        base.kind = .definition ∧ base.module = (decl d).module ∧ base.isUnsafe = false ∧
        base.isPartial = false ∧ base.implementedBy = none ∧ base.isExtern = false := by
    unfold Regula.Closed.Tables.helperBaseFits
    split
    · rename_i b hb
      rw [any_index_iff hu]
      have hn := (helperBase_eq _ _).mp hb
      constructor
      · rintro ⟨x, hx, rfl, hp⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none] at hp
        obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hp
        exact ⟨decl x, mem_decls.mpr ⟨x, hx, rfl⟩, hn, (kindDef_iff x).mp h1, h2, h3, h4, h5, h6⟩
      · rintro ⟨x, hx, hxn, h1, h2, h3, h4, h5, h6⟩
        obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
        have hyb : y.name = b := by
          have : Name.str b "_unsafe_rec" = Name.str y.name "_unsafe_rec" := hn.symm.trans hxn
          simpa using this.symm
        refine ⟨y, hy, hyb, ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none]
        exact ⟨⟨⟨⟨⟨(kindDef_iff y).mpr h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
    · rename_i hb
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      rintro x - hxn
      have h2 : Regula.Closed.Tables.helperBase? d.name = some x.name := (helperBase_eq _ _).mpr hxn
      rw [hb] at h2
      simp at h2
  rw [htail]
  simp only [Input.RecursionHelper, decl]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩

theorem mentionsLoop_iff (d : Regula.Closed.Decl) :
    Regula.Closed.mentionsLoop d = true ↔ MentionsLoop (decl d) := by
  simp [Regula.Closed.mentionsLoop, Regula.Closed.loopConstructs, MentionsLoop, loopConstructs, decl]

/-- The function that the checker runs reports a constant exactly when it violates RG1006. RG1006 reads
no axiom set. -/
theorem rg1006_exact (hu : (i.decls.map (·.name)).Nodup) (s : Name) :
    s ∈ i.tables.rg1006.map (·.subject) ↔ Violates1006 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1006
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed i).mp hd
    refine ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with ⟨hf, hn⟩ | hl
    · exact .inl ⟨hf, fun hh => by simp [(recursionHelper_iff hu d).mpr hh] at hn⟩
    · exact .inr ((mentionsLoop_iff d).mp hl)
  · rintro ⟨x, hx, rfl, hm, hv⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    refine ⟨d, (mem_claimed i).mpr ⟨hd, hm⟩, ?_, rfl⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    rcases hv with ⟨hf, hh⟩ | hl
    · refine .inl ⟨hf, ?_⟩
      cases hb : i.tables.recursionHelper d with
      | false => rfl
      | true => exact absurd ((recursionHelper_iff hu d).mp hb) hh
    · exact .inr ((mentionsLoop_iff d).mpr hl)

end Link

end RegulaSpecification
