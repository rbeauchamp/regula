import RegulaSpecification.Proofs.Tables

/-!
# RG1001 to RG1006, against their statements

{name}`Regula.Closed.Tables.rg1001` to {name (full := Regula.Closed.Tables.rg1006)}`rg1006` are the functions that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

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

theorem known_iff (a : Name) :
    t.known a = true ↔ (toSpec i).Known a := by
  unfold Regula.Closed.Tables.known
  rw [Bool.and_eq_true, any_index_iff t]
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

theorem admits_iff (p : Regula.Closed.Profile) (a : Name) :
    t.admits p a = true ↔ (toSpec i).Admits (profile p) a := by
  cases p with
  | kernelOnly => simp [Regula.Closed.Tables.admits, profile, Input.Admits]
  | choiceFree =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, Bool.and_eq_true,
      Bool.or_eq_true, beq_iff_eq, known_iff t]
  | standardLogical =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, known_iff t]

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

theorem rg1001_exact (s : Name) :
    s ∈ t.rg1001.map (·.subject) ↔ Violates1001 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1001
  have hk : ∀ d : Regula.Closed.Decl, (d.kind == .axiom) = true ↔ (decl d).kind = .axiom := by
    intro d
    simpa using kind_axiom_iff d
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, (hk d).mp hc⟩
  · rintro ⟨x, hx, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, (hk d).mpr hc, rfl⟩

theorem rg1002_exact (s : Name) :
    s ∈ t.rg1002.map (·.subject) ↔ Violates1002 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1002
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    exact ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩,
      (axiomSet_iff t _ _).mp (by simpa using hc)⟩
  · rintro ⟨hc, ha⟩
    obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
    exact ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩,
      by simpa using (axiomSet_iff t _ _).mpr ha, rfl⟩

theorem rg1003_exact (s : Name) :
    s ∈ t.rg1003.map (·.subject) ↔ Violates1003 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1003
  dsimp only
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    obtain ⟨a, hax, hf⟩ := filter_nonempty.mp hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hf
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hf
    exact ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩, a,
      (axiomSet_iff t _ _).mp hax,
      fun hk => by simp [(known_iff t a).mpr hk] at h1, h2,
      fun hn => by simp [(native_iff a).mpr hn] at h3, not_mem_compiler a⟩
  · rintro ⟨hc, a, ha, hk, hs, hn, -⟩
    obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
    refine ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ?_, rfl⟩
    refine filter_nonempty.mpr ⟨a, (axiomSet_iff t _ _).mpr ha, ?_⟩
    have h1 : t.known a = false := by
      cases hb : t.known a with
      | false => rfl
      | true => exact absurd ((known_iff t a).mp hb) hk
    have h3 : Regula.Closed.nativeProofAxiom a = false := by
      cases hb : Regula.Closed.nativeProofAxiom a with
      | false => rfl
      | true => exact absurd ((native_iff a).mp hb) hn
    simp [h1, h3, hs, Regula.Closed.compilerAxioms]

theorem rg1004_exact (s : Name) :
    s ∈ t.rg1004.map (·.subject) ↔ Violates1004 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1004
  dsimp only
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    obtain ⟨a, hax, hf⟩ := filter_nonempty.mp hc
    simp only [compiler_contains, Bool.or_false] at hf
    exact ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩, a,
      (axiomSet_iff t _ _).mp hax, .inl ((native_iff a).mp hf)⟩
  · rintro ⟨hc, a, ha, hn | hn⟩
    · obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
      refine ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ?_, rfl⟩
      exact filter_nonempty.mpr ⟨a, (axiomSet_iff t _ _).mpr ha,
        by simp [(native_iff a).mpr hn]⟩
    · exact absurd hn (not_mem_compiler a)

theorem rg1005_exact (s : Name) :
    s ∈ t.rg1005.map (·.subject) ↔ Violates1005 (toSpec i) s := by
  unfold Regula.Closed.Tables.rg1005
  dsimp only
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    obtain ⟨a, hax, hf⟩ := filter_nonempty.mp hc
    refine ⟨⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm⟩, a,
      (axiomSet_iff t _ _).mp hax, fun hk => ?_⟩
    have ha : t.admits i.profile a = true := (admits_iff t i.profile a).mpr hk
    simp [ha] at hf
  · rintro ⟨hc, a, ha, hn⟩
    obtain ⟨d, hd, rfl, hm⟩ := claimedName_of_mem hc
    refine ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ?_, rfl⟩
    refine filter_nonempty.mpr ⟨a, (axiomSet_iff t _ _).mpr ha, ?_⟩
    cases hb : t.admits i.profile a with
    | false => rfl
    | true => exact absurd ((admits_iff t i.profile a).mp hb) hn

/-- The compiler's own test of a helper's name holds exactly of the form that {name}`HelperNamed`
states. The checker runs this test, so a toolchain whose test differs fails this proof. -/
theorem isUnsafeRecName_eq (n b : Name) :
    Lean.Compiler.isUnsafeRecName? n = some b ↔ n = Name.str b "_unsafe_rec" := by
  constructor
  · intro h
    unfold Lean.Compiler.isUnsafeRecName? at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  · rintro rfl
    simp [Lean.Compiler.isUnsafeRecName?]

/-- The name under which the compiler looks up the helper of {name}`b` ({name (full := Lean.Compiler.mkUnsafeRecName)}`mkUnsafeRecName`, which
{lit}`getDeclInfo?` reads) is one that {name}`HelperNamed` covers. -/
theorem mkUnsafeRecName_eq (b : Name) :
    Lean.Compiler.mkUnsafeRecName b = Name.str b "_unsafe_rec" := rfl

theorem namedAsHelper_iff (d : Regula.Closed.Decl) :
    Regula.Closed.namedAsHelper d = true ↔ HelperNamed (decl d) := by
  unfold Regula.Closed.namedAsHelper HelperNamed
  simp only [Option.isSome_iff_exists, decl]
  exact exists_congr fun b => isUnsafeRecName_eq d.name b

theorem kindDef_iff (b : Regula.Closed.Decl) :
    b.kind = .definition ↔ (decl b).kind = .definition := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

theorem kindInd_iff (b : Regula.Closed.Decl) :
    b.kind = .inductive ↔ (decl b).kind = .inductive := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

theorem safety_iff (b : Regula.Closed.Decl) (v : Regula.Closed.Safety) :
    b.safety = v ↔ (decl b).safety = safety v := by
  cases hd : b.safety <;> cases v <;> simp [decl, safety, hd]

theorem ctorIdxForm_iff (b : Regula.Closed.Decl) (v : Regula.Closed.CtorIdxForm) :
    b.ctorIdxForm = v ↔ (decl b).ctorIdxForm = ctorIdxForm v := by
  cases hd : b.ctorIdxForm <;> cases v <;> simp [decl, ctorIdxForm, hd]

theorem recursionHelper_iff (d : Regula.Closed.Decl) :
    t.helperForm d = true ↔ (toSpec i).HelperForm (decl d) := by
  have htail : t.helperBaseFits d = true ↔
      ∃ base ∈ (toSpec i).decls, (decl d).name = Name.str base.name "_unsafe_rec" ∧
        base.kind = .definition ∧ base.module = (decl d).module ∧ base.safety = .safe ∧
        base.implementedBy = none ∧ base.isExtern = false := by
    simp only [Regula.Closed.Tables.helperBaseFits]
    split
    · rename_i b hb
      rw [any_index_iff t]
      have hn := (isUnsafeRecName_eq _ _).mp hb
      constructor
      · rintro ⟨x, hx, rfl, hp⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none] at hp
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
        exact ⟨decl x, mem_decls.mpr ⟨x, hx, rfl⟩, hn, (kindDef_iff x).mp h1, h2,
          (safety_iff x .safe).mp h3, h4, h5⟩
      · rintro ⟨x, hx, hxn, h1, h2, h3, h4, h5⟩
        obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
        have hyb : y.name = b := by
          have : Name.str b "_unsafe_rec" = Name.str y.name "_unsafe_rec" := hn.symm.trans hxn
          simpa using this.symm
        refine ⟨y, hy, hyb, ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none]
        exact ⟨⟨⟨⟨(kindDef_iff y).mpr h1, h2⟩, (safety_iff y .safe).mpr h3⟩, h4⟩, h5⟩
    · rename_i hb
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      rintro x - hxn
      have h2 : Lean.Compiler.isUnsafeRecName? d.name = some x.name :=
        (isUnsafeRecName_eq _ _).mpr hxn
      rw [hb] at h2
      cases h2
  simp only [Regula.Closed.Tables.helperForm, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    Option.isNone_iff_eq_none, htail, Input.HelperForm, safety_iff d .partial]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem ctorIdxImpl_iff (d : Regula.Closed.Decl) :
    t.ctorIdxImpl d = true ↔ (toSpec i).CtorIdxImpl (decl d) := by
  have hpair (ind : Name) (defDecl : Regula.Closed.Decl) :
      t.ctorIdxPair ind defDecl d = true ↔
        (∃ tag ∈ (toSpec i).decls, tag.name = `getObjTagNat ∧ tag.inToolchain = true) ∧
        (∃ indDecl ∈ (toSpec i).decls, indDecl.name = ind ∧ indDecl.kind = .inductive ∧
          indDecl.safety = .safe ∧ indDecl.module = (decl d).module) ∧
        (decl d).name = Name.str (Name.str ind "ctorIdx") "_impl" ∧
        (decl d).kind = .definition ∧ (decl d).safety = .unsafe ∧
        (decl d).ctorIdxForm = .impl ind ∧
        (decl d).implementedBy = none ∧ (decl d).isExtern = false ∧
        (decl defDecl).name = Name.str ind "ctorIdx" ∧
        (decl defDecl).module = (decl d).module ∧
        (decl defDecl).kind = .definition ∧ (decl defDecl).safety = .safe ∧
        (decl defDecl).ctorIdxForm = .defn ind ∧
        (decl defDecl).implementedBy = some (Name.str (Name.str ind "ctorIdx") "_impl") ∧
        (decl defDecl).isExtern = false := by
    simp only [Regula.Closed.Tables.ctorIdxPair, Bool.and_eq_true, Bool.not_eq_true',
      beq_iff_eq, Option.isNone_iff_eq_none, any_index_iff t]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨htag, hind⟩, hdn⟩, hdk⟩, hds⟩, hdf⟩, hdi⟩, hde⟩,
        hin⟩, him⟩, hik⟩, his⟩, hif⟩, hii⟩, hie⟩
      refine ⟨?_, ?_, hin, (kindDef_iff d).mp hik, (safety_iff d .unsafe).mp his,
        (ctorIdxForm_iff d (.impl ind)).mp hif, hii, hie,
        hdn, him.symm, (kindDef_iff defDecl).mp hdk, (safety_iff defDecl .safe).mp hds,
        (ctorIdxForm_iff defDecl (.defn ind)).mp hdf, hdi, hde⟩
      · obtain ⟨x, hx, hn, ht⟩ := htag
        exact ⟨decl x, mem_decls.mpr ⟨x, hx, rfl⟩, hn, ht⟩
      · obtain ⟨x, hx, hn, ⟨⟨hk, hs⟩, hm⟩⟩ := hind
        exact ⟨decl x, mem_decls.mpr ⟨x, hx, rfl⟩, hn, (kindInd_iff x).mp hk,
          (safety_iff x .safe).mp hs, hm.trans him.symm⟩
    · rintro ⟨htag, hind, hin, hik, his, hif, hii, hie, hdn, him, hdk, hds, hdf, hdi, hde⟩
      refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, hdn⟩, (kindDef_iff defDecl).mpr hdk⟩,
        (safety_iff defDecl .safe).mpr hds⟩, (ctorIdxForm_iff defDecl (.defn ind)).mpr hdf⟩,
        hdi⟩, hde⟩, hin⟩, him.symm⟩, (kindDef_iff d).mpr hik⟩,
        (safety_iff d .unsafe).mpr his⟩, (ctorIdxForm_iff d (.impl ind)).mpr hif⟩, hii⟩, hie⟩
      · obtain ⟨x, hx, hn, ht⟩ := htag
        obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
        exact ⟨y, hy, hn, ht⟩
      · obtain ⟨x, hx, hn, hk, hs, hm⟩ := hind
        obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
        exact ⟨y, hy, hn, ⟨⟨(kindInd_iff y).mpr hk, (safety_iff y .safe).mpr hs⟩, hm.trans him.symm⟩⟩
  simp only [Regula.Closed.Tables.ctorIdxImpl, Input.CtorIdxImpl]
  cases hcf : d.ctorIdxForm with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists]
    intro ind h
    have h1 := (ctorIdxForm_iff d (.impl ind)).mpr h.2.2.2.2.2.1
    rw [hcf] at h1
    cases h1
  | defn ind =>
    simp only [Bool.false_eq_true, false_iff, not_exists]
    intro ind' h
    have h1 := (ctorIdxForm_iff d (.impl ind')).mpr h.2.2.2.2.2.1
    rw [hcf] at h1
    cases h1
  | impl ind =>
    rw [any_index_iff t]
    constructor
    · rintro ⟨defDecl, hdef, hname, hp⟩
      obtain ⟨htag, hind, hin, hik, his, hif, hii, hie, hdn, him, hdk, hds, hdf, hdi, hde⟩ :=
        (hpair ind defDecl).mp hp
      exact ⟨ind, htag, hind, hin, hik, his, hif, hii, hie,
        decl defDecl, mem_decls.mpr ⟨defDecl, hdef, rfl⟩, hdn, him, hdk, hds, hdf, hdi, hde⟩
    · rintro ⟨ind', htag, hind, hin, hik, his, hif, hii, hie,
        defSpec, hdefSpec, hdn, him, hdk, hds, hdf, hdi, hde⟩
      have heq : ind = ind' := by
        have h1 := (ctorIdxForm_iff d (.impl ind')).mpr hif
        rw [hcf] at h1
        cases h1
        rfl
      subst heq
      obtain ⟨defDecl, hdef, rfl⟩ := mem_decls.mp hdefSpec
      exact ⟨defDecl, hdef, hdn, (hpair ind defDecl).mpr
        ⟨htag, hind, hin, hik, his, hif, hii, hie, hdn, him, hdk, hds, hdf, hdi, hde⟩⟩

theorem mentionsLoop_iff (d : Regula.Closed.Decl) :
    Regula.Closed.mentionsLoop d = true ↔ MentionsLoop (decl d) := by
  simp [Regula.Closed.mentionsLoop, Regula.Closed.loopConstructs, MentionsLoop, loopConstructs,
    decl]

theorem not_safe_iff (d : Regula.Closed.Decl) :
    (d.safety != .safe) = true ↔ (decl d).safety ≠ .safe := by
  cases hd : d.safety <;> simp [decl, safety, hd]

theorem rg1006_exact (s : Name) :
    s ∈ t.rg1006.map (·.subject) ↔ Violates1006 (toSpec i) s := by
  rw [Regula.Closed.Tables.rg1006, mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    refine ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with ⟨⟨hf, hn⟩, hci⟩ | hl
    · refine .inl ⟨?_, fun hh => by simp [(recursionHelper_iff t d).mpr hh] at hn,
        fun hc' => by simp [(ctorIdxImpl_iff t d).mpr hc'] at hci⟩
      rcases hf with hf | hf
      · exact .inl ((not_safe_iff d).mp hf)
      · exact .inr ((namedAsHelper_iff d).mp hf)
    · exact .inr ((mentionsLoop_iff d).mp hl)
  · rintro ⟨x, hx, rfl, hm, hv⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    refine ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ?_, rfl⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    rcases hv with ⟨hf, hh, hci⟩ | hl
    · refine .inl ⟨⟨?_, ?_⟩, ?_⟩
      · rcases hf with hf | hf
        · exact .inl ((not_safe_iff d).mpr hf)
        · exact .inr ((namedAsHelper_iff d).mpr hf)
      · cases hb : t.helperForm d with
        | false => rfl
        | true => exact absurd ((recursionHelper_iff t d).mp hb) hh
      · cases hb : t.ctorIdxImpl d with
        | false => rfl
        | true => exact absurd ((ctorIdxImpl_iff t d).mp hb) hci
    · exact .inr ((mentionsLoop_iff d).mpr hl)

theorem rg1006_reports_named_not_partial {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hm : (toSpec i).ClaimedModule d.module) (hn : HelperNamed (decl d))
    (hp : d.safety ≠ .partial) : d.name ∈ t.rg1006.map (·.subject) :=
  (rg1006_exact t d.name).mpr ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm,
    .inl ⟨.inr hn, fun h => hp ((safety_iff d .partial).mpr h.1), fun hc => by
      obtain ⟨b, hb⟩ := hn
      obtain ⟨ind, -, -, heq, -⟩ := hc
      have hne : Name.str b "_unsafe_rec" = Name.str (Name.str ind "ctorIdx") "_impl" := hb.symm.trans heq
      simp at hne⟩⟩

/-- A constant with the form of a recursion helper, whose value mentions no loop construct, is not
reported. So a rule that refuses each name of the form `b._unsafe_rec`, or all recursion, does not
meet this. -/
theorem rg1006_admits_helper {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hh : (toSpec i).HelperForm (decl d)) (hl : ¬ MentionsLoop (decl d)) :
    d.name ∉ t.rg1006.map (·.subject) := by
  intro h
  obtain ⟨x, hx, hxn, -, hv⟩ := (rg1006_exact t d.name).mp h
  obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
  have hyd : y = d := by
    have hn : y.name = d.name := hxn
    have hg := get_of_mem t hy
    rw [hn, get_of_mem t hd] at hg
    exact (Option.some.inj hg).symm
  subst hyd
  rcases hv with ⟨-, hnot, -⟩ | hm
  · exact hnot hh
  · exact hl hm

/-- A constant with the exempted `ctorIdx._impl` form, whose value mentions no loop construct, is not
reported. -/
theorem rg1006_admits_ctorIdxImpl {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hc : (toSpec i).CtorIdxImpl (decl d)) (hl : ¬ MentionsLoop (decl d)) :
    d.name ∉ t.rg1006.map (·.subject) := by
  intro h
  obtain ⟨x, hx, hxn, -, hv⟩ := (rg1006_exact t d.name).mp h
  obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
  have hyd : y = d := by
    have hn : y.name = d.name := hxn
    have hg := get_of_mem t hy
    rw [hn, get_of_mem t hd] at hg
    exact (Option.some.inj hg).symm
  subst hyd
  rcases hv with ⟨-, -, hnot⟩ | hm
  · exact hnot hc
  · exact hl hm

end Link

end RegulaSpecification
