/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Tables

/-!
# RG1001 to RG1006, against their statements

`Regula.Closed.Tables.rg1001` to `rg1006` are the functions that the checker runs. For each,
`rg100N_exact` proves that, for every value of `Tables i`, it reports a subject exactly when
`Violates100N` holds of it at `toSpec i`. The rules that read an axiom set read `Tables.axiomSet`, a
function of the input (`axiomSet_iff`).
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

/-- A rule that reports each member of a list that passes a test. -/
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

/-- A filtered list is not empty exactly when a member passes the test. -/
theorem filter_nonempty {α : Type} {l : List α} {p : α → Bool} :
    (!(l.filter p).isEmpty) = true ↔ ∃ a ∈ l, p a = true := by
  simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, List.mem_filter]

/-- The test of a known axiom is `Input.Known`. -/
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

/-- The test of what a profile admits is `Input.Admits`. -/
theorem admits_iff (p : Regula.Closed.Profile) (a : Name) :
    t.admits p a = true ↔ (toSpec i).Admits (profile p) a := by
  cases p with
  | kernelOnly => simp [Regula.Closed.Tables.admits, profile, Input.Admits]
  | choiceFree =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, Bool.and_eq_true,
      Bool.or_eq_true, beq_iff_eq, known_iff t]
  | standardLogical =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, known_iff t]

/-- The test of a native proof's axiom is `NativeProofAxiom`. -/
theorem native_iff (a : Name) : Regula.Closed.nativeProofAxiom a = true ↔ NativeProofAxiom a := by
  constructor
  · intro h
    unfold Regula.Closed.nativeProofAxiom at h
    split at h
    · exact ⟨_, _, _, rfl⟩
    · simp at h
  · rintro ⟨p, t, s, rfl⟩
    simp [Regula.Closed.nativeProofAxiom]

/-- The checker's list of compiler axioms holds nothing. -/
theorem compiler_contains (a : Name) : Regula.Closed.compilerAxioms.contains a = false := by
  simp [Regula.Closed.compilerAxioms]

/-- The specification's list of compiler axioms holds nothing. -/
theorem not_mem_compiler (a : Name) : a ∉ compilerAxioms := by simp [compilerAxioms]

/-- The function that the checker runs reports a constant exactly when it violates RG1001. -/
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

/-- The function that the checker runs reports a constant exactly when it violates RG1002. -/
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

/-- The function that the checker runs reports a constant exactly when it violates RG1003. -/
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

/-- The function that the checker runs reports a constant exactly when it violates RG1004. -/
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

/-- The function that the checker runs reports a constant exactly when it violates RG1005. -/
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

/-- The compiler's own test of a helper's name holds exactly of the form that `HelperNamed`
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

/-- The name under which the compiler looks up the helper of `b` (`mkUnsafeRecName`, which
`getDeclInfo?` reads) is one that `HelperNamed` covers. -/
theorem mkUnsafeRecName_eq (b : Name) :
    Lean.Compiler.mkUnsafeRecName b = Name.str b "_unsafe_rec" := rfl

/-- The test of a helper's name is `HelperNamed`. -/
theorem namedAsHelper_iff (d : Regula.Closed.Decl) :
    Regula.Closed.namedAsHelper d = true ↔ HelperNamed (decl d) := by
  unfold Regula.Closed.namedAsHelper HelperNamed
  simp only [Option.isSome_iff_exists, decl]
  exact exists_congr fun b => isUnsafeRecName_eq d.name b

/-- `kind` is `definition` in the checker exactly when it is in the specification. -/
theorem kindDef_iff (b : Regula.Closed.Decl) :
    b.kind = .definition ↔ (decl b).kind = .definition := by
  cases hd : b.kind <;> simp [decl, constKind, hd]

/-- `safety` has one value in the checker exactly when it has it in the specification. -/
theorem safety_iff (b : Regula.Closed.Decl) (v : Regula.Closed.Safety) :
    b.safety = v ↔ (decl b).safety = safety v := by
  cases hd : b.safety <;> cases v <;> simp [decl, safety, hd]

/-- The test of a recursion helper's form is `Input.RecursionHelper`. -/
theorem recursionHelper_iff (d : Regula.Closed.Decl) :
    t.recursionHelper d = true ↔ (toSpec i).RecursionHelper (decl d) := by
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
  simp only [Regula.Closed.Tables.recursionHelper, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    Option.isNone_iff_eq_none, htail, Input.RecursionHelper, safety_iff d .partial]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-- The test of a loop construct in a value is `MentionsLoop`. -/
theorem mentionsLoop_iff (d : Regula.Closed.Decl) :
    Regula.Closed.mentionsLoop d = true ↔ MentionsLoop (decl d) := by
  simp [Regula.Closed.mentionsLoop, Regula.Closed.loopConstructs, MentionsLoop, loopConstructs,
    decl]

/-- A constant is not safe in the checker exactly when it is not in the specification. -/
theorem not_safe_iff (d : Regula.Closed.Decl) :
    (d.safety != .safe) = true ↔ (decl d).safety ≠ .safe := by
  cases hd : d.safety <;> simp [decl, safety, hd]

/-- The function that the checker runs reports a constant exactly when it violates RG1006. RG1006
reads no axiom set. -/
theorem rg1006_exact (s : Name) :
    s ∈ t.rg1006.map (·.subject) ↔ Violates1006 (toSpec i) s := by
  rw [Regula.Closed.Tables.rg1006, mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    refine ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with ⟨hf, hn⟩ | hl
    · refine .inl ⟨?_, fun hh => by simp [(recursionHelper_iff t d).mpr hh] at hn⟩
      rcases hf with hf | hf
      · exact .inl ((not_safe_iff d).mp hf)
      · exact .inr ((namedAsHelper_iff d).mp hf)
    · exact .inr ((mentionsLoop_iff d).mp hl)
  · rintro ⟨x, hx, rfl, hm, hv⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    refine ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ?_, rfl⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    rcases hv with ⟨hf, hh⟩ | hl
    · refine .inl ⟨?_, ?_⟩
      · rcases hf with hf | hf
        · exact .inl ((not_safe_iff d).mpr hf)
        · exact .inr ((namedAsHelper_iff d).mpr hf)
      · cases hb : t.recursionHelper d with
        | false => rfl
        | true => exact absurd ((recursionHelper_iff t d).mp hb) hh
    · exact .inr ((mentionsLoop_iff d).mpr hl)

/-- Every constant of a claimed module with a helper's name that is not partial is reported,
whatever its kind and however it was declared. -/
theorem rg1006_reports_named_not_partial {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hm : (toSpec i).ClaimedModule d.module) (hn : HelperNamed (decl d))
    (hp : d.safety ≠ .partial) : d.name ∈ t.rg1006.map (·.subject) :=
  (rg1006_exact t d.name).mpr ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm,
    .inl ⟨.inr hn, fun h => hp ((safety_iff d .partial).mpr h.1)⟩⟩

/-- A constant with the form of a recursion helper, whose value mentions no loop construct, is not
reported. So a rule that refuses each name of the form `b._unsafe_rec`, or all recursion, does not
meet this. -/
theorem rg1006_admits_helper {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hh : (toSpec i).RecursionHelper (decl d)) (hl : ¬ MentionsLoop (decl d)) :
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
  rcases hv with ⟨-, hnot⟩ | hm
  · exact hnot hh
  · exact hl hm

end Link

end RegulaSpecification
