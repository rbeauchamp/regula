module

public import RegulaSpecification.Rule
public import Regula.Rules.RG1006
public import Lean.Compiler.Old
import all Init.Prelude
import all Lean.Compiler.Old
import all Regula.Rule
import all Regula.Rules.RG1006

@[expose] public section

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

namespace Input

variable (i : Input)

def HelperForm (d : Decl) : Prop :=
  d.safety = .partial ∧ d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ base ∈ i.decls, d.name = Name.str base.name "_unsafe_rec" ∧ base.kind = .definition ∧
      base.module = d.module ∧ base.safety = .safe ∧ base.implementedBy = none ∧
      base.isExtern = false

end Input

def HelperNamed (d : Decl) : Prop := ∃ b : Name, d.name = Name.str b "_unsafe_rec"

def MentionsLoop (d : Decl) : Prop := ∃ l ∈ loopConstructs, l ∈ d.valueUses

def MentionsOrderFix (d : Decl) : Prop :=
  (d.kind = .definition ∨ d.kind = .opaque) ∧ ``Lean.Order.fix ∈ d.valueUses

def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧
    (((d.safety ≠ .safe ∨ HelperNamed d) ∧ ¬ i.HelperForm d ∧ ¬ i.CtorIdxImpl d) ∨
      MentionsLoop d ∨ MentionsOrderFix d)

def SafeMentionsSafe (i : Input) : Prop :=
  ∀ d ∈ i.decls, d.safety = .safe → ∀ u ∈ d.uses, ∀ q ∈ i.decls, q.name = u → q.safety = .safe

theorem Input.eq_of_name_eq {l : List Decl} (h : (l.map (·.name)).Nodup) {a b : Decl} (ha : a ∈ l) (hb : b ∈ l)
    (he : a.name = b.name) : a = b := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact absurd (List.mem_map.mpr ⟨b, hb', he.symm⟩) h1
    · exact absurd (List.mem_map.mpr ⟨a, ha', he⟩) h1
    · exact ih h2 ha' hb'

theorem safe_reach_safe {i : Input} (h : SafeMentionsSafe i) {c e : Name} (hr : i.Reaches c e) :
    ∀ d ∈ i.decls, d.name = c → d.safety = .safe → ∀ p ∈ i.decls, p.name = e → p.safety = .safe := by
  induction hr with
  | refl c =>
    intro d hd hc hs p hp he
    have hsame : p = d := Input.eq_of_name_eq i.unique hp hd (he.trans hc.symm)
    rw [hsame]
    exact hs
  | @step c u e d₀ hd₀ hc₀ hu hrest ih =>
    intro d hd hc hs p hp he
    have hsame : d₀ = d := Input.eq_of_name_eq i.unique hd₀ hd (hc₀.trans hc.symm)
    subst hsame
    by_cases hq : ∃ q ∈ i.decls, q.name = u
    · obtain ⟨q, hqm, hqn⟩ := hq
      exact ih q hqm hqn (h d₀ hd₀ hs u hu q hqm hqn) p hp he
    · cases hrest with
      | refl => exact absurd ⟨p, hp, he⟩ hq
      | step x hx hxn _ _ => exact absurd ⟨x, hx, hxn⟩ hq

theorem helperForm_unreached {i : Input} (h : SafeMentionsSafe i) {d p : Decl} (hd : d ∈ i.decls) (hs : d.safety = .safe)
    (hp : p ∈ i.decls) (hf : i.HelperForm p) : ¬ i.Reaches d.name p.name := fun hr => by
  have := safe_reach_safe h hr d hd rfl hs p hp rfl
  rw [hf.1] at this
  cases this

theorem ctorIdxImpl_unreached {i : Input} (h : SafeMentionsSafe i) {d p : Decl} (hd : d ∈ i.decls)
    (hs : d.safety = .safe) (hp : p ∈ i.decls) (hc : i.CtorIdxImpl p) :
    ¬ i.Reaches d.name p.name := fun hr => by
  have hs' := safe_reach_safe h hr d hd rfl hs p hp rfl
  obtain ⟨_, _, _, hp'⟩ := hc
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hunsafe, _⟩ := hp'
  rw [hunsafe] at hs'
  cases hs'

def rg1006 := ruleRecord "RG1006" Violates1006

namespace Witnesses

def partialDecl : Decl := { plain `Good.p `Good .definition [] with safety := .partial }

theorem helper_mem : helperDecl ∈ base.decls := by simp [base, baseDecls]

theorem base_helper : base.HelperForm helperDecl :=
  ⟨rfl, rfl, rfl, fDecl, by simp [base, baseDecls], rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem base_safeMentionsSafe : SafeMentionsSafe base := by
  unfold SafeMentionsSafe
  decide +kernel

theorem safeMentionsSafe_refutable : ¬ SafeMentionsSafe (withDecls [partialDecl, plain `Good.m `Good .definition [`Good.p]]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, partialDecl])) := by
  unfold SafeMentionsSafe
  decide +kernel

def w1006 : Witnessed Violates1006 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨d, hd, hn, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls [partialDecl]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, partialDecl])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [partialDecl, plain]))
  bad := `Good.p
  bad_violates := by
    refine ⟨partialDecl, by simp [withDecls], rfl, claimed_withDecls,
      .inl ⟨Or.inl (by simp [partialDecl, plain]), ?_, ?_⟩⟩
    · rintro ⟨-, -, -, b, -, hn, -⟩
      simp [partialDecl, plain] at hn
    · rintro ⟨_, _, _, hp⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hunsafe, _⟩ := hp
      simp [partialDecl, plain] at hunsafe
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f._unsafe_rec
  fine_admitted := by
    rintro ⟨d, hd, hn, -, ⟨-, hnot, -⟩ | ⟨l, -, hl⟩ | ⟨-, hf⟩⟩
    · rw [eq_of_name hd helper_mem (by simp [hn, helperDecl, plain])] at hnot
      exact hnot base_helper
    · rw [eq_of_name hd helper_mem (by simp [hn, helperDecl, plain])] at hl
      simp [helperDecl, plain] at hl
    · rw [eq_of_name hd helper_mem (by simp [hn, helperDecl, plain])] at hf
      simp [helperDecl, plain] at hf

theorem rg1006_adequate : O2 rg1006 ∧ O2Run rg1006 ∧ O3 rg1006 ∧ O4 rg1006 ∧
    O5 rg1006 (.rel SameReports) := adequate w1006

theorem rg1006_noisy : ¬ rg1006.Meets w1006.candidates :=
  noisy_fails w1006 (List.mem_map_of_mem helper_mem)

def forgedDecl : Decl := plain `Good.g._unsafe_rec `Good .definition []

def withForged : Input := withDecls [plain `Good.g `Good .definition [], forgedDecl]
  (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, forgedDecl])

theorem rg1006_refuses_forged_name : Violates1006 withForged `Good.g._unsafe_rec := by
  refine ⟨forgedDecl, by simp [withForged, withDecls], rfl, claimed_withDecls,
    .inl ⟨Or.inr ⟨`Good.g, rfl⟩, ?_, ?_⟩⟩
  · rintro ⟨h, -⟩
    simp [forgedDecl, plain] at h
  · rintro ⟨_, _, _, hp⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hunsafe, _⟩ := hp
    simp [forgedDecl, plain] at hunsafe

theorem wf_withForged : withForged.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [plain, forgedDecl]))

def loopUser (l : Name) : Decl := { plain `Good.l `Good .definition [l] with valueUses := [l] }

def withLoop {l : Name} (hl : l ∈ loopConstructs) : Input :=
  withDecls [toolchain l .definition, loopUser l] (by
    simp only [loopConstructs, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, loopUser])

theorem rg1006_refuses_loop {l : Name} (hl : l ∈ loopConstructs) :
    Violates1006 (withLoop hl) `Good.l :=
  ⟨loopUser l, by simp [withLoop, withDecls], rfl, claimed_withDecls,
    .inr (.inl ⟨l, hl, by simp [loopUser]⟩)⟩

theorem wf_withLoop {l : Name} (hl : l ∈ loopConstructs) : (withLoop hl).WellFormed := by
  simp only [loopConstructs, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;>
    exact wf_withDecls _ _
      (uses_resolve (by simp [plain, toolchain, loopUser, base, baseDecls, helperDecl, fDecl]))

theorem rg1006_admits_type_mention :
    ¬ MentionsLoop (plain `Good.l `Good .definition [``Lean.Loop.mk]) := by
  rintro ⟨l, -, h⟩
  simp [plain] at h

def fixDef : Decl :=
  { plain `Good.fixDef `Good .definition [``Lean.Order.fix] with valueUses := [``Lean.Order.fix] }

def fixOpaque : Decl :=
  { plain `Good.fixOpaque `Good .opaque [``Lean.Order.fix] with valueUses := [``Lean.Order.fix] }

def fixThm : Decl :=
  { plain `Good.fixThm `Good .theorem [``Lean.Order.fix] with valueUses := [``Lean.Order.fix] }

def lfpDef : Decl :=
  { plain `Good.lfpDef `Good .definition [``Lean.Order.lfp_monotone] with
    valueUses := [``Lean.Order.lfp_monotone] }

def fixTypeOnly : Decl := plain `Good.fixType `Good .definition [``Lean.Order.fix]

def withFixpoint : Input :=
  withDecls [toolchain ``Lean.Order.fix .definition, toolchain ``Lean.Order.lfp_monotone .definition,
      fixDef, fixOpaque, fixThm, lfpDef, fixTypeOnly]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, fixDef, fixOpaque, fixThm,
      lfpDef, fixTypeOnly])

theorem wf_withFixpoint : withFixpoint.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, fixDef, fixOpaque,
      fixThm, lfpDef, fixTypeOnly]))

theorem rg1006_refuses_fix_def : Violates1006 withFixpoint `Good.fixDef :=
  ⟨fixDef, by simp [withFixpoint, withDecls], rfl, claimed_withDecls,
    .inr (.inr ⟨.inl rfl, by simp [fixDef]⟩)⟩

theorem rg1006_refuses_fix_opaque : Violates1006 withFixpoint `Good.fixOpaque :=
  ⟨fixOpaque, by simp [withFixpoint, withDecls], rfl, claimed_withDecls,
    .inr (.inr ⟨.inr rfl, by simp [fixOpaque]⟩)⟩

theorem rg1006_admits_fix_theorem : ¬ Violates1006 withFixpoint `Good.fixThm := by
  rintro ⟨d, hd, hn, -, hv⟩
  have hmem : fixThm ∈ withFixpoint.decls := by simp [withFixpoint, withDecls]
  rw [eq_of_name hd hmem (by simp [hn, fixThm, plain])] at hv
  rcases hv with ⟨hflag, -⟩ | ⟨l, hl, hu⟩ | ⟨hk, -⟩
  · rcases hflag with hs | ⟨b, hb⟩
    · simp [fixThm, plain] at hs
    · simp [fixThm, plain] at hb
  · simp [fixThm, loopConstructs] at hl hu
    rcases hl with rfl | rfl <;> simp at hu
  · simp [fixThm, plain] at hk

theorem rg1006_admits_lfp_monotone : ¬ Violates1006 withFixpoint `Good.lfpDef := by
  rintro ⟨d, hd, hn, -, hv⟩
  have hmem : lfpDef ∈ withFixpoint.decls := by simp [withFixpoint, withDecls]
  rw [eq_of_name hd hmem (by simp [hn, lfpDef, plain])] at hv
  rcases hv with ⟨hflag, -⟩ | ⟨l, hl, hu⟩ | ⟨-, hu⟩
  · rcases hflag with hs | ⟨b, hb⟩
    · simp [lfpDef, plain] at hs
    · simp [lfpDef, plain] at hb
  · simp [lfpDef, loopConstructs] at hl hu
    rcases hl with rfl | rfl <;> simp at hu
  · simp [lfpDef] at hu

theorem rg1006_admits_fix_type_mention : ¬ Violates1006 withFixpoint `Good.fixType := by
  rintro ⟨d, hd, hn, -, hv⟩
  have hmem : fixTypeOnly ∈ withFixpoint.decls := by simp [withFixpoint, withDecls]
  rw [eq_of_name hd hmem (by simp [hn, fixTypeOnly, plain])] at hv
  rcases hv with ⟨hflag, -⟩ | ⟨l, -, hu⟩ | ⟨-, hu⟩
  · rcases hflag with hs | ⟨b, hb⟩
    · simp [fixTypeOnly, plain] at hs
    · simp [fixTypeOnly, plain] at hb
  · simp [fixTypeOnly, plain] at hu
  · simp [fixTypeOnly, plain] at hu

theorem rg1006_admits_ctorIdx : ¬ Violates1006 withCtorIdx `Good.T.ctorIdx._impl := by
  rintro ⟨d, hd, hn, -, hv⟩
  have hmem : ctorIdxImplDecl ∈ withCtorIdx.decls := by simp [withCtorIdx, withDecls]
  rw [eq_of_name hd hmem (by simp [hn, ctorIdxImplDecl, plain])] at hv
  rcases hv with ⟨-, -, hnc⟩ | ⟨l, -, hu⟩ | ⟨-, hu⟩
  · refine hnc ⟨`Good.T, ctorIdxDefDecl, by simp [withCtorIdx, withDecls], ?_⟩
    exact ⟨⟨toolchain `getObjTagNat .opaque, by simp [withCtorIdx, withDecls], rfl, rfl⟩,
      ⟨ctorIdxInd, by simp [withCtorIdx, withDecls], rfl, rfl, rfl, rfl⟩,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [ctorIdxImplDecl, plain] at hu
  · simp [ctorIdxImplDecl, plain] at hu

def forgedCtorIdxImpl : Decl :=
  { plain `Good.T.ctorIdx._impl `Good .definition [`Good.T, `getObjTagNat] with
    safety := .unsafe, ctorIdxForm := .none }

def withForgedCtorIdx : Input :=
  withDecls [toolchain `getObjTagNat .opaque, ctorIdxInd, ctorIdxDefDecl, forgedCtorIdxImpl]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, ctorIdxInd, ctorIdxDefDecl,
      forgedCtorIdxImpl])

theorem wf_withForgedCtorIdx : withForgedCtorIdx.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, ctorIdxInd,
      ctorIdxDefDecl, forgedCtorIdxImpl]))

theorem rg1006_refuses_forged_ctorIdx : Violates1006 withForgedCtorIdx `Good.T.ctorIdx._impl := by
  refine ⟨forgedCtorIdxImpl, by simp [withForgedCtorIdx, withDecls], rfl, claimed_withDecls,
    .inl ⟨.inl (by simp [forgedCtorIdxImpl, plain]), ?_, ?_⟩⟩
  · rintro ⟨h, -⟩
    simp [forgedCtorIdxImpl, plain] at h
  · rintro ⟨_, _, _, hp⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hcf, _⟩ := hp
    simp [forgedCtorIdxImpl, plain] at hcf

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

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

theorem mkUnsafeRecName_eq (b : Name) :
    Lean.Compiler.mkUnsafeRecName b = Name.str b "_unsafe_rec" := by
  rfl

theorem namedAsHelper_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1006.namedAsHelper d = true ↔ HelperNamed (decl d) := by
  unfold Regula.Rules.RG1006.namedAsHelper HelperNamed
  simp only [Option.isSome_iff_exists, decl]
  exact exists_congr fun b => isUnsafeRecName_eq d.name b

theorem recursionHelper_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1006.helperForm t d = true ↔ (toSpec i).HelperForm (decl d) := by
  have htail : Regula.Rules.RG1006.helperBaseFits t d = true ↔
      ∃ base ∈ (toSpec i).decls, (decl d).name = Name.str base.name "_unsafe_rec" ∧
        base.kind = .definition ∧ base.module = (decl d).module ∧ base.safety = .safe ∧
        base.implementedBy = none ∧ base.isExtern = false := by
    simp only [Regula.Rules.RG1006.helperBaseFits]
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
  simp only [Regula.Rules.RG1006.helperForm, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    Option.isNone_iff_eq_none, htail, Input.HelperForm, safety_iff d .partial]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem mentionsLoop_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1006.mentionsLoop d = true ↔ MentionsLoop (decl d) := by
  simp [Regula.Rules.RG1006.mentionsLoop, Regula.Closed.loopConstructs, MentionsLoop, loopConstructs,
    decl]

theorem mentionsOrderFix_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1006.mentionsOrderFix d = true ↔ MentionsOrderFix (decl d) := by
  cases hd : d.kind <;>
    simp [Regula.Rules.RG1006.mentionsOrderFix, MentionsOrderFix, decl, constKind, hd]

theorem not_safe_iff (d : Regula.Closed.Decl) :
    (d.safety != .safe) = true ↔ (decl d).safety ≠ .safe := by
  cases hd : d.safety <;> simp [decl, safety, hd]

theorem rg1006_exact (s : Name) :
    s ∈ (Regula.Rules.RG1006.check t).map (·.subject.name) ↔ Violates1006 (toSpec i) s := by
  rw [Regula.Rules.RG1006.check, mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    refine ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hc
    rcases hc with (⟨⟨hf, hn⟩, hci⟩ | hl) | hpf
    · refine .inl ⟨?_, fun hh => by simp [(recursionHelper_iff t d).mpr hh] at hn,
        fun hc' => by simp [(ctorIdxImpl_iff t d).mpr hc'] at hci⟩
      rcases hf with hf | hf
      · exact .inl ((not_safe_iff d).mp hf)
      · exact .inr ((namedAsHelper_iff d).mp hf)
    · exact .inr (.inl ((mentionsLoop_iff d).mp hl))
    · exact .inr (.inr ((mentionsOrderFix_iff d).mp hpf))
  · rintro ⟨x, hx, rfl, hm, hv⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    refine ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ?_, rfl⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
    rcases hv with ⟨hf, hh, hci⟩ | hl | hpf
    · refine .inl (.inl ⟨⟨?_, ?_⟩, ?_⟩)
      · rcases hf with hf | hf
        · exact .inl ((not_safe_iff d).mpr hf)
        · exact .inr ((namedAsHelper_iff d).mpr hf)
      · cases hb : Regula.Rules.RG1006.helperForm t d with
        | false => rfl
        | true => exact absurd ((recursionHelper_iff t d).mp hb) hh
      · cases hc : t.ctorIdxImpl d with
        | false => rfl
        | true => exact absurd ((ctorIdxImpl_iff t d).mp hc) hci
    · exact .inl (.inr ((mentionsLoop_iff d).mpr hl))
    · exact .inr ((mentionsOrderFix_iff d).mpr hpf)

theorem rg1006_subject {v : Regula.Closed.Violation} (hv : v ∈ Regula.Rules.RG1006.check t) :
    ∃ d ∈ i.decls, v.subject = .constant d.name d.module := by
  obtain ⟨d, hd, -, rfl⟩ := mem_report_violation hv
  exact ⟨d, ((mem_claimed t).mp hd).1, rfl⟩

theorem rg1006_reports_named_not_partial {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hm : (toSpec i).ClaimedModule d.module) (hn : HelperNamed (decl d))
    (hp : d.safety ≠ .partial) : d.name ∈ (Regula.Rules.RG1006.check t).map (·.subject.name) :=
  (rg1006_exact t d.name).mpr ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm,
    .inl ⟨.inr hn, fun h => hp ((safety_iff d .partial).mpr h.1), fun hc => by
      obtain ⟨_, _, _, hp'⟩ := hc
      obtain ⟨_, _, _, _, _, _, _, _, _, hin, _⟩ := hp'
      obtain ⟨b, hb⟩ := hn
      rw [hb] at hin
      simp at hin⟩⟩

theorem rg1006_admits_helper {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hh : (toSpec i).HelperForm (decl d)) (hl : ¬ MentionsLoop (decl d))
    (hpf : ¬ MentionsOrderFix (decl d)) :
    d.name ∉ (Regula.Rules.RG1006.check t).map (·.subject.name) := by
  intro h
  obtain ⟨x, hx, hxn, -, hv⟩ := (rg1006_exact t d.name).mp h
  obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
  have hyd : y = d := by
    have hn : y.name = d.name := hxn
    have hg := get_of_mem t hy
    rw [hn, get_of_mem t hd] at hg
    exact (Option.some.inj hg).symm
  subst hyd
  rcases hv with ⟨-, hnot, -⟩ | hm | hfix
  · exact hnot hh
  · exact hl hm
  · exact hpf hfix

theorem rg1006_admits_ctorIdxImpl {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hc : (toSpec i).CtorIdxImpl (decl d)) (hl : ¬ MentionsLoop (decl d))
    (hpf : ¬ MentionsOrderFix (decl d)) :
    d.name ∉ (Regula.Rules.RG1006.check t).map (·.subject.name) := by
  intro h
  obtain ⟨x, hx, hxn, -, hv⟩ := (rg1006_exact t d.name).mp h
  obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
  have hyd : y = d := by
    have hn : y.name = d.name := hxn
    have hg := get_of_mem t hy
    rw [hn, get_of_mem t hd] at hg
    exact (Option.some.inj hg).symm
  subst hyd
  rcases hv with ⟨-, -, hnot⟩ | hm | hfix
  · exact hnot hc
  · exact hl hm
  · exact hpf hfix

end Link

def rg1006Proved : Proved :=
  ⟨Regula.Rules.RG1006.rule, Violates1006, Link.rg1006_exact, Witnesses.w1006,
    fun t _ hv => .inl ⟨by decide, Link.rg1006_subject t hv⟩⟩

def rg1006Checker : Checker Input Name := rg1006Proved.checker

theorem rg1006_meets : rg1006.Meets rg1006Checker := rg1006Proved.meets "RG1006"

theorem rg1006_cases :
    Witnesses.w1006.bad ∈ rg1006Checker ⟨Witnesses.w1006.refused, Witnesses.w1006.refused_wf⟩ ∧
      Witnesses.w1006.fine ∉
        rg1006Checker ⟨Witnesses.w1006.admitted, Witnesses.w1006.admitted_wf⟩ :=
  rg1006Proved.cases_hold

theorem rg1006_checker_refuses_loop {l : Name} (hl : l ∈ loopConstructs) :
    `Good.l ∈ rg1006Checker ⟨Witnesses.withLoop hl, Witnesses.wf_withLoop hl⟩ :=
  ((meets_iff _).mp rg1006_meets _ _).mpr (Witnesses.rg1006_refuses_loop hl)

theorem rg1006_checker_refuses_forged_name :
    `Good.g._unsafe_rec ∈ rg1006Checker ⟨Witnesses.withForged, Witnesses.wf_withForged⟩ :=
  ((meets_iff _).mp rg1006_meets _ _).mpr Witnesses.rg1006_refuses_forged_name

theorem rg1006_checker_refuses_partial_fixpoint :
    `Good.fixDef ∈ rg1006Checker ⟨Witnesses.withFixpoint, Witnesses.wf_withFixpoint⟩ ∧
      `Good.fixOpaque ∈ rg1006Checker ⟨Witnesses.withFixpoint, Witnesses.wf_withFixpoint⟩ :=
  ⟨((meets_iff _).mp rg1006_meets _ _).mpr Witnesses.rg1006_refuses_fix_def,
    ((meets_iff _).mp rg1006_meets _ _).mpr Witnesses.rg1006_refuses_fix_opaque⟩

theorem rg1006_checker_admits_fix_theorem_and_lfp :
    `Good.fixThm ∉ rg1006Checker ⟨Witnesses.withFixpoint, Witnesses.wf_withFixpoint⟩ ∧
      `Good.lfpDef ∉ rg1006Checker ⟨Witnesses.withFixpoint, Witnesses.wf_withFixpoint⟩ ∧
      `Good.fixType ∉ rg1006Checker ⟨Witnesses.withFixpoint, Witnesses.wf_withFixpoint⟩ :=
  ⟨fun h => Witnesses.rg1006_admits_fix_theorem (((meets_iff _).mp rg1006_meets _ _).mp h),
    fun h => Witnesses.rg1006_admits_lfp_monotone (((meets_iff _).mp rg1006_meets _ _).mp h),
    fun h => Witnesses.rg1006_admits_fix_type_mention (((meets_iff _).mp rg1006_meets _ _).mp h)⟩

theorem rg1006_checker_ctorIdx :
    `Good.T.ctorIdx._impl ∉ rg1006Checker ⟨Witnesses.withCtorIdx, Witnesses.wf_withCtorIdx⟩ ∧
      `Good.T.ctorIdx._impl ∈ rg1006Checker ⟨Witnesses.withForgedCtorIdx, Witnesses.wf_withForgedCtorIdx⟩ :=
  ⟨fun h => Witnesses.rg1006_admits_ctorIdx (((meets_iff _).mp rg1006_meets _ _).mp h),
    ((meets_iff _).mp rg1006_meets _ _).mpr Witnesses.rg1006_refuses_forged_ctorIdx⟩

end RegulaSpecification
