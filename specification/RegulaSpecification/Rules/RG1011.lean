module

public import RegulaSpecification.Rule
public import Regula.Rules.RG1011
import all Regula.Rule
import all Regula.Rules.RG1011

@[expose] public section

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

def Initialized (d : Decl) : Prop := d.kind = .definition ∧ ∃ fn, d.initFn = some fn

def Replaced (i : Input) (d : Decl) : Prop :=
  ((∃ impl, d.implementedBy = some impl) ∧ ¬ i.CtorIdxDef d) ∨ d.isExtern = true ∨ Initialized d

def ForeignCSimpIn (i : Input) (m c : Name) : Prop :=
  i.ClaimedModule m ∧ i.HasCSimp m c ∧ ¬ i.DeclaredInClaimed c

def ForeignCSimp (i : Input) (c : Name) : Prop := ∃ m, ForeignCSimpIn i m c

def Violates1011 (i : Input) (c : Name) : Prop :=
  (∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ Replaced i d) ∨ ForeignCSimp i c

def rg1011 := ruleRecord "RG1011" Violates1011

namespace Witnesses

def implemented : Decl := { plain `Good.r `Good .definition [] with implementedBy := some `Good.f }

def foreign : Decl := { plain `Good.e `Good .opaque [] with isExtern := true }

def initialized : Decl := { plain `Good.x `Good .definition [] with initFn := some `Good.i }

def initializedOpaque : Decl := { plain `Good.o `Good .opaque [] with initFn := some `Good.i }

def depThm : Decl := plain `Dep.bad `Dep .theorem []

def mergedThm : Decl := plain `Dep.shared `Dep .theorem []

def w1011 : Witnessed Violates1011 where
  support i := i.decls.map (·.name) ++ i.csimps.map (·.thm)
  support_complete i c h := by
    rcases h with ⟨d, hd, hn, -⟩ | ⟨m, -, hcs, -⟩
    · exact List.mem_append_left _ (name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨m, c⟩, hcs, rfl⟩)
  refused := withDecls [implemented] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, implemented])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [implemented, plain]))
  bad := `Good.r
  bad_violates := .inl ⟨implemented, by simp [withDecls], rfl, claimed_withDecls,
    .inl ⟨⟨`Good.f, rfl⟩, fun h => by
      obtain ⟨_, _, _, hp⟩ := h
      obtain ⟨_, _, _, _, _, hcf, _⟩ := hp
      simp [implemented, plain] at hcf⟩⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, hcs, -⟩)
    · rw [t_of_name hd hn] at hr
      simp [Replaced, Initialized, tDecl, plain] at hr
    · simp [Input.HasCSimp, base] at hcs

theorem rg1011_adequate : O2 rg1011 ∧ O2Run rg1011 ∧ O3 rg1011 ∧ O4 rg1011 ∧
    O5 rg1011 (.rel SameReports) := adequate w1011

theorem rg1011_noisy : ¬ rg1011.Meets w1011.candidates :=
  noisy_fails w1011 (List.mem_append_left _ t_mem_support)

def withForeign : Input := withDecls [foreign] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, foreign])

theorem rg1011_refuses_extern : Violates1011 withForeign `Good.e :=
  .inl ⟨foreign, by simp [withForeign, withDecls], rfl, claimed_withDecls, .inr (.inl rfl)⟩

theorem wf_withForeign : withForeign.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [foreign, plain]))

def withInitialized : Input :=
  withDecls [initialized, initializedOpaque]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, initialized, initializedOpaque])

theorem wf_withInitialized : withInitialized.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [initialized, initializedOpaque, plain]))

theorem rg1011_refuses_initialized : Violates1011 withInitialized `Good.x :=
  .inl ⟨initialized, by simp [withInitialized, withDecls], rfl, claimed_withDecls, .inr (.inr ⟨rfl, `Good.i, rfl⟩)⟩

theorem rg1011_admits_initialized_opaque : ¬ Violates1011 withInitialized `Good.o := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, hcs, -⟩)
  · have hmem : initializedOpaque ∈ withInitialized.decls := by simp [withInitialized, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, initializedOpaque, plain])] at hr
    simp [Replaced, Initialized, initializedOpaque, plain] at hr
  · simp [Input.HasCSimp, withInitialized, withDecls, base] at hcs

def withForeignCSimp : Input :=
  { withDecls [depThm] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depThm]) with
    csimps := [⟨`Good, `Dep.bad⟩] }

theorem wf_withForeignCSimp : withForeignCSimp.WellFormed :=
  let h := wf_withDecls [depThm]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depThm])
    (uses_resolve (by simp [depThm, plain]))
  ⟨h.closed, h.claims⟩

theorem rg1011_refuses_foreign_csimp : Violates1011 withForeignCSimp `Dep.bad :=
  .inr ⟨`Good, by simp [withForeignCSimp, withDecls, base, Input.ClaimedModule],
    by simp [withForeignCSimp, Input.HasCSimp],
    by simp [withForeignCSimp, withDecls, base, Input.DeclaredInClaimed]⟩

def withClaimedCSimp : Input :=
  { base with claimedConstants := [`Good.t], csimps := [⟨`Good, `Good.t⟩] }

theorem wf_withClaimedCSimp : withClaimedCSimp.WellFormed := ⟨wf_base.closed, wf_base.claims⟩

theorem rg1011_admits_claimed_csimp : ¬ Violates1011 withClaimedCSimp `Good.t := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, -, hnot⟩)
  · rw [t_of_name hd hn] at hr
    simp [Replaced, Initialized, tDecl, plain] at hr
  · exact hnot (by simp [withClaimedCSimp, base, Input.DeclaredInClaimed])

def withMergedCSimp : Input :=
  { withDecls [mergedThm] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, mergedThm]) with
    claimedConstants := [`Dep.shared]
    csimps := [⟨`Good, `Dep.shared⟩] }

theorem wf_withMergedCSimp : withMergedCSimp.WellFormed :=
  let h := wf_withDecls [mergedThm]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, mergedThm])
    (uses_resolve (by simp [mergedThm, plain]))
  ⟨h.closed, h.claims⟩

theorem rg1011_admits_merged_csimp : ¬ Violates1011 withMergedCSimp `Dep.shared := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, -, hnot⟩)
  · have hmem : mergedThm ∈ withMergedCSimp.decls := by simp [withMergedCSimp, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, mergedThm, plain])] at hr
    simp [Replaced, Initialized, mergedThm, plain] at hr
  · exact hnot (by simp [withMergedCSimp, Input.DeclaredInClaimed])

def withDepCSimp : Input :=
  { withDecls [depThm] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depThm]) with
    csimps := [⟨`Dep, `Dep.bad⟩] }

theorem rg1011_admits_dep_csimp : ¬ Violates1011 withDepCSimp `Dep.bad := by
  rintro (⟨d, hd, hn, hcm, -⟩ | ⟨m, hcm, hcs, -⟩)
  · have hmem : depThm ∈ withDepCSimp.decls := by simp [withDepCSimp, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, depThm, plain])] at hcm
    simp [withDepCSimp, withDecls, base, Input.ClaimedModule, depThm, plain] at hcm
  · simp only [withDepCSimp, Input.HasCSimp, List.mem_singleton, CSimpEntry.mk.injEq] at hcs
    rw [hcs.1] at hcm
    simp [withDepCSimp, withDecls, base, Input.ClaimedModule] at hcm

theorem rg1011_admits_ctorIdx : ¬ Violates1011 withCtorIdx `Good.T.ctorIdx := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, hcs, -⟩)
  · have hmem : ctorIdxDefDecl ∈ withCtorIdx.decls := by simp [withCtorIdx, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, ctorIdxDefDecl, plain])] at hr
    rcases hr with ⟨-, hnc⟩ | hext | hinit
    · refine hnc ⟨`Good.T, ctorIdxImplDecl, by simp [withCtorIdx, withDecls], ?_⟩
      exact ⟨⟨toolchain `getObjTagNat .opaque, by simp [withCtorIdx, withDecls], rfl, rfl⟩,
        ⟨ctorIdxInd, by simp [withCtorIdx, withDecls], rfl, rfl, rfl, rfl⟩,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp [ctorIdxDefDecl, plain] at hext
    · simp [Initialized, ctorIdxDefDecl, plain] at hinit
  · simp [Input.HasCSimp, withCtorIdx, withDecls, base] at hcs

def forgedCtorIdxDef11 : Decl :=
  { plain `Good.T.ctorIdx `Good .definition [`Good.T] with
    implementedBy := some `Good.T.ctorIdx._impl, ctorIdxForm := .none }

def withForgedCtorIdx11 : Input :=
  withDecls [toolchain `getObjTagNat .opaque, ctorIdxInd, forgedCtorIdxDef11, ctorIdxImplDecl]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, ctorIdxInd,
      forgedCtorIdxDef11, ctorIdxImplDecl])

theorem wf_withForgedCtorIdx11 : withForgedCtorIdx11.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, ctorIdxInd,
      forgedCtorIdxDef11, ctorIdxImplDecl]))

theorem rg1011_refuses_forged_ctorIdx : Violates1011 withForgedCtorIdx11 `Good.T.ctorIdx :=
  .inl ⟨forgedCtorIdxDef11, by simp [withForgedCtorIdx11, withDecls], rfl, claimed_withDecls,
    .inl ⟨⟨`Good.T.ctorIdx._impl, rfl⟩, fun h => by
      obtain ⟨_, _, _, hp⟩ := h
      obtain ⟨_, _, _, _, _, hcf, _⟩ := hp
      simp [forgedCtorIdxDef11, plain] at hcf⟩⟩

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem initialized_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1011.initialized d = true ↔ Initialized (decl d) := by
  simp only [Regula.Rules.RG1011.initialized, Initialized, decl, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists]
  cases d.kind <;> simp [constKind]

theorem replaced_iff (d : Regula.Closed.Decl) :
    ((d.implementedBy.isSome && !t.ctorIdxDef d) || d.isExtern || Regula.Rules.RG1011.initialized d) = true ↔
      Replaced (toSpec i) (decl d) := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    ctorIdxDef_iff t d, initialized_iff, Replaced, or_assoc, Option.isSome_iff_exists]
  rfl

theorem foreignCSimps_subject (s : Regula.Closed.Subject) :
    s ∈ (Regula.Rules.RG1011.foreignCSimps i).map (·.subject) ↔
      ∃ e ∈ i.csimps, e.module ∈ i.modules ∧ e.thm ∉ i.claimedConstants ∧
        s = .constant e.thm e.module := by
  unfold Regula.Rules.RG1011.foreignCSimps
  split
  · rename_i h
    simp [List.isEmpty_iff.mp h]
  · constructor
    · intro h
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
      obtain ⟨e, he, hc, rfl⟩ := mem_report_violation hv
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
        Regula.Closed.mem_setOf] at hc
      exact ⟨e, he, hc.1, hc.2, rfl⟩
    · rintro ⟨e, he, hm, hn, rfl⟩
      have h1 := (Regula.Closed.mem_setOf i.modules e.module).mpr hm
      have h2 : (Regula.Closed.setOf i.claimedConstants).contains e.thm = false :=
        Bool.eq_false_iff.mpr fun h => hn ((Regula.Closed.mem_setOf _ _).mp h)
      refine List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨e, he, ite_eq_left ?_⟩, rfl⟩
      simp only [h1, h2, Bool.not_false, Bool.and_self]

theorem foreignCSimps_exact (c m : Name) :
    .constant c m ∈ (Regula.Rules.RG1011.foreignCSimps i).map (·.subject) ↔
      ForeignCSimpIn (toSpec i) m c := by
  rw [foreignCSimps_subject]
  simp only [ForeignCSimpIn, Input.ClaimedModule, Input.HasCSimp, Input.DeclaredInClaimed, toSpec,
    toSpecDraft, List.mem_map]
  constructor
  · rintro ⟨e, he, hm, hn, hs⟩
    cases hs
    exact ⟨hm, ⟨e, he, rfl⟩, hn⟩
  · rintro ⟨hm, ⟨e, he, hmk⟩, hn⟩
    have hmod : e.module = m := congrArg CSimpEntry.module hmk
    have hthm : e.thm = c := congrArg CSimpEntry.thm hmk
    exact ⟨e, he, hmod ▸ hm, hthm ▸ hn, by rw [hmod, hthm]⟩

theorem foreignCSimps_iff (s : Name) :
    s ∈ (Regula.Rules.RG1011.foreignCSimps i).map (·.subject.name) ↔ ForeignCSimp (toSpec i) s := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    have hmem := List.mem_map_of_mem (f := (·.subject)) hv
    obtain ⟨e, -, -, -, hs⟩ := (foreignCSimps_subject v.subject).mp hmem
    rw [hs] at hmem ⊢
    exact ⟨e.module, (foreignCSimps_exact e.thm e.module).mp hmem⟩
  · rintro ⟨m, h⟩
    obtain ⟨v, hv, hs⟩ := List.mem_map.mp ((foreignCSimps_exact s m).mpr h)
    exact List.mem_map.mpr ⟨v, hv, congrArg Regula.Closed.Subject.name hs⟩

theorem replaced_exact (s : Name) :
    s ∈ (Regula.Rules.RG1011.replaced t).map (·.subject.name) ↔
      ∃ d ∈ (toSpec i).decls, d.name = s ∧ (toSpec i).ClaimedModule d.module ∧ Replaced (toSpec i) d := by
  unfold Regula.Rules.RG1011.replaced
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, (replaced_iff t d).mp hc⟩
  · rintro ⟨x, hx, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, (replaced_iff t d).mpr hc, rfl⟩

theorem check_eq_append :
    Regula.Rules.RG1011.check t = Regula.Rules.RG1011.foreignCSimps i ++ Regula.Rules.RG1011.replaced t := by
  simp only [Regula.Rules.RG1011.check]
  split
  · rename_i h
    rw [List.isEmpty_iff.mp h, List.nil_append]
  · rfl

theorem rg1011_exact (s : Name) :
    s ∈ (Regula.Rules.RG1011.check t).map (·.subject.name) ↔ Violates1011 (toSpec i) s := by
  rw [check_eq_append, List.map_append, List.mem_append, foreignCSimps_iff, replaced_exact,
    Violates1011, or_comm]

theorem replaced_subject {v : Regula.Closed.Violation} (hv : v ∈ Regula.Rules.RG1011.replaced t) :
    ∃ d ∈ i.decls, d.module ∈ i.modules ∧ v.subject = .constant d.name d.module := by
  unfold Regula.Rules.RG1011.replaced at hv
  obtain ⟨d, hd, -, rfl⟩ := mem_report_violation hv
  obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
  exact ⟨d, hd, hm, rfl⟩

theorem rg1011_subject {v : Regula.Closed.Violation} (hv : v ∈ Regula.Rules.RG1011.check t) :
    (∃ d ∈ i.decls, d.module ∈ i.modules ∧ v.subject = .constant d.name d.module) ∨
      ∃ e ∈ i.csimps, e.module ∈ i.modules ∧ e.thm ∉ i.claimedConstants ∧
        v.subject = .constant e.thm e.module := by
  rw [check_eq_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact .inr ((foreignCSimps_subject v.subject).mp (List.mem_map_of_mem (f := (·.subject)) hv))
  · exact .inl (replaced_subject t hv)

theorem rg1011_attributed (c m : Name) :
    .constant c m ∈ (Regula.Rules.RG1011.check t).map (·.subject) ↔
      (∃ d ∈ (toSpec i).decls, d.name = c ∧ d.module = m ∧ (toSpec i).ClaimedModule m ∧ Replaced (toSpec i) d) ∨
        ForeignCSimpIn (toSpec i) m c := by
  rw [check_eq_append, List.map_append, List.mem_append, foreignCSimps_exact, or_comm]
  refine or_congr ?_ Iff.rfl
  unfold Regula.Rules.RG1011.replaced
  constructor
  · intro h
    obtain ⟨v, hv, hs⟩ := List.mem_map.mp h
    obtain ⟨d, hd, hc, rfl⟩ := mem_report_violation hv
    have hs : Regula.Closed.Subject.constant d.name d.module = .constant c m := hs
    cases hs
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, rfl, hm, (replaced_iff t d).mp hc⟩
  · rintro ⟨x, hx, rfl, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr
      ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ite_eq_left ((replaced_iff t d).mpr hc)⟩, rfl⟩

theorem check_eq_replaced (h : i.csimps = []) :
    Regula.Rules.RG1011.check t = Regula.Rules.RG1011.replaced t := by
  simp [Regula.Rules.RG1011.check, Regula.Rules.RG1011.foreignCSimps, h]

theorem rg1011_admits_neither {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hi : d.implementedBy = none) (he : d.isExtern = false)
    (hinit : d.initFn = none ∨ d.kind ≠ .definition) :
    d.name ∉ (Regula.Rules.RG1011.replaced t).map (·.subject.name) := by
  intro h
  obtain ⟨x, hx, hxn, -, hr⟩ := (replaced_exact t d.name).mp h
  obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
  have hyd : y = d := by
    have hn : y.name = d.name := hxn
    have hg := get_of_mem t hy
    rw [hn, get_of_mem t hd] at hg
    exact (Option.some.inj hg).symm
  subst hyd
  rcases hr with ⟨⟨impl, himpl⟩, -⟩ | hext | hfn
  · exact absurd (himpl.symm.trans hi) (by simp)
  · exact absurd (hext.symm.trans he) (by simp)
  · have hy := (initialized_iff y).mpr hfn
    simp only [Regula.Rules.RG1011.initialized, Bool.and_eq_true, beq_iff_eq] at hy
    rcases hinit with hnone | hkind
    · simp [hnone] at hy
    · exact hkind hy.1

theorem rg1011_admits_ctorIdxDef {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hc : (toSpec i).CtorIdxDef (decl d)) :
    d.name ∉ (Regula.Rules.RG1011.replaced t).map (·.subject.name) := by
  intro h
  obtain ⟨x, hx, hxn, -, hr⟩ := (replaced_exact t d.name).mp h
  obtain ⟨y, hy, rfl⟩ := mem_decls.mp hx
  have hyd : y = d := by
    have hn : y.name = d.name := hxn
    have hg := get_of_mem t hy
    rw [hn, get_of_mem t hd] at hg
    exact (Option.some.inj hg).symm
  subst hyd
  obtain ⟨_, _, _, hp⟩ := id hc
  obtain ⟨_, _, _, _, _, _, _, hext', hinit', _⟩ := hp
  rcases hr with ⟨-, hnot⟩ | hext | ⟨_, fn, hfn⟩
  · exact hnot hc
  · exact absurd (hext.symm.trans hext') (by simp)
  · exact absurd (hfn.symm.trans hinit') (by simp)

end Link

def rg1011Proved : Proved :=
  ⟨Regula.Rules.RG1011.rule, Violates1011, Link.rg1011_exact, Witnesses.w1011,
    fun t _ hv => .inr (.inr ⟨rfl, Link.rg1011_subject t hv⟩)⟩

def rg1011Checker : Checker Input Name := rg1011Proved.checker

theorem rg1011_meets : rg1011.Meets rg1011Checker := rg1011Proved.meets "RG1011"

theorem rg1011_cases :
    Witnesses.w1011.bad ∈ rg1011Checker ⟨Witnesses.w1011.refused, Witnesses.w1011.refused_wf⟩ ∧
      Witnesses.w1011.fine ∉
        rg1011Checker ⟨Witnesses.w1011.admitted, Witnesses.w1011.admitted_wf⟩ :=
  rg1011Proved.cases_hold

theorem rg1011_checker_refuses_extern :
    `Good.e ∈ rg1011Checker ⟨Witnesses.withForeign, Witnesses.wf_withForeign⟩ :=
  ((meets_iff _).mp rg1011_meets _ _).mpr Witnesses.rg1011_refuses_extern

theorem rg1011_checker_reads_definitions :
    `Good.x ∈ rg1011Checker ⟨Witnesses.withInitialized, Witnesses.wf_withInitialized⟩ ∧
      `Good.o ∉ rg1011Checker ⟨Witnesses.withInitialized, Witnesses.wf_withInitialized⟩ :=
  ⟨((meets_iff _).mp rg1011_meets _ _).mpr Witnesses.rg1011_refuses_initialized,
    fun h => Witnesses.rg1011_admits_initialized_opaque (((meets_iff _).mp rg1011_meets _ _).mp h)⟩

theorem rg1011_checker_refuses_foreign_csimp :
    `Dep.bad ∈ rg1011Checker ⟨Witnesses.withForeignCSimp, Witnesses.wf_withForeignCSimp⟩ :=
  ((meets_iff _).mp rg1011_meets _ _).mpr Witnesses.rg1011_refuses_foreign_csimp

theorem rg1011_checker_admits_claimed_csimp :
    `Good.t ∉ rg1011Checker ⟨Witnesses.withClaimedCSimp, Witnesses.wf_withClaimedCSimp⟩ ∧
      `Dep.shared ∉ rg1011Checker ⟨Witnesses.withMergedCSimp, Witnesses.wf_withMergedCSimp⟩ :=
  ⟨fun h => Witnesses.rg1011_admits_claimed_csimp (((meets_iff _).mp rg1011_meets _ _).mp h),
    fun h => Witnesses.rg1011_admits_merged_csimp (((meets_iff _).mp rg1011_meets _ _).mp h)⟩

theorem rg1011_checker_ctorIdx :
    `Good.T.ctorIdx ∉ rg1011Checker ⟨Witnesses.withCtorIdx, Witnesses.wf_withCtorIdx⟩ ∧
      `Good.T.ctorIdx ∈ rg1011Checker ⟨Witnesses.withForgedCtorIdx11, Witnesses.wf_withForgedCtorIdx11⟩ :=
  ⟨fun h => Witnesses.rg1011_admits_ctorIdx (((meets_iff _).mp rg1011_meets _ _).mp h),
    ((meets_iff _).mp rg1011_meets _ _).mpr Witnesses.rg1011_refuses_forged_ctorIdx⟩

end RegulaSpecification
