module

public import RegulaSpecification.Rule
public import Regula.Rules.RG1011
import all Regula.Rule
import all Regula.Rules.RG1011

/-!
# RG1011: replaced compiled code

A constant of a claimed module has {attr}`@[implemented_by]` or {attr}`@[extern]`, or is a definition for
which {attr}`@[init]` or {attr}`@[builtin_init]` names an initialization function; or a claimed module has
an exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entry whose theorem is not declared in any
claimed module's own {lit}`.olean` data. For the first three, Lean's compiler compiles no code from the
definition: it runs the constant that {attr}`@[implemented_by]` names, a function outside Lean for
{attr}`@[extern]`, or the initialization function, whose result it stores as the constant when the constant
has no parameter, and nothing proves any of them equal to the definition that the constant's proofs are
about. The input reads those three through the queries that the compiler reads
({lit}`Lean.Compiler.getImplementedBy?`, {lit}`Lean.isExtern` and {lit}`Lean.getInitFnNameFor?`).

An initialization function is read of a definition alone. An opaque constant that has one, which the
command {lit}`initialize` declares, is not reported for it: Lean's logic states nothing of an opaque
constant's value, so no proof is about a value that the function replaces. The form of either
attribute that names no function runs a constant of the type {lit}`IO Unit` when the program starts and
replaces nothing, and the input does not hold it.

For {attr}`@[csimp]`, Lean's compiler replaces {lit}`f` by {lit}`g` only through a declaration of equality
type {lit}`@f = @g` ({lit}`isConstantReplacement?`, {lit}`Lean/Compiler/CSimpAttr.lean:40-55` at v4.35.0),
but none of the attribute's checks requires a safe theorem or excludes {name}`sorryAx`, custom axioms, or
{lit}`unsafe def` ({lit}`:40-55, 68-80`), and Lean allows a claimed module to attach {attr}`@[csimp]`
(global or {lit}`scoped`) to a declaration of another module, which can otherwise escape the claim's
kernel replay cone and RG1001 to RG1006 when no claimed constant mentions it. RG1011 refuses every exported ({lit}`global` or {lit}`scoped`)
claimed-module {attr}`@[csimp]` entry whose theorem is not declared in any claimed module's own
{lit}`.olean` data ({name (full := RegulaSpecification.Input.DeclaredInClaimed)}`Input.DeclaredInClaimed`), while admitting exported {attr}`@[csimp]` entries
whose theorem is declared in a claimed module (including a merged theorem whose merged module index
points to an unclaimed dependency), because every such theorem enters the claim's kernel replay cone and
is checked by RG1001 to RG1006 and the loader's unshown-constant check. {lit}`attribute [local csimp]` is
never persisted to {lit}`.olean` ({lit}`Lean/ScopedEnvExtension.lean:17-19, 96-112, 191-193`) and
dependency-registered {attr}`@[csimp]` entries are not read under the proof verdict. Under the full verdict
RG1010 refuses {lit}`csimp` in each file it reads, a project with a {lit}`require` has only the proof
verdict, and the toolchain's own {attr}`@[csimp]` registrations stay trusted. {name (full := Regula.Rules.RG1011.check)}`Regula.Rules.RG1011.check`
is the function that the checker runs.
-/

@[expose] public section

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- {name}`d` is a definition, and {attr}`@[init]` or {attr}`@[builtin_init]` names an initialization function
for it. The compiler then compiles no code from the definition, and stores the function's result in its
place when the definition has no parameter. -/
def Initialized (d : Decl) : Prop := d.kind = .definition ∧ ∃ fn, d.initFn = some fn

/-- The definition of {name}`d` is not what compiled code runs for it: it names a constant that
{attr}`@[implemented_by]` gives, it is {attr}`@[extern]`, or it is a definition with an initialization
function. -/
def Replaced (d : Decl) : Prop :=
  (∃ impl, d.implementedBy = some impl) ∨ d.isExtern = true ∨ Initialized d

/-- The claimed module {name}`m` has an exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entry
naming {name}`c`, and no claimed module's own {lit}`.olean` data declares {name}`c`. A finding of it names
{name}`c` with {name}`m`, the module that registered the entry. -/
def ForeignCSimpIn (i : Input) (m c : Name) : Prop :=
  i.ClaimedModule m ∧ i.HasCSimp m c ∧ ¬ i.DeclaredInClaimed c

/-- A claimed module has an exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entry naming
{name}`c`, and no claimed module's own {lit}`.olean` data declares {name}`c`. -/
def ForeignCSimp (i : Input) (c : Name) : Prop := ∃ m, ForeignCSimpIn i m c

/-- RG1011: a constant of a claimed module has {attr}`@[implemented_by]` or {attr}`@[extern]`, or is a
definition with an initialization function, or a claimed module has an exported {attr}`@[csimp]` entry
whose theorem is not declared in any claimed module. -/
def Violates1011 (i : Input) (c : Name) : Prop :=
  (∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ Replaced d) ∨ ForeignCSimp i c

/-- The intent record of RG1011. -/
def rg1011 := ruleRecord "RG1011" Violates1011

namespace Witnesses

/-- A definition of a claimed module that {attr}`@[implemented_by]` replaces with `Good.f`. -/
def implemented : Decl := { plain `Good.r `Good .definition [] with implementedBy := some `Good.f }

/-- An {attr}`@[extern]` opaque constant of a claimed module. -/
def foreign : Decl := { plain `Good.e `Good .opaque [] with isExtern := true }

/-- A definition of a claimed module for which {attr}`@[init]` names the initialization function `Good.i`. -/
def initialized : Decl := { plain `Good.x `Good .definition [] with initFn := some `Good.i }

/-- An opaque constant of a claimed module with the same initialization function, as the command
{lit}`initialize` declares one. -/
def initializedOpaque : Decl := { plain `Good.o `Good .opaque [] with initFn := some `Good.i }

/-- A theorem declared only in an unclaimed dependency module {lit}`Dep`. -/
def depThm : Decl := plain `Dep.bad `Dep .theorem []

/-- A theorem whose merged module index points to an unclaimed dependency {lit}`Dep`, while a claimed module
also declares it in its own {lit}`.olean` data (merged-theorem case). -/
def mergedThm : Decl := plain `Dep.shared `Dep .theorem []

/-- The cases of RG1011. -/
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
  bad_violates := .inl ⟨implemented, by simp [withDecls], rfl, claimed_withDecls, .inl ⟨`Good.f, rfl⟩⟩
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

/-- {name}`base`, with an {attr}`@[extern]` constant. -/
def withForeign : Input := withDecls [foreign] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, foreign])

theorem rg1011_refuses_extern : Violates1011 withForeign `Good.e :=
  .inl ⟨foreign, by simp [withForeign, withDecls], rfl, claimed_withDecls, .inr (.inl rfl)⟩

theorem wf_withForeign : withForeign.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [foreign, plain]))

/-- {name}`base`, with a definition and an opaque constant that each have an initialization function. -/
def withInitialized : Input :=
  withDecls [initialized, initializedOpaque]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, initialized, initializedOpaque])

theorem wf_withInitialized : withInitialized.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [initialized, initializedOpaque, plain]))

/-- The definition with an initialization function is a violation. -/
theorem rg1011_refuses_initialized : Violates1011 withInitialized `Good.x :=
  .inl ⟨initialized, by simp [withInitialized, withDecls], rfl, claimed_withDecls, .inr (.inr ⟨rfl, `Good.i, rfl⟩)⟩

/-- The opaque constant with the same initialization function, in the same input, is none: the rule reads an
initialization function of a definition alone. -/
theorem rg1011_admits_initialized_opaque : ¬ Violates1011 withInitialized `Good.o := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, hcs, -⟩)
  · have hmem : initializedOpaque ∈ withInitialized.decls := by simp [withInitialized, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, initializedOpaque, plain])] at hr
    simp [Replaced, Initialized, initializedOpaque, plain] at hr
  · simp [Input.HasCSimp, withInitialized, withDecls, base] at hcs

/-- {name}`base`, with a dependency theorem {name}`depThm` registered as {attr}`@[csimp]` by the claimed module {lit}`Good`. -/
def withForeignCSimp : Input :=
  { withDecls [depThm] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depThm]) with
    csimps := [⟨`Good, `Dep.bad⟩] }

theorem wf_withForeignCSimp : withForeignCSimp.WellFormed :=
  let h := wf_withDecls [depThm]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depThm])
    (uses_resolve (by simp [depThm, plain]))
  ⟨h.closed, h.claims⟩

/-- A claimed module's exported {attr}`@[csimp]` entry targeting an unclaimed dependency theorem is a violation. -/
theorem rg1011_refuses_foreign_csimp : Violates1011 withForeignCSimp `Dep.bad :=
  .inr ⟨`Good, by simp [withForeignCSimp, withDecls, base, Input.ClaimedModule],
    by simp [withForeignCSimp, Input.HasCSimp],
    by simp [withForeignCSimp, withDecls, base, Input.DeclaredInClaimed]⟩

/-- {name}`base`, with a claimed theorem `Good.t` registered as {attr}`@[csimp]` by {lit}`Good`. -/
def withClaimedCSimp : Input :=
  { base with claimedConstants := [`Good.t], csimps := [⟨`Good, `Good.t⟩] }

theorem wf_withClaimedCSimp : withClaimedCSimp.WellFormed := ⟨wf_base.closed, wf_base.claims⟩

/-- A claimed module's exported {attr}`@[csimp]` entry targeting a theorem declared in a claimed module is admitted. -/
theorem rg1011_admits_claimed_csimp : ¬ Violates1011 withClaimedCSimp `Good.t := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, -, hnot⟩)
  · rw [t_of_name hd hn] at hr
    simp [Replaced, Initialized, tDecl, plain] at hr
  · exact hnot (by simp [withClaimedCSimp, base, Input.DeclaredInClaimed])

/-- {name}`base`, with a merged theorem {name}`mergedThm` whose merged module is unclaimed {lit}`Dep`, while
a claimed module also declares it in its own {lit}`.olean` data and registers {attr}`@[csimp]` on it. -/
def withMergedCSimp : Input :=
  { withDecls [mergedThm] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, mergedThm]) with
    claimedConstants := [`Dep.shared]
    csimps := [⟨`Good, `Dep.shared⟩] }

theorem wf_withMergedCSimp : withMergedCSimp.WellFormed :=
  let h := wf_withDecls [mergedThm]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, mergedThm])
    (uses_resolve (by simp [mergedThm, plain]))
  ⟨h.closed, h.claims⟩

/-- A merged theorem declared in a claimed module's own {lit}`.olean` data is admitted for {attr}`@[csimp]`,
even when {lit}`Decl.module` names an unclaimed dependency. -/
theorem rg1011_admits_merged_csimp : ¬ Violates1011 withMergedCSimp `Dep.shared := by
  rintro (⟨d, hd, hn, -, hr⟩ | ⟨m, -, -, hnot⟩)
  · have hmem : mergedThm ∈ withMergedCSimp.decls := by simp [withMergedCSimp, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, mergedThm, plain])] at hr
    simp [Replaced, Initialized, mergedThm, plain] at hr
  · exact hnot (by simp [withMergedCSimp, Input.DeclaredInClaimed])

/-- {name}`base`, with a dependency-registered {attr}`@[csimp]` entry in unclaimed module {lit}`Dep`. -/
def withDepCSimp : Input :=
  { withDecls [depThm] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depThm]) with
    csimps := [⟨`Dep, `Dep.bad⟩] }

/-- A dependency-registered {attr}`@[csimp]` entry in an unclaimed module is outside RG1011. -/
theorem rg1011_admits_dep_csimp : ¬ Violates1011 withDepCSimp `Dep.bad := by
  rintro (⟨d, hd, hn, hcm, -⟩ | ⟨m, hcm, hcs, -⟩)
  · have hmem : depThm ∈ withDepCSimp.decls := by simp [withDepCSimp, withDecls]
    rw [eq_of_name hd hmem (by simp [hn, depThm, plain])] at hcm
    simp [withDepCSimp, withDecls, base, Input.ClaimedModule, depThm, plain] at hcm
  · simp only [withDepCSimp, Input.HasCSimp, List.mem_singleton, CSimpEntry.mk.injEq] at hcs
    rw [hcs.1] at hcm
    simp [withDepCSimp, withDecls, base, Input.ClaimedModule] at hcm

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem initialized_iff (d : Regula.Closed.Decl) :
    Regula.Rules.RG1011.initialized d = true ↔ Initialized (decl d) := by
  simp only [Regula.Rules.RG1011.initialized, Initialized, decl, Bool.and_eq_true, beq_iff_eq,
    Option.isSome_iff_exists]
  cases d.kind <;> simp [constKind]

theorem replaced_iff (d : Regula.Closed.Decl) :
    (d.implementedBy.isSome || d.isExtern || Regula.Rules.RG1011.initialized d) = true ↔ Replaced (decl d) := by
  simp only [Bool.or_eq_true, initialized_iff, Replaced, or_assoc, Option.isSome_iff_exists]
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

/-- The check's {attr}`@[csimp]` clause reports the constant {name}`c` with the module {name}`m` exactly when
{name}`m` is a claimed module whose exported entry names {name}`c` and no claimed module declares {name}`c`.
So each claimed module that registers a foreign theorem is reported with it, and no other module is. -/
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

/-- What the check reported before the {attr}`@[csimp]` clause, which {name}`Regula.Rules.RG1011.replaced`
still reports, is exactly the replaced constants of claimed modules. -/
theorem replaced_exact (s : Name) :
    s ∈ (Regula.Rules.RG1011.replaced t).map (·.subject.name) ↔
      ∃ d ∈ (toSpec i).decls, d.name = s ∧ (toSpec i).ClaimedModule d.module ∧ Replaced d := by
  unfold Regula.Rules.RG1011.replaced
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, (replaced_iff d).mp hc⟩
  · rintro ⟨x, hx, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, (replaced_iff d).mpr hc, rfl⟩

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

/-- A violation that {name}`Regula.Rules.RG1011.replaced` reports carries the name and the module of a
declaration of a claimed module. -/
theorem replaced_subject {v : Regula.Closed.Violation} (hv : v ∈ Regula.Rules.RG1011.replaced t) :
    ∃ d ∈ i.decls, d.module ∈ i.modules ∧ v.subject = .constant d.name d.module := by
  unfold Regula.Rules.RG1011.replaced at hv
  obtain ⟨d, hd, -, rfl⟩ := mem_report_violation hv
  obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
  exact ⟨d, hd, hm, rfl⟩

/-- A violation of the check carries the name and the module of a declaration of a claimed module, or the
theorem of a claimed module's exported {attr}`@[csimp]` entry that no claimed module declares, with that
claimed module. -/
theorem rg1011_subject {v : Regula.Closed.Violation} (hv : v ∈ Regula.Rules.RG1011.check t) :
    (∃ d ∈ i.decls, d.module ∈ i.modules ∧ v.subject = .constant d.name d.module) ∨
      ∃ e ∈ i.csimps, e.module ∈ i.modules ∧ e.thm ∉ i.claimedConstants ∧
        v.subject = .constant e.thm e.module := by
  rw [check_eq_append] at hv
  rcases List.mem_append.mp hv with hv | hv
  · exact .inr ((foreignCSimps_subject v.subject).mp (List.mem_map_of_mem (f := (·.subject)) hv))
  · exact .inl (replaced_subject t hv)

/-- The check reports the constant {name}`c` with the module {name}`m` exactly when {name}`c` is a replaced
constant of the claimed module {name}`m`, or {name}`m` is a claimed module whose exported {attr}`@[csimp]`
entry names {name}`c` and no claimed module declares {name}`c`. -/
theorem rg1011_attributed (c m : Name) :
    .constant c m ∈ (Regula.Rules.RG1011.check t).map (·.subject) ↔
      (∃ d ∈ (toSpec i).decls, d.name = c ∧ d.module = m ∧ (toSpec i).ClaimedModule m ∧ Replaced d) ∨
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
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, rfl, hm, (replaced_iff d).mp hc⟩
  · rintro ⟨x, hx, rfl, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact List.mem_map.mpr ⟨_, List.mem_filterMap.mpr
      ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, ite_eq_left ((replaced_iff d).mpr hc)⟩, rfl⟩

/-- On an input with {lit}`i.csimps = []` (no exported {attr}`@[csimp]` entry; for loader output, no
claimed-module exported {attr}`@[csimp]` entry), the check reports what it reported before that clause,
in the same order. -/
theorem check_eq_replaced (h : i.csimps = []) :
    Regula.Rules.RG1011.check t = Regula.Rules.RG1011.replaced t := by
  simp [Regula.Rules.RG1011.check, Regula.Rules.RG1011.foreignCSimps, h]

/-- A constant with neither {attr}`@[implemented_by]` nor {attr}`@[extern]`, that has no initialization function
or is no definition, is not among what {name}`Regula.Rules.RG1011.replaced` reports, whatever else it has. So
a rule that refuses every definition, every constant with an initialization function, or every constant that
compiled code replaces by any means, does not meet this. The check reports such a constant only by its
{attr}`@[csimp]` clause ({name}`rg1011_attributed`). -/
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
  rcases hr with ⟨impl, himpl⟩ | hext | hfn
  · exact absurd (himpl.symm.trans hi) (by simp)
  · exact absurd (hext.symm.trans he) (by simp)
  · have hy := (initialized_iff y).mpr hfn
    simp only [Regula.Rules.RG1011.initialized, Bool.and_eq_true, beq_iff_eq] at hy
    rcases hinit with hnone | hkind
    · simp [hnone] at hy
    · exact hkind hy.1

end Link

/-- RG1011 with its statement, its proofs and its cases, for the registry. -/
def rg1011Proved : Proved :=
  ⟨Regula.Rules.RG1011.rule, Violates1011, Link.rg1011_exact, Witnesses.w1011,
    fun t _ hv => .inr (.inr ⟨rfl, Link.rg1011_subject t hv⟩)⟩

/-- The function of RG1011 over the specification's input. -/
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

/-- The checker's function reports the definition with an initialization function, and not the opaque constant
with the same function. -/
theorem rg1011_checker_reads_definitions :
    `Good.x ∈ rg1011Checker ⟨Witnesses.withInitialized, Witnesses.wf_withInitialized⟩ ∧
      `Good.o ∉ rg1011Checker ⟨Witnesses.withInitialized, Witnesses.wf_withInitialized⟩ :=
  ⟨((meets_iff _).mp rg1011_meets _ _).mpr Witnesses.rg1011_refuses_initialized,
    fun h => Witnesses.rg1011_admits_initialized_opaque (((meets_iff _).mp rg1011_meets _ _).mp h)⟩

/-- The checker's function reports an unclaimed dependency theorem registered as {attr}`@[csimp]` by a claimed module. -/
theorem rg1011_checker_refuses_foreign_csimp :
    `Dep.bad ∈ rg1011Checker ⟨Witnesses.withForeignCSimp, Witnesses.wf_withForeignCSimp⟩ :=
  ((meets_iff _).mp rg1011_meets _ _).mpr Witnesses.rg1011_refuses_foreign_csimp

/-- The checker's function admits a claimed theorem and a merged claimed theorem registered as {attr}`@[csimp]`. -/
theorem rg1011_checker_admits_claimed_csimp :
    `Good.t ∉ rg1011Checker ⟨Witnesses.withClaimedCSimp, Witnesses.wf_withClaimedCSimp⟩ ∧
      `Dep.shared ∉ rg1011Checker ⟨Witnesses.withMergedCSimp, Witnesses.wf_withMergedCSimp⟩ :=
  ⟨fun h => Witnesses.rg1011_admits_claimed_csimp (((meets_iff _).mp rg1011_meets _ _).mp h),
    fun h => Witnesses.rg1011_admits_merged_csimp (((meets_iff _).mp rg1011_meets _ _).mp h)⟩

end RegulaSpecification
