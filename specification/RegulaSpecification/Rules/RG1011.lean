import RegulaSpecification.Rule
import Regula.Rules.RG1011

/-!
# RG1011: replaced compiled code

A constant of a claimed module has {attr}`@[implemented_by]` or {attr}`@[extern]`, or is a definition for
which {attr}`@[init]` or {attr}`@[builtin_init]` names an initialization function. Lean's compiler then
compiles no code from its definition: it runs the constant that {attr}`@[implemented_by]` names, a
function outside Lean for {attr}`@[extern]`, or the initialization function, whose result it stores as
the constant, and nothing proves any of them equal to the definition that the constant's proofs are
about. The input reads the three through the queries that the compiler reads
({lit}`Lean.Compiler.getImplementedBy?`, {lit}`Lean.isExtern` and {lit}`Lean.getInitFnNameFor?`).

An initialization function is read of a definition alone. An opaque constant that has one, which the
command {lit}`initialize` declares, is not reported for it: Lean's logic states nothing of an opaque
constant's value, so no proof is about a value that the function replaces. The form of either
attribute that names no function runs a constant of the type {lit}`IO Unit` when the program starts and
replaces nothing, and the input does not hold it.

{attr}`@[csimp]` is not read, so this rule does not report a constant that has it and none of the
three. Its theorem states {lit}`@f = @g`, and the compiler replaces {lit}`f` by {lit}`g` only through such a
theorem ({lit}`isConstantReplacement?`, {lit}`Lean/Compiler/CSimpAttr.lean:40-55` at v4.35.0), so the
replacement equals the original in Lean's logic as far as that theorem's proof is sound. On a pass,
Lean's kernel checked each theorem of a claimed module in the replay of the cone, and each axiom that it
reaches is one that the profile admits (RG1002 to RG1005). {name (full := Regula.Rules.RG1011.check)}`Regula.Rules.RG1011.check`
is the function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- An initialization function stands in for the value of {name}`d` in compiled code: {name}`d` is a
definition, and {attr}`@[init]` or {attr}`@[builtin_init]` names a function for it. -/
def Initialized (d : Decl) : Prop := d.kind = .definition ∧ ∃ fn, d.initFn = some fn

/-- The definition of {name}`d` is not what compiled code runs for it: it names a constant that
{attr}`@[implemented_by]` gives, it is {attr}`@[extern]`, or it is a definition with an initialization
function. -/
def Replaced (d : Decl) : Prop :=
  (∃ impl, d.implementedBy = some impl) ∨ d.isExtern = true ∨ Initialized d

/-- RG1011: a constant of a claimed module has {attr}`@[implemented_by]` or {attr}`@[extern]`, or is a
definition with an initialization function. -/
def Violates1011 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ Replaced d

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

/-- The cases of RG1011. -/
def w1011 : Witnessed Violates1011 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨d, hd, hn, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls [implemented] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, implemented])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [implemented, plain]))
  bad := `Good.r
  bad_violates := ⟨implemented, by simp [withDecls], rfl, claimed_withDecls, .inl ⟨`Good.f, rfl⟩⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨d, hd, hn, -, hr⟩
    rw [t_of_name hd hn] at hr
    simp [Replaced, Initialized, tDecl, plain] at hr

theorem rg1011_adequate : O2 rg1011 ∧ O2Run rg1011 ∧ O3 rg1011 ∧ O4 rg1011 ∧
    O5 rg1011 (.rel SameReports) := adequate w1011

theorem rg1011_noisy : ¬ rg1011.Meets w1011.candidates := noisy_fails w1011 t_mem_support

/-- {name}`base`, with an {attr}`@[extern]` constant. -/
def withForeign : Input := withDecls [foreign] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, foreign])

theorem rg1011_refuses_extern : Violates1011 withForeign `Good.e :=
  ⟨foreign, by simp [withForeign, withDecls], rfl, claimed_withDecls, .inr (.inl rfl)⟩

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
  ⟨initialized, by simp [withInitialized, withDecls], rfl, claimed_withDecls, .inr (.inr ⟨rfl, `Good.i, rfl⟩)⟩

/-- The opaque constant with the same initialization function, in the same input, is none: the rule reads an
initialization function of a definition alone. -/
theorem rg1011_admits_initialized_opaque : ¬ Violates1011 withInitialized `Good.o := by
  rintro ⟨d, hd, hn, -, hr⟩
  have hmem : initializedOpaque ∈ withInitialized.decls := by simp [withInitialized, withDecls]
  rw [eq_of_name hd hmem (by simp [hn, initializedOpaque, plain])] at hr
  simp [Replaced, Initialized, initializedOpaque, plain] at hr

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

theorem rg1011_exact (s : Name) :
    s ∈ (Regula.Rules.RG1011.check t).map (·.subject) ↔ Violates1011 (toSpec i) s := by
  unfold Regula.Rules.RG1011.check
  rw [mem_report (sub := (·.name)) (fun _ => rfl)]
  constructor
  · rintro ⟨d, hd, hc, rfl⟩
    obtain ⟨hd, hm⟩ := (mem_claimed t).mp hd
    exact ⟨decl d, mem_decls.mpr ⟨d, hd, rfl⟩, rfl, hm, (replaced_iff d).mp hc⟩
  · rintro ⟨x, hx, rfl, hm, hc⟩
    obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
    exact ⟨d, (mem_claimed t).mpr ⟨hd, hm⟩, (replaced_iff d).mpr hc, rfl⟩

/-- A constant with neither {attr}`@[implemented_by]` nor {attr}`@[extern]`, that has no initialization function
or is no definition, is not reported, whatever else it has: the input holds no other attribute,
{attr}`@[csimp]` among them. So a rule that refuses every definition, every constant with an initialization
function, or every constant that compiled code replaces by any means, does not meet this. -/
theorem rg1011_admits_neither {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hi : d.implementedBy = none) (he : d.isExtern = false)
    (hinit : d.initFn = none ∨ d.kind ≠ .definition) :
    d.name ∉ (Regula.Rules.RG1011.check t).map (·.subject) := by
  intro h
  obtain ⟨x, hx, hxn, -, hr⟩ := (rg1011_exact t d.name).mp h
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

/-- RG1011 with its statement, its proof and its cases, for the registry. -/
def rg1011Proved : Proved := ⟨Regula.Rules.RG1011.rule, Violates1011, Link.rg1011_exact, Witnesses.w1011⟩

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

end RegulaSpecification
