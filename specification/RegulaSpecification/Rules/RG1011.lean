import RegulaSpecification.Rule
import Regula.Rules.RG1011

/-!
# RG1011: replaced compiled code

A constant of a claimed module has {attr}`@[implemented_by]` or {attr}`@[extern]`. Lean's compiler then
compiles no code from its definition: it runs the constant that {attr}`@[implemented_by]` names, or a
function outside Lean for {attr}`@[extern]`, and nothing proves either equal to the definition that the
constant's proofs are about. The input reads both through the queries that the compiler reads
({lit}`Lean.Compiler.getImplementedBy?` and {lit}`Lean.isExtern`).

{attr}`@[csimp]` is not read, so this rule does not report a constant that has it and neither of the
two. Its theorem states {lit}`@f = @g`, and the compiler replaces {lit}`f` by {lit}`g` only through such a
theorem ({lit}`isConstantReplacement?`, {lit}`Lean/Compiler/CSimpAttr.lean:40-55` at v4.35.0), so the
replacement equals the original in Lean's logic as far as that theorem's proof is sound. On a pass,
Lean's kernel checked each theorem of a claimed module in the replay of the cone, and each axiom that it
reaches is one that the profile admits (RG1002 to RG1005). {name (full := Regula.Rules.RG1011.check)}`Regula.Rules.RG1011.check`
is the function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- The definition of {name}`d` is not what compiled code runs for it: it names a constant that
{attr}`@[implemented_by]` gives, or it is {attr}`@[extern]`. -/
def Replaced (d : Decl) : Prop := (∃ impl, d.implementedBy = some impl) ∨ d.isExtern = true

/-- RG1011: a constant of a claimed module has {attr}`@[implemented_by]` or {attr}`@[extern]`. -/
def Violates1011 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ Replaced d

/-- The intent record of RG1011. -/
def rg1011 := ruleRecord "RG1011" Violates1011

namespace Witnesses

/-- A definition of a claimed module that {attr}`@[implemented_by]` replaces with `Good.f`. -/
def implemented : Decl := { plain `Good.r `Good .definition [] with implementedBy := some `Good.f }

/-- An {attr}`@[extern]` opaque constant of a claimed module. -/
def foreign : Decl := { plain `Good.e `Good .opaque [] with isExtern := true }

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
    simp [Replaced, tDecl, plain] at hr

theorem rg1011_adequate : O2 rg1011 ∧ O2Run rg1011 ∧ O3 rg1011 ∧ O4 rg1011 ∧
    O5 rg1011 (.rel SameReports) := adequate w1011

theorem rg1011_noisy : ¬ rg1011.Meets w1011.candidates := noisy_fails w1011 t_mem_support

/-- {name}`base`, with an {attr}`@[extern]` constant. -/
def withForeign : Input := withDecls [foreign] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, foreign])

theorem rg1011_refuses_extern : Violates1011 withForeign `Good.e :=
  ⟨foreign, by simp [withForeign, withDecls], rfl, claimed_withDecls, .inr rfl⟩

theorem wf_withForeign : withForeign.WellFormed :=
  wf_withDecls _ _
    (uses_resolve (by simp [foreign, plain]))

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem replaced_iff (d : Regula.Closed.Decl) :
    (d.implementedBy.isSome || d.isExtern) = true ↔ Replaced (decl d) := by
  simp [Replaced, decl, Option.isSome_iff_exists]

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

/-- A constant with neither {attr}`@[implemented_by]` nor {attr}`@[extern]` is not reported, whatever else it
has: the input holds no other attribute, {attr}`@[csimp]` among them. So a rule that refuses every
definition, or every constant that compiled code replaces by any means, does not meet this. -/
theorem rg1011_admits_neither {d : Regula.Closed.Decl} (hd : d ∈ i.decls)
    (hi : d.implementedBy = none) (he : d.isExtern = false) :
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
  rcases hr with ⟨impl, himpl⟩ | hext
  · exact absurd (himpl.symm.trans hi) (by simp)
  · exact absurd (hext.symm.trans he) (by simp)

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

end RegulaSpecification
