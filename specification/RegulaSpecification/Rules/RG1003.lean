import RegulaSpecification.Rule
import Regula.Rules.RG1003

/-!
# RG1003: unknown axioms

A constant of a claimed module depends on an axiom other than {name}`propext`, {name}`Quot.sound` and
{name}`Classical.choice` of the toolchain, and RG1002 and RG1004 do not name it.
{name (full := Regula.Rules.RG1003.check)}`Regula.Rules.RG1003.check` is the function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- RG1003: a constant of a claimed module depends on an axiom that is not one of the known
three, and that RG1002 and RG1004 do not name. -/
def Violates1003 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ ∃ a, i.AxiomOf c a ∧ ¬ i.Known a ∧ a ≠ ``sorryAx ∧
    ¬ NativeProofAxiom a ∧ a ∉ compilerAxioms

/-- The intent record of RG1003. -/
def rg1003 := ruleRecord "RG1003" Violates1003

namespace Witnesses

/-- A theorem that uses an axiom of a dependency. -/
def depAxiom : List Decl := [plain `Dep.ax `Dep .axiom [], plain `Good.u `Good .theorem [`Dep.ax]]

/-- The cases of RG1003. -/
def w1003 : Witnessed Violates1003 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls depAxiom
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depAxiom])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [depAxiom, plain, base, baseDecls, toolchain, helperDecl, fDecl]))
  bad := `Good.u
  bad_violates := by
    refine ⟨⟨plain `Good.u `Good .theorem [`Dep.ax], by simp [withDecls, depAxiom], rfl,
      claimed_withDecls⟩, `Dep.ax, ⟨?_, ?_⟩, ?_, by simp, ?_, by simp [compilerAxioms]⟩
    · exact .step (plain `Good.u `Good .theorem [`Dep.ax]) (by simp [withDecls, depAxiom]) rfl
        (by simp [plain]) (.refl _)
    · exact ⟨plain `Dep.ax `Dep .axiom [], by simp [withDecls, depAxiom], rfl, rfl⟩
    · exact not_known_of_not_logical (by simp [logicalAxioms])
    · exact not_native_of_components (by simp [components])
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨-, a, ha, hk, -⟩
    rw [base_axioms_t ha] at hk
    exact hk base_known_propext

theorem rg1003_adequate : O2 rg1003 ∧ O2Run rg1003 ∧ O3 rg1003 ∧ O4 rg1003 ∧
    O5 rg1003 (.rel SameReports) := adequate w1003

theorem rg1003_noisy : ¬ rg1003.Meets w1003.candidates := noisy_fails w1003 t_mem_support

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem rg1003_exact (s : Name) :
    s ∈ (Regula.Rules.RG1003.check t).map (·.subject) ↔ Violates1003 (toSpec i) s := by
  unfold Regula.Rules.RG1003.check
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

end Link

/-- RG1003 with its statement, its proof and its cases, for the registry. -/
def rg1003Proved : Proved := ⟨Regula.Rules.RG1003.rule, Violates1003, Link.rg1003_exact, Witnesses.w1003⟩

/-- The function of RG1003 over the specification's input. -/
def rg1003Checker : Checker Input Name := rg1003Proved.checker

theorem rg1003_meets : rg1003.Meets rg1003Checker := rg1003Proved.meets "RG1003"

theorem rg1003_cases :
    Witnesses.w1003.bad ∈ rg1003Checker ⟨Witnesses.w1003.refused, Witnesses.w1003.refused_wf⟩ ∧
      Witnesses.w1003.fine ∉
        rg1003Checker ⟨Witnesses.w1003.admitted, Witnesses.w1003.admitted_wf⟩ :=
  rg1003Proved.cases_hold

end RegulaSpecification
