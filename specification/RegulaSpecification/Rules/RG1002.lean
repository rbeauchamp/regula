import RegulaSpecification.Rule
import Regula.Rules.RG1002

/-!
# RG1002: proof holes

A constant of a claimed module depends on {name}`sorryAx`, directly or through an import: its transitive axiom
set ({name (full := RegulaSpecification.Input.AxiomOf)}`Input.AxiomOf`) holds it.
{name (full := Regula.Rules.RG1002.check)}`Regula.Rules.RG1002.check` is the function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- RG1002: a constant of a claimed module depends on {name}`sorryAx`. -/
def Violates1002 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ i.AxiomOf c ``sorryAx

/-- The intent record of RG1002. -/
def rg1002 := ruleRecord "RG1002" Violates1002

namespace Witnesses

/-- A theorem that uses {name}`sorryAx`. -/
def hole : List Decl :=
  [toolchain ``sorryAx .axiom, plain `Good.h `Good .theorem [``sorryAx]]

/-- The cases of RG1002. -/
def w1002 : Witnessed Violates1002 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := name_mem (P := fun _ => True) (by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h; exact ⟨d, hd, hn, trivial⟩)
  refused := withDecls hole (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, hole])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [hole, plain, toolchain, base, baseDecls, helperDecl, fDecl]))
  bad := `Good.h
  bad_violates := by
    refine ⟨⟨plain `Good.h `Good .theorem [``sorryAx], by simp [withDecls, hole], rfl,
      claimed_withDecls⟩, ?_, ?_⟩
    · exact .step (plain `Good.h `Good .theorem [``sorryAx]) (by simp [withDecls, hole]) rfl
        (by simp [plain]) (.refl _)
    · exact ⟨toolchain ``sorryAx .axiom, by simp [withDecls, hole], rfl, rfl⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨-, h⟩
    have := base_axioms_t h
    simp at this

theorem rg1002_adequate : O2 rg1002 ∧ O2Run rg1002 ∧ O3 rg1002 ∧ O4 rg1002 ∧
    O5 rg1002 (.rel SameReports) := adequate w1002

theorem rg1002_noisy : ¬ rg1002.Meets w1002.candidates := noisy_fails w1002 t_mem_support

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem rg1002_exact (s : Name) :
    s ∈ (Regula.Rules.RG1002.check t).map (·.subject) ↔ Violates1002 (toSpec i) s := by
  unfold Regula.Rules.RG1002.check
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

end Link

/-- RG1002 with its statement, its proof and its cases, for the registry. -/
def rg1002Proved : Proved := ⟨Regula.Rules.RG1002.rule, Violates1002, Link.rg1002_exact, Witnesses.w1002⟩

/-- The function of RG1002 over the specification's input. -/
def rg1002Checker : Checker Input Name := rg1002Proved.checker

theorem rg1002_meets : rg1002.Meets rg1002Checker := rg1002Proved.meets "RG1002"

theorem rg1002_cases :
    Witnesses.w1002.bad ∈ rg1002Checker ⟨Witnesses.w1002.refused, Witnesses.w1002.refused_wf⟩ ∧
      Witnesses.w1002.fine ∉
        rg1002Checker ⟨Witnesses.w1002.admitted, Witnesses.w1002.admitted_wf⟩ :=
  rg1002Proved.cases_hold

end RegulaSpecification
