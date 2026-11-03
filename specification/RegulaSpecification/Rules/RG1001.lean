import RegulaSpecification.Rule
import Regula.Rules.RG1001

/-!
# RG1001: project axioms

A constant of a claimed module has the kind {lit}`axiom`, the axiom of a native proof included. RG1001 alone
reports an axiom that nothing uses. {name (full := Regula.Rules.RG1001.check)}`Regula.Rules.RG1001.check` is the
function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- RG1001: a claimed module declares an axiom, the axiom of a native proof included. -/
def Violates1001 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ d.kind = .axiom

/-- The intent record of RG1001. -/
def rg1001 := ruleRecord "RG1001" Violates1001

namespace Witnesses

/-- An axiom of a claimed module. -/
def ax : Decl := plain `Good.ax `Good .axiom []

/-- The cases of RG1001. -/
def w1001 : Witnessed Violates1001 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨d, hd, hn, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls [ax] (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, ax])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [ax, plain]))
  bad := `Good.ax
  bad_violates := ⟨ax, by simp [withDecls], rfl, claimed_withDecls, rfl⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨d, hd, hn, -, hk⟩
    rw [t_of_name hd hn] at hk
    simp [tDecl, plain] at hk

theorem rg1001_adequate : O2 rg1001 ∧ O2Run rg1001 ∧ O3 rg1001 ∧ O4 rg1001 ∧
    O5 rg1001 (.rel SameReports) := adequate w1001

theorem rg1001_noisy : ¬ rg1001.Meets w1001.candidates := noisy_fails w1001 t_mem_support

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem rg1001_exact (s : Name) :
    s ∈ (Regula.Rules.RG1001.check t).map (·.subject) ↔ Violates1001 (toSpec i) s := by
  unfold Regula.Rules.RG1001.check
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

end Link

/-- RG1001 with its statement, its proof and its cases, for the registry. -/
def rg1001Proved : Proved := ⟨Regula.Rules.RG1001.rule, Violates1001, Link.rg1001_exact, Witnesses.w1001⟩

/-- The function of RG1001 over the specification's input. -/
def rg1001Checker : Checker Input Name := rg1001Proved.checker

theorem rg1001_meets : rg1001.Meets rg1001Checker := rg1001Proved.meets "RG1001"

theorem rg1001_cases :
    Witnesses.w1001.bad ∈ rg1001Checker ⟨Witnesses.w1001.refused, Witnesses.w1001.refused_wf⟩ ∧
      Witnesses.w1001.fine ∉
        rg1001Checker ⟨Witnesses.w1001.admitted, Witnesses.w1001.admitted_wf⟩ :=
  rg1001Proved.cases_hold

end RegulaSpecification
