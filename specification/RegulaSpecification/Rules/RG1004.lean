import RegulaSpecification.Rule
import Regula.Rules.RG1004

/-!
# RG1004: native proofs

A constant of a claimed module depends on an axiom with the name form that {tactic}`native_decide`,
{tactic}`decide +native` and {tactic}`bv_decide` give ({name (full := RegulaSpecification.NativeProofAxiom)}`NativeProofAxiom`), or on an axiom by which the
kernel trusts the compiler ({name (full := RegulaSpecification.compilerAxioms)}`compilerAxioms`). {name (full := Regula.Rules.RG1004.check)}`Regula.Rules.RG1004.check`
is the function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

/-- RG1004: a constant of a claimed module depends on a native proof's axiom or on an axiom by
which the kernel trusts the compiler. -/
def Violates1004 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ ∃ a, i.AxiomOf c a ∧ (NativeProofAxiom a ∨ a ∈ compilerAxioms)

/-- The intent record of RG1004. -/
def rg1004 := ruleRecord "RG1004" Violates1004

namespace Witnesses

/-- A theorem that uses the axiom of a native proof. -/
def native : List Decl :=
  [plain `Good.n._native.native_decide.ax_1 `Good .axiom [],
    plain `Good.n `Good .theorem [`Good.n._native.native_decide.ax_1]]

/-- The cases of RG1004. -/
def w1004 : Witnessed Violates1004 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls native
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, native])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [native, plain, base, baseDecls, toolchain, helperDecl, fDecl]))
  bad := `Good.n
  bad_violates := by
    refine ⟨⟨plain `Good.n `Good .theorem [`Good.n._native.native_decide.ax_1],
      by simp [withDecls, native], rfl, claimed_withDecls⟩,
      `Good.n._native.native_decide.ax_1, ⟨?_, ?_⟩, Or.inl ⟨`Good.n, "native_decide", "ax_1", rfl⟩⟩
    · exact .step (plain `Good.n `Good .theorem [`Good.n._native.native_decide.ax_1])
        (by simp [withDecls, native]) rfl (by simp [plain]) (.refl _)
    · exact ⟨plain `Good.n._native.native_decide.ax_1 `Good .axiom [],
        by simp [withDecls, native], rfl, rfl⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨-, a, ha, hn⟩
    rw [base_axioms_t ha] at hn
    rcases hn with hn | hn
    · exact not_native_of_components (by simp [components]) hn
    · simp [compilerAxioms] at hn

theorem rg1004_adequate : O2 rg1004 ∧ O2Run rg1004 ∧ O3 rg1004 ∧ O4 rg1004 ∧
    O5 rg1004 (.rel SameReports) := adequate w1004

theorem rg1004_noisy : ¬ rg1004.Meets w1004.candidates := noisy_fails w1004 t_mem_support

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem rg1004_exact (s : Name) :
    s ∈ (Regula.Rules.RG1004.check t).map (·.subject) ↔ Violates1004 (toSpec i) s := by
  unfold Regula.Rules.RG1004.check
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

end Link

/-- RG1004 with its statement, its proof and its cases, for the registry. -/
def rg1004Proved : Proved := ⟨Regula.Rules.RG1004.rule, Violates1004, Link.rg1004_exact, Witnesses.w1004⟩

/-- The function of RG1004 over the specification's input. -/
def rg1004Checker : Checker Input Name := rg1004Proved.checker

theorem rg1004_meets : rg1004.Meets rg1004Checker := rg1004Proved.meets "RG1004"

theorem rg1004_cases :
    Witnesses.w1004.bad ∈ rg1004Checker ⟨Witnesses.w1004.refused, Witnesses.w1004.refused_wf⟩ ∧
      Witnesses.w1004.fine ∉
        rg1004Checker ⟨Witnesses.w1004.admitted, Witnesses.w1004.admitted_wf⟩ :=
  rg1004Proved.cases_hold

end RegulaSpecification
