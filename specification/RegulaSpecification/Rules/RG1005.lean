import RegulaSpecification.Rule
import Regula.Rules.RG1005

/-!
# RG1005: the profile

A constant of a claimed module depends on an axiom that the project's profile does not admit. Kernel-only
admits no axiom, choice-free admits {name}`propext` and {name}`Quot.sound`, and standard-logical also admits
{name}`Classical.choice`, each the toolchain's own ({lit}`Input.Admits`).
{name (full := Regula.Rules.RG1005.check)}`Regula.Rules.RG1005.check` is the function that the checker runs.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Input

variable (i : Input)

/-- Profile {lit}`p` admits axiom {lit}`a`: a known axiom in the profile's set. -/
def Admits : Profile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, a => i.Known a ∧ (a = ``propext ∨ a = ``Quot.sound)
  | .standardLogical, a => i.Known a

end Input

/-- RG1005: a constant of a claimed module depends on an axiom that the project's profile does not
admit. -/
def Violates1005 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ ∃ a, i.AxiomOf c a ∧ ¬ i.Admits i.profile a

/-- The intent record of RG1005. -/
def rg1005 := ruleRecord "RG1005" Violates1005

theorem admits_known {i : Input} {p : Profile} {a : Name} (h : i.Admits p a) : i.Known a := by
  cases p with
  | kernelOnly => exact absurd h id
  | choiceFree => exact h.1
  | standardLogical => exact h

theorem rg1005_of_known {i : Input} {c a : Name} (hc : i.ClaimedName c) (ha : i.AxiomOf c a)
    (hk : ¬ i.Known a) : Violates1005 i c := by
  exact ⟨hc, a, ha, fun h => hk (admits_known h)⟩

namespace Witnesses

theorem base_t_admitted {a : Name} (ha : base.AxiomOf `Good.t a) : base.Admits base.profile a := by
  have := base_axioms_t ha
  subst this
  exact ⟨base_known_propext, Or.inl rfl⟩

/-- A theorem that uses {name}`Classical.choice`, which the profile of {name}`base` does not admit. -/
def choice : List Decl :=
  [toolchain ``Classical.choice .axiom, plain `Good.c `Good .theorem [``Classical.choice]]

/-- The cases of RG1005. -/
def w1005 : Witnessed Violates1005 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls choice
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, choice])
  refused_wf := wf_withDecls _ _
    (uses_resolve (by simp [choice, plain, base, baseDecls, toolchain, helperDecl, fDecl]))
  bad := `Good.c
  bad_violates := by
    refine ⟨⟨plain `Good.c `Good .theorem [``Classical.choice], by simp [withDecls, choice], rfl,
      claimed_withDecls⟩, ``Classical.choice, ⟨?_, ?_⟩, ?_⟩
    · exact .step (plain `Good.c `Good .theorem [``Classical.choice])
        (by simp [withDecls, choice]) rfl (by simp [plain]) (.refl _)
    · exact ⟨toolchain ``Classical.choice .axiom, by simp [withDecls, choice], rfl, rfl⟩
    · rintro ⟨-, h | h⟩ <;> simp at h
  admitted := base
  admitted_wf := wf_base
  fine := `Good.t
  fine_admitted := by
    rintro ⟨-, a, ha, hna⟩
    exact hna (base_t_admitted ha)

theorem rg1005_adequate : O2 rg1005 ∧ O2Run rg1005 ∧ O3 rg1005 ∧ O4 rg1005 ∧
    O5 rg1005 (.rel SameReports) := adequate w1005

theorem rg1005_noisy : ¬ rg1005.Meets w1005.candidates := noisy_fails w1005 t_mem_support

end Witnesses

namespace Link

variable {i : Regula.Closed.Input} (t : Regula.Closed.Tables i)

theorem admits_iff (p : Regula.Closed.Profile) (a : Name) :
    t.admits p a = true ↔ (toSpec i).Admits (profile p) a := by
  cases p with
  | kernelOnly => simp [Regula.Closed.Tables.admits, profile, Input.Admits]
  | choiceFree =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, Bool.and_eq_true,
      Bool.or_eq_true, beq_iff_eq, known_iff t]
  | standardLogical =>
    simp only [Regula.Closed.Tables.admits, profile, Input.Admits, known_iff t]

theorem rg1005_exact (s : Name) :
    s ∈ (Regula.Rules.RG1005.check t).map (·.subject) ↔ Violates1005 (toSpec i) s := by
  unfold Regula.Rules.RG1005.check
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

end Link

/-- RG1005 with its statement, its proof and its cases, for the registry. -/
def rg1005Proved : Proved := ⟨Regula.Rules.RG1005.rule, Violates1005, Link.rg1005_exact, Witnesses.w1005⟩

/-- The function of RG1005 over the specification's input. -/
def rg1005Checker : Checker Input Name := rg1005Proved.checker

theorem rg1005_meets : rg1005.Meets rg1005Checker := rg1005Proved.meets "RG1005"

theorem rg1005_cases :
    Witnesses.w1005.bad ∈ rg1005Checker ⟨Witnesses.w1005.refused, Witnesses.w1005.refused_wf⟩ ∧
      Witnesses.w1005.fine ∉
        rg1005Checker ⟨Witnesses.w1005.admitted, Witnesses.w1005.admitted_wf⟩ :=
  rg1005Proved.cases_hold

end RegulaSpecification
