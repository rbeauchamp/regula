/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Witnesses

/-!
# Cases of RG1001 and RG1002, and the lemmas the other cases use

Each `w…` gives the case the rule must refuse and the case it must admit; `rg…_adequate` is
lean-intent's obligations for the rule's record, and `rg…_noisy` refutes the checker that reports
every candidate.
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

/-- A list whose images are distinct has one member of each image. -/
theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · rw [ex, ey]
    · exact absurd (List.mem_map.mpr ⟨y, hy', by rw [← hxy, ex]⟩) h.1
    · exact absurd (List.mem_map.mpr ⟨x, hx', by rw [hxy, ey]⟩) h.1
    · exact eq_of_mem_of_nodup_map h.2 hx' hy' hxy

/-- A name determines its constant. -/
theorem eq_of_name {i : Input} {d d' : Decl} (hd : d ∈ i.decls)
    (hd' : d' ∈ i.decls) (h : d.name = d'.name) : d = d' :=
  eq_of_mem_of_nodup_map i.unique hd hd' h

/-- The name of a constant of the input is among the names of its constants. -/
theorem name_mem {i : Input} {c : Name} {P : Decl → Prop} (h : ∃ d ∈ i.decls, d.name = c ∧ P d) :
    c ∈ i.decls.map (·.name) := by
  obtain ⟨d, hd, rfl, -⟩ := h
  exact List.mem_map_of_mem hd

/-- The theorem `Good.t` of `base`. -/
def tDecl : Decl := plain `Good.t `Good .theorem [``propext]

/-- `Good.t` is a constant of `base`. -/
theorem t_mem : tDecl ∈ base.decls := by simp [tDecl, base, baseDecls]

/-- The constant of `base` named `Good.t` is `tDecl`. -/
theorem t_of_name {d : Decl} (hd : d ∈ base.decls) (hn : d.name = `Good.t) : d = tDecl :=
  eq_of_name hd t_mem (by simp [hn, tDecl, plain])

/-- `Good.t` is a candidate of each rule on `base`. -/
theorem t_mem_support : `Good.t ∈ base.decls.map (·.name) := List.mem_map_of_mem t_mem

/-- The profile of `base` admits each axiom of `Good.t`. -/
theorem base_t_admitted {a : Name} (ha : base.AxiomOf `Good.t a) : base.Admits base.profile a := by
  have := base_axioms_t ha
  subst this
  exact ⟨base_known_propext, Or.inl rfl⟩

/-! ## RG1001 -/

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

/-- Every obligation lean-intent states, discharged for RG1001. -/
theorem rg1001_adequate : O2 rg1001 ∧ O2Run rg1001 ∧ O3 rg1001 ∧ O4 rg1001 ∧
    O5 rg1001 (.rel SameReports) := adequate w1001

/-- The checker that reports every candidate does not meet RG1001. -/
theorem rg1001_noisy : ¬ rg1001.Meets w1001.candidates := noisy_fails w1001 t_mem_support

/-! ## RG1002 -/

/-- A theorem that uses `sorryAx`. -/
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

/-- Every obligation lean-intent states, discharged for RG1002. -/
theorem rg1002_adequate : O2 rg1002 ∧ O2Run rg1002 ∧ O3 rg1002 ∧ O4 rg1002 ∧
    O5 rg1002 (.rel SameReports) := adequate w1002

/-- The checker that reports every candidate does not meet RG1002. -/
theorem rg1002_noisy : ¬ rg1002.Meets w1002.candidates := noisy_fails w1002 t_mem_support

end Witnesses

end RegulaSpecification
