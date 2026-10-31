import RegulaSpecification.CasesDeclarations

/-!
# Cases of RG1003 to RG1006
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

theorem not_native_of_components {a : Name} (h : components a < 3) : ¬ NativeProofAxiom a :=
  fun hn => absurd (components_of_native hn) (by omega)

theorem not_known_of_not_logical {i : Input} {a : Name} (h : a ∉ logicalAxioms) : ¬ i.Known a :=
  fun hk => h hk.1

/-! ## RG1003 -/

def depAxiom : List Decl := [plain `Dep.ax `Dep .axiom [], plain `Good.u `Good .theorem [`Dep.ax]]

def w1003 : Witnessed Violates1003 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls depAxiom
  refused_wf := wf_withDecls depAxiom
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, depAxiom])
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

theorem rg1003_noisy : ¬ rg1003.Meets w1003.support := noisy_fails w1003 t_mem_support

/-! ## RG1004 -/

def native : List Decl :=
  [plain `Good.n._native.native_decide.ax_1 `Good .axiom [],
    plain `Good.n `Good .theorem [`Good.n._native.native_decide.ax_1]]

def w1004 : Witnessed Violates1004 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls native
  refused_wf := wf_withDecls native
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, native])
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

theorem rg1004_noisy : ¬ rg1004.Meets w1004.support := noisy_fails w1004 t_mem_support

/-! ## RG1005 -/

def choice : List Decl :=
  [toolchain ``Classical.choice .axiom, plain `Good.c `Good .theorem [``Classical.choice]]

def w1005 : Witnessed Violates1005 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨⟨d, hd, hn, -⟩, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls choice
  refused_wf := wf_withDecls choice
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, choice])
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

theorem rg1005_noisy : ¬ rg1005.Meets w1005.support := noisy_fails w1005 t_mem_support

/-! ## RG1006 -/

def partialDecl : Decl := { plain `Good.p `Good .definition [] with isPartial := true }

theorem helper_mem : helperDecl ∈ base.decls := by simp [base, baseDecls]

theorem base_helper : base.RecursionHelper helperDecl :=
  ⟨rfl, rfl, rfl, rfl, fDecl, by simp [base, baseDecls], rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

def w1006 : Witnessed Violates1006 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨d, hd, hn, -⟩ := h
    exact name_mem (P := fun _ => True) ⟨d, hd, hn, trivial⟩
  refused := withDecls [partialDecl]
  refused_wf := wf_withDecls [partialDecl]
    (by simp [base, baseDecls, plain, toolchain, helperDecl, fDecl, partialDecl])
    (uses_resolve (by simp [partialDecl, plain]))
  bad := `Good.p
  bad_violates := by
    refine ⟨partialDecl, by simp [withDecls], rfl, claimed_withDecls, Or.inr rfl, ?_⟩
    rintro ⟨-, -, -, -, b, -, hn, -⟩
    simp [partialDecl, plain] at hn
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f._unsafe_rec
  fine_admitted := by
    rintro ⟨d, hd, hn, -, -, hnot⟩
    rw [eq_of_name wf_base hd helper_mem (by simp [hn, helperDecl, plain])] at hnot
    exact hnot base_helper

theorem rg1006_adequate : O2 rg1006 ∧ O2Run rg1006 ∧ O3 rg1006 ∧ O4 rg1006 ∧
    O5 rg1006 (.rel SameReports) := adequate w1006

theorem rg1006_noisy : ¬ rg1006.Meets w1006.support :=
  noisy_fails w1006 (List.mem_map_of_mem helper_mem)

end Witnesses

end RegulaSpecification
