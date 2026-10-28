import RegulaSpecification.CasesFoundation

/-!
# Cases of RG1007 to RG1009
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

def baseContract : Contract := ⟨`Good.f_spec, `Good.f, 0, .decides, [`Good.Spec], []⟩

def specDecl : Decl := plain `Good.f_spec `Good .theorem [`Good.f, `Good.Spec]

theorem spec_mem : specDecl ∈ base.decls := by simp [specDecl, base, baseDecls]

theorem base_claimed_spec : base.ClaimedName `Good.f_spec :=
  ⟨specDecl, spec_mem, rfl, _, _, base_claims_good⟩

/-- From `Good.Spec`, only `Good.Spec` is reached in `base`. -/
theorem base_reaches_Spec {e : Name} (h : base.Reaches `Good.Spec e) : e = `Good.Spec := by
  refine reaches_closed (i := base) (fun n => n = `Good.Spec) ?_ rfl h
  intro d hd hS u hu
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl] at hS hu ⊢

theorem base_safe_f : base.SafeComputable `Good.f :=
  ⟨plain `Good.f `Good .definition [], by simp [base, baseDecls], rfl, rfl, rfl, rfl⟩

/-! ## RG1007 -/

def w1007 : Witnessed Violates1007 where
  support i := i.contracts.map (·.theorem_)
  support_complete _ _ h := by
    obtain ⟨k, hk, hn, -⟩ := h
    exact List.mem_map.mpr ⟨k, hk, hn⟩
  refused := { base with contracts := [{ baseContract with fixedArgs := 1 }] }
  refused_wf := wf_congr wf_base rfl rfl rfl
  bad := `Good.f_spec
  bad_violates := ⟨{ baseContract with fixedArgs := 1 }, by simp, rfl, base_claimed_spec,
    Or.inl (by simp)⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f_spec
  fine_admitted := by
    rintro ⟨k, hk, -, -, h⟩
    simp only [base, List.mem_singleton] at hk
    subst hk
    rcases h with h | h | ⟨-, s, hs, hr⟩
    · exact h rfl
    · exact h base_safe_f
    · simp only [List.mem_singleton] at hs
      subst hs
      exact absurd (base_reaches_Spec hr) (by simp)

theorem rg1007_adequate : O2 rg1007 ∧ O2Run rg1007 ∧ O3 rg1007 ∧ O4 rg1007 ∧
    O5 rg1007 (.rel SameReports) := adequate w1007

theorem rg1007_noisy : ¬ rg1007.Meets w1007.support :=
  noisy_fails w1007 (show (`Good.f_spec : Name) ∈ base.contracts.map (·.theorem_) by simp [base])

/-! ## RG1008 -/

def w1008 : Witnessed Violates1008 where
  support i := i.decisions
  support_complete _ _ h := h.1
  refused := { base with decisions := [`Good.f, `Good.Spec] }
  refused_wf := wf_congr wf_base rfl rfl rfl
  bad := `Good.Spec
  bad_violates := by
    refine ⟨by simp, ⟨plain `Good.Spec `Good .definition [], by simp [base, baseDecls], rfl, _, _,
      base_claims_good⟩, by simp [base], ?_⟩
    rintro ⟨k, hk, hi, -⟩
    simp only [base, List.mem_singleton] at hk
    subst hk
    simp at hi
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f
  fine_admitted := by
    rintro ⟨-, -, -, h⟩
    exact h ⟨baseContract, by simp [base, baseContract], rfl, by simp [Contract.IsDecision,
      baseContract], base_claimed_spec⟩

theorem rg1008_adequate : O2 rg1008 ∧ O2Run rg1008 ∧ O3 rg1008 ∧ O4 rg1008 ∧
    O5 rg1008 (.rel SameReports) := adequate w1008

theorem rg1008_noisy : ¬ rg1008.Meets w1008.support :=
  noisy_fails w1008 (show (`Good.f : Name) ∈ base.decisions by simp [base])

/-! ## RG1009 -/

def shared : List Decl :=
  [{ plain `Good.test `Good .definition [] with isBoolTest := true },
    plain `Good.Spec2 `Good .definition [`Good.test], plain `Good.g `Good .definition [`Good.test],
    plain `Good.g_spec `Good .theorem [`Good.g, `Good.Spec2]]

def sharedContract : Contract := ⟨`Good.g_spec, `Good.g, 0, .decides, [`Good.Spec2], []⟩

def w1009 : Witnessed Violates1009 where
  support i := i.contracts.map (·.theorem_)
  support_complete _ _ h := by
    obtain ⟨k, hk, hn, -⟩ := h
    exact List.mem_map.mpr ⟨k, hk, hn⟩
  refused := { withDecls shared with contracts := [sharedContract] }
  refused_wf := wf_congr (wf_withDecls shared
    (by simp [base, baseDecls, plain, toolchain, helperDecl, shared])
    (uses_resolve (by simp [shared, plain, base, baseDecls, toolchain, helperDecl]))) rfl rfl rfl
  bad := `Good.g_spec
  bad_violates := by
    refine ⟨sharedContract, by simp, rfl,
      ⟨plain `Good.g_spec `Good .theorem [`Good.g, `Good.Spec2], by simp [withDecls, shared], rfl,
        _, _, base_claims_good⟩, by simp [Contract.IsDecision, sharedContract], `Good.test,
      ⟨{ plain `Good.test `Good .definition [] with isBoolTest := true },
        by simp [withDecls, shared], rfl, rfl, rfl⟩,
      ⟨`Good.Spec2, by simp [sharedContract], ?_⟩, Or.inl ?_⟩
    · exact .step (plain `Good.Spec2 `Good .definition [`Good.test])
        (by simp [withDecls, shared]) rfl (by simp [plain]) (.refl _)
    · exact .step (plain `Good.g `Good .definition [`Good.test])
        (by simp [withDecls, shared]) rfl (by simp [plain]) (.refl _)
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f_spec
  fine_admitted := by
    rintro ⟨k, hk, -, -, -, t, ⟨d, hd, hn, hb, -⟩, ⟨s, hs, hr⟩, -⟩
    simp only [base, List.mem_singleton] at hk
    subst hk
    simp only [List.mem_singleton] at hs
    subst hs
    rw [base_reaches_Spec hr] at hn
    have : d = plain `Good.Spec `Good .definition [] :=
      eq_of_name wf_base hd (by simp [base, baseDecls]) (by simp [hn, plain])
    subst this
    simp [plain] at hb

theorem rg1009_adequate : O2 rg1009 ∧ O2Run rg1009 ∧ O3 rg1009 ∧ O4 rg1009 ∧
    O5 rg1009 (.rel SameReports) := adequate w1009

theorem rg1009_noisy : ¬ rg1009.Meets w1009.support :=
  noisy_fails w1009 (show (`Good.f_spec : Name) ∈ base.contracts.map (·.theorem_) by simp [base])

end Witnesses

end RegulaSpecification
