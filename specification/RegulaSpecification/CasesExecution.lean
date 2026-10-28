import RegulaSpecification.CasesProject

/-!
# Cases of RG3001, RG3002 and RG6001, and the obligations of the verdict
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

def mainDecl : Decl := plain `main `App .definition [`Good.f]

theorem main_mem : mainDecl ∈ base.decls := by simp [mainDecl, base, baseDecls]

theorem base_root : base.ExecutableRoot `main .checked :=
  ⟨appTarget, by simp [base, appTarget], rfl, ⟨.standardLogical, by simp [base, appTarget]⟩,
    mainDecl, main_mem, rfl, rfl, by simp [mainDecl, plain, appTarget]⟩

theorem base_no_main_helper : ¬ base.HasHelper `main := by
  rintro ⟨h, hh, hn, -⟩
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl] at hn

theorem base_has_helper : base.HasHelper `Good.f := ⟨helperDecl, helper_mem, rfl, base_helper⟩

theorem base_executes_f : base.Executes `main `Good.f :=
  .step mainDecl (.root _) main_mem rfl (Or.inr (Or.inr ⟨rfl, base_no_main_helper, by simp [mainDecl,
    plain]⟩))

/-! ## RG3001 -/

def replaced : Decl := { plain `Good.f `Good .definition [] with implementedBy := some `Gone }

def decls3001 : List Decl :=
  [toolchain ``propext .axiom, plain `Good.t `Good .theorem [``propext], replaced, helperDecl,
    plain `Good.Spec `Good .definition [], plain `Good.f_spec `Good .theorem [`Good.f, `Good.Spec],
    plain `Good.intent `Good .definition [], mainDecl]

def refused3001 : Input := { base with decls := decls3001 }

theorem wf3001 : refused3001.WellFormed := by
  refine ⟨by decide, ?_, wf_base.loaded⟩
  intro d hd
  simp only [refused3001, decls3001, List.mem_cons, List.not_mem_nil, or_false] at hd
  suffices h : ∀ u ∈ d.uses, u ∈ decls3001.map (·.name) by
    intro u hu
    obtain ⟨d', hd', hn⟩ := List.mem_map.mp (h u hu)
    exact ⟨d', hd', hn⟩
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [decls3001, plain, toolchain, helperDecl, replaced, mainDecl]

def w3001 : Witnessed Violates3001 where
  support i := i.decls.flatMap fun d => d.uses ++ d.implementedBy.toList ++ [Name.str d.name "_unsafe_rec"]
  support_complete i c h := by
    obtain ⟨r, e, ⟨-, -, -, -, d, hd, hn, -⟩, hx, hnr⟩ := h
    cases hx with
    | root => exact absurd ⟨d, hd, hn⟩ hnr
    | step d' _ hd' hn' hrun =>
      refine List.mem_flatMap.mpr ⟨d', hd', ?_⟩
      rcases hrun with h | ⟨-, -, rfl⟩ | ⟨-, -, h⟩
      · simp [h]
      · simp
      · simp [h]
  refused := refused3001
  refused_wf := wf3001
  bad := `Gone
  bad_violates := by
    refine ⟨`main, .checked, ⟨appTarget, by simp [refused3001, base, appTarget], rfl,
      ⟨.standardLogical, by simp [refused3001, base, appTarget]⟩, mainDecl,
      by simp [refused3001, decls3001], rfl, rfl, by simp [mainDecl, plain, appTarget]⟩, ?_, ?_⟩
    · refine .step replaced (.step mainDecl (.root _) (by simp [refused3001, decls3001]) rfl
        (Or.inr (Or.inr ⟨rfl, ?_, by simp [mainDecl, plain, replaced]⟩)))
        (by simp [refused3001, decls3001]) rfl (Or.inl rfl)
      rintro ⟨h, hh, hn, -⟩
      simp only [refused3001, decls3001, List.mem_cons, List.not_mem_nil, or_false] at hh
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [plain, toolchain, helperDecl, replaced, mainDecl] at hn
    · rintro ⟨d, hd, hn⟩
      simp only [refused3001, decls3001, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [plain, toolchain, helperDecl, replaced, mainDecl] at hn
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f
  fine_admitted := by
    rintro ⟨-, -, -, -, h⟩
    exact h ⟨plain `Good.f `Good .definition [], by simp [base, baseDecls], rfl⟩

theorem rg3001_adequate : O2 rg3001 ∧ O2Run rg3001 ∧ O3 rg3001 ∧ O4 rg3001 ∧
    O5 rg3001 (.rel SameReports) := adequate w3001

theorem rg3001_noisy : ¬ rg3001.Meets w3001.support :=
  noisy_fails w3001 (show (`Good.f : Name) ∈ base.decls.flatMap (fun d =>
    d.uses ++ d.implementedBy.toList ++ [Name.str d.name "_unsafe_rec"]) from
    List.mem_flatMap.mpr ⟨mainDecl, main_mem, by simp [mainDecl, plain]⟩)

/-! ## RG3002 -/

def unproved : List Goal :=
  [.obligation .o1 `Good.intent, .obligation .o2 `Good.intent, .obligation .o3 `Good.intent,
    .obligation .o4 `Good.intent, .obligation .o5 `Good.intent, .fulfils `Good.f `Good.intent]

def w3002 : Witnessed Violates3002 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨-, -, -, ⟨d, hd, hn, -⟩, -⟩ := h
    exact List.mem_map.mpr ⟨d, hd, hn⟩
  refused := { base with proved := unproved }
  refused_wf := wf_congr wf_base rfl rfl rfl
  bad := `Good.f
  bad_violates := ⟨`main, base_root,
    .step mainDecl (.root _) main_mem rfl
      (Or.inr (Or.inr ⟨rfl, base_no_main_helper, by simp [mainDecl, plain]⟩)),
    ⟨plain `Good.f `Good .definition [], by simp [base, baseDecls], rfl, rfl,
      Or.inr (Or.inl base_has_helper)⟩, Or.inl (by simp [unproved])⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f
  fine_admitted := by
    rintro ⟨-, -, -, -, h | ⟨d, hd, hn, -, he⟩⟩
    · exact h (by simp [base])
    · simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [plain, toolchain, helperDecl, Input.Unbindable] at hn he

theorem rg3002_adequate : O2 rg3002 ∧ O2Run rg3002 ∧ O3 rg3002 ∧ O4 rg3002 ∧
    O5 rg3002 (.rel SameReports) := adequate w3002

theorem rg3002_noisy : ¬ rg3002.Meets w3002.support :=
  noisy_fails w3002 (show (`Good.f : Name) ∈ base.decls.map (·.name) by
    simp [base, baseDecls, plain, toolchain, helperDecl])

/-- `Good.f` made `@[extern]`, with its correspondence still proved. -/
def externF : Decl := { plain `Good.f `Good .definition [] with isExtern := true }

def declsExtern : List Decl :=
  [toolchain ``propext .axiom, plain `Good.t `Good .theorem [``propext], externF, helperDecl,
    plain `Good.Spec `Good .definition [], plain `Good.f_spec `Good .theorem [`Good.f, `Good.Spec],
    plain `Good.intent `Good .definition [], mainDecl]

/-- A checked executable that reaches an `@[extern]` function violates RG3002, although a theorem
states its correspondence: no theorem of Lean speaks of the foreign code. -/
theorem rg3002_refuses_extern : Violates3002 { base with decls := declsExtern } `Good.f := by
  have noHelper : ¬ ({ base with decls := declsExtern } : Input).HasHelper `main := by
    rintro ⟨h, hh, hn, -⟩
    simp only [declsExtern, List.mem_cons, List.not_mem_nil, or_false] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [plain, toolchain, helperDecl, externF, mainDecl] at hn
  refine ⟨`main, ⟨appTarget, by simp [base, appTarget], rfl,
    ⟨.standardLogical, by simp [base, appTarget]⟩, mainDecl, by simp [declsExtern], rfl, rfl,
    by simp [mainDecl, plain, appTarget]⟩, ?_, ⟨externF, by simp [declsExtern], rfl, rfl,
    Or.inr (Or.inr (Or.inl rfl))⟩, Or.inr ⟨externF, by simp [declsExtern], rfl, rfl, Or.inl rfl⟩⟩
  exact .step mainDecl (.root _) (by simp [declsExtern]) rfl
    (Or.inr (Or.inr ⟨rfl, noHelper, by simp [mainDecl, plain]⟩))

/-! ## RG6001 -/

/-- The parts of a deliverable that a finding can name. -/
def partsOf (i : Input) (f : Name) : List (Name × IntentPart) :=
  [(f, .record), (f, .obligation .o1), (f, .obligation .o2), (f, .obligation .o3),
    (f, .obligation .o4), (f, .obligation .o5), (f, .dependsOnImplementation), (f, .fulfilment)] ++
    i.confirmed.map fun q => (f, .consequence q.2)

def withoutFulfilment : List Goal :=
  [.obligation .o1 `Good.intent, .obligation .o2 `Good.intent, .obligation .o3 `Good.intent,
    .obligation .o4 `Good.intent, .obligation .o5 `Good.intent, .corresponds `Good.f]

def w6001 : Witnessed Violates6001 where
  support i := i.deliverables.flatMap fun p => partsOf i p.1
  support_complete i s h := by
    obtain ⟨record, hmem, hf⟩ := h
    refine List.mem_flatMap.mpr ⟨(s.1, record), hmem, ?_⟩
    obtain ⟨f, part⟩ := s
    cases part with
    | obligation k => cases k <;> simp [partsOf]
    | consequence c => exact List.mem_append_right _ (List.mem_map.mpr ⟨(record, c), hf.1, rfl⟩)
    | _ => simp [partsOf]
  refused := { base with proved := withoutFulfilment }
  refused_wf := wf_congr wf_base rfl rfl rfl
  bad := (`Good.f, .fulfilment)
  bad_violates := ⟨`Good.intent, by simp [base], by simp [IntentPart.Fails, withoutFulfilment]⟩
  admitted := base
  admitted_wf := wf_base
  fine := (`Good.f, .fulfilment)
  fine_admitted := by
    rintro ⟨r, hr, h⟩
    simp only [base, List.mem_singleton, Prod.mk.injEq, true_and] at hr
    subst hr
    exact h (by simp [base])

theorem rg6001_adequate : O2 rg6001 ∧ O2Run rg6001 ∧ O3 rg6001 ∧ O4 rg6001 ∧
    O5 rg6001 (.rel SameReports) := adequate w6001

theorem rg6001_noisy : ¬ rg6001.Meets w6001.support :=
  noisy_fails w6001 (show ((`Good.f : Name), IntentPart.fulfilment) ∈
    base.deliverables.flatMap (fun p => partsOf base p.1) from
    List.mem_flatMap.mpr ⟨(`Good.f, `Good.intent), by simp [base], by simp [partsOf]⟩)

end Witnesses

end RegulaSpecification
