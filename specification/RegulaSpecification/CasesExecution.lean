import RegulaSpecification.CasesProject

/-!
# Cases of RG3001 and RG3002
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

def mainDecl : Decl := plain `main `App .definition [`Good.f]

theorem main_mem : mainDecl ∈ base.decls := by simp [mainDecl, base, baseDecls]

theorem f_mem : fDecl ∈ base.decls := by simp [fDecl, base, baseDecls]

theorem base_root : base.ExecutableRoot `main .standardLogical .checked :=
  ⟨appTarget, by simp [base, appTarget], rfl, by simp [base, appTarget], mainDecl, main_mem, rfl,
    rfl, by simp [mainDecl, plain, appTarget]⟩

/-- The only executable root of `base` with a checked execution claim is claimed standard-logical. -/
theorem base_root_profile {r : Name} {p : Profile} (h : base.ExecutableRoot r p .checked) :
    p = .standardLogical := by
  obtain ⟨t, -, -, hm, -⟩ := h
  simp [base] at hm
  exact hm.2

/-- The only departure of `base` runs the recursion helper of `Good.f`. -/
theorem base_departs {c n : Name} (h : base.Departs c n) : c = `Good.f ∧ n = `Good.f._unsafe_rec := by
  obtain ⟨d, hd, x, hx, rfl, rfl, -⟩ := h
  simp only [base, baseDecls, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl] at hx <;> subst hx <;> exact ⟨rfl, rfl⟩

/-- A path of departures starts with a departure. -/
theorem DepartsTo.head {i : Input} {c n : Name} (h : i.DepartsTo c n) : ∃ m, i.Departs c m := by
  cases h with
  | one h => exact ⟨_, h⟩
  | more h _ => exact ⟨_, h⟩

theorem no_cycle_base (c : Name) : ¬ base.DepartsTo c c := by
  intro h
  cases h with
  | one h =>
    obtain ⟨rfl, h⟩ := base_departs h
    exact absurd h (by decide)
  | more h t =>
    obtain ⟨rfl, rfl⟩ := base_departs h
    obtain ⟨m, hm⟩ := DepartsTo.head t
    exact absurd (base_departs hm).1 (by decide)

/-! ## RG3001 -/

/-- `Good.f`, whose compiled code runs `Gone`, which is not a constant, in place of its kernel
value. -/
def replaced : Decl :=
  { plain `Good.f `Good .definition [] with compiled := [`Gone], departures := [⟨`Good.f, `Gone, false⟩] }

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

/-- The names the RG3001 witness can report: each constant, each name that compiled code runs, and
the reference of each departure. -/
def support3001 (i : Input) : List Name :=
  i.decls.map (·.name) ++ i.decls.flatMap fun d => d.compiled ++ d.departures.map (·.reference)

def w3001 : Witnessed Violates3001 where
  support := support3001
  support_complete i c h := by
    obtain ⟨r, p, e, ⟨-, -, -, -, d, hd, hn, -⟩, hx, hnr | hcyc⟩ := h
    · cases hx with
      | root => exact absurd ⟨d, hd, hn⟩ hnr
      | step d' _ hd' _ hrun =>
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨d', hd', List.mem_append_left _ hrun⟩)
    · obtain ⟨m, d', hd', x, hx', hr, -⟩ := DepartsTo.head hcyc
      exact List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨d', hd', List.mem_append_right _ (List.mem_map.mpr ⟨x, hx', hr⟩)⟩)
  refused := refused3001
  refused_wf := wf3001
  bad := `Gone
  bad_violates := by
    refine ⟨`main, .standardLogical, .checked, ⟨appTarget, by simp [refused3001, base, appTarget],
      rfl, by simp [refused3001, base, appTarget], mainDecl, by simp [refused3001, decls3001], rfl,
      rfl, by simp [mainDecl, plain, appTarget]⟩, ?_, Or.inl ?_⟩
    · exact .step replaced (.step mainDecl (.root _) (by simp [refused3001, decls3001]) rfl
        (by simp [mainDecl, plain, replaced])) (by simp [refused3001, decls3001]) rfl (by simp [replaced])
    · rintro ⟨d, hd, hn⟩
      simp only [refused3001, decls3001, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [plain, toolchain, helperDecl, replaced, mainDecl] at hn
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f
  fine_admitted := by
    rintro ⟨-, -, -, -, -, h | h⟩
    · exact h ⟨fDecl, f_mem, rfl⟩
    · exact no_cycle_base _ h

theorem rg3001_adequate : O2 rg3001 ∧ O2Run rg3001 ∧ O3 rg3001 ∧ O4 rg3001 ∧
    O5 rg3001 (.rel SameReports) := adequate w3001

theorem rg3001_noisy : ¬ rg3001.Meets w3001.support :=
  noisy_fails w3001 (show (`Good.f : Name) ∈ support3001 base from
    List.mem_append_left _ (by simp [base, baseDecls, plain]))

/-- The compiled code of `Good.f` runs `Good.g` in place of its kernel value, and the compiled
code of `Good.g` runs `Good.f` in place of its own. -/
def cycleF : Decl :=
  { plain `Good.f `Good .definition [] with
    compiled := [`Good.g], departures := [⟨`Good.f, `Good.g, false⟩] }
def cycleG : Decl :=
  { plain `Good.g `Good .definition [] with
    compiled := [`Good.f], departures := [⟨`Good.g, `Good.f, false⟩] }

/-- A claimed executable that reaches a cycle of departures violates RG3001, although each name of
the cycle resolves. -/
theorem rg3001_refuses_cycle :
    Violates3001 { base with decls := [cycleF, cycleG, mainDecl] } `Good.f :=
  ⟨`main, .standardLogical, .checked, ⟨appTarget, by simp [base, appTarget], rfl,
    by simp [base, appTarget], mainDecl, by simp, rfl, rfl, by simp [mainDecl, plain, appTarget]⟩,
    .step mainDecl (.root _) (by simp) rfl (by simp [mainDecl, plain]),
    Or.inr (.more
      ⟨cycleF, by simp, ⟨`Good.f, `Good.g, false⟩, by simp [cycleF], rfl, rfl, by decide⟩
      (.one ⟨cycleG, by simp, ⟨`Good.g, `Good.f, false⟩, by simp [cycleG], rfl, rfl, by decide⟩))⟩

/-! ## RG3002 -/

theorem t_safe_admitted : base.AdmittedProof .standardLogical `Good.t :=
  ⟨⟨tDecl, t_mem, rfl, rfl, rfl⟩, fun _ ha => by rw [base_axioms_t ha]; exact base_known_propext⟩

/-- `Good.t` proves the correspondence of the recursion helper of `Good.f`, under the profile of
`app`. -/
theorem base_corresponds : base.Corresponds .standardLogical helperDeparture :=
  ⟨⟨.corresponds `Good.f `Good.f._unsafe_rec, `Good.t⟩, by simp [base], rfl, t_safe_admitted⟩

theorem base_boundary_f : base.BoundaryAt `Good.f helperDeparture :=
  ⟨fDecl, f_mem, rfl, by simp [fDecl], rfl⟩

def w3002 : Witnessed Violates3002 where
  support i := i.decls.map (·.name)
  support_complete _ _ h := by
    obtain ⟨-, -, -, -, ⟨d, hd, hn, -⟩ | ⟨-, ⟨d, hd, hn, -⟩, -⟩⟩ := h
    · exact List.mem_map.mpr ⟨d, hd, hn⟩
    · exact List.mem_map.mpr ⟨d, hd, hn⟩
  refused := { base with proved := proofsOf goodDeliverable `Good.t }
  refused_wf := wf_congr wf_base rfl rfl rfl
  bad := `Good.f
  bad_violates := by
    refine ⟨`main, .standardLogical, base_root,
      .step mainDecl (.root _) main_mem rfl (by simp [mainDecl, plain]),
      Or.inr ⟨helperDeparture, base_boundary_f, ?_⟩⟩
    rintro ⟨q, hq, hs, -⟩
    simp only [proofsOf, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs
  admitted := base
  admitted_wf := wf_base
  fine := `Good.f
  fine_admitted := by
    rintro ⟨r, p, hr, -, ⟨d, hd, hn, -, he⟩ | ⟨x, ⟨d, hd, hn, hx, -⟩, hc⟩⟩
    · rw [eq_of_name wf_base hd f_mem (by simp [hn, fDecl, plain])] at he
      simp [Input.Unbindable, fDecl, plain] at he
    · rw [eq_of_name wf_base hd f_mem (by simp [hn, fDecl, plain])] at hx
      simp only [fDecl, List.mem_singleton] at hx
      subst hx
      rw [base_root_profile hr] at hc
      exact hc base_corresponds

theorem rg3002_adequate : O2 rg3002 ∧ O2Run rg3002 ∧ O3 rg3002 ∧ O4 rg3002 ∧
    O5 rg3002 (.rel SameReports) := adequate w3002

theorem rg3002_noisy : ¬ rg3002.Meets w3002.support :=
  noisy_fails w3002 (show (`Good.f : Name) ∈ base.decls.map (·.name) by
    simp [base, baseDecls, plain])

/-- `Good.f` made `@[extern]`. -/
def externF : Decl := { plain `Good.f `Good .definition [] with isExtern := true }

def declsExtern : List Decl :=
  [toolchain ``propext .axiom, plain `Good.t `Good .theorem [``propext], externF, helperDecl,
    plain `Good.Spec `Good .definition [], plain `Good.f_spec `Good .theorem [`Good.f, `Good.Spec],
    plain `Good.intent `Good .definition [], mainDecl]

/-- A checked executable that reaches an `@[extern]` function violates RG3002, whatever theorems
the project proves: no theorem of Lean speaks of the foreign code. -/
theorem rg3002_refuses_extern : Violates3002 { base with decls := declsExtern } `Good.f :=
  ⟨`main, .standardLogical, ⟨appTarget, by simp [base, appTarget], rfl, by simp [base, appTarget],
    mainDecl, by simp [declsExtern], rfl, rfl, by simp [mainDecl, plain, appTarget]⟩,
    .step mainDecl (.root _) (by simp [declsExtern]) rfl (by simp [mainDecl, plain]),
    Or.inl ⟨externF, by simp [declsExtern], rfl, rfl, Or.inl rfl⟩⟩

/-- `Good.fFast`, an `@[extern]` constant. -/
def externFast : Decl := { plain `Good.fFast `Good .definition [] with isExtern := true }

/-- A safe `@[csimp]` lemma `@Good.f = @Good.fFast`, which uses no axiom. -/
def csimpLemma : Decl := plain `Good.f_eq_fFast `Good .theorem []

/-- A `main` whose call site of the pure `Good.f` runs `Good.fFast`, by the `@[csimp]` lemma. -/
def csimpMain : Decl :=
  { plain `main `App .definition [`Good.f] with
    compiled := [`Good.fFast], departures := [⟨`Good.f, `Good.fFast, false⟩] }

def csimpInput : Input :=
  { base with
    decls := [plain `Good.f `Good .definition [], externFast, csimpLemma, csimpMain]
    proved := [⟨.corresponds `Good.f `Good.fFast, `Good.f_eq_fFast⟩] }

/-- A checked executable whose call site runs an `@[extern]` constant in place of a pure one, by a
`@[csimp]` lemma, violates RG3002 at the `@[extern]` constant. The safe lemma is a correspondence
of the departure, but no theorem of Lean speaks of the foreign code. -/
theorem rg3002_refuses_csimp_extern :
    csimpInput.Corresponds .standardLogical ⟨`Good.f, `Good.fFast, false⟩ ∧
      Violates3002 csimpInput `Good.fFast := by
  refine ⟨⟨⟨.corresponds `Good.f `Good.fFast, `Good.f_eq_fFast⟩, by simp [csimpInput], rfl,
    ⟨csimpLemma, by simp [csimpInput], rfl, rfl, rfl⟩, fun a ha => ?_⟩,
    `main, .standardLogical, ⟨appTarget, by simp [csimpInput, base, appTarget], rfl,
      by simp [csimpInput, base, appTarget], csimpMain, by simp [csimpInput], rfl, rfl,
      by simp [csimpMain, plain, appTarget]⟩,
    .step csimpMain (.root _) (by simp [csimpInput]) rfl (by simp [csimpMain]),
    Or.inl ⟨externFast, by simp [csimpInput], rfl, rfl, Or.inl rfl⟩⟩
  obtain ⟨hr, d, hd, hn, hk⟩ := ha
  have := reaches_closed (i := csimpInput) (fun n => n = `Good.f_eq_fFast) (by
    intro d hd hS u hu
    simp only [csimpInput, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [plain, externFast, csimpLemma, csimpMain] at hS hu)
    rfl hr
  subst this
  simp only [csimpInput, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp [plain, externFast, csimpLemma, csimpMain] at hn hk

/-- An unsafe theorem `Good.u`. -/
def unsafeLemma : Decl := { plain `Good.u `Good .theorem [] with isUnsafe := true }

/-- `base` with the correspondence of the recursion helper proved by the unsafe `Good.u` only. -/
def unsafeInput : Input :=
  { withDecls [unsafeLemma] with
    proved :=
      proofsOf goodDeliverable `Good.t ++ [⟨.corresponds `Good.f `Good.f._unsafe_rec, `Good.u⟩] }

/-- A checked executable whose boundary has a correspondence proved only by an unsafe theorem
violates RG3002: the exporter of `lake check` skips unsafe constants, so the kernel does not
replay that proof. -/
theorem rg3002_refuses_unsafe_proof : unsafeInput.WellFormed ∧ Violates3002 unsafeInput `Good.f := by
  refine ⟨wf_congr (wf_withDecls [unsafeLemma]
      (by simp [base, baseDecls, plain, toolchain, helperDecl, unsafeLemma])
      (uses_resolve (by simp [unsafeLemma, plain]))) rfl rfl rfl,
    `main, .standardLogical, ⟨appTarget, by simp [unsafeInput, withDecls, base, appTarget], rfl,
      by simp [unsafeInput, withDecls, base, appTarget], mainDecl,
      List.mem_append_left _ main_mem, rfl, rfl, by simp [mainDecl, plain, appTarget]⟩,
    .step mainDecl (.root _) (List.mem_append_left _ main_mem) rfl (by simp [mainDecl, plain]),
    Or.inr ⟨helperDeparture, ⟨fDecl, List.mem_append_left _ f_mem, rfl, by simp [fDecl], rfl⟩, ?_⟩⟩
  rintro ⟨q, hq, hs, ⟨d, hd, hn, hu, -⟩, -⟩
  simp only [unsafeInput, proofsOf, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs
  simp only [unsafeInput, withDecls, base, baseDecls, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [plain, toolchain, helperDecl, unsafeLemma] at hn hu

/-- A theorem `Good.s` that uses the project axiom `Good.ax`. -/
def axiomLemma : Decl := plain `Good.s `Good .theorem [`Good.ax]

/-- `base` with the correspondence of the recursion helper proved by `Good.s` only. -/
def unadmittedInput : Input :=
  { withDecls [ax, axiomLemma] with
    proved :=
      proofsOf goodDeliverable `Good.t ++ [⟨.corresponds `Good.f `Good.f._unsafe_rec, `Good.s⟩] }

/-- A checked executable whose boundary has a correspondence proved only by a theorem that uses an
axiom outside the profile of the claim violates RG3002. -/
theorem rg3002_refuses_unadmitted_proof :
    unadmittedInput.WellFormed ∧ Violates3002 unadmittedInput `Good.f := by
  refine ⟨wf_congr (wf_withDecls [ax, axiomLemma]
      (by simp [base, baseDecls, plain, toolchain, helperDecl, ax, axiomLemma])
      (uses_resolve (by simp [ax, axiomLemma, plain]))) rfl rfl rfl,
    `main, .standardLogical, ⟨appTarget, by simp [unadmittedInput, withDecls, base, appTarget], rfl,
      by simp [unadmittedInput, withDecls, base, appTarget], mainDecl,
      List.mem_append_left _ main_mem, rfl, rfl, by simp [mainDecl, plain, appTarget]⟩,
    .step mainDecl (.root _) (List.mem_append_left _ main_mem) rfl (by simp [mainDecl, plain]),
    Or.inr ⟨helperDeparture, ⟨fDecl, List.mem_append_left _ f_mem, rfl, by simp [fDecl], rfl⟩, ?_⟩⟩
  rintro ⟨q, hq, hs, -, hadm⟩
  simp only [unadmittedInput, proofsOf, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hs
  have hax := hadm `Good.ax
    ⟨.step axiomLemma (by simp [unadmittedInput, withDecls]) rfl (by simp [axiomLemma, plain])
      (.refl _), ax, by simp [unadmittedInput, withDecls], rfl, rfl⟩
  simp [Input.Admits, Input.Known, logicalAxioms] at hax

end Witnesses

end RegulaSpecification
