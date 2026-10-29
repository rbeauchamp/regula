import RegulaSpecification.CasesContracts

/-!
# Cases of RG2002, RG2004, RG2006 and RG2007
-/

namespace RegulaSpecification

open Lean (Name)
open LeanIntent

namespace Witnesses

def goodTarget : Target := ⟨`Good, .library, [`Good], strict, [], true⟩
def appTarget : Target := ⟨`app, .executable, [`App], strict, [], true⟩

/-- Changing only the modules of `base`, with each target module still loaded. -/
theorem wf_modules (ms : List ModuleRecord) (hg : ∃ r ∈ ms, r.name = `Good)
    (ha : ∃ r ∈ ms, r.name = `App) : ({ base with modules := ms } : Input).WellFormed := by
  refine ⟨wf_base.unique, wf_base.closed, ?_⟩
  intro t ht m hm
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> simp at hm <;> subst hm
  · exact hg
  · exact ha

/-! ## RG2002 -/

def w2002 : Witnessed Violates2002 where
  support i := i.targets.map (·.name) ++ i.manifest.map (·.target)
  support_complete _ _ h := by
    rcases h with ⟨⟨tg, htg, hn⟩, -⟩ | ⟨⟨e, he, hn⟩, -⟩ | ⟨x, hx, hn, -⟩ | ⟨x, hx, hn, -⟩
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨tg, htg, hn⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, hn⟩)
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, hn⟩)
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨x, hx, hn⟩)
  refused := { base with manifest := [⟨`Good, .claimed .choiceFree .report⟩] }
  refused_wf := wf_congr wf_base rfl rfl rfl
  bad := `app
  bad_violates := Or.inl ⟨⟨appTarget, by simp [base, appTarget], rfl⟩,
    by simp [Input.entriesFor]⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good
  fine_admitted := by
    rintro (⟨-, h⟩ | ⟨-, h⟩ | ⟨x, hx, hn, hk, -⟩ | ⟨x, hx, -, -, hd⟩)
    · exact h (by simp [Input.entriesFor, base])
    · exact h ⟨goodTarget, by simp [base, goodTarget], rfl⟩
    · simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp at hn hk
    · simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp at hd

theorem rg2002_adequate : O2 rg2002 ∧ O2Run rg2002 ∧ O3 rg2002 ∧ O4 rg2002 ∧
    O5 rg2002 (.rel SameReports) := adequate w2002

theorem rg2002_noisy : ¬ rg2002.Meets w2002.support :=
  noisy_fails w2002 (show (`Good : Name) ∈ base.targets.map (·.name) ++ base.manifest.map (·.target)
    by simp [base])

/-- A claimed executable that is not a default target violates RG2002: `lake check` would not
check its modules. -/
theorem rg2002_refuses_nondefault :
    Violates2002 { base with targets := [goodTarget, { appTarget with isDefault := false }] } `app :=
  Or.inr (Or.inr (Or.inr ⟨{ appTarget with isDefault := false }, by simp, rfl,
    ⟨.standardLogical, .checked, by simp [base]⟩, rfl⟩))

/-! ## RG2004 -/

def extraModule : ModuleRecord := ⟨`Good.Extra, [`Init], []⟩

def w2004 : Witnessed Violates2004 where
  support i := i.modules.map (·.name)
  support_complete _ _ h := by
    obtain ⟨r, hr, hn, -⟩ := h
    exact List.mem_map.mpr ⟨r, hr, hn⟩
  refused := { base with modules := base.modules ++ [extraModule] }
  refused_wf := wf_modules _ ⟨⟨`Good, [`Init], [`Lean.declRangeExt]⟩, by simp [base], rfl⟩
    ⟨⟨`App, [`Init, `Good], []⟩, by simp [base], rfl⟩
  bad := `Good.Extra
  bad_violates := ⟨extraModule, by simp, rfl, Or.inl (by
    simp [Input.Covered, Input.librariesOf, base])⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good
  fine_admitted := by
    rintro ⟨r, -, -, h | ⟨-, n, -, t, -, -, he⟩⟩
    · exact h (Or.inl (by simp [Input.librariesOf, base]))
    · simp [base] at he

theorem rg2004_adequate : O2 rg2004 ∧ O2Run rg2004 ∧ O3 rg2004 ∧ O4 rg2004 ∧
    O5 rg2004 (.rel SameReports) := adequate w2004

theorem rg2004_noisy : ¬ rg2004.Meets w2004.support :=
  noisy_fails w2004 (show (`Good : Name) ∈ base.modules.map (·.name) by simp [base])

/-! ## RG2006 -/

def laxTarget : Target := ⟨`Good, .library, [`Good], [(`relaxedAutoImplicit, "false")], [], true⟩

def w2006 (allowed : Name → Prop) (ha : allowed `autoImplicit)
    (hr : allowed `relaxedAutoImplicit) : Witnessed (Violates2006 allowed) where
  support i := i.targets.map (·.name)
  support_complete _ _ h := by
    obtain ⟨tg, htg, hn, -⟩ := h
    exact List.mem_map.mpr ⟨tg, htg, hn⟩
  refused := { base with targets := [laxTarget, appTarget] }
  refused_wf := by
    refine ⟨wf_base.unique, wf_base.closed, ?_⟩
    intro t ht m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp [laxTarget, appTarget] at hm <;> subst hm <;> simp [base]
  bad := `Good
  bad_violates := ⟨laxTarget, by simp, rfl, ⟨.choiceFree, .report, by simp [base]⟩,
    Or.inl (by simp [laxTarget])⟩
  admitted := base
  admitted_wf := wf_base
  fine := `Good
  fine_admitted := by
    rintro ⟨tg, htg, hn, -, h⟩
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at htg
    rcases htg with rfl | rfl
    · rcases h with h | h | ⟨o, ho, -, hv⟩ | ⟨o, ho, hno⟩ | h
      · simp [strict] at h
      · simp [strict] at h
      · simp only [strict, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> exact hv rfl
      · simp only [strict, List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl
        · exact hno ha
        · exact hno hr
      · simp at h
    · simp at hn

theorem rg2006_adequate (allowed : Name → Prop) (ha : allowed `autoImplicit)
    (hr : allowed `relaxedAutoImplicit) :
    O2 (rg2006 allowed) ∧ O2Run (rg2006 allowed) ∧ O3 (rg2006 allowed) ∧ O4 (rg2006 allowed) ∧
      O5 (rg2006 allowed) (.rel SameReports) := adequate (w2006 allowed ha hr)

/-- `Good` with the strict options followed by `autoImplicit` set to `true`. -/
def overrideTarget : Target :=
  { goodTarget with options := strict ++ [(`autoImplicit, "true")] }

/-- A claimed target whose options are the strict options followed by `autoImplicit` set to `true`
violates RG2006, for each allowlist: the rule refuses each value other than `false`, whatever its
position, so no order of the options turns automatic implicits on. -/
theorem rg2006_refuses_override (allowed : Name → Prop) :
    Violates2006 allowed { base with targets := [overrideTarget, appTarget] } `Good :=
  ⟨overrideTarget, by simp, rfl, ⟨.choiceFree, .report, by simp [base]⟩,
    Or.inr (Or.inr (Or.inl ⟨(`autoImplicit, "true"), by simp [overrideTarget], Or.inl rfl,
      by simp⟩))⟩

/-! ## RG2007 -/

def macroModule : ModuleRecord := ⟨`Good, [`Init], [`Lean.declRangeExt, `Lean.Elab.macroAttribute]⟩

def w2007 (declarative : Name → Prop) (hc : ClosedAllowlist declarative)
    (hd : declarative `Lean.declRangeExt) : Witnessed (Violates2007 declarative) where
  support i := i.modules.map (·.name)
  support_complete _ _ h := by
    obtain ⟨-, r, hr, hn, -⟩ := h
    exact List.mem_map.mpr ⟨r, hr, hn⟩
  refused := { base with modules := [macroModule, ⟨`App, [`Init, `Good], []⟩] }
  refused_wf := wf_modules _ ⟨macroModule, by simp, rfl⟩ ⟨⟨`App, [`Init, `Good], []⟩, by simp, rfl⟩
  bad := `Good
  bad_violates := rg2007_refuses_meta hc ⟨_, _, base_claims_good⟩ (r := macroModule) (by simp) rfl
    (x := `Lean.Elab.macroAttribute) (by simp [macroModule]) (by simp [metaExtensions])
  admitted := base
  admitted_wf := wf_base
  fine := `Good
  fine_admitted := by
    rintro ⟨-, r, hr, hn, x, hx, hnx⟩
    simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [List.mem_singleton] at hx
      subst hx
      exact hnx hd
    · simp at hn

theorem rg2007_adequate (declarative : Name → Prop) (hc : ClosedAllowlist declarative)
    (hd : declarative `Lean.declRangeExt) :
    O2 (rg2007 declarative) ∧ O2Run (rg2007 declarative) ∧ O3 (rg2007 declarative) ∧
      O4 (rg2007 declarative) ∧ O5 (rg2007 declarative) (.rel SameReports) :=
  adequate (w2007 declarative hc hd)

end Witnesses

end RegulaSpecification
