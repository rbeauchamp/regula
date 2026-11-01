/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Reader

/-!
# What the load of a finished build gives

For every response: the closed input of a run is what the proved `Regula.Load.Facts.input` gives on the environment,
the places and the modules that Lean and Lake returned, or an error because one of them failed.
-/

namespace RegulaSpecification.Effects

open Lean (Name Environment)
open System (FilePath)
open Regula.Effect
open Regula.Reader
open Regula.Shell

variable {L E : Type}

/-- `readModules` lists each module with the place Lean's search gave, or a search failed. -/
theorem readModules_spec {toolchainDir rootDir : FilePath} (names : List Name) {t : List (Event L E)}
    {b : Except String { ms : List Regula.Load.LoadedModule // ms.map (·.name) = names ∧
      ∀ m ∈ ms, m = Regula.Load.LoadedModule.ofPlace toolchainDir rootDir m.name m.olean }}
    (h : Runs (readModules toolchainDir rootDir names : Attempt L E _).run t b) :
    (∀ ms, b = .ok ms → ∀ m ∈ ms.1, (⟨.findOLean m.name, .ok m.olean⟩ : Event L E) ∈ t) ∧
      ((∃ e, b = .error e) → ∃ e ∈ t, Event.failedLoad e) ∧ ∀ e ∈ t, e.acted? = none := by
  induction names generalizing t with
  | nil =>
    rw [readModules] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun ms he => (by cases he; simp), fun ⟨e, he⟩ => (by cases he), fun e he => (by cases he)⟩
  | cons n rest ih =>
    rw [readModules] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
    obtain rfl := runs_call_iff.mp h₃
    cases r' with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₂
      refine ⟨fun _ he => (by cases he), fun _ => ⟨⟨.findOLean n, .error e⟩, by simp, ⟨e, rfl⟩⟩, fun x hx => ?_⟩
      simp only [List.append_nil, List.mem_singleton] at hx
      subst hx
      rfl
    | ok olean =>
      obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨i1, i2, i3⟩ := ih h₄
      have hact : ∀ x ∈ ([⟨.findOLean n, .ok olean⟩] : List (Event L E)) ++ t₃, x.acted? = none := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have : x = ⟨.findOLean n, .ok olean⟩ := by simpa using hx
          subst this
          rfl
        · exact i3 x hx
      cases r₃ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₅
        obtain ⟨e', he', hf⟩ := i2 ⟨why, rfl⟩
        exact ⟨fun _ he => (by cases he), fun _ => ⟨e', by simp [he'], hf⟩, by simpa using hact⟩
      | ok ms =>
        obtain ⟨ms, hn, hp⟩ := ms
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₅
        refine ⟨fun ms' he m hm => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hact⟩
        cases he
        rcases List.mem_cons.mp hm with rfl | hm
        · simp [Regula.Load.LoadedModule.ofPlace]
        · have := i1 ⟨ms, hn, hp⟩ rfl m hm
          simp [this]

/-- `factsOf` holds the environment and the places it was given. -/
theorem factsOf_spec {env : Environment} {toolchainDir rootDir : FilePath} {t : List (Event L E)}
    {b : Except String Regula.Load.Facts}
    (h : Runs (factsOf env toolchainDir rootDir : Attempt L E _).run t b) :
    (∀ f, b = .ok f → f.env = env ∧ f.toolchainDir = toolchainDir ∧ f.rootDir = rootDir ∧
      ∀ m ∈ f.modules, (⟨.findOLean m.name, .ok m.olean⟩ : Event L E) ∈ t) ∧
      ((∃ e, b = .error e) → ∃ e ∈ t, Event.failedLoad e) ∧ ∀ e ∈ t, e.acted? = none := by
  rw [factsOf] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨m1, m2, m3⟩ := readModules_spec _ h₁
  cases r with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨e', he', hf⟩ := m2 ⟨why, rfl⟩
    exact ⟨fun _ he => (by cases he), fun _ => ⟨e', by simpa using he', hf⟩, by simpa using m3⟩
  | ok ms =>
    obtain ⟨ms, hn, hp⟩ := ms
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
    refine ⟨fun f he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using m3⟩
    cases he
    refine ⟨rfl, rfl, rfl, fun m hm => ?_⟩
    have := m1 ⟨ms, hn, hp⟩ rfl m (by simpa using hm)
    simpa using this

/-- `inputOf`: what `Facts.input` gives on what Lean and Lake returned, or one of them failed. -/
theorem inputOf_spec {T t : List (Event L E)} {root : Root L} {p : Regula.Closed.Profile} {b : Except String Regula.Closed.Input}
    (hT : t.Sublist T) (h : Runs (inputOf root p : Attempt L E Regula.Closed.Input).run t b) :
    ((∃ f roots, BuildRead T root f roots ∧ b = f.input roots p) ∨
      ((∃ e ∈ T, Event.failedLoad e) ∧ ∃ why, b = .error why)) ∧ ∀ e ∈ t, e.acted? = none := by
  rw [inputOf] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  have hT₁ : t₁.Sublist T := (List.sublist_append_left _ _).trans hT
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
  obtain ⟨m1, m2⟩ := defaultModules_spec (T := T) root root.defaultTargets hT₁.subset h₁
  have mact := defaultModules_no_act h₁
  cases r with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨lib, x, hx⟩ := m2 ⟨why, rfl⟩
    exact ⟨.inr ⟨⟨_, hT₁.subset hx, ⟨x, rfl⟩⟩, why, rfl⟩, by simpa using mact⟩
  | ok modules =>
    dsimp only at h₂
    obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨u, h₅, rfl⟩ := runs_lift_iff.mp h₃
    obtain rfl := runs_call_iff.mp h₅
    obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₄
    obtain ⟨r₆, h₈, rfl⟩ := runs_attempt_iff.mp h₆
    obtain rfl := runs_call_iff.mp h₈
    cases r₆ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₇
      refine ⟨.inr ⟨⟨⟨.importForRules (modules.map (·.1)).toArray, .error e⟩,
        hT₂.subset (by simp), ⟨e, rfl⟩⟩, _, rfl⟩, fun x hx => ?_⟩
      simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl
      · exact mact x hx
      · rfl
      · rfl
    | ok env =>
      obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
      obtain ⟨f1, f2, f3⟩ := factsOf_spec h₉
      have hquiet : ∀ x ∈ t₁ ++ ([⟨.setSearchPath root.leanPath, u⟩] ++ ([⟨.importForRules (modules.map (·.1)).toArray, .ok env⟩] ++ t₇)),
          x.acted? = none := by
        intro x hx
        simp only [List.cons_append, List.nil_append, List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | rfl | hx
        · exact mact x hx
        · rfl
        · rfl
        · exact f3 x hx
      cases r₇ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₁₀
        obtain ⟨e', he', hf⟩ := f2 ⟨why, rfl⟩
        refine ⟨.inr ⟨⟨e', ?_, hf⟩, why, rfl⟩, by simpa using hquiet⟩
        refine hT₂.subset ?_
        simp [he']
      | ok f =>
        have hres : t₈ = [] := (runs_done_iff.mp h₁₀).1
        have hb : b = f.input (modules.map (·.1)) p := (runs_done_iff.mp h₁₀).2
        subst hres
        obtain ⟨he, ht, hr, hm⟩ := f1 f rfl
        refine ⟨.inl ⟨f, modules.map (·.1), ⟨modules, m1 modules rfl, rfl, ?_, ht, hr, fun m hm' => ?_⟩, hb⟩,
          by simpa using hquiet⟩
        · rw [he]
          have u' : u = () := rfl
          subst u'
          refine List.Sublist.trans ?_ hT₂
          simp only [List.cons_append, List.nil_append, List.append_nil]
          exact List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.nil_sublist _))
        · refine hT₂.subset ?_
          simp [hm m hm']

end RegulaSpecification.Effects
