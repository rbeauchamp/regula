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

/-- `readModules` lists each module with the place Lean's search gave on the search path of `root`, or a search failed. -/
theorem readModules_spec {root : Root L} {toolchainDir rootDir : FilePath} (names : List Name) {t : List (Event L E)}
    {b : Except String { ms : List Regula.Load.LoadedModule // ms.map (·.name) = names ∧
      ∀ m ∈ ms, m = Regula.Load.LoadedModule.ofPlace toolchainDir rootDir m.name m.olean }}
    (h : Runs (readModules root.leanPath toolchainDir rootDir names : Attempt L E _).run t b) :
    (∀ ms, b = .ok ms → (∀ m ∈ ms.1, (⟨.findOLean root.leanPath m.name, .ok m.olean⟩ : Event L E) ∈ t) ∧ Clean t) ∧
      ((∃ e, b = .error e) → ∃ m ∈ names, ∃ e, (⟨.findOLean root.leanPath m, .error e⟩ : Event L E) ∈ t) ∧ InputPreparation root t := by
  induction names generalizing t with
  | nil =>
    rw [readModules] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    exact ⟨fun ms he => (by cases he; exact ⟨by simp, clean_nil⟩), fun ⟨e, he⟩ => (by cases he), fun e he => (by cases he)⟩
  | cons n rest ih =>
    rw [readModules] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
    obtain rfl := runs_call_iff.mp h₃
    have hone {r} : InputPreparation root ([⟨.findOLean root.leanPath n, r⟩] : List (Event L E)) := by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact .inr rfl
    cases r' with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨fun _ he => (by cases he), fun _ => ⟨n, List.mem_cons_self .., e, by simp⟩, by simpa using hone⟩
    | ok olean =>
      obtain ⟨t₃, t₄, r₃, rfl, h₄, h₅⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨i1, i2, i3⟩ := ih h₄
      have hprep : InputPreparation root (([⟨.findOLean root.leanPath n, .ok olean⟩] : List (Event L E)) ++ t₃) := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hone x hx
        · exact i3 x hx
      cases r₃ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₅
        obtain ⟨m, hm, e', he'⟩ := i2 ⟨why, rfl⟩
        exact ⟨fun _ he => (by cases he), fun _ => ⟨m, List.mem_cons_of_mem _ hm, e', by simp [he']⟩, by simpa using hprep⟩
      | ok ms =>
        obtain ⟨ms, hn, hp⟩ := ms
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₅
        refine ⟨fun ms' he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using hprep⟩
        cases he
        obtain ⟨g1, g2⟩ := i1 ⟨ms, hn, hp⟩ rfl
        refine ⟨fun m hm => ?_, by simpa using (clean_one (by rintro ⟨y, hy⟩; cases hy)).append g2⟩
        rcases List.mem_cons.mp hm with rfl | hm
        · simp [Regula.Load.LoadedModule.ofPlace]
        · simp [g1 m hm]

/-- `factsOf` holds the environment and the places it was given. -/
theorem factsOf_spec {env : Environment} {root : Root L} {toolchainDir rootDir : FilePath} {t : List (Event L E)}
    {b : Except String Regula.Load.Facts}
    (h : Runs (factsOf env root.leanPath toolchainDir rootDir : Attempt L E _).run t b) :
    (∀ f, b = .ok f → f.env = env ∧ f.toolchainDir = toolchainDir ∧ f.rootDir = rootDir ∧
      (∀ m ∈ f.modules, (⟨.findOLean root.leanPath m.name, .ok m.olean⟩ : Event L E) ∈ t) ∧ Clean t) ∧
      ((∃ e, b = .error e) → ∃ m ∈ env.header.moduleNames, ∃ e, (⟨.findOLean root.leanPath m, .error e⟩ : Event L E) ∈ t) ∧
      InputPreparation root t := by
  rw [factsOf] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨m1, m2, m3⟩ := readModules_spec _ h₁
  cases r with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨m, hm, e', he'⟩ := m2 ⟨why, rfl⟩
    exact ⟨fun _ he => (by cases he), fun _ => ⟨m, Array.mem_toList_iff.mp hm, e', by simpa using he'⟩, by simpa using m3⟩
  | ok ms =>
    obtain ⟨ms, hn, hp⟩ := ms
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₂
    refine ⟨fun f he => ?_, fun ⟨e, he⟩ => (by cases he), by simpa using m3⟩
    cases he
    obtain ⟨g1, g2⟩ := m1 ⟨ms, hn, hp⟩ rfl
    exact ⟨rfl, rfl, rfl, fun m hm => by simpa using g1 m (by simpa using hm), by simpa using g2⟩

/-- `inputOf`: what `Facts.input` gives on what Lean and Lake returned, with no failed answer, or one of them failed. Each lookup and import
names the search path of `root`. -/
theorem inputOf_spec {T t : List (Event L E)} {root : Root L} {p : Regula.Closed.Profile} {b : Except String Regula.Closed.Input}
    (hT : t.Sublist T) (h : Runs (inputOf root p : Attempt L E Regula.Closed.Input).run t b) :
    ((∃ f roots, BuildRead T root f roots ∧ b = f.input roots p ∧ Clean t) ∨
      (BuildFailed T root ∧ ∃ why, b = .error why)) ∧ InputPreparation root t := by
  rw [inputOf] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  have hT₁ : t₁.Sublist T := (List.sublist_append_left _ _).trans hT
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
  obtain ⟨m1, m2, m3⟩ := defaultModules_spec (T := T) root root.defaultTargets hT₁.subset h₁
  cases r with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨tg, lib, x, hg, hl, hx⟩ := m2 ⟨why, rfl⟩
    exact ⟨.inr ⟨.library hg hl (hT₁.subset hx), why, rfl⟩, by simpa using InputPreparation.prepend (t := []) m3 (fun e he => by cases he)⟩
  | ok modules =>
    obtain ⟨hmods, hcl⟩ := m1 modules rfl
    dsimp only at h₂
    obtain ⟨t₅, t₆, r₅, rfl, h₆, h₇⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨r₆, h₈, rfl⟩ := runs_attempt_iff.mp h₆
    obtain rfl := runs_call_iff.mp h₈
    have himport {r} : InputPreparation root ([⟨.importForRules root.leanPath (modules.map (·.1)).toArray, r⟩] : List (Event L E)) := by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact .inr rfl
    cases r₆ with
    | error e =>
      obtain ⟨rfl, rfl⟩ := h₇
      exact ⟨.inr ⟨.import hmods (hT₂.subset (by simp) :
        (⟨.importForRules root.leanPath (modules.map (·.1)).toArray, .error e⟩ : Event L E) ∈ T), _, rfl⟩,
        by simpa using InputPreparation.prepend m3 himport⟩
    | ok env =>
      obtain ⟨t₇, t₈, r₇, rfl, h₉, h₁₀⟩ := runs_attempt_bind_iff.mp h₇
      obtain ⟨f1, f2, f3⟩ := factsOf_spec h₉
      have hprep : InputPreparation root (t₁ ++ ([⟨.importForRules root.leanPath (modules.map (·.1)).toArray, .ok env⟩] ++ t₇)) := by
        refine InputPreparation.prepend m3 fun x hx => ?_
        rcases List.mem_append.mp hx with hx | hx
        · exact himport x hx
        · exact f3 x hx
      cases r₇ with
      | error why =>
        obtain ⟨rfl, rfl⟩ := h₁₀
        obtain ⟨m, hm, e', he'⟩ := f2 ⟨why, rfl⟩
        have hf : (⟨.findOLean root.leanPath m, .error e'⟩ : Event L E) ∈ T := hT₂.subset (by simp [he'])
        exact ⟨.inr ⟨.search hmods (hT₂.subset (by simp) :
          (⟨.importForRules root.leanPath (modules.map (·.1)).toArray, .ok env⟩ : Event L E) ∈ T) hm hf, why, rfl⟩,
          by simpa using hprep⟩
      | ok f =>
        have hres : t₈ = [] := (runs_done_iff.mp h₁₀).1
        have hb : b = f.input (modules.map (·.1)) p := (runs_done_iff.mp h₁₀).2
        subst hres
        obtain ⟨he, ht, hr, hm, hcl₇⟩ := f1 f rfl
        have hcl₆ : Clean ([⟨.importForRules root.leanPath (modules.map (·.1)).toArray, .ok env⟩] : List (Event L E)) :=
          clean_one (by rintro ⟨y, hy⟩; cases hy)
        refine ⟨.inl ⟨f, modules.map (·.1), ⟨modules, hmods, rfl, ?_, ht, hr, fun m hm' => ?_⟩, hb,
          by simpa [List.append_assoc] using hcl.append (hcl₆.append hcl₇)⟩, by simpa using hprep⟩
        · rw [he]
          exact hT₂.subset (by simp)
        · refine hT₂.subset ?_
          simp [hm m hm']

end RegulaSpecification.Effects
