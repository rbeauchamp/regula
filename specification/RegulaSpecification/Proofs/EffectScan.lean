/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.ProgramCheck.EffectScan
import RegulaSpecification.Proofs.Foundation

/-!
# What the check of effects decides

`Regula.ProgramCheck.Effects` runs `scan` and `judge` of `Regula.ProgramCheck.EffectScan` on the import closure of the executable and the two library roots,
and fails the gate's build on what `judge` refuses. `mem_scan_iff` and `judge_ok_iff` state what they decide, for
every graph, of the definitions that the check runs. `mem_own_iff` states what `graphOf` selects from the environment.
`allowed_iff` states the closed set of what may mention an effect, by the modules' names, apart from the table that `allowed` reads. `check_ok_iff` puts them together. What `Environment.find?` and the header hold, and what `Expr.getUsedConstants` lists, stays
Lean's.
-/

namespace RegulaSpecification.EffectScan

open Lean
open Regula.ProgramCheck.EffectScan

/-- A constant of the repository is one of the graph. -/
def Own (g : Graph) (n : Name) : Prop := n ∈ g.own.map (·.1)

/-- A name that marks an effect by itself, in the terms of the graph. -/
def Hit (g : Graph) (u : Name) : Prop :=
  u ∈ effectRoots ∨ (¬ Own g u ∧ g.foreign u = true)

/-- A constant of the repository mentions an effect: it mentions a name that marks one, or a constant of the repository that
mentions one. -/
inductive Effectful (g : Graph) : Name → Prop where
  /-- It mentions a name that marks an effect. -/
  | direct {n u} : Own g n → u ∈ g.mentions n → Hit g u → Effectful g n
  /-- It mentions a constant of the repository that mentions an effect. -/
  | through {n u} : Own g n → u ∈ g.mentions n → Effectful g u → Effectful g n

theorem hit_iff (g : Graph) (u : Name) : g.hit u = true ↔ Hit g u := by
  simp only [Graph.hit, Bool.or_eq_true, List.contains_iff_mem, Hit, Own, Bool.and_eq_true, Bool.not_eq_true',
    Graph.ownNames]
  have hc : (Std.HashSet.ofList (g.own.map (·.1))).contains u = false ↔ u ∉ g.own.map (·.1) := by
    rw [← Bool.not_eq_true, Std.HashSet.contains_ofList]
    simp
  rw [hc]

/-- What the fold of `callers` holds. -/
theorem mem_callersFold (g : Graph) (l : List (Name × Name)) (init : Std.HashMap Name (List Name)) (u c : Name) :
    c ∈ (l.foldl (fun m x => (g.mentions x.1).foldl (fun m v => m.insert v (x.1 :: m.getD v [])) m) init).getD u [] ↔
      (∃ x ∈ l, x.1 = c ∧ u ∈ g.mentions x.1) ∨ c ∈ init.getD u [] := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, Regula.Closed.Input.mem_mentionFold, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | ⟨h, rfl⟩ | h)
      · exact .inl (.inr h)
      · exact .inl (.inl ⟨rfl, h⟩)
      · exact .inr h
    · rintro ((⟨rfl, h⟩ | h) | h)
      · exact .inr (.inl ⟨h, rfl⟩)
      · exact .inl h
      · exact .inr (.inr h)

theorem mem_callers (g : Graph) (u c : Name) :
    c ∈ g.callers.getD u [] ↔ Own g c ∧ u ∈ g.mentions c := by
  unfold Graph.callers
  rw [mem_callersFold]
  simp only [Std.HashMap.getD_empty, List.not_mem_nil, or_false, Own, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl, hu⟩
    exact ⟨⟨x, hx, rfl⟩, hu⟩
  · rintro ⟨⟨x, hx, rfl⟩, hu⟩
    exact ⟨x, hx, rfl, hu⟩

/-- A name that the search reaches back from a seed is a constant that mentions an effect, and each such constant is reached. -/
theorem mem_found_iff (g : Graph) (n : Name) :
    (Regula.Closed.reach (g.callers.getD · [])
      ((g.callers.keys.map fun k => (g.callers.getD k []).length).sum) g.seeds).contains n = true ↔ Effectful g n := by
  rw [Regula.Closed.mem_reach g.callers.keys g.seeds ?_ (Nat.le_refl _)]
  · constructor
    · rintro ⟨s, hs, hr⟩
      simp only [Graph.seeds, List.mem_filter, List.any_eq_true] at hs
      obtain ⟨ho, u, hu, hh⟩ := hs
      have hbase : Effectful g s := .direct ho hu ((hit_iff g u).mp hh)
      induction hr with
      | refl => exact hbase
      | step _ hc ih =>
        obtain ⟨hown, hm⟩ := (mem_callers g _ _).mp hc
        exact .through hown hm ih
    · intro h
      induction h with
      | direct ho hu hh =>
        refine ⟨_, ?_, .refl⟩
        simp only [Graph.seeds, List.mem_filter, List.any_eq_true]
        exact ⟨ho, _, hu, (hit_iff g _).mpr hh⟩
      | through ho hu _ ih =>
        obtain ⟨s, hs, hr⟩ := ih
        exact ⟨s, hs, .step hr ((mem_callers g _ _).mpr ⟨ho, hu⟩)⟩
  · intro k hk
    refine Classical.byContradiction fun hno => hk ?_
    have hnot : k ∉ g.callers := by simpa [Std.HashMap.mem_keys] using hno
    simp [Std.HashMap.getD_eq_fallback hnot]

/-- `scan` gives exactly the constants of the repository that mention an effect, with their modules. -/
theorem mem_scan_iff (g : Graph) (x : Name × Name) : x ∈ scan g ↔ x ∈ g.own ∧ Effectful g x.1 := by
  simp only [scan, List.mem_filter, mem_found_iff]

/-- `judge` passes exactly when the interpreter is found and each constant found may mention an effect. -/
theorem judge_ok_iff (found : List (Name × Name)) :
    judge found = .ok () ↔
      (∃ x ∈ found, x.1 = `Regula.Effect.Prog.interpret) ∧ ∀ x ∈ found, allowed x = true := by
  unfold judge
  split
  · rename_i hc
    have hi : (found.any (·.1 == `Regula.Effect.Prog.interpret)) = false := by simpa using hc
    refine ⟨fun h => (by cases h), ?_⟩
    rintro ⟨⟨x, hx, hn⟩, -⟩
    have ht : (found.any (·.1 == `Regula.Effect.Prog.interpret)) = true :=
      List.any_eq_true.mpr ⟨x, hx, by simpa using hn⟩
    rw [hi] at ht
    cases ht
  · rename_i hc
    have hi : (found.any (·.1 == `Regula.Effect.Prog.interpret)) = true := by simpa using hc
    have hex : ∃ x ∈ found, x.1 = `Regula.Effect.Prog.interpret := by
      obtain ⟨x, hx, hb⟩ := List.any_eq_true.mp hi
      exact ⟨x, hx, by simpa using hb⟩
    cases hf : found.filter (!allowed ·) with
    | nil =>
      have hall : ∀ x ∈ found, allowed x = true := by
        intro x hx
        have := List.filter_eq_nil_iff.mp hf x hx
        simpa using this
      exact ⟨fun _ => ⟨hex, hall⟩, fun _ => rfl⟩
    | cons a l =>
      have hmem : a ∈ found.filter (!allowed ·) := by simp [hf]
      obtain ⟨h1, h2⟩ := List.mem_filter.mp hmem
      refine ⟨fun h => (by cases h), ?_⟩
      rintro ⟨-, hall⟩
      exact absurd (hall a h1) (by simpa using h2)

/-- What `graphOf` selects of the environment: each constant that a module of the repository's root states in its own data, by
that module's index in the header. -/
theorem mem_own_iff (env : Environment) (n m : Name) :
    (n, m) ∈ (graphOf env).own ↔ ∃ data, (m, data) ∈ env.header.moduleNames.zip env.header.moduleData ∧
      m.getRoot = `Regula ∧ n ∈ data.constNames := by
  simp only [graphOf, List.mem_flatMap, List.mem_filter, List.mem_map, Array.mem_toList_iff, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨m', data⟩, ⟨hz, hroot⟩, n', hn, rfl, rfl⟩
    exact ⟨data, hz, hroot, hn⟩
  · rintro ⟨data, hz, hroot, hn⟩
    exact ⟨(m, data), ⟨hz, hroot⟩, n, hn, rfl, rfl⟩

/-- What may mention an effect, by name, apart from `effectModules`: a constant of the one table, of the calls of Lake or of the executable's root, or the interpreter's in `Regula.Effect`. So a check that allowed more than this fails this theorem. -/
theorem allowed_iff (x : Name × Name) :
    allowed x = true ↔
      x.2 ∈ [`Regula.Table, `Regula.Workspace, `Regula.LintMain] ∨
        (x.2 = `Regula.Effect ∧ (`Regula.Effect.Prog.interpret).isPrefixOf x.1 = true) := by
  simp [allowed, effectModules]

/-- The decision of the check on an environment: it passes exactly when the interpreter mentions an effect and each constant of
`own` that mentions one lies where `allowed_iff` says. -/
theorem check_ok_iff (env : Environment) :
    judge (scan (graphOf env)) = .ok () ↔
      (∃ m, (`Regula.Effect.Prog.interpret, m) ∈ (graphOf env).own ∧
        Effectful (graphOf env) `Regula.Effect.Prog.interpret) ∧
      ∀ x ∈ (graphOf env).own, Effectful (graphOf env) x.1 →
        x.2 ∈ [`Regula.Table, `Regula.Workspace, `Regula.LintMain] ∨
          (x.2 = `Regula.Effect ∧ (`Regula.Effect.Prog.interpret).isPrefixOf x.1 = true) := by
  simp only [← allowed_iff]
  rw [judge_ok_iff]
  constructor
  · rintro ⟨⟨x, hx, hn⟩, hall⟩
    obtain ⟨h1, h2⟩ := (mem_scan_iff _ _).mp hx
    obtain ⟨n, m⟩ := x
    obtain rfl : n = _ := hn
    exact ⟨⟨m, h1, h2⟩, fun y hy he => hall y ((mem_scan_iff _ _).mpr ⟨hy, he⟩)⟩
  · rintro ⟨⟨m, h1, h2⟩, hall⟩
    exact ⟨⟨(_, m), (mem_scan_iff _ _).mpr ⟨h1, h2⟩, rfl⟩, fun y hy => by
      obtain ⟨a, b⟩ := (mem_scan_iff _ _).mp hy
      exact hall y a b⟩

end RegulaSpecification.EffectScan
