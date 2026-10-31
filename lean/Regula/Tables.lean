/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Input
public import Regula.Reach

/-!
# The tables of the closed input

A value of `Tables i` holds what the rules look up of the input `i`, with the proofs of what each
table holds. So a table of another input cannot reach a rule, and no theorem about a rule has a
hypothesis about its table. `Input.tables` constructs the one that a run computes, and the proofs
are here because the proof fields of that value need them.

The tables compute the axiom set of a constant from the input itself: the constants that each
constant mentions and the kind of each (`Tables.axiomSet`). No field holds a set, so no set can be
missing, and `Tables.mem_axiomSet` states what it holds.
-/

public section

namespace Regula.Closed

open Lean (Name)

namespace Input

variable (i : Input)

/-- `e` is `c`, or a constant that `c` reaches through the constants each mentions. -/
inductive Reaches : Name → Name → Prop
  /-- A constant reaches itself. -/
  | refl (c : Name) : Reaches c c
  /-- A constant reaches what a constant that it mentions reaches. -/
  | step {c u e : Name} (d : Decl) : d ∈ i.decls → d.name = c → u ∈ d.uses → Reaches u e →
      Reaches c e

/-- `a` is an axiom of the input that `c` reaches. -/
def AxiomOf (c a : Name) : Prop :=
  i.Reaches c a ∧ ∃ d ∈ i.decls, d.name = a ∧ d.kind = .axiom

end Input

/-- What the rules look up of the input `i`, computed once, with what each table holds. -/
structure Tables (i : Input) where
  /-- The constants by name. -/
  index : Std.HashMap Name Decl
  /-- The index holds exactly the constants of the input, each under its name. -/
  mem_index : ∀ n d, index[n]? = some d ↔ d ∈ i.decls ∧ d.name = n
  /-- The constants of claimed modules. -/
  claimed : List Decl
  /-- These are exactly the constants of the input whose module is claimed. -/
  mem_claimed : ∀ d, d ∈ claimed ↔ d ∈ i.decls ∧ d.module ∈ i.modules
  /-- Each axiom of the input, with the constants that reach it through the constants each mentions
  (`axiomSet`). -/
  axiomReach : List (Name × Std.HashSet Name)
  /-- The sets hold exactly the axioms that each constant reaches. -/
  mem_axiomReach : ∀ c a, (∃ s, (a, s) ∈ axiomReach ∧ s.contains c = true) ↔ i.AxiomOf c a

namespace Input

variable (i : Input)

/-- What folding the constants of `l` into a table holds. -/
theorem mem_indexFold (l : List Decl) (hu : (l.map (·.name)).Nodup)
    (init : Std.HashMap Name Decl) (n : Name) (d : Decl) :
    (l.foldl (fun m d => m.insert d.name d) init)[n]? = some d ↔
      (d ∈ l ∧ d.name = n) ∨ (n ∉ l.map (·.name) ∧ init[n]? = some d) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons] at hu
    simp only [List.foldl_cons, ih hu.2, Std.HashMap.getElem?_insert, List.mem_cons, List.map_cons,
      not_or]
    by_cases han : a.name = n
    · subst han
      have hnot : a.name ∈ l.map (·.name) → False := hu.1
      constructor
      · rintro (⟨hd, hn⟩ | ⟨-, h⟩)
        · exact .inl ⟨.inr hd, hn⟩
        · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact .inl ⟨.inl rfl, rfl⟩
      · rintro (⟨rfl | hd, hn⟩ | ⟨h, -⟩)
        · exact .inr ⟨hnot, by simp⟩
        · exact .inl ⟨hd, hn⟩
        · exact absurd rfl h.1
    · have hb : (a.name == n) = false := by simpa using han
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (⟨hd, hn⟩ | ⟨h1, h2⟩)
        · exact .inl ⟨.inr hd, hn⟩
        · exact .inr ⟨⟨fun h => han h.symm, h1⟩, h2⟩
      · rintro (⟨rfl | hd, hn⟩ | ⟨h1, h2⟩)
        · exact absurd hn han
        · exact .inl ⟨hd, hn⟩
        · exact .inr ⟨h1.2, h2⟩

/-- The constants of the input by name. -/
def index : Std.HashMap Name Decl :=
  i.decls.foldl (fun m d => m.insert d.name d) {}

/-- The index holds exactly the constants of the input, each under its name: the names are unique.
-/
theorem index_eq_some (n : Name) (d : Decl) : i.index[n]? = some d ↔ d ∈ i.decls ∧ d.name = n := by
  rw [index, mem_indexFold _ i.unique]
  simp

/-- The constants of claimed modules. -/
def claimedDecls : List Decl :=
  let claimed := setOf i.modules
  i.decls.filter (claimed.contains ·.module)

/-- These are exactly the constants of the input whose module is claimed. -/
theorem mem_claimedDecls (d : Decl) : d ∈ i.claimedDecls ↔ d ∈ i.decls ∧ d.module ∈ i.modules := by
  simp only [claimedDecls, List.mem_filter, mem_setOf]

/-- The constants that mention each constant. -/
def mentionedBy : Std.HashMap Name (List Name) :=
  i.decls.foldl (init := {}) fun m d =>
    d.uses.foldl (init := m) fun m u => m.insert u (d.name :: m.getD u [])

/-- What folding the mentions of one constant into the table holds. -/
theorem mem_mentionFold (name : Name) (uses : List Name) (init : Std.HashMap Name (List Name))
    (u c : Name) :
    c ∈ (uses.foldl (fun m v => m.insert v (name :: m.getD v [])) init).getD u [] ↔
      (u ∈ uses ∧ c = name) ∨ c ∈ init.getD u [] := by
  induction uses generalizing init with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons, ih, Std.HashMap.getD_insert, List.mem_cons]
    by_cases hv : v = u
    · subst hv
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons, true_or, true_and]
      by_cases hc : c = name <;> simp [hc]
    · have hb : (v == u) = false := by simpa using hv
      have hne : u ≠ v := fun h => hv h.symm
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      simp [hne]

/-- What folding the mentions of the constants of `l` into the table holds. -/
theorem mem_mentionedFold (l : List Decl) (init : Std.HashMap Name (List Name)) (u c : Name) :
    c ∈ (l.foldl (fun m d => d.uses.foldl (fun m v => m.insert v (d.name :: m.getD v [])) m)
        init).getD u [] ↔ (∃ d ∈ l, d.name = c ∧ u ∈ d.uses) ∨ c ∈ init.getD u [] := by
  induction l generalizing init with
  | nil => simp
  | cons d ds ih =>
    simp only [List.foldl_cons, ih, mem_mentionFold, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro (h | ⟨hu, rfl⟩ | h)
      · exact .inl (.inr h)
      · exact .inl (.inl ⟨rfl, hu⟩)
      · exact .inr h
    · rintro ((⟨rfl, hu⟩ | h) | h)
      · exact .inr (.inl ⟨hu, rfl⟩)
      · exact .inl h
      · exact .inr (.inr h)

/-- The constants that mention `u`, as the table holds them. -/
theorem mem_mentionedBy (u c : Name) :
    c ∈ i.mentionedBy.getD u [] ↔ ∃ d ∈ i.decls, d.name = c ∧ u ∈ d.uses := by
  rw [mentionedBy, mem_mentionedFold]
  simp

/-- The search backwards from `a` reaches `c` exactly when `c` reaches `a`. -/
theorem reach_mentionedBy_iff {a c : Name} :
    Reach (fun n => i.mentionedBy.getD n []) a c ↔ i.Reaches c a := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | step _ hc ih =>
      obtain ⟨d, hd, rfl, hu⟩ := (mem_mentionedBy i _ _).mp hc
      exact .step d hd rfl hu ih
  · intro h
    induction h with
    | refl => exact .refl
    | step d hd hn hu _ ih => exact .step ih ((mem_mentionedBy i _ _).mpr ⟨d, hd, hn, hu⟩)

/-- Each axiom of the input, with the constants that reach it: the search over the mentions, read
backwards from the axiom. The search costs what the graph of the input costs, once for each axiom.
-/
def axiomReach : List (Name × Std.HashSet Name) :=
  let callers := i.mentionedBy
  let weight := (callers.keys.map fun n => (callers.getD n []).length).sum
  (i.decls.filter (·.kind == .axiom)).map fun a =>
    (a.name, reach (callers.getD · []) weight [a.name])

/-- The sets hold exactly the axioms that each constant reaches. -/
theorem mem_axiomReach (c a : Name) :
    (∃ s, (a, s) ∈ i.axiomReach ∧ s.contains c = true) ↔ i.AxiomOf c a := by
  have hsearch : (reach (fun n => i.mentionedBy.getD n [])
      ((i.mentionedBy.keys.map fun n => (i.mentionedBy.getD n []).length).sum) [a]).contains c =
        true ↔ i.Reaches c a := by
    rw [mem_reach i.mentionedBy.keys [a] ?_ (Nat.le_refl _)]
    · simp [reach_mentionedBy_iff]
    · intro n hn
      rw [Std.HashMap.mem_keys]
      refine Classical.byContradiction fun hm => hn ?_
      rw [Std.HashMap.getD_eq_fallback hm]
  simp only [axiomReach, List.mem_map, List.mem_filter, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨s, ⟨d, ⟨hd, hk⟩, rfl, rfl⟩, hc⟩
    exact ⟨hsearch.mp hc, d, hd, rfl, hk⟩
  · rintro ⟨hr, d, hd, rfl, hk⟩
    exact ⟨_, ⟨d, ⟨hd, hk⟩, rfl, rfl⟩, hsearch.mpr hr⟩

/-- The tables of the input. -/
def tables : Tables i where
  index := i.index
  mem_index := i.index_eq_some
  claimed := i.claimedDecls
  mem_claimed := i.mem_claimedDecls
  axiomReach := i.axiomReach
  mem_axiomReach := i.mem_axiomReach

end Input

namespace Tables

variable {i : Input} (t : Tables i)

/-- The axiom set of constant `c` (`Input.AxiomOf`): each axiom of the input that `c` reaches. -/
def axiomSet (c : Name) : List Name :=
  t.axiomReach.filterMap fun p => if p.2.contains c then some p.1 else none

/-- The axiom set of a constant holds exactly the axioms that it reaches. -/
theorem mem_axiomSet (c a : Name) : a ∈ t.axiomSet c ↔ i.AxiomOf c a := by
  rw [← t.mem_axiomReach c a]
  simp only [axiomSet, List.mem_filterMap]
  constructor
  · rintro ⟨⟨b, s⟩, hm, hif⟩
    split at hif
    · rename_i hc
      simp only [Option.some.injEq] at hif
      subst hif
      exact ⟨s, hm, hc⟩
    · cases hif
  · rintro ⟨s, hm, hc⟩
    exact ⟨(a, s), hm, by simp [hc]⟩

end Tables

end Regula.Closed
