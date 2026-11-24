module

public import Regula.Input
public import Regula.Reach

public section

namespace Regula.Closed

open Lean (Name)

namespace Input

variable (i : Input)

inductive Reaches : Name → Name → Prop
  | refl (c : Name) : Reaches c c
  | step {c u e : Name} (d : Decl) : d ∈ i.decls → d.name = c → u ∈ d.uses → Reaches u e →
      Reaches c e

def AxiomOf (c a : Name) : Prop :=
  i.Reaches c a ∧ ∃ d ∈ i.decls, d.name = a ∧ d.kind = .axiom

end Input

structure Tables (i : Input) where
  index : Std.HashMap Name Decl
  mem_index : ∀ n d, index[n]? = some d ↔ d ∈ i.decls ∧ d.name = n
  claimed : List Decl
  mem_claimed : ∀ d, d ∈ claimed ↔ d ∈ i.decls ∧ d.module ∈ i.modules
  axiomReach : List (Name × Std.HashSet Name)
  mem_axiomReach : ∀ c a, (∃ s, (a, s) ∈ axiomReach ∧ s.contains c = true) ↔ i.AxiomOf c a

namespace Input

variable (i : Input)

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

def index : Std.HashMap Name Decl :=
  i.decls.foldl (fun m d => m.insert d.name d) {}

theorem index_eq_some (n : Name) (d : Decl) : i.index[n]? = some d ↔ d ∈ i.decls ∧ d.name = n := by
  rw [index, mem_indexFold _ i.unique]
  simp

def claimedDecls : List Decl :=
  let claimed := setOf i.modules
  i.decls.filter (claimed.contains ·.module)

theorem mem_claimedDecls (d : Decl) : d ∈ i.claimedDecls ↔ d ∈ i.decls ∧ d.module ∈ i.modules := by
  simp only [claimedDecls, List.mem_filter, mem_setOf]

def mentionedBy : Std.HashMap Name (List Name) :=
  i.decls.foldl (init := {}) fun m d =>
    d.uses.foldl (init := m) fun m u => m.insert u (d.name :: m.getD u [])

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

theorem mem_mentionedBy (u c : Name) :
    c ∈ i.mentionedBy.getD u [] ↔ ∃ d ∈ i.decls, d.name = c ∧ u ∈ d.uses := by
  rw [mentionedBy, mem_mentionedFold]
  simp

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

def axiomReach : List (Name × Std.HashSet Name) :=
  let callers := i.mentionedBy
  let weight := (callers.keys.map fun n => (callers.getD n []).length).sum
  (i.decls.filter (·.kind == .axiom)).map fun a =>
    (a.name, reach (callers.getD · []) weight [a.name])

theorem mem_axiomReach (c a : Name) :
    (∃ s, (a, s) ∈ i.axiomReach ∧ s.contains c = true) ↔ i.AxiomOf c a := by
  have hsearch : (reach (fun n => i.mentionedBy.getD n [])
      ((i.mentionedBy.keys.map fun n => (i.mentionedBy.getD n []).length).sum) [a]).contains c =
        true ↔ i.Reaches c a := by
    rw [mem_reach i.mentionedBy.keys [a] ?_ (Nat.le_refl _)]
    · simp [reach_mentionedBy_iff]
    · intro n hn
      rw [Std.HashMap.mem_keys]
      cases hc : i.mentionedBy.contains n with
      | true => exact Std.HashMap.contains_iff_mem.mp hc
      | false =>
        exact absurd (Std.HashMap.getD_eq_fallback (Std.HashMap.contains_eq_false_iff_not_mem.mp hc)) hn
  simp only [axiomReach, List.mem_map, List.mem_filter, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨s, ⟨d, ⟨hd, hk⟩, rfl, rfl⟩, hc⟩
    exact ⟨hsearch.mp hc, d, hd, rfl, hk⟩
  · rintro ⟨hr, d, hd, rfl, hk⟩
    exact ⟨_, ⟨d, ⟨hd, hk⟩, rfl, rfl⟩, hsearch.mpr hr⟩

def kernelNames : List Name :=
  [`Nat, `String, `Nat.zero, `Nat.succ, `String.ofList, `List.cons, `List.nil, `Char, `Char.ofNat, `Bool.true,
    `Bool.false]

def cone (seeds : List Name) : Std.HashSet Name :=
  let index := i.index
  reach (fun n => ((index[n]?).map (·.uses)).getD []) (i.decls.map (·.uses.length)).sum
    (i.claimedDecls.map (·.name) ++ seeds)

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

def axiomSet (c : Name) : List Name :=
  t.axiomReach.filterMap fun p => if p.2.contains c then some p.1 else none

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

structure Prepared where
  input : Input
  tables : Tables input

end Regula.Closed
