import RegulaCore.CopyProgram
import RegulaPolicy.EnvironmentChange

/-! # Git isolation of a process tree

Lake starts its Git commands with no environment of its own, so each inherits the environment of
the process that runs Lake: the checker itself when it loads or builds a workspace in its own
process, or a Lake child. `Regula.Filesystem.Construction.processEnvironment` is the environment
that isolates every such command: Git's own repository-local names removed, no namespace, no
system or global configuration, and command-scope `core.symlinks=false`. A compiled program starts
again under it unless its environment already has it (`Regula.GitIsolation.enter`).

This module states the two decisions that start depends on, over the definitions it runs:
`unisolated` finds exactly the entries an environment lacks (`unisolated_eq_empty_iff`), and an
environment made by applying `processEnvironment` after any other changes lacks none
(`processEnvironment_isolated`), so a program started again under it runs at once. That the
operating system gives the child the environment Lean's spawn describes is the runtime's part
(`Regula.Process.effective`). -/

namespace Regula.GitIsolation

open Regula.Filesystem.Construction
open Regula.Process (effective)

/-- The entries of `isolation` whose value the environment `read` does not have. -/
def unisolated (read : String → Option String) (isolation : Array (String × Option String)) :
    Array (String × Option String) :=
  isolation.filter fun (name, value) => read name != value

/-- The environment `read` has every value that `isolation` names. -/
def Isolated (read : String → Option String) (isolation : Array (String × Option String)) :
    Prop :=
  ∀ entry ∈ isolation, read entry.1 = entry.2

/-- `unisolated` decides `Isolated` exactly, over every environment and every isolation. -/
theorem unisolated_eq_empty_iff (read : String → Option String)
    (isolation : Array (String × Option String)) :
    unisolated read isolation = #[] ↔ Isolated read isolation := by
  simp only [unisolated, Isolated, Array.filter_eq_empty_iff, bne_iff_ne, ne_eq,
    Decidable.not_not]

/-- No two entries of `changes` name one variable with two values. -/
def Consistent (changes : Array (String × Option String)) : Prop :=
  ∀ first ∈ changes, ∀ second ∈ changes, first.1 = second.1 → first.2 = second.2

/-- Changes that name another variable leave the value of `name` as it was. -/
private theorem foldl_other (name : String) :
    ∀ (changes : List (String × Option String)) (initial : Option String),
      (∀ entry ∈ changes, entry.1 ≠ name) →
      changes.foldl (fun value (key, replacement) => if key = name then replacement else value)
        initial = initial
  | [], _, _ => rfl
  | (key, replacement) :: rest, initial, other => by
    have head : key ≠ name := other (key, replacement) (List.mem_cons_self ..)
    have tail : ∀ later ∈ rest, later.1 ≠ name := fun later member =>
      other later (List.mem_cons_of_mem _ member)
    simp only [List.foldl_cons, head, ite_false]
    exact foldl_other name rest initial tail

/-- After changes that name `name` at least once, each time with `value`, `name` has `value`. -/
private theorem foldl_named (name : String) (value : Option String) :
    ∀ (changes : List (String × Option String)) (initial : Option String),
      (∃ entry ∈ changes, entry.1 = name) →
      (∀ entry ∈ changes, entry.1 = name → entry.2 = value) →
      changes.foldl (fun value (key, replacement) => if key = name then replacement else value)
        initial = value
  | [], _, ⟨_, member, _⟩, _ => nomatch member
  | (key, replacement) :: rest, initial, ⟨found, member, named⟩, agree => by
    simp only [List.foldl_cons]
    have tail : ∀ later ∈ rest, later.1 = name → later.2 = value := fun later member =>
      agree later (List.mem_cons_of_mem _ member)
    by_cases later : ∃ other ∈ rest, other.1 = name
    · exact foldl_named name value rest _ later tail
    · have none : ∀ other ∈ rest, other.1 ≠ name := fun other member same =>
        later ⟨other, member, same⟩
      rw [foldl_other name rest _ none]
      have same : key = name := by
        rcases List.mem_cons.mp member with rfl | member
        · exact named
        · exact absurd named (none found member)
      simp only [same, ite_true]
      exact agree (key, replacement) (List.mem_cons_self ..) same

/-- A variable that consistent changes name has their value after them, whatever changes came
before. -/
theorem effective_append (initial : Option String) (before : Array (String × Option String))
    {changes : Array (String × Option String)} (consistent : Consistent changes)
    {entry : String × Option String} (member : entry ∈ changes) :
    effective initial (before ++ changes) entry.1 = entry.2 := by
  rcases before with ⟨before⟩
  rcases changes with ⟨changes⟩
  simp only [effective, List.append_toArray, List.foldl_toArray', List.foldl_append]
  apply foldl_named entry.1 entry.2 changes
  · exact ⟨entry, List.mem_toArray.mp member, rfl⟩
  · intro other member' same
    exact consistent other (List.mem_toArray.mpr member') entry member same

/-- The settings name each variable once. -/
theorem isolationSettings_consistent : Consistent isolationSettings := by
  intro first member second member' same
  simp only [isolationSettings, List.mem_toArray, List.mem_cons, List.mem_nil_iff, or_false]
    at member member'
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases member' with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- `processEnvironment` names each variable with one value: Git's names are removed, and a Git
name that a setting also names is left to the setting. -/
theorem processEnvironment_consistent (names : Array String) :
    Consistent (processEnvironment names) := by
  intro first member second member' same
  simp only [processEnvironment, Array.mem_append, Array.mem_map, Array.mem_filter]
    at member member'
  rcases member with ⟨name, ⟨_, free⟩, rfl⟩ | setting <;>
    rcases member' with ⟨name', ⟨_, free'⟩, rfl⟩ | setting'
  · rfl
  · exfalso
    simp only [Bool.not_eq_true', Array.any_eq_false', beq_iff_eq] at free
    exact free second setting' same.symm
  · exfalso
    simp only [Bool.not_eq_true', Array.any_eq_false', beq_iff_eq] at free'
    exact free' first setting same
  · exact isolationSettings_consistent first setting second setting' same

/-- A child started with `processEnvironment names` after any other changes `before` has it: the
re-executed program finds no entry it lacks, so the start ends after one restart. -/
theorem processEnvironment_isolated (names : Array String) (parent : String → Option String)
    (before : Array (String × Option String)) :
    Isolated (fun name => effective (parent name) (before ++ processEnvironment names) name)
      (processEnvironment names) := fun entry member =>
  effective_append (parent entry.1) before (processEnvironment_consistent names) member

end Regula.GitIsolation
