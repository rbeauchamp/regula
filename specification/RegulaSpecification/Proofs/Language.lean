/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.Language
import RegulaSpecification.Language

/-!
# The language decision against its record

`Regula.Language.decision` meets `languageRecord`, over every reading and in both directions, and
`Regula.Language.gate`, at the recording monad of `traced`, meets `fullGateRecord`, for every outcome, build result and
verdict. Each theorem is about the definition that the checker
runs. What fills a `Reading` from a real project (`Regula.Reader`) is in `Proofs/Reader.lean`, and the
specification's trusted base lists what stays assumed.
-/

namespace RegulaSpecification.Language

open Lean (Name Syntax)
open Regula.Language
open LeanIntent

theorem contains_iff {α : Type} [BEq α] [LawfulBEq α] {l : List α} {x : α} :
    l.contains x = true ↔ x ∈ l := List.contains_iff_mem

/-! ## The walk -/

theorem occurs_node {s : Syntax} {i k} {as : Array Syntax} :
    Occurs s (.node i k as) ↔ s = .node i k as ∨ (k ∉ leafKinds ∧ ∃ c ∈ as, Occurs s c) := by
  constructor
  · intro h
    cases h with
    | self => exact .inl rfl
    | child hk hc hs => exact .inr ⟨hk, _, hc, hs⟩
  · rintro (rfl | ⟨hk, c, hc, hs⟩)
    · exact .self _
    · exact .child hk hc hs

theorem occurs_leaf {s t : Syntax} (h : Occurs s t) (ht : ∀ i k as, t ≠ .node i k as) : s = t := by
  cases h with
  | self => rfl
  | child _ _ _ => exact absurd rfl (ht _ _ _)

/-- `positions` lists exactly the positions the specification reads. -/
theorem mem_positions_iff (t : Syntax) (s : Syntax) : s ∈ positions t ↔ Occurs s t := by
  induction t using Syntax.rec
    (motive_2 := fun as => s ∈ positionsOfArray as ↔ ∃ c ∈ as, Occurs s c)
    (motive_3 := fun l => s ∈ positionsOfList l ↔ ∃ c ∈ l, Occurs s c) with
  | missing =>
    simp only [positions, List.mem_singleton]
    exact ⟨fun h => h ▸ .self _, fun h => occurs_leaf h (by intros; exact Syntax.noConfusion)⟩
  | node i k as ih =>
    rw [occurs_node]
    simp only [positions, List.mem_cons]
    refine or_congr Iff.rfl ?_
    by_cases hk : k ∈ leafKinds
    · simp [hk]
    · simp [hk, ih]
  | atom i v =>
    simp only [positions, List.mem_singleton]
    exact ⟨fun h => h ▸ .self _, fun h => occurs_leaf h (by intros; exact Syntax.noConfusion)⟩
  | ident i r n p =>
    simp only [positions, List.mem_singleton]
    exact ⟨fun h => h ▸ .self _, fun h => occurs_leaf h (by intros; exact Syntax.noConfusion)⟩
  | mk l ih =>
    simp only [positionsOfArray, ih, List.mem_toArray]
  | nil => simp [positionsOfList]
  | cons x xs hx hxs =>
    simp only [positionsOfList, List.mem_append, hx, hxs, List.mem_cons, exists_eq_or_imp]

/-! ## One position -/

theorem anonymous_not_reserved : ¬ ReservedName .anonymous := fun h => by cases h

theorem root_not_reserved : ¬ ReservedName (.str .anonymous "_root_") := by
  intro h
  generalize he : Name.str .anonymous "_root_" = x at h
  cases h with
  | underscore _ hne =>
    obtain ⟨hp, hs⟩ := Name.str.inj he
    subst hp
    exact hne (by rw [hs])
  | autoParam =>
    have := (Name.str.inj he).2
    exact absurd this (by decide)
  | str h =>
    have := (Name.str.inj he).1
    subst this
    exact anonymous_not_reserved h
  | num _ => cases he

theorem reservedName_iff (n : Name) : reservedName n = true ↔ ReservedName n := by
  induction n with
  | anonymous =>
    simp only [reservedName, Bool.false_eq_true, false_iff]
    intro h
    cases h
  | num p m ih =>
    simp only [reservedName, ih]
    exact ⟨.num, fun h => by cases h with | num h => exact h⟩
  | str p s ih =>
    by_cases hr : (p, s) = (Name.anonymous, "_root_")
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      simp only [reservedName, Bool.false_eq_true, false_iff]
      exact root_not_reserved
    · have heq : reservedName (.str p s) =
          (s.front == '_' || s == "autoParam" || reservedName p) := by
        cases p with
        | anonymous =>
          have : s ≠ "_root_" := fun h => hr (by rw [h])
          simp [reservedName, this]
        | str _ _ => rfl
        | num _ _ => rfl
      rw [heq]
      simp only [Bool.or_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ((h | rfl) | h)
        · exact .underscore h hr
        · exact .autoParam
        · exact .str h
      · intro h
        cases h with
        | underscore h _ => exact .inl (.inl h)
        | autoParam => exact .inl (.inr rfl)
        | str h => exact .inr h

theorem mem_targets_iff (as : Array Syntax) (n : Name) : n ∈ targets as ↔ TargetOf as n := by
  simp only [targets, List.mem_flatMap, TargetOf]
  constructor
  · rintro ⟨x, hx, hn⟩
    have hx' : x ∈ as := by simpa using hx
    match x, hx', hn with
    | .ident i r m p, hx', hn =>
      have : n = m := by simpa using hn
      subst this
      exact ⟨i, r, p, .inl hx'⟩
    | .node i' k xs, hx', hn =>
      by_cases hk : k = `null
      · subst hk
        simp only [List.mem_filterMap] at hn
        obtain ⟨y, hy, hm⟩ := hn
        match y, hy, hm with
        | .ident i r m p, hy, hm =>
          have : m = n := by simpa using hm
          subst this
          exact ⟨i, r, p, .inr ⟨i', xs, hx', by simpa using hy⟩⟩
        | .missing, _, hm => simp at hm
        | .atom .., _, hm => simp at hm
        | .node .., _, hm => simp at hm
      · simp [hk] at hn
    | .missing, _, hn => simp at hn
    | .atom .., _, hn => simp at hn
  · rintro ⟨i, r, p, h | ⟨i', xs, hx, hy⟩⟩
    · exact ⟨_, by simpa using h, by simp⟩
    · refine ⟨_, by simpa using hx, ?_⟩
      simp only [List.mem_filterMap]
      exact ⟨_, by simpa using hy, by simp⟩

theorem canActivate_iff (N n : Name) : canActivate N n = true ↔ CanActivate N n := by
  simp only [canActivate, List.any_eq_true, List.mem_range, CanActivate, targetComponents]
  have hdrop : (fun x => x == `_root_) = (fun x : Name => decide (x = `_root_)) := by
    funext x
    by_cases h : x = `_root_ <;> simp [h]
  rw [hdrop]
  constructor
  · rintro ⟨i, hi, hs⟩
    refine ⟨i + 1, by omega, by omega, ?_⟩
    simpa [List.isSuffixOf_iff_suffix] using hs
  · rintro ⟨i, h0, hi, hs⟩
    refine ⟨i - 1, by omega, ?_⟩
    have : i - 1 + 1 = i := by omega
    rw [this]
    simpa [List.isSuffixOf_iff_suffix] using hs

theorem identIn_iff (allowed : List Name) (as : Array Syntax) (n : Nat) :
    identIn allowed as n = true ↔ ∃ i r c p, as[n]? = some (.ident i r c p) ∧ c ∈ allowed := by
  unfold identIn
  match h : as[n]? with
  | none => simp
  | some .missing => simp
  | some (.atom ..) => simp
  | some (.node ..) => simp
  | some (.ident i r c p) =>
    simp only [contains_iff, Option.some.injEq, Syntax.ident.injEq]
    exact ⟨fun hc => ⟨_, _, _, _, ⟨rfl, rfl, rfl, rfl⟩, hc⟩,
      fun ⟨_, _, _, _, ⟨_, _, hc, _⟩, hm⟩ => hc ▸ hm⟩

theorem noArgument_iff (o : Option Syntax) :
    noArgument o = true ↔ ∃ i', o = some (.node i' `null #[]) := by
  match o with
  | none => simp [noArgument]
  | some .missing => simp [noArgument]
  | some (.atom ..) => simp [noArgument]
  | some (.ident ..) => simp [noArgument]
  | some (.node i k xs) =>
    by_cases hk : k = `null
    · subst hk
      constructor
      · intro h
        have : xs = #[] := by simpa [noArgument] using h
        subst this
        exact ⟨i, rfl⟩
      · rintro ⟨i', h⟩
        cases Option.some.inj h
        simp [noArgument]
    · simp [noArgument, hk]

/-- The five clauses of `NodeAdmitted` that read a kind's arguments, against `argumentsAdmitted`. -/
theorem argumentsAdmitted_iff (sp : List Name) (k : Name) (as : Array Syntax) :
    argumentsAdmitted sp k as = true ↔
      (k = `Lean.Parser.Attr.simple →
        (∃ i r a p, as[0]? = some (.ident i r a p) ∧ a ∈ simpleAttributes) ∧
          ∃ i', as[1]? = some (.node i' `null #[])) ∧
      (k = `Lean.Parser.Command.set_option →
        ∃ i r o p, as[1]? = some (.ident i r o p) ∧ o ∈ options) ∧
      (k = `Lean.Parser.Tactic.posConfigItem →
        ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ configItems) ∧
      (k = `Lean.Parser.Command.derivingClass →
        ∃ i r c p, as[1]? = some (.ident i r c p) ∧ c ∈ derivingClasses) ∧
      ((k = `Lean.Parser.Command.namespace ∨ k = `Lean.Parser.Command.openSimple) →
        ∀ n, TargetOf as n → ∀ N ∈ sp, ¬ CanActivate N n) := by
  have htargets : (targets as).all (fun n => sp.all fun N => !canActivate N n) = true ↔
      ∀ n, TargetOf as n → ∀ N ∈ sp, ¬ CanActivate N n := by
    simp only [List.all_eq_true, mem_targets_iff, Bool.not_eq_true', ← canActivate_iff,
      Bool.not_eq_true]
  unfold argumentsAdmitted
  by_cases h1 : k = `Lean.Parser.Attr.simple
  · subst h1
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, identIn_iff, noArgument_iff]
    exact ⟨fun h => ⟨fun _ => h, fun e => absurd e (by decide), fun e => absurd e (by decide),
        fun e => absurd e (by decide),
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.1 trivial⟩
  have b1 : (k == `Lean.Parser.Attr.simple) = false := by simpa using h1
  by_cases h2 : k = `Lean.Parser.Command.set_option
  · subst h2
    simp only [b1, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [identIn_iff]
    exact ⟨fun h => ⟨fun e => absurd e (by decide), fun _ => h, fun e => absurd e (by decide),
        fun e => absurd e (by decide),
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.2.1 trivial⟩
  have b2 : (k == `Lean.Parser.Command.set_option) = false := by simpa using h2
  by_cases h3 : k = `Lean.Parser.Tactic.posConfigItem
  · subst h3
    simp only [b1, b2, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [identIn_iff]
    exact ⟨fun h => ⟨fun e => absurd e (by decide), fun e => absurd e (by decide), fun _ => h,
        fun e => absurd e (by decide),
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.2.2.1 trivial⟩
  have b3 : (k == `Lean.Parser.Tactic.posConfigItem) = false := by simpa using h3
  by_cases h4 : k = `Lean.Parser.Command.derivingClass
  · subst h4
    simp only [b1, b2, b3, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    rw [identIn_iff]
    exact ⟨fun h => ⟨fun e => absurd e (by decide), fun e => absurd e (by decide),
        fun e => absurd e (by decide), fun _ => h,
        fun e => e.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))⟩,
      fun h => h.2.2.2.1 trivial⟩
  have b4 : (k == `Lean.Parser.Command.derivingClass) = false := by simpa using h4
  simp only [b1, b2, b3, b4, Bool.false_eq_true, ↓reduceIte]
  by_cases h5 : k = `Lean.Parser.Command.namespace ∨ k = `Lean.Parser.Command.openSimple
  · have b5 : (k == `Lean.Parser.Command.namespace || k == `Lean.Parser.Command.openSimple) = true := by
      simpa using h5
    simp only [b5, ↓reduceIte, htargets]
    exact ⟨fun h => ⟨fun e => absurd e h1, fun e => absurd e h2, fun e => absurd e h3,
        fun e => absurd e h4, fun _ => h⟩, fun h => h.2.2.2.2 h5⟩
  · have b5 : (k == `Lean.Parser.Command.namespace || k == `Lean.Parser.Command.openSimple) = false := by
      simpa [Bool.or_eq_false_iff, not_or] using h5
    simp only [b5, Bool.false_eq_true, ↓reduceIte, true_iff]
    exact ⟨fun e => absurd e h1, fun e => absurd e h2, fun e => absurd e h3, fun e => absurd e h4,
      fun e => absurd e h5⟩

theorem positionAdmitted_iff (sp : List Name) (s : Syntax) :
    positionAdmitted sp s = true ↔ PositionAdmitted sp s := by
  cases s with
  | missing => simp [positionAdmitted, PositionAdmitted]
  | atom i v => simp [positionAdmitted, PositionAdmitted]
  | ident i r n p =>
    simp only [positionAdmitted, PositionAdmitted, Bool.not_eq_true', ← reservedName_iff,
      Bool.not_eq_true]
  | node i k as =>
    simp only [positionAdmitted, PositionAdmitted, NodeAdmitted, Bool.and_eq_true, Bool.or_eq_true,
      contains_iff, argumentsAdmitted_iff]

/-- A tree has no offender exactly when the specification admits it. -/
theorem offenders_eq_nil_iff (sp : List Name) (t : Syntax) :
    offenders sp t = [] ↔ TreeAdmitted sp t := by
  simp only [offenders, List.filter_eq_nil_iff, mem_positions_iff, TreeAdmitted, Bool.not_eq_true',
    ← positionAdmitted_iff]
  simp

/-- `offenders` reports a position exactly when it is a position of the tree that the specification
does not admit. -/
theorem mem_offenders_iff (sp : List Name) (t s : Syntax) :
    s ∈ offenders sp t ↔ Occurs s t ∧ ¬ PositionAdmitted sp s := by
  simp [offenders, mem_positions_iff, ← positionAdmitted_iff]

theorem moduleFile_iff (h : Syntax) : moduleFile h = true ↔ ModuleFile h := by
  simp only [moduleFile, List.any_eq_true, mem_positions_iff, ModuleFile]
  constructor
  · rintro ⟨x, hx, hk⟩
    match x, hx, hk with
    | .node i k as, hx, hk =>
      have : k = `Lean.Parser.Module.moduleTk := by simpa [isNodeOf] using hk
      subst this
      exact ⟨i, as, hx⟩
    | .missing, _, hk => simp [isNodeOf] at hk
    | .atom .., _, hk => simp [isNodeOf] at hk
    | .ident .., _, hk => simp [isNodeOf] at hk
  · rintro ⟨i, as, hx⟩
    exact ⟨_, hx, by simp [isNodeOf]⟩

theorem readToEnd_iff (cs : List Syntax) : readToEnd cs = true ↔ ReadToEnd cs := by
  simp only [readToEnd, ReadToEnd]
  match h : cs.getLast? with
  | none => simp
  | some .missing => simp [isNodeOf]
  | some (.atom ..) => simp [isNodeOf]
  | some (.ident ..) => simp [isNodeOf]
  | some (.node i k as) =>
    simp only [isNodeOf, beq_iff_eq, Option.some.injEq, Syntax.node.injEq]
    exact ⟨fun hk => ⟨i, as, ⟨rfl, hk, rfl⟩⟩, fun ⟨_, _, _, hk, _⟩ => hk⟩

/-- `FileRead.admitted` is `FileAdmitted`. -/
theorem fileAdmitted_iff (f : FileRead) : f.admitted = true ↔ FileAdmitted f := by
  simp only [FileRead.admitted, FileRead.offenders, Bool.and_eq_true, moduleFile_iff, readToEnd_iff,
    List.isEmpty_iff, List.flatMap_eq_nil_iff, List.mem_cons, forall_eq_or_imp, offenders_eq_nil_iff,
    FileAdmitted, and_assoc]

/-! ## The module names -/

theorem closedNameChar_iff (c : Char) : closedNameChar c = true ↔ ClosedChar c := by
  simp [closedNameChar, ClosedChar, or_assoc]

theorem closedComponent_iff (s : String) : closedComponent s = true ↔ ClosedComponent s := by
  simp [closedComponent, ClosedComponent, closedNameChar_iff]

/-- `closedModuleName` decides the specification's closed domain. -/
theorem closedModuleName_iff (n : Name) : closedModuleName n = true ↔ ClosedModuleName n := by
  induction n with
  | anonymous =>
    simp only [closedModuleName, Bool.false_eq_true, false_iff]
    intro h
    cases h
  | num p m _ =>
    simp only [closedModuleName, Bool.false_eq_true, false_iff]
    intro h
    cases h
  | str p s ih =>
    cases p with
    | anonymous =>
      simp only [closedModuleName, closedComponent_iff]
      exact ⟨.one, fun h => by
        cases h with
        | one hc => exact hc
        | more hp _ => cases hp⟩
    | str q t =>
      simp only [closedModuleName, closedComponent_iff, Bool.and_eq_true] at ih ⊢
      exact ⟨fun ⟨hp, hc⟩ => .more (ih.mp hp) hc, fun h => by
        cases h with
        | more hp hc => exact ⟨ih.mpr hp, hc⟩⟩
    | num q k =>
      simp only [closedModuleName, Bool.false_eq_true, false_iff]
      intro h
      cases h with
      | more hp _ => cases hp

/-! ## The reading -/

theorem configKeyAdmitted_iff (k : Name) : configKeyAdmitted k = true ↔ ConfigKeyAdmitted k := by
  simp [configKeyAdmitted, ConfigKeyAdmitted, List.any_eq_true]

theorem configClosed_iff (r : Reading) : r.configClosed = true ↔ ConfigClosed r := by
  have h : (∀ k ∈ r.configKeys, k.getRoot = `require ∨ ConfigKeyAdmitted k) ↔
      ∀ k ∈ r.configKeys, ¬ k.getRoot = `require → ConfigKeyAdmitted k :=
    forall_congr' fun k => forall_congr' fun _ => by
      by_cases hk : k.getRoot = `require <;> simp [hk]
  simp [Reading.configClosed, ConfigClosed, configKeyAdmitted_iff, and_assoc, h]

theorem readInFull_iff (r : Reading) : r.readInFull = true ↔ ReadInFull r := by
  simp [Reading.readInFull, ReadInFull]

theorem requiresDependency_iff (r : Reading) :
    r.requiresDependency = true ↔ RequiresDependency r := by
  simp [Reading.requiresDependency, RequiresDependency]

theorem mathlibReached_iff (r : Reading) : r.mathlibReached = true ↔ MathlibReached r := by
  simp [Reading.mathlibReached, MathlibReached]

theorem covered_iff (r : Reading) : r.covered = true ↔ Covered r := by
  simp [Reading.covered, Covered, closedModuleName_iff, and_assoc]

theorem filesAdmitted_iff (r : Reading) : r.filesAdmitted = true ↔ FilesAdmitted r := by
  simp [Reading.filesAdmitted, FilesAdmitted, fileAdmitted_iff]

/-- The decision the checker runs meets the record. -/
theorem decision_meets : languageRecord.Meets decision := by
  rw [language_meets_iff]
  have hn {b : Bool} {P : Prop} (h : b = true ↔ P) (hp : ¬ P) : b = false := by
    cases b
    · rfl
    · exact absurd (h.mp rfl) hp
  have base {r : Reading} (c : ConfigClosed r) (f : ReadInFull r) (k : ¬ RequiresDependency r) :
      r.configClosed = true ∧ r.readInFull = true ∧ r.requiresDependency = false :=
    ⟨(configClosed_iff r).mpr c, (readInFull_iff r).mpr f, hn (requiresDependency_iff r) k⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r c
    simp [decision, hn (configClosed_iff r) c]
  · intro r c f
    simp [decision, (configClosed_iff r).mpr c, hn (readInFull_iff r) f]
  · intro r c f k
    simp [decision, (configClosed_iff r).mpr c, (readInFull_iff r).mpr f,
      (requiresDependency_iff r).mpr k]
  · intro r c f k m
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, (mathlibReached_iff r).mpr m]
  · intro r c f k m v
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, hn (mathlibReached_iff r) m, hn (covered_iff r) v]
  · intro r c f k m v o
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, hn (mathlibReached_iff r) m, (covered_iff r).mpr v,
      hn (filesAdmitted_iff r) o]
  · intro r c f k m v o
    obtain ⟨b1, b2, b3⟩ := base c f k
    simp [decision, b1, b2, b3, hn (mathlibReached_iff r) m, (covered_iff r).mpr v,
      (filesAdmitted_iff r).mpr o]

/-- The check admits a reading exactly when `Inside` holds: its configuration and files are in the closed set, nothing is left
out, and there is no dependency and no Mathlib. This is the theorem the check exists for, over every `Lean.Syntax` that a reading can hold. -/
theorem decision_admitted_iff (r : Reading) : decision r = .admitted ↔ Inside r :=
  admitted_iff decision_meets r

/-- An empty set of files is never admitted. -/
theorem no_files_not_admitted (r : Reading) (h : r.files = []) : decision r ≠ .admitted := by
  intro ha
  obtain ⟨-, -, -, -, ⟨hroots, hr, -, hc⟩, -⟩ := (decision_admitted_iff r).mp ha
  cases hl : r.roots with
  | nil => exact hroots hl
  | cons m rest =>
    have hm : m ∈ r.reached := hr m (by simp [hl])
    obtain ⟨f, hf, -⟩ := hc m hm
    simp [h] at hf

/-- A project with Mathlib in its imports is never admitted. -/
theorem mathlib_not_admitted (r : Reading) (h : MathlibReached r) : decision r ≠ .admitted :=
  fun ha => ((decision_admitted_iff r).mp ha).2.2.2.1 h

/-- A project with a dependency is never admitted. -/
theorem dependency_not_admitted (r : Reading) (h : RequiresDependency r) : decision r ≠ .admitted :=
  fun ha => ((decision_admitted_iff r).mp ha).2.2.1 h

/-- A source directory or a `globs` entry that `openPaths` names is never admitted. -/
theorem open_path_not_admitted (r : Reading) (h : r.openPaths ≠ []) : decision r ≠ .admitted :=
  fun ha => h ((decision_admitted_iff r).mp ha).1.2.2.1

/-- A module name outside the closed domain is never admitted. -/
theorem unclosed_module_not_admitted (r : Reading) (m : Name) (hm : m ∈ r.reached)
    (hn : closedModuleName m = false) : decision r ≠ .admitted := fun ha => by
  have := ((decision_admitted_iff r).mp ha).2.2.2.2.1.2.2.1 m hm
  simp [(closedModuleName_iff m).mpr this] at hn

/-- A file with an offender is never admitted. -/
theorem offender_not_admitted (r : Reading) (f : FileRead) (hf : f ∈ r.files) (s t : Syntax)
    (ht : t = f.header ∨ t ∈ f.commands) (ho : s ∈ offenders f.scopedParsers t) :
    decision r ≠ .admitted := by
  intro ha
  obtain ⟨-, -, -, -, -, hfiles⟩ := (decision_admitted_iff r).mp ha
  have hadm : FileAdmitted f := hfiles f hf
  obtain ⟨hocc, hbad⟩ := (mem_offenders_iff _ _ _).mp ho
  rcases ht with rfl | ht
  · exact hbad (hadm.2.2.2.1 s hocc)
  · exact hbad (hadm.2.2.2.2 t ht s hocc)

/-! ## The checker's tree -/

/-- `treeRelative` gives what `path` holds below `base`, and each component of that starts with no `.`. -/
theorem treeRelative_iff (base path rel : List String) :
    treeRelative base path = some rel ↔ TreeRelative base path rel := by
  simp only [treeRelative, TreeRelative]
  by_cases hp : base <+: path
  · obtain ⟨tail, rfl⟩ := hp
    have hpre : base.isPrefixOf (base ++ tail) = true := by simp [List.isPrefixOf_iff_prefix]
    simp only [hpre, ↓reduceIte, List.drop_left, List.append_cancel_left_eq]
    constructor
    · intro h
      split at h
      · rename_i hall
        have := Option.some.inj h
        subst this
        simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hall
        refine ⟨rfl, fun c hc => ?_⟩
        have := hall c hc
        simp_all
      · simp at h
    · rintro ⟨rfl, hc⟩
      have : (tail.all fun c => !c.isEmpty && c.front != '.') = true := by
        simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq]
        intro c h
        exact ⟨by simpa using (hc c h).1, (hc c h).2⟩
      exact ite_eq_left_iff.mpr (fun h => absurd this h)
  · have hnone : base.isPrefixOf path = false := by
      rw [← Bool.not_eq_true, List.isPrefixOf_iff_prefix]
      exact hp
    simp only [hnone, Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff]
    rintro ⟨rfl, -⟩
    exact hp (List.prefix_append _ _)

/-- `..`, `.` and `.lake` are no components of what `treeRelative` gives. A component may still hold a separator or be
absolute, for an argument that no real path is. -/
theorem treeRelative_no_parent {base path rel : List String} (h : treeRelative base path = some rel) :
    ".." ∉ rel ∧ "." ∉ rel ∧ ".lake" ∉ rel := by
  obtain ⟨-, hc⟩ := (treeRelative_iff base path rel).mp h
  refine ⟨fun m => (hc _ m).2 ?_, fun m => (hc _ m).2 ?_, fun m => (hc _ m).2 ?_⟩ <;> decide

/-! ## The gate -/

/-- The gate over a monad that records its steps, as the specification reads it. -/
def traced : GateRun := fun o b v =>
  let tell (s : Step) : StateM (List Step) Unit := modify (s :: ·)
  let run := gate (m := StateM (List Step)) (tell .read *> pure o) (tell .build *> pure b)
    (tell .rules *> pure v)
  let (report, steps) := run.run []
  (report, steps.reverse)

/-- `gate`, at the recording monad of `traced`, meets its record, for every outcome, build result and verdict. -/
theorem gate_meets : fullGateRecord.Meets traced := by
  rw [fullGate_meets_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

/-- O2 before running: the gate's record has a model. -/
theorem fullGate_o2Run : O2Run fullGateRecord := o2Run_of_meets gate_meets

/-- The whole gate exits with 0 only for a full verdict's pass, on a reading the check admitted. -/
theorem gate_exit_zero_iff (r : Reading) (b : Bool) (v : Regula.Closed.Verdict) :
    (traced (decision r) b v).1.exitCode = 0 ↔
      Inside r ∧ b = true ∧ v = .pass := by
  rw [Report.exitCode_eq_zero_iff, ← decision_admitted_iff]
  obtain ⟨u1, u2, u3, u4, u5⟩ := (fullGate_meets_iff traced).mp gate_meets
  cases decision r <;> cases b <;> simp_all

end RegulaSpecification.Language
