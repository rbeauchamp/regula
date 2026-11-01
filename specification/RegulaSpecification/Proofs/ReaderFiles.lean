/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderWalk

/-!
# What the reader's parse of each file gives

For every response: each file of a reading holds the header and the commands that Lean's parser gave from the text
the walk read, in the environment that an import gave for exactly the modules `Sees` states.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open RegulaSpecification.Language

variable {L E : Type}

/-- What a list's `lookup` gives is a member of the list. -/
theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    simp only [List.lookup_cons] at h
    by_cases hk : a = k
    · subst hk
      simp at h
      subst h
      simp
    · have : (a == k) = false := by simpa using hk
      simp only [this] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- With no key twice, `lookup` gives the value of each member. -/
theorem lookup_of_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {a : α} {b : β}
    (hn : (l.map (·.1)).Nodup) (h : (a, b) ∈ l) : l.lookup a = some b := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    obtain ⟨k, v⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with he | hm
    · cases he
      simp
    · have hk : a ≠ k := by
        rintro rfl
        exact hn.1 (List.mem_map.mpr ⟨(a, b), hm, rfl⟩)
      have : (a == k) = false := by simpa using hk
      simp only [List.lookup_cons, this]
      exact ih hn.2 hm

/-- The events of a parse act on nothing. -/
theorem parsed_no_act {input : InputContext} {env : E} {fuel : Nat} {state : ModuleParserState} {messages : MessageLog}
    {commands : List Syntax} {final : MessageLog} {t : List (Event L E)}
    (h : Parsed input env fuel state messages commands final t) : ∀ e ∈ t, e.acted? = none := by
  induction h with
  | stop => intro e he; cases he
  | last _ =>
    intro e he
    have : e = _ := List.mem_singleton.mp he
    subst this
    rfl
  | next _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rfl
    · exact ih e he

/-- What one file of a reading holds, from the source `s`. -/
def FileFrom (T : List (Event L E)) (sources : List (Name × Source)) (toolchain : List Name) (m : Name)
    (s : Source) (f : FileRead) : Prop :=
  f.module = m ∧ f.header = s.header ∧
    ∃ (env : E) (final : MessageLog) (commands : List (Event L E)),
      (⟨.importForParser
          (visibleToolchain (fun n => (sources.lookup n).map (·.imports)) toolchain.contains
            (s.imports.toList.map (·.module)) []
            ((s.imports.toList.map (·.module)).length + (sources.map (·.2.imports.size)).sum + 1)).eraseDups,
        .ok (env, f.scopedParsers)⟩ : Event L E) ∈ T ∧
      Parsed s.input env (s.input.inputString.utf8ByteSize + 1) s.state s.messages f.commands final commands ∧
        commands.Sublist T ∧
      f.parsed = !final.hasErrors

/-- What the search gives holds only the toolchain's modules. -/
theorem mem_visible_held {headers : Name → Option (Array Import)} {isToolchain : Name → Bool} {todo seen : List Name}
    {fuel : Nat} {n : Name} (h : n ∈ visibleToolchain headers isToolchain todo seen fuel) : isToolchain n = true := by
  induction fuel generalizing todo seen with
  | zero => simp [visibleToolchain] at h
  | succ fuel ih =>
    cases todo with
    | nil => simp [visibleToolchain] at h
    | cons m rest =>
      simp only [visibleToolchain] at h
      split at h
      · rename_i ht
        rcases List.mem_cons.mp h with rfl | h
        · exact ht
        · exact ih h
      · split at h
        · exact ih h
        · exact ih h

/-- `environmentFor` gives what an import gave for exactly those modules. -/
theorem environmentFor_spec {T t : List (Event L E)} {cache : ParserCache E} {mods : List Name}
    {b : Except String ((E × List Name) × ParserCache E)} (hT : t.Sublist T)
    (hc : ∀ x ∈ cache, (⟨.importForParser x.1, .ok x.2⟩ : Event L E) ∈ T)
    (h : Runs (environmentFor cache mods : Attempt L E _).run t b) :
    (∀ pair c', b = .ok (pair, c') → (⟨.importForParser mods.eraseDups, .ok pair⟩ : Event L E) ∈ T ∧
      ∀ x ∈ c', (⟨.importForParser x.1, .ok x.2⟩ : Event L E) ∈ T) ∧
    ((∃ e, b = .error e) → ∃ x, (⟨.importForParser mods.eraseDups, .error x⟩ : Event L E) ∈ t) ∧
    ∀ e ∈ t, e.acted? = none := by
  rw [environmentFor] at h
  split at h
  · rename_i pair' hl
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    refine ⟨fun pair c' he => ?_, fun ⟨e, he⟩ => (by cases he), fun e he => (by cases he)⟩
    cases he
    exact ⟨hc _ (mem_of_lookup hl), hc⟩
  · obtain ⟨t₅, t₆, r₅, rfl, h₅, h₆⟩ := runs_attempt_bind_iff.mp h
    obtain ⟨r₆, h₇, rfl⟩ := runs_attempt_iff.mp h₅
    obtain rfl := runs_call_iff.mp h₇
    cases r₆ with
    | error e' =>
      obtain ⟨rfl, rfl⟩ := h₆
      refine ⟨fun _ _ he => (by cases he), fun _ =>
        ⟨e', by simp⟩, fun e he => ?_⟩
      simp only [List.append_nil, List.mem_singleton] at he
      subst he
      rfl
    | ok p =>
      obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₆
      refine ⟨fun pair c' he => ?_, fun ⟨e, he⟩ => (by cases he), fun e he => ?_⟩
      · cases he
        have hev : (⟨.importForParser mods.eraseDups, .ok p⟩ : Event L E) ∈ T := hT.subset (by simp)
        refine ⟨hev, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hev
        · exact hc x hx
      · simp only [List.append_nil, List.mem_singleton] at he
        subst he
        rfl

/-- `parseFile` holds what `FileFrom` states, or an import failed. -/
theorem parseFile_spec {T t : List (Event L E)} {sources : List (Name × Source)} {toolchain : List Name}
    {cache : ParserCache E} {m : Name} {s : Source} {b : Except String (FileRead × ParserCache E)}
    (hT : t.Sublist T) (hc : ∀ x ∈ cache, (⟨.importForParser x.1, .ok x.2⟩ : Event L E) ∈ T)
    (h : Runs (parseFile cache sources toolchain m s : Attempt L E _).run t b) :
    (∀ f c', b = .ok (f, c') → FileFrom T sources toolchain m s f ∧
      ∀ x ∈ c', (⟨.importForParser x.1, .ok x.2⟩ : Event L E) ∈ T) ∧
    ((∃ e, b = .error e) → ∃ mods x, (⟨.importForParser mods, .error x⟩ : Event L E) ∈ t ∧ ∀ n ∈ mods, n ∈ toolchain) ∧
    ∀ e ∈ t, e.acted? = none := by
  rw [parseFile] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  have hT₁ : t₁.Sublist T := (List.sublist_append_left _ _).trans hT
  have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
  obtain ⟨e1, e2, e3⟩ := environmentFor_spec hT₁ hc h₁
  cases r with
  | error why =>
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨x, hx⟩ := e2 ⟨why, rfl⟩
    refine ⟨fun _ _ he => (by cases he), fun _ => ⟨_, x, by simpa using hx, fun n hn => ?_⟩, by simpa using e3⟩
    have := mem_visible_held (List.mem_eraseDups.mp hn)
    simpa using this
  | ok envResult =>
    obtain ⟨⟨env, scopedParsers⟩, cache'⟩ := envResult
    obtain ⟨hev, hc'⟩ := e1 _ _ rfl
    obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
    obtain ⟨⟨commands, final⟩, h₅, rfl⟩ := runs_lift_iff.mp h₃
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
    have hparsed := parseAll_parsed _ _ _ _ _ h₅
    have hact := parsed_no_act hparsed
    refine ⟨fun f c' he => ?_, fun ⟨e, he⟩ => (by cases he), fun e he => ?_⟩
    · cases he
      exact ⟨⟨rfl, rfl, env, final, t₃, hev, hparsed, by simpa using hT₂, rfl⟩, hc'⟩
    · simp only [List.append_nil, List.mem_append] at he
      rcases he with he | he
      · exact e3 e he
      · exact hact e he

/-- `parseFiles` holds each source's file, and nothing else, or an import failed. -/
theorem parseFiles_spec (sources : List (Name × Source)) (toolchain : List Name) {T : List (Event L E)}
    (todo : List (Name × Source)) (cache : ParserCache E) {t : List (Event L E)}
    {b : Except String (List FileRead)}
    (hT : t.Sublist T) (hc : ∀ x ∈ cache, (⟨.importForParser x.1, .ok x.2⟩ : Event L E) ∈ T)
    (h : Runs (parseFiles sources toolchain cache todo : Attempt L E _).run t b) :
    (∀ files, b = .ok files → (∀ f ∈ files, ∃ x ∈ todo, FileFrom T sources toolchain x.1 x.2 f) ∧
      ∀ x ∈ todo, ∃ f ∈ files, FileFrom T sources toolchain x.1 x.2 f) ∧
    ((∃ e, b = .error e) → ∃ mods x, (⟨.importForParser mods, .error x⟩ : Event L E) ∈ t ∧ ∀ n ∈ mods, n ∈ toolchain) ∧
    ∀ e ∈ t, e.acted? = none := by
  induction todo generalizing cache t b with
  | nil =>
    rw [parseFiles] at h
    obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h
    refine ⟨fun files he => ?_, fun ⟨e, he⟩ => (by cases he), fun e he => (by cases he)⟩
    cases he
    simp
  | cons x todo ih =>
    obtain ⟨m, s⟩ := x
    rw [parseFiles] at h
    obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
    have hT₁ : t₁.Sublist T := (List.sublist_append_left _ _).trans hT
    have hT₂ : t₂.Sublist T := (List.sublist_append_right _ _).trans hT
    obtain ⟨p1, p2, p3⟩ := parseFile_spec hT₁ hc h₁
    cases r with
    | error why =>
      obtain ⟨rfl, rfl⟩ := h₂
      obtain ⟨mods, x, hx, hn⟩ := p2 ⟨why, rfl⟩
      exact ⟨fun _ he => (by cases he), fun _ => ⟨mods, x, by simp [hx], hn⟩, by simpa using p3⟩
    | ok fileResult =>
      obtain ⟨file, cache'⟩ := fileResult
      obtain ⟨hfile, hc'⟩ := p1 _ _ rfl
      obtain ⟨t₃, t₄, r₃, rfl, h₃, h₄⟩ := runs_attempt_bind_iff.mp h₂
      obtain ⟨i1, i2, i3⟩ := ih cache' ((List.sublist_append_left _ _).trans hT₂) hc' h₃
      have hact : ∀ e ∈ t₁ ++ (t₃ ++ t₄), e.acted? = none ∧ True := by
        intro e he
        cases r₃ with
        | error w =>
          obtain ⟨rfl, rfl⟩ := h₄
          simp only [List.append_nil, List.mem_append] at he
          rcases he with he | he
          · exact ⟨p3 e he, trivial⟩
          · exact ⟨i3 e he, trivial⟩
        | ok fs =>
          obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
          simp only [List.append_nil, List.mem_append] at he
          rcases he with he | he
          · exact ⟨p3 e he, trivial⟩
          · exact ⟨i3 e he, trivial⟩
      cases r₃ with
      | error w =>
        obtain ⟨rfl, rfl⟩ := h₄
        obtain ⟨mods, x, hx, hn⟩ := i2 ⟨w, rfl⟩
        exact ⟨fun _ he => (by cases he), fun _ => ⟨mods, x, by simp [hx], hn⟩, fun e he => (hact e he).1⟩
      | ok fs =>
        obtain ⟨rfl, rfl⟩ := runs_attempt_pure_iff.mp h₄
        refine ⟨fun files he => ?_, fun ⟨e, he⟩ => (by cases he), fun e he => (hact e he).1⟩
        cases he
        obtain ⟨j1, j2⟩ := i1 fs rfl
        constructor
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact ⟨(m, s), List.mem_cons_self .., hfile⟩
          · obtain ⟨x, hx, hxf⟩ := j1 f hf
            exact ⟨x, List.mem_cons_of_mem _ hx, hxf⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨file, List.mem_cons_self .., hfile⟩
          · obtain ⟨f, hf, hxf⟩ := j2 x hx
            exact ⟨f, List.mem_cons_of_mem _ hf, hxf⟩

end RegulaSpecification.Effects
