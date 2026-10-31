/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.ReaderParts

/-!
# What the reader's walk over the imports gives

For every response: each source it holds was read by the exact-path test, its text written to the same relative
path of the tree and parsed from that same text; each toolchain module was found below the toolchain's library;
what it could not read has a `Reason`; and when nothing was left unread, each import of each source was reached.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open RegulaSpecification.Language

variable {L E : Type}

/-! ## One file -/

/-- `readExact` reads a file only through the exact-path test. -/
theorem readExact_spec {project path : FilePath} {t : List (Event L E)} {b : Except String String}
    (h : Runs (readExact project path : Attempt L E String).run t b) :
    (∀ text, b = .ok text → ∃ real, t = [⟨.realPath path, .ok real⟩, ⟨.readFile path, .ok text⟩] ∧
      Regula.Load.exactBelow project path real = true) ∧
    ((∃ e, b = .error e) → (∃ e ∈ t, Event.failedRead e) ∨
      ∃ real, t = [⟨.realPath path, .ok real⟩] ∧ Regula.Load.exactBelow project path real = false) := by
  rw [readExact] at h
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  obtain ⟨r', h₃, rfl⟩ := runs_attempt_iff.mp h₁
  obtain rfl := runs_call_iff.mp h₃
  cases r' with
  | error e =>
    obtain ⟨rfl, rfl⟩ := h₂
    exact ⟨fun _ h' => by cases h',
      fun _ => .inl ⟨⟨.realPath path, .error e⟩, by simp, ⟨e, rfl⟩⟩⟩
  | ok real =>
    dsimp only [Except.mapError] at h₂
    split at h₂
    · rename_i hb
      obtain ⟨r'', h₄, rfl⟩ := runs_attempt_iff.mp h₂
      obtain rfl := runs_call_iff.mp h₄
      cases r'' with
      | ok text =>
        exact ⟨fun _ he => by cases he; exact ⟨real, rfl, hb⟩, fun ⟨e, he⟩ => by cases he⟩
      | error e =>
        exact ⟨fun _ he => by cases he, fun _ =>
          .inl ⟨⟨.readFile path, .error e⟩, by simp, ⟨e, rfl⟩⟩⟩
    · rename_i hb
      obtain ⟨rfl, rfl⟩ := runs_attempt_throw_iff.mp h₂
      exact ⟨fun _ he => by cases he, fun _ =>
        .inr ⟨real, rfl, by simpa using hb⟩⟩

/-- `inTree` is `TreeRelative`. -/
theorem inTree_iff (tree path : FilePath) :
    inTree tree path = true ↔ ∃ rel, TreeRelative (parts tree) (parts path) rel := by
  simp only [inTree, Option.isSome_iff_exists, treeRelative_iff]

/-- `writeInTree` writes only after its tests of the path and of the directory above it. -/
theorem writeInTree_spec {tree path : FilePath} {text : String} {t : List (Event L E)}
    {b : Except String Unit} (h : Runs (writeInTree tree path text : Attempt L E Unit).run t b) :
    (b = .ok () → (⟨.writeFile path text, .ok ()⟩ : Event L E) ∈ t ∧
      ∃ pre, t = pre ++ [⟨.writeFile path text, .ok ()⟩]) ∧
    ((∃ e, b = .error e) → OutsideTree tree path ∨ ∃ e ∈ t, Event.failedRead e) ∧
    (∀ e ∈ t, ∀ p, e.acted? = some p → inTree tree p = true) ∧
    (∀ e ∈ t, ∀ input header state messages imports,
      e ≠ ⟨.parseHeader input, .ok (header, state, messages, imports)⟩) := by
  have hnotIn : inTree tree path = false → OutsideTree tree path := by
    intro hf
    refine .inl fun rel hr => ?_
    have := (inTree_iff tree path).mpr ⟨rel, hr⟩
    simp [hf] at this
  have hdirOut : ∀ d, path.parent = some d → inTree tree d = false → OutsideTree tree path := by
    intro d hd hf
    refine .inr ⟨d, hd, fun rel hr => ?_⟩
    have := (inTree_iff tree d).mpr ⟨rel, hr⟩
    simp [hf] at this
  sorry

end RegulaSpecification.Effects
