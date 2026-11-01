/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord
import Regula.Reader
import Regula.Table

/-!
# Runs of a program, and what the interpreter does

The rules that take a statement about a run of a program to statements about its parts, and the link from a
program to its execution: `interpret_runs` proves that `Regula.Effect.Prog.interpret`, at `BaseIO` and from any
state of the world, gives a run in the sense of `Runs`, each of whose responses is the table's answer at the world
the run has reached. `BaseIO` is a state monad in Lean's own definition (`Init/System/ST.lean`), so this is a
theorem about the definition and no assumption about how effects are ordered; that the compiler keeps that order
stays with the compiler, which the trusted base lists.
-/

namespace RegulaSpecification.Effects

open Regula.Effect
open Regula.Reader (Attempt attempt)

variable {L E α β : Type}

theorem runs_done_iff {a b : α} {t : List (Event L E)} : Runs (.done a) t b ↔ t = [] ∧ b = a := by
  constructor
  · rintro ⟨⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .done _

theorem runs_ask_iff {o : Op L E} {next : Resp o → Prog L E α} {t : List (Event L E)} {a : α} :
    Runs (.ask o next) t a ↔ ∃ r t', t = ⟨o, r⟩ :: t' ∧ Runs (next r) t' a := by
  constructor
  · intro h
    cases h with
    | ask _ _ r h => exact ⟨r, _, rfl, h⟩
  · rintro ⟨r, t', rfl, h⟩
    exact .ask _ _ _ h

/-- A run of `p` and then `f` is a run of `p` followed by a run of what its value selects. -/
theorem runs_bind_iff {p : Prog L E α} {f : α → Prog L E β} {t : List (Event L E)} {b : β} :
    Runs (Prog.bind p f) t b ↔ ∃ t₁ t₂ a, t = t₁ ++ t₂ ∧ Runs p t₁ a ∧ Runs (f a) t₂ b := by
  induction p generalizing t with
  | done a =>
    constructor
    · intro h
      exact ⟨[], t, a, rfl, .done _, h⟩
    · rintro ⟨t₁, t₂, a', rfl, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₁
      exact h₂
  | ask o next ih =>
    simp only [Prog.bind, runs_ask_iff]
    constructor
    · rintro ⟨r, t', rfl, h⟩
      obtain ⟨t₁, t₂, a, rfl, h₁, h₂⟩ := (ih r).mp h
      exact ⟨⟨o, r⟩ :: t₁, t₂, a, rfl, ⟨r, t₁, rfl, h₁⟩, h₂⟩
    · rintro ⟨t₁, t₂, a, rfl, ⟨r, t', rfl, h₁⟩, h₂⟩
      exact ⟨r, t' ++ t₂, rfl, (ih r).mpr ⟨t', t₂, a, rfl, h₁, h₂⟩⟩

theorem runs_pure_iff {a b : α} {t : List (Event L E)} :
    Runs (pure a : Prog L E α) t b ↔ t = [] ∧ b = a :=
  runs_done_iff

theorem runs_seq_iff {p : Prog L E α} {f : α → Prog L E β} {t : List (Event L E)} {b : β} :
    Runs (p >>= f) t b ↔ ∃ t₁ t₂ a, t = t₁ ++ t₂ ∧ Runs p t₁ a ∧ Runs (f a) t₂ b :=
  runs_bind_iff

/-- A run of one operation is its one event. -/
theorem runs_call_iff {o : Op L E} {t : List (Event L E)} {r : Resp o} :
    Runs (Prog.call o) t r ↔ t = [⟨o, r⟩] := by
  simp only [Prog.call, runs_ask_iff, runs_done_iff]
  constructor
  · rintro ⟨r', t', rfl, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨r, [], rfl, rfl, rfl⟩

/-! ## Programs that can stop -/

/-- A run of an attempt and then what its value selects: the second part runs only on success. -/
theorem runs_attempt_bind_iff {x : Attempt L E α} {f : α → Attempt L E β} {t : List (Event L E)}
    {b : Except String β} :
    Runs (x >>= f).run t b ↔ ∃ t₁ t₂ r, t = t₁ ++ t₂ ∧ Runs x.run t₁ r ∧
      match r with
      | .ok a => Runs (f a).run t₂ b
      | .error e => t₂ = [] ∧ b = .error e := by
  change Runs (Prog.bind x.run _) t b ↔ _
  rw [runs_bind_iff]
  constructor
  · rintro ⟨t₁, t₂, r, rfl, h₁, h₂⟩
    refine ⟨t₁, t₂, r, rfl, h₁, ?_⟩
    cases r with
    | ok a => exact h₂
    | error e => exact runs_done_iff.mp h₂
  · rintro ⟨t₁, t₂, r, rfl, h₁, h₂⟩
    refine ⟨t₁, t₂, r, rfl, h₁, ?_⟩
    cases r with
    | ok a => exact h₂
    | error e => exact runs_done_iff.mpr h₂

theorem runs_attempt_pure_iff {a : α} {t : List (Event L E)} {b : Except String α} :
    Runs (pure a : Attempt L E α).run t b ↔ t = [] ∧ b = .ok a :=
  runs_done_iff

theorem runs_attempt_throw_iff {e : String} {t : List (Event L E)} {b : Except String α} :
    Runs (throw e : Attempt L E α).run t b ↔ t = [] ∧ b = .error e :=
  runs_done_iff

/-- A run of a program that cannot stop, inside an attempt. -/
theorem runs_lift_iff {p : Prog L E α} {t : List (Event L E)} {b : Except String α} :
    Runs (ExceptT.lift p : Attempt L E α).run t b ↔ ∃ a, Runs p t a ∧ b = .ok a := by
  change Runs (Prog.bind p _) t b ↔ _
  rw [runs_bind_iff]
  constructor
  · rintro ⟨t₁, t₂, a, rfl, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₂
    exact ⟨a, by simpa using h₁, rfl⟩
  · rintro ⟨a, h, rfl⟩
    exact ⟨t, [], a, by simp, h, .done _⟩

/-- A run of an operation that can fail, with its failure as the reason. -/
theorem runs_attempt_iff {step : Prog L E (Except IO.Error α)} {t : List (Event L E)}
    {b : Except String α} :
    Runs (attempt step).run t b ↔ ∃ r, Runs step t r ∧ b = r.mapError toString := by
  change Runs (Prog.bind step _) t b ↔ _
  rw [runs_bind_iff]
  constructor
  · rintro ⟨t₁, t₂, r, rfl, h₁, h₂⟩
    refine ⟨r, ?_, ?_⟩
    all_goals cases r <;> obtain ⟨rfl, rfl⟩ := runs_done_iff.mp h₂ <;> simp_all [Except.mapError]
  · rintro ⟨r, h, rfl⟩
    refine ⟨t, [], r, by simp, h, ?_⟩
    cases r <;> exact .done _

/-! ## Each operation of a program is asked in order: the interpreter -/

/-- The events that the interpreter records, from the world `w`, for the program `p`. -/
def traceFrom (table : (o : Op L E) → BaseIO (Resp o)) :
    Prog L E α → Void IO.RealWorld → List (Event L E)
  | .done _, _ => []
  | .ask o next, w =>
    ⟨o, (table o w).val⟩ :: traceFrom table (next (table o w).val) (table o w).state

/-- From any world, `interpret` gives the value of a run whose events are the operations the program asks,
each with the table's answer at the world the run has reached. So what is proved of `Runs` holds of what the
definition of `interpret` gives, for every table. -/
theorem interpret_runs (table : (o : Op L E) → BaseIO (Resp o)) (p : Prog L E α) (w : Void IO.RealWorld) :
    Runs p (traceFrom table p w) (Prog.interpret table p w).val := by
  induction p generalizing w with
  | done a => exact .done a
  | ask o next ih =>
    have := ih ((table o w).val) (table o w).state
    exact .ask o next _ this

end RegulaSpecification.Effects
