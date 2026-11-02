/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Reader

/-!
# What the reader never asks

The reader asks only what `ReadOp` admits: on no response does it ask a Lake command, a load of a build for the rules, or a
print. So the reader requests no build, for every response.
-/

namespace RegulaSpecification.Effects

open Lean (Name)
open System (FilePath)
open Regula.Effect
open Regula.Reader

variable {L E α β : Type}

/-- An operation that the reader may ask. -/
def ReadOp : Op L E → Prop
  | .runLake .. | .importForRules .. | .println _ | .flush | .createTempDir | .removeDirAll _ | .leanVersion => False
  | _ => True

/-- On every response, a program asks only operations of `P`. -/
def OnlyIn (P : Op L E → Prop) (p : Prog L E α) : Prop :=
  ∀ t a, Runs p t a → ∀ e ∈ t, P e.op

/-- On every response, a program asks only what the reader may. -/
abbrev Only (p : Prog L E α) : Prop :=
  OnlyIn ReadOp p

variable {P : Op L E → Prop}

theorem only_pure (a : α) : OnlyIn P (pure a : Prog L E α) := by
  intro t b h e he
  obtain ⟨rfl, -⟩ := runs_pure_iff.mp h
  cases he

theorem only_call {o : Op L E} (h : P o) : OnlyIn P (Prog.call o) := by
  intro t a hr e he
  obtain rfl := runs_call_iff.mp hr
  have : e = _ := List.mem_singleton.mp he
  subst this
  exact h

theorem only_seq {p : Prog L E α} {f : α → Prog L E β} (hp : OnlyIn P p) (hf : ∀ a, OnlyIn P (f a)) :
    OnlyIn P (p >>= f) := by
  intro t b h e he
  obtain ⟨t₁, t₂, a, rfl, h₁, h₂⟩ := runs_seq_iff.mp h
  rcases List.mem_append.mp he with he | he
  · exact hp _ _ h₁ e he
  · exact hf a _ _ h₂ e he

/-- An attempt's program asks only operations of `P`. -/
def OnlyAIn (P : Op L E → Prop) (x : Attempt L E α) : Prop :=
  OnlyIn P x.run

/-- An attempt's program asks only what the reader may. -/
abbrev OnlyA (x : Attempt L E α) : Prop :=
  OnlyAIn ReadOp x

theorem onlyA_pure (a : α) : OnlyAIn P (pure a : Attempt L E α) :=
  only_pure _

theorem onlyA_throw (e : String) : OnlyAIn P (throw e : Attempt L E α) :=
  only_pure _

theorem onlyA_seq {x : Attempt L E α} {f : α → Attempt L E β} (hx : OnlyAIn P x)
    (hf : ∀ a, OnlyAIn P (f a)) : OnlyAIn P (x >>= f) := by
  intro t b h e he
  obtain ⟨t₁, t₂, r, rfl, h₁, h₂⟩ := runs_attempt_bind_iff.mp h
  rcases List.mem_append.mp he with he | he
  · exact hx _ _ h₁ e he
  · cases r with
    | ok a => exact hf a _ _ h₂ e he
    | error why =>
      obtain ⟨rfl, -⟩ := h₂
      cases he

theorem onlyA_lift {p : Prog L E α} (hp : OnlyIn P p) : OnlyAIn P (ExceptT.lift p : Attempt L E α) := by
  intro t b h e he
  obtain ⟨a, h₁, -⟩ := runs_lift_iff.mp h
  exact hp _ _ h₁ e he

theorem onlyA_attempt {step : Prog L E (Except IO.Error α)} (hp : OnlyIn P step) :
    OnlyAIn P (attempt step) := by
  intro t b h e he
  obtain ⟨r, h₁, -⟩ := runs_attempt_iff.mp h
  exact hp _ _ h₁ e he

/-- Each step of a program whose operations the reader may ask, by its structure. -/
macro "only_steps" : tactic =>
  `(tactic| repeat' first
    | exact only_pure _ | exact onlyA_pure _ | exact onlyA_throw _
    | exact onlyA_attempt (only_call trivial) | exact onlyA_lift (only_call trivial) | exact only_call trivial
    | refine onlyA_seq ?_ fun _ => ?_ | refine only_seq ?_ fun _ => ?_
    | refine onlyA_lift ?_ | split | dsimp only)

theorem only_readExact (project path : FilePath) : OnlyA (readExact project path : Attempt L E _) := by
  rw [readExact, realPath]; only_steps

theorem only_writeInTree (tree path : FilePath) (text : String) : OnlyA (writeInTree tree path text : Attempt L E _) := by
  rw [writeInTree, makeParent]; only_steps

theorem only_readSource (project tree path : FilePath) : OnlyA (readSource project tree path : Attempt L E _) := by
  rw [readSource, readForTree]
  refine onlyA_seq ?_ fun _ => by only_steps
  split
  · exact onlyA_throw _
  · split
    · exact only_readExact _ _
    · exact onlyA_throw _

theorem only_walk (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (fuel : Nat) (todo : List Name) (w : Walk) :
    Only (walk project tree root modules fuel todo w : Prog L E Walk) := by
  induction fuel generalizing todo w with
  | zero => cases todo <;> (rw [walk]; exact only_pure _)
  | succ fuel ih =>
    cases todo with
    | nil => rw [walk]; exact only_pure _
    | cons m rest =>
      rw [walk]
      split
      · exact ih _ _
      · split
        · exact ih _ _
        · split
          · exact ih _ _
          · split
            · exact only_seq (only_readSource _ _ _) fun r => by cases r <;> exact ih _ _
            · refine only_seq ?_ fun r => by cases r <;> exact ih _ _
              rw [toolchainOLean]; only_steps

theorem only_parseAll (input) (env : E) (state) (messages) (fuel : Nat) :
    Only (parseAll input env state messages fuel : Prog L E _) := by
  induction fuel generalizing state messages with
  | zero => rw [parseAll]; exact only_pure _
  | succ fuel ih =>
    rw [parseAll]
    refine only_seq (only_call trivial) fun ⟨stx, state', messages'⟩ => ?_
    dsimp only
    split
    · exact only_pure _
    · exact only_seq (ih _ _) fun _ => only_pure _

theorem only_parseFiles (path : List FilePath) (sources : List (Name × Source)) (toolchain : List Name) (todo : List (Name × Source))
    (cache : ParserCache E) : OnlyA (parseFiles path sources toolchain cache todo : Attempt L E _) := by
  induction todo generalizing cache with
  | nil => rw [parseFiles]; exact onlyA_pure _
  | cons x todo ih =>
    obtain ⟨m, s⟩ := x
    rw [parseFiles]
    refine onlyA_seq ?_ fun r => onlyA_seq (ih _) fun _ => onlyA_pure _
    rw [parseFile]
    refine onlyA_seq ?_ fun r => onlyA_seq (onlyA_lift (only_parseAll _ _ _ _ _)) fun _ => onlyA_pure _
    rw [environmentFor]; only_steps

theorem only_defaultModules (root : Root L) (targets : List Name) :
    OnlyA (defaultModules root targets : Attempt L E _) := by
  induction targets with
  | nil => rw [defaultModules]; exact onlyA_pure _
  | cons t ts ih =>
    rw [defaultModules]
    refine onlyA_seq ?_ fun _ => onlyA_seq ih fun _ => onlyA_pure _
    rw [modulesOfTarget]; only_steps

theorem only_readBack (l : List (FilePath × String)) : OnlyA (readBack l : Attempt L E _) := by
  induction l with
  | nil => rw [readBack]; exact onlyA_pure _
  | cons x rest ih =>
    rw [readBack]
    refine onlyA_seq (onlyA_attempt (only_call trivial)) fun _ => ?_
    split
    · exact ih
    · exact onlyA_throw _

theorem only_writeSources (tree : FilePath) (srcs : List (Name × Source)) :
    OnlyA (writeSources tree srcs : Attempt L E _) := by
  induction srcs with
  | nil => rw [writeSources]; exact onlyA_pure _
  | cons x rest ih =>
    rw [writeSources]
    exact onlyA_seq (only_writeInTree _ _ _) fun _ => ih

theorem only_existsByName (path : FilePath) : OnlyA (existsByName path : Attempt L E _) := by
  rw [existsByName]
  refine only_seq (only_call trivial) fun r => ?_
  cases r with
  | ok _ => exact only_pure _
  | error e => cases e <;> exact only_pure _

/-- The reader asks only what `ReadOp` admits, on every response. -/
theorem only_readProject (sysroot : String) (dir treeDir : FilePath) :
    OnlyA (read sysroot dir treeDir : Attempt L E _) := by
  unfold Regula.Reader.read readProject realPath toolchainOf readConfig readKeys readRoot readFiles noOtherConfig
  repeat' first
    | exact only_readExact _ _ | exact only_existsByName _ | exact only_writeInTree _ _ _ | exact only_defaultModules _ _
    | exact only_walk _ _ _ _ _ _ _ | exact only_parseFiles _ _ _ _ _ | exact only_writeSources _ _ | exact only_readBack _
    | exact only_pure _ | exact onlyA_pure _ | exact onlyA_throw _
    | exact onlyA_attempt (only_call trivial) | exact onlyA_lift (only_call trivial) | exact only_call trivial
    | refine onlyA_seq ?_ fun _ => ?_ | refine only_seq ?_ fun _ => ?_
    | refine onlyA_lift ?_ | split | dsimp only | (rename_i r; cases r)

end RegulaSpecification.Effects
