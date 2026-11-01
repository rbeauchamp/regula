/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Behaviour
import RegulaSpecification.Proofs.OwedExact

/-!
# A model of what a pass rests on

The premises of `plain_owed` and `full_owed` are statements about what Lean, Lake and the operating system answered. This module
shows that they are met by a run of the program the executable interprets, and that what they state of the operations does not
settle the conclusion by itself: for paths that meet `WitnessPaths` and an
environment with the floor (`EnvModel`), there is a run, whose proof takes the answers of the witness (`Proofs/Witness.lean`), that receives what `FullOwed` and `PlainOwed` state and exits with 0 (`full_model`,
`plain_model`); there is a run in which no answer failed that does not exit with 0, whose proof takes a project with a
`lakefile.lean` (`refused_model`). The hypotheses of the two models are what remains: `WitnessPaths` because `System.FilePath` depends on an
`opaque` constant, and for two facts about the pinned text and an empty log, and `EnvModel` because `Lean.Environment`'s constructor is private. `plain_exit_zero_owed` and
`full_exit_zero_owed` also apply to any run meeting the record with exit 0, under `OneAnswer` and, for
the full run's reading, `OneContext`. Those hypotheses are needed for the converse, not the owed-pass
implications. The witness runs meet the strengthened preparation relations through `run_meets`;
neither the models nor those relations assert consistency of a filesystem behind the responses.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax MessageLog)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Shell
open RegulaSpecification.Language
open RegulaSpecification.Loader

variable {α : Type}

/-- What an environment of the witness must be: each reading of it that those answers allow has `BuildAnswer.Floor`. `Lean.Environment`'s
constructor is private (`Lean/Environment.lean:213`, `:553`), so a proof here cannot build one with a claimed module. A real
one is what a finished build gives, and `plain_exit_zero_owed` and `full_exit_zero_owed` state that a run that exits with 0
read one with this floor, on one answer for each operation and, for the full reading, one context for each input. -/
structure EnvModel (w : WitnessPaths) (env : Lean.Environment) (p : Regula.Closed.Profile) : Prop where
  /-- Each reading has the floor. -/
  floor : ∀ a : BuildAnswer, a.env = env → a.toolchainDir = w.toolchainDir → a.rootDir = w.rootLib →
    a.places.map (·.1) = env.header.moduleNames.toList → (∀ x ∈ a.places, x.2 = w.olean) → a.Floor [`Good] p

theorem floor_of_read {w : WitnessPaths} {env : Lean.Environment} {p : Regula.Closed.Profile} (hm : EnvModel w env p)
    {q : Prog Unit Unit α} {T : List (Event Unit Unit)} (hT : T.Sublist (traceWith (answers w env) q))
    {a : BuildAnswer} {roots : List Name} (h : BuildAnswered T (witnessRoot w) a roots) :
    a.Floor roots p := by
  obtain ⟨modules, hd, rfl, hs, ht, hr, hn, hol⟩ := h
  have hmods := good_modules (DefaultModules.mono hT hd)
  subst hmods
  have henv : (Except.ok a.env : Except IO.Error Lean.Environment) = .ok env :=
    resp_eq (hT.subset (hs.subset (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))
  have he := Except.ok.inj henv
  exact hm.floor a he ht hr (by rw [hn, he]) fun x hx =>
    Except.ok.inj (resp_eq (hT.subset (hol x hx)) : (Except.ok _ : Except IO.Error FilePath) = .ok _)

/-- Those answers owe a pass of the full gate. -/
theorem fullOwed_answers {w : WitnessPaths} {env : Lean.Environment} {p : Regula.Closed.Profile} (hm : EnvModel w env p)
    (q : Prog Unit Unit α) : FullOwed (traceWith (answers w env) q) w.project p := by
  have hrulesT : (rulesPhase (traceWith (answers w env) q)).Sublist (traceWith (answers w env) q) := by
    have h := ((traceWith (answers w env) q).reverse.takeWhile_sublist (p := fun e => !e.isBuild)).reverse
    rwa [List.reverse_reverse] at h
  have hreadT : (readPhase (traceWith (answers w env) q)) <:+: (traceWith (answers w env) q) :=
    List.IsInfix.trans (List.takeWhile_prefix _).isInfix (List.drop_suffix _ _).isInfix
  have htree : ∀ {tree rest}, traceWith (answers w env) q = ⟨.createTempDir, .ok tree⟩ :: rest → tree = w.tree := by
    intro tree rest he
    have hmem : (⟨.createTempDir, .ok tree⟩ : Event Unit Unit) ∈ traceWith (answers w env) q := by simp [he]
    exact Except.ok.inj (resp_eq hmem : (Except.ok _ : Except IO.Error FilePath) = .ok _)
  have hreal : ∀ {T : List (Event Unit Unit)}, T.Sublist (traceWith (answers w env) q) → ∀ {a b : FilePath},
      (⟨.realPath a, .ok b⟩ : Event Unit Unit) ∈ T → b = a := fun hs _ _ h =>
    Except.ok.inj (resp_eq (hs.subset h) : (Except.ok _ : Except IO.Error FilePath) = .ok _)
  have hrootOf : ∀ {sysroot tree root}, TreeRoot sysroot tree (rulesPhase (traceWith (answers w env) q)) root →
      root = witnessRoot w := by
    rintro sysroot tree root ⟨real, log, -, h⟩
    have he : (Except.ok (some root, log) : Except String (Option (Root Unit) × List String)) =
        .ok (some (witnessRoot w), []) := resp_eq (hrulesT.subset h)
    have := Except.ok.inj he
    simp only [Prod.mk.injEq, Option.some.injEq] at this
    exact this.1
  have hbuild : ∀ {root}, ¬ BuildFailed (rulesPhase (traceWith (answers w env) q)) root := by
    intro root hf
    cases hf with
    | library _ _ h => cases resp_eq (hrulesT.subset h)
    | «import» _ h => cases resp_eq (hrulesT.subset h)
    | search _ _ _ h => cases resp_eq (hrulesT.subset h)
  refine ⟨fun e he => ?_, fun tree rest o he => ?_, fun tree rest s he _ hr => ?_, fun tree rest s he _ hr => ?_,
    fun tree rest s root a roots he _ hg hb => ?_⟩
  · cases resp_eq he
  · obtain rfl := htree he
    exact fun hr => no_reason w env q o (Reason.mono hreadT hr)
  · have hok : ∀ {a : FilePath} {b : List String} {c : FilePath} {r : Except IO.Error UInt32},
        (⟨.runLake a c b, r⟩ : Event Unit Unit) ∈ traceWith (answers w env) q → r = .ok 0 := fun h => resp_eq h
    cases hr with
    | build _ h1 h2 => exact h2 (hok h1)
    | replay _ _ h1 h2 => exact h2 (hok h1)
  · cases hr with
    | noTree h => cases resp_eq (hrulesT.subset h)
    | load _ h hf =>
      have hv := resp_eq (hrulesT.subset h)
      rcases hf with ⟨x, hx⟩ | ⟨x, hx⟩
      · rw [hx] at hv
        cases hv
      · rw [hx] at hv
        cases hv
    | build _ hf => exact hbuild hf
  · obtain rfl := hrootOf hg
    exact floor_of_read hm hrulesT hb

/-- The full gate on `dir` as a whole run, on the answers `f` after the two that select it. -/
theorem runs_full {L E : Type} (f : (o : Op L E) → Resp o) (dir : String) :
    Runs (Regula.Shell.run ["standard-logical"] : Prog L E UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, some dir⟩ ::
        traceWith f (runFull .standardLogical (FilePath.mk dir)))
      (valueWith f (runFull .standardLogical (FilePath.mk dir))) :=
  .ask _ _ _ (.ask _ _ _ (runs_with f _))

/-- The proof verdict as a whole run, on the answers `f` after the two that select it. -/
theorem runs_plain {L E : Type} (f : (o : Op L E) → Resp o) :
    Runs (Regula.Shell.run ["standard-logical"] : Prog L E UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, none⟩ :: traceWith f (runPlain .standardLogical))
      (valueWith f (runPlain .standardLogical)) :=
  .ask _ _ _ (.ask _ _ _ (runs_with f _))

/-- For paths that meet `WitnessPaths` and an environment with the floor, there is a run of the full gate, whose proof takes the answers of the witness, that
receives what `FullOwed` states, and exits with 0: a model of the premises of `full_owed`, in which they are met by a run of the
program that the executable interprets. -/
theorem full_model (w : WitnessPaths) (env : Lean.Environment) (hm : EnvModel w env .standardLogical) :
    ∃ rest, Runs (Regula.Shell.run ["standard-logical"] : Prog Unit Unit UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, some w.project.toString⟩ :: rest) 0 ∧
      FullOwed rest (FilePath.mk w.project.toString) .standardLogical := by
  have hr := runs_full (answers w env) w.project.toString
  generalize hc : valueWith (answers w env) _ = c at hr
  have howed : FullOwed (traceWith (answers w env) (runFull .standardLogical (FilePath.mk w.project.toString)))
      (FilePath.mk w.project.toString) .standardLogical :=
    fullOwed_answers hm _
  have := (run_full_owed (p := .standardLogical) run_meets (by rfl) hr howed).1
  subst this
  exact ⟨_, hr, howed⟩

/-- A project with a `lakefile.lean`: every operation that the run asks succeeds, and the run does not pass, on these answers. So
that each operation succeeded does not by itself settle that a run passes: `FullOwed` also asks what the project holds. -/
def answersRefused (w : WitnessPaths) (env : Lean.Environment) (m : IO.FS.Metadata) : (o : Op Unit Unit) → Resp o
  | .symlinkMetadata _ => .ok m
  | o => answers w env o

/-- Every answer of `answersRefused` is a success. -/
theorem answersRefused_healthy (w : WitnessPaths) (env : Lean.Environment) (m : IO.FS.Metadata) (o : Op Unit Unit) :
    ¬ Event.failed (⟨o, answersRefused w env m o⟩ : Event Unit Unit) := by
  cases o <;> first
    | exact id
    | (rintro ⟨x, hx⟩; cases hx; done)
    | (rintro ⟨x, hx, -⟩; cases hx; done)
    | (rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> cases hx; done)
    | exact fun hn => by cases hn
    | exact fun hn => hn rfl

/-- There is a run of the full gate that receives no failed answer, and does not exit with 0. -/
theorem refused_model (w : WitnessPaths) (env : Lean.Environment) (m : IO.FS.Metadata) :
    ∃ rest c, Runs (Regula.Shell.run ["standard-logical"] : Prog Unit Unit UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, some w.project.toString⟩ :: rest) c ∧
      (∀ e ∈ rest, ¬ e.failed) ∧ c ≠ 0 := by
  have hr := runs_full (answersRefused w env m) w.project.toString
  refine ⟨_, _, hr, fun e he => ?_, fun h0 => ?_⟩
  · have := traceWith_answers he
    rw [this]
    exact answersRefused_healthy w env m e.op
  · rw [h0] at hr
    have hm := run_meets _ _ _ hr
    have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
    simp only [hsp] at hm
    obtain ⟨v, rest', he, hrun, -⟩ := hm
    cases he
    obtain ⟨v', r', rest'', he', hf⟩ := hrun rfl
    cases he'
    simp only at hf
    rcases hf with ⟨e, rest, -, hc, -⟩ | ⟨tree, tRead, tGate, r, last, ht, -, -, o, report, hdec, -, hn, -, hc, -⟩
    · exact absurd hc (by decide)
    · have hrep : report = .full .pass := (Report.exitCode_eq_zero_iff report).mp hc.symm
      subst hrep
      cases o with
      | refused => cases (hn (by simp)).2
      | proofOnly => cases (hn (by simp)).2
      | incomplete => cases (hn (by simp)).2
      | admitted =>
        obtain ⟨r', -, -, hev, -⟩ := hdec.1 rfl
        obtain ⟨_, _, _, _, _, _, ⟨e, habs, -⟩, -⟩ := hev.places
        have hin : ∀ {x : Event Unit Unit}, x ∈ tRead → x ∈ traceWith (answersRefused w env m)
            (runFull .standardLogical (FilePath.mk w.project.toString)) := fun hx => by
          rw [ht]
          simp [hx]
        cases resp_eq (hin habs)

/-- The answers of one function of the operation are one answer for each operation. So `OneAnswer` holds of
each run on such answers. -/
theorem oneAnswer_traceWith {L E : Type} (f : (o : Op L E) → Resp o) (p : Prog L E α) : OneAnswer (traceWith f p) := by
  intro e he e' he' _ hop
  obtain ⟨o, r⟩ := e
  obtain ⟨o', r'⟩ := e'
  simp only at hop
  subst hop
  have h1 := resp_eq he
  have h2 := resp_eq he'
  subst h1 h2
  rfl

/-- Those answers owe a pass of the proof verdict. -/
theorem plainOwed_answers {w : WitnessPaths} {env : Lean.Environment} {p : Regula.Closed.Profile} (hm : EnvModel w env p)
    (q : Prog Unit Unit α) : PlainOwed (traceWith (answers w env) q) p := by
  have hroot : ∀ {root}, PlainRoot (traceWith (answers w env) q) root → root = witnessRoot w := by
    rintro root ⟨_, _, log, _, -, h, -⟩
    have he : (Except.ok (some root, log) : Except String (Option (Root Unit) × List String)) =
        .ok (some (witnessRoot w), []) := resp_eq h
    have := Except.ok.inj he
    simp only [Prod.mk.injEq, Option.some.injEq] at this
    exact this.1
  refine ⟨fun hr => ?_, fun root a roots hg hb => ?_⟩
  · cases hr with
    | noSysroot h => cases resp_eq h
    | noDirectory h => cases resp_eq h
    | load _ _ h hf =>
      have hv := resp_eq h
      rcases hf with ⟨x, hx⟩ | ⟨x, hx⟩
      · rw [hx] at hv
        cases hv
      · rw [hx] at hv
        cases hv
    | noSearchPath h => cases resp_eq h
    | @elsewhere s d root log lp _ _ h1 h3 hn =>
      have he : (Except.ok (some root, log) : Except String (Option (Root Unit) × List String)) =
          .ok (some (witnessRoot w), []) := resp_eq h1
      have hx := Except.ok.inj he
      simp only [Prod.mk.injEq, Option.some.injEq] at hx
      obtain ⟨rfl, -⟩ := hx
      exact hn ⟨_, rfl⟩
    | build _ hf =>
      cases hf with
      | library _ _ h => cases resp_eq h
      | «import» _ h => cases resp_eq h
      | search _ _ _ h => cases resp_eq h
  · obtain rfl := hroot hg
    exact floor_of_read hm (List.Sublist.refl _) hb

/-- The same for a run of the proof verdict. -/
theorem plain_model (w : WitnessPaths) (env : Lean.Environment) (hm : EnvModel w env .standardLogical) :
    ∃ rest, Runs (Regula.Shell.run ["standard-logical"] : Prog Unit Unit UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, none⟩ :: rest) 0 ∧
      PlainOwed (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) .standardLogical := by
  have hr := runs_plain (answers w env)
  generalize hc : valueWith (answers w env) _ = c at hr
  have howed := plainOwed_answers hm (.ask .leanVersion fun _ => runPlain .standardLogical : Prog Unit Unit UInt32)
  have := (run_plain_owed (p := .standardLogical) run_meets (by rfl) hr howed).1
  subst this
  exact ⟨_, hr, howed⟩


/-! ## Exit 0 exactly when a pass is owed -/

/-- Exit 0 from a run of the proof verdict of the program that the executable interprets holds exactly when it received what
`PlainOwed` states, on one answer for each operation. From `PlainOwed` to exit 0 needs no such hypothesis (`plain_owed`). -/
theorem run_plain_exit_zero_iff {L E : Type} {text : String} {p : Regula.Closed.Profile}
    (hp : Regula.Closed.Profile.ofSpelling? text = some p) {t : List (Event L E)} {c : UInt32}
    (h : Runs (Regula.Shell.run [text] : Prog L E UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, none⟩ :: t) c)
    (hone : OneAnswer (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: t : List (Event L E))) :
    c = 0 ↔ PlainOwed (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: t) p := by
  have hm := run_meets _ _ _ h
  simp only [hp] at hm
  obtain ⟨v, rest', he, hrun, -⟩ := hm
  cases he
  obtain ⟨v', r, rest'', he', hr⟩ := hrun rfl
  cases he'
  exact ⟨fun h0 => plain_exit_zero_owed (h0 ▸ hr) hone, fun howed => (plain_owed hr howed).1⟩

/-- The same of a run of the full gate, on one answer for each operation of its reading and of its load of the result, and one
context for each input. From `FullOwed` to exit 0 needs no such hypothesis (`full_owed`). -/
theorem run_full_exit_zero_iff {L E : Type} {text dir : String} {p : Regula.Closed.Profile}
    (hp : Regula.Closed.Profile.ofSpelling? text = some p) {t : List (Event L E)} {c : UInt32}
    (h : Runs (Regula.Shell.run [text] : Prog L E UInt32)
      (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: ⟨.getEnv fullVariable, some dir⟩ :: t) c)
    (h1 : OneAnswer (readPhase t)) (h2 : OneContext (readPhase t)) (h3 : OneAnswer (rulesPhase t)) :
    c = 0 ↔ FullOwed t (FilePath.mk dir) p := by
  have hm := run_meets _ _ _ h
  simp only [hp] at hm
  obtain ⟨v, rest', he, hrun, -⟩ := hm
  cases he
  obtain ⟨v', r, rest'', he', hf⟩ := hrun rfl
  cases he'
  exact ⟨fun h0 => full_exit_zero_owed (h0 ▸ hf) h1 h2 h3, fun howed => (full_owed hf howed).1⟩

/-! ## A program that refuses on what does not justify it -/

/-- A program that asks `LEAN_SYSROOT`, ignores the answer, and says that the proof verdict is incomplete. -/
def misjudge {L E : Type} (_ : List String) : Prog L E UInt32 :=
  .ask .leanVersion fun _ =>
    .ask (.getEnv Regula.Shell.fullVariable) fun _ =>
      .ask (.getEnv "LEAN_SYSROOT") fun _ =>
        .ask (.println (Regula.Closed.Verdict.proofLine .incomplete)) fun _ => .done 2

/-- It fails the record: it says incomplete with only `LEAN_SYSROOT` asked, and that answered. -/
theorem misjudge_fails {L E : Type} : ¬ RunMeets (misjudge : List String → Prog L E UInt32) := by
  intro hw
  have hr : Runs (misjudge ["standard-logical"] : Prog L E UInt32)
      [⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv Regula.Shell.fullVariable, none⟩, ⟨.getEnv "LEAN_SYSROOT", some ""⟩,
        ⟨.println (Regula.Closed.Verdict.proofLine .incomplete), .ok ()⟩] 2 :=
    .ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.done _))))
  have hm := hw _ _ _ hr
  have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
  simp only [hsp] at hm
  obtain ⟨v, rest, he, hrun, -⟩ := hm
  cases he
  obtain ⟨v', r, rest, he', hf⟩ := hrun rfl
  cases he'
  obtain ⟨result, subject, hl, -⟩ := hf
  have hno : ∀ {o : Op L E} {r : Resp o},
      (⟨o, r⟩ : Event L E) ∈ ([⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv "LEAN_SYSROOT", some ""⟩,
        ⟨.println (Regula.Closed.Verdict.proofLine .incomplete), .ok ()⟩] : List (Event L E)) →
      (o = .leanVersion ∨ o = .getEnv "LEAN_SYSROOT" ∨ o = .println (Regula.Closed.Verdict.proofLine .incomplete)) := by
    intro o r hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm
    · exact .inl (congrArg Event.op hm)
    · exact .inr (.inl (congrArg Event.op hm))
    · exact .inr (.inr (congrArg Event.op hm))
  have hplain : ∀ root, ¬ PlainRoot ([⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv "LEAN_SYSROOT", some ""⟩,
      ⟨.println (Regula.Closed.Verdict.proofLine .incomplete), .ok ()⟩] : List (Event L E)) root := by
    rintro root ⟨s, d, l, lp, -, hload, -⟩
    rcases hno hload with h | h | h <;> cases h
  rcases hl with ⟨root, f, roots, hg, -⟩ | ⟨hw', -⟩
  · exact hplain root hg
  · cases hw' with
    | noSysroot h =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h <;> cases h
    | noDirectory h => rcases hno h with h | h | h <;> cases h
    | load _ _ h _ => rcases hno h with h | h | h <;> cases h
    | noSearchPath h =>
      rcases hno h with h | h | h <;> first | cases h | (injection h with h; exact absurd h (by decide))
    | elsewhere _ _ h => rcases hno h with h | h | h <;> cases h
    | build h _ => exact hplain _ h

/-- A trace of one event, a failed real path of a path other than the project and the tree, holds no reason. -/
theorem unrelated_read_no_reason {L E : Type} {u dir treeDir : FilePath} {e : IO.Error} {o : Outcome}
    (h1 : u ≠ dir) (h2 : u ≠ treeDir) :
    ¬ Reason ([⟨.realPath u, .error e⟩] : List (Event L E)) dir treeDir o := by
  intro hr
  have hne {a : Op L E} {b : Resp a} (hm : (⟨a, b⟩ : Event L E) ∈ ([⟨.realPath u, .error e⟩] : List (Event L E))) :
      a = .realPath u := congrArg Event.op (List.mem_singleton.mp hm)
  have hok {p q : FilePath} (hm : (⟨.realPath p, .ok q⟩ : Event L E) ∈ ([⟨.realPath u, .error e⟩] : List (Event L E))) :
      False := by
    have h := List.mem_singleton.mp hm
    injection h with h4 h5
    injection h4 with h6
    subst h6
    first | cases h5 | cases eq_of_heq h5
  have hsc {a b c d : FilePath} {r : Root L} {q : List (Name × FilePath)} :
      ¬ Scene ([⟨.realPath u, .error e⟩] : List (Event L E)) a b c d r q := fun x => hok x.project_real
  have htl {a b c : FilePath} {r : Root L} : ¬ TreeLoaded ([⟨.realPath u, .error e⟩] : List (Event L E)) a b c r :=
    fun x => hok x.1
  have htm {a : FilePath} {x : Lake.Toml.Table} : ¬ TomlRead ([⟨.realPath u, .error e⟩] : List (Event L E)) a x := by
    rintro ⟨_, _, h, -⟩
    exact hok h
  cases hr with
  | failed he hn _ =>
    rw [List.mem_singleton] at he
    subst he
    cases hn with
    | project => exact h1 rfl
    | tree => exact h2 rfl
    | tomlReal h => exact hok h
    | sourceReal h => exact hsc h
  | load hp _ => cases hne hp.event
  | toolchain h => exact hok h
  | toolchainFailed h => exact hok h
  | toolchainNotExact h => exact hok h
  | toolchainNoReal h => exact hok h
  | tomlNotExact h => exact hok h
  | notApart h => exact hok h
  | configNotInTree h => exact hok h
  | moduleNotInTree h => exact hsc h
  | moduleNotExact h => exact hsc h
  | leanConfig h => exact hok h
  | configShadowed h => exact hok h
  | key h => exact htm h
  | deep h => exact htm h
  | deepDependency h => exact htm h
  | dependency h => exact htm h
  | openDir h => exact htl h
  | openGlob h => exact htl h
  | noClaim h => exact hsc h
  | targetName h => exact htl h
  | twoFiles h => exact hsc h
  | twoRoots h => exact hsc h
  | treeDiffers h => exact hsc h
  | twoTexts h => exact hsc h
  | moduleName h => exact hsc h
  | importedRoot h => exact hsc h
  | tooMany h => exact hsc h
  | mathlib h => exact hsc h
  | file h => exact hsc h

end RegulaSpecification.Effects
