/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord

/-!
# Preservation through the build and reload phases

These consequences read the contract alone. `buildAndReplay_protocol` and `rules_reload` in
`Proofs.Shell` establish its additional fields for the actual definitions, on every response.
This does not establish the reader's preparation or the effects internal to trusted Lake calls.
-/

namespace RegulaSpecification.Effects

open System (FilePath)
open Regula.Effect

variable {L E : Type}

/-- Only the specified command and reporting occur in a command segment. -/
theorem LakeInvocation.operations {program tree : FilePath} {args : List String} {response}
    {t : List (Event L E)} (h : LakeInvocation program tree args response t) :
    ∀ e ∈ t, e.isOnlySaying = true ∨ e.op = .runLake program tree args := by
  obtain ⟨pre, post, rfl, hp, hq⟩ := h
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact .inl (hp e he)
  · rcases List.mem_cons.mp he with rfl | he
    · exact .inr rfl
    · exact .inl (hq e he)

/-- All requests in the build phase identify Lake, invoke its specified commands or report. -/
theorem BuildProtocol.operations {sysroot : String} {tree : FilePath} {t : List (Event L E)}
    (h : BuildProtocol sysroot tree t) :
    ∃ program, ∀ e ∈ t, e.isOnlySaying = true ∨ e.op = .lakeInstall sysroot ∨
      e.op = .runLake program tree ["build", "--wfail"] ∨ e.op = .runLake program tree replayArguments := by
  obtain ⟨program, lakeLib, first, rest, response, rfl, hf, hr⟩ := h
  refine ⟨program, fun e he => ?_⟩
  rcases List.mem_cons.mp he with rfl | he
  · exact .inr (.inl rfl)
  · rcases List.mem_append.mp he with he | he
    · rcases hf.operations e he with hs | hl
      · exact .inl hs
      · exact .inr (.inr (.inl hl))
    · rcases hr with ⟨-, rfl⟩ | ⟨-, replay, hr⟩
      · cases he
      · rcases hr.operations e he with hs | hl
        · exact .inl hs
        · exact .inr (.inr (.inr hl))

/-- The commands requested by a trace, in their actual order. -/
def lakeCommands (t : List (Event L E)) : List (FilePath × FilePath × List String) :=
  t.filterMap fun e => match e.op with
    | .runLake program tree args => some (program, tree, args)
    | _ => none

/-- A command segment requests exactly one command; reporting cannot conceal another. -/
theorem LakeInvocation.commands {program tree : FilePath} {args : List String} {response}
    {t : List (Event L E)} (h : LakeInvocation program tree args response t) :
    lakeCommands t = [(program, tree, args)] := by
  obtain ⟨pre, post, rfl, hp, hq⟩ := h
  have quiet {u : List (Event L E)} (hu : ∀ e ∈ u, e.isOnlySaying = true) : lakeCommands u = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hs := hu e he
    obtain ⟨o, r⟩ := e
    cases o <;> first | rfl | cases hs
  simp only [lakeCommands, List.filterMap_append, List.filterMap_cons]
  change lakeCommands pre ++ (program, tree, args) :: lakeCommands post = _
  rw [quiet hp, quiet hq]
  rfl

/-- A build phase has exactly a build, or that build followed by one replay. -/
theorem BuildProtocol.commands {sysroot : String} {tree : FilePath} {t : List (Event L E)}
    (h : BuildProtocol sysroot tree t) :
    ∃ program, lakeCommands t = [(program, tree, ["build", "--wfail"])] ∨
      lakeCommands t = [(program, tree, ["build", "--wfail"]), (program, tree, replayArguments)] := by
  obtain ⟨program, lakeLib, first, rest, response, rfl, hf, hr⟩ := h
  refine ⟨program, ?_⟩
  have he : lakeCommands (⟨.lakeInstall sysroot, (program, lakeLib)⟩ :: (first ++ rest)) =
      lakeCommands first ++ lakeCommands rest := by simp [lakeCommands]
  rw [he, hf.commands]
  rcases hr with ⟨-, rfl⟩ | ⟨-, replay, hr⟩
  · exact .inl rfl
  · rw [hr.commands]
    exact .inr rfl

/-- No explicit write, directory creation, allocation or removal belongs to either phase. Effects
inside trusted Lean/Lake calls are not events of this trace. -/
theorem BuildAndRules.no_mutation {sysroot : String} {tree : FilePath} {tBuild tRules : List (Event L E)}
    {p : Regula.Closed.Profile} {report : Regula.Language.Report}
    (h : BuildAndRules sysroot tBuild tRules tree p report) :
    ∀ e ∈ tBuild ++ tRules, (match e.op with
      | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ => False
      | _ => True) := by
  obtain ⟨program, hp⟩ := h.1.operations
  intro e he
  rcases List.mem_append.mp he with he | he
  · rcases hp e he with hs | hi | hb | hr
    · obtain ⟨o, r⟩ := e
      cases o <;> first | trivial | cases hs
    · rw [hi]; trivial
    · rw [hb]; trivial
    · rw [hr]; trivial
  · have hr := h.2.1 e he
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | exact hr.elim

/-- In every full run, either allocation failed before any other operation, or the only removal is the
terminal cleanup after the reader, build and reload. This includes nonzero and failed removals. -/
theorem FullRun.removal_order {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) :
    (∀ e ∈ t, NotRemoving e.op) ∨
      ∃ tree response pre post, t = pre ++ ⟨.removeDirAll tree, response⟩ :: post ∧
        (∀ e ∈ pre, NotRemoving e.op) ∧ (∀ e ∈ post, e.isOnlySaying = true) := by
  have saying {e : Event L E} (hs : e.isOnlySaying = true) : NotRemoving e.op := by
    obtain ⟨o, r⟩ := e
    cases o <;> first | trivial | cases hs
  rcases h with ⟨error, rest, rfl, -, -, hs⟩ |
    ⟨tree, tRead, tGate, response, last, ht, -, hlast, o, report, -, -, hn, ha, -, -, -, -, hkeep⟩
  · left
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact saying (hs e he)
  · right
    refine ⟨tree, response, ⟨.createTempDir, .ok tree⟩ :: (tRead ++ tGate), last,
      by simpa using ht, ?_, hlast⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · rcases List.mem_append.mp he with he | he
      · exact hkeep e he
      · by_cases ho : o = .admitted
        · obtain ⟨sysroot, tBuild, tRules, -, hgate, hb⟩ := ha ho
          rw [hgate] at he
          have hm := hb.no_mutation e he
          obtain ⟨op, r⟩ := e
          cases op <;> first | trivial | exact hm.elim
        · rw [(hn ho).1] at he
          cases he

/-- Every operation following a removal only reports. The statement quantifies over all paths,
responses and trace positions, so it also excludes reload and import after removal. -/
theorem FullRun.after_removal_saying {t : List (Event L E)} {dir : FilePath}
    {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) :
    ∀ pre path response rest, t = pre ++ ⟨.removeDirAll path, response⟩ :: rest →
      ∀ e ∈ rest, e.isOnlySaying = true := by
  intro pre path response rest ht
  rcases h.removal_order with hn | ⟨tree, r, before, after, he, hbefore, hafter⟩
  · have hm : (⟨.removeDirAll path, response⟩ : Event L E) ∈ t := by simp [ht]
    exact (hn _ hm).elim
  · have compare := List.append_eq_append_iff.mp (ht.symm.trans he)
    rcases compare with ⟨middle, hpre, htail⟩ | ⟨middle, hpre, htail⟩
    · cases middle with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at htail
        rw [htail.2]
        exact hafter
      | cons x xs =>
        simp only [List.cons_append, List.cons.injEq] at htail
        have hm : (⟨.removeDirAll path, response⟩ : Event L E) ∈ before := by
          rw [hpre]
          simp [← htail.1]
        exact (hbefore _ hm).elim
    · cases middle with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at htail
        rw [← htail.2]
        exact hafter
      | cons x xs =>
        simp only [List.cons_append, List.cons.injEq] at htail
        have hm : (⟨.removeDirAll path, response⟩ : Event L E) ∈ after := by
          rw [htail.2]
          simp
        have hs := hafter _ hm
        cases hs

/-- A removal cannot precede any later Lake command in a full run. -/
theorem FullRun.no_remove_before_command {t : List (Event L E)} {dir : FilePath}
    {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) :
    ∀ pre path response rest, t = pre ++ ⟨.removeDirAll path, response⟩ :: rest →
      ∀ e ∈ rest, e.isBuild = false := by
  intro pre path response rest ht e he
  have hs := h.after_removal_saying pre path response rest ht e he
  obtain ⟨op, r⟩ := e
  cases op <;> first | rfl | cases hs

end RegulaSpecification.Effects
