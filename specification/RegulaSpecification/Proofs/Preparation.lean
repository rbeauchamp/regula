/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord

/-!
# Consequences of ordered preparation

These consequences read the contract alone. The exact copy segments determine their first act;
`ReadingPreparation.first_directory` makes a directory that is the first tree act the TOML copy's parent, and
`manufacturedCopy_fails` excludes the reported trace for every path, text, error, profile and exit code.
`BuildProtocol.commands`, `BuildAndRules.no_mutation` and `FullRun.after_removal_saying` constrain the
later phases. The proofs in `PreparationReader`, `PreparationLoad` and `Shell` establish the ordered
relations for the actual reader and loaders, composed in `run_meets`, for every response. No result
here assumes consistent filesystem responses or describes effects inside trusted Lean/Lake calls.
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
    ⟨tree, tRead, tGate, response, last, ht, -, hlast, o, report, -, -, hn, ha, -, -, -, -, hkeep, -⟩
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

/-- The requests that act on the tree, retaining order and responses. -/
def treeActs (t : List (Event L E)) : List (Event L E) := t.filter fun e => e.acted?.isSome

theorem treeActs_append (a b : List (Event L E)) : treeActs (a ++ b) = treeActs a ++ treeActs b :=
  List.filter_append a b

theorem Quiet.treeActs_nil {t : List (Event L E)} (h : Quiet t) : treeActs t = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro e he
  have hq := h e he
  obtain ⟨op, response⟩ := e
  cases op <;> simp_all [QuietOp, Event.acted?]

/-- The first act of a copy is its own parent creation, or its write when it has no parent. -/
def CopyHead (path : FilePath) (text : String) (e : Event L E) : Prop :=
  (∃ parent response, path.parent = some parent ∧ e = ⟨.createDirAll parent, response⟩) ∨
    (path.parent = none ∧ ∃ response, e = ⟨.writeFile path text, response⟩)

theorem CopyStep.first {tree path : FilePath} {text : String} {t : List (Event L E)} {complete : Bool}
    (h : CopyStep tree path text t complete) :
    (complete = false ∧ treeActs t = []) ∨ ∃ e rest, treeActs t = e :: rest ∧ CopyHead path text e := by
  cases h with
  | outside _ => exact .inl ⟨rfl, rfl⟩
  | noParent _ hp => exact .inr ⟨_, [], rfl, .inr ⟨hp, _, rfl⟩⟩
  | parentFailed _ hp _ => exact .inr ⟨_, [], rfl, .inl ⟨_, _, hp, rfl⟩⟩
  | parentWritten _ hp _ => exact .inr ⟨_, [_], rfl, .inl ⟨_, _, hp, rfl⟩⟩

/-- No later copy can supply the first act: the first configuration step either makes it or stops all
acts. This rules out a preparation directory chosen independently of that step's parent. -/
theorem ConfigCopies.first {sysroot : String} {project tree path : FilePath} {text : String} {copies}
    {prior t : List (Event L E)} (h : ConfigCopies sysroot project tree ((path, text) :: copies) prior t) :
    treeActs t = [] ∨ ∃ e rest, treeActs t = e :: rest ∧ CopyHead path text e := by
  cases h with
  | stopped hq => exact .inl hq.treeActs_nil
  | failed hpre hc hrest =>
    rename_i before step rest
    have he : treeActs (before ++ step ++ rest) = treeActs step := by
      rw [treeActs_append, treeActs_append]
      rw [hpre.treeActs_nil, hrest.treeActs_nil]
      simp
    rcases hc.first with ⟨-, hn⟩ | ⟨e, rest, ht, hh⟩
    · exact .inl (he.trans hn)
    · exact .inr ⟨e, rest, he.trans ht, hh⟩
  | next hpre hc hrest =>
    rename_i before step after
    rcases hc.first with ⟨hf, -⟩ | ⟨e, rest, ht, hh⟩
    · cases hf
    · refine .inr ⟨e, rest ++ treeActs after, ?_, hh⟩
      rw [treeActs_append, treeActs_append]
      rw [hpre.treeActs_nil, ht]
      rfl

/-- When the first tree act of a prepared reading creates a directory, that directory is the parent
of its first TOML copy, irrespective of the creation's success or failure. -/
theorem ReadingPreparation.first_directory {t : List (Event L E)} {dir treeDir path : FilePath}
    {response : Except IO.Error Unit} {rest : List (Event L E)}
    (h : ReadingPreparation t dir treeDir) (hf : treeActs t = ⟨.createDirAll path, response⟩ :: rest) :
    ∃ tree, (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧
      (tree / "lakefile.toml").parent = some path := by
  rcases h with hq | ⟨project, tree, sysroot, text, before, after, rfl, hq, -, ht, -, -, hc⟩
  · rw [hq.treeActs_nil] at hf; cases hf
  · have he : treeActs (before ++ after) = treeActs after := by
      rw [treeActs_append]
      rw [hq.treeActs_nil]
      rfl
    rw [he] at hf
    rcases hc.first with hn | ⟨e, tail, he, hh⟩
    · rw [hn] at hf; cases hf
    · have hx := (List.cons.inj (he.symm.trans hf)).1
      subst e
      rcases hh with ⟨parent, r, hp, he⟩ | ⟨-, r, he⟩
      · have hop := congrArg Event.op he
        cases hop
        exact ⟨tree, List.mem_append_left _ ht, hp⟩
      · cases congrArg Event.op he

/-- A reading without any toolchain response can only observe and report. -/
theorem ReadingPreparation.no_sysroot {t : List (Event L E)} {dir tree : FilePath}
    (h : ReadingPreparation t dir tree) (hn : ∀ s, ¬ SysrootIs t s) : Quiet t := by
  rcases h with h | ⟨project, real, sysroot, text, before, after, rfl, -, -, -, hs, -⟩
  · exact h
  · exact (hn sysroot (List.mem_append_left _ hs)).elim

/-- With no received toolchain, a full run cannot create a copy directory or write a file. This is a
property of every subject of the record, not an assumption that its responses are consistent. -/
theorem FullRun.no_sysroot_no_copy {t : List (Event L E)} {dir : FilePath}
    {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c) (hn : ∀ s, ¬ SysrootIs t s) :
    ∀ e ∈ t, (match e.op with | .createDirAll _ | .writeFile .. => False | _ => True) := by
  have quiet {u : List (Event L E)} (hq : Quiet u) :
      ∀ e ∈ u, (match e.op with | .createDirAll _ | .writeFile .. => False | _ => True) := by
    intro e he
    have hp := hq e he
    obtain ⟨op, response⟩ := e
    cases op <;> first | trivial | exact hp.elim
  have saying {u : List (Event L E)} (hs : ∀ e ∈ u, e.isOnlySaying = true) : Quiet u := by
    intro e he
    have hp := hs e he
    obtain ⟨op, response⟩ := e
    cases op <;> first | trivial | cases hp
  rcases h with ⟨error, rest, rfl, -, -, hs⟩ |
    ⟨tree, tRead, tGate, response, last, rfl, -, hs, o, report, -, -, hstop, hgate, -, -, -, -, -, hp⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · exact quiet (saying hs) e he
  · have hr : ∀ s, ¬ SysrootIs tRead s := by
      intro s h
      exact hn s (by
        simp only [SysrootIs, List.cons_append, List.mem_cons, List.mem_append]
        exact .inr (.inl (.inl h)))
    have hq := hp.no_sysroot hr
    have hg : tGate = [] := by
      by_cases ho : o = .admitted
      · obtain ⟨sysroot, _, _, hsys, -⟩ := hgate ho
        exact (hr sysroot hsys).elim
      · exact (hstop ho).1
    subst tGate
    intro e he
    simp only [List.append_nil, List.cons_append, List.mem_cons, List.mem_append] at he
    rcases he with rfl | (he | rfl | he)
    · trivial
    · exact quiet hq e he
    · trivial
    · exact quiet (saying hs) e he

/-- The reported manufactured refusal: read the requested TOML, create a directory at its destination,
fail the write, remove the tree, and report incomplete. -/
def manufacturedCopyTrace (dir tree : FilePath) (text : String) (error : IO.Error) : List (Event L E) :=
  [⟨.createTempDir, .ok tree⟩, ⟨.realPath dir, .ok dir⟩, ⟨.realPath tree, .ok tree⟩,
   ⟨.readFile (dir / "lakefile.toml"), .ok text⟩, ⟨.createDirAll (tree / "lakefile.toml"), .ok ()⟩,
   ⟨.writeFile (tree / "lakefile.toml") text, .error error⟩, ⟨.removeDirAll tree, .ok ()⟩,
   ⟨.println Regula.Language.Report.incomplete.label, .ok ()⟩]

/-- The previously admitted trace fails the strengthened record, for every path, text and error.
`ReadingPreparation.first_directory` separately states the copy-order invariant over all traces. -/
theorem manufacturedCopy_fails (dir tree : FilePath) (text : String) (error : IO.Error)
    (p : Regula.Closed.Profile) (c : UInt32) :
    ¬ FullRun (manufacturedCopyTrace (L := L) (E := E) dir tree text error) dir p c := by
  intro h
  have hn : ∀ s, ¬ SysrootIs (manufacturedCopyTrace (L := L) (E := E) dir tree text error) s := by
    intro s hs
    simp only [SysrootIs, manufacturedCopyTrace, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with h | h | h | h | h | h | h | h <;> cases congrArg Event.op h
  exact h.no_sysroot_no_copy hn ⟨.createDirAll (tree / "lakefile.toml"), .ok ()⟩
    (by simp [manufacturedCopyTrace])

end RegulaSpecification.Effects
