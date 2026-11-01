/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRecord
import RegulaSpecification.Proofs.Load

/-!
# A pass is owed

What the record of a run (`RegulaSpecification.Effects.programRecord`) requires of every program that meets it, by the
record alone. It reads no program, so it holds of each subject and not only of the one that runs.

`PlainOwed` and `FullOwed` state what it takes for a build to pass, over what the run received: no case of the closed set
of reasons holds, the build and its replay ended with 0, and the environment that Lean's import gave has `LoadFloor`.
`plain_owed` and `full_owed` state that a run on such responses gives the pass verdict and exit 0. So a run that refuses or
reports incomplete has a reason in that closed set, or the environment lacks that floor (`plain_refused_justified`,
`full_refused_justified`). No premise reads a branch of a program: each is about what a response holds.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language
open RegulaSpecification.Loader

variable {L E : Type}

/-- The prepared response is an event of the trace, after the successful configuration copies. -/
theorem PreparedLoad.event {t : List (Event L E)} {dir treeDir sysroot tree response}
    (h : PreparedLoad t dir treeDir sysroot tree response) :
    (⟨.loadRoot sysroot tree, response⟩ : Event L E) ∈ t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hi, _⟩ := h
  exact hi.subset (by simp)

/-- The general failure constructor cannot cite a load; a load requires `PreparedLoad`. -/
theorem needed_not_loadRoot {t : List (Event L E)} {dir treeDir sysroot tree} :
    ¬ Needed t dir treeDir (.loadRoot sysroot tree) := by
  intro h
  cases h

/-! ## The events of a phase of a run -/

/-- What a run of the full gate did after it made its tree and before it built or loaded anything. -/
def readPhase (t : List (Event L E)) : List (Event L E) :=
  (t.drop 1).takeWhile fun e => !e.isBuild && !e.isImportForRules

/-- What a run of the full gate did after its last Lake command. -/
def rulesPhase (t : List (Event L E)) : List (Event L E) :=
  (t.reverse.takeWhile fun e => !e.isBuild).reverse

theorem sublist_takeWhile_of_all {α : Type} {p : α → Bool} {a b : List α} (h : ∀ x ∈ a, p x = true) :
    a.Sublist ((a ++ b).takeWhile p) := by
  rw [List.takeWhile_append_of_pos h]
  exact List.sublist_append_left _ _

theorem readPhase_sublist {tRead rest : List (Event L E)} {x : Event L E}
    (h : ∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false) :
    tRead.Sublist (readPhase (x :: tRead ++ rest)) := by
  refine sublist_takeWhile_of_all (p := fun e : Event L E => !e.isBuild && !e.isImportForRules) fun e he => ?_
  obtain ⟨h1, h2⟩ := h e he
  simp [h1, h2]

/-- The reading is a contiguous prefix of its phase; extending the phase inserts no effects inside it. -/
theorem readPhase_infix {tRead rest : List (Event L E)} {x : Event L E}
    (h : ∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false) :
    tRead <:+: readPhase (x :: tRead ++ rest) := by
  have hall : ∀ e ∈ tRead, (!e.isBuild && !e.isImportForRules) = true := by
    intro e he
    obtain ⟨h1, h2⟩ := h e he
    simp [h1, h2]
  simpa [readPhase, List.takeWhile_append_of_pos hall] using
    (List.infix_append_left (l₁ := tRead)
      (l₂ := rest.takeWhile fun e => !e.isBuild && !e.isImportForRules))

theorem rulesPhase_sublist {pre tRules post : List (Event L E)} (h1 : ∀ e ∈ tRules, e.isBuild = false)
    (h2 : ∀ e ∈ post, e.isBuild = false) : tRules.Sublist (rulesPhase (pre ++ tRules ++ post)) := by
  have hall : ∀ e ∈ post.reverse ++ tRules.reverse, (!e.isBuild) = true := by
    intro e he
    simp only [List.mem_append, List.mem_reverse] at he
    rcases he with he | he
    · simp [h2 e he]
    · simp [h1 e he]
  have hrev : (pre ++ tRules ++ post).reverse = (post.reverse ++ tRules.reverse) ++ pre.reverse := by simp
  unfold rulesPhase
  rw [hrev, List.takeWhile_append_of_pos hall]
  have hs : tRules.reverse.Sublist
      (post.reverse ++ tRules.reverse ++ pre.reverse.takeWhile fun e => !e.isBuild) := by
    rw [List.append_assoc]
    exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  simp

/-! ## A larger trace -/

section Mono

variable {T T' : List (Event L E)} (hs : T.Sublist T')
include hs

theorem DefaultModules.mono {root : Root L} {targets modules}
    (h : DefaultModules T root targets modules) : DefaultModules T' root targets modules := by
  induction h with
  | nil => exact .nil
  | lib hl he _ ih => exact .lib hl (hs.subset he) ih
  | exe hl hx _ ih => exact .exe hl hx ih
  | other hl hx _ ih => exact .other hl hx ih

theorem HeldByToolchain.mono {root : Root L} {n} (h : HeldByToolchain T root n) : HeldByToolchain T' root n := by
  obtain ⟨o, r, d, dr, h1, h2, h3, h4⟩ := h
  exact ⟨o, r, d, dr, h1.trans hs, h2, hs.subset h3, h4⟩

omit hs in
theorem PreparedLoad.mono (hi : T <:+: T') {dir treeDir sysroot tree response}
    (h : PreparedLoad T dir treeDir sysroot tree response) : PreparedLoad T' dir treeDir sysroot tree response := by
  obtain ⟨project, text, toolchain, between, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨project, text, toolchain, between, hi.subset h1, hi.subset h2, hi.subset h3,
    hi.subset h4, hi.subset h5, h6, h7.trans hi, h8⟩

omit hs in
theorem TreeLoaded.mono (hi : T <:+: T') {dir treeDir tree : FilePath} {root : Root L}
    (h : TreeLoaded T dir treeDir tree root) : TreeLoaded T' dir treeDir tree root := by
  obtain ⟨h1, s, l, h2, h3, h4⟩ := h
  exact ⟨hi.subset h1, s, l, hi.subset h2, hi.subset h3, PreparedLoad.mono hi h4⟩

omit hs in
theorem Scene.mono (hi : T <:+: T') {dir treeDir project tree : FilePath} {root : Root L} {modules}
    (h : Scene T dir treeDir project tree root modules) : Scene T' dir treeDir project tree root modules :=
  ⟨hi.subset h.project_real, TreeLoaded.mono hi h.loaded, DefaultModules.mono hi.sublist h.default⟩

theorem SourceText.mono {project tree path : FilePath} {text} (h : SourceText T project tree path text) :
    SourceText T' project tree path text := by
  obtain ⟨r, h1, h2⟩ := h
  exact ⟨r, h1, hs.subset h2⟩

theorem HeaderOf.mono {project tree : FilePath} {root : Root L} {modules m imports}
    (h : HeaderOf T project tree root modules m imports) : HeaderOf T' project tree root modules m imports := by
  obtain ⟨p, x, a, b, c, h1, h2, h3⟩ := h
  exact ⟨p, x, a, b, c, h1, SourceText.mono hs h2, hs.subset h3⟩

theorem Named.mono {project tree : FilePath} {root : Root L} {modules m}
    (h : Named T project tree root modules m) : Named T' project tree root modules m := by
  induction h with
  | root hm => exact .root hm
  | imported _ hh hi ih => exact .imported ih (HeaderOf.mono hs hh) hi

theorem ReadAs.mono {project tree : FilePath} {f path imports mods}
    (h : ReadAs T project tree f path imports mods) : ReadAs T' project tree f path imports mods := by
  obtain ⟨rel, real, text, state, messages, final, env, commands, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨rel, real, text, state, messages, final, env, commands, h1, h2, h3, h4.trans hs, hs.subset h5, h6,
    h7.trans hs, h8⟩

omit hs in
theorem Needed.mono (hi : T <:+: T') {dir treeDir : FilePath} {o : Op L E}
    (h : Needed T dir treeDir o) : Needed T' dir treeDir o := by
  have m {e : Event L E} (he : e ∈ T) : e ∈ T' := hi.subset he
  cases h with
  | sysroot => exact .sysroot
  | searchPath => exact .searchPath
  | project => exact .project
  | tree => exact .tree
  | app => exact .app
  | appReal h => exact .appReal (m h)
  | leanConfig h => exact .leanConfig (m h)
  | tomlReal h => exact .tomlReal (m h)
  | tomlRead h => exact .tomlRead (m h)
  | tomlParse h1 h2 => exact .tomlParse (m h1) (m h2)
  | copyParent h1 h2 h3 => exact .copyParent (m h1) h2 h3
  | copyToml h1 h2 h3 => exact .copyToml (m h1) (m h2) (m h3)
  | copyToolchain h => exact .copyToolchain (m h)
  | library h1 h2 h3 => exact .library (TreeLoaded.mono hi h1) h2 h3
  | toolchainDir h1 h2 => exact .toolchainDir (TreeLoaded.mono hi h1) h2
  | search h1 h2 h3 h4 => exact .search (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 h4
  | oleanReal h1 h2 h3 h4 h5 => exact .oleanReal (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 h4 (m h5)
  | sourceReal h1 h2 h3 h4 => exact .sourceReal (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 h4
  | sourceRead h1 h2 h3 h4 => exact .sourceRead (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 h4
  | sourceParent h1 h2 h3 h4 => exact .sourceParent (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 h4
  | sourceWrite h1 h2 h3 h4 => exact .sourceWrite (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 (SourceText.mono hi.sublist h4)
  | sourceHeader h1 h2 h3 h4 => exact .sourceHeader (Scene.mono hi h1) (Named.mono hi.sublist h2) h3 (SourceText.mono hi.sublist h4)
  | parser h1 h2 =>
    exact .parser (Scene.mono hi h1) fun n hn =>
      ⟨Named.mono hi.sublist (h2 n hn).1, HeldByToolchain.mono hi.sublist (h2 n hn).2⟩

theorem TomlRead.mono {dir : FilePath} {table} (h : TomlRead T dir table) : TomlRead T' dir table := by
  obtain ⟨p, x, h1, h2, h3⟩ := h
  exact ⟨p, x, hs.subset h1, hs.subset h2, hs.subset h3⟩

omit hs in
theorem Reason.mono (hi : T <:+: T') {dir treeDir : FilePath} {o}
    (h : Reason T dir treeDir o) : Reason T' dir treeDir o := by
  have hs := hi.sublist
  have m {e : Event L E} (he : e ∈ T) : e ∈ T' := hi.subset he
  have sc {a b c d r q} := Scene.mono (L := L) (E := E) (dir := a) (treeDir := b) (project := c) (tree := d) (root := r)
    (modules := q) hi
  have nm {c d r q x} := Named.mono (L := L) (E := E) (project := c) (tree := d) (root := r) (modules := q) (m := x) hs
  have hd {c d r q x y} := HeaderOf.mono (L := L) (E := E) (project := c) (tree := d) (root := r) (modules := q)
    (m := x) (imports := y) hs
  have tl {d a b r} := TreeLoaded.mono (L := L) (E := E) (dir := d) (treeDir := a) (tree := b) (root := r) hi
  cases h with
  | failed h1 h2 h3 => exact .failed (m h1) (Needed.mono hi h2) h3
  | load h1 h2 => exact .load (PreparedLoad.mono hi h1) h2
  | toolchain h1 h2 h3 => exact .toolchain (m h1) (m h2) h3
  | toolchainFailed h1 h2 => exact .toolchainFailed (m h1) (m h2)
  | toolchainNotExact h1 h2 h3 => exact .toolchainNotExact (m h1) (m h2) h3
  | toolchainNoReal h1 h2 => exact .toolchainNoReal (m h1) (m h2)
  | started h1 h2 h3 h4 h5 h6 h7 => exact .started (m h1) (m h2) (m h3) (m h4) (m h5) (m h6) h7
  | tomlNotExact h1 h2 h3 => exact .tomlNotExact (m h1) (m h2) h3
  | notApart h1 h2 h3 => exact .notApart (m h1) (m h2) h3
  | configNotInTree h1 h2 h3 => exact .configNotInTree (m h1) h2 h3
  | moduleNotInTree h1 h2 h3 h4 => exact .moduleNotInTree (sc h1) (nm h2) h3 h4
  | moduleNotExact h1 h2 h3 h4 h5 h6 => exact .moduleNotExact (sc h1) (nm h2) h3 h4 (m h5) h6
  | leanConfig h1 h2 => exact .leanConfig (m h1) (m h2)
  | key h1 h2 h3 h4 => exact .key (TomlRead.mono hs h1) h2 h3 h4
  | deep h1 h2 => exact .deep (TomlRead.mono hs h1) h2
  | deepDependency h1 h2 => exact .deepDependency (TomlRead.mono hs h1) h2
  | dependency h1 h2 h3 => exact .dependency (TomlRead.mono hs h1) h2 h3
  | openDir h1 h2 h3 => exact .openDir (tl h1) h2 h3
  | openGlob h1 h2 h3 h4 => exact .openGlob (tl h1) h2 h3 h4
  | noClaim h1 => exact .noClaim (sc h1)
  | targetName h1 h2 h3 => exact .targetName (tl h1) h2 h3
  | twoFiles h1 h2 h3 h4 => exact .twoFiles (sc h1) h2 h3 h4
  | twoRoots h1 h2 h3 h4 => exact .twoRoots (sc h1) h2 h3 h4
  | moduleName h1 h2 h3 => exact .moduleName (sc h1) (nm h2) h3
  | importedRoot h1 h2 h3 h4 h5 h6 => exact .importedRoot (sc h1) (nm h2) (hd h3) h4 h5 h6
  | notToolchain h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .notToolchain (sc h1) (nm h2) h3 h4 (m h5) (m h6) h7 fun x hx => ⟨m (h8 x hx).1, (h8 x hx).2⟩
  | tooMany h1 h2 h3 h4 => exact .tooMany (sc h1) h2 (fun x hx => ⟨nm (h3 x hx).1, hd (h3 x hx).2⟩) h4
  | mathlib h1 h2 h3 => exact .mathlib (sc h1) (nm h2) h3
  | file h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .file (sc h1) (nm h2) h3 (ReadAs.mono hs h4) (fun x hx => hd (h5 x hx))
      (fun n hn => ⟨nm (h6 n hn).1, HeldByToolchain.mono hs (h6 n hn).2⟩) h7 h8 h9 h10

theorem BuildFailed.mono {root : Root L} (h : BuildFailed T root) : BuildFailed T' root := by
  cases h with
  | library h1 h2 h3 => exact .library h1 h2 (hs.subset h3)
  | «import» h1 h2 => exact .import (DefaultModules.mono hs h1) (hs.subset h2)
  | search h1 h2 h3 h4 => exact .search (DefaultModules.mono hs h1) (hs.subset h2) h3 (hs.subset h4)

theorem TreeRoot.mono {sysroot tree} {root : Root L} (h : TreeRoot sysroot tree T root) : TreeRoot sysroot tree T' root := by
  obtain ⟨r, l, h1, h2⟩ := h
  exact ⟨r, l, hs.subset h1, hs.subset h2⟩

theorem TreeReason.mono {sysroot tree} (h : TreeReason sysroot tree T) : TreeReason sysroot tree T' := by
  cases h with
  | noTree h1 => exact .noTree (hs.subset h1)
  | load h1 h2 h3 => exact .load (hs.subset h1) (hs.subset h2) h3
  | build h1 h2 => exact .build (TreeRoot.mono hs h1) (BuildFailed.mono hs h2)

theorem BuildRejected.mono {sysroot tree} (h : BuildRejected sysroot tree T) : BuildRejected sysroot tree T' := by
  cases h with
  | build h1 h2 h3 => exact .build (hs.subset h1) (hs.subset h2) h3
  | replay h1 h2 h3 h4 => exact .replay (hs.subset h1) (hs.subset h2) (hs.subset h3) h4

theorem BuildRead.mono {root : Root L} {f roots} (h : BuildRead T root f roots) : BuildRead T' root f roots := by
  obtain ⟨q, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨q, DefaultModules.mono hs h1, h2, h3.trans hs, h4, h5, fun x hx => hs.subset (h6 x hx)⟩

end Mono

/-! ## What a healthy build owes -/

/-- What a run of the proof verdict receives on a build that it owes a pass: no reason in the closed set holds, and each
environment that the run read of the workspace Lake dispatched has `LoadFloor`. -/
structure PlainOwed (t : List (Event L E)) (p : Regula.Closed.Profile) : Prop where
  /-- Nothing that the load needs failed, and the current directory is the workspace Lake dispatched. -/
  noReason : ¬ PlainReason t
  /-- What Lean's import gave has the floor. -/
  floor : ∀ root f roots, PlainRoot t root → BuildRead t root f roots → LoadFloor f roots p

/-- What a run of the full gate receives on a build that it owes a pass: the run has its tree, nothing keeps the project from
being admitted, the build and its replay ended with 0, nothing that the load of the result needs failed, and each
environment that the run read of that build has `LoadFloor`. -/
structure FullOwed (t : List (Event L E)) (dir : FilePath) (p : Regula.Closed.Profile) : Prop where
  /-- The tree. -/
  tree : ∀ e, (⟨.createTempDir, .error e⟩ : Event L E) ∉ t
  /-- No reason keeps the project from being admitted. -/
  admitted : ∀ tree rest o, t = ⟨.createTempDir, .ok tree⟩ :: rest → ¬ Reason (readPhase t) dir tree o
  /-- The build and its replay. -/
  built : ∀ tree rest sysroot, t = ⟨.createTempDir, .ok tree⟩ :: rest → SysrootIs (readPhase t) sysroot →
    ¬ BuildRejected sysroot tree t
  /-- The load of the result. -/
  loaded : ∀ tree rest sysroot, t = ⟨.createTempDir, .ok tree⟩ :: rest → SysrootIs (readPhase t) sysroot →
    ¬ TreeReason sysroot tree (rulesPhase t)
  /-- What Lean's import gave has the floor. -/
  floor : ∀ tree rest sysroot root f roots, t = ⟨.createTempDir, .ok tree⟩ :: rest → SysrootIs (readPhase t) sysroot →
    TreeRoot sysroot tree (rulesPhase t) root → BuildRead (rulesPhase t) root f roots → LoadFloor f roots p

/-- The last line of a pass of the proof verdict. -/
abbrev plainPass : String := Regula.Closed.Verdict.proofLine .pass

/-- The last line of a pass of the full verdict. -/
abbrev fullPass : String := (Report.full .pass).label

/-- A run of the proof verdict that receives what `PlainOwed` states passes: exit 0 and the last line of the pass. -/
theorem plain_owed {t : List (Event L E)} {p : Regula.Closed.Profile} {c : UInt32} (h : PlainRun t p c)
    (owed : PlainOwed t p) : c = 0 ∧ EndsWith t plainPass := by
  obtain ⟨result, hl, hc, he, -⟩ := h
  rcases hl with ⟨root, f, roots, hg, hb, rfl⟩ | ⟨hw, -⟩
  · have hv := pass_iff_floor.mpr (owed.floor root f roots hg hb)
    rw [hv] at hc he
    exact ⟨hc, he⟩
  · exact absurd hw owed.noReason

/-- A run of the full gate that receives what `FullOwed` states passes: exit 0 and the last line of the pass. -/
theorem full_owed {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32} (h : FullRun t dir p c)
    (owed : FullOwed t dir p) : c = 0 ∧ EndsWith t fullPass := by
  rcases h with ⟨e, rest, ht, -⟩ | ⟨tree, tRead, tGate, r, last, ht, hq, hlast, o, report, hdec, -, hn, ha, hc, hend, -⟩
  · exact (owed.tree e (by rw [ht]; exact List.mem_cons_self ..)).elim
  · have htree : t = ⟨.createTempDir, .ok tree⟩ :: (tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last) := by
      rw [ht]; simp
    have hread : tRead.Sublist (readPhase t) := by
      have := readPhase_sublist (x := ⟨.createTempDir, .ok tree⟩)
        (rest := tGate ++ ⟨.removeDirAll tree, r⟩ :: last) hq
      simpa [ht] using this
    have hadm : o = .admitted := by
      refine Classical.byContradiction fun hne => ?_
      have hri : tRead <:+: readPhase t := by
        simpa [ht, List.append_assoc] using (readPhase_infix
          (x := (⟨.createTempDir, .ok tree⟩ : Event L E))
          (rest := tGate ++ ⟨.removeDirAll tree, r⟩ :: last) hq)
      exact owed.admitted tree _ o htree (Reason.mono hri (hdec.2.1 hne))
    subst hadm
    obtain ⟨sysroot, tBuild, tRules, hs, rfl, hb⟩ := ha rfl
    have hsys : SysrootIs (readPhase t) sysroot := hread.subset hs
    have htb : tBuild.Sublist t := by
      rw [ht]
      simp only [List.cons_append, List.append_assoc]
      exact ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _)).trans
        (List.sublist_cons_self _ _)
    have hrep : report = .full .pass := by
      rcases hb.2.2 with ⟨program, lakeLib, result, hnb, -, hl, rfl⟩ | ⟨-, -, hrej⟩
      · have hrules : tRules.Sublist (rulesPhase t) := by
          have hpost : ∀ e ∈ (⟨.removeDirAll tree, r⟩ :: last : List (Event L E)), e.isBuild = false := by
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · rfl
            · have := hlast e he
              obtain ⟨o', r'⟩ := e
              cases o' <;> first | rfl | cases this
          have := rulesPhase_sublist (pre := ⟨.createTempDir, .ok tree⟩ :: tRead ++ tBuild) hnb hpost
          simpa [ht, List.append_assoc] using this
        rcases hl with ⟨root, f, roots, hg, hbr, rfl⟩ | ⟨hw, -⟩
        · rw [pass_iff_floor.mpr (owed.floor tree _ sysroot root f roots htree hsys
            (TreeRoot.mono hrules hg) (BuildRead.mono hrules hbr))]
        · exact absurd (TreeReason.mono hrules hw) (owed.loaded tree _ sysroot htree hsys)
      · exact absurd (BuildRejected.mono htb hrej) (owed.built tree _ sysroot htree hsys)
    subst hrep
    exact ⟨hc, hend⟩

/-- A run of the proof verdict that does not pass has a reason in the closed set, or what it read lacks the floor. -/
theorem plain_refused_justified {t : List (Event L E)} {p : Regula.Closed.Profile} {c : UInt32} (h : PlainRun t p c)
    (hc : c ≠ 0) :
    PlainReason t ∨ ∃ root f roots, PlainRoot t root ∧ BuildRead t root f roots ∧ ¬ LoadFloor f roots p := by
  refine Classical.byContradiction fun hno => hc (plain_owed h ⟨fun hr => hno (.inl hr), fun root f roots h1 h2 => ?_⟩).1
  exact Classical.byContradiction fun hf => hno (.inr ⟨root, f, roots, h1, h2, hf⟩)

/-- A run of the full gate that does not pass has, on the requested build, no tree, a reason in the closed set, a rejected
build, a failed load of its result, or what it read of that result lacks the floor. -/
theorem full_refused_justified {t : List (Event L E)} {dir : FilePath} {p : Regula.Closed.Profile} {c : UInt32}
    (h : FullRun t dir p c) (hc : c ≠ 0) : ¬ FullOwed t dir p :=
  fun owed => hc (full_owed h owed).1

/-! ## Every subject of the record -/

/-- For every program that meets the record, every run of the proof verdict on the pinned Lean, on responses that owe a pass,
passes. So a program that refuses a healthy build does not meet the record. -/
theorem run_plain_owed {w : List String → Prog L E UInt32} (hw : RunMeets w) {text : String} {p : Regula.Closed.Profile}
    (hp : Regula.Closed.Profile.ofSpelling? text = some p) {rest : List (Event L E)} {c : UInt32}
    (h : Runs (w [text]) (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) c)
    (owed : PlainOwed (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) p) :
    c = 0 ∧ EndsWith (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) plainPass := by
  have hm := hw _ _ _ h
  simp only [hp] at hm
  obtain ⟨v, rest', he, hrun, -⟩ := hm
  cases he
  exact plain_owed (hrun rfl) owed

/-- The same of every run of the full gate. -/
theorem run_full_owed {w : List String → Prog L E UInt32} (hw : RunMeets w) {text dir : String}
    {p : Regula.Closed.Profile} (hp : Regula.Closed.Profile.ofSpelling? text = some p) {rest : List (Event L E)}
    {c : UInt32} (h : Runs (w [text, "full", dir]) (⟨.leanVersion, Regula.Closed.pinnedLean⟩ :: rest) c)
    (owed : FullOwed rest (FilePath.mk dir) p) : c = 0 ∧ EndsWith rest fullPass := by
  have hm := hw _ _ _ h
  simp only [hp] at hm
  obtain ⟨v, rest', he, hrun, -⟩ := hm
  cases he
  obtain ⟨rest'', v', he', hf⟩ := hrun rfl
  cases he'
  exact full_owed hf owed

/-! ## A program that manufactures a reason -/

/-- A program that asks which Lean this is, reads an environment variable that the build does not need, and says that the
proof verdict is incomplete. The audit of 2026-10-31 proved that it met the earlier form of the record. -/
def manufacturer (name : String) (_ : List String) : Prog L E UInt32 :=
  .ask .leanVersion fun _ =>
    .ask (.getEnv name) fun _ =>
      .ask (.println (Regula.Closed.Verdict.proofLine .incomplete)) fun _ => .done 2

/-- A reason that reads an unrelated variable: no case of the closed set holds of it, so that program fails the record, for
every name but the two that the load needs. -/
theorem manufacturer_fails {name : String} (h1 : name ≠ "LEAN_SYSROOT") (h2 : name ≠ "LEAN_PATH") :
    ¬ RunMeets (manufacturer name : List String → Prog L E UInt32) := by
  intro hw
  have hr : Runs (manufacturer name ["standard-logical"] : Prog L E UInt32)
      [⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv name, none⟩,
        ⟨.println (Regula.Closed.Verdict.proofLine .incomplete), .ok ()⟩] 2 :=
    .ask _ _ _ (.ask _ _ _ (.ask _ _ _ (.done _)))
  have hm := hw _ _ _ hr
  have hsp : Regula.Closed.Profile.ofSpelling? "standard-logical" = some .standardLogical := rfl
  simp only [hsp] at hm
  obtain ⟨v, rest, he, hrun, -⟩ := hm
  cases he
  obtain ⟨result, hl, -⟩ := hrun rfl
  have hno : ∀ {o : Op L E} {r : Resp o},
      (⟨o, r⟩ : Event L E) ∈ ([⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv name, none⟩,
        ⟨.println (Regula.Closed.Verdict.proofLine .incomplete), .ok ()⟩] : List (Event L E)) →
      (o = .leanVersion ∨ o = .getEnv name ∨ o = .println (Regula.Closed.Verdict.proofLine .incomplete)) := by
    intro o r hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm | hm
    · exact .inl (congrArg Event.op hm)
    · exact .inr (.inl (congrArg Event.op hm))
    · exact .inr (.inr (congrArg Event.op hm))
  have hplain : ∀ root, ¬ PlainRoot ([⟨.leanVersion, Regula.Closed.pinnedLean⟩, ⟨.getEnv name, none⟩,
      ⟨.println (Regula.Closed.Verdict.proofLine .incomplete), .ok ()⟩] : List (Event L E)) root := by
    rintro root ⟨s, d, l, lp, ll, prog, -, hload, -⟩
    rcases hno hload with h | h | h <;> cases h
  rcases hl with ⟨root, f, roots, hg, -⟩ | ⟨hw', -⟩
  · exact hplain root hg
  · cases hw' with
    | noSysroot h =>
      rcases hno h with h | h | h <;> first | (cases h; exact h1 rfl) | cases h
    | noDirectory h => rcases hno h with h | h | h <;> cases h
    | load _ _ h _ => rcases hno h with h | h | h <;> cases h
    | noSearchPath h =>
      rcases hno h with h | h | h <;> first | (cases h; exact h2 rfl) | cases h
    | elsewhere _ _ h => rcases hno h with h | h | h <;> cases h
    | build h _ => exact hplain _ h

end RegulaSpecification.Effects
