/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.Proofs.Shell

/-!
# A project that the reader admits

`admits_a_project` shows that the record is no empty promise and that the reader refuses not everything: there are
answers of Lean, Lake and the operating system, for a project of one module `Good` in the closed language, on which the
check that runs admits the project and the gate builds it.

The answers are `answers`, one function of the operation. The tests of a path read `System.FilePath`, whose separator
depends on `System.Platform.isWindows`, which the kernel cannot evaluate, so `WitnessPaths` states what those tests give
on the paths of the project as hypotheses. **Observed**: the gate's run on Regula's own checkout takes the same branches
on real paths, and its run ends with `full verdict: pass`.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax MessageLog)
open Lean.Parser (ModuleParserState)
open System (FilePath)
open Regula.Effect
open Regula.Language
open Regula.Reader
open Regula.Shell
open RegulaSpecification.Language

/-- The events of a program, for the answers `f`, one function of the operation. -/
def traceWith {L E α : Type} (f : (o : Op L E) → Resp o) : Prog L E α → List (Event L E)
  | .done _ => []
  | .ask o next => ⟨o, f o⟩ :: traceWith f (next (f o))

/-- The value of a program, for those answers. -/
def valueWith {L E α : Type} (f : (o : Op L E) → Resp o) : Prog L E α → α
  | .done a => a
  | .ask o next => valueWith f (next (f o))

theorem runs_with {L E α : Type} (f : (o : Op L E) → Resp o) (p : Prog L E α) :
    Runs p (traceWith f p) (valueWith f p) := by
  induction p with
  | done a => exact .done a
  | ask o next ih => exact .ask o next _ (ih _)

theorem traceWith_answers {L E α : Type} {f : (o : Op L E) → Resp o} {p : Prog L E α} {e : Event L E}
    (h : e ∈ traceWith f p) : e = ⟨e.op, f e.op⟩ := by
  induction p with
  | done a => cases h
  | ask o next ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact ih _ h

/-- The paths of the witness, and what the tests of them give. -/
structure WitnessPaths where
  /-- The project. -/
  project : FilePath
  /-- The checker's tree. -/
  tree : FilePath
  /-- This program. -/
  app : FilePath
  /-- The search path Lake gave. -/
  leanPath : String
  /-- The library directory of Lake. -/
  lakeLib : FilePath
  /-- The file that Lake names for the module `Good`. -/
  file : FilePath
  /-- Its components below the tree. -/
  rel : List String
  /-- The directory of the toolchain's library. -/
  toolchainDir : FilePath
  /-- An `.olean` of that library. -/
  olean : FilePath
  /-- It lies below that library. -/
  oleanBelow : Regula.Load.below toolchainDir olean = true
  /-- This program lies outside the project. -/
  outside : Regula.Load.below project app = false
  /-- The Lake that started it dispatched from its own package. -/
  dispatched : (app.parent.bind (·.parent)).map (· / "lib" / "lean") |>.any fun lib =>
    Regula.Load.dispatchedFrom lib.toString lakeLib.toString
      ((System.SearchPath.parse leanPath).map toString)
  /-- The project and the tree lie apart. -/
  apart : apart project tree = true
  /-- `lean-toolchain` lies at itself below the project. -/
  toolchainExact : Regula.Load.exactBelow project (project / "lean-toolchain") (project / "lean-toolchain") = true
  /-- `lakefile.toml` lies at itself below the project. -/
  tomlExact : Regula.Load.exactBelow project (project / "lakefile.toml") (project / "lakefile.toml") = true
  /-- The tree's copies lie below it. -/
  tomlInTree : ¬ OutsideTree tree (tree / "lakefile.toml")
  /-- The tree's copies lie below it. -/
  toolchainInTree : ¬ OutsideTree tree (tree / "lean-toolchain")
  /-- The module's file lies below the tree, at `rel`. -/
  fileRel : TreeRelative (Regula.Load.exactParts tree) (Regula.Load.exactParts file) rel
  /-- Its directory too. -/
  fileInTree : ¬ OutsideTree tree file
  /-- The same relative path lies at itself below the project. -/
  fileExact : Regula.Load.exactBelow project (under project rel) (under project rel) = true
  /-- The pinned text is the text of the file, trimmed. -/
  pinned : leanToolchain.trimAscii.toString = leanToolchain
  /-- An empty log holds no error. -/
  noErrors : ({} : MessageLog).hasErrors = false

/-- What the workspace of the witness holds: one default library of the module `Good`. -/
def witnessRoot (w : WitnessPaths) : Root Unit where
  sourceDirs := []
  libraries := []
  defaultTargets := [`Good]
  findLib := fun _ => some ()
  findExe := fun _ => none
  targets := []
  resolve := fun _ => none
  leanPath := []
  toolchain := [w.toolchainDir]
  leanLib := w.toolchainDir
  rootLib := w.tree

/-- The answers of the witness: every read gives the pinned text, every parse a file in the closed language with no
import, and nothing fails. -/
def answers (w : WitnessPaths) : (o : Op Unit Unit) → Resp o
  | .leanVersion => Regula.Closed.pinnedLean
  | .getEnv _ => some w.leanPath
  | .appPath => .ok w.app
  | .realPath p => .ok p
  | .readFile _ => .ok leanToolchain
  | .symlinkMetadata _ => .error (.noFileOrDirectory "" 0 "")
  | .writeFile .. => .ok ()
  | .createDirAll _ => .ok ()
  | .createTempDir => .ok w.tree
  | .removeDirAll _ => .ok ()
  | .println _ => .ok ()
  | .flush => .ok ()
  | .parseHeader _ => .ok (moduleHeader, default, {}, #[])
  | .parseCommand .. => (endOfInput, default, {})
  | .setSearchPath _ => ()
  | .findOLean _ => .ok w.olean
  | .importForRules _ => .error (.userError "")
  | .importForParser _ => .ok ((), [])
  | .parseToml _ => .ok Lake.Toml.Table.empty
  | .lakeInstall _ => (w.tree, w.lakeLib)
  | .loadWorkspace .. => .error ""
  | .loadRoot .. => .ok (some (witnessRoot w), [])
  | .libModules _ => .ok #[(`Good, w.file)]
  | .runLake .. => .ok 0

variable {α : Type}

theorem resp_eq {L E : Type} {f : (o : Op L E) → Resp o} {p : Prog L E α} {o : Op L E} {r : Resp o}
    (h : (⟨o, r⟩ : Event L E) ∈ traceWith f p) : r = f o := by
  have := traceWith_answers h
  simpa using this

theorem keyPath_empty {pre k : Name} : ¬ KeyPath pre Lake.Toml.Table.empty k := by
  intro h
  generalize ht : Lake.Toml.Table.empty = t at h
  cases h <;> (subst ht; simp [Lake.Toml.Table.empty, Lake.Toml.RBDict.empty] at *)

theorem deeper_empty : ¬ Deeper 8 Lake.Toml.Table.empty := by
  intro h
  generalize ht : Lake.Toml.Table.empty = t at h
  cases h <;> (subst ht; simp [Lake.Toml.Table.empty, Lake.Toml.RBDict.empty] at *)

/-- What the reader read of a file, on the answers of the witness, is in the closed language. -/
theorem good_file {w : WitnessPaths} {p : Prog Unit Unit α} {f : FileRead} {project tree path : FilePath}
    {imports : Array Lean.Import} {mods : List Name}
    (h : ReadAs (traceWith (answers w) p) project tree f path imports mods) : FileAdmitted f := by
  obtain ⟨rel, real, text, state, messages, final, env, commands, -, -, -, hsub, hev, hparsed, hcsub, hp⟩ := h
  have hmem : (⟨.parseHeader (Lean.Parser.mkInputContext text path.toString),
      .ok (f.header, state, messages, imports)⟩ : Event Unit Unit) ∈ traceWith (answers w) p :=
    hsub.subset (by simp)
  have hheader : (Except.ok (f.header, state, messages, imports) :
      Except IO.Error (Syntax × ModuleParserState × MessageLog × Array Lean.Import)) =
      .ok (moduleHeader, default, {}, #[]) := resp_eq hmem
  have hscoped : (Except.ok (env, f.scopedParsers) : Except IO.Error (Unit × List Name)) = .ok ((), []) :=
    resp_eq hev
  have hheader' := Except.ok.inj hheader
  have hscoped' := Except.ok.inj hscoped
  simp only [Prod.mk.injEq] at hheader' hscoped'
  obtain ⟨h1, rfl, rfl, rfl⟩ := hheader'
  obtain ⟨-, h2⟩ := hscoped'
  have hterm : Lean.Parser.isTerminalCommand endOfInput = true := by decide
  generalize hfuel : (Lean.Parser.mkInputContext text path.toString).inputString.utf8ByteSize + 1 = fuel at hparsed
  generalize hcmds : f.commands = cmds at hparsed
  generalize hst : (default : ModuleParserState) = st at hparsed
  generalize hmsg : ({} : MessageLog) = ms at hparsed
  cases hparsed with
  | stop => omega
  | last ht =>
    subst hst hmsg
    have hc' := resp_eq (hcsub.subset (List.mem_singleton.mpr rfl))
    cases (hc' : (_, _, _) = (endOfInput, (default : ModuleParserState), ({} : MessageLog)))
    refine ⟨by rw [hp, w.noErrors]; rfl, ?_, ?_, ?_, ?_⟩
    · rw [h1]
      exact ⟨.none, _, .self _⟩
    · rw [hcmds]
      exact ⟨.none, _, rfl⟩
    · rw [h1, h2]
      exact admitted_moduleHeader
    · intro c hc
      rw [hcmds] at hc
      have : c = endOfInput := by simpa using hc
      rw [this, h2]
      exact admitted_endOfInput
  | next ht _ =>
    subst hst hmsg
    have hc' := resp_eq (hcsub.subset (List.mem_cons_self ..))
    cases (hc' : (_, _, _) = (endOfInput, (default : ModuleParserState), ({} : MessageLog)))
    rw [hterm] at ht
    cases ht

/-- What the default targets of the witness give. -/
theorem good_modules {w : WitnessPaths} {p : Prog Unit Unit α} {modules : List (Name × FilePath)}
    (h : DefaultModules (traceWith (answers w) p) (witnessRoot w) (witnessRoot w).defaultTargets modules) :
    modules = [(`Good, w.file)] := by
  have hd : (witnessRoot w).defaultTargets = [`Good] := rfl
  rw [hd] at h
  cases h with
  | lib hl hev hrest =>
    have he : (Except.ok _ : Except IO.Error (Array (Name × FilePath))) = .ok #[(`Good, w.file)] := resp_eq hev
    cases Except.ok.inj he
    cases hrest
    rfl
  | exe hl => cases hl
  | other hl => cases hl

/-- No reason keeps the project of the witness from being admitted. -/
theorem no_reason (w : WitnessPaths) (p : Prog Unit Unit α) (o : Outcome) :
    ¬ Reason (traceWith (answers w) p) w.project w.tree o := by
  intro hr
  have hreal : ∀ {q real : FilePath}, (⟨.realPath q, .ok real⟩ : Event Unit Unit) ∈ traceWith (answers w) p →
      real = q := fun h => Except.ok.inj (resp_eq h : (Except.ok _ : Except IO.Error FilePath) = .ok _)
  have hroot : ∀ {sysroot : String} {dir : FilePath} {root : Root Unit} {log : List String},
      (⟨.loadRoot sysroot dir, .ok (some root, log)⟩ : Event Unit Unit) ∈ traceWith (answers w) p →
      root = witnessRoot w := fun h => by
    have he : (Except.ok (some _, _) : Except String (Option (Root Unit) × List String)) =
        .ok (some (witnessRoot w), []) := resp_eq h
    have := Except.ok.inj he
    simp only [Prod.mk.injEq, Option.some.injEq] at this
    exact this.1
  have htable : ∀ {input} {table : Lake.Toml.Table},
      (⟨.parseToml input, .ok table⟩ : Event Unit Unit) ∈ traceWith (answers w) p →
      table = Lake.Toml.Table.empty := fun h =>
    Except.ok.inj (resp_eq h : (Except.ok _ : Except Lean.MessageLog Lake.Toml.Table) = .ok _)
  have hnoImports : ∀ {input header state messages} {imports : Array Lean.Import},
      (⟨.parseHeader input, .ok (header, state, messages, imports)⟩ : Event Unit Unit) ∈
        traceWith (answers w) p → imports = #[] := fun {input header state messages imports} h => by
    have he : (Except.ok (header, state, messages, imports) :
        Except IO.Error (Syntax × ModuleParserState × MessageLog × Array Lean.Import)) =
        .ok (moduleHeader, default, {}, #[]) := resp_eq h
    have := Except.ok.inj he
    simp only [Prod.mk.injEq] at this
    exact this.2.2.2
  have hnamed : ∀ {modules : List (Name × FilePath)} {m : Name},
      modules = [(`Good, w.file)] → Named (traceWith (answers w) p) modules m → m = `Good := by
    intro modules m hm hn
    rcases hn with hn | ⟨input, header, state, messages, imports, hev, i, hi, -⟩
    · subst hm
      simpa using hn
    · rw [hnoImports hev] at hi
      simp at hi
  cases hr with
  | failed he hf =>
    rename_i e
    obtain ⟨op, r⟩ := e
    have hrr := resp_eq he
    subst hrr
    cases op <;> first
      | exact hf.elim
      | (obtain ⟨e, he, hne⟩ := hf
         cases (he : Except.error _ = Except.error e)
         exact hne _ _ _ rfl
         done)
      | (rcases hf with ⟨e, he⟩ | ⟨l, he⟩
         · cases (he : (Except.ok (some (witnessRoot w), []) :
             Except String (Option (Root Unit) × List String)) = .error e)
         · cases (he : (Except.ok (some (witnessRoot w), []) :
             Except String (Option (Root Unit) × List String)) = .ok (none, l))
         done)
      | (simp [Event.failedRead, answers] at hf
         done)
  | noSysroot he => cases resp_eq he
  | noSearchPath he => cases resp_eq he
  | toolchain hp ht hne =>
    have := Except.ok.inj (resp_eq ht : (Except.ok _ : Except IO.Error String) = .ok _)
    subst this
    exact hne w.pinned
  | toolchainFailed hp ht => cases resp_eq ht
  | toolchainNotExact hp hr he =>
    rw [hreal hp] at he hr
    rw [hreal hr, w.toolchainExact] at he
    cases he
  | toolchainNoReal hp ht => cases resp_eq ht
  | started hp hl ha hr henv hcase =>
    rename_i project sysroot program lakeLib app real leanPath
    obtain rfl := hreal hp
    have hla : (program, lakeLib) = (w.tree, w.lakeLib) := resp_eq hl
    cases hla
    have happ := Except.ok.inj (resp_eq ha : (Except.ok _ : Except IO.Error FilePath) = .ok _)
    subst happ
    obtain rfl := hreal hr
    have hen : some leanPath = some w.leanPath := resp_eq henv
    cases hen
    rcases hcase with h' | h'
    · rw [w.outside] at h'
      cases h'
    · have hd := w.dispatched
      cases hown : (w.app.parent.bind (·.parent)).map (· / "lib" / "lean") with
      | none => simp [hown] at hd
      | some own =>
        simp only [hown, Option.any_some] at hd
        rw [h' own hown] at hd
        cases hd
  | tomlNotExact hp hr he =>
    obtain rfl := hreal hp
    rw [hreal hr, w.tomlExact] at he
    cases he
  | notApart hp ht hna =>
    obtain rfl := hreal hp
    obtain rfl := hreal ht
    exact hna ((apart_iff _ _).mp w.apart)
  | configNotInTree ht hp ho =>
    obtain rfl := hreal ht
    rcases hp with rfl | rfl
    · exact w.tomlInTree ho
    · exact w.toolchainInTree ho
  | moduleNotInTree ht hl hd hp ho =>
    obtain rfl := hreal ht
    obtain rfl := hroot hl
    rw [good_modules hd] at hp
    rcases hp with hp | hp
    · have : _ = _ := List.mem_singleton.mp hp
      cases this
      exact w.fileInTree ho
    · cases hp
  | moduleNotExact hp ht hl hd hm hrel hr he =>
    obtain rfl := hreal hp
    obtain rfl := hreal ht
    obtain rfl := hroot hl
    rw [good_modules hd] at hm
    rcases hm with hm | hm
    · have : _ = _ := List.mem_singleton.mp hm
      cases this
      have hrel2 := w.fileRel
      have hsame : _ = w.rel := List.append_cancel_left (hrel.1.symm.trans hrel2.1)
      subst hsame
      rw [hreal hr, w.fileExact] at he
      cases he
    · cases hm
  | leanConfig hp hm => cases resp_eq hm
  | key hp hk hroot' hna =>
    rw [htable hp] at hk
    exact keyPath_empty hk
  | deep hp hd =>
    rw [htable hp] at hd
    exact deeper_empty hd
  | deepDependency hp hd =>
    rw [htable hp] at hd
    exact deeper_empty hd
  | dependency hp hk hroot' =>
    rw [htable hp] at hk
    exact keyPath_empty hk
  | openDir hl hd hn =>
    obtain rfl := hroot hl
    cases hd
  | openGlob hl hd hg hn =>
    obtain rfl := hroot hl
    cases hd
  | noClaim hl hd =>
    obtain rfl := hroot hl
    have := good_modules hd
    cases this
  | targetName hl hn hc =>
    obtain rfl := hroot hl
    cases hn
  | twoFiles hl hd hm hres hne =>
    obtain rfl := hroot hl
    cases hres
  | twoRoots hl hd hm hm2 hne =>
    obtain rfl := hroot hl
    rw [good_modules hd] at hm hm2
    have h1 : _ = _ := List.mem_singleton.mp hm
    have h2 : _ = _ := List.mem_singleton.mp hm2
    cases h1
    cases h2
    exact hne rfl
  | moduleName hl hd hn hc =>
    obtain rfl := hroot hl
    have hg := hnamed (good_modules hd) hn
    subst hg
    exact hc good_closed_name
  | importedRoot hl hd he hi hsome hres =>
    rw [hnoImports he] at hi
    simp at hi
  | notToolchain hl hf hr hmap hall =>
    rename_i m olean real sysroot tree root log reals
    obtain rfl := hroot hl
    have ho := Except.ok.inj (resp_eq hf : (Except.ok _ : Except IO.Error FilePath) = .ok _)
    subst ho
    obtain rfl := hreal hr
    have hmap' : reals.map Prod.fst = [w.toolchainDir] := hmap
    cases reals with
    | nil => cases hmap'
    | cons x xs =>
      have h1 : x.1 = w.toolchainDir := by
        simp only [List.map_cons, List.cons.injEq] at hmap'
        exact hmap'.1
      obtain ⟨hev, hb⟩ := hall x (List.mem_cons_self ..)
      have := hreal hev
      rw [this, h1, w.oleanBelow] at hb
      cases hb
  | tooMany hl hd hb =>
    obtain rfl := hroot hl
    rw [good_modules hd] at hb
    have hall : ∀ e ∈ traceWith (answers w) p, Event.importsStated e = 0 := by
      intro e he
      obtain ⟨op, r⟩ := e
      have hrr := resp_eq he
      subst hrr
      cases op <;> rfl
    have hsum : ∀ l : List (Event Unit Unit), (∀ e ∈ l, Event.importsStated e = 0) → importCount l = 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [importCount, List.map_cons, List.sum_cons] at ih ⊢
        rw [hl x (List.mem_cons_self ..), ih fun e he => hl e (List.mem_cons_of_mem _ he)]
    have hzero := hsum _ hall
    rw [hzero] at hb
    simp at hb
  | mathlib hl hd hn hroot' =>
    obtain rfl := hroot hl
    have hg := hnamed (good_modules hd) hn
    subst hg
    exact absurd hroot' (by decide)
  | file hp ht ha hna =>
    exact hna (good_file ha)

/-- There are answers on which the check that runs admits a project: the record is not empty, and the reader refuses
not everything. -/
theorem admits_a_project (w : WitnessPaths) (sysroot : String) :
    ∃ t, Runs (check sysroot w.project w.tree : Prog Unit Unit Outcome) t .admitted := by
  refine ⟨traceWith (answers w) (check sysroot w.project w.tree),
    ?_⟩
  have hr := runs_with (answers w) (check sysroot w.project w.tree : Prog Unit Unit Outcome)
  obtain ⟨hd, -⟩ := check_spec (List.Sublist.refl _) hr
  cases ho : valueWith (answers w) (check sysroot w.project w.tree : Prog Unit Unit Outcome) with
  | admitted => rw [ho] at hr; exact hr
  | refused => rw [ho] at hd; exact absurd (hd.2.1 (by simp)) (no_reason w _ _)
  | proofOnly => rw [ho] at hd; exact absurd (hd.2.1 (by simp)) (no_reason w _ _)
  | incomplete => rw [ho] at hd; exact absurd (hd.2.1 (by simp)) (no_reason w _ _)

end RegulaSpecification.Effects
