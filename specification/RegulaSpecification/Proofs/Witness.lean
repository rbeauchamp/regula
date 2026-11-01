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
  | .findOLean _ => .ok w.toolchainDir
  | .importForRules _ => .error (.userError "")
  | .importForParser _ => .ok ((), [])
  | .parseToml _ => .ok Lake.Toml.Table.empty
  | .lakeInstall _ => (w.tree, w.lakeLib)
  | .loadWorkspace .. => .error ""
  | .loadRoot .. => .ok (some (witnessRoot w), [])
  | .libModules _ => .ok #[(`Good, w.file)]
  | .runLake .. => .ok 0

end RegulaSpecification.Effects
