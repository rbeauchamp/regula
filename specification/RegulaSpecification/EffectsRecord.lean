/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRun

/-!
# The record of a run

`Reason` states relevance to the requested build (`Scene`, `Named`, `Needed`). `FullRun` additionally requires the
ordered preparation of every copy, load, command and search-path consumer, including failed attempts, and that an
admission rests on `Evidence` of the state `written` that the reading leaves, so that it is about the text that stands.
Neither relevance alone nor the absence of a reason establishes preparation. `PlainRun` requires the same search-path discipline for a
proof verdict. Responses remain arbitrary: these relations constrain the requests, not the external system's truth.
`PlainReason`, `TreeReason` and `BuildRejected` state the reasons of the finished load and build. `programRecord` states
a whole run, for every response, and it is the contract that
`Regula.Shell.run` is proved against. `RegulaSpecification.Proofs.Owed` states what follows of every program that meets it:
a run in which nothing that the build needs has failed, on a project nothing keeps from being admitted, and whose environment has
`LoadFloor`, passes.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-! ## The requested build, by this run's responses -/

/-- The toolchain of the run: the answer to `LEAN_SYSROOT`. -/
def SysrootIs (t : List (Event L E)) (sysroot : String) : Prop :=
  (⟨.getEnv "LEAN_SYSROOT", some sysroot⟩ : Event L E) ∈ t

/-- Lake receives the requested project's configuration, after both successful copies. The intervening
events can only create directories: an overwrite, removal or load cannot be hidden between the copies
and this load. The response belongs to this occurrence of the prepared operation. -/
def PreparedLoad (t : List (Event L E)) (dir treeDir : FilePath) (sysroot : String) (tree : FilePath)
    (response : Resp (Op.loadRoot (L := L) (E := E) sysroot tree)) : Prop :=
  ∃ project text toolchain between,
    (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
    (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧ SysrootIs t sysroot ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t ∧
    (⟨.readFile (project / "lean-toolchain"), .ok toolchain⟩ : Event L E) ∈ t ∧
    toolchain.trimAscii.toString = leanToolchain ∧
    ([⟨.writeFile (tree / "lakefile.toml") text, .ok ()⟩] ++ between ++
      [⟨.writeFile (tree / "lean-toolchain") leanToolchain, .ok ()⟩,
       ⟨.loadRoot sysroot tree, response⟩] : List (Event L E)) <:+: t ∧
    ∀ e ∈ between, ∃ d, e = (⟨.createDirAll d, .ok ()⟩ : Event L E)

/-- What a prepared load of the requested project's configuration gave, on the run's toolchain. -/
def TreeLoaded (t : List (Event L E)) (dir treeDir tree : FilePath) (root : Root L) : Prop :=
  (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧
    ∃ sysroot log, SysrootIs t sysroot ∧ (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      PreparedLoad t dir treeDir sysroot tree (.ok (some root, log))

/-- The requested build: the project that `dir` names, the checker's tree, what Lake's load of the tree gave, and the
modules of its default targets. -/
structure Scene (t : List (Event L E)) (dir treeDir project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) : Prop where
  /-- The project's real path. -/
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t
  /-- Lake's load of the tree. -/
  loaded : TreeLoaded t dir treeDir tree root
  /-- The modules of the default targets. -/
  default : DefaultModules t root root.defaultTargets modules

/-- The text that the run read of the project's file that lies at the same relative path as `path` does in the tree. -/
def SourceText (t : List (Event L E)) (project tree path : FilePath) (text : String) : Prop :=
  ∃ rel, TreeRelative (parts tree) (parts path) rel ∧ (⟨.readFile (under project rel), .ok text⟩ : Event L E) ∈ t

/-- What Lean's parser gave as the imports of the file of the module `m`, on the text read of that file. -/
def HeaderOf (t : List (Event L E)) (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (m : Name) (imports : Array Import) : Prop :=
  ∃ path text header state messages, FileOfModule root modules m path ∧ SourceText t project tree path text ∧
    (⟨.parseHeader (mkInputContext text (Regula.Load.inputName path)), .ok (header, state, messages, imports)⟩ : Event L E) ∈ t

/-- A name the build needs: a module of a default target, or what the file of a name it needs imports. A header that the
run parsed of anything else names nothing. -/
inductive Named (t : List (Event L E)) (project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) : Name → Prop where
  /-- A module of a default target. -/
  | root {m} : m ∈ modules.map (·.1) → Named t project tree root modules m
  /-- What the file of a name that the build needs imports. -/
  | imported {m imports i} : Named t project tree root modules m → HeaderOf t project tree root modules m imports →
      i ∈ imports → Named t project tree root modules i.module

/-! ## Preparation at each occurrence -/

/-- Observations and reporting that neither change the tree or search path nor consume either context.
The closed operation type makes a new operation a new specification obligation. -/
def QuietOp : Op L E → Prop
  | .leanVersion | .getEnv _ | .appPath | .realPath _ | .readFile _ | .symlinkMetadata _
  | .println _ | .flush | .parseHeader _ | .parseCommand .. | .parseToml _ | .lakeInstall _
  | .libModules _ => True
  | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ | .runLake ..
  | .setSearchPath _ | .findOLean _ | .importForRules _ | .importForParser _
  | .loadRoot .. | .loadWorkspace .. => False

/-- Every event of a segment is an observation or report independent of the prepared contexts. -/
def Quiet (t : List (Event L E)) : Prop := ∀ e ∈ t, QuietOp e.op

/-- What the file system answered after the last act of `t`, which in `Decided` is the reading: `t` ends with a segment that holds no act, and for each
write of `t` whose text stands by `written`, that segment holds a read through the path it was written at that gave that text. A
statement of `written` alone is a model of the file system, in which different components name different files and a write that
answered success stored its text. This clause needs neither. A read through another path string with the same components does not
discharge this clause, and `written` still treats such strings as one place. It asks for a read that matches, and does not exclude
another read that differs: that the program stops at one is `Regula.Reader.readBack`'s, and inconsistent answers stay accepted.

That segment also holds the file system's answer that nothing has the name `lakefile.lean` in the tree `tree`. Lake prefers that
name to `lakefile.toml` when it looks for a configuration with no extension, which is what its command line does
(`resolveConfigFile`, `Lake/Load/Package.lean:109-117`, `defaultConfigFile`, `Lake/CLI/Main.lean:48`). So a module's file that the
file system takes for that name, by case folding or anything else, has a second role, as the configuration. Which file the name
reaches is the file system's to say, so the clause asks it through that name and models no folding. -/
def ReadBack (t : List (Event L E)) (tree : FilePath) : Prop :=
  ∃ pre suffix, t = pre ++ suffix ∧ Quiet suffix ∧
    (∀ path text r, (⟨.writeFile path text, r⟩ : Event L E) ∈ t → written t (parts path) = some text →
      (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix) ∧
    ∃ e, (⟨.symlinkMetadata (tree / "lakefile.lean"), .error e⟩ : Event L E) ∈ suffix ∧
      ∃ name code details, e = .noFileOrDirectory name code details

/-- Whether an attempted copy completed, as its write response states. -/
def copyComplete : Except IO.Error Unit → Bool
  | .ok _ => true
  | .error _ => false

/-- The complete acts of one copy attempt, including failed attempts. A path or parent outside the tree
makes no act. A failed directory creation ends the step; otherwise the write immediately follows its own
successful parent creation, or has no parent. -/
inductive CopyStep (tree path : FilePath) (text : String) : List (Event L E) → Bool → Prop where
  /-- An out-of-tree path or parent produces no act. -/
  | outside : OutsideTree tree path → CopyStep tree path text [] false
  /-- A path with no parent is written directly. -/
  | noParent {r} : (∃ rel, TreeRelative (parts tree) (parts path) rel) → path.parent = none →
      CopyStep tree path text [⟨.writeFile path text, r⟩] (copyComplete r)
  /-- A failed parent creation ends this attempt before any write. -/
  | parentFailed {parent error} : (∃ rel, TreeRelative (parts tree) (parts path) rel) →
      path.parent = some parent → (∃ rel, TreeRelative (parts tree) (parts parent) rel) →
      CopyStep tree path text [⟨.createDirAll parent, .error error⟩] false
  /-- Successful parent creation is followed by the write, with either response. -/
  | parentWritten {parent r} : (∃ rel, TreeRelative (parts tree) (parts path) rel) →
      path.parent = some parent → (∃ rel, TreeRelative (parts tree) (parts parent) rel) →
      CopyStep tree path text [⟨.createDirAll parent, .ok ()⟩, ⟨.writeFile path text, r⟩] (copyComplete r)

/-- A consumer of the reading phase's search path. -/
def ParserSearchOp : Op L E → Prop
  | .findOLean _ | .importForParser _ => True
  | _ => False

/-- A consumer of the finished build's search path. -/
def RulesSearchOp : Op L E → Prop
  | .findOLean _ | .importForRules _ => True
  | _ => False

/-- Module copies in order, with reads free between them. Each step uses a name and text justified by
the prefix before that step. A failed module step does not prevent the remaining steps. No search-path
setter, load, command, removal or unrelated copy is a case. This grammar says only which acts may occur: it admits a
later copy of another text, and it is `Evidence` of what stands afterwards that refuses one the run did not judge
(`uncheckedCopy_fails`). -/
inductive ModuleCopies (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) :
    List (Event L E) → List (Event L E) → Prop where
  /-- No further module-copy events remain. -/
  | nil {prior} : ModuleCopies project tree root modules prior []
  /-- An observation or parser search extends the prefix for subsequent steps. -/
  | observe {prior e rest} : (QuietOp e.op ∨ ParserSearchOp e.op) →
      ModuleCopies project tree root modules (prior ++ [e]) rest →
      ModuleCopies project tree root modules prior (e :: rest)
  /-- Copy a needed module's file using text read in the preceding prefix. -/
  | copy {prior m path text step rest complete} : Named prior project tree root modules m →
      FileOfModule root modules m path → SourceText prior project tree path text →
      CopyStep tree path text step complete → ModuleCopies project tree root modules (prior ++ step) rest →
      ModuleCopies project tree root modules prior (step ++ rest)

/-- After the configuration load, either only observations follow, or the loaded root's toolchain
search path is set once and all module copies and parser consumers follow that setter. -/
def ReadingLoaded (prior : List (Event L E)) (project tree : FilePath) (root : Root L)
    (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before rest modules,
    t = before ++ ⟨.setSearchPath root.toolchain, ()⟩ :: rest ∧ Quiet before ∧
    DefaultModules (prior ++ before) root root.defaultTargets modules ∧
    ModuleCopies project tree root modules (prior ++ before ++ [⟨.setSearchPath root.toolchain, ()⟩]) rest

/-- At most one configuration load, after the two completed copies. Every load response, including a
failure, belongs to this occurrence. Observations may precede it; no act may intervene. -/
def ReadingLoad (prior : List (Event L E)) (sysroot : String) (project tree : FilePath)
    (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before response rest,
    t = before ++ ⟨.loadRoot sysroot tree, response⟩ :: rest ∧ Quiet before ∧
    match response with
    | .ok (some root, _) =>
        ReadingLoaded (prior ++ before ++ [⟨.loadRoot sysroot tree, response⟩]) project tree root rest
    | _ => Quiet rest

/-- Configuration copies in the stated order. A failed step ends the acts; only after all successful
steps may the prepared configuration be loaded. `prior` is the exact earlier prefix. -/
inductive ConfigCopies (sysroot : String) (project tree : FilePath) :
    List (FilePath × String) → List (Event L E) → List (Event L E) → Prop where
  /-- Completed configuration copies permit the prepared load phase. -/
  | done {prior t} : ReadingLoad prior sysroot project tree t → ConfigCopies sysroot project tree [] prior t
  /-- A reading that stops here performs only observations and reporting. -/
  | stopped {copies prior t} : Quiet t → ConfigCopies sysroot project tree copies prior t
  /-- A failed configuration-copy step permits no further acts. -/
  | failed {path text copies prior before step rest} : Quiet before → CopyStep tree path text step false →
      Quiet rest → ConfigCopies sysroot project tree ((path, text) :: copies) prior (before ++ step ++ rest)
  /-- A completed copy advances to the remaining configuration steps. -/
  | next {path text copies prior before step rest} : Quiet before → CopyStep tree path text step true →
      ConfigCopies sysroot project tree copies (prior ++ before ++ step) rest →
      ConfigCopies sysroot project tree ((path, text) :: copies) prior (before ++ step ++ rest)

/-- The reading phase's complete ordered acts. Configuration text comes from an earlier read of the
requested project; the second copy is the pinned toolchain text. The remaining copies are precisely
steps of named module files with earlier source reads. No act is allowed before the first copy. What the
acts leave standing is `Decided`'s statement, through `written`. -/
def ReadingPreparation (t : List (Event L E)) (dir treeDir : FilePath) : Prop :=
  Quiet t ∨ ∃ project tree sysroot text before rest,
    t = before ++ rest ∧ Quiet before ∧
    (⟨.realPath dir, .ok project⟩ : Event L E) ∈ before ∧
    (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ before ∧ SysrootIs before sysroot ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ before ∧
    ConfigCopies sysroot project tree [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)]
      before rest

/-- The loaded build's search path is installed before every lookup or rules import, with no later
setter. A load that stops before those consumers needs no setter. -/
def InputPreparation (root : Root L) (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before rest, t = before ++ ⟨.setSearchPath root.leanPath, ()⟩ :: rest ∧ Quiet before ∧
    ∀ e ∈ rest, QuietOp e.op ∨ RulesSearchOp e.op

/-- Reloading the finished tree: one load of the real path received for that tree, followed only by
observations or the loaded root's prepared input phase. -/
def RulesPreparation (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before real response rest,
    t = before ++ ⟨.loadRoot sysroot real, response⟩ :: rest ∧ Quiet before ∧
    (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ∧
    match response with
    | .ok (some root, _) => InputPreparation root rest
    | _ => Quiet rest

/-- The proof verdict loads the requested current workspace on the received toolchain, then installs
that load's search path before any lookup or import. No other setter or load is allowed. -/
def PlainPreparation (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before sysroot dir response rest,
    t = before ++ ⟨.loadWorkspace sysroot dir, response⟩ :: rest ∧ Quiet before ∧
    SysrootIs before sysroot ∧ (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ before ∧
    match response with
    | .ok (some root, _) => InputPreparation root rest
    | _ => Quiet rest

/-- Relevance to the requested build: its observations and copies, and each needed name's file or place
in the toolchain. This relation alone does not order events. `FullRun` also requires `ReadingPreparation`
on the exact reading phase, so a relevant failed copy or search has its preparation at that occurrence.
Configuration loads use `PreparedLoad` separately. An operation outside these cases justifies nothing. -/
inductive Needed (t : List (Event L E)) (dir treeDir : FilePath) : Op L E → Prop where
  /-- The toolchain. -/
  | sysroot : Needed t dir treeDir (.getEnv "LEAN_SYSROOT")
  /-- What Lake gave as the search path, which says who started the run. -/
  | searchPath : Needed t dir treeDir (.getEnv "LEAN_PATH")
  /-- The project. -/
  | project : Needed t dir treeDir (.realPath dir)
  /-- The checker's tree. -/
  | tree : Needed t dir treeDir (.realPath treeDir)
  /-- This program, to tell the start from outside. -/
  | app : Needed t dir treeDir .appPath
  /-- Its real path. -/
  | appReal {app} : (⟨.appPath, .ok app⟩ : Event L E) ∈ t → Needed t dir treeDir (.realPath app)
  /-- Whether `lakefile.lean` exists. -/
  | leanConfig {project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.symlinkMetadata (project / "lakefile.lean"))
  /-- The real path of `lakefile.toml`. -/
  | tomlReal {project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.realPath (project / "lakefile.toml"))
  /-- The text of `lakefile.toml`. -/
  | tomlRead {project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.readFile (project / "lakefile.toml"))
  /-- Lake's parser, on that text. -/
  | tomlParse {project text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.parseToml (mkInputContext text "lakefile.toml"))
  /-- The directory above a copy of the configuration in the tree. -/
  | copyParent {tree path d} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") → path.parent = some d →
      Needed t dir treeDir (.createDirAll d)
  /-- The copy of `lakefile.toml` in the tree, of the text read. -/
  | copyToml {project tree text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.writeFile (tree / "lakefile.toml") text)
  /-- The tree's `lean-toolchain`. -/
  | copyToolchain {tree} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.writeFile (tree / "lean-toolchain") leanToolchain)
  /-- The modules of a default library. -/
  | library {tree root target lib} : TreeLoaded t dir treeDir tree root → target ∈ root.defaultTargets →
      root.findLib target = some lib → Needed t dir treeDir (.libModules lib)
  /-- A directory of the toolchain's library. -/
  | toolchainDir {tree root d} : TreeLoaded t dir treeDir tree root → d ∈ root.toolchain →
      Needed t dir treeDir (.realPath d)
  /-- Whether anything has the name that Lake prefers as its configuration, in the tree. -/
  | treeLeanConfig {tree} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.symlinkMetadata (tree / "lakefile.lean"))
  /-- Where Lean finds a name the build needs that no file of the project holds. -/
  | search {project tree root modules m} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → modules.lookup m = none → root.resolve m = none →
      Needed t dir treeDir (.findOLean m)
  /-- The real path of what Lean found. -/
  | oleanReal {project tree root modules m olean} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → modules.lookup m = none → root.resolve m = none →
      (⟨.findOLean m, .ok olean⟩ : Event L E) ∈ t → Needed t dir treeDir (.realPath olean)
  /-- The real path of the project's file of a name the build needs. -/
  | sourceReal {project tree root modules m path rel} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      TreeRelative (parts tree) (parts path) rel → Needed t dir treeDir (.realPath (under project rel))
  /-- Its text. -/
  | sourceRead {project tree root modules m path rel} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      TreeRelative (parts tree) (parts path) rel → Needed t dir treeDir (.readFile (under project rel))
  /-- The directory above its copy in the tree. -/
  | sourceParent {project tree root modules m path d} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path → path.parent = some d →
      Needed t dir treeDir (.createDirAll d)
  /-- Its copy in the tree, of the text read. -/
  | sourceWrite {project tree root modules m path text} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      SourceText t project tree path text → Needed t dir treeDir (.writeFile path text)
  /-- Lean's header parser, on the text read. -/
  | sourceHeader {project tree root modules m path text} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      SourceText t project tree path text →
      Needed t dir treeDir (.parseHeader (mkInputContext text (Regula.Load.inputName path)))
  /-- The import for Lean's parser, of names the build needs that the toolchain holds. -/
  | parser {project tree root modules mods} : Scene t dir treeDir project tree root modules →
      (∀ n ∈ mods, Named t project tree root modules n ∧ HeldByToolchain t root n) →
      Needed t dir treeDir (.importForParser mods)

/-- What the text of `lakefile.toml` of the project at `dir` gave Lake's parser. -/
def TomlRead (t : List (Event L E)) (dir : FilePath) (table : Lake.Toml.Table) : Prop :=
  ∃ project text, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t ∧
    (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t

/-- A text that an admission would have the tree hold at `path`, by what the run read: the configuration's, the pinned
`lean-toolchain`, or a needed name's file. -/
inductive Planned (t : List (Event L E)) (project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) : FilePath → String → Prop where
  /-- The text read of `lakefile.toml`. -/
  | toml {text} : (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t →
      Planned t project tree root modules (tree / "lakefile.toml") text
  /-- The pinned text. -/
  | toolchain : Planned t project tree root modules (tree / "lean-toolchain") leanToolchain
  /-- The text read of a needed name's file. -/
  | source {m path text} : Named t project tree root modules m → FileOfModule root modules m path →
      SourceText t project tree path text → Planned t project tree root modules path text

/-- What may keep the requested project from admission, with the outcome each response justifies.
`Needed` supplies relevance; `FullRun` separately requires preparation at every occurrence in this same
reading phase. Thus a `Reason` by itself is not a complete refusal contract. Successful and failed copy,
load and search attempts all obey that phase's ordered acts, without assuming consistent responses. -/
inductive Reason (t : List (Event L E)) (dir treeDir : FilePath) : Outcome → Prop where
  /-- An operation that the build needs failed. -/
  | failed {e : Event L E} : e ∈ t → Needed t dir treeDir e.op → e.failed → Reason t dir treeDir .incomplete
  /-- Lake failed on the requested project's copied configuration, with both copies already complete. -/
  | load {sysroot tree response} : PreparedLoad t dir treeDir sysroot tree response →
      Event.failed (⟨.loadRoot sysroot tree, response⟩ : Event L E) → Reason t dir treeDir .incomplete
  /-- The toolchain's file names another Lean. -/
  | toolchain {project text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t →
      text.trimAscii.toString ≠ leanToolchain → Reason t dir treeDir .refused
  /-- The toolchain's file failed its read. -/
  | toolchainFailed {project e} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .error e⟩ : Event L E) ∈ t → Reason t dir treeDir .refused
  /-- The toolchain's file failed the exact-path test. -/
  | toolchainNotExact {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t →
      Regula.Load.exactBelow project (project / "lean-toolchain") real = false →
      Reason t dir treeDir .refused
  /-- The toolchain's real path failed. -/
  | toolchainNoReal {project e} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .error e⟩ : Event L E) ∈ t → Reason t dir treeDir .refused
  /-- This program was not started from outside the project, by the responses that say where it lies and which
  Lake started it. -/
  | started {project sysroot program lakeLib app real leanPath} :
      (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t → SysrootIs t sysroot →
      (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
      (⟨.appPath, .ok app⟩ : Event L E) ∈ t → (⟨.realPath app, .ok real⟩ : Event L E) ∈ t →
      (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t →
      (Regula.Load.below project real = true ∨
        ∀ own, (real.parent.bind (·.parent)).map (· / "lib" / "lean") = some own →
          Regula.Load.dispatchedFrom own.toString lakeLib.toString
            ((System.SearchPath.parse leanPath).map toString) = false) →
      Reason t dir treeDir .incomplete
  /-- `lakefile.toml` crossed a link, or lies outside the project. -/
  | tomlNotExact {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ t →
      Regula.Load.exactBelow project (project / "lakefile.toml") real = false →
      Reason t dir treeDir .incomplete
  /-- The project and the checker's tree do not lie apart. -/
  | notApart {project tree} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t → ¬ Apart project tree →
      Reason t dir treeDir .incomplete
  /-- A file of the configuration does not lie below the tree: nothing is written there. -/
  | configNotInTree {tree path} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") → OutsideTree tree path →
      Reason t dir treeDir .incomplete
  /-- The file that Lake names for a name the build needs, or a directory above it, does not lie below the tree: nothing
  is written there. -/
  | moduleNotInTree {project tree root modules m path} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path → OutsideTree tree path →
      Reason t dir treeDir .incomplete
  /-- The project's file of a name the build needs crossed a link, or lies outside the project. -/
  | moduleNotExact {project tree root modules m path rel real} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      TreeRelative (parts tree) (parts path) rel →
      (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t →
      Regula.Load.exactBelow project (under project rel) real = false →
      Reason t dir treeDir .incomplete
  /-- A `lakefile.lean` exists. -/
  | leanConfig {project metadata} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (project / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t →
      Reason t dir treeDir .refused
  /-- A key of the project's `lakefile.toml` outside the closed set. -/
  | key {table k} : TomlRead t dir table → KeyPath .anonymous table k → k.getRoot ≠ `require →
      ¬ ConfigKeyAdmitted k → Reason t dir treeDir .refused
  /-- A project's `lakefile.toml` deeper than the reader follows. -/
  | deep {table} : TomlRead t dir table → Deeper 8 table → Reason t dir treeDir .refused
  /-- A dependency in a `lakefile.toml` deeper than the reader follows. -/
  | deepDependency {table} : TomlRead t dir table → Deeper 8 table → Reason t dir treeDir .proofOnly
  /-- A dependency in the project's `lakefile.toml`. -/
  | dependency {table k} : TomlRead t dir table → KeyPath .anonymous table k → k.getRoot = `require →
      Reason t dir treeDir .proofOnly
  /-- A source directory outside the tree. -/
  | openDir {tree root d} : TreeLoaded t dir treeDir tree root → d ∈ root.sourceDirs →
      (∀ rel, ¬ TreeRelative (parts tree) (parts d) rel) → Reason t dir treeDir .refused
  /-- A `globs` entry that is no single module. -/
  | openGlob {tree root lib g} : TreeLoaded t dir treeDir tree root → lib ∈ root.libraries →
      g ∈ lib.2 → (∀ n, g ≠ .one n) → Reason t dir treeDir .refused
  /-- No module is claimed. -/
  | noClaim {project tree root} : Scene t dir treeDir project tree root [] → Reason t dir treeDir .incomplete
  /-- A target's name outside the closed domain. -/
  | targetName {tree root n} : TreeLoaded t dir treeDir tree root → n ∈ root.targets →
      ¬ ClosedModuleName n → Reason t dir treeDir .incomplete
  /-- A default root whose name Lake's import resolution gives another file for, by components: two spellings of one path are
  one file. -/
  | twoFiles {project tree root modules m file other} : Scene t dir treeDir project tree root modules →
      (m, file) ∈ modules → root.resolve m = some other → parts other ≠ parts file → Reason t dir treeDir .incomplete
  /-- Two default targets that hold one module name with two files, by components: two spellings of one path are one file. -/
  | twoRoots {project tree root modules m file other} : Scene t dir treeDir project tree root modules →
      (m, file) ∈ modules → (m, other) ∈ modules → parts other ≠ parts file → Reason t dir treeDir .incomplete
  /-- Something answers to `lakefile.lean` in the tree, which Lake prefers to the configuration judged: a file of the plan that
  the file system takes for that name has a second role, so no admission could be about what Lake takes as its configuration. -/
  | configShadowed {tree metadata} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (tree / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → Reason t dir treeDir .incomplete
  /-- A planned file written with its text answers otherwise, by the same path, after that write: another read gave another text,
  or the read failed. A file that another spelling of a path replaced with another text shows up here. The order keeps a run from citing a read it
  asked before it wrote, and `Planned` from citing a text it read from nowhere. -/
  | treeDiffers {project tree root modules path text r} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text →
      ([⟨.writeFile path text, .ok ()⟩, ⟨.readFile path, r⟩] : List (Event L E)).Sublist t → r ≠ .ok text →
      Reason t dir treeDir .incomplete
  /-- What an admission would have the tree hold is two texts at one path: another read gave a needed file another text, or
  a needed file lies at the path of the configuration or of `lean-toolchain` with another text. The tree can hold one, so no
  admission could be about what the build consumes under each name. -/
  | twoTexts {project tree root modules path text path' text'} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text → Planned t project tree root modules path' text' →
      parts path = parts path' → text ≠ text' → Reason t dir treeDir .incomplete
  /-- A name the build needs outside the closed domain. -/
  | moduleName {project tree root modules m} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → ¬ ClosedModuleName m → Reason t dir treeDir .incomplete
  /-- An import, by a file the build needs, of a default executable's root that no library holds. -/
  | importedRoot {project tree root modules m imports i} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → HeaderOf t project tree root modules m imports → i ∈ imports →
      (modules.lookup i.module).isSome = true → root.resolve i.module = none → Reason t dir treeDir .incomplete
  /-- A name the build needs that no file of the project holds, whose `.olean` does not lie below the toolchain's library. -/
  | notToolchain {project tree root modules m olean real} {reals : List (FilePath × FilePath)} :
      Scene t dir treeDir project tree root modules → Named t project tree root modules m →
      modules.lookup m = none → root.resolve m = none →
      (⟨.findOLean m, .ok olean⟩ : Event L E) ∈ t → (⟨.realPath olean, .ok real⟩ : Event L E) ∈ t →
      reals.map Prod.fst = root.toolchain →
      (∀ x ∈ reals, (⟨.realPath x.1, .ok x.2⟩ : Event L E) ∈ t ∧ Regula.Load.below x.2 real = false) →
      Reason t dir treeDir .incomplete
  /-- The roots, and the imports of distinct files that the build needs, are more names than the reader follows. -/
  | tooMany {project tree root modules} {ms : List (Name × Array Import)} :
      Scene t dir treeDir project tree root modules → (ms.map (·.1)).Nodup →
      (∀ x ∈ ms, Named t project tree root modules x.1 ∧ HeaderOf t project tree root modules x.1 x.2) →
      1000000 < modules.length + (ms.map (·.2.size)).sum → Reason t dir treeDir .incomplete
  /-- Mathlib is in what the build needs. -/
  | mathlib {project tree root modules m} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → m.getRoot = `Mathlib → Reason t dir treeDir .proofOnly
  /-- The file of a name the build needs, read as Lean reads it in the context that the file sees, is not in the closed
  language. -/
  | file {project tree root modules f path imports mods} {headers : List (Name × Array Import)} {held : List Name} :
      Scene t dir treeDir project tree root modules → Named t project tree root modules f.module →
      FileOfModule root modules f.module path → ReadAs t project tree f path imports mods →
      (∀ x ∈ headers, HeaderOf t project tree root modules x.1 x.2) →
      (∀ n ∈ held, Named t project tree root modules n ∧ HeldByToolchain t root n) →
      (∀ i ∈ imports, i.module ∈ held ∨ (headers.lookup i.module).isSome = true) →
      (∀ x ∈ headers, ∀ i ∈ x.2, i.module ∈ held ∨ (headers.lookup i.module).isSome = true) →
      (∀ n, n ∈ mods ↔ ∃ m ∈ imports, Sees headers held m.module n) →
      ¬ FileAdmitted f → Reason t dir treeDir .refused

/-- The outcome `o` of the language check is what its reading gives. An admitted project rests on `Evidence` of the state
`written t` that the whole reading leaves, so an admission is about the text that stands and not about one that a later
write replaced, and on `ReadBack`, so each text credited is what the file system answered after the reading's last act, and
nothing answers to the name that Lake prefers to the configuration judged. Any other outcome rests on a `Reason`. -/
def Decided (t : List (Event L E)) (dir tree : FilePath) (o : Outcome) : Prop :=
  (o = .admitted → ∃ r real, Inside r ∧ Evidence t dir tree (written t) r ∧ (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧ ReadBack t real) ∧
    (o ≠ .admitted → Reason t dir tree o) ∧
    ((∃ r, o = decision r) ∨ o = .incomplete)

/-- What a finished build gave the rules, by this run's responses. `root` is the workspace that Lake's load
gave. -/
def BuildRead (t : List (Event L E)) (root : Root L) (f : Regula.Load.Facts) (roots : List Name) : Prop :=
  ∃ modules,
    DefaultModules t root root.defaultTargets modules ∧ roots = modules.map (·.1) ∧
    ([⟨.setSearchPath root.leanPath, ()⟩, ⟨.importForRules roots.toArray, .ok f.env⟩] :
      List (Event L E)).Sublist t ∧
    f.toolchainDir = root.leanLib ∧ f.rootDir = root.rootLib ∧
    ∀ m ∈ f.modules, (⟨.findOLean m.name, .ok m.olean⟩ : Event L E) ∈ t

/-- Lake's load of the workspace that Lake dispatched from the current directory, on the run's toolchain: the root that the
run read, on the search path that Lake gave it, which names that workspace. -/
def PlainRoot (t : List (Event L E)) (root : Root L) : Prop :=
  ∃ (sysroot : String) (dir : FilePath) (log : List String) (leanPath : String) (lakeLib program : FilePath),
    SysrootIs t sysroot ∧
    (⟨.loadWorkspace sysroot dir, .ok (some root, log)⟩ : Event L E) ∈ t ∧
    (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ t ∧
    (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t ∧
    (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t ∧
    Regula.Load.dispatchedFrom root.rootLib.toString lakeLib.toString
      ((System.SearchPath.parse leanPath).map toString) = true

/-- Lake's load of the root package in the checker's tree, on the run's toolchain `sysroot`. -/
def TreeRoot (sysroot : String) (tree : FilePath) (t : List (Event L E)) (root : Root L) : Prop :=
  ∃ (real : FilePath) (log : List String),
    (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧
    (⟨.loadRoot sysroot real, .ok (some root, log)⟩ : Event L E) ∈ t

/-- An operation that the load of the finished build of the workspace `root` needs failed: the modules of a default
library, the import of the modules of the default targets, or where Lean finds a module of that import. -/
inductive BuildFailed (t : List (Event L E)) (root : Root L) : Prop where
  /-- The modules of a default library. -/
  | library {target lib e} : target ∈ root.defaultTargets → root.findLib target = some lib →
      (⟨.libModules lib, .error e⟩ : Event L E) ∈ t → BuildFailed t root
  /-- The import of the modules of the default targets. -/
  | import {modules e} : DefaultModules t root root.defaultTargets modules →
      (⟨.importForRules (modules.map (·.1)).toArray, .error e⟩ : Event L E) ∈ t → BuildFailed t root
  /-- Where Lean finds a module of that import. -/
  | search {modules env m e} : DefaultModules t root root.defaultTargets modules →
      (⟨.importForRules (modules.map (·.1)).toArray, .ok env⟩ : Event L E) ∈ t →
      m ∈ env.header.moduleNames → (⟨.findOLean m, .error e⟩ : Event L E) ∈ t → BuildFailed t root

/-- What may keep a run of the proof verdict from reading the finished build of the workspace that Lake dispatched: each
case is what a response said about an operation that this load needs. -/
inductive PlainReason (t : List (Event L E)) : Prop where
  /-- `LEAN_SYSROOT` is not set, so the toolchain of the build is not known. -/
  | noSysroot : (⟨.getEnv "LEAN_SYSROOT", none⟩ : Event L E) ∈ t → PlainReason t
  /-- The current directory has no real path. -/
  | noDirectory {e} : (⟨.realPath ".", .error e⟩ : Event L E) ∈ t → PlainReason t
  /-- Lake's load of the workspace there, on the run's toolchain, failed. -/
  | load {sysroot dir r} : SysrootIs t sysroot → (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ t →
      (⟨.loadWorkspace sysroot dir, r⟩ : Event L E) ∈ t → Event.failed (⟨.loadWorkspace sysroot dir, r⟩ : Event L E) →
      PlainReason t
  /-- `LEAN_PATH` is not set, so the workspace that Lake dispatched is not known. -/
  | noSearchPath : (⟨.getEnv "LEAN_PATH", none⟩ : Event L E) ∈ t → PlainReason t
  /-- The current directory is not the workspace Lake dispatched. -/
  | elsewhere {sysroot dir root log leanPath program lakeLib} : SysrootIs t sysroot →
      (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ t →
      (⟨.loadWorkspace sysroot dir, .ok (some root, log)⟩ : Event L E) ∈ t →
      (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
      (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t →
      Regula.Load.dispatchedFrom root.rootLib.toString lakeLib.toString
        ((System.SearchPath.parse leanPath).map toString) = false → PlainReason t
  /-- The load of the finished build of that workspace failed. -/
  | build {root} : PlainRoot t root → BuildFailed t root → PlainReason t

/-- What may keep the full gate from reading the finished build in the checker's tree, on the toolchain `sysroot`. -/
inductive TreeReason (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop where
  /-- The tree has no real path. -/
  | noTree {e} : (⟨.realPath tree, .error e⟩ : Event L E) ∈ t → TreeReason sysroot tree t
  /-- Lake's load of the tree failed. -/
  | load {real r} : (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t → (⟨.loadRoot sysroot real, r⟩ : Event L E) ∈ t →
      Event.failed (⟨.loadRoot sysroot real, r⟩ : Event L E) → TreeReason sysroot tree t
  /-- The load of the finished build failed. -/
  | build {root} : TreeRoot sysroot tree t root → BuildFailed t root → TreeReason sysroot tree t

/-- The load's result is what the proved pure function gives on what Lean and Lake returned for the requested build, or an
error for a reason `why` gives, which `PlainReason` and `TreeReason` close. `Regula.Load.Facts.input` is that function,
and `gave` says which of Lake's loads gave the root. -/
def Loaded (gave : List (Event L E) → Root L → Prop) (why : List (Event L E) → Prop) (t : List (Event L E))
    (p : Regula.Closed.Profile) (result : Except String Regula.Closed.Input) : Prop :=
  (∃ root f roots, gave t root ∧ BuildRead t root f roots ∧ result = f.input roots p) ∨
    (why t ∧ ∃ message, result = .error message)

/-- A line that is no verdict: two spaces start it. -/
def IsDetail (l : String) : Prop :=
  ∃ s, l = "  " ++ s

/-- The last event requests one physical line, and every physical line requested by earlier `println`
calls starts with two spaces. No earlier requested line can be read as the final verdict. -/
def EndsWith (t : List (Event L E)) (line : String) : Prop :=
  ∃ pre r, t = pre ++ [⟨.println line, r⟩] ∧ '\n' ∉ line.toList ∧ ∀ l ∈ printed pre, IsDetail l

/-- A run with a Lean or arguments that the checker does not read: only says so. -/
def Refusal (t : List (Event L E)) (c : UInt32) : Prop :=
  c = 2 ∧ EndsWith t (Regula.Closed.Verdict.proofLine .incomplete) ∧ ∀ e ∈ t, e.isOnlySaying = true

/-- A run of the proof verdict: its exit code and last line are the verdict's on what the load gave, and it
acts on nothing. A run that exits with 0 received no failed answer. -/
def PlainRun (t : List (Event L E)) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  ∃ result, Loaded PlainRoot PlainReason t p result ∧
    c = (Regula.Closed.decision result).verdict.exitCode ∧
    EndsWith t (Regula.Closed.decision result).verdict.proofLine ∧
    (∀ e ∈ t, e.acted? = none) ∧ (c = 0 → ∀ e ∈ t, ¬ e.failed) ∧ PlainPreparation t

/-- Every act of a run lies in the tree: either the run acted only on the
tree it was given, or it read their real paths and each act lies at or below the tree's. -/
def Confined (t : List (Event L E)) (dir tree : FilePath) : Prop :=
  (∀ e ∈ t, ∀ path, e.acted? = some path → path = tree) ∨
    ∃ project real, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧ Apart project real ∧
      ∀ e ∈ t, ∀ path, e.acted? = some path → path = tree ∨ AtOrBelow real path

/-- The arguments of Lean's replay of a build, as this platform needs them (`lake check`). -/
def replayArguments : List String :=
  if System.Platform.isOSX then ["check", "--inadvisably-no-sandbox"] else ["check"]

/-- One requested Lake command, with only reporting before and after its occurrence. No explicit
filesystem mutation or extra command request can be inserted around it in this segment. -/
def LakeInvocation (program tree : FilePath) (args : List String) (response : Except IO.Error UInt32)
    (t : List (Event L E)) : Prop :=
  ∃ pre post, t = pre ++ ⟨.runLake program tree args, response⟩ :: post ∧
    (∀ e ∈ pre, e.isOnlySaying = true) ∧ ∀ e ∈ post, e.isOnlySaying = true

/-- The complete build phase: obtain this toolchain's Lake, build once, and replay once exactly when the
build succeeded. No unlisted effect fits between those operations. This constrains Regula's requests,
not the filesystem effects of the trusted Lake commands. -/
def BuildProtocol (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop :=
  ∃ program lakeLib first rest response,
    t = ⟨.lakeInstall sysroot, (program, lakeLib)⟩ :: (first ++ rest) ∧
    LakeInvocation program tree ["build", "--wfail"] response first ∧
    ((response ≠ .ok 0 ∧ rest = []) ∨
      (response = .ok 0 ∧ ∃ replay, LakeInvocation program tree replayArguments replay rest))

/-- The reload and rule phase issues no explicit write, directory creation, allocation, removal or
command request. `RulesPreparation` additionally orders its load and search-path setter; effects inside trusted calls
remain outside the trace.
The cases are the closed effect type, rather than a list of remembered call sites. -/
def ReloadOp : Op L E → Prop
  | .leanVersion | .getEnv _ | .appPath | .realPath _ | .readFile _ | .symlinkMetadata _
  | .println _ | .flush | .parseHeader _ | .parseCommand .. | .setSearchPath _ | .findOLean _
  | .importForRules _ | .importForParser _ | .parseToml _ | .lakeInstall _ | .loadWorkspace ..
  | .loadRoot .. | .libModules _ => True
  | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ | .runLake .. => False

/-- The build or its replay in the tree `tree` ended with other than 0, with the Lake that lies beside the run's toolchain:
each is an operation that the requested build needs, and what the response says of it justifies a failure. -/
inductive BuildRejected (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop where
  /-- The build. -/
  | build {program lakeLib r} : (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
      (⟨.runLake program tree ["build", "--wfail"], r⟩ : Event L E) ∈ t → r ≠ .ok 0 →
      BuildRejected sysroot tree t
  /-- The replay, of a build that ended with 0. -/
  | replay {program lakeLib r} : (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
      (⟨.runLake program tree ["build", "--wfail"], .ok 0⟩ : Event L E) ∈ t →
      (⟨.runLake program tree replayArguments, r⟩ : Event L E) ∈ t → r ≠ .ok 0 →
      BuildRejected sysroot tree t

/-- The exact build/replay protocol and the report justified by their responses or the rules. Neither
phase may explicitly alter the copied inputs. `RulesPreparation` directs the reload by the tree's
real-path response and sets the loaded root's search path before every rules import or lookup, failed
attempts included. These are request guarantees, not assumptions about effects inside Lake. -/
def BuildAndRules (sysroot : String) (tBuild tRules : List (Event L E)) (tree : FilePath) (p : Regula.Closed.Profile)
    (report : Report) : Prop :=
  BuildProtocol sysroot tree tBuild ∧ (∀ e ∈ tRules, ReloadOp e.op) ∧
  ((∃ (program lakeLib : FilePath) (result : Except String Regula.Closed.Input),
    (∀ e ∈ tRules, e.isBuild = false) ∧
    ([⟨.lakeInstall sysroot, (program, lakeLib)⟩, ⟨.runLake program tree ["build", "--wfail"], .ok 0⟩,
      ⟨.runLake program tree replayArguments, .ok 0⟩] : List (Event L E)).Sublist tBuild ∧
    Loaded (TreeRoot sysroot tree) (TreeReason sysroot tree) tRules p result ∧
    report = .full (Regula.Closed.decision result).verdict) ∨
  (report = .full .fail ∧ (∀ e ∈ tRules, e.isImportForRules = false) ∧ BuildRejected sysroot tree tBuild)) ∧
  RulesPreparation sysroot tree tRules

/-- An operation does not remove a directory. This excludes removal even when it reports an error:
an unsuccessful external removal may already have removed some files. -/
def NotRemoving : Op L E → Prop
  | .removeDirAll _ => False
  | _ => True

/-- A full run on `dir`: relevance and ordered preparation hold together on the exact reading phase.
The TOML copy precedes the pinned toolchain copy and configuration load; named module copies use earlier
source reads. Each copy makes only its own parent before writing, and each search consumer follows its
load's setter. Failed attempts obey the same order. An admission rests on `Evidence` of the state the reading
leaves. Build, replay and rules follow only an admission, with no later explicit copy or early removal, so no
request of theirs changes that state (`FullRun.at_consumer`). Cleanup is terminal and every act is confined to the tree.
Exit code and last line are the report's alone; exit 0 received no failed answer. All responses remain
arbitrary, including inconsistent filesystem answers and opaque effects inside trusted calls. -/
def FullRun (t : List (Event L E)) (dir : FilePath) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  -- No temporary directory.
  (∃ e rest, t = ⟨.createTempDir, .error e⟩ :: rest ∧ c = Report.incomplete.exitCode ∧
    EndsWith t Report.incomplete.label ∧ ∀ e ∈ rest, e.isOnlySaying = true) ∨
  ∃ (tree : FilePath) (tRead tGate : List (Event L E)) (r : Except IO.Error Unit) (last : List (Event L E)),
    t = ⟨.createTempDir, .ok tree⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last ∧
    (∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false) ∧ (∀ e ∈ last, e.isOnlySaying = true) ∧
    ∃ (o : Outcome) (report : Report), Decided tRead dir tree o ∧
      -- On an admission, no answer to what the reader asked failed.
      (o = .admitted → ∀ e ∈ tRead, ¬ e.failed) ∧
      (o ≠ .admitted → tGate = [] ∧ report = (match o with
        | .refused => Report.refused
        | .proofOnly => Report.proofOnly
        | _ => Report.incomplete)) ∧
      (o = .admitted → ∃ sysroot tBuild tRules, SysrootIs tRead sysroot ∧ tGate = tBuild ++ tRules ∧
        BuildAndRules sysroot tBuild tRules tree p report) ∧
      c = report.exitCode ∧ EndsWith t report.label ∧ Confined t dir tree ∧
      (c = 0 → ∀ e ∈ t, ¬ e.failed) ∧ (∀ e ∈ tRead, NotRemoving e.op) ∧ ReadingPreparation tRead dir tree

/-- On the one Lean that this revision reads, what the run states; on any other, a refusal. The run asks first which
Lean it is. -/
def OnPinnedLean (t : List (Event L E)) (run : List (Event L E) → Prop) (c : UInt32) : Prop :=
  ∃ v rest, t = ⟨.leanVersion, v⟩ :: rest ∧ (v = Regula.Closed.pinnedLean → run t) ∧
    (v ≠ Regula.Closed.pinnedLean → Refusal t c)

/-- What a whole run does, for each argument list: a subject is a program of the checker. -/
def RunMeets (w : List String → Prog L E UInt32) : Prop :=
  ∀ args t c, Runs (w args) t c →
    match args with
    | [text] =>
      match Regula.Closed.Profile.ofSpelling? text with
      | some p => OnPinnedLean t (fun t => PlainRun t p c) c
      | none => Refusal t c
    | [text, "full", dir] =>
      match Regula.Closed.Profile.ofSpelling? text with
      | some p => OnPinnedLean t (fun t => ∃ rest v, t = ⟨.leanVersion, v⟩ :: rest ∧
          FullRun rest (FilePath.mk dir) p c) c
      | none => Refusal t c
    | _ => Refusal t c

/-- The record of the checker's run, for the types `L` and `E` that it passes on and never reads. The subject is a
program, so the properties hold of every response that a program can receive. It is a design of the agents, derived
from the owner's account (`confirmation.md`), and no statement of the owner's. -/
def programRecord (L E : Type) : LeanIntent.IntentRecord (List String → Prog L E UInt32) where
  shape := .function (List String) (fun _ => Prog L E UInt32)
  dom := []
  props := [
    ⟨"a run does what its arguments ask, on every response, and it refuses what it cannot read", RunMeets⟩]
  vocab := [
    ⟨"a line that is no verdict", String, IsDetail⟩,
    ⟨"a project wholly inside the closed language", Reading, Inside⟩]

end RegulaSpecification.Effects
