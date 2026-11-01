/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import RegulaSpecification.EffectsRun

/-!
# The record of a run

`Reason` is the closed set of what may keep a project from being admitted: each case is what a response said,
so a reader that refuses a project without such a reason is no behaviour the record allows. `programRecord`
states a whole run, for every response, and it is the contract that `Regula.Shell.run` is proved against.
-/

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

/-- A table with a chain of more than `n` nested tables, which the reader does not follow. -/
inductive Deeper : Nat → Lake.Toml.Table → Prop where
  /-- Any table is deeper than nothing. -/
  | zero {t} : Deeper 0 t
  /-- Through a table that holds a key. -/
  | table {n k r sub t} : (k, Lake.Toml.Value.table r sub) ∈ t.items → sub.items.isEmpty = false →
      Deeper n sub → Deeper (n + 1) t
  /-- Through a table in an array that holds a key. -/
  | array {n k r xs r' sub t} : (k, Lake.Toml.Value.array r xs) ∈ t.items →
      Lake.Toml.Value.table r' sub ∈ xs → sub.items.isEmpty = false → Deeper n sub → Deeper (n + 1) t

/-- How many imports the header of an event states. -/
def Event.importsStated : Event L E → Nat
  | ⟨.parseHeader _, .ok (_, _, _, imports)⟩ => imports.size
  | _ => 0

/-- How many imports the headers of a run state. -/
def importCount (t : List (Event L E)) : Nat :=
  (t.map Event.importsStated).sum

/-- A name the reader reaches: a module of a default target, or what a header it read imports. -/
def Named (t : List (Event L E)) (modules : List (Name × FilePath)) (m : Name) : Prop :=
  m ∈ modules.map (·.1) ∨
    ∃ input header state messages imports,
      (⟨.parseHeader input, .ok (header, state, messages, imports)⟩ : Event L E) ∈ t ∧
      ∃ i ∈ imports, i.module = m

/-- A path, or the directory above it, does not lie below the tree by `TreeRelative`. -/
def OutsideTree (tree path : FilePath) : Prop :=
  (∀ rel, ¬ TreeRelative (parts tree) (parts path) rel) ∨
    ∃ d, path.parent = some d ∧ ∀ rel, ¬ TreeRelative (parts tree) (parts d) rel

/-- What may keep the project at `dir` from being admitted. Each case is what a response of the run said, and
it gives the one outcome that it may. -/
inductive Reason (t : List (Event L E)) (dir : FilePath) : Outcome → Prop where
  /-- An answer to what the reader asks failed. -/
  | failed {e : Event L E} : e ∈ t → e.failedRead → Reason t dir .incomplete
  /-- LEAN_SYSROOT is not set, so the toolchain is not known. -/
  | noSysroot : (⟨.getEnv "LEAN_SYSROOT", none⟩ : Event L E) ∈ t → Reason t dir .incomplete
  /-- LEAN_PATH is not set, so the start cannot be told. -/
  | noSearchPath : (⟨.getEnv "LEAN_PATH", none⟩ : Event L E) ∈ t → Reason t dir .incomplete
  /-- The toolchain's file names another Lean. -/
  | toolchain {project text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t →
      text.trimAscii.toString ≠ leanToolchain → Reason t dir .refused
  /-- The toolchain's file failed its read. -/
  | toolchainFailed {project e} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .error e⟩ : Event L E) ∈ t → Reason t dir .refused
  /-- The toolchain's file failed the exact-path test. -/
  | toolchainNotExact {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t →
      Regula.Load.exactBelow project (project / "lean-toolchain") real = false → Reason t dir .refused
  /-- The toolchain's real path failed. -/
  | toolchainNoReal {project e} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .error e⟩ : Event L E) ∈ t → Reason t dir .refused
  /-- This program was not started from outside the project, by the responses that say where it lies and which
  Lake started it. -/
  | started {project sysroot program lakeLib app real leanPath} :
      (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
      (⟨.appPath, .ok app⟩ : Event L E) ∈ t → (⟨.realPath app, .ok real⟩ : Event L E) ∈ t →
      (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t →
      (Regula.Load.below project real = true ∨
        ∀ own, (real.parent.bind (·.parent)).map (· / "lib" / "lean") = some own →
          Regula.Load.dispatchedFrom own.toString lakeLib.toString
            ((System.SearchPath.parse leanPath).map toString) = false) →
      Reason t dir .incomplete
  /-- A project's file crossed a link, or lies outside the project. -/
  | notExact {path real project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath path, .ok real⟩ : Event L E) ∈ t →
      Regula.Load.exactBelow project path real = false → Reason t dir .incomplete
  /-- A file that Lake names, or a directory above it, does not lie below the tree: nothing is written there. -/
  | configNotInTree {tree treePath path} : (⟨.realPath treePath, .ok tree⟩ : Event L E) ∈ t →
      (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") → OutsideTree tree path →
      Reason t dir .incomplete
  /-- A file that Lake names, or a directory above it, does not lie below the tree: nothing is written there. -/
  | moduleNotInTree {tree treePath sysroot root log modules m path} :
      (⟨.realPath treePath, .ok tree⟩ : Event L E) ∈ t →
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets modules →
      ((m, path) ∈ modules ∨ root.resolve m = some path) → OutsideTree tree path →
      Reason t dir .incomplete
  /-- The project and the checker's tree do not lie apart. -/
  | notApart {project tree treePath} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath treePath, .ok tree⟩ : Event L E) ∈ t → ¬ Apart project tree →
      Reason t dir .incomplete
  /-- A `lakefile.lean` exists. -/
  | leanConfig {project metadata} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (project / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t →
      Reason t dir .refused
  /-- A key outside the closed set. -/
  | key {table input k} : (⟨.parseToml input, .ok table⟩ : Event L E) ∈ t →
      KeyPath .anonymous table k → k.getRoot ≠ `require → ¬ ConfigKeyAdmitted k → Reason t dir .refused
  /-- A configuration deeper than the reader follows. -/
  | deep {table input} : (⟨.parseToml input, .ok table⟩ : Event L E) ∈ t → Deeper 8 table →
      Reason t dir .refused
  /-- A dependency in a configuration deeper than the reader follows. -/
  | deepDependency {table input} : (⟨.parseToml input, .ok table⟩ : Event L E) ∈ t → Deeper 8 table →
      Reason t dir .proofOnly
  /-- A dependency. -/
  | dependency {table input k} : (⟨.parseToml input, .ok table⟩ : Event L E) ∈ t →
      KeyPath .anonymous table k → k.getRoot = `require → Reason t dir .proofOnly
  /-- A source directory outside the tree. -/
  | openDir {sysroot tree root log d} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t → d ∈ root.sourceDirs →
      (∀ rel, ¬ TreeRelative (parts tree) (parts d) rel) → Reason t dir .refused
  /-- A `globs` entry that is no single module. -/
  | openGlob {sysroot tree root log lib g} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t → lib ∈ root.libraries →
      g ∈ lib.2 → (∀ n, g ≠ .one n) → Reason t dir .refused
  /-- No module is claimed. -/
  | noClaim {sysroot tree root log} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets [] → Reason t dir .incomplete
  /-- A target's name outside the closed domain. -/
  | targetName {sysroot tree root log n} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t → n ∈ root.targets →
      ¬ ClosedModuleName n → Reason t dir .incomplete
  /-- A default root whose name Lake's import resolution gives another file for. -/
  | twoFiles {sysroot tree root log modules m file other} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets modules → (m, file) ∈ modules →
      root.resolve m = some other → other ≠ file → Reason t dir .incomplete
  /-- Two default targets that hold one module name with two files. -/
  | twoRoots {sysroot tree root log modules m file other} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets modules → (m, file) ∈ modules → (m, other) ∈ modules →
      other ≠ file → Reason t dir .incomplete
  /-- A module's name outside the closed domain. -/
  | moduleName {sysroot tree root log modules m} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets modules → Named t modules m → ¬ ClosedModuleName m →
      Reason t dir .incomplete
  /-- An import of a default executable's root that no library holds. -/
  | importedRoot {sysroot tree root log modules input header state messages imports i} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets modules →
      (⟨.parseHeader input, .ok (header, state, messages, imports)⟩ : Event L E) ∈ t → i ∈ imports →
      (modules.lookup i.module).isSome → root.resolve i.module = none → Reason t dir .incomplete
  /-- A module's `.olean` that does not lie below the toolchain's library. -/
  | notToolchain {m olean real sysroot tree root log} {reals : List (FilePath × FilePath)} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      (⟨.findOLean m, .ok olean⟩ : Event L E) ∈ t → (⟨.realPath olean, .ok real⟩ : Event L E) ∈ t →
      reals.map Prod.fst = root.toolchain →
      (∀ x ∈ reals, (⟨.realPath x.1, .ok x.2⟩ : Event L E) ∈ t ∧ Regula.Load.below x.2 real = false) →
      Reason t dir .incomplete
  /-- The imports reach more modules than the reader follows. -/
  | tooMany {roots : List Name} : 1000000 ≤ roots.length + importCount t → Reason t dir .incomplete
  /-- Mathlib is in the imports. -/
  | mathlib {sysroot tree root log modules m} :
      (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t →
      DefaultModules t root root.defaultTargets modules → Named t modules m → m.getRoot = `Mathlib →
      Reason t dir .proofOnly
  /-- A file read that is not in the closed language. -/
  | file {f path imports mods tree project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      ReadAs t project tree f path imports mods → ¬ FileAdmitted f → Reason t dir .refused

/-- The outcome `o` of the language check is what its reading gives. An admitted project rests on `Evidence`,
and any other outcome on a `Reason`. -/
def Decided (t : List (Event L E)) (dir tree : FilePath) (o : Outcome) : Prop :=
  (o = .admitted → ∃ r, Inside r ∧ Evidence t dir tree r) ∧ (o ≠ .admitted → Reason t dir o)

/-- What a finished build gave the rules, by this run's responses. `root` is the workspace that Lake's load
gave. -/
def BuildRead (t : List (Event L E)) (root : Root L) (f : Regula.Load.Facts) (roots : List Name) : Prop :=
  ∃ modules,
    DefaultModules t root root.defaultTargets modules ∧ roots = modules.map (·.1) ∧
    ([⟨.setSearchPath root.leanPath, ()⟩, ⟨.importForRules roots.toArray, .ok f.env⟩] :
      List (Event L E)).Sublist t ∧
    f.toolchainDir = root.leanLib ∧ f.rootDir = root.rootLib ∧
    ∀ m ∈ f.modules, (⟨.findOLean m.name, .ok m.olean⟩ : Event L E) ∈ t

/-- A failed answer to what the load of a finished build asks. -/
def Event.failedLoad : Event L E → Prop
  | ⟨.getEnv _, r⟩ => r = (none : Option String)
  | ⟨.realPath _, r⟩ | ⟨.findOLean _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error FilePath)
  | ⟨.libModules _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error (Array (Name × FilePath)))
  | ⟨.importForRules _, r⟩ => ∃ e, r = (Except.error e : Except IO.Error Environment)
  | ⟨.loadWorkspace .., r⟩ | ⟨.loadRoot .., r⟩ =>
    (∃ e, r = (Except.error e : Except String (Option (Root L) × List String))) ∨
      ∃ log, r = (Except.ok (none, log) : Except String (Option (Root L) × List String))
  | _ => False

/-- The load's result is what the proved pure function gives on what Lean and Lake returned, or an error when
one of them failed. `Regula.Load.Facts.input` is that function. -/
def Loaded (t : List (Event L E)) (p : Regula.Closed.Profile)
    (result : Except String Regula.Closed.Input) : Prop :=
  (∃ root f roots, BuildRead t root f roots ∧ result = f.input roots p) ∨
    ((∃ e ∈ t, e.failedLoad) ∧ ∃ why, result = .error why) ∨
    -- The current directory is not the workspace Lake dispatched.
    (∃ (root : Root L) (leanPath : String) (lakeLib program : FilePath) (sysroot : String) (log : List String)
        (dir : FilePath),
      (⟨.loadWorkspace sysroot dir, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t ∧
      (⟨.getEnv "LEAN_PATH", some leanPath⟩ : Event L E) ∈ t ∧
      Regula.Load.dispatchedFrom root.rootLib.toString lakeLib.toString
        ((System.SearchPath.parse leanPath).map toString) = false ∧
      ∃ why, result = .error why)

/-- A line that is no verdict: two spaces start it. -/
def IsDetail (l : String) : Prop :=
  ∃ s, l = "  " ++ s

/-- The last event of a run printed this line, and each line before it starts with two spaces, so no line
before the last can be read as a verdict and a run that stops anywhere before the end has printed none. -/
def EndsWith (t : List (Event L E)) (line : String) : Prop :=
  ∃ pre r, t = pre ++ [⟨.println line, r⟩] ∧ ∀ l ∈ printed pre, IsDetail l

/-- A run with a Lean or arguments that the checker does not read: only says so. -/
def Refusal (t : List (Event L E)) (c : UInt32) : Prop :=
  c = 2 ∧ EndsWith t (Regula.Closed.Verdict.proofLine .incomplete) ∧ ∀ e ∈ t, e.isOnlySaying = true

/-- A run of the proof verdict: its exit code and last line are the verdict's on what the load gave, and it
acts on nothing. -/
def PlainRun (t : List (Event L E)) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  ∃ result, Loaded t p result ∧
    c = (Regula.Closed.decision result).verdict.exitCode ∧
    EndsWith t (Regula.Closed.decision result).verdict.proofLine ∧
    ∀ e ∈ t, e.acted? = none

/-- Every act of a run lies in the tree, and the project and the tree lie apart: either the run acted only on the
tree it was given, or it read their real paths and each act lies at or below the tree's. -/
def Confined (t : List (Event L E)) (dir tree : FilePath) : Prop :=
  (∀ e ∈ t, ∀ path, e.acted? = some path → path = tree) ∨
    ∃ project real, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧ Apart project real ∧
      ∀ e ∈ t, ∀ path, e.acted? = some path → path = tree ∨ AtOrBelow real path

/-- The build and its replay, by `tBuild`, and the rules on the result, by `tRules`, or a failure of the build,
and no rules. `report` is what they gave. -/
def BuildAndRules (tBuild tRules : List (Event L E)) (tree : FilePath) (p : Regula.Closed.Profile)
    (report : Report) : Prop :=
  (∃ (program : FilePath) (args : List String) (result : Except String Regula.Closed.Input),
    ([⟨.runLake program tree ["build", "--wfail"], .ok 0⟩, ⟨.runLake program tree ("check" :: args), .ok 0⟩] :
      List (Event L E)).Sublist tBuild ∧
    Loaded tRules p result ∧ report = .full (Regula.Closed.decision result).verdict) ∨
  (report = .full .fail ∧ (∀ e ∈ tRules, e.isImportForRules = false) ∧
    ∃ (program cwd : FilePath) (args : List String) (r : Except IO.Error UInt32),
      (⟨.runLake program cwd args, r⟩ : Event L E) ∈ tBuild ∧ r ≠ .ok 0)

/-- A run of the full gate on the project at `dir`. The check comes first, and nothing is built or loaded unless it
admitted the project. The tree is removed on every way out, and every act lies in the tree. Exit code and last line
are the report's alone. -/
def FullRun (t : List (Event L E)) (dir : FilePath) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  -- No temporary directory.
  (∃ e, (⟨.createTempDir, .error e⟩ : Event L E) ∈ t ∧ c = Report.incomplete.exitCode ∧
    EndsWith t Report.incomplete.label ∧ ∀ e ∈ t, e.acted? = none) ∨
  ∃ (tree : FilePath) (tRead tGate : List (Event L E)) (r : Except IO.Error Unit) (last : List (Event L E)),
    t = ⟨.createTempDir, .ok tree⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last ∧
    (∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false) ∧
    ∃ (o : Outcome) (report : Report), Decided tRead dir tree o ∧
      (o ≠ .admitted → tGate = [] ∧ report = (match o with
        | .refused => Report.refused
        | .proofOnly => Report.proofOnly
        | _ => Report.incomplete)) ∧
      (o = .admitted → ∃ tBuild tRules, tGate = tBuild ++ tRules ∧ BuildAndRules tBuild tRules tree p report) ∧
      c = report.exitCode ∧ EndsWith t report.label ∧ Confined t dir tree

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

end RegulaSpecification.Effects
