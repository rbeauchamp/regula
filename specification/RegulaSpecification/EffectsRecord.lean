module

public import Regula.Rules
public import RegulaSpecification.EffectsRun

@[expose] public section

namespace RegulaSpecification.Effects

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState mkInputContext)
open System (FilePath)
open Regula.Effect
open Regula.Language
open RegulaSpecification.Language

variable {L E : Type}

def SysrootIs (t : List (Event L E)) (sysroot : String) : Prop :=
  (⟨.getEnv "LEAN_SYSROOT", some sysroot⟩ : Event L E) ∈ t

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

def TreeLoaded (t : List (Event L E)) (dir treeDir tree : FilePath) (root : Root L) : Prop :=
  (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t ∧
    ∃ sysroot log, SysrootIs t sysroot ∧ (⟨.loadRoot sysroot tree, .ok (some root, log)⟩ : Event L E) ∈ t ∧
      PreparedLoad t dir treeDir sysroot tree (.ok (some root, log))

structure Scene (t : List (Event L E)) (dir treeDir project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) : Prop where
  project_real : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t
  loaded : TreeLoaded t dir treeDir tree root
  default : DefaultModules t root root.defaultTargets modules

def SourceText (t : List (Event L E)) (project tree path : FilePath) (text : String) : Prop :=
  ∃ rel, TreeRelative (parts tree) (parts path) rel ∧ (⟨.readFile (under project rel), .ok text⟩ : Event L E) ∈ t

def HeaderOf (t : List (Event L E)) (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath))
    (m : Name) (imports : Array Import) : Prop :=
  ∃ path text header state messages, FileOfModule root modules m path ∧ SourceText t project tree path text ∧
    (⟨.parseHeader (mkInputContext text (inputNameOf path)), .ok (header, state, messages, imports)⟩ : Event L E) ∈ t

inductive Named (t : List (Event L E)) (project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) : Name → Prop where
  | root {m} : m ∈ modules.map (·.1) → Named t project tree root modules m
  | imported {m imports i} : Named t project tree root modules m → HeaderOf t project tree root modules m imports →
      i ∈ imports → Named t project tree root modules i.module

def QuietOp : Op L E → Prop
  | .leanVersion | .getEnv _ | .realPath _ | .readFile _ | .symlinkMetadata _
  | .println _ | .flush | .parseHeader _ | .parseCommand .. | .parseToml _ | .lakeInstall _
  | .libModules _ | .kernelReplay _ => True
  | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ | .runLake ..
  | .findOLean .. | .importForRules .. | .importForParser ..
  | .loadRoot .. | .loadWorkspace .. => False

def Quiet (t : List (Event L E)) : Prop := ∀ e ∈ t, QuietOp e.op

def ReadBack (t : List (Event L E)) (tree : FilePath) : Prop :=
  ∃ pre suffix, t = pre ++ suffix ∧ Quiet suffix ∧
    (∀ path text r, (⟨.writeFile path text, r⟩ : Event L E) ∈ t → written t (parts path) = some text →
      (⟨.readFile path, .ok text⟩ : Event L E) ∈ suffix) ∧
    ∃ e, (⟨.symlinkMetadata (tree / "lakefile.lean"), .error e⟩ : Event L E) ∈ suffix ∧
      ∃ name code details, e = .noFileOrDirectory name code details

def copyComplete : Except IO.Error Unit → Bool
  | .ok _ => true
  | .error _ => false

inductive CopyStep (tree path : FilePath) (text : String) : List (Event L E) → Bool → Prop where
  | outside : OutsideTree tree path → CopyStep tree path text [] false
  | noParent {r} : (∃ rel, TreeRelative (parts tree) (parts path) rel) → path.parent = none →
      CopyStep tree path text [⟨.writeFile path text, r⟩] (copyComplete r)
  | parentFailed {parent error} : (∃ rel, TreeRelative (parts tree) (parts path) rel) →
      path.parent = some parent → (∃ rel, TreeRelative (parts tree) (parts parent) rel) →
      CopyStep tree path text [⟨.createDirAll parent, .error error⟩] false
  | parentWritten {parent r} : (∃ rel, TreeRelative (parts tree) (parts path) rel) →
      path.parent = some parent → (∃ rel, TreeRelative (parts tree) (parts parent) rel) →
      CopyStep tree path text [⟨.createDirAll parent, .ok ()⟩, ⟨.writeFile path text, r⟩] (copyComplete r)

def ParserSearchOp (root : Root L) : Op L E → Prop
  | .findOLean path _ | .importForParser path _ => path = root.toolchain
  | _ => False

def RulesSearchOp (root : Root L) : Op L E → Prop
  | .findOLean path _ | .importForRules path _ => path = root.leanPath
  | _ => False

inductive ModuleCopies (project tree : FilePath) (root : Root L) (modules : List (Name × FilePath)) :
    List (Event L E) → List (Event L E) → Prop where
  | nil {prior} : ModuleCopies project tree root modules prior []
  | observe {prior e rest} : (QuietOp e.op ∨ ParserSearchOp root e.op) →
      ModuleCopies project tree root modules (prior ++ [e]) rest →
      ModuleCopies project tree root modules prior (e :: rest)
  | copy {prior m path text step rest complete} : Named prior project tree root modules m →
      FileOfModule root modules m path → SourceText prior project tree path text →
      CopyStep tree path text step complete → ModuleCopies project tree root modules (prior ++ step) rest →
      ModuleCopies project tree root modules prior (step ++ rest)

def ReadingLoaded (prior : List (Event L E)) (project tree : FilePath) (root : Root L)
    (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before rest modules,
    t = before ++ rest ∧ Quiet before ∧
    DefaultModules (prior ++ before) root root.defaultTargets modules ∧
    ModuleCopies project tree root modules (prior ++ before) rest

def ReadingLoad (prior : List (Event L E)) (sysroot : String) (project tree : FilePath)
    (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before response rest,
    t = before ++ ⟨.loadRoot sysroot tree, response⟩ :: rest ∧ Quiet before ∧
    match response with
    | .ok (some root, _) =>
        ReadingLoaded (prior ++ before ++ [⟨.loadRoot sysroot tree, response⟩]) project tree root rest
    | _ => Quiet rest

inductive ConfigCopies (sysroot : String) (project tree : FilePath) :
    List (FilePath × String) → List (Event L E) → List (Event L E) → Prop where
  | done {prior t} : ReadingLoad prior sysroot project tree t → ConfigCopies sysroot project tree [] prior t
  | stopped {copies prior t} : Quiet t → ConfigCopies sysroot project tree copies prior t
  | failed {path text copies prior before step rest} : Quiet before → CopyStep tree path text step false →
      Quiet rest → ConfigCopies sysroot project tree ((path, text) :: copies) prior (before ++ step ++ rest)
  | next {path text copies prior before step rest} : Quiet before → CopyStep tree path text step true →
      ConfigCopies sysroot project tree copies (prior ++ before ++ step) rest →
      ConfigCopies sysroot project tree ((path, text) :: copies) prior (before ++ step ++ rest)

def ReadingPreparation (t : List (Event L E)) (dir treeDir : FilePath) : Prop :=
  Quiet t ∨ ∃ project tree sysroot text before rest,
    t = before ++ rest ∧ Quiet before ∧
    (⟨.realPath dir, .ok project⟩ : Event L E) ∈ before ∧
    (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ before ∧ Apart project tree ∧ SysrootIs before sysroot ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ before ∧
    ConfigCopies sysroot project tree [(tree / "lakefile.toml", text), (tree / "lean-toolchain", leanToolchain)]
      before rest

def InputPreparation (root : Root L) (t : List (Event L E)) : Prop :=
  ∀ e ∈ t, QuietOp e.op ∨ RulesSearchOp root e.op

def RulesPreparation (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before real response rest,
    t = before ++ ⟨.loadRoot sysroot real, response⟩ :: rest ∧ Quiet before ∧
    (⟨.realPath tree, .ok real⟩ : Event L E) ∈ before ∧
    match response with
    | .ok (some root, _) => InputPreparation root rest
    | _ => Quiet rest

def PlainPreparation (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before sysroot dir response rest,
    t = before ++ ⟨.loadWorkspace sysroot dir, response⟩ :: rest ∧ Quiet before ∧
    SysrootIs before sysroot ∧ (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ before ∧
    match response with
    | .ok (some root, _) => InputPreparation root rest
    | _ => Quiet rest

def OutProofPreparation (target : FilePath) (t : List (Event L E)) : Prop :=
  Quiet t ∨ ∃ before sysroot dir err name code details response rest,
    t = before ++ ⟨.loadRoot sysroot dir, response⟩ :: rest ∧ Quiet before ∧
    SysrootIs before sysroot ∧ (⟨.realPath target, .ok dir⟩ : Event L E) ∈ before ∧
    (⟨.symlinkMetadata (dir / "lakefile.lean"), .error err⟩ : Event L E) ∈ before ∧
    err = .noFileOrDirectory name code details ∧
    match response with
    | .ok (some root, _) =>
        if root.defaultTargets ≠ [] ∧ ∀ target ∈ root.defaultTargets, (root.findLib target).isSome = true then
          InputPreparation root rest
        else
          Quiet rest
    | _ => Quiet rest

inductive Needed (t : List (Event L E)) (dir treeDir : FilePath) : Op L E → Prop where
  | sysroot : Needed t dir treeDir (.getEnv "LEAN_SYSROOT")
  | project : Needed t dir treeDir (.realPath dir)
  | tree : Needed t dir treeDir (.realPath treeDir)
  | leanConfig {project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.symlinkMetadata (project / "lakefile.lean"))
  | tomlReal {project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.realPath (project / "lakefile.toml"))
  | tomlRead {project} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.readFile (project / "lakefile.toml"))
  | tomlParse {project text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.parseToml (mkInputContext text "lakefile.toml"))
  | copyParent {tree path d} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") → path.parent = some d →
      Needed t dir treeDir (.createDirAll d)
  | copyToml {project tree text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.writeFile (tree / "lakefile.toml") text)
  | copyToolchain {tree} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.writeFile (tree / "lean-toolchain") leanToolchain)
  | library {tree root target lib} : TreeLoaded t dir treeDir tree root → target ∈ root.defaultTargets →
      root.findLib target = some lib → Needed t dir treeDir (.libModules lib)
  | treeLeanConfig {tree} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      Needed t dir treeDir (.symlinkMetadata (tree / "lakefile.lean"))
  | search {project tree root modules m} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → modules.lookup m = none → root.resolve m = none →
      Needed t dir treeDir (.findOLean root.toolchain m)
  | sourceReal {project tree root modules m path rel} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      TreeRelative (parts tree) (parts path) rel → Needed t dir treeDir (.realPath (under project rel))
  | sourceRead {project tree root modules m path rel} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      TreeRelative (parts tree) (parts path) rel → Needed t dir treeDir (.readFile (under project rel))
  | sourceParent {project tree root modules m path d} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path → path.parent = some d →
      Needed t dir treeDir (.createDirAll d)
  | sourceWrite {project tree root modules m path text} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      SourceText t project tree path text → Needed t dir treeDir (.writeFile path text)
  | sourceHeader {project tree root modules m path text} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      SourceText t project tree path text →
      Needed t dir treeDir (.parseHeader (mkInputContext text (inputNameOf path)))
  | parser {project tree root modules mods} : Scene t dir treeDir project tree root modules →
      (∀ n ∈ mods, Named t project tree root modules n ∧ HeldByToolchain t root n) →
      Needed t dir treeDir (.importForParser root.toolchain mods)

def TomlRead (t : List (Event L E)) (dir : FilePath) (table : Lake.Toml.Table) : Prop :=
  ∃ project text, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
    (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t ∧
    (⟨.parseToml (mkInputContext text "lakefile.toml"), .ok table⟩ : Event L E) ∈ t

inductive Planned (t : List (Event L E)) (project tree : FilePath) (root : Root L)
    (modules : List (Name × FilePath)) : FilePath → String → Prop where
  | toml {text} : (⟨.readFile (project / "lakefile.toml"), .ok text⟩ : Event L E) ∈ t →
      Planned t project tree root modules (tree / "lakefile.toml") text
  | toolchain : Planned t project tree root modules (tree / "lean-toolchain") leanToolchain
  | source {m path text} : Named t project tree root modules m → FileOfModule root modules m path →
      SourceText t project tree path text → Planned t project tree root modules path text

inductive Reason (t : List (Event L E)) (dir treeDir : FilePath) : Outcome → Prop where
  | failed {e : Event L E} : e ∈ t → Needed t dir treeDir e.op → e.failed → Reason t dir treeDir .incomplete
  | load {sysroot tree response} : PreparedLoad t dir treeDir sysroot tree response →
      Event.failed (⟨.loadRoot sysroot tree, response⟩ : Event L E) → Reason t dir treeDir .incomplete
  | toolchain {project text} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .ok text⟩ : Event L E) ∈ t →
      text.trimAscii.toString ≠ leanToolchain → Reason t dir treeDir .refused
  | toolchainFailed {project e} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.readFile (project / "lean-toolchain"), .error e⟩ : Event L E) ∈ t → Reason t dir treeDir .refused
  | toolchainNotExact {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .ok real⟩ : Event L E) ∈ t →
      ¬ ExactlyBelow project (project / "lean-toolchain") real →
      Reason t dir treeDir .refused
  | toolchainNoReal {project e} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lean-toolchain"), .error e⟩ : Event L E) ∈ t → Reason t dir treeDir .refused
  | tomlNotExact {project real} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath (project / "lakefile.toml"), .ok real⟩ : Event L E) ∈ t →
      ¬ ExactlyBelow project (project / "lakefile.toml") real →
      Reason t dir treeDir .incomplete
  | notApart {project tree} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t → ¬ Apart project tree →
      Reason t dir treeDir .incomplete
  | configNotInTree {tree path} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (path = tree / "lakefile.toml" ∨ path = tree / "lean-toolchain") → OutsideTree tree path →
      Reason t dir treeDir .incomplete
  | moduleNotInTree {project tree root modules m path} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path → OutsideTree tree path →
      Reason t dir treeDir .incomplete
  | moduleNotExact {project tree root modules m path rel real} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → FileOfModule root modules m path →
      TreeRelative (parts tree) (parts path) rel →
      (⟨.realPath (under project rel), .ok real⟩ : Event L E) ∈ t →
      ¬ ExactlyBelow project (under project rel) real →
      Reason t dir treeDir .incomplete
  | leanConfig {project metadata} : (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (project / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t →
      Reason t dir treeDir .refused
  | key {table k} : TomlRead t dir table → KeyPath .anonymous table k → k.getRoot ≠ `require →
      ¬ ConfigKeyAdmitted k → Reason t dir treeDir .refused
  | deep {table} : TomlRead t dir table → Deeper 8 table → Reason t dir treeDir .refused
  | deepDependency {table} : TomlRead t dir table → Deeper 8 table → Reason t dir treeDir .proofOnly
  | dependency {table k} : TomlRead t dir table → KeyPath .anonymous table k → k.getRoot = `require →
      Reason t dir treeDir .proofOnly
  | openDir {tree root d} : TreeLoaded t dir treeDir tree root → d ∈ root.sourceDirs →
      (∀ rel, TreeRelative (parts tree) (parts d) rel → ∃ c ∈ rel, ¬ ClosedComponent c) →
      Reason t dir treeDir .refused
  | openGlob {tree root lib g} : TreeLoaded t dir treeDir tree root → lib ∈ root.libraries →
      g ∈ lib.2 → (∀ n, g ≠ .one n) → Reason t dir treeDir .refused
  | notLibrary {tree root target} : TreeLoaded t dir treeDir tree root → target ∈ root.defaultTargets →
      root.findLib target = none → Reason t dir treeDir .refused
  | noClaim {project tree root} : Scene t dir treeDir project tree root [] → Reason t dir treeDir .incomplete
  | targetName {tree root n} : TreeLoaded t dir treeDir tree root → n ∈ root.targets →
      ¬ ClosedModuleName n → Reason t dir treeDir .incomplete
  | rootElsewhere {project tree root modules m file} : Scene t dir treeDir project tree root modules →
      (m, file) ∈ modules → (∀ other, root.resolve m = some other → parts other ≠ parts file) →
      Reason t dir treeDir .incomplete
  | configShadowed {tree metadata} : (⟨.realPath treeDir, .ok tree⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (tree / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → Reason t dir treeDir .incomplete
  | treeDiffers {project tree root modules path text r} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text →
      ([⟨.writeFile path text, .ok ()⟩, ⟨.readFile path, r⟩] : List (Event L E)).Sublist t → r ≠ .ok text →
      Reason t dir treeDir .incomplete
  | twoTexts {project tree root modules path text path' text'} : Scene t dir treeDir project tree root modules →
      Planned t project tree root modules path text → Planned t project tree root modules path' text' →
      parts path = parts path' → text ≠ text' → Reason t dir treeDir .incomplete
  | moduleName {project tree root modules m} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → ¬ ClosedModuleName m → Reason t dir treeDir .incomplete
  | tooMany {project tree root modules} {ms : List (Name × Array Import)} :
      Scene t dir treeDir project tree root modules → (ms.map (·.1)).Nodup →
      (∀ x ∈ ms, Named t project tree root modules x.1 ∧ HeaderOf t project tree root modules x.1 x.2) →
      1000000 < modules.length + (ms.map (·.2.size)).sum → Reason t dir treeDir .incomplete
  | mathlib {project tree root modules m} : Scene t dir treeDir project tree root modules →
      Named t project tree root modules m → m.getRoot = `Mathlib → Reason t dir treeDir .proofOnly
  | file {project tree root modules f path imports mods} {headers : List (Name × Array Import)} {held : List Name} :
      Scene t dir treeDir project tree root modules → Named t project tree root modules f.module →
      FileOfModule root modules f.module path → ReadAs t root project tree f path imports mods →
      (∀ x ∈ headers, HeaderOf t project tree root modules x.1 x.2) →
      (∀ n ∈ held, Named t project tree root modules n ∧ HeldByToolchain t root n) →
      (∀ i ∈ imports, i.module ∈ held ∨ (headers.lookup i.module).isSome = true) →
      (∀ x ∈ headers, ∀ i ∈ x.2, i.module ∈ held ∨ (headers.lookup i.module).isSome = true) →
      (∀ n, n ∈ mods ↔ ∃ m ∈ imports, Sees headers held m.module n) →
      ¬ FileAdmitted f → Reason t dir treeDir .refused

def Decided (t : List (Event L E)) (dir tree : FilePath) (o : Outcome) : Prop :=
  (o = .admitted → ∃ r real, Inside r ∧ Evidence t dir tree (written t) r ∧ (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧ ReadBack t real) ∧
    (o ≠ .admitted → Reason t dir tree o) ∧
    ((∃ r, o = decision r) ∨ o = .incomplete)

def BuildRead (t : List (Event L E)) (root : Root L) (f : Regula.Load.Facts) (roots : List Name) : Prop :=
  ∃ modules,
    DefaultModules t root root.defaultTargets modules ∧ roots = modules.map (·.1) ∧
    (⟨.importForRules root.leanPath roots.toArray, .ok f.env⟩ : Event L E) ∈ t ∧
    f.toolchainDir = root.leanLib ∧ f.rootDir = root.rootLib ∧
    ∀ m ∈ f.modules, (⟨.findOLean root.leanPath m.name, .ok m.olean⟩ : Event L E) ∈ t

def SearchPathStarts (received : String) (root : Root L) : Prop :=
  ∃ inherited, (System.SearchPath.parse received).map toString = root.leanPath.map toString ++ inherited

def PlainRoot (t : List (Event L E)) (root : Root L) : Prop :=
  ∃ (sysroot : String) (dir : FilePath) (log : List String) (received : String),
    SysrootIs t sysroot ∧
    (⟨.loadWorkspace sysroot dir, .ok (some root, log)⟩ : Event L E) ∈ t ∧
    (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ t ∧
    (⟨.getEnv "LEAN_PATH", some received⟩ : Event L E) ∈ t ∧
    SearchPathStarts received root

def TreeRoot (sysroot : String) (tree : FilePath) (t : List (Event L E)) (root : Root L) : Prop :=
  ∃ (real : FilePath) (log : List String),
    (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧
    (⟨.loadRoot sysroot real, .ok (some root, log)⟩ : Event L E) ∈ t

def OutProofLoaded (dir : FilePath) (t : List (Event L E)) (root : Root L) : Prop :=
  dir.toString ≠ "" ∧
  ∃ sysroot real err name code details log,
    SysrootIs t sysroot ∧
    (⟨.realPath dir, .ok real⟩ : Event L E) ∈ t ∧
    (⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩ : Event L E) ∈ t ∧
    err = .noFileOrDirectory name code details ∧
    (⟨.loadRoot sysroot real, .ok (some root, log)⟩ : Event L E) ∈ t

def OutProofRoot (dir : FilePath) (t : List (Event L E)) (root : Root L) : Prop :=
  OutProofLoaded dir t root ∧
  root.defaultTargets ≠ [] ∧
  ∀ target ∈ root.defaultTargets, (root.findLib target).isSome = true

inductive BuildFailed (t : List (Event L E)) (root : Root L) : Prop where
  | library {target lib e} : target ∈ root.defaultTargets → root.findLib target = some lib →
      (⟨.libModules lib, .error e⟩ : Event L E) ∈ t → BuildFailed t root
  | import {modules e} : DefaultModules t root root.defaultTargets modules →
      (⟨.importForRules root.leanPath (modules.map (·.1)).toArray, .error e⟩ : Event L E) ∈ t → BuildFailed t root
  | search {modules env m e} : DefaultModules t root root.defaultTargets modules →
      (⟨.importForRules root.leanPath (modules.map (·.1)).toArray, .ok env⟩ : Event L E) ∈ t →
      m ∈ env.header.moduleNames → (⟨.findOLean root.leanPath m, .error e⟩ : Event L E) ∈ t → BuildFailed t root

inductive PlainReason (t : List (Event L E)) : Prop where
  | noSysroot : (⟨.getEnv "LEAN_SYSROOT", none⟩ : Event L E) ∈ t → PlainReason t
  | noDirectory {e} : (⟨.realPath ".", .error e⟩ : Event L E) ∈ t → PlainReason t
  | load {sysroot dir r} : SysrootIs t sysroot → (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ t →
      (⟨.loadWorkspace sysroot dir, r⟩ : Event L E) ∈ t → Event.failed (⟨.loadWorkspace sysroot dir, r⟩ : Event L E) →
      PlainReason t
  | noSearchPath : (⟨.getEnv "LEAN_PATH", none⟩ : Event L E) ∈ t → PlainReason t
  | otherSearchPath {sysroot dir root log received} : SysrootIs t sysroot →
      (⟨.realPath ".", .ok dir⟩ : Event L E) ∈ t →
      (⟨.loadWorkspace sysroot dir, .ok (some root, log)⟩ : Event L E) ∈ t →
      (⟨.getEnv "LEAN_PATH", some received⟩ : Event L E) ∈ t →
      ¬ SearchPathStarts received root → PlainReason t
  | build {root} : PlainRoot t root → BuildFailed t root → PlainReason t

inductive TreeReason (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop where
  | noTree {e} : (⟨.realPath tree, .error e⟩ : Event L E) ∈ t → TreeReason sysroot tree t
  | load {real r} : (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t → (⟨.loadRoot sysroot real, r⟩ : Event L E) ∈ t →
      Event.failed (⟨.loadRoot sysroot real, r⟩ : Event L E) → TreeReason sysroot tree t
  | build {root} : TreeRoot sysroot tree t root → BuildFailed t root → TreeReason sysroot tree t

inductive OutProofReason (dir : FilePath) (t : List (Event L E)) : Prop where
  | emptyTarget : dir.toString = "" → OutProofReason dir t
  | noSysroot : (⟨.getEnv "LEAN_SYSROOT", none⟩ : Event L E) ∈ t → OutProofReason dir t
  | noDirectory {e} : dir.toString ≠ "" → (⟨.realPath dir, .error e⟩ : Event L E) ∈ t → OutProofReason dir t
  | configShadowed {real metadata} : dir.toString ≠ "" →
      (⟨.realPath dir, .ok real⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (real / "lakefile.lean"), .ok metadata⟩ : Event L E) ∈ t → OutProofReason dir t
  | leanConfig {real r} : dir.toString ≠ "" →
      (⟨.realPath dir, .ok real⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (real / "lakefile.lean"), r⟩ : Event L E) ∈ t →
      Event.failed (⟨.symlinkMetadata (real / "lakefile.lean"), r⟩ : Event L E) → OutProofReason dir t
  | load {sysroot real err name code details r} : dir.toString ≠ "" → SysrootIs t sysroot →
      (⟨.realPath dir, .ok real⟩ : Event L E) ∈ t →
      (⟨.symlinkMetadata (real / "lakefile.lean"), .error err⟩ : Event L E) ∈ t →
      err = .noFileOrDirectory name code details →
      (⟨.loadRoot sysroot real, r⟩ : Event L E) ∈ t →
      Event.failed (⟨.loadRoot sysroot real, r⟩ : Event L E) → OutProofReason dir t
  | emptyTargets {root} : OutProofLoaded dir t root → root.defaultTargets = [] → OutProofReason dir t
  | notLibrary {root target} : OutProofLoaded dir t root → target ∈ root.defaultTargets →
      root.findLib target = none → OutProofReason dir t
  | build {root} : OutProofRoot dir t root → BuildFailed t root → OutProofReason dir t

def Replayed (t : List (Event L E)) (f : Regula.Load.Facts) :
    Except String Regula.Closed.Input → Except String Regula.Closed.Input → Prop
  | .error message, result => result = .error message
  | .ok i, result => ∃ r, (⟨.kernelReplay (f.replayConstants i), r⟩ : Event L E) ∈ t ∧
      ((r = .ok () ∧ result = .ok i) ∨ ((∃ e, r = .error e) ∧ ∃ message, result = .error message))

def Loaded (gave : List (Event L E) → Root L → Prop) (why : List (Event L E) → Prop) (t : List (Event L E))
    (p : Regula.Closed.Profile) (result : Except String Regula.Closed.Input) : Prop :=
  (∃ root f roots, gave t root ∧ BuildRead t root f roots ∧ Replayed t f (f.input roots p) result) ∨
    (why t ∧ ∃ message, result = .error message)

def IsDetail (l : String) : Prop :=
  ∃ s, l = "  " ++ s

def EndsWith (t : List (Event L E)) (line : String) : Prop :=
  ∃ pre r, t = pre ++ [⟨.println line, r⟩] ∧ '\n' ∉ line.toList ∧ ∀ l ∈ printed pre, IsDetail l

def Refusal (t : List (Event L E)) (c : UInt32) : Prop :=
  c = 2 ∧ EndsWith t (Regula.Closed.Verdict.proofLine .incomplete) ∧ ∀ e ∈ t, e.isOnlySaying = true

def ConflictingRefusal (t : List (Event L E)) (c : UInt32) : Prop :=
  ∃ v rf rp rest,
    t = ⟨.leanVersion, v⟩ :: ⟨.getEnv "REGULA_FULL", some rf⟩ :: ⟨.getEnv "REGULA_PROOF", some rp⟩ :: rest ∧
    Refusal rest c

def PlainRun (t : List (Event L E)) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  ∃ result, Loaded PlainRoot PlainReason t p result ∧
    c = (Regula.Closed.decision result).verdict.exitCode ∧
    (match (Regula.Closed.decision result).verdict with
      | .pass => ∃ subject : FilePath,
          EndsWith t (Regula.Closed.Verdict.pass.proofLineOn subject.toString) ∧
          (⟨.realPath ".", .ok subject⟩ : Event L E) ∈ t ∧
          ∃ sysroot root log, (⟨.loadWorkspace sysroot subject, .ok (some root, log)⟩ : Event L E) ∈ t ∧ PlainRoot t root
      | v => EndsWith t v.proofLine) ∧
    (∀ e ∈ t, e.acted? = none) ∧ (c = 0 → ∀ e ∈ t, ¬ e.failed) ∧ PlainPreparation t

def OutProofRun (t : List (Event L E)) (dir : FilePath) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  ∃ result, Loaded (OutProofRoot dir) (OutProofReason dir) t p result ∧
    c = (Regula.Closed.decision result).verdict.exitCode ∧
    (match (Regula.Closed.decision result).verdict with
      | .pass => ∃ subject : FilePath,
          EndsWith t (Regula.Closed.Verdict.pass.proofLineOn subject.toString) ∧
          (⟨.realPath dir, .ok subject⟩ : Event L E) ∈ t ∧
          ∃ sysroot root log err name code details,
            SysrootIs t sysroot ∧
            (⟨.symlinkMetadata (subject / "lakefile.lean"), .error err⟩ : Event L E) ∈ t ∧
            err = .noFileOrDirectory name code details ∧
            (⟨.loadRoot sysroot subject, .ok (some root, log)⟩ : Event L E) ∈ t ∧ OutProofRoot dir t root
      | v => EndsWith t v.proofLine) ∧
    (∀ e ∈ t, e.acted? = none) ∧ (c = 0 → ∀ e ∈ t, ¬ e.failed) ∧ OutProofPreparation dir t

def Confined (t : List (Event L E)) (dir tree : FilePath) : Prop :=
  (∀ e ∈ t, ∀ path, e.acted? = some path → path = tree) ∨
    ∃ project real, (⟨.realPath dir, .ok project⟩ : Event L E) ∈ t ∧
      (⟨.realPath tree, .ok real⟩ : Event L E) ∈ t ∧ Apart project real ∧
      ∀ e ∈ t, ∀ path, e.acted? = some path → path = tree ∨ AtOrBelow real path

def LakeInvocation (program tree : FilePath) (args : List String) (response : Except IO.Error UInt32)
    (t : List (Event L E)) : Prop :=
  ∃ pre post, t = pre ++ ⟨.runLake program tree args, response⟩ :: post ∧
    (∀ e ∈ pre, e.isOnlySaying = true) ∧ ∀ e ∈ post, e.isOnlySaying = true

def BuildProtocol (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop :=
  ∃ program lakeLib first response,
    t = ⟨.lakeInstall sysroot, (program, lakeLib)⟩ :: first ∧
    LakeInvocation program tree ["build", "--wfail"] response first

def ReloadOp : Op L E → Prop
  | .leanVersion | .getEnv _ | .realPath _ | .readFile _ | .symlinkMetadata _
  | .println _ | .flush | .parseHeader _ | .parseCommand .. | .findOLean ..
  | .importForRules .. | .importForParser .. | .kernelReplay _ | .parseToml _ | .lakeInstall _ | .loadWorkspace ..
  | .loadRoot .. | .libModules _ => True
  | .writeFile .. | .createDirAll _ | .createTempDir | .removeDirAll _ | .runLake .. => False

inductive BuildRejected (sysroot : String) (tree : FilePath) (t : List (Event L E)) : Prop where
  | build {program lakeLib r} : (⟨.lakeInstall sysroot, (program, lakeLib)⟩ : Event L E) ∈ t →
      (⟨.runLake program tree ["build", "--wfail"], r⟩ : Event L E) ∈ t → r ≠ .ok 0 →
      BuildRejected sysroot tree t

def BuildAndRules (sysroot : String) (tBuild tRules : List (Event L E)) (tree : FilePath) (p : Regula.Closed.Profile)
    (report : Report) : Prop :=
  BuildProtocol sysroot tree tBuild ∧ (∀ e ∈ tRules, ReloadOp e.op) ∧
  ((∃ (program lakeLib : FilePath) (result : Except String Regula.Closed.Input),
    (∀ e ∈ tRules, e.isBuild = false) ∧
    ([⟨.lakeInstall sysroot, (program, lakeLib)⟩, ⟨.runLake program tree ["build", "--wfail"], .ok 0⟩] :
      List (Event L E)).Sublist tBuild ∧
    Loaded (TreeRoot sysroot tree) (TreeReason sysroot tree) tRules p result ∧
    report = .full (Regula.Closed.decision result).verdict) ∨
  (report = .full .fail ∧ (∀ e ∈ tRules, e.isImportForRules = false) ∧ BuildRejected sysroot tree tBuild)) ∧
  RulesPreparation sysroot tree tRules

def NotRemoving : Op L E → Prop
  | .removeDirAll _ => False
  | _ => True

def FullRun (t : List (Event L E)) (dir : FilePath) (p : Regula.Closed.Profile) (c : UInt32) : Prop :=
  (∃ e rest, t = ⟨.createTempDir, .error e⟩ :: rest ∧ c = Report.incomplete.exitCode ∧
    EndsWith t Report.incomplete.label ∧ ∀ e ∈ rest, e.isOnlySaying = true) ∨
  ∃ (tree : FilePath) (tRead tGate : List (Event L E)) (r : Except IO.Error Unit) (last : List (Event L E)),
    t = ⟨.createTempDir, .ok tree⟩ :: tRead ++ tGate ++ ⟨.removeDirAll tree, r⟩ :: last ∧
    (∀ e ∈ tRead, e.isBuild = false ∧ e.isImportForRules = false) ∧ (∀ e ∈ last, e.isOnlySaying = true) ∧
    ∃ (o : Outcome) (report : Report), Decided tRead dir tree o ∧
      (o = .admitted → ∀ e ∈ tRead, ¬ e.failed) ∧
      (o ≠ .admitted → tGate = [] ∧ report = (match o with
        | .refused => Report.refused
        | .proofOnly => Report.proofOnly
        | _ => Report.incomplete)) ∧
      (o = .admitted → ∃ sysroot tBuild tRules, SysrootIs tRead sysroot ∧ tGate = tBuild ++ tRules ∧
        BuildAndRules sysroot tBuild tRules tree p report) ∧
      c = report.exitCode ∧ EndsWith t (report.labelOn dir.toString) ∧ Confined t dir tree ∧
      (c = 0 → ∀ e ∈ t, ¬ e.failed) ∧ (∀ e ∈ tRead, NotRemoving e.op) ∧ ReadingPreparation tRead dir tree

def OnPinnedLean (t : List (Event L E)) (run : List (Event L E) → Prop) (c : UInt32) : Prop :=
  ∃ v rest, t = ⟨.leanVersion, v⟩ :: rest ∧ (v = Regula.Closed.pinnedLean → run t) ∧
    (v ≠ Regula.Closed.pinnedLean → Refusal t c)

def RunMeets (w : List String → Prog L E UInt32) : Prop :=
  ∀ args t c, Runs (w args) t c →
    match args with
    | [text] =>
      match Regula.Closed.Profile.ofSpelling? text with
      | some p => OnPinnedLean t (fun t => ∃ v rf rp rest,
          t = ⟨.leanVersion, v⟩ :: ⟨.getEnv "REGULA_FULL", rf⟩ :: ⟨.getEnv "REGULA_PROOF", rp⟩ :: rest ∧
          match rf, rp with
          | some _, some _ => Refusal rest c
          | some dir, none => FullRun rest (FilePath.mk dir) p c
          | none, some dir => OutProofRun rest (FilePath.mk dir) p c
          | none, none => PlainRun (⟨.leanVersion, v⟩ :: rest) p c) c
      | none => Refusal t c
    | _ => Refusal t c

def programRecord (L E : Type) : LeanIntent.IntentRecord (List String → Prog L E UInt32) where
  shape := .function (List String) (fun _ => Prog L E UInt32)
  dom := []
  props := [
    ⟨"a run does what its arguments ask, on every response, and it refuses what it cannot read", RunMeets⟩]
  vocab := [
    ⟨"a line that is no verdict", String, IsDetail⟩,
    ⟨"a project wholly inside the closed language", Reading, Inside⟩]

end RegulaSpecification.Effects
