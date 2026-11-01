/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
import Regula.Effect
import RegulaSpecification.Language

/-!
# Which projects a full verdict is owed to

This module states the domain of the full verdict: the projects to which a run of the full gate owes a pass when its
reads answer consistently, its Lake commands succeed and the rules hold. It says this in the terms of a project's author:
what `lakefile.toml` says, what its files hold, and what the closed language admits. It imports neither the program that
reads a project nor the relation `Reason` that lists a run's refusals, so that it can be compared with them: the
definition of healthy that once was the absence of every refusal left out a healthy project (a `srcDir` spelled `./`
beside one spelled `.`).

`RegulaSpecification.Proofs.Domain` relates this statement to the run. It proves that every reason falls under a failed or
differing answer, a project outside this domain, or a conflict, and that a project in this domain whose reads answer
consistently is owed a pass.

The statement is a design of the owner's delegated agents, derived from the owner's account (`confirmation.md`), and no
statement of the owner's.
-/

namespace RegulaSpecification.Domain

open Lean (Name Import)
open Regula.Language
open RegulaSpecification.Language

/-! ## One spelling of a directory -/

/-- The pieces of a list of characters between each `/`. It is structural so that the kernel can evaluate an example. -/
def splitAtSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match splitAtSlash cs with
    | [] => [[]]
    | w :: ws => if c == '/' then [] :: w :: ws else (c :: w) :: ws

/-- What a directory's spelling names: the components that `/` separates, with each empty one and each `.` left out. So
`.`, `./`, the empty string and `.//` name no component, and `a/b`, `a//b`, `./a/b/` and `a/./b` name the same two. Two
spellings with the same components are **one spelling** of one directory. This is about the text alone, and takes no file
system: on POSIX a `.` component and an empty one change nothing, and nothing here follows a link or folds a case. -/
def components (s : String) : List String :=
  ((splitAtSlash s.toList).map String.ofList).filter fun c => c != "" && c != "."

/-- Two spellings of one directory: the same components, and both relative or both absolute. -/
def OneSpelling (a b : String) : Prop :=
  components a = components b ∧ (a.front = '/' ↔ b.front = '/')

/-- A directory that lies below the project, whatever it holds: its spelling is relative, and no component starts with
`.`, so none is `..` and none is `.lake`. -/
def Relative (s : String) : Prop :=
  s.front ≠ '/' ∧ ∀ c ∈ components s, c.front ≠ '.'

/-! ## What `lakefile.toml` says -/

/-- A `[[lean_lib]]`, with Lake's defaults filled in: `srcDir` is `.`, `roots` is the name, and `globs` is the roots. -/
structure Library where
  /-- `name`. -/
  name : Name
  /-- `srcDir`, as the author spelled it. -/
  srcDir : String
  /-- `roots`. -/
  roots : List Name
  /-- `globs`. -/
  globs : List Lake.Glob
  deriving Inhabited

/-- A `[[lean_exe]]`, with Lake's defaults filled in: `srcDir` is `.`, and `root` is the name. -/
structure Executable where
  /-- `name`. -/
  name : Name
  /-- `srcDir`, as the author spelled it. -/
  srcDir : String
  /-- `root`. -/
  root : Name
  deriving Inhabited

/-- What the text of `lakefile.toml` says, by Lake's own parser and its defaults. -/
structure Configuration where
  /-- Every key path of the text, one for each leaf: `lean_lib.name`, `leanOptions.autoImplicit`. -/
  keys : List Name
  /-- How many tables the deepest key lies inside. -/
  nesting : Nat
  /-- The package's `srcDir`, as the author spelled it. -/
  srcDir : String
  /-- Each library, in the order of the text. -/
  libraries : List Library
  /-- Each executable, in the order of the text. -/
  executables : List Executable
  /-- `defaultTargets`. -/
  defaultTargets : List Name

namespace Configuration

variable (c : Configuration)

/-- Every source directory that the text states. -/
def sourceDirs : List String :=
  c.srcDir :: c.libraries.map (·.srcDir) ++ c.executables.map (·.srcDir)

/-- Every target's name. -/
def targetNames : List Name :=
  c.libraries.map (·.name) ++ c.executables.map (·.name)

end Configuration

/-- The directories that a name's components give. -/
def moduleDirs : Name → List String
  | .anonymous => []
  | .str p s => moduleDirs p ++ [s]
  | .num p _ => moduleDirs p

/-- The file of a module below a source directory: each component of the name a directory, and the last one a file with
the extension `lean`, as Lean's `modToFilePath` joins them. -/
def moduleFile : Name → List String
  | .anonymous => []
  | .str p s => moduleDirs p ++ [s ++ ".lean"]
  | .num p _ => moduleFile p

namespace Configuration

variable (c : Configuration)

/-- The file of a module of a library, below the project: the package's source directory, the library's, and the module's
own file. -/
def fileIn (lib : Library) (m : Name) : List String :=
  components c.srcDir ++ components lib.srcDir ++ moduleFile m

/-- The file of an executable's root, below the project. -/
def exeFile (exe : Executable) : List String :=
  components c.srcDir ++ components exe.srcDir ++ moduleFile exe.root

/-- Whether a library builds a module: an entry of its `globs` matches it, or a root that such an entry matches is a
prefix of it (`isBuildableModule`, `Lake/Config/LeanLibConfig.lean:144-146` at v4.35.0). -/
def buildable (lib : Library) (m : Name) : Bool :=
  lib.globs.any (Lake.Glob.matches m) ||
    lib.roots.any fun root => root.isPrefixOf m && lib.globs.any (Lake.Glob.matches root)

/-- The file that an import of the module `m` names: that of the last library that builds it, as Lake's own resolution
searches (`Package.findModule?`, `Lake/Config/Module.lean:58-59`, `findSomeRev?`). An executable's root is no library's. -/
def resolve (m : Name) : Option (List String) :=
  (c.libraries.reverse.find? (buildable · m)).map (c.fileIn · m)

/-- The modules that a library lists: one for each entry of `globs` that is a single module. -/
def listed (lib : Library) : List Name :=
  lib.globs.filterMap fun
    | .one n => some n
    | _ => none

/-- The modules of one target, each with its file below the project. A default target that names neither a library nor an
executable builds no Lean module (`Package.recCollectDefaultModules`, `Lake/Build/Package.lean:45-61`). -/
def modulesOf (target : Name) : List (Name × List String) :=
  match c.libraries.find? (·.name == target) with
  | some lib => (listed lib).map fun m => (m, c.fileIn lib m)
  | none =>
    match c.executables.find? (·.name == target) with
    | some exe => [(exe.root, c.exeFile exe)]
    | none => []

/-- **The claim**: each module of the default targets, each with its file below the project. -/
def claim : List (Name × List String) :=
  c.defaultTargets.flatMap c.modulesOf

/-- A configuration inside the domain. Each clause is what a project's author can check by reading `lakefile.toml`. -/
structure InDomain : Prop where
  /-- Each key is one of the closed set of keys, so no key can run a plugin, pass an argument to Lean or move Lake's
  output. -/
  keys : ∀ k ∈ c.keys, ConfigKeyAdmitted k
  /-- No `require`: nothing of a dependency is read, so a project with one can have only the proof verdict. -/
  noDependency : ∀ k ∈ c.keys, k.getRoot ≠ `require
  /-- No key lies deeper than the reader follows. -/
  shallow : c.nesting < 8
  /-- Each source directory is relative, and no component of it starts with `.`. Two spellings of one directory are one
  value here: this reads a directory only through `components` and `Relative`. -/
  sourceDirs : ∀ s ∈ c.sourceDirs, Relative s
  /-- Each `globs` entry is a single module, so finding the modules lists no directory. -/
  globs : ∀ lib ∈ c.libraries, ∀ g ∈ lib.globs, ∃ n, g = .one n
  /-- Each target's name is a closed module name, because Lake joins a name onto its output directories. -/
  targetNames : ∀ n ∈ c.targetNames, ClosedModuleName n
  /-- No two targets share a name, which Lake's load refuses (`decodeTargetDecls`, `Lake/Load/Toml.lean:451`). -/
  distinctTargets : c.targetNames.Nodup
  /-- The claim holds a module: a pass that claims nothing says nothing. -/
  claimsSomething : c.claim ≠ []
  /-- One name, one file: the targets that hold a module name it with one file, up to spelling, because the build makes
  one output for a name and an admission must be about the file that output comes from. -/
  oneFile : ∀ x ∈ c.claim, ∀ y ∈ c.claim, x.1 = y.1 → x.2 = y.2
  /-- An import of a claimed name reaches that same file. -/
  resolvesToClaim : ∀ x ∈ c.claim, ∀ rel, c.resolve x.1 = some rel → rel = x.2
  /-- Each default target names a target, because Lake's build refuses one that names nothing. -/
  defaultsDeclared : ∀ n ∈ c.defaultTargets, n ∈ c.targetNames

end Configuration

/-! ## What the project's files hold -/

/-- A Lean file of the project, as a read gave it. -/
structure SourceFile where
  /-- The module whose file this is. -/
  module : Name
  /-- Its path below the project, by components. -/
  rel : List String
  /-- Its text. -/
  text : String
  /-- What its header imports. -/
  imports : Array Import
  /-- What Lean's parser makes of its text, in the context this file sees. -/
  read : FileRead

/-- A project, as its author's files state it. -/
structure Project where
  /-- The text of `lean-toolchain`, if the project holds it as a plain file: no link on the way. -/
  toolchainFile : Option String
  /-- Whether anything has the name `lakefile.lean`, a link with no target included. -/
  leanConfig : Bool
  /-- The text of `lakefile.toml`, if the project holds it as a plain file: no link on the way. -/
  configFile : Option String
  /-- What that text says. -/
  config : Configuration
  /-- Each Lean file that the claim reaches through its imports, which is a plain file: no link on the way. -/
  sources : List SourceFile
  /-- The modules of the toolchain's own library that a file of the project imports. -/
  toolchainModules : List Name

namespace Project

variable (p : Project)

/-- **The domain of the full verdict.** A project is inside it when each of these holds. A project outside it is refused
by a reason that says which, and a project inside it is owed a pass when the reads answer as its files state, the Lake
commands succeed and the rules hold (`domain_owed`). -/
structure InDomain : Prop where
  /-- `lean-toolchain` is a plain file that names the one Lean this revision reads. -/
  toolchain : ∃ text, p.toolchainFile = some text ∧ text.trimAscii.toString = leanToolchain
  /-- No `lakefile.lean`, because Lake prefers it and runs it. -/
  noLeanConfig : p.leanConfig = false
  /-- `lakefile.toml` is a plain file. -/
  plainConfig : p.configFile.isSome = true
  /-- What it says lies inside the domain. -/
  config : p.config.InDomain
  /-- Each module of the claim has its file among the sources. -/
  claimRead : ∀ x ∈ p.config.claim, ∃ s ∈ p.sources, s.module = x.1 ∧ s.rel = x.2
  /-- Each source is the file of its module, as the claim or an import names it. -/
  sourceFile : ∀ s ∈ p.sources, (s.module, s.rel) ∈ p.config.claim ∨ p.config.resolve s.module = some s.rel
  /-- Each module has one source. -/
  oneSource : (p.sources.map (·.module)).Nodup
  /-- An import names a library's module that is among the sources, or a module of the toolchain's own library. So an
  import of an executable's root that no library holds is outside: Lake's resolution covers libraries alone. -/
  imports : ∀ s ∈ p.sources, ∀ i ∈ s.imports,
    (∃ s' ∈ p.sources, s'.module = i.module ∧ p.config.resolve i.module = some s'.rel) ∨
      (i.module ∈ p.toolchainModules ∧ p.config.resolve i.module = none ∧ (p.config.claim.lookup i.module).isNone)
  /-- Each module's name is a closed module name. -/
  moduleNames : ∀ s ∈ p.sources, ClosedModuleName s.module
  /-- Each module of the toolchain that a file imports has a closed name. -/
  toolchainNames : ∀ m ∈ p.toolchainModules, ClosedModuleName m
  /-- Mathlib is nowhere in the imports, because its code runs when it is imported. -/
  noMathlib : (∀ s ∈ p.sources, s.module.getRoot ≠ `Mathlib) ∧ ∀ m ∈ p.toolchainModules, m.getRoot ≠ `Mathlib
  /-- Each file is in the closed language. -/
  language : ∀ s ∈ p.sources, s.read.module = s.module ∧ FileAdmitted s.read
  /-- One path, one text: two sources at one path hold one text, as one file does. -/
  oneText : ∀ s ∈ p.sources, ∀ s' ∈ p.sources, s.rel = s'.rel → s.text = s'.text
  /-- A source has one role: no module's file is one of the files Lake takes as configuration or that names the toolchain.
  That its name is no other spelling of `lakefile.lean` on the tree's volume is what the file system answers, and not a
  statement about text: see `Answers.leanConfigAbsent`. -/
  oneRole : ∀ s ∈ p.sources, s.rel ≠ ["lakefile.lean"] ∧ s.rel ≠ ["lakefile.toml"] ∧ s.rel ≠ ["lean-toolchain"]
  /-- No component of a source's path is empty or starts with `.`, which a relative source directory and a closed module name give. -/
  sourcePath : ∀ s ∈ p.sources, ∀ c ∈ s.rel, c ≠ "" ∧ c.front ≠ '.'
  /-- The roots and the imports stay within what the reader follows. -/
  bounded : p.config.claim.length + (p.sources.map (·.imports.size)).sum ≤ 1000000

end Project

end RegulaSpecification.Domain
