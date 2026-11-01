/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lake.Config.Glob
public import Lake.Toml.Data.Value
public import Lean.Environment
public import Lean.Parser.Module

/-!
# The effects of the checker

The checker's program is a value of `Prog`: a tree whose every node names one operation of the closed
type `Op`, with what to do for each response that operation can give. Nothing in the tree performs an
effect. `Prog.interpret` runs a tree: it performs each operation through a table, and passes the response
to the rest. So a decision of the checker is pure code in the tree, about whatever a response holds, and a
theorem about the tree holds for every response, a failure included, with no assumption that the file system
stays still.

A failure is a response. Each operation that can fail gives an `Except`, so the interpreter runs in `BaseIO`,
whose type holds no exception, and the tree has one way out: its leaf.

`L` and `E` stand for two values of Lake and Lean that the tree passes on and never reads: a library, whose
modules Lake lists, and the environment that Lean's parser reads. The checker runs at `Lake.LeanLib` and
`Lean.Environment`, and each theorem holds at every type.
-/

public section

namespace Regula.Effect

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState)
open System (FilePath)

/-- What Lake's load gives of the root package and its workspace, each field a projection of that load. -/
structure Root (L : Type) where
  /-- The source directories that the configuration names: the package's, each library's and each
  executable's. -/
  sourceDirs : List FilePath
  /-- Each library, with the entries of its `globs`. -/
  libraries : List (Name × List Lake.Glob)
  /-- The default targets of the root package. -/
  defaultTargets : List Name
  /-- The library of a name, by Lake's own search. -/
  findLib : Name → Option L
  /-- The root module of the executable of a name, with its file, by Lake's own search. -/
  findExe : Name → Option (Name × FilePath)
  /-- The names of the package's libraries and executables, which Lake joins onto its output directories. -/
  targets : List Name
  /-- The file of a module, by Lake's own resolution of an import. -/
  resolve : Name → Option FilePath
  /-- The search path of the workspace (`Workspace.augmentedLeanPath`). -/
  leanPath : List FilePath
  /-- The toolchain's library directories, Lean's and Lake's. -/
  toolchain : List FilePath
  /-- Lean's library directory. -/
  leanLib : FilePath
  /-- The root package's library directory. -/
  rootLib : FilePath

/-- The operations of the checker: the closed set of what its program can ask of Lean, Lake and the
operating system. -/
inductive Op (L E : Type) where
  /-- The version and commit of this Lean. -/
  | leanVersion
  /-- An environment variable. -/
  | getEnv (name : String)
  /-- The path of this program. -/
  | appPath
  /-- The real path of a path. -/
  | realPath (path : FilePath)
  /-- The text of a file. -/
  | readFile (path : FilePath)
  /-- What the file system holds of this name, following no link. -/
  | symlinkMetadata (path : FilePath)
  /-- Write the text of a file. -/
  | writeFile (path : FilePath) (text : String)
  /-- Make a directory and its parents. -/
  | createDirAll (path : FilePath)
  /-- Make a new temporary directory. -/
  | createTempDir
  /-- Remove a directory and what it holds. -/
  | removeDirAll (path : FilePath)
  /-- Print a line. -/
  | println (text : String)
  /-- Flush standard output. -/
  | flush
  /-- Lean's parser, on the header of a file. -/
  | parseHeader (input : InputContext)
  /-- Lean's parser, on one command of a file. -/
  | parseCommand (input : InputContext) (env : E) (state : ModuleParserState) (messages : MessageLog)
  /-- Set Lean's search path for modules. -/
  | setSearchPath (path : List FilePath)
  /-- Where Lean finds the `.olean` of a module on that search path. -/
  | findOLean (module : Name)
  /-- Load the modules of a finished build, for the rules. -/
  | importForRules (modules : Array Name)
  /-- Load modules of the toolchain, for Lean's parser. -/
  | importForParser (modules : List Name)
  /-- Lake's TOML parser. -/
  | parseToml (input : InputContext)
  /-- The Lake that lies beside the Lean of a system root: its program and its library directory. -/
  | lakeInstall (sysroot : String)
  /-- Lake's load of a workspace with its dependencies. -/
  | loadWorkspace (sysroot : String) (dir : FilePath)
  /-- Lake's load of a root package's `lakefile.toml` alone, with no manifest and no dependency. -/
  | loadRoot (sysroot : String) (dir : FilePath)
  /-- The modules of a library, with the file Lake compiles for each. -/
  | libModules (lib : L)
  /-- A Lake command in a directory: its exit code. -/
  | runLake (program : FilePath) (cwd : FilePath) (args : List String)

/-- What each operation can give. An operation that can fail gives its failure as a value. -/
@[expose] def Resp {L E : Type} : Op L E → Type
  | .leanVersion => String × String
  | .getEnv _ => Option String
  | .appPath => Except IO.Error FilePath
  | .realPath _ => Except IO.Error FilePath
  | .readFile _ => Except IO.Error String
  | .symlinkMetadata _ => Except IO.Error IO.FS.Metadata
  | .writeFile _ _ => Except IO.Error Unit
  | .createDirAll _ => Except IO.Error Unit
  | .createTempDir => Except IO.Error FilePath
  | .removeDirAll _ => Except IO.Error Unit
  | .println _ => Except IO.Error Unit
  | .flush => Except IO.Error Unit
  | .parseHeader _ => Except IO.Error (Syntax × ModuleParserState × MessageLog × Array Import)
  | .parseCommand .. => Syntax × ModuleParserState × MessageLog
  | .setSearchPath _ => Unit
  | .findOLean _ => Except IO.Error FilePath
  | .importForRules _ => Except IO.Error Environment
  | .importForParser _ => Except IO.Error (E × List Name)
  | .parseToml _ => Except MessageLog Lake.Toml.Table
  | .lakeInstall _ => FilePath × FilePath
  | .loadWorkspace .. => Except String (Option (Root L) × List String)
  | .loadRoot .. => Except String (Option (Root L) × List String)
  | .libModules _ => Except IO.Error (Array (Name × FilePath))
  | .runLake .. => Except IO.Error UInt32

/-- A program: the value it ends with, or one operation and what follows each response to it. -/
inductive Prog (L E α : Type) where
  /-- The program ends with this value. -/
  | done (a : α)
  /-- Ask this operation, and go on with what its response selects. -/
  | ask (o : Op L E) (next : Resp o → Prog L E α)

namespace Prog

variable {L E α β : Type}

/-- The program `p`, and then what its value selects. -/
def bind : Prog L E α → (α → Prog L E β) → Prog L E β
  | .done a, f => f a
  | .ask o next, f => .ask o fun r => bind (next r) f

instance : Monad (Prog L E) where
  pure := .done
  bind := bind

/-- Ask one operation, and end with its response. -/
def call (o : Op L E) : Prog L E (Resp o) :=
  .ask o .done

/-- Run a program: perform each operation through `table`, and go on with its response. -/
def interpret (table : (o : Op L E) → BaseIO (Resp o)) : Prog L E α → BaseIO α
  | .done a => pure a
  | .ask o next => do
    let r ← table o
    interpret table (next r)

end Prog

end Regula.Effect
