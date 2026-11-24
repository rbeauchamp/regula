module

public import Lake.Config.Glob
public import Lake.Toml.Data.Value
public import Lean.Environment
public import Lean.Parser.Module

public section

namespace Regula.Effect

open Lean (Name Syntax Environment Import MessageLog ConstantInfo)
open Lean.Parser (InputContext ModuleParserState)
open System (FilePath)

structure Root (L : Type) where
  sourceDirs : List FilePath
  libraries : List (Name × List Lake.Glob)
  defaultTargets : List Name
  findLib : Name → Option L
  findExe : Name → Option (Name × FilePath)
  targets : List Name
  resolve : Name → Option FilePath
  leanPath : List FilePath
  toolchain : List FilePath
  leanLib : FilePath
  rootLib : FilePath

inductive Op (L E : Type) where
  | leanVersion
  | getEnv (name : String)
  | realPath (path : FilePath)
  | readFile (path : FilePath)
  | symlinkMetadata (path : FilePath)
  | writeFile (path : FilePath) (text : String)
  | createDirAll (path : FilePath)
  | createTempDir
  | removeDirAll (path : FilePath)
  | println (text : String)
  | flush
  | parseHeader (input : InputContext)
  | parseCommand (input : InputContext) (env : E) (state : ModuleParserState) (messages : MessageLog)
  | findOLean (path : List FilePath) (module : Name)
  | importForRules (path : List FilePath) (modules : Array Name)
  | importForParser (path : List FilePath) (modules : List Name)
  | kernelReplay (constants : Std.HashMap Name ConstantInfo)
  | parseToml (input : InputContext)
  | lakeInstall (sysroot : String)
  | loadWorkspace (sysroot : String) (dir : FilePath)
  | loadRoot (sysroot : String) (dir : FilePath)
  | libModules (lib : L)
  | runLake (program : FilePath) (cwd : FilePath) (args : List String)

@[expose] def Resp {L E : Type} : Op L E → Type
  | .leanVersion => String × String
  | .getEnv _ => Option String
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
  | .findOLean .. => Except IO.Error FilePath
  | .importForRules .. => Except IO.Error Environment
  | .importForParser .. => Except IO.Error (E × List Name)
  | .kernelReplay _ => Except IO.Error Unit
  | .parseToml _ => Except MessageLog Lake.Toml.Table
  | .lakeInstall _ => FilePath × FilePath
  | .loadWorkspace .. => Except String (Option (Root L) × List String)
  | .loadRoot .. => Except String (Option (Root L) × List String)
  | .libModules _ => Except IO.Error (Array (Name × FilePath))
  | .runLake .. => Except IO.Error UInt32

inductive Prog (L E α : Type) where
  | done (a : α)
  | ask (o : Op L E) (next : Resp o → Prog L E α)

namespace Prog

variable {L E α β : Type}

def bind : Prog L E α → (α → Prog L E β) → Prog L E β
  | .done a, f => f a
  | .ask o next, f => .ask o fun r => bind (next r) f

instance : Monad (Prog L E) where
  pure := .done
  bind := bind

def call (o : Op L E) : Prog L E (Resp o) :=
  .ask o .done

def interpret (table : (o : Op L E) → BaseIO (Resp o)) : Prog L E α → BaseIO α
  | .done a => pure a
  | .ask o next => do
    let r ← table o
    interpret table (next r)

end Prog

end Regula.Effect
