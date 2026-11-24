module

public import Lean.Elab.Import
public import Regula.Effect
public import Lean.Util.Path
public import Lean.Replay
import Lean.Parser.Extension

public section

namespace Regula.Effect

open Lean (Name Syntax Environment Import MessageLog)
open Lean.Parser (InputContext ModuleParserState)
open System (FilePath)

structure LakeCalls (L : Type) where
  parseToml : InputContext → BaseIO (Except MessageLog Lake.Toml.Table)
  lakeInstall : String → BaseIO (FilePath × FilePath)
  loadWorkspace : String → FilePath → BaseIO (Except String (Option (Root L) × List String))
  loadRoot : String → FilePath → BaseIO (Except String (Option (Root L) × List String))
  libModules : L → BaseIO (Except IO.Error (Array (Name × FilePath)))

def scopedParsersOf (env : Environment) : List Name :=
  (Lean.Parser.parserExtension.ext.getState env).scopedEntries.map.toList.map (·.1)

def spawnLake (program cwd : FilePath) (args : List String) : IO UInt32 := do
  let child ← IO.Process.spawn
    { cmd := "/usr/bin/env", args := #["-i", "PATH=/usr/bin:/bin", "LAKE_ARTIFACT_CACHE=false", program.toString] ++ args.toArray,
      cwd := some cwd, stdin := .null }
  child.wait

def importParsers (enable : BaseIO Unit) (modules : List Name) : IO (Environment × List Name) := do
  enable
  let env ← Lean.importModules (modules.toArray.map ({ module := · })) {} (loadExts := true)
    (level := .exported)
  return (env, scopedParsersOf env)

def table {L : Type} (enable : BaseIO Unit) (lake : LakeCalls L) : (o : Op L Environment) → BaseIO (Resp o)
  | .leanVersion => pure (Lean.versionString, Lean.githash)
  | .getEnv name => IO.getEnv name
  | .realPath path => (IO.FS.realPath path).toBaseIO
  | .readFile path => (IO.FS.readFile path).toBaseIO
  | .symlinkMetadata path => path.symlinkMetadata.toBaseIO
  | .writeFile path text => (IO.FS.writeFile path text).toBaseIO
  | .createDirAll path => (IO.FS.createDirAll path).toBaseIO
  | .createTempDir => IO.FS.createTempDir.toBaseIO
  | .removeDirAll path => (IO.FS.removeDirAll path).toBaseIO
  | .println text => (IO.println text).toBaseIO
  | .flush => (do (← IO.getStdout).flush : IO Unit).toBaseIO
  | .parseHeader input =>
    (do
      let (header, state, messages) ← Lean.Parser.parseHeader input
      return (header.raw, state, messages, Lean.Elab.HeaderSyntax.imports header) :
        IO (Syntax × ModuleParserState × MessageLog × Array Import)).toBaseIO
  | .parseCommand input env state messages =>
    pure (Lean.Parser.parseCommand input { env, options := {} } state messages)
  | .findOLean path module => (do Lean.searchPathRef.set path; Lean.findOLean module : IO FilePath).toBaseIO
  | .importForRules path modules =>
    (do
      Lean.searchPathRef.set path
      Lean.importModules (modules.map ({ module := · })) {} (loadExts := false) (level := .private) : IO Environment).toBaseIO
  | .importForParser path modules =>
    (do Lean.searchPathRef.set path; importParsers enable modules : IO (Environment × List Name)).toBaseIO
  | .kernelReplay constants =>
    (do let _ ← (← Lean.mkEmptyEnvironment).toKernelEnv.replay constants : IO Unit).toBaseIO
  | .parseToml input => lake.parseToml input
  | .lakeInstall sysroot => lake.lakeInstall sysroot
  | .loadWorkspace sysroot dir => lake.loadWorkspace sysroot dir
  | .loadRoot sysroot dir => lake.loadRoot sysroot dir
  | .libModules lib => lake.libModules lib
  | .runLake program cwd args => (spawnLake program cwd args).toBaseIO

end Regula.Effect
