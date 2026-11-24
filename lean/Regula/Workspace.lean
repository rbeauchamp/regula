module

public import Lake.Load.Workspace
public import Lake.Toml.Load
public import Regula.Table

public section

namespace Regula.Load

open System (FilePath)
open Regula.Effect

def lakeEnvironment (sysroot : String) : EIO String Lake.Env := do
  let lean ← Lake.LeanInstall.get sysroot (collocated := true)
  let env ← Lake.Env.compute (Lake.LakeInstall.ofLean lean) lean (← Lake.findElanInstall?)
  return { env with initLeanPath := [], initLeanSrcPath := [] }

def rootOf (ws : Lake.Workspace) : Root Lake.LeanLib where
  sourceDirs :=
    ws.root.srcDir :: (ws.root.leanLibs.map (·.srcDir)).toList ++ (ws.root.leanExes.map (·.root.lib.srcDir)).toList
  libraries := (ws.root.leanLibs.map fun lib => (lib.name, lib.config.globs.toList)).toList
  defaultTargets := ws.root.defaultTargets.toList
  findLib := ws.root.findLeanLib?
  findExe := fun target => (ws.root.findLeanExe? target).map fun exe => (exe.root.name, exe.root.leanFile)
  targets := (ws.root.leanLibs.map (·.name)).toList ++ (ws.root.leanExes.map (·.name)).toList
  resolve := fun m => (ws.findModule? m).map (·.leanFile)
  leanPath := ws.augmentedLeanPath
  toolchain := [ws.lakeEnv.lean.leanLibDir, ws.lakeEnv.lake.libDir]
  leanLib := ws.lakeEnv.lean.leanLibDir
  rootLib := ws.root.leanLibDir

def messagesOf (log : Lake.Log) : List String :=
  (log.entries.map (·.message)).toList

def lakeCalls : LakeCalls Lake.LeanLib where
  parseToml := fun input => (Lake.Toml.loadToml input).toBaseIO
  lakeInstall := fun sysroot => do
    let lake := Lake.LakeInstall.ofLean (← Lake.LeanInstall.get sysroot (collocated := true))
    return (lake.lake, lake.libDir)
  loadWorkspace := fun sysroot wsDir => EIO.toBaseIO do
    let lakeEnv ← lakeEnvironment sysroot
    let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
    return (ws?.map rootOf, messagesOf log)
  loadRoot := fun sysroot wsDir => EIO.toBaseIO do
    let lakeEnv ← lakeEnvironment sysroot
    let (ws?, log) ← Lake.ELogT.run? (m := BaseIO)
      (Lake.loadWorkspaceRoot { lakeEnv, wsDir, relConfigFile := "lakefile.toml" })
    return (ws?.map rootOf, messagesOf log)
  libModules := fun lib => EIO.toBaseIO do
    return (← lib.getModuleArray).map fun m => (m.name, m.leanFile)

end Regula.Load
