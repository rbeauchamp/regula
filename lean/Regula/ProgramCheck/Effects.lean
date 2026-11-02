/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Regula.Workspace
import all Regula.Workspace
meta import Lean.Elab.Command
meta import Lean.Util.Path
meta import Regula.ProgramCheck.EffectScan
public import Regula.Table
public import Regula.LintMain
public import Regula.Contract
public import Regula.Decision

/-! # Where the effects of the repository's code lie

This module checks the specification's section "So thin that it only calls Lean" where the
specification's package cannot, because a constant that calls Lake's load depends on axioms that no
profile admits, and `lake check` of that package would refuse them. The theorems below state, each by
`rfl`, that each row of `Regula.Load.lakeCalls` is a straight line of calls of Lake. The check reads,
through Lean's own environment and at the level where bodies are held, each constant of the
repository's Lean libraries that the executable and the library that gives no verdict reach, and fails
the build on a constant outside the allowed modules whose type, or whose value as a definition,
mentions an effect, directly or through another constant of the repository. So a decision that comes
to mention one in `Regula.Reader`, `Regula.Shell` or `Regula.Load` fails the gate.
-/

public section

namespace Regula.ProgramCheck.Effects

open Lean

theorem parseToml_row : Regula.Load.lakeCalls.parseToml = fun input => (Lake.Toml.loadToml input).toBaseIO := by
  rfl

theorem lakeInstall_row : Regula.Load.lakeCalls.lakeInstall = fun sysroot => do
    let lake := Lake.LakeInstall.ofLean (← Lake.LeanInstall.get sysroot (collocated := true))
    return (lake.lake, lake.libDir) := by
  rfl

theorem loadWorkspace_row : Regula.Load.lakeCalls.loadWorkspace = fun sysroot wsDir => EIO.toBaseIO do
    let lakeEnv ← Regula.Load.lakeEnvironment sysroot
    let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
    return (ws?.map Regula.Load.rootOf, Regula.Load.messagesOf log) := by
  rfl

theorem loadRoot_row : Regula.Load.lakeCalls.loadRoot = fun sysroot wsDir => EIO.toBaseIO do
    let lakeEnv ← Regula.Load.lakeEnvironment sysroot
    let (ws?, log) ← Lake.ELogT.run? (m := BaseIO)
      (Lake.loadWorkspaceRoot { lakeEnv, wsDir, relConfigFile := "lakefile.toml" })
    return (ws?.map Regula.Load.rootOf, Regula.Load.messagesOf log) := by
  rfl

theorem libModules_row : Regula.Load.lakeCalls.libModules = fun lib => EIO.toBaseIO do
    return (← lib.getModuleArray).map fun m => (m.name, m.leanFile) := by
  rfl

theorem rootOf_eq (ws : Lake.Workspace) : Regula.Load.rootOf ws =
    { sourceDirs := ws.root.srcDir :: (ws.root.leanLibs.map (·.srcDir)).toList ++
        (ws.root.leanExes.map (·.root.lib.srcDir)).toList
      libraries := (ws.root.leanLibs.map fun lib => (lib.name, lib.config.globs.toList)).toList
      defaultTargets := ws.root.defaultTargets.toList
      findLib := ws.root.findLeanLib?
      findExe := fun target => (ws.root.findLeanExe? target).map fun exe => (exe.root.name, exe.root.leanFile)
      targets := (ws.root.leanLibs.map (·.name)).toList ++ (ws.root.leanExes.map (·.name)).toList
      resolve := fun m => (ws.findModule? m).map (·.leanFile)
      leanPath := ws.augmentedLeanPath
      toolchain := [ws.lakeEnv.lean.leanLibDir, ws.lakeEnv.lake.libDir]
      leanLib := ws.lakeEnv.lean.leanLibDir
      rootLib := ws.root.leanLibDir } := by
  rfl

theorem messagesOf_eq (log : Lake.Log) :
    Regula.Load.messagesOf log = (log.entries.map (·.message)).toList := by
  rfl

theorem lakeEnvironment_eq (sysroot : String) : Regula.Load.lakeEnvironment sysroot = (do
    let lean ← Lake.LeanInstall.get sysroot (collocated := true)
    let env ← Lake.Env.compute (Lake.LakeInstall.ofLean lean) lean (← Lake.findElanInstall?)
    return { env with initLeanPath := [], initLeanSrcPath := [] }) := by
  rfl

run_cmd do
  initSearchPath (← findSysroot)
  let mods := #[`Regula.LintMain, `Regula.Contract, `Regula.Decision]
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := false) (level := .private)
  match EffectScan.judge (EffectScan.scan (EffectScan.graphOf env)) with
  | .ok () => pure ()
  | .error why => throwError why

end Regula.ProgramCheck.Effects
