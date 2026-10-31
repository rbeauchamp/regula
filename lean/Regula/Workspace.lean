/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

public import Lake.Load.Workspace
public import Lake.Toml.Load
public import Regula.Reader

/-!
# The calls of Lake

Direct calls of Lake and nothing else: its environment, its TOML parser, its loads of a workspace, the
source directories and `globs` entries of the configuration, the modules of the default targets with their
source files, its resolver of an import, and its program's path.
What decides anything from their results is in `Regula.Load` and `Regula.Reader`, which are in a default
target.

This module is in the library `Regula`, which is no default target. Lake declares each entry of its
open families of data types as an axiom, such as `Lake.DataType.bool` (`Lake/Util/Family.lean`,
`Lake/Config/Kinds.lean` at v4.35.0). So a constant that calls Lake's load depends on axioms that no
profile admits, and an import of it puts them in the scope of `lake check`, which refuses them.
Lake's load is trusted.
-/

public section

namespace Regula.Load

open Lean (Name)
open System (FilePath)
open Regula.Closed

/-- The Lake environment of the toolchain that `LEAN_SYSROOT` names, with the Lake installed beside
its Lean and no inherited search path. -/
def lakeEnvironment : IO Lake.Env := do
  let some sysroot ← IO.getEnv "LEAN_SYSROOT"
    | refuse "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the \
        checker with `lake lint` or `lake exe lint`, which set it"
  let lean ← Lake.LeanInstall.get sysroot (collocated := true)
  let lake := Lake.LakeInstall.ofLean lean
  match ← (Lake.Env.compute lake lean (← Lake.findElanInstall?)).toBaseIO with
  | .ok env => return { env with initLeanPath := [], initLeanSrcPath := [] }
  | .error why => refuse s!"Lake could not compute its environment: {why}"

/-- Lake's load of the workspace whose root is `dir`, with its dependencies: the plain `lake lint`, whose
workspace Lake has already loaded before this program starts. -/
def loadWorkspace (dir : FilePath) : IO Lake.Workspace := do
  let lakeEnv ← lakeEnvironment
  let wsDir ← IO.FS.realPath dir
  let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
  match ws? with
  | some ws => return ws
  | none =>
    refuse s!"Lake could not load the workspace at {dir}: \
      {"; ".intercalate (log.entries.map (·.message)).toList}"

/-- Lake's load of the root package at `dir` from its `lakefile.toml`: its configuration only, with no
manifest and no dependency (`Lake/Load/Workspace.lean:31-47` at v4.35.0), which does not prefer a
`lakefile.lean` that lies there (`Lake/Load/Package.lean:100-105`). -/
def loadRootWorkspace (dir : FilePath) : IO Lake.Workspace := do
  let lakeEnv ← lakeEnvironment
  let wsDir ← IO.FS.realPath dir
  let (ws?, log) ← Lake.ELogT.run? (m := BaseIO) (Lake.loadWorkspaceRoot { lakeEnv, wsDir, relConfigFile := "lakefile.toml" })
  match ws? with
  | some ws => return ws
  | none =>
    refuse s!"Lake could not load the configuration at {dir}: \
      {"; ".intercalate (log.entries.map (·.message)).toList}"

/-- The modules that the default targets of the root package name, with the file Lake compiles for each:
each module of a default library, and the root of each default executable. A default target that is
neither builds no Lean module (`Package.recCollectDefaultModules`, `Lake/Build/Package.lean:45-61` at
v4.35.0). `getModuleArray` lists a directory for a `globs` entry other than a single module
(`Glob.forEachModuleIn`, `Lake/Config/Glob.lean:53-59`): the reader calls this for the full gate only after
it has tested each entry through `rootOf`, and the plain `lake lint` keeps Lake's own listing. -/
def defaultModules (ws : Lake.Workspace) : IO (Array (Name × FilePath)) := do
  let mut out := #[]
  for target in ws.root.defaultTargets do
    if let some lib := ws.root.findLeanLib? target then
      out := out ++ (← lib.getModuleArray).map fun m => (m.name, m.leanFile)
    else if let some exe := ws.root.findLeanExe? target then
      out := out.push (exe.root.name, exe.root.leanFile)
  return out

/-- What the reader asks of the root package's configuration, from Lake's load of it. Building this lists no
directory, and `modules` is the action that can. -/
def rootOf (ws : Lake.Workspace) : Regula.Reader.Root where
  sourceDirs :=
    ws.root.srcDir :: (ws.root.leanLibs.map (·.srcDir)).toList ++ (ws.root.leanExes.map (·.root.lib.srcDir)).toList
  libraries := (ws.root.leanLibs.map fun lib =>
    (lib.name, lib.config.globs.all fun | .one _ => true | _ => false)).toList
  modules := return (← defaultModules ws).toList
  targets := (ws.root.leanLibs.map (·.name)).toList ++ (ws.root.leanExes.map (·.name)).toList
  resolve := fun m => (ws.findModule? m).map (·.leanFile)
  toolchain := [ws.lakeEnv.lean.leanLibDir, ws.lakeEnv.lake.libDir]

/-- Lake's calls, for the reader. -/
def lakeCalls : Regula.Reader.LakeCalls where
  program := return (← lakeEnvironment).lake.lake
  libDir := return (← lakeEnvironment).lake.libDir
  parseToml := fun input =>
    EIO.toIO (fun _ => IO.userError "Lake's TOML parser refused it") (Lake.Toml.loadToml input)
  loadRoot := fun dir => return rootOf (← loadRootWorkspace dir)

/-- The closed input of the finished build of the workspace `ws`, or an error that refuses it. -/
def inputOf (ws : Lake.Workspace) (profile : Profile) : IO Input := do
  inputFrom ws.augmentedLeanPath ((← defaultModules ws).map (·.1)) ws.lakeEnv.lean.leanLibDir
    ws.root.leanLibDir profile

/-- The closed input of the finished build of the workspace that Lake dispatched from the current
directory, or an error that refuses it. -/
def loadInput (profile : Profile) : IO Input := do
  let ws ← loadWorkspace "."
  requireDispatched ws.root.leanLibDir ws.lakeEnv.lake.libDir
  inputOf ws profile

/-- The closed input of the finished build at `dir`, for a checker that Lake started from another
workspace (`Regula.Reader.startedOutside`), through the root package's load alone. The full gate calls it only
after the check admitted the project, so each `globs` entry is a single module and it lists no directory. -/
def loadInputAt (dir : FilePath) (profile : Profile) : IO Input := do
  inputOf (← loadRootWorkspace dir) profile

end Regula.Load
