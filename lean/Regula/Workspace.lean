import Lake.Load.Workspace
import Regula.Load

/-!
# Lake's load of the workspace

The part of the loader that calls Lake: Lake's load of the workspace (`Lake.loadWorkspace`), the
modules of the root package's default targets, and the import of the environment (`loadInput`).

This module is in the library `Regula`, which is no default target. Lake declares each entry of its
open families of data types as an axiom, such as `Lake.DataType.bool` (`Lake/Util/Family.lean`,
`Lake/Config/Kinds.lean` at v4.35.0). So a constant that calls Lake's load depends on axioms that no
profile admits, and an import of it puts them in the scope of `lake check`, which refuses them.
Lake's load is trusted.
-/

namespace Regula.Load

open Lean System
open Regula.Closed

/-- The Lake environment of the toolchain that `LEAN_SYSROOT` names, with the Lake installed beside
its Lean and no inherited search path. -/
def lakeEnvironment : IO Lake.Env := do
  let some sysroot ← IO.getEnv "LEAN_SYSROOT"
    | refuse "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the \
        checker with `lake lint`, which sets it"
  let lean ← Lake.LeanInstall.get sysroot (collocated := true)
  let lake := Lake.LakeInstall.ofLean lean
  match ← (Lake.Env.compute lake lean (← Lake.findElanInstall?)).toBaseIO with
  | .ok env => return { env with initLeanPath := [], initLeanSrcPath := [] }
  | .error why => refuse s!"Lake could not compute its environment: {why}"

/-- Lake's load of the workspace whose root is `dir`. -/
def loadWorkspace (dir : FilePath) : IO Lake.Workspace := do
  let lakeEnv ← lakeEnvironment
  let wsDir ← IO.FS.realPath dir
  let (ws?, log) ← (Lake.loadWorkspace { lakeEnv, wsDir }).captureLog
  match ws? with
  | some ws => return ws
  | none =>
    refuse s!"Lake could not load the workspace at {dir}: \
      {"; ".intercalate (log.entries.map (·.message)).toList}"

/-- The modules that the default targets of the root package name: each module of a default library,
and the root of each default executable. A default target that is neither builds no Lean module
(`Package.recCollectDefaultModules`, `Lake/Build/Package.lean:45-61` at v4.35.0). -/
def defaultModules (ws : Lake.Workspace) : IO (Array Name) := do
  let mut out := #[]
  for target in ws.root.defaultTargets do
    if let some lib := ws.root.findLeanLib? target then
      out := out ++ (← lib.getModuleArray).map (·.name)
    else if let some exe := ws.root.findLeanExe? target then
      out := out.push exe.root.name
  return out

/-- The closed input of the finished build of the workspace that Lake dispatched from the current
directory, or an error that refuses it. -/
def loadInput (profile : Profile) : IO Input := do
  let ws ← loadWorkspace "."
  let received := (((← IO.getEnv "LEAN_PATH").map SearchPath.parse).getD []).map toString
  unless dispatchedFrom ws.root.leanLibDir.toString ws.lakeEnv.lake.libDir.toString received do
    refuse "the current directory is not the workspace Lake dispatched; run `lake lint` from that \
      workspace's directory"
  searchPathRef.set ws.augmentedLeanPath
  let roots ← defaultModules ws
  let env ← try importModules (roots.map ({ module := · })) {} (loadExts := false)
    catch e => refuse s!"Lean could not load the modules of the default targets: {e}"
  let f ← facts env ws.lakeEnv.lean.leanLibDir ws.root.leanLibDir
  for m in roots do
    unless f.claimed.contains m do
      refuse s!"the module {m} of a default target has its .olean outside the root package's build \
        {ws.root.leanLibDir}"
  match f.input profile with
  | .ok input => return input
  | .error why => refuse why

end Regula.Load
