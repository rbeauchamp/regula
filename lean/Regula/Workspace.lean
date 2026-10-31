import Lake.Load.Workspace
import Regula.Load

/-!
# Lake's load of the workspace

The part of the loader that calls Lake: Lake's load of the workspace (`Lake.loadWorkspace`), the
root package's targets, and the bundle of a finished build (`loadBundle`), which starts from them.

This module is in the excluded library `Regula`, and the rest of the loader is in the claimed library
`RegulaChecker`. Lake declares each entry of its open families of data types as an axiom, such as
`Lake.DataType.bool` (`Lake/Util/Family.lean`, `Lake/Config/Kinds.lean` at v4.35.0). So a constant
that calls Lake's load depends on axioms that no profile admits (RG1003, RG1005), and an import of it
puts them in the scope of `lake check`, which refuses them (RG2005). Lake's load is trusted, as the
specification's trusted base states.
-/

namespace Regula.Load

open Lean System
open Regula.Closed

/-- The Lake environment of the toolchain that `LEAN_SYSROOT` names, with the Lake installed beside
its Lean and no inherited search path. -/
def lakeEnvironment : IO Lake.Env := do
  let some sysroot ← IO.getEnv "LEAN_SYSROOT"
    | refuse "LEAN_SYSROOT is not set, so the toolchain of the build is not known: run the \
        checker with `lake lint` or `lake exe`, which set it"
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

/-- The target of a library as Lake configures it, with `modules` the modules Lake builds for it. -/
def targetOf (ws : Lake.Workspace) (lib : Lake.LeanLib) (kind : TargetKind) (name : Name)
    (modules : List Name) : Target :=
  let (dOptions, args) := splitArgs (lib.weakLeanArgs ++ lib.leanArgs).toList
  { name, kind, modules
    options := lib.leanOptions.values.toList.map (fun (n, v) => (n, optionText v)) ++ dOptions
    extras := args ++ lib.plugins.toList.map (fun t => s!"plugin {t.key}") ++
      lib.dynlibs.toList.map (fun t => s!"dynamic library {t.key}")
    isDefault := ws.root.defaultTargets.contains name }

/-- The root package's library and executable targets. -/
def targets (ws : Lake.Workspace) : IO (List Target) := do
  let mut out := []
  for lib in ws.root.leanLibs do
    let modules ← lib.getModuleArray
    out := out ++ [targetOf ws lib .library lib.name (modules.map (·.name)).toList]
  for exe in ws.root.leanExes do
    out := out ++ [targetOf ws exe.toLeanLib .executable exe.name [exe.root.name]]
  return out

/-- The closed input of the selected finished build, or an error that refuses it. An implicit
selection must match Lake's dispatch (`dispatchedFrom_iff`). Each environment is imported, read
into the input, copied out of its data, and freed with `free` before the next one is imported. -/
def loadBundle (free : Environment → IO Unit) (selection : WorkspaceSelection) : IO Bundle := do
  let dir := selection.directory
  let ws ← loadWorkspace dir
  match selection with
  | .dispatched =>
    let received := (((← IO.getEnv "LEAN_PATH").map SearchPath.parse).getD []).map toString
    unless dispatchedFrom ws.root.leanLibDir.toString ws.lakeEnv.lake.libDir.toString
        received do
      refuse "the current directory is not the workspace Lake dispatched; run `lake lint` \
        from that workspace's directory"
  | .named _ => pure ()
  searchPathRef.set ws.augmentedLeanPath
  let ts ← targets ws
  let manifest ← claim dir
  let files ← rootModules ws.root.leanLibDir ts
  let records := files.toList.map (·.2.record)
  let claimedTargets := manifest.filterMap fun e => match e.classification with
    | .claimed .. => some e.target
    | .excluded => none
  let claimed : NameSet := ts.foldl (init := {}) fun s t =>
    if claimedTargets.contains t.name then t.modules.foldl (·.insert ·) s else s
  let root : NameSet := files.foldl (fun s m _ => s.insert m) {}
  let mut envs := []
  let mut known : AxiomSets := {}
  for g in ← groups files ts do
    let env ← try importModules (g.imports.map ({ module := · })) {} (loadExts := false)
      catch e => refuse s!"Lean could not load the modules {g.imports.toList}: {e}"
    let f ← facts env ws.lakeEnv.lean.leanLibDir claimed root
    let raw ← match f.input ts manifest records known with
      | .ok raw => pure raw
      | .error why => refuse why
    let input ← (copyInput raw).run' {}
    free env
    for d in input.decls do
      if let some axs := d.axioms then known := known.insert (d.module, d.name) axs
    envs := envs ++ [input]
  return { envs }

end Regula.Load
