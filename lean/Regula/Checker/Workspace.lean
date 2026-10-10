import Lake
import Lake.Load
import Regula.Checker.Common

/-!
# In-process Lake workspace loading

In-process Lake workspace loading for checker discovery. A checked project
loads through Lake's own elaborated package model, so `lakefile.lean` and
`lakefile.toml` projects take the same path; no custom Lake facets or
source-format guesses participate. Load failures fail closed.
-/

namespace Regula.Checker.Workspace

open Lean System

/-- The Lake environment of the detected Lean install, with the Lake installed beside that Lean
(`LakeInstall.ofLean`), as the toolchain's `lake` command computes it for itself. Lake's own
`findInstall?` run from this process reads `LAKE_HOME`, which a parent `lake` sets to the
toolchain's root, as the root of a Lake build tree, so it names Lake's library where none
exists, and a build in this process cannot load that library into a module that needs it. -/
private def detectEnvironment : IO _root_.Lake.Env := do
  let (elan?, lean?, _) ← _root_.Lake.findInstall?
  let some lean := lean?
    | throw <| IO.userError "lake-workspace-load-failed: cannot detect a Lean install"
  let lake := _root_.Lake.LakeInstall.ofLean lean
  match ← EIO.toIO' (_root_.Lake.Env.compute lake lean elan?) with
  | .ok env => return env
  | .error error => throw <| IO.userError s!"lake-workspace-load-failed: {error}"

/-- Load the workspace rooted at `repo` with Lake's loader and pass it to
`action`. The action runs in the same process, so it must not retain mutable
workspace state beyond its return value. With `scrubSearchPath`, the inherited
`LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for `scrubbedLeanPathEnv`. Setup may disable
`resolveDependencies` to load only the root configuration without materializing dependencies. -/
def withRootWorkspace {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α)
    (scrubSearchPath := false) (resolveDependencies := true) : IO α := do
  let lakeEnv ← detectEnvironment
  let lakeEnv := if scrubSearchPath then { lakeEnv with initLeanPath := [], initLeanSrcPath := [] }
    else lakeEnv
  let config : _root_.Lake.LoadConfig := { lakeEnv, wsDir := ← IO.FS.realPath repo }
  let (ws?, log) ← (if resolveDependencies then _root_.Lake.loadWorkspace config
    else _root_.Lake.loadWorkspaceRoot config).captureLog
  match ws? with
  | some ws => action ws
  | none =>
      let messages := log.entries.map (·.message)
      throw <| IO.userError <|
        s!"lake-workspace-load-failed: {"; ".intercalate messages.toList}"

/-! ## Builds without Lake's artifact cache

A module that Lake restores from its artifact cache gets a trace with an empty log, so a build
that restores it reports none of its warnings, and the warning-free build check (RG2003) would
pass it. A checker build therefore runs on `uncachedWorkspace`, where no package reads or writes
the cache, after `dropRestoredTraces`, so no root-package module keeps a restored trace. It also
requests the artifacts of each module of the claimed targets it builds, whose traces must then
record an elaboration (`elaborationTrace`). -/

/-- `pkg` with Lake's artifact cache turned off by its own configuration
(`enableArtifactCache? := some false`), and so every package it records as a dependency
(`Package.depPkgs`), at every depth (`uncached_reaches`). -/
def uncachedPackage (pkg : _root_.Lake.Package) : _root_.Lake.Package :=
  { pkg with
    config := { pkg.config with enableArtifactCache? := some false }
    depPkgs := pkg.depPkgs.attach.map fun ⟨dep, _⟩ => uncachedPackage dep }
termination_by pkg
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹dep ∈ pkg.depPkgs›
  cases pkg
  simp_all
  omega

/-- `uncachedPackage` turns the artifact cache off in the package's own configuration. -/
theorem uncachedPackage_config (pkg : _root_.Lake.Package) :
    (uncachedPackage pkg).config.enableArtifactCache? = some false := by
  rw [uncachedPackage]

/-- `uncachedPackage` keeps the package's workspace index. -/
theorem uncachedPackage_wsIdx (pkg : _root_.Lake.Package) :
    (uncachedPackage pkg).wsIdx = pkg.wsIdx := by
  rw [uncachedPackage]

/-- `uncachedPackage` keeps the workspace indices of the package's dependencies. -/
theorem uncachedPackage_depIdxs (pkg : _root_.Lake.Package) :
    (uncachedPackage pkg).depIdxs = pkg.depIdxs := by
  rw [uncachedPackage]

/-- Every dependency package that `uncachedPackage` records is itself an `uncachedPackage`. -/
theorem uncachedPackage_depPkgs (pkg : _root_.Lake.Package) :
    ∀ dep ∈ (uncachedPackage pkg).depPkgs, ∃ original, dep = uncachedPackage original := by
  intro dep h
  rw [uncachedPackage] at h
  simp only [Array.mem_map, Array.mem_attach, true_and, Subtype.exists] at h
  obtain ⟨original, _, rfl⟩ := h
  exact ⟨original, rfl⟩

/-- `target` is `pkg` or a package recorded, at some depth, among the dependency packages
(`Package.depPkgs`) of `pkg`. -/
inductive Reaches : _root_.Lake.Package → _root_.Lake.Package → Prop
  /-- A package reaches itself. -/
  | refl (pkg : _root_.Lake.Package) : Reaches pkg pkg
  /-- A package reaches what a package it records as a dependency reaches. -/
  | dep {pkg dep target : _root_.Lake.Package} :
      dep ∈ pkg.depPkgs → Reaches dep target → Reaches pkg target

private theorem reaches_uncached {start target : _root_.Lake.Package}
    (reach : Reaches start target) :
    (∃ original, start = uncachedPackage original) →
      target.config.enableArtifactCache? = some false := by
  induction reach with
  | refl p =>
    rintro ⟨original, rfl⟩
    exact uncachedPackage_config original
  | dep mem _ ih =>
    rintro ⟨original, rfl⟩
    exact ih (uncachedPackage_depPkgs original _ mem)

/-- Every package an `uncachedPackage` reaches has the artifact cache turned off by its own
configuration. -/
theorem uncached_reaches {pkg target : _root_.Lake.Package}
    (h : Reaches (uncachedPackage pkg) target) :
    target.config.enableArtifactCache? = some false :=
  reaches_uncached h ⟨pkg, rfl⟩

/-- `ws` with every package replaced by its `uncachedPackage`, the package map rebuilt from them
as Lake's own dependency resolution rebuilds it (`Workspace.updateDepPkgs`), and the
environment's cache setting (`LAKE_ARTIFACT_CACHE`, which Lake passes on to the processes it
starts) off as well. A build finds its packages through these: its modules, libraries and
executables through `packages` and the targets each package declares, which carry that package;
a package by its key through `packageMap`; and a package's dependencies through `depPkgs`. -/
def uncachedWorkspace (ws : _root_.Lake.Workspace) : _root_.Lake.Workspace :=
  let packages := ws.packages.map uncachedPackage
  { ws with
    lakeEnv := { ws.lakeEnv with enableArtifactCache? := some false }
    packages
    packageMap := packages.foldl (fun map pkg => map.insert pkg.keyName pkg) {}
    size_packages_pos := by simpa [packages] using ws.size_packages_pos
    packages_wsIdx := fun {i} h => by
      simp [packages, uncachedPackage_wsIdx, ws.packages_wsIdx]
    depIdxs_packages := fun p hp i hi => by
      simp only [packages, Array.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [uncachedPackage_depIdxs] at hi
      simpa [packages] using ws.depIdxs_packages q hq i hi }

/-- Lake v4.34.1 consults `Package.isArtifactCacheReadable` before every read of its artifact
cache in a build and `Package.isArtifactCacheWritable` before every write (`fetchCore` in
`Lake/Build/Module.lean`, `Module.packLtar`, and `buildArtifactUnlessUpToDate` in
`Lake/Build/Common.lean`). For every package that a package of `uncachedWorkspace` reaches, the
first returns `false` whatever the workspace, the environment or the package's own lakefile say. -/
theorem uncachedWorkspace_unreadable {ws : _root_.Lake.Workspace}
    {pkg target : _root_.Lake.Package} (mem : pkg ∈ (uncachedWorkspace ws).packages)
    (reach : Reaches pkg target) {m : Type → Type} [Monad m] [_root_.Lake.MonadWorkspace m] :
    target.isArtifactCacheReadable (m := m) =
      (fun _ => false) <$> _root_.Lake.MonadWorkspace.getWorkspace := by
  simp only [uncachedWorkspace, Array.mem_map] at mem
  obtain ⟨original, _, rfl⟩ := mem
  simp [_root_.Lake.Package.isArtifactCacheReadable, _root_.Lake.Package.enableArtifactCache?,
    uncached_reaches reach]

/-- `uncachedWorkspace_unreadable` for writes: `Package.isArtifactCacheWritable` returns
`false` for every package that a package of `uncachedWorkspace` reaches. -/
theorem uncachedWorkspace_unwritable {ws : _root_.Lake.Workspace}
    {pkg target : _root_.Lake.Package} (mem : pkg ∈ (uncachedWorkspace ws).packages)
    (reach : Reaches pkg target) {m : Type → Type} [Monad m] [_root_.Lake.MonadWorkspace m] :
    target.isArtifactCacheWritable (m := m) =
      (fun _ => false) <$> _root_.Lake.MonadWorkspace.getWorkspace := by
  simp only [uncachedWorkspace, Array.mem_map] at mem
  obtain ⟨original, _, rfl⟩ := mem
  simp [_root_.Lake.Package.isArtifactCacheWritable, _root_.Lake.Package.enableArtifactCache?,
    uncached_reaches reach]

/-- Whether `text`, the content of a module's Lake trace file, records a restore from Lake's
artifact cache instead of a build: Lake v4.34.1 writes such a trace (`BuildMetadata.ofFetch`)
with `synthetic` set and an empty log, and replays that empty log while the trace's input hash
matches. Text that Lake cannot read as a trace is not such a record: Lake rebuilds the module. -/
def restoredTrace (text : String) : Bool :=
  match _root_.Lake.BuildMetadata.parse text with
  | .ok data => data.synthetic
  | .error _ => false

/-- Remove the trace file of every module of the root package of `ws` whose trace records a
restore from Lake's artifact cache (`restoredTrace`): the modules of its Lean libraries, as Lake's
globs give them, and the root module of each of its executables. Lake then has no trace for such
a module, so a build that needs it elaborates it again and records its log. A library whose
modules Lake cannot list, such as one whose glob names a directory that does not exist yet,
contributes none, as it does to a `lake build` of other targets; an audit lists every module of
each claimed library through Lake (`Lake.surfaceInventory`) before it builds, and fails if it
cannot. -/
def dropRestoredTraces (ws : _root_.Lake.Workspace) : IO Unit := do
  let drop (mod : _root_.Lake.Module) : IO Unit := do
    if let .ok text ← (IO.FS.readFile mod.traceFile).toBaseIO then
      if restoredTrace text then IO.FS.removeFile mod.traceFile
  for lib in ws.root.leanLibs do
    if let .ok modules ← lib.getModuleArray.toBaseIO then
      for mod in modules do drop mod
  for exe in ws.root.leanExes do drop exe.root

/-- Whether `text`, the content of a module's Lake trace file, records an elaboration: Lake can
read it as a trace, and it does not record a restore from the artifact cache. Lake v4.34.1 writes
such a trace with the log of the elaboration that produced the module's artifacts, and replays
that log while the trace's input hash matches. -/
def elaborationTrace (text : String) : Bool :=
  match _root_.Lake.BuildMetadata.parse text with
  | .ok data => !data.synthetic
  | .error _ => false

/-- A trace that records an elaboration is not one that `dropRestoredTraces` removes. -/
theorem restoredTrace_eq_false_of_elaborationTrace {text : String}
    (h : elaborationTrace text = true) : restoredTrace text = false := by
  cases parsed : _root_.Lake.BuildMetadata.parse text <;>
    simp_all [elaborationTrace, restoredTrace]

end Regula.Checker.Workspace
