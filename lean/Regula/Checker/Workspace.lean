import Lake
import Lake.Load
import Regula.Checker.Common
import Regula.ToolchainProgram
import Regula.Filesystem

/-!
# In-process Lake workspace loading

In-process Lake workspace loading for checker discovery. A checked project
loads through Lake's own elaborated package model, so `lakefile.lean` and
`lakefile.toml` projects take the same path; no custom Lake facets or
source-format guesses participate. Load failures fail closed.
-/

namespace Regula.Checker.Workspace

open Lean System

/-- The Lake environment of the toolchain's identity-checked installation
(`Regula.Toolchain.sysroot`), with the Lake installed beside its Lean (`LakeInstall.ofLean`), as
the toolchain's `lake` command computes it for itself. Lake's own `findInstall?` is not run: it
reads the running program as a `lake`, so a `lean` beside this checker's executable would select
the checker's build directory as the installation, and it reads `LAKE_HOME`, which a parent `lake`
sets to the toolchain's root, as the root of a Lake build tree. The installation's commit is the
one `Regula.Toolchain.sysroot` checked its `lean` reports. -/
private def detectEnvironment : IO _root_.Lake.Env := do
  let sysroot ← Regula.Toolchain.sysroot
  let elan? ← _root_.Lake.findElanInstall?
  let lean ← _root_.Lake.LeanInstall.get sysroot (collocated := true)
  let lean := { lean with githash := RegulaPolicy.Compiler.commit }
  let lake := _root_.Lake.LakeInstall.ofLean lean
  match ← EIO.toIO' (_root_.Lake.Env.compute lake lean elan?) with
  | .ok env => return env
  | .error error => throw <| IO.userError s!"lake-workspace-load-failed: {error}"

/-- The configuration with which the workspace rooted at `repo` is loaded. With
`scrubSearchPath`, the inherited `LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for
`scrubbedLeanPathEnv`. -/
private def loadConfig (repo : FilePath) (scrubSearchPath : Bool) : IO _root_.Lake.LoadConfig := do
  let lakeEnv ← detectEnvironment
  let lakeEnv := if scrubSearchPath then { lakeEnv with initLeanPath := [], initLeanSrcPath := [] }
    else lakeEnv
  return { lakeEnv, wsDir := ← IO.FS.realPath repo }

/-- Pass the workspace that a load gave to `action`, or fail with the messages of its log. -/
private def withLoaded {α : Type} (ws? : Option _root_.Lake.Workspace) (log : _root_.Lake.Log)
    (action : _root_.Lake.Workspace → IO α) : IO α :=
  match ws? with
  | some ws => action ws
  | none =>
      let messages := log.entries.map (·.message)
      throw <| IO.userError <|
        s!"lake-workspace-load-failed: {"; ".intercalate messages.toList}"

/-! ## The places where Lake removes or replaces entries

Lake v4.34.1 removes and replaces entries itself, in this process, when it loads a package's
configuration, materializes a dependency and builds. Each function below derives, from Lake's own
path functions, the places below which it does so, and the loaders stop before Lake runs unless
`Regula.Filesystem.requireLakePlaces` admits them: each place is below a directory that is its own
real path, and no component from that directory down to the place, nor any entry below a place
that Lake changes at any depth, is a symbolic link (`Regula.Removal.lakePlacesAdmitted_iff`). -/

open _root_.Lake in
/-- The place below which Lake's loader removes and writes the compiled configuration of each
package of the workspace in `wsDir`, at any depth: `.lake/config`. Lake gives the package with
index `i` the directory `i` there (`configDir_eq`), the root package index `0` and each dependency
the next one, with the workspace's directory (`Lake.mkDepLoadConfig`,
`Lake/Load/Resolve.lean:33-39`). There the loader removes the stale `lakefile.olean` and its trace
(`Lake/Load/Lean/Elab.lean:244`, `:262`), opens the lock and the trace for writing (`:207`, `:223`,
`:294`) and writes the new `lakefile.olean` and its siblings through temporary files that it
renames over them (`:256`, `src/library/module.cpp:311-314`, `:403`, `:408`). -/
def configPlace (wsDir : FilePath) : Regula.Removal.LakePlace :=
  { base := wsDir, path := wsDir / _root_.Lake.defaultLakeDir / "config", tree := true }

open _root_.Lake in
/-- Lake's directory of a package's compiled configuration is an entry of `configPlace`, for every
package index. -/
theorem configDir_eq (config : _root_.Lake.LoadConfig) :
    config.configDir = (configPlace config.wsDir).path / toString config.pkgIdx := rfl

/-- The places below which Lake removes or replaces entries in a build of `pkg`, each read from the
package's directory. At any depth: its build directory and the directories that Lake joins to it
for its Lean libraries, IR, executables and native libraries (`Lake.Package.buildDir`,
`leanLibDir`, `irDir`, `binDir`, `staticLibDir`, `sharedLibDir`), where a build removes each stale
artifact, its `.hash` file and the no-build trace beside its trace (`Lake.buildAction`,
`Lake.clearFileHash`, `Lake.Module.clearOutputArtifacts`, `Lake/Build/Common.lean:313-326`) and
unpacks a downloaded archive (`Lake.Package.fetchBuildArchive`). At the path alone: the build
archive and the Reservoir barrel, each with its trace and no-build trace, which a download removes
and writes (`Lake.Package.buildArchiveFile`, `barrelFile`, `Lake.download`). -/
def buildPlaces (pkg : _root_.Lake.Package) : List Regula.Removal.LakePlace :=
  let below (tree : Bool) (path : FilePath) : Regula.Removal.LakePlace :=
    { base := pkg.dir, path, tree }
  [pkg.buildDir, pkg.leanLibDir, pkg.irDir, pkg.binDir, pkg.staticLibDir,
      pkg.sharedLibDir].map (below true) ++
    ([pkg.buildArchiveFile, pkg.barrelFile].flatMap fun archive =>
      let trace := archive.addExtension "trace"
      [archive, trace, trace.addExtension "nobuild"]).map (below false)

open _root_.Lake in
/-- The clones below which Lake's materialization of the dependencies that `manifest` locks removes
or replaces entries. Lake merges the entries of `manifest`, of the workspace's package overrides
file and of `overrides`, a later entry of a name replacing an earlier one, and it fails for a
dependency of any package that none of them names (`Lake.Workspace.materializeDeps`), so these are
the dependencies of every depth. It keeps the clone of a Git entry at
`<workspace>/<packages>/<Lake.PackageEntry.dirName>`, with the manifest's packages directory or
the workspace's. When a directory is there whose `HEAD` is not the entry's revision, Lake updates
it with Git and removes it when its remote is not the entry's URL (`Lake.updateGitRepo`); it leaves
a clone at that revision as it is, and clones into an absent path (`Lake.PackageEntry.materialize`,
`Lake/Load/Materialize.lean:251-261`). So the places are the clones that Lake would update, read as
Lake reads them (`Lake.GitRepo.dirExists`, `Lake.GitRepo.getHeadRevision?`). Git does not follow a
symbolic link inside a work tree, and `IO.FS.removeDirAll` removes such a link and not its target,
so only the path of each clone is checked. -/
private def clonePlaces (ws : _root_.Lake.Workspace) (manifest : _root_.Lake.Manifest)
    (overrides : Array _root_.Lake.PackageEntry) : IO (List Regula.Removal.LakePlace) := do
  let packages := manifest.packagesDir?.getD ws.relPkgsDir
  let fromFile ← _root_.Lake.Manifest.tryLoadEntries ws.packageOverridesFile
  let mut entries : Std.HashMap Name _root_.Lake.PackageEntry := {}
  for entry in manifest.packages ++ fromFile ++ overrides do
    entries := entries.insert entry.name entry
  let mut places := []
  for (_, entry) in entries do
    let .git (rev := rev) .. := entry.src | continue
    let repo := _root_.Lake.GitRepo.mk (ws.dir / (packages / entry.dirName))
    if (← repo.dirExists) && (← repo.getHeadRevision?) != some rev then
      places := { base := ws.dir, path := repo.dir, tree := false } :: places
  return places

open _root_.Lake in
/-- The places below which Lake's update of a workspace without a manifest removes or replaces
entries (`Lake.Workspace.updateAndMaterialize`). At any depth: the packages directory, where Lake
clones each Git dependency at its name (`Lake.Dependency.dirName`) and updates or removes a clone
that is there (`Lake.materializeGitRepo`, `Lake/Load/Materialize.lean:83-91`). At the path alone:
the clone of each Git dependency that the root package declares, so that a name of the root's
places it below the workspace, and the manifest and the toolchain file that the update writes
(`Lake.Workspace.writeManifest`, `Lake.Workspace.updateToolchain`). Lake learns the name of a
dependency of a dependency, and of a Reservoir package, only during the update, so each of those
is assumed to name a place below the packages directory (`Regula.Removal.libraryRemovals`). -/
private def updatePlaces (ws : _root_.Lake.Workspace) : List Regula.Removal.LakePlace :=
  let clones := ws.root.depConfigs.toList.filterMap fun dep =>
    match dep.src? with
    | some (.git ..) =>
      some { base := ws.dir, path := ws.dir / (ws.relPkgsDir / dep.dirName), tree := false }
    | _ => none
  [{ base := ws.dir, path := ws.pkgsDir, tree := true },
    { base := ws.dir, path := ws.manifestFile, tree := false },
    { base := ws.dir, path := ws.root.dir / _root_.Lake.toolchainFileName, tree := false }] ++
    clones

/-- Stop with a load failure unless Lake may run at `places`
(`Regula.Filesystem.requireLakePlaces`). -/
private def requirePlaces (places : List Regula.Removal.LakePlace) : IO Unit :=
  try Regula.Filesystem.requireLakePlaces places
  catch error => throw <| IO.userError s!"lake-workspace-load-failed: {error}"

/-- Load the root package of the workspace that `config` describes (`Lake.loadWorkspaceRoot`),
with the messages of its log, once Lake may run at the place of the packages' compiled
configurations (`configPlace`). -/
private def loadRoot (config : _root_.Lake.LoadConfig) :
    IO (Option _root_.Lake.Workspace × _root_.Lake.Log) := do
  requirePlaces [configPlace config.wsDir]
  let load : _root_.Lake.LoggerIO _root_.Lake.Workspace := _root_.Lake.loadWorkspaceRoot config
  load.captureLog

/-- Load the workspace rooted at `repo` with Lake's loader and pass it to
`action`. The action runs in the same process, so it must not retain mutable
workspace state beyond its return value. With `scrubSearchPath`, the inherited
`LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for `scrubbedLeanPathEnv`. Setup may disable
`resolveDependencies` to load only the root configuration without materializing dependencies.

The root package is loaded once Lake may run at the place of the compiled configurations
(`loadRoot`). With `resolveDependencies`, the dependencies are resolved as `Lake.loadWorkspace`
resolves them: from the manifest when there is one (`Lake.Workspace.materializeDeps`), once Lake
may run at each clone that it would update (`clonePlaces`), and otherwise by Lake's update
(`Lake.Workspace.updateAndMaterialize`), once Lake may run at the packages directory and the files
that the update writes (`updatePlaces`). Before `action`, which can build, Lake must be able to run
at the build places of every package of the workspace (`buildPlaces`). -/
def withRootWorkspace {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α)
    (scrubSearchPath := false) (resolveDependencies := true) : IO α := do
  let config ← loadConfig repo scrubSearchPath
  let (ws?, log) ← loadRoot config
  withLoaded ws? log fun ws => do
    let resolved ← if !resolveDependencies then pure ws else do
      let refuse {β : Type} (error : IO.Error) : IO β :=
        throw <| IO.userError s!"lake-workspace-load-failed: {error}"
      let manifest ← try _root_.Lake.Manifest.load? ws.manifestFile catch error => refuse error
      let resolve ← match manifest with
        | some manifest => do
            requirePlaces (← clonePlaces ws manifest config.packageOverrides)
            pure (ws.materializeDeps manifest config.leanOpts config.reconfigure
              config.packageOverrides)
        | none => do
            requirePlaces (updatePlaces ws)
            pure (ws.updateAndMaterialize {} config.leanOpts config.updateToolchain)
      let (ws?, log) ← resolve.captureLog
      withLoaded ws? log pure
    requirePlaces (resolved.packages.toList.flatMap buildPlaces)
    action resolved

/-- Load only the root package of the workspace at `repo` (`loadRoot`) and pass it to `action`,
after refusing a root package that declares a dependency, and once Lake may run at the root
package's build places (`buildPlaces`). For a root that declares none, `Lake.loadWorkspace` loads
no other package, so `action` gets the packages that `withRootWorkspace` gives it. The compiled
code of this function calls no loader that resolves or materializes a dependency, which removes
directories (`Regula.Removal.checkProgram`). -/
def withRootPackage {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α) :
    IO α := do
  let (ws?, log) ← loadRoot (← loadConfig repo false)
  withLoaded ws? log fun ws => do
    unless ws.root.depConfigs.isEmpty do
      throw <| IO.userError s!"lake-workspace-load-failed: the root package at {repo} declares \
        a dependency, so its root package alone is not its workspace"
    requirePlaces (ws.packages.toList.flatMap buildPlaces)
    action ws

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

/-- Lake v4.34.1 reaches each read of its artifact cache in a build only when
`Package.isArtifactCacheWritable` or `Package.isArtifactCacheReadable` returns `true`, and each
write only when `Package.isArtifactCacheWritable` does (`fetchCore` in `Lake/Build/Module.lean`,
`Module.packLtar`, and `buildArtifactUnlessUpToDate` in `Lake/Build/Common.lean`). For every
package that a package of `uncachedWorkspace` reaches, `Package.isArtifactCacheReadable` returns
`false` whatever the workspace, the environment or the package's own lakefile say. -/
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
      if restoredTrace text then Regula.Filesystem.removePath .file mod.traceFile
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
