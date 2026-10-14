import Lake
import Lake.Load
import Regula.Checker.Common
import Regula.ToolchainProgram
import Regula.Filesystem
import Regula.GitIsolation

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

/-- The configuration file that Lake v4.34.1's rule gives the package at `dir` whose configuration
is named `relConfigFile`, with each candidate observed strictly: `relConfigFile` with the extension
`lean` when it is present, else with the extension `toml` when it is present, else none. Lake's
`resolveConfigFile` takes the same order for a name without an extension
(`Lake/Load/Package.lean:107-119`). Both candidates are observed through
`Regula.Filesystem.realPathIfPresent`, so a failure of either observation other than a missing
file is thrown with its error. Lake instead resolves each candidate with `Lake.resolvePath`
(`Lake/Util/IO.lean:75-89`), which gives no path for every failure of `realPath`, so a
`lakefile.lean` that cannot be resolved, such as a link into a directory without search
permission, is passed over for a `lakefile.toml` beside it. -/
def configChoice (dir relConfigFile : FilePath) : IO (Option FilePath) := do
  let lean := relConfigFile.withExtension "lean"
  let toml := relConfigFile.withExtension "toml"
  let leanPath ← Regula.Filesystem.realPathIfPresent (dir / lean)
  let tomlPath ← Regula.Filesystem.realPathIfPresent (dir / toml)
  return if leanPath.isSome then some lean else tomlPath.map fun _ => toml

/-- Refuse unless each candidate of `configChoice` is absent or resolves: a failure of either
observation other than a missing file is thrown with its error. Where the configuration is named
with its extension, Lake reads that file alone and fails when it cannot resolve it; the other
candidate is observed too, and its failure refuses. -/
def requireConfigCandidates (dir relConfigFile : FilePath) : IO Unit :=
  discard <| configChoice dir relConfigFile

/-- Refuse a package that Lake loaded from a configuration file other than the one that
`configChoice` gives for its directory, naming the package and the two remedies. Lake takes a
dependency's configuration file from its entry when the entry names the file with its extension
(`MaterializedDep.relConfigFile`, `Lake/Load/Materialize.lean:136-137`, then
`Lake/Load/Package.lean:96-102`). The entry is the workspace's manifest's, unless the workspace's
package overrides, `overrides` (`.lake/package-overrides.json` by default), have one for the
package, which replaces it after the manifest is read (`Lake/Load/Resolve.lean:603-605`); the
loaders set no other override. Lake writes each manifest entry with the file it chose when it last
resolved the package (`Workspace.writeManifest`, `Lake/Load/Resolve.lean:520-528`). A choice that
a failed resolution made, in this load or in an earlier one that recorded it, is therefore refused
here, as is each other choice that an entry records and the rule does not give now. The loaded
package does not record which entry gave its file, so the refusal names both remedies:
`lake update`, which resolves the package again and records the choice in the manifest, and a
correction or removal of the package's entry in `overrides`, which `lake update` leaves in force. -/
def requireConfigChoice (overrides : FilePath) (package : _root_.Lake.Package) : IO Unit := do
  let choice ← configChoice package.dir package.relConfigFile
  unless choice == some package.relConfigFile do
    let rule := match choice with
      | some file => s!"its candidates give {file}"
      | none => "neither candidate is present"
    throw <| IO.userError s!"lake-workspace-load-failed: Lake loaded package \
      '{package.prettyName}' from {package.relConfigFile} in {package.dir}, but {rule}: a choice \
      that Lake's rule does not give now, such as one recorded while a candidate could not be \
      resolved. When the manifest records it, run `lake update` to resolve the package's \
      configuration again; when the package's entry in {overrides} gives it, correct or remove \
      that entry, which `lake update` leaves in force"

/-- The configuration with which the workspace rooted at `repo` is loaded, after the observation
of the root package's configuration candidates (`requireConfigCandidates`). With
`scrubSearchPath`, the inherited `LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for
`scrubbedLeanPathEnv`. -/
private def loadConfig (repo : FilePath) (scrubSearchPath : Bool) : IO _root_.Lake.LoadConfig := do
  let wsDir ← IO.FS.realPath repo
  requireConfigCandidates wsDir _root_.Lake.defaultConfigFile
  let lakeEnv ← detectEnvironment
  let lakeEnv := if scrubSearchPath then { lakeEnv with initLeanPath := [], initLeanSrcPath := [] }
    else lakeEnv
  return { lakeEnv, wsDir }

/-- Pass the workspace that a load gave to `action`, after each package's configuration file is
checked against the strict observation of its candidates (`requireConfigChoice`), or fail with
the messages of its log. -/
private def withLoaded {α : Type} (ws? : Option _root_.Lake.Workspace) (log : _root_.Lake.Log)
    (action : _root_.Lake.Workspace → IO α) : IO α :=
  match ws? with
  | some ws => do
      for package in ws.packages do
        requireConfigChoice ws.packageOverridesFile package
      action ws
  | none =>
      let messages := log.entries.map (·.message)
      throw <| IO.userError <|
        s!"lake-workspace-load-failed: {"; ".intercalate messages.toList}"

/-- Load the workspace rooted at `repo` with Lake's loader and pass it to
`action`. The action runs in the same process, so it must not retain mutable
workspace state beyond its return value. With `scrubSearchPath`, the inherited
`LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for `scrubbedLeanPathEnv`. Setup may disable
`resolveDependencies` to load only the root configuration without materializing dependencies.

Lake's loader removes and replaces entries of the workspace itself, as `lake build` and
`lake update` would there: the compiled configuration of each package, and the clones of its
dependencies. Those removals act on the workspace that the caller asked Lake to load, and they rest
on its own contents, which its adopter trusts as Lake does (`Regula.Removal.libraryRemovals`).

The Git commands that Lake runs here, to materialize a dependency or, in a build that `action`
runs, to look up a prebuilt archive, inherit this process's environment. Before it loads anything,
the function refuses unless that environment is Git-isolated (`Regula.GitIsolation.requireIsolated`),
which `Regula.TaskManager.guard` gives every compiled Regula program. -/
def withRootWorkspace {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α)
    (scrubSearchPath := false) (resolveDependencies := true) : IO α := do
  Regula.GitIsolation.requireIsolated "lake-workspace-load-failed: nothing was loaded"
  let config ← loadConfig repo scrubSearchPath
  let (ws?, log) ← (if resolveDependencies then _root_.Lake.loadWorkspace config
    else _root_.Lake.loadWorkspaceRoot config).captureLog
  withLoaded ws? log action

/-- Load only the root package of the workspace at `repo` (`Lake.loadWorkspaceRoot`) and pass it
to `action`, after refusing a root package that declares a dependency. For a root that declares
none, `Lake.loadWorkspace` loads no other package, so `action` gets the packages that
`withRootWorkspace` gives it. The compiled code of this function calls no loader that resolves or
materializes a dependency, which removes directories (`Regula.Removal.checkProgram`).

Its prerequisites: before the loader runs, it refuses unless this process's environment is
Git-isolated, as `withRootWorkspace` does, and it refuses when `.lake` or `.lake/config` below the
checkout is there and is not a directory at its own place
(`Regula.Filesystem.requireOwnDirectory`). It also refuses when the directory of the root
package's compiled configuration (`Lake.LoadConfig.configDir`, `.lake/config/0`) is not such a
directory, or has an entry that is a symbolic link (`Regula.Filesystem.requireNoLinkedEntries`).
That directory is the one where the loader removes and writes files, the configuration lock among
them (`Lake/Load/Lean/Elab.lean:185-187`). It removes the stale `lakefile.olean` and the trace
(`:244`, `:262`), and opens the lock and the trace for writing (`:207`, `:223`, `:294`).
`Lean.writeModule` writes the new `lakefile.olean` and its siblings (`:256`) through
`<file>.tmp.<pid>`, opened with `std::ofstream` (`src/library/module.cpp:311-314`). An open of an
existing file for writing follows a final link, so with this check each file that the loader
writes there is the checkout's own. -/
def withRootPackage {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α) :
    IO α := do
  Regula.GitIsolation.requireIsolated "lake-workspace-load-failed: nothing was loaded"
  let config ← loadConfig repo false
  let lake := config.wsDir / _root_.Lake.defaultLakeDir
  let refuse {β : Type} (error : IO.Error) : IO β := throw <| IO.userError
    s!"lake-workspace-load-failed: nothing was loaded: {error}"
  for directory in [lake, lake / "config"] do
    try Regula.Filesystem.requireOwnDirectory directory catch error => refuse error
  try Regula.Filesystem.requireNoLinkedEntries config.configDir catch error => refuse error
  let load : _root_.Lake.LoggerIO _root_.Lake.Workspace := _root_.Lake.loadWorkspaceRoot config
  let (ws?, log) ← load.captureLog
  withLoaded ws? log fun ws => do
    unless ws.root.depConfigs.isEmpty do
      throw <| IO.userError s!"lake-workspace-load-failed: the root package at {repo} declares \
        a dependency, so its root package alone is not its workspace"
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
cannot.

When it finds such a trace, it resolves the root package's build directory once
(`Regula.Filesystem.ownRoot`), and removes each such trace at the path that Lake gives
(`Lake.Module.traceFile`) with that real path in place of the build directory. So a `.lake` that
the adopter made a symbolic link does not make the removal refuse. -/
def dropRestoredTraces (ws : _root_.Lake.Workspace) : IO Unit := do
  let mut modules : Array _root_.Lake.Module := #[]
  for lib in ws.root.leanLibs do
    if let .ok found ← lib.getModuleArray.toBaseIO then modules := modules ++ found
  modules := modules ++ ws.root.leanExes.map (·.root)
  let restored ← modules.filterM fun mod => do
    match ← (IO.FS.readFile mod.traceFile).toBaseIO with
    | .ok text => pure (restoredTrace text)
    | .error _ => pure false
  if restored.isEmpty then return
  let build ← Regula.Filesystem.ownRoot ws.root.buildDir
  for mod in restored do
    Regula.Filesystem.removeOwn .file
      (mod.filePath (build / ws.root.config.leanLibDir.normalize) "trace")

/-- Whether `text`, the content of a module's Lake trace file, records an elaboration: Lake can
read it as a trace, and it does not record a restore from the artifact cache. Lake v4.34.1 writes
such a trace with the log of the elaboration that produced the module's artifacts, and replays
that log while the trace's input hash matches. -/
def elaborationTrace (text : String) : Bool :=
  match _root_.Lake.BuildMetadata.parse text with
  | .ok data => !data.synthetic
  | .error _ => false

/-- The caption and value of one input of a Lake trace file as Lake v4.34.1 writes it, a
two-element array of the caption and either a hash or the array of that input's own inputs
(`serializeInputs`, `Lake/Build/Common.lean` lines 129 to 136), or none for other JSON. -/
def pairOf? : Json → Option (String × Json)
  | .arr items =>
    if h : items.size = 2 then
      match items[0] with
      | .str caption => some (caption, items[1])
      | _ => none
    else none
  | _ => none

/-- `pairOf?` reads exactly a two-element array whose first element is a string. -/
theorem pairOf?_eq_some_iff {item : Json} {caption : String} {value : Json} :
    pairOf? item = some (caption, value) ↔ item = .arr #[.str caption, value] := by
  constructor
  · intro h
    unfold pairOf? at h
    split at h
    · rename_i items
      split at h
      · rename_i hSize
        split at h
        · rename_i c hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          congr 1
          apply Array.ext
          · simp [hSize]
          · intro i h1 h2
            simp only [List.size_toArray, List.length_cons, List.length_nil] at h2
            match i, h2 with
            | 0, _ => simpa using hc
            | 1, _ => rfl
        · simp at h
      · simp at h
    · simp at h
  · rintro rfl
    simp [pairOf?]

/-- The value that `pairOf?` reads is smaller than the input it reads it from. -/
theorem sizeOf_lt_of_pairOf? {item : Json} {caption : String} {value : Json}
    (h : pairOf? item = some (caption, value)) : sizeOf value < sizeOf item := by
  rw [pairOf?_eq_some_iff.mp h]
  simp
  omega

/-- Whether the trace inputs `json`, an array of inputs as `pairOf?` reads them, hold an input
whose caption `admits` accepts, at any depth. -/
def valueRecords (admits : String → Bool) : Json → Bool
  | .arr items => items.attach.any fun ⟨item, member⟩ =>
      match hPair : pairOf? item with
      | some (other, value) =>
        have : sizeOf value < 1 + sizeOf items := by
          have := Array.sizeOf_lt_of_mem member
          have := sizeOf_lt_of_pairOf? hPair
          omega
        admits other || valueRecords admits value
      | none => false
  | _ => false
termination_by json => sizeOf json

/-- Trace inputs `json` record an input whose caption `admits` accepts: one of its two-element
arrays starts with such a caption, or starts with another and its value records one. -/
inductive Records (admits : String → Bool) : Json → Prop where
  /-- An input of the array has an admitted caption. -/
  | here {items : Array Json} {caption : String} {value : Json} :
      Json.arr #[.str caption, value] ∈ items → admits caption = true → Records admits (.arr items)
  /-- The inputs of an input of the array record it. -/
  | deeper {items : Array Json} {other : String} {value : Json} :
      Json.arr #[.str other, value] ∈ items → Records admits value → Records admits (.arr items)

/-- `valueRecords` decides `Records`. -/
theorem valueRecords_iff (admits : String → Bool) : ∀ json : Json,
    valueRecords admits json = true ↔ Records admits json
  | .arr items => by
    rw [valueRecords.eq_1, Array.any_eq_true']
    constructor
    · rintro ⟨⟨item, member⟩, -, h⟩
      dsimp only at h
      split at h
      · rename_i other value hPair
        have hItem := pairOf?_eq_some_iff.mp hPair
        subst hItem
        rcases Bool.or_eq_true_iff.mp h with hEq | hDeep
        · exact .here member hEq
        · have : sizeOf value < 1 + sizeOf items := by
            have := Array.sizeOf_lt_of_mem member
            simp at this
            omega
          exact .deeper member ((valueRecords_iff admits value).mp hDeep)
      · simp at h
    · intro h
      cases h with
      | here member admitted =>
        refine ⟨⟨_, member⟩, Array.mem_attach _ _, ?_⟩
        dsimp only
        split
        · rename_i other value hPair
          rw [pairOf?_eq_some_iff] at hPair
          simp at hPair
          simp [← hPair.1, admitted]
        · rename_i hNone
          simp [pairOf?] at hNone
      | deeper member records =>
        rename_i other value
        have : sizeOf value < 1 + sizeOf items := by
          have := Array.sizeOf_lt_of_mem member
          simp at this
          omega
        refine ⟨⟨_, member⟩, Array.mem_attach _ _, ?_⟩
        dsimp only
        split
        · rename_i other' value' hPair
          rw [pairOf?_eq_some_iff] at hPair
          simp at hPair
          obtain ⟨rfl, rfl⟩ := hPair
          simp [(valueRecords_iff admits value).mpr records]
        · rename_i hNone
          simp [pairOf?] at hNone
  | .null | .bool _ | .num _ | .str _ | .obj _ => by
    simp only [valueRecords, Bool.false_eq_true, false_iff]
    intro h; cases h
termination_by json => sizeOf json

/-- Whether `text`, the content of a module's Lake trace file, records among the inputs of the
elaboration it holds one whose caption `admits` accepts. Lake v4.34.1 writes, with an elaboration's
log, the caption of each input of its trace at any depth (`BuildMetadata.ofBuildCore`,
`serializeInputs`, `Lake/Build/Common.lean` lines 129 to 145).

Assumes: Lake v4.34.1 writes a module's trace file in this form, with the inputs of the elaboration
whose log it holds. -/
def traceRecords (admits : String → Bool) (text : String) : Bool :=
  match _root_.Lake.BuildMetadata.parse text with
  | .ok data => valueRecords admits (toJson data.inputs)
  | .error _ => false

/-- A trace file records an admitted caption exactly when Lake reads it as a trace whose inputs
record one. -/
theorem traceRecords_iff (admits : String → Bool) (text : String) :
    traceRecords admits text = true ↔
      ∃ data, _root_.Lake.BuildMetadata.parse text = .ok data ∧
        Records admits (toJson data.inputs) := by
  unfold traceRecords
  split
  · rename_i data hData
    rw [valueRecords_iff]
    exact ⟨fun h => ⟨data, hData, h⟩, fun ⟨_, hOk, h⟩ => by cases hData.symm.trans hOk; exact h⟩
  · rename_i error hError
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, hOk, -⟩
    cases hError.symm.trans hOk

/-- The characters `stdout:` and a line break, with which Lake v4.34.1 starts the information
entry it logs for a run of output lines of a program that are not a message of it
(`unparsedCompilerOutput`). -/
def stdoutPrefix : List Char := ['s', 't', 'd', 'o', 'u', 't', ':', '\n']

/-- Whether `entry` is one that Lake can have made from output of the Lean compiler that is not a
Lean message. Lake v4.34.1's `compileLeanModule` runs `lean --json`, which prints each message as
one JSON line on its standard output, and logs each line that parses as a Lean message through
`LogEntry.ofSerialMessage`. It logs each run of other standard output lines as one information
entry, `stdout:`, a line break and the text (`Lake/Build/Actions.lean`, lines 66 to 81), so a
message whose JSON line other output corrupted is in such an entry, whatever its severity. Lake
writes the standard output of other programs it runs in the same form (`logOutput`,
`Lake/Util/Proc.lean`, lines 22 to 27), at the level its caller chooses, and this selects such an
entry only at information level: `proc (quiet := true)` logs a successful program's output at trace
level (line 44), which neither this nor a warning failure level catches. Standard error, which Lake
logs after `stderr:`, holds no Lean message, so this does not select it.
An entry Lake made from a Lean message whose file name has no line break is never selected
(`unparsedCompilerOutput_ofSerialMessage`), and `lineBreakSourcePaths` refuses the modules whose
message file name has one.

Assumes: Lake v4.34.1 logs the standard output of `lean --json` that is not a Lean message only as
such an entry. -/
def unparsedCompilerOutput (entry : _root_.Lake.LogEntry) : Bool :=
  entry.level == .info && stdoutPrefix.isPrefixOf entry.message.toList

/-- A list that starts with a file name with no line break, then `:` and a character other than a
line break, does not start with `stdoutPrefix`. -/
theorem not_stdoutPrefix_prefix {name : List Char} {next : Char} (hName : '\n' ∉ name)
    (hNext : next ≠ '\n') (rest : List Char) :
    ¬ stdoutPrefix <+: name ++ ':' :: next :: rest := by
  rcases name with
    _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, _ | ⟨c7, t⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all [stdoutPrefix, List.cons_prefix_cons] <;>
    exact fun _ _ _ _ _ _ h => hNext h.symm

/-- The decimal rendering of a natural number starts with a character other than a line break. -/
theorem toString_nat_head (n : Nat) :
    ∃ first rest, (toString n).toList = first :: rest ∧ first ≠ '\n' := by
  cases h : (toString n).toList with
  | nil => simp [toString, Nat.repr] at h
  | cons first rest =>
    refine ⟨first, rest, rfl, fun hFirst => ?_⟩
    have digit : first ∈ Nat.toDigits 10 n := by
      have : first ∈ (toString n).toList := by rw [h]; exact List.mem_cons_self
      simpa [toString, Nat.repr] using this
    have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) digit
    simp [hFirst] at this

/-- Lake's entry for a Lean message (`LogEntry.ofSerialMessage`, whose text is the file name, `:`,
the line number and the rest, `mkErrorStringWithPos`) is never one that `unparsedCompilerOutput`
selects when the message's file name has no line break. -/
theorem unparsedCompilerOutput_ofSerialMessage (message : SerialMessage)
    (h : '\n' ∉ message.fileName.toList) :
    unparsedCompilerOutput (_root_.Lake.LogEntry.ofSerialMessage message) = false := by
  obtain ⟨first, rest, hLine, hFirst⟩ := toString_nat_head message.pos.line
  obtain ⟨tail, hText⟩ : ∃ tail, (_root_.Lake.LogEntry.ofSerialMessage message).message.toList =
      message.fileName.toList ++ ':' :: first :: tail := by
    simp only [_root_.Lake.LogEntry.ofSerialMessage, mkErrorStringWithPos, String.toList_append]
    rw [show toString message.fileName = message.fileName from rfl,
      show (toString ":").toList = [':'] from rfl, hLine]
    exact ⟨_, by simp only [List.append_assoc, List.cons_append, List.nil_append]; rfl⟩
  simp only [unparsedCompilerOutput, Bool.and_eq_false_iff, hText]
  right
  cases hPrefix : stdoutPrefix.isPrefixOf (message.fileName.toList ++ ':' :: first :: tail)
  · rfl
  · exact absurd (List.isPrefixOf_iff_prefix.mp hPrefix) (not_stdoutPrefix_prefix h hFirst tail)

/-- The file name Lake v4.34.1 gives each message of the elaboration of a module of `pkg` from
`srcFile`, the source file of its `presetup` facet's result: `Module.buildLean` passes `lean` that
file and its path relative to the package's directory (`Lake/Build/Module.lean` lines 981 to 989),
and `compileLeanModule` names each parsed message by `mkRelPathString` of that relative path
(`Lake/Build/Actions.lean` line 72).

Assumes: Lake v4.34.1 names each message of a module's elaboration as this does, and its `leanArts`
facet compiles from its `presetup` facet's result. -/
def messageFileName (pkg : _root_.Lake.Package) (srcFile : System.FilePath) : String :=
  _root_.Lake.mkRelPathString (_root_.Lake.relPathFrom pkg.dir srcFile)

/-- Why the messages of the module that the build key `key` compiles, if any, are not covered by
`unparsedCompilerOutput_ofSerialMessage`, or none when they are or `key` compiles nothing, with
`source?` giving the source file of each module's completed `presetup` result. A key compiles a
module when it is the module's `leanArts` job. Its messages are covered when a package of `ws` has
the key's package name and the file name Lake gives them (`messageFileName`, from that source
file) has no line break. -/
def sourcePathFailure? (ws : _root_.Lake.Workspace)
    (source? : Name → Name → Option System.FilePath)
    (key : _root_.Lake.BuildKey) : Option String :=
  match key with
  | .facet (.packageModule package module) facet =>
    if facet != _root_.Lake.Module.leanArtsFacet then none else
    match ws.packages.find? (·.keyName == package), source? package module with
    | none, _ => some s!"no package of the workspace is {package}, which has module {module}, so \
        the file name Lake gives its messages is unknown"
    | _, none => some s!"the build holds no completed presetup of module {module}, so the file \
        name Lake gives its messages is unknown"
    | some pkg, some srcFile =>
      if '\n' ∈ (messageFileName pkg srcFile).toList then
        some s!"the file name Lake gives each message of module {module}, \
          {(messageFileName pkg srcFile).quote}, has a line break"
      else none
  | _ => none

/-- A key that compiles a module and has no `sourcePathFailure?` names a package of `ws` and a
source file, given by `source?`, from which Lake names the module's messages with no line break,
the hypothesis of `unparsedCompilerOutput_ofSerialMessage`. -/
theorem sourcePathFailure?_eq_none {ws : _root_.Lake.Workspace}
    {source? : Name → Name → Option System.FilePath} {package module : Name}
    (h : sourcePathFailure? ws source?
      (.facet (.packageModule package module) _root_.Lake.Module.leanArtsFacet) = none) :
    ∃ pkg srcFile, ws.packages.find? (·.keyName == package) = some pkg ∧
      source? package module = some srcFile ∧
      '\n' ∉ (messageFileName pkg srcFile).toList := by
  simp only [sourcePathFailure?, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
  split at h
  · simp at h
  · simp at h
  · rename_i pkg srcFile hPkg hSrc
    refine ⟨pkg, srcFile, hPkg, hSrc, fun hBreak => ?_⟩
    simp [hBreak] at h

/-- Each `sourcePathFailure?` of the keys of the build `store` of `ws`, with `source?` giving the
source file of each module's completed `presetup` result. -/
def lineBreakSourcePaths (ws : _root_.Lake.Workspace) (store : _root_.Lake.BuildStore)
    (source? : Name → Name → Option System.FilePath) : Array String :=
  store.keys.toArray.filterMap (sourcePathFailure? ws source?)

/-- `lineBreakSourcePaths` is empty exactly when no key of the store has a `sourcePathFailure?`. -/
theorem lineBreakSourcePaths_eq_empty_iff (ws : _root_.Lake.Workspace)
    (store : _root_.Lake.BuildStore) (source? : Name → Name → Option System.FilePath) :
    lineBreakSourcePaths ws store source? = #[] ↔
      ∀ key ∈ store.keys, sourcePathFailure? ws source? key = none := by
  simp [lineBreakSourcePaths]

/-- A trace that records an elaboration is not one that `dropRestoredTraces` removes. -/
theorem restoredTrace_eq_false_of_elaborationTrace {text : String}
    (h : elaborationTrace text = true) : restoredTrace text = false := by
  cases parsed : _root_.Lake.BuildMetadata.parse text <;>
    simp_all [elaborationTrace, restoredTrace]

end Regula.Checker.Workspace
