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

/-- Load the workspace rooted at `repo` with Lake's loader and pass it to
`action`. The action runs in the same process, so it must not retain mutable
workspace state beyond its return value. With `scrubSearchPath`, the inherited
`LEAN_PATH` and `LEAN_SRC_PATH` are ignored, as for `scrubbedLeanPathEnv`. Setup may disable
`resolveDependencies` to load only the root configuration without materializing dependencies.

Lake's loader removes and replaces entries of the workspace itself, as `lake build` and
`lake update` would there: the compiled configuration of each package, and the clones of its
dependencies. Those removals act on the workspace that the caller asked Lake to load, and they rest
on its own contents, which its adopter trusts as Lake does (`Regula.Removal.libraryRemovals`). -/
def withRootWorkspace {α : Type} (repo : FilePath) (action : _root_.Lake.Workspace → IO α)
    (scrubSearchPath := false) (resolveDependencies := true) : IO α := do
  let config ← loadConfig repo scrubSearchPath
  let (ws?, log) ← (if resolveDependencies then _root_.Lake.loadWorkspace config
    else _root_.Lake.loadWorkspaceRoot config).captureLog
  withLoaded ws? log action

/-- Load only the root package of the workspace at `repo` (`Lake.loadWorkspaceRoot`) and pass it
to `action`, after refusing a root package that declares a dependency. For a root that declares
none, `Lake.loadWorkspace` loads no other package, so `action` gets the packages that
`withRootWorkspace` gives it. The compiled code of this function calls no loader that resolves or
materializes a dependency, which removes directories (`Regula.Removal.checkProgram`).

Its prerequisite: before the loader runs, it refuses when `.lake` or `.lake/config` below the
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
logs the standard output of other programs it runs in the same form (`logOutput`,
`Lake/Util/Proc.lean`, lines 22 to 27), which this also selects. Standard error, which Lake logs
after `stderr:`, holds no Lean message, so this does not select it.
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

/-- The file name Lake v4.34.1 gives each message of the elaboration of `mod`: the path of its
source file relative to its package's directory (`Module.buildLean` and `compileLeanModule`,
`Lake/Build/Module.lean` lines 981 to 989 and `Lake/Build/Actions.lean` line 74, with the source
file `Module.leanFile`, line 31 of that module).

Assumes: Lake v4.34.1 names each message of a module's elaboration as this does. -/
def messageFileName (mod : _root_.Lake.Module) : String :=
  _root_.Lake.mkRelPathString (_root_.Lake.relPathFrom mod.pkg.dir mod.leanFile)

/-- Each module of the build `store` of `ws`, by the name Lake keys its facets with, whose message
file name (`messageFileName`) holds a line break, so that `unparsedCompilerOutput_ofSerialMessage`
does not cover its messages. A module key names a package and a module; each module of a library of
that package with that name and each executable of it with that root counts, and a key that names
none is reported too, since its file name is unknown. -/
def lineBreakSourcePaths (ws : _root_.Lake.Workspace) (store : _root_.Lake.BuildStore) :
    Array String := Id.run do
  let mut found := #[]
  let mut seen : Std.HashSet (Name × Name) := {}
  for key in store.keys do
    let .facet (.packageModule package module) _ := key | continue
    if seen.contains (package, module) then continue
    seen := seen.insert (package, module)
    let candidates := (ws.packages.filter (·.keyName == package)).flatMap fun pkg =>
      pkg.leanLibs.filterMap (·.findModule? module) ++
        (pkg.leanExes.filter (·.root.name == module)).map (·.root)
    if candidates.isEmpty then
      found := found.push s!"{module}: no library or executable of package {package} has it"
    for mod in candidates do
      if '\n' ∈ (messageFileName mod).toList then
        found := found.push s!"{module}: {(messageFileName mod).quote}"
  return found

/-- A trace that records an elaboration is not one that `dropRestoredTraces` removes. -/
theorem restoredTrace_eq_false_of_elaborationTrace {text : String}
    (h : elaborationTrace text = true) : restoredTrace text = false := by
  cases parsed : _root_.Lake.BuildMetadata.parse text <;>
    simp_all [elaborationTrace, restoredTrace]

end Regula.Checker.Workspace
