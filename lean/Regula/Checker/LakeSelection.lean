import Regula.Checker.Workspace

/-! # Lake's selection of a workspace's packages and their files

What Lake v4.34.1 selects when it loads a workspace, shared by the checks that must follow it. Lake's
loaded workspace records each package's directory, configuration file and manifest file, but not
the entries it materialized the packages from (`withRootSelection`). So one read of the
workspace's manifest and package overrides file gives the entries (`RootSelection`), and Lake's
one load corroborates each field that it records (`agrees`). From these follow the entry that each
dependency is materialized from (`lastEntry`, `effectiveEntry`), the packages directory
(`packagesDir`, `checkoutDir`, `entryDir`), the packages taken from a path entry
(`pathPackages`), and the files that decide a package's configuration and pins
(`configCandidates`, `ownRootFiles`, `rootEntries`, `lakeInputs`). The files are read by Lake's
own readers (`Lake.Manifest.load?`, `Lake.Manifest.tryLoadEntries`). Where Lake has no function
for a rule, the definition here is a copy of the rule alone, and its docstring cites the Lake lines
in an `Assumes:` entry. The documentation check's pin comparison and input capture
(`Documentation.sharedPinMismatch`, `Documentation.captureVersoPackage`), the dependency inventory
(`Lake.surfaceInventoryOf`), which a copy of the project takes too (`Lake.copyProject`), and the
copy's packages directory and the checkouts it prunes (`Lake.relocateDependencies`,
`Lake.copyProject`) use it. -/

namespace Regula.Checker.LakeSelection
open Lean System

/-- The last of `entries` that `selects` holds for. For `selects` the test of a package's name, it
is the entry that Lake materializes that package from (`effectiveEntry`), and `lastEntry_eq_some`
states which entry it is.

Assumes:
- Lake v4.34.1 inserts the entries of a workspace's manifest and then those of its package
  overrides file into a name map, in that order, and materializes each dependency from the entry
  that the map holds for its name (`Lake/Load/Resolve.lean:599-613`). An insertion replaces the
  entry that the map holds for the name. -/
def lastEntry (entries : Array _root_.Lake.PackageEntry)
    (selects : _root_.Lake.PackageEntry → Bool) : Option _root_.Lake.PackageEntry :=
  entries.findRev? selects

/-- `lastEntry` gives `e` exactly when `selects` holds for `e` and for no entry after it. -/
theorem lastEntry_eq_some {entries : Array _root_.Lake.PackageEntry}
    {selects : _root_.Lake.PackageEntry → Bool} {e : _root_.Lake.PackageEntry} :
    lastEntry entries selects = some e ↔
      selects e = true ∧
        ∃ pre post, entries.toList = pre ++ e :: post ∧ ∀ x ∈ post, selects x = false := by
  rw [lastEntry, Array.findRev?_eq_find?_reverse, ← Array.find?_toList, Array.toList_reverse,
    List.find?_eq_some_iff_append]
  simp only [Bool.not_eq_true']
  constructor
  · rintro ⟨h, as, bs, hx, has⟩
    rw [List.reverse_eq_append_iff] at hx
    exact ⟨h, bs.reverse, as.reverse, by simpa using hx,
      fun x hx => has x (List.mem_reverse.mp hx)⟩
  · rintro ⟨h, pre, post, hx, hpost⟩
    refine ⟨h, post.reverse, pre.reverse, ?_, fun x hx => hpost x (List.mem_reverse.mp hx)⟩
    rw [hx]; simp

/-- The entry that Lake materializes the package named `name` from, among `entries`, the entries of
a workspace root (`rootEntries`): the last entry with that name (`lastEntry`).

Assumes:
- The package that Lake loads for a dependency has the name of its entry
  (`Lake/Load/Resolve.lean:40`, `Lake/Load/Toml.lean:491`, `Lake/DSL/Package.lean:29-32`). -/
def effectiveEntry (entries : Array _root_.Lake.PackageEntry) (name : Name) :
    Option _root_.Lake.PackageEntry :=
  lastEntry entries (·.name == name)

/-- `effectiveEntry` gives the entry `e` for `name` exactly when `e` has that name and no entry
after it has. -/
theorem effectiveEntry_eq_some {entries : Array _root_.Lake.PackageEntry} {name : Name}
    {e : _root_.Lake.PackageEntry} :
    effectiveEntry entries name = some e ↔
      e.name = name ∧
        ∃ pre post, entries.toList = pre ++ e :: post ∧ ∀ x ∈ post, x.name ≠ name := by
  simp [effectiveEntry, lastEntry_eq_some]

/-- The Git source and revision that `entry` pins, or `none` for a path entry. -/
def gitPin (entry : _root_.Lake.PackageEntry) : Option (String × String) :=
  match entry.src with
  | .git url rev _ _ => some (url, rev)
  | .path _ => none

/-- The first entry among `verso`, by its name, whose package two workspaces both pin by Git at a
different source or revision: the workspace whose root entries are `verso` and the one whose root
entries are `own`, each by the entry that Lake materializes the package from (`effectiveEntry`). -/
def pinMismatch (verso own : Array _root_.Lake.PackageEntry) : Option Name :=
  (verso.find? fun entry =>
    match (effectiveEntry verso entry.name).bind gitPin,
        (effectiveEntry own entry.name).bind gitPin with
    | some pin, some pin' => pin != pin'
    | _, _ => false).map (·.name)

/-- `pinMismatch` finds nothing exactly when the two workspaces pin each package that both pin by
Git at the same source and revision. -/
theorem pinMismatch_eq_none {verso own : Array _root_.Lake.PackageEntry} :
    pinMismatch verso own = none ↔
      ∀ name pin pin', (effectiveEntry verso name).bind gitPin = some pin →
        (effectiveEntry own name).bind gitPin = some pin' → pin = pin' := by
  rw [pinMismatch, Option.map_eq_none_iff, Array.find?_eq_none]
  constructor
  · intro h name pin pin' hv ho
    obtain ⟨e, he, hpin⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨hname, pre, post, hx, -⟩ := effectiveEntry_eq_some.mp he
    have hmem : e ∈ verso := by
      rw [← Array.mem_toList_iff, hx]; simp
    have := h e hmem
    rw [hname, hv, ho] at this
    simpa using this
  · intro h e _
    split
    · next pin pin' hv ho => simpa using h e.name pin pin' hv ho
    · simp

/-- The configuration files, relative to a package's directory, whose presence decides the one
that Lake loads the package from, given the name `configFile` that Lake resolves: for a name with an
extension, that file, and for one without, its Lean file and its TOML file.

Assumes:
- Lake v4.34.1 loads a package from its configuration name in its directory when that name has an
  extension. For a name without one it loads `<name>.lean` when that exists and `<name>.toml`
  otherwise (`Lake/Load/Package.lean:93-118`). A dependency's name is the `configFile` of the entry
  it is materialized from (`Lake/Load/Materialize.lean:136-137`, `Lake/Load/Resolve.lean:43`), and
  a workspace root's is `lakefile` unless its load configuration names another
  (`Lake/Load/Config.lean:44`, `Lake/Config/Defaults.lean:26`). -/
def configCandidates (configFile : FilePath) : List FilePath :=
  if configFile.extension.isSome then [configFile]
  else [configFile.addExtension "lean", configFile.addExtension "toml"]

/-- The configuration name of the root package of a workspace that Lake loads under a load
configuration that names none, as the `lake` command's and `Workspace.withRootWorkspace`'s do
(`rootConfigFile_lake`). -/
def rootConfigFile : FilePath := _root_.Lake.defaultConfigFile

/-- A load configuration that names no configuration gives its root `rootConfigFile`. -/
theorem rootConfigFile_lake (env : _root_.Lake.Env) (dir : FilePath) :
    ({ lakeEnv := env, wsDir := dir } : _root_.Lake.LoadConfig).relConfigFile = rootConfigFile :=
  rfl

/-- The manifest and package overrides file of the workspace that Lake loads with the package at
`dir` as its root under a load configuration that names no manifest, as the `lake` command's and
`Workspace.withRootWorkspace`'s do (`ownRootFiles_lake`). Their entries decide the Git revisions
that a build of that package checks out (`rootEntries`).

Assumes:
- Lake v4.34.1 gives the root package of a workspace the `relManifestFile` of its load
  configuration (`Lake/Load/Package.lean:35-51`), `lake-manifest.json` unless it names another
  (`Lake/Load/Config.lean:54`), and the directory `wsDir` (`Lake/Load/Config.lean:40-42`). The
  `lake` command names no other manifest (`Lake/CLI/Main.lean:116-130`), nor does
  `Workspace.withRootWorkspace`. -/
def ownRootFiles (dir : FilePath) : FilePath × FilePath :=
  (_root_.Lake.joinRelative dir _root_.Lake.defaultManifestFile,
    _root_.Lake.joinRelative (_root_.Lake.joinRelative dir _root_.Lake.defaultLakeDir)
      "package-overrides.json")

/-- For a workspace whose root has the manifest that a load configuration naming no manifest gives
it, `ownRootFiles` of the root's directory are the workspace's manifest and package overrides
file, as Lake joins paths. -/
theorem ownRootFiles_lake (ws : _root_.Lake.Workspace) (env : _root_.Lake.Env)
    (h : ws.root.relManifestFile =
      ({ lakeEnv := env, wsDir := ws.root.dir } : _root_.Lake.LoadConfig).relManifestFile) :
    ownRootFiles ws.root.dir = (ws.manifestFile, ws.packageOverridesFile) := by
  simp only [ownRootFiles, _root_.Lake.Workspace.manifestFile, _root_.Lake.Package.manifestFile,
    h, _root_.Lake.Workspace.packageOverridesFile, _root_.Lake.Workspace.lakeDir,
    _root_.Lake.Package.lakeDir, _root_.Lake.Package.relLakeDir]
  rfl

/-- The entries, in Lake's order, that a build of the package at a workspace root would materialize
its dependencies from, given its manifest and package overrides file `files` (`ownRootFiles`):
those of the manifest, then those of the overrides file. A root without a manifest gives none:
Lake would resolve its requirements anew, at revisions that no file records, and would read no
overrides file. Each file is read by Lake's own reader, so an entry that Lake refuses is refused
here too.

Assumes:
- Lake v4.34.1 materializes a workspace's dependencies from its manifest and its package overrides
  file when its manifest exists, and otherwise resolves its requirements anew without reading the
  overrides file (`Lake/Load/Workspace.lean:61-69`, `Lake/Load/Resolve.lean:603`,
  `Lake/Load/Resolve.lean:472-519`). -/
def rootEntries (files : FilePath × FilePath) : IO (Array _root_.Lake.PackageEntry) := do
  let some manifest ← _root_.Lake.Manifest.load? files.1 | return #[]
  return manifest.packages ++ (← _root_.Lake.Manifest.tryLoadEntries files.2)

/-- The packages directory, relative to a workspace's directory, that Lake materializes the
workspace's Git entries into: `recorded`, the one its manifest records, or else `relPkgsDir`, the
one its root configuration gives (`Lake.Workspace.relPkgsDir`).

Assumes:
- Lake v4.34.1 materializes each Git entry of a workspace below `manifest.packagesDir?.getD
  ws.relPkgsDir` (`Lake/Load/Resolve.lean:598`), and `ws.relPkgsDir` is the `packagesDir` of the
  root package's configuration (`Lake/Config/Workspace.lean:184-185`,
  `Lake/Config/Package.lean:216-217`). -/
def packagesDir (recorded : Option FilePath) (relPkgsDir : FilePath) : FilePath :=
  recorded.getD relPkgsDir

/-- The directory, relative to the workspace's directory, that Lake materializes `entry` at before
it takes the entry's subdirectory, given the workspace's packages directory `packagesDir`
(`packagesDir`): a path entry's directory, and a Git entry's checkout `packagesDir / dirName`.

Assumes:
- Lake v4.34.1 materializes a path entry at its directory and clones a Git entry at that checkout
  (`Lake/Load/Materialize.lean:241-246`), joined as Lake joins paths
  (`Lake/Util/FilePath.lean:42-48`). -/
def checkoutDir (packagesDir : FilePath) (entry : _root_.Lake.PackageEntry) : FilePath :=
  match entry.src with
  | .path dir => dir
  | .git .. => _root_.Lake.joinRelative packagesDir entry.dirName

/-- The directory, relative to the workspace's directory, that Lake materializes `entry` into,
given the workspace's packages directory `packagesDir` (`packagesDir`): its `checkoutDir`, below a
Git entry's subdirectory when it names one.

Assumes:
- Lake v4.34.1 materializes a Git entry that names a subdirectory below its checkout
  (`Lake/Load/Materialize.lean:264`), joined as Lake joins paths
  (`Lake/Util/FilePath.lean:42-48`), and gives the package that directory as its `relDir`
  (`Lake/Load/Resolve.lean:42`, `Lake/Load/Package.lean:35-51`). -/
def entryDir (packagesDir : FilePath) (entry : _root_.Lake.PackageEntry) : FilePath :=
  match entry.src with
  | .git (subDir? := some subDir) .. =>
    _root_.Lake.joinRelative (checkoutDir packagesDir entry) subDir
  | _ => checkoutDir packagesDir entry

/-- The remote URL that Lake records for a package that it materializes from `entry`: empty for a
path entry, and for a Git entry its URL as `Lake.Git.filterUrl?` gives it, or empty when that
gives none.

Assumes:
- Lake v4.34.1 records these (`Lake/Load/Materialize.lean:243`, `Lake/Load/Materialize.lean:266`,
  `Lake/Load/Resolve.lean:47`, `Lake/Load/Package.lean:35-51`). -/
def entryRemoteUrl (entry : _root_.Lake.PackageEntry) : String :=
  match entry.src with
  | .path _ => ""
  | .git url .. => (_root_.Lake.Git.filterUrl? url).getD ""

/-- What Lake's load of a workspace selected for its dependencies: the entries, in Lake's order,
that it materializes them from (`effectiveEntry`), the packages directory of its Git entries
(`packagesDir`), and whether the load wrote the entries itself (`written`). -/
structure RootSelection where
  /-- The entries of the workspace's manifest, then those of its package overrides file. -/
  entries : Array _root_.Lake.PackageEntry
  /-- The packages directory, relative to the workspace's directory. -/
  packagesDir : FilePath
  /-- Whether the workspace had no manifest before the load, so that Lake resolved its
  requirements anew and wrote `entries` to the manifest from the packages it materialized. -/
  written : Bool := false

/-- Whether the package `pkg` that Lake loaded agrees with `entry` of the selection `selection` on
each field that the load records from the entry it materializes a package from: the name, the
scope, the directory (`entryDir`), the configuration file, which is the entry's own or, for a name
without an extension, one of its candidates (`configCandidates`), and the manifest file,
`lake-manifest.json` when the entry records none. The remote URL (`entryRemoteUrl`) is compared
too, unless the load wrote the entry (`RootSelection.written`). A Git revision and the `inherited`
flag are not recorded by the load.

Assumes:
- Lake v4.34.1 loads a package from the load configuration that it builds from the entry
  (`Lake/Load/Resolve.lean:33-46`, `Lake/Load/Materialize.lean:124-137`), whose configuration name
  it resolves (`Lake/Load/Resolve.lean:70`, `Lake/Load/Package.lean:93-118`), and records these
  fields of that configuration in the package (`Lake/Load/Package.lean:35-51`).
- When Lake v4.34.1 resolves a requirement anew, the remote URL it records comes from the
  requirement, or from Reservoir, while the entry it writes names the URL it cloned from, which
  `LAKE_PKG_URL_MAP` can replace (`Lake/Load/Materialize.lean:183-185`,
  `Lake/Load/Materialize.lean:196-213`, `Lake/Load/Materialize.lean:219-223`). Lake reads a
  package's remote URL only for the repository of its release archive
  (`Lake/Build/Package.lean:128-130`), which selects none of the files that these checks read. -/
def agrees (selection : RootSelection) (pkg : _root_.Lake.Package)
    (entry : _root_.Lake.PackageEntry) : Bool :=
  pkg.baseName == entry.name && pkg.scope == entry.scope &&
    pkg.relDir == entryDir selection.packagesDir entry &&
    (selection.written || pkg.remoteUrl == entryRemoteUrl entry) &&
    (configCandidates entry.configFile).contains pkg.relConfigFile &&
    pkg.relManifestFile == entry.manifestFile?.getD _root_.Lake.defaultManifestFile

/-- A package that agrees with an entry has its directory and its manifest file from the entry, and
its configuration file among the entry's candidates. Unless the load wrote the entry, it also has
the entry's remote URL. -/
theorem agrees_fields {selection : RootSelection} {pkg : _root_.Lake.Package}
    {entry : _root_.Lake.PackageEntry} (h : agrees selection pkg entry = true) :
    pkg.relDir = entryDir selection.packagesDir entry ∧
      pkg.relConfigFile ∈ configCandidates entry.configFile ∧
      pkg.relManifestFile = entry.manifestFile?.getD _root_.Lake.defaultManifestFile ∧
      (selection.written = false → pkg.remoteUrl = entryRemoteUrl entry) := by
  simp only [agrees, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  exact ⟨h.1.1.1.2, h.1.2, h.2, fun written => h.1.1.2.resolve_left (by simp [written])⟩

/-- Refuse unless each package that Lake loaded in the workspace `ws` other than the root has an
entry in `selection` (`effectiveEntry`) and agrees with it on each field that the load records
(`agrees`). -/
def checkSelection (ws : _root_.Lake.Workspace) (selection : RootSelection) : IO Unit := do
  for pkg in ws.packages do
    if pkg.isRoot then continue
    let some entry := effectiveEntry selection.entries pkg.baseName
      | throw <| IO.userError s!"lake-workspace-load-failed: Lake loaded the package \
          {pkg.baseName}, for which {ws.manifestFile} and {ws.packageOverridesFile} have no entry"
    unless agrees selection pkg entry do
      throw <| IO.userError s!"lake-workspace-load-failed: Lake loaded the package \
        {pkg.baseName} from {pkg.relDir} with configuration {pkg.relConfigFile}, manifest \
        {pkg.relManifestFile} and remote URL '{pkg.remoteUrl}', which its entry in \
        {ws.manifestFile} or {ws.packageOverridesFile} does not give"

/-- Load the workspace rooted at `dir` (`Workspace.withRootWorkspace`) and pass it to `action` with
its selection. The selection is one read, before the load, of the workspace's manifest and package
overrides file (`ownRootFiles`) by Lake's own readers. These must be the files that Lake's load
reads (`ownRootFiles_lake`), and each package that Lake loaded other than the root must agree with
the entry that the selection gives it (`checkSelection`); otherwise the load is refused.
So the load corroborates each field that it records, and the read supplies what the load does not
record: the kind of each entry, its Git revision and its configuration name before Lake resolves
it.

When the manifest does not exist before the load, `requireManifest` refuses the workspace, as the
documentation checks do, since its requirements would be resolved at revisions that no file
records. Otherwise Lake's load resolves the requirements anew and writes the entries it
materialized from to the manifest, with the configuration and manifest files it resolved, and
reads no overrides file. The selection is then the entries of that manifest, read after the load,
and marked as written (`RootSelection.written`).

Assumes:
- Lake v4.34.1 materializes the dependencies from the manifest and the overrides file when the
  manifest exists, and otherwise resolves them anew and writes the manifest
  (`Lake/Load/Workspace.lean:61-69`, `Lake/Load/Resolve.lean:587-627`,
  `Lake/Load/Resolve.lean:521-560`). The entries it materialized from are not recorded in the
  loaded workspace: they are a local of `Workspace.materializeDeps`
  (`Lake/Load/Resolve.lean:599-613`), or written to the manifest
  (`Lake/Load/Resolve.lean:524-527`).
- Trusted: no process writes the workspace's manifest or package overrides file during one call.
  Such a write is outside the checker's model of the filesystem, as it is for the checker's other
  reads. A write that changes a field the load records is refused by `agrees`. -/
def withRootSelection {α : Type} (dir : FilePath)
    (action : _root_.Lake.Workspace → RootSelection → IO α) (requireManifest := false) :
    IO α := do
  let files := ownRootFiles (← IO.FS.realPath dir)
  let read ← match ← _root_.Lake.Manifest.load? files.1 with
    | some manifest => pure (some (manifest, ← _root_.Lake.Manifest.tryLoadEntries files.2))
    | none => pure none
  if requireManifest && read.isNone then
    throw <| IO.userError s!"lake-workspace-load-failed: {dir} has no {files.1}; Lake would \
      resolve its requirements anew, at revisions that no file records"
  Workspace.withRootWorkspace dir fun ws => do
    unless (ws.manifestFile, ws.packageOverridesFile) == files do
      throw <| IO.userError s!"lake-workspace-load-failed: Lake's load of {dir} reads \
        {ws.manifestFile} and {ws.packageOverridesFile}, not {files.1} and {files.2}"
    let (manifest, overrides) ← match read with
      | some read => pure read
      | none =>
        let some written ← _root_.Lake.Manifest.load? ws.manifestFile
          | throw <| IO.userError s!"lake-workspace-load-failed: Lake's load of {dir} left no \
              manifest at {ws.manifestFile}"
        pure (written, #[])
    let selection : RootSelection := {
      entries := manifest.packages ++ overrides
      packagesDir := packagesDir manifest.packagesDir? ws.relPkgsDir
      written := read.isNone }
    checkSelection ws selection
    action ws selection

/-- The packages that Lake loaded in the workspace `ws` from a path entry: each package other than
the root whose entry in `selection` (`withRootSelection`, `effectiveEntry`) is a path entry, with
that entry. These are the packages that the root requires by local path, directly or not, after
Lake's traversal of the requirements and its overrides. -/
def pathPackages (ws : _root_.Lake.Workspace) (selection : RootSelection) :
    Array (_root_.Lake.Package × _root_.Lake.PackageEntry) :=
  ws.packages.filterMap fun pkg =>
    if pkg.isRoot then none
    else match effectiveEntry selection.entries pkg.baseName with
      | some entry => match entry.src with
        | .path _ => some (pkg, entry)
        | .git .. => none
      | none => none

/-- The Lake inputs of a package, joined to `anchor`, which stands for the package's directory,
given the configuration name `configFile` that Lake resolves for it and the manifest `manifestFile?`
that its entry records: the configuration files whose presence decides the one Lake loads
(`configCandidates`), that manifest, which Lake reads when it materializes the package, the
manifest and package overrides file of the workspace the package roots (`ownRootFiles`), and its
toolchain file.

Assumes:
- Lake v4.34.1 reads the manifest that a dependency's entry records when it materializes the
  dependency, and none when the entry records none (`Lake/Load/Materialize.lean:272-277`).
- Lake v4.34.1 reads a package's toolchain at `lean-toolchain` in its directory
  (`Lake/Util/Version.lean:230`, `Lake/Util/Version.lean:304-305`). -/
def lakeInputs (configFile : FilePath) (manifestFile? : Option FilePath) (anchor : FilePath) :
    List FilePath :=
  (configCandidates configFile ++ manifestFile?.toList).map (_root_.Lake.joinRelative anchor) ++
    [(ownRootFiles anchor).1, (ownRootFiles anchor).2,
      _root_.Lake.joinRelative anchor _root_.Lake.toolchainFileName]

/-- `lakeInputs` binds each configuration file that decides the one Lake loads, the manifest that
the entry records, and both files of the workspace the package roots. -/
theorem lakeInputs_cover (configFile : FilePath) (manifestFile? : Option FilePath)
    (anchor : FilePath) :
    (∀ c ∈ configCandidates configFile,
        _root_.Lake.joinRelative anchor c ∈ lakeInputs configFile manifestFile? anchor) ∧
      (∀ m ∈ manifestFile?,
        _root_.Lake.joinRelative anchor m ∈ lakeInputs configFile manifestFile? anchor) ∧
      (ownRootFiles anchor).1 ∈ lakeInputs configFile manifestFile? anchor ∧
      (ownRootFiles anchor).2 ∈ lakeInputs configFile manifestFile? anchor := by
  refine ⟨fun c hc => ?_, fun m hm => ?_, by simp [lakeInputs], by simp [lakeInputs]⟩
  · simp only [lakeInputs, List.mem_append, List.mem_map]
    exact Or.inl ⟨c, Or.inl hc, rfl⟩
  · simp only [lakeInputs, List.mem_append, List.mem_map]
    exact Or.inl ⟨m, Or.inr (by simpa using hm), rfl⟩

end Regula.Checker.LakeSelection
