import Regula.Checker.Lake
import Regula.Removal
import Regula.Scratch
import Regula.TaskManagerCheck
import RegulaPolicy.Domain

/-! # The removal check and the task-manager check of every program of the package

Each program of the package runs the check that every removal its compiled code reaches goes
through the filesystem observer (`Regula.Removal.checkProgram`) when its root module, or a module
that imports it, is built, and the module records the program (`Regula.Removal.reached`). Each
compiled program, the root module of an executable, also runs the check that it starts through the
guard of Lean's task manager when its compiled code needs one
(`Regula.TaskManagerCheck.checkProgram`), and the module records it
(`Regula.TaskManagerCheck.checked`). This campaign reads the compiled modules of the root package as
Lake resolves them (`Regula.Checker.Lake.rootSurfaceInventory`) and refuses unless each program is
recorded: by both checks the root module of each executable, and by the removal check each module
of a library that declares `main`, which a script runs with `lean --run`. The `lean` executable
starts its own task manager before it elaborates such a module, so that program needs no guard
(`Regula.TaskManagerCheck`). The `Fixtures` library is not read: it holds the inputs of the
checker's controls, which no script runs and the acceptance build does not build.

A root module outside every library, which no library module can import (`auditApp`'s `Main`), is
checked here: its environment is imported and checked as each `checkProgram` checks it
(`Regula.Removal.rawRemovals`, `Regula.Removal.programRefusal`,
`Regula.TaskManagerCheck.refusal`).

The removal check reads a linked module under `Init`, `Std`, `Lean` or `Lake` as Lean's own by its
name, under the hypothesis that no package of the workspace that builds the program provides one
(`Regula.Removal.toolchainModules`). This campaign checks that hypothesis for three workspaces of
this repository, the root package's, the `markdown/` package's and the `audit/` package's
(`checkToolchainWorkspaces`): it loads each with Lake, and refuses a module under those roots that
a package of it provides, the root package or a dependency, and an entry of those roots in the
library directory of a package. Its control, a workspace whose dependency package provides
`Lean.Planted`, runs first (`toolchainControl`). The Mathlib integration's workspace, which builds
programs of the package too, and an adopter's workspace are not checked: their builds rest on the
hypothesis unchecked.

The campaign acquires no dependency, under the hypothesis of `toolchainFindings` that no other
process changes the manifest, the package overrides or a dependency's checkout between its check
and Lake's load. Before Lake loads a workspace, it refuses one whose manifest pins a Git package
that is not checked out at the pinned commit, since Lake's loader could then clone, fetch or check
it out (`unprovisioned`), and names the provisioning step that acquires it. The
`markdown/` workspace pins MD4Lean, which `lean --run lean/RegulaProvision.lean verso` acquires.
The control of that refusal, a workspace whose manifest pins a Git package that it does not hold,
runs first (`provisionControl`). -/

namespace Regula.Qualification.Observers

open Lean System

/-- The programs of `programs` that `recorded` does not record. -/
def unrecorded (programs : Array Name) (recorded : Name → Bool) : Array Name :=
  programs.filter (!recorded ·)

/-- A program is unrecorded exactly when it is one of `programs` and `recorded` does not record
it. -/
theorem mem_unrecorded_iff (programs : Array Name) (recorded : Name → Bool) (program : Name) :
    program ∈ unrecorded programs recorded ↔
      program ∈ programs ∧ recorded program = false := by
  simp [unrecorded, Array.mem_filter]

/-- The library whose modules are not programs of the package. -/
def fixtures : String := "Fixtures"

/-- The names of the programs that the markers with the prefix `marker` among `names` record:
each name `marker ++ root` records the program whose root module is `root`. -/
def recordedBy (marker : Name) (names : Array Name) : Array Name :=
  names.filterMap fun name =>
    if marker.isPrefixOf name && name != marker then some (name.replacePrefix marker .anonymous)
    else none

/-- The roots of Lean's toolchain (`RegulaPolicy.ToolchainRoot`), as a list. -/
def toolchainRoots : List Name := [`Init, `Std, `Lean, `Lake]

/-- A name is one of `toolchainRoots` exactly when it is a root of Lean's toolchain. -/
theorem mem_toolchainRoots_iff (root : Name) :
    root ∈ toolchainRoots ↔ RegulaPolicy.ToolchainRoot root := by
  simp [toolchainRoots, RegulaPolicy.ToolchainRoot]

/-- The modules under a root of Lean's toolchain (`RegulaPolicy.ToolchainRoot`) that the libraries
and executables `targets` of a package provide, each with its target. -/
def toolchainProvided (targets : Array Regula.Checker.Lake.TargetInventory) :
    Array (String × Name) :=
  targets.flatMap fun target =>
    (target.modules.filter fun module => decide (RegulaPolicy.ToolchainRoot module.getRoot)).map
      (target.target, ·)

/-- A target and a module are found exactly when one of `targets`, with that name, provides the
module, and the module's root is a root of Lean's toolchain. -/
theorem mem_toolchainProvided_iff (targets : Array Regula.Checker.Lake.TargetInventory)
    (target : String) (module : Name) :
    (target, module) ∈ toolchainProvided targets ↔
      ∃ provider ∈ targets, provider.target = target ∧ module ∈ provider.modules ∧
        RegulaPolicy.ToolchainRoot module.getRoot := by
  simp only [toolchainProvided, Array.mem_flatMap, Array.mem_map, Array.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨provider, member, found, ⟨provided, root⟩, rfl, rfl⟩
    exact ⟨provider, member, rfl, provided, root⟩
  · rintro ⟨provider, member, rfl, provided, root⟩
    exact ⟨provider, member, module, ⟨provided, root⟩, rfl, rfl⟩

/-- The entries of a library directory where Lean's search path finds a module under a root of
Lean's toolchain: the directory and the `.olean` file of each root. In each directory of the search
path, `Lean.SearchPath.findWithExt` looks for the module root's directory or `.olean` file, and it
reads every module under that root from the first directory that has one
(`Lean/Util/Path.lean:61-65`). -/
def toolchainEntries : List String :=
  toolchainRoots.flatMap fun root => [root.toString, s!"{root}.olean"]

/-- What breaks, in a package of a workspace, the hypothesis of
`Regula.Removal.toolchainModules`. -/
inductive ToolchainFinding where
  /-- The package provides the module, under a root of Lean's toolchain, by the target. -/
  | provides (package target : String) (module : Name)
  /-- The package's library directory has the entry, one of `toolchainEntries`. -/
  | holds (package entry : String)
  deriving BEq, Repr

/-- The text of a finding. -/
def ToolchainFinding.describe : ToolchainFinding → String
  | .provides package target module =>
    s!"package {package} provides the module {module} ({target})"
  | .holds package entry => s!"package {package} has {entry} in its library directory"

/-- The entries from which Lake's loader materializes the dependencies of a workspace with the
manifest `manifest` and the package overrides `overrides`, by name, as
`Lake.Workspace.materializeDeps` builds them (`Lake/Load/Resolve.lean:599-607`): the manifest's
packages, then the overrides, each inserted by its name, so an override replaces the manifest's
entry of the same name. The load configuration of `Regula.Checker.Workspace.withRootWorkspace`
supplies no further overrides. -/
def loaderEntries (manifest : _root_.Lake.Manifest) (overrides : Array _root_.Lake.PackageEntry) :
    NameMap _root_.Lake.PackageEntry :=
  overrides.foldl (init := manifest.packages.foldl (init := mkNameMap _)
    fun map entry => map.insert entry.name entry)
    fun map entry => map.insert entry.name entry

/-- The Git packages, by the names of their entries, that are not checked out at their pinned
commits in the workspace `ws`, which is loaded with its root package alone
(`Lake.loadWorkspaceRoot`): a superset of those that Lake's loader can acquire when it loads the
workspace. With a manifest, the loader materializes each dependency from its entry of
`loaderEntries`, and a dependency with no entry there is an error, not an acquisition
(`Lake/Load/Resolve.lean:611-622`). `Lake.PackageEntry.materialize` leaves a Git package as it is,
with no fetch, clone or checkout, exactly when its directory below the manifest's packages
directory exists and its `HEAD` is the pinned commit (`Lake/Load/Materialize.lean:237-264`). Each
Git entry of `loaderEntries` whose checkout is not so is listed. The list can also name an entry
that the loader never reaches, such as a stale entry of the manifest, so a refusal by it is
conservative; `lake update` removes such an entry. With no manifest, the loader resolves every
dependency anew (`Lake/Load/Workspace.lean:61-69`), so a root package that declares a dependency
gives the entry `lake-manifest.json`. -/
def unprovisioned (ws : _root_.Lake.Workspace) : IO (Array String) := do
  let some manifest ← _root_.Lake.Manifest.load? ws.manifestFile
    | return if ws.root.depConfigs.isEmpty then #[] else #["lake-manifest.json"]
  let packages := ws.dir / manifest.packagesDir?.getD ws.relPkgsDir
  let overrides ← _root_.Lake.Manifest.tryLoadEntries ws.packageOverridesFile
  let mut missing := #[]
  for (_, entry) in loaderEntries manifest overrides do
    if let .git (rev := rev) .. := entry.src then
      let checkout : _root_.Lake.GitRepo := ⟨packages / entry.dirName⟩
      unless (← checkout.dirExists) && (← checkout.getHeadRevision?) == some rev do
        missing := missing.push entry.prettyName
  return missing

/-- The text that names the step that provisions the pinned Git packages of this repository's
workspaces: MD4Lean, which the `markdown/` workspace pins, with the website's Verso. -/
def provisioningStep : String := "lean --run lean/RegulaProvision.lean verso"

/-- The findings of the workspace that Lake loads for the project at `repo`: for each package of
the workspace, the root package and each dependency, each module under a root of Lean's toolchain
that the package provides by Lake's module lookup (`Regula.Checker.Lake.packageModules`,
`toolchainProvided`), and each of `toolchainEntries` that its library directory (`leanLibDir`)
has. It first loads the root package alone, and refuses, before Lake loads the workspace, when a
Git package of its manifest is not checked out at the pinned commit (`unprovisioned`). So, under
the hypothesis below, the load acquires no dependency.

Assumes: between that check and Lake's load of the workspace, no other process changes the
manifest, the package overrides (`.lake/package-overrides.json`) or a checkout of a dependency
that the check reads. The check does not hold them: a checkout whose `HEAD` moved in between would
make the loader fetch (`Lake.updateGitRepo`), and one removed would make it clone. This campaign
does not resolve the dependencies itself, which would repeat Lake's resolution. -/
def toolchainFindings (repo : FilePath) : IO (Array ToolchainFinding) := do
  let missing ← Regula.Checker.Workspace.withRootWorkspace repo (resolveDependencies := false)
    unprovisioned
  unless missing.isEmpty do
    throw <| IO.userError s!"observers: the workspace {repo} needs {missing.toList} at the commits \
      that its manifest pins before Lake loads it, and this check provisions no dependency: \
      provision them with `{provisioningStep}`"
  Regula.Checker.Workspace.withRootWorkspace repo fun ws => do
    Regula.Checker.Lake.checkWorkspaceModuleNames ws
    let mut findings := #[]
    for package in ws.packages do
      let name := package.baseName.toString
      let (targets, _) ← Regula.Checker.Lake.packageModules package
      for (target, module) in toolchainProvided targets do
        findings := findings.push (.provides name target module)
      for entry in toolchainEntries do
        if ← (package.leanLibDir / entry).pathExists then
          findings := findings.push (.holds name entry)
    return findings

/-- The directories, below the repository root, of the three workspaces of this repository that
`checkToolchainWorkspaces` checks, whose builds run the removal check of a program
(`Regula.Removal.checkProgram`): the root package's, the `markdown/` package's, which builds
`MarkdownMain`, and the `audit/` package's, which builds the root package's `axiomGate` and `lint`.
The Mathlib integration's workspace builds the root package's programs too, and is not one of
them: loading it needs Mathlib, which this campaign does not provision. Its builds, and an
adopter's, rest on the hypothesis of `Regula.Removal.toolchainModules` unchecked. -/
def toolchainWorkspaces : List FilePath := [".", "markdown", "audit"]

/-- Write the manifest of a control workspace at `dir` with the package entries `packages`, as
`Lake.Manifest.save` writes one (`Lake.Manifest.toJson`), through the writer of
`Regula.Filesystem`. -/
def writeControlManifest (dir : FilePath) (packages : Array _root_.Lake.PackageEntry) :
    IO Unit :=
  let manifest : _root_.Lake.Manifest :=
    { name := `control, lakeDir := ".lake", fixedToolchain := false
      packagesDir? := some ".lake/packages", packages }
  Regula.Filesystem.writeReplacing (dir / "lake-manifest.json")
    ((Json.pretty manifest.toJson).push '\n').toUTF8

/-- The control of `unprovisioned`: a workspace whose root package requires the Git package
`planted` and whose manifest pins it, with no checkout of it, is refused before Lake loads it, by
the text that names `planted` and the provisioning step. The package's address is a `file:` URL
that names no directory, so a check that let Lake load the workspace would make no network
request. -/
def provisionControl (repo : FilePath) : IO Unit := do
  let rev := "0000000000000000000000000000000000000000"
  let (refusal, _) ← Regula.Scratch.withScratch repo "provision-control" fun scratch => do
    Regula.Filesystem.writeReplacing (scratch / "lakefile.toml")
      s!"name = \"control\"\n\n[[require]]\nname = \"planted\"\n\
        git = \"file:///nonexistent\"\nrev = \"{rev}\"\n".toUTF8
    writeControlManifest scratch
      #[{ name := `planted, inherited := false, configFile := "lakefile.toml"
          manifestFile? := some "lake-manifest.json"
          src := .git "file:///nonexistent" rev (some rev) none }]
    try
      discard <| toolchainFindings scratch
      return none
    catch error => return some error.toString
  unless refusal.any fun text => text.contains "[planted]" && text.contains provisioningStep do
    throw <| IO.userError s!"observers: the control of the unprovisioned packages gave \
      {refusal}, not a refusal that names planted and `{provisioningStep}`"

/-- The control of `toolchainFindings`: a workspace whose dependency package provides the modules
`Lean.Planted` and `Planted.Fine`, and whose root package's library directory has the directory
`Std`, gives exactly the findings of `Lean.Planted` and of `Std`. It makes the workspace, with its
manifest, in a scratch directory, through the writer of `Regula.Filesystem`. -/
def toolchainControl (repo : FilePath) : IO Unit := do
  let (findings, _) ← Regula.Scratch.withScratch repo "toolchain-control" fun scratch => do
    let write (path : FilePath) (text : String) := Regula.Filesystem.writeReplacing path text.toUTF8
    let dependency := scratch / "dependency"
    write (scratch / "lakefile.toml")
      "name = \"control\"\n\n[[require]]\nname = \"dependency\"\npath = \"dependency\"\n"
    writeControlManifest scratch
      #[{ name := `dependency, inherited := false, configFile := "lakefile.toml"
          manifestFile? := some "lake-manifest.json", src := .path "dependency" }]
    write (dependency / "lakefile.toml")
      "name = \"dependency\"\n\n[[lean_lib]]\nname = \"Planted\"\n\
        roots = [\"Lean.Planted\", \"Planted.Fine\"]\n"
    write (dependency / "Lean" / "Planted.lean") ""
    write (dependency / "Planted" / "Fine.lean") ""
    discard <| Regula.Filesystem.ownRoot (scratch / ".lake" / "build" / "lib" / "lean" / "Std")
    toolchainFindings scratch
  let expected : Array ToolchainFinding :=
    #[.holds "control" "Std", .provides "dependency" "lean_lib Planted" `Lean.Planted]
  unless findings.size == expected.size && expected.all findings.contains do
    throw <| IO.userError s!"observers: the control of the toolchain modules gave \
      {(findings.map (·.describe)).toList}, not {(expected.map (·.describe)).toList}"

/-- Refuse a workspace of `toolchainWorkspaces` below the repository root `repo` with a finding
(`toolchainFindings`), or with a Git package that it pins and does not hold (`unprovisioned`),
after the controls (`provisionControl`, `toolchainControl`) gave their answers. -/
def checkToolchainWorkspaces (repo : FilePath) : IO Unit := do
  provisionControl repo
  toolchainControl repo
  for workspace in toolchainWorkspaces do
    let findings ← toolchainFindings (repo / workspace)
    unless findings.isEmpty do
      throw <| IO.userError s!"observers: the workspace {workspace} breaks the hypothesis of \
        `Regula.Removal.toolchainModules`: {(findings.map (·.describe)).toList}"
    IO.println s!"observers: workspace {workspace}: no package provides a module under Init, \
      Std, Lean or Lake"

/-- Import the environment of the root module `root`, and check it as `checkProgram` checks a
program that names no call and does not elaborate (`Regula.Removal.rawRemovals`,
`Regula.Removal.elaborationRefusal`), and as `Regula.TaskManagerCheck.checkProgram` checks a
compiled one (`Regula.TaskManagerCheck.refusal`). -/
def checkOutside (root : Name) : IO Unit := do
  let env ← importModules #[{ module := root }] {} 0
  let reach := Regula.Removal.rawRemovals env root
  if let some refused := Regula.Removal.programRefusal env root reach then
    throw <| IO.userError s!"observers: {refused}"
  if let some refused := Regula.Removal.elaborationRefusal env root false then
    throw <| IO.userError s!"observers: {refused}"
  if let some refused := Regula.TaskManagerCheck.refusal env root then
    throw <| IO.userError s!"observers: {refused}"

/-- Refuse unless every program of the root package is recorded as checked, each compiled one by
the task-manager check too, and check each root module outside every library and each workspace of
`toolchainWorkspaces` (`checkToolchainWorkspaces`). -/
def check : IO Unit := do
  let repo ← Regula.Checker.repoRoot
  let inventory ← Regula.Checker.Lake.rootSurfaceInventory repo
  Regula.Checker.initializeLeanSearchPath
  checkToolchainWorkspaces repo
  let inLibraries := (inventory.libraries.filter (·.library != fixtures)).flatMap (·.modules)
  let outside := (inventory.executables.map (·.root)).filter (!inLibraries.contains ·)
  let compiled := inventory.executables.map (·.root)
  let mut programs := compiled
  let mut records : Std.HashSet Name := {}
  let mut taskRecords : Std.HashSet Name := {}
  for module in inLibraries do
    -- Every part of a `module` file, whose exported part omits a constant it does not export.
    let names := (← Regula.Checker.readModuleCensus (← findOLean module)).2.map (·.name)
    if names.contains `main && !programs.contains module then
      programs := programs.push module
    records := records.insertMany (recordedBy Regula.Removal.reached names)
    taskRecords := taskRecords.insertMany (recordedBy Regula.TaskManagerCheck.checked names)
  for root in outside do
    checkOutside root
    records := records.insert root
    taskRecords := taskRecords.insert root
  let missing := unrecorded programs records.contains
  unless missing.isEmpty do
    throw <| IO.userError s!"observers: no module records the removal check of the programs \
      {missing.toList}: each runs `Regula.Removal.checkProgram` in its root module or in a \
      module that imports it"
  let unguarded := unrecorded compiled taskRecords.contains
  unless unguarded.isEmpty do
    throw <| IO.userError s!"observers: no module records the task-manager check of the \
      compiled programs {unguarded.toList}: each runs `Regula.TaskManagerCheck.checkProgram` at \
      the end of its root module"
  for program in programs do
    let task := if compiled.contains program then ", task-manager check recorded" else ""
    IO.println s!"observers: {program}: removal check recorded{task}"
  IO.println s!"observers: PASS ({programs.size} programs, {compiled.size} compiled)"

end Regula.Qualification.Observers
