import Regula.Qualification.Support
import Regula.Checker.Lake

/-! # The relocation of a copy's dependencies

The control of `qualify copy-relocation`. `Lake.copyProject` copies a project without its `.lake`
and without the checkouts in its packages directory, but with the owned sources there. It gives the
copy an override for each dependency, to the directory and through the files that Lake's load of
the project takes (`Lake.relocateDependencies`). Lake's load of the copy must then select what its
load of the project selects (`Lake.checkCopiedWorkspace`). The control copies
`examples/fixtures/copy-relocation`, with two projects:
- `project` requires the package `dep` by path. Its manifest has two entries for `dep`: the first
  names the configuration file `a.toml`, and the last names `b.toml`.
- `git-project` keeps its dependencies' checkouts in `vendor` and requires `gdep` by Git. The
  control commits `gdep` to a Git repository of its own, which Lake clones without a network. Two
  of the project's libraries have owned sources in `vendor` (`ownedSources`).

The control's Git commands and its workers run without the Git repository variables that their
process inherits (`Construction.gitEnvironment`).

Lake's load of a project, its copy, Git and the files they read are trusted IO that the control
observes, not proves. -/

namespace Regula.Qualification.CopyRelocation
open Lean System RegulaQualification
open Regula.Checker

/-- The path entry for `dep` in its directory with the configuration file `a.toml`, as the first
manifest entry of the project gives it. -/
private def firstEntry : _root_.Lake.PackageEntry :=
  { name := `dep, scope := "", inherited := false, configFile := "a.toml"
    manifestFile? := some "lake-manifest.json", src := .path "../dep" }

/-- Copy the project at `project` into a new directory below `copies` named `name`, check Lake's
load of the copy against the copy's selection (`Lake.checkCopiedWorkspace`), and give the copied
project, the configuration file that Lake's load of the project selects for the package `package`
and the entries of the copy's package overrides file. -/
private def copied (project copies : FilePath) (name package : String) :
    IO (FilePath × FilePath × Array _root_.Lake.PackageEntry) := do
  let exclude := copies / name
  IO.FS.createDirAll exclude
  let copy ← Lake.copyProject project (exclude / "tree") exclude
  discard <| Lake.checkCopiedWorkspace copy.root (some copy.selection)
    (← Lake.surfaceInventory copy.project)
  let some dependency := copy.selection.dependencies.find? (·.package == package)
    | throw <| IO.userError s!"the project's selection has no dependency {package}"
  let overrides ← _root_.Lake.Manifest.tryLoadEntries
    (LakeSelection.ownRootFiles copy.project).2
  return (copy.project, dependency.configFile, overrides)

/-- Throws, labelled with `what` and the process's combined output, unless it exited with code 0. -/
private def succeeded (what : String) (result : IO.Process.Output) : IO Unit :=
  requireChecks [⟨s!"{what}: {result.stdout}{result.stderr}", result.exitCode == 0⟩]

/-- Commit the files of the directory `dir` to a new Git repository there, and give the real path
of that repository and its commit. Each Git command runs through `run`, which removes Git's
repository variables from its environment (`Construction.gitProcessArgs`). -/
private def commitRepository (dir : FilePath) : IO (String × String) := do
  for args in #[#["init", "-q"], #["add", "."], #["-c", "user.name=Copy Relocation Control", "-c",
      "user.email=copy-relocation@example.invalid", "-c", "commit.gpgsign=false", "commit", "-qm",
      "copy relocation control"]] do
    succeeded s!"git {args}" (← run dir "git" args)
  let head ← run dir "git" #["rev-parse", "HEAD"]
  succeeded "git rev-parse HEAD" head
  return ((← IO.FS.realPath dir).toString, head.stdout.trimAscii.toString)

/-- Write the manifest of the Git project at `project`: one entry, which gives `gdep` by Git at the
commit `rev` of the repository `repository`, and no packages directory, so that Lake's load takes
the configuration's `vendor` (`LakeSelection.packagesDir`). -/
def writeManifest (project : FilePath) (repository rev : String) : IO Unit := do
  let entry : _root_.Lake.PackageEntry :=
    { name := `gdep, scope := "", inherited := false, configFile := "lakefile.toml"
      manifestFile? := some _root_.Lake.defaultManifestFile, src := .git repository rev none none }
  let manifest : _root_.Lake.Manifest :=
    { name := `git_project, lakeDir := _root_.Lake.defaultLakeDir, fixedToolchain := false
      packagesDir? := none, packages := #[entry] }
  manifest.save (LakeSelection.ownRootFiles project).1

/-- The owned sources of the Git project that lie in its packages directory `vendor`: the module
and a file that is not a module in the source directory `vendor/src` of the library `Vendored`,
and the module `vendor.Packaged` of the library `Packaged`, whose source directory is the
project's. -/
def ownedSources : Array String :=
  #["vendor/src/Example.lean", "vendor/src/notes.txt", "vendor/Packaged.lean"]

/-- The worker of `qualify copy-relocation-load PROJECT COPIES`, in the environment that its parent
gives it (`workerEnvironment`): the dependency inventory of the Git project at `project`
(`Lake.surfaceInventory`), and a copy of the project below `copies` (`copied`). It prints, as one
JSON object, each dependency with its real directory, each override of the copy with the directory
it names, whether the copy holds `vendor/gdep`, and which of the owned sources in `vendor`
(`ownedSources`) it holds. -/
def loadWorker (project copies : String) : IO Unit := do
  let inventory ← Lake.surfaceInventory project
  let (copy, _, overrides) ← copied project copies "copy" "gdep"
  let dependencies ← inventory.dependencies.mapM fun dependency => do
    return (dependency.package, (← IO.FS.realPath dependency.root).toString)
  let overrides := overrides.map fun entry => (entry.name.toString, match entry.src with
    | .path dir => dir.toString
    | .git url .. => url)
  let sources ← ownedSources.filterM fun (path : String) => (copy / path).pathExists
  IO.println (Json.mkObj [("dependencies", toJson dependencies), ("overrides", toJson overrides),
    ("checkout", toJson (← (copy / "vendor" / "gdep").pathExists)),
    ("sources", toJson sources)]).compress

/-- Check the answer `output` that the worker (`loadWorker`) printed for the Git project at
`project`: Lake's load took the configuration's `vendor` and loaded `gdep` from `vendor/gdep`. The
copy leaves out that checkout and has an override that names it. It keeps each of the owned
sources in `vendor` (`ownedSources`), and Lake's load of the copy selects the libraries `Vendored`
and `Packaged` as the project's does (`copied`). -/
def checkAnswer (project : FilePath) (output : String) : IO Unit := do
  let some line := (output.splitOn "\n").filter (!·.isEmpty) |>.getLast?
    | throw <| IO.userError s!"the worker's load of {project} printed nothing"
  let answer ← IO.ofExcept (Json.parse line)
  let dependencies ← IO.ofExcept (answer.getObjValAs? (Array (String × String)) "dependencies")
  let overrides ← IO.ofExcept (answer.getObjValAs? (Array (String × String)) "overrides")
  let checkout ← IO.ofExcept (answer.getObjValAs? Bool "checkout")
  let sources ← IO.ofExcept (answer.getObjValAs? (Array String) "sources")
  let vendored := (← IO.FS.realPath (project / "vendor" / "gdep")).toString
  requireChecks [
    ⟨s!"Lake loads gdep from vendor/gdep: {dependencies}",
      dependencies == #[("gdep", vendored)]⟩,
    ⟨s!"the copy's override names vendor/gdep of the project: {overrides}",
      overrides == #[("gdep", vendored)]⟩,
    ⟨"the copy leaves out the checkout in vendor", !checkout⟩,
    ⟨s!"the copy keeps the owned sources in vendor: {sources}", sources == ownedSources⟩]

/-- The environment of a worker (`loadWorker`) that the control starts from its scratch directory
`scratch`, with the changes `env` applied last. Git's repository variables are removed
(`Construction.gitEnvironment`), and Git searches for no repository above `scratch`
(`GIT_CEILING_DIRECTORIES`). That ceiling does not bound a `GIT_DIR`, so the removal is what keeps
an inherited one from selecting its repository. -/
def workerEnvironment (scratch : FilePath) (env : Array (String × Option String)) :
    IO (Array (String × Option String)) := do
  let ceiling ← IO.FS.realPath scratch
  return (← Regula.Filesystem.Construction.gitEnvironment) ++
    #[("GIT_CEILING_DIRECTORIES", some ceiling.toString)] ++ env

/-- Run the worker (`loadWorker`) on the Git project at `project`, with its copy below `copies`, in
the environment `workerEnvironment scratch env`, and check its answer (`checkAnswer`). -/
private def loadInWorker (root scratch project copies : FilePath)
    (env : Array (String × Option String)) : IO Unit := do
  let result ← run root (← IO.appPath).toString
    #["--under-deadline", "copy-relocation-load", project.toString, copies.toString]
    (← workerEnvironment scratch env)
  succeeded s!"the worker's load of {project}" result
  checkAnswer project result.stdout

/-- The steps of the control (`check`) that run Git and Lake, as `qualify copy-relocation-git
SCRATCH`, in the scratch directory `scratch` that holds the control's copy of the fixture:
- With the manifest that `writeManifest` gives `git-project`, which records no packages directory,
  Lake's load of the project clones `gdep` into the configuration's `vendor`. The selection takes
  that directory, and a selection that took Lake's default `.lake/packages` would not agree with the
  load (`LakeSelection.checkSelection`). The copy leaves out the checkout, names it in an override,
  and keeps the owned sources in `vendor` (`ownedSources`).
- Without a manifest, in a copy of `git-project` and with `LAKE_PKG_URL_MAP` mapping `gdep` to the
  local repository, Lake's load resolves the requirement anew. It records the remote URL of the
  requirement's URL for `gdep` and writes the local repository into its entry, and the inventory
  must accept that load (`LakeSelection.RootSelection.written`).

The loads run in a worker (`loadWorker`) in the environment `workerEnvironment` gives. -/
def gitSteps (scratch : String) : IO Unit := do
  let root ← rootDirectory
  let scratch := FilePath.mk scratch
  let fixture := root / "examples" / "fixtures" / "copy-relocation"
  let source := scratch / "source"
  let (repository, rev) ← commitRepository (source / "gdep")
  let gitProject := source / "git-project"
  writeManifest gitProject repository rev
  loadInWorker root scratch gitProject (scratch / "copies-vendor") #[]
  IO.println "copy relocation packages directory of the configuration: PASS"
  let unlocked := scratch / "url-map"
  copyFixture (fixture / "git-project") unlocked
  let map := (Json.mkObj [("gdep", toJson repository)]).compress
  loadInWorker root scratch unlocked (scratch / "copies-url-map") #[("LAKE_PKG_URL_MAP", map)]
  let some manifest ← _root_.Lake.Manifest.load? (LakeSelection.ownRootFiles unlocked).1
    | throw <| IO.userError s!"Lake's load of {unlocked} wrote no manifest"
  let url := match LakeSelection.effectiveEntry manifest.packages `gdep with
    | some { src := .git url .., .. } => some url
    | _ => none
  requireChecks [⟨s!"Lake's load wrote the mapped repository into the entry of gdep: {url}",
    url == some repository⟩]
  IO.println "copy relocation URL map without a manifest: PASS"

/-- Each entry below `dir`, with the bytes of each file, read through the shared no-follow capture
(`Construction.capture`). -/
private def snapshot (dir : FilePath) : IO (List (List String × Option (List UInt8))) := do
  return (← Regula.Filesystem.Construction.capture dir).map fun item =>
    (item.relative, match item.payload with
      | .directory => none
      | .file bytes _ => some bytes.toList)

/-- The control, in a copy of the fixture:
- With a package overrides file of `project` that selects `a.toml` for `dep`, Lake's load of the
  project takes `a.toml`, and the copy's manifest, whose last entry names `b.toml`, would not. The
  copy's override names `a.toml`, and Lake's load of the copy selects what the project's selects.
- Without that overrides file, Lake's load of the project takes `b.toml`, and the copy's override
  names it.
- The steps that run Git and Lake (`gitSteps`) run in a process that inherits a `GIT_DIR` of a
  repository and an absolute `GIT_INDEX_FILE`, both in a temporary directory outside the scratch
  directory. The steps must pass, and that directory must hold the same entries and bytes after
  them. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "copy-relocation" fun scratch => do
    let fixture := root / "examples" / "fixtures" / "copy-relocation"
    let source := scratch / "source"
    copyFixture fixture source
    let project := source / "project"
    let copies := scratch / "copies"
    let overridesFile := (LakeSelection.ownRootFiles project).2
    requireChecks [⟨s!"{overridesFile} does not exist before the control writes it",
      !(← overridesFile.pathExists)⟩]
    if let some parent := overridesFile.parent then IO.FS.createDirAll parent
    _root_.Lake.Manifest.saveEntries overridesFile #[firstEntry]
    let overriddenCopy := do
      try copied project copies "overridden" "dep"
      finally Regula.Filesystem.removePath .file overridesFile
    let (_, overridden, replacements) ← overriddenCopy
    requireChecks [
      ⟨s!"the project's overrides file selects a.toml: {overridden}",
        overridden == "a.toml"⟩,
      ⟨s!"the copy's override names a.toml: {replacements.map (·.configFile)}",
        replacements.map (fun entry => (entry.name, entry.configFile.toString)) ==
          #[(`dep, "a.toml")]⟩]
    IO.println "copy relocation last manifest entry replaced: PASS"
    let (_, restored, leftover) ← copied project copies "restored" "dep"
    requireChecks [
      ⟨s!"the project's last manifest entry selects b.toml: {restored}", restored == "b.toml"⟩,
      ⟨s!"the copy's override names b.toml: {leftover.map (·.configFile)}",
        leftover.map (fun entry => (entry.name, entry.configFile.toString)) ==
          #[(`dep, "b.toml")]⟩]
    IO.println "copy relocation restored: PASS"
    Regula.Filesystem.withOwnTempDir fun outside => do
      succeeded "git init of the inherited repository"
        (← run outside "git" #["init", "-q", "inherited"])
      let inherited := #[("GIT_DIR", some (outside / "inherited" / ".git").toString),
        ("GIT_INDEX_FILE", some (outside / "index").toString)]
      let before ← snapshot outside
      let result ← run root (← IO.appPath).toString
        #["--under-deadline", "copy-relocation-git", scratch.toString] inherited
      IO.print result.stdout
      let after ← snapshot outside
      requireChecks [
        ⟨"the inherited GIT_DIR and GIT_INDEX_FILE are left untouched", before == after⟩,
        ⟨s!"the steps that run Git and Lake: {result.stdout}{result.stderr}",
          result.exitCode == 0⟩]
      IO.println "copy relocation inherited Git repository variables untouched: PASS"

end Regula.Qualification.CopyRelocation
