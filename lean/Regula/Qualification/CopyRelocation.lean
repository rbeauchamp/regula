import Regula.Qualification.Support
import Regula.Checker.Lake

/-! # The relocation of a copy's dependencies

The control of `qualify copy-relocation`. `Lake.copyProject` copies a project without its `.lake`
and without the checkouts in its packages directory, and gives the copy an override for each
dependency, to the directory and through the files that Lake's load of the project takes
(`Lake.relocateDependencies`). Lake's load of the copy must then select what its load of the
project selects (`Lake.checkCopiedWorkspace`). The control copies
`examples/fixtures/copy-relocation`, with two projects:
- `project` requires the package `dep` by path. Its manifest has two entries for `dep`: the first
  names the configuration file `a.toml`, and the last names `b.toml`.
- `git-project` keeps its dependencies' checkouts in `vendor` and requires `gdep` by Git. The
  control commits `gdep` to a Git repository of its own, which Lake clones without a network.

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
of that repository and its commit. -/
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

/-- The worker of `qualify copy-relocation-load PROJECT COPIES`, in the environment that its parent
gives it: the dependency inventory of the Git project at `project` (`Lake.surfaceInventory`), and
a copy of the project below `copies` (`copied`). It prints, as one JSON object, each dependency
with its real directory, each override of the copy with the directory it names, and whether the
copy holds `vendor/gdep`. -/
def loadWorker (project copies : String) : IO Unit := do
  let inventory ← Lake.surfaceInventory project
  let (copy, _, overrides) ← copied project copies "copy" "gdep"
  let dependencies ← inventory.dependencies.mapM fun dependency => do
    return (dependency.package, (← IO.FS.realPath dependency.root).toString)
  let overrides := overrides.map fun entry => (entry.name.toString, match entry.src with
    | .path dir => dir.toString
    | .git url .. => url)
  IO.println (Json.mkObj [("dependencies", toJson dependencies), ("overrides", toJson overrides),
    ("checkout", toJson (← (copy / "vendor" / "gdep").pathExists))]).compress

/-- Check the answer `output` that the worker (`loadWorker`) printed for the Git project at
`project`: Lake's load took the configuration's `vendor` and loaded `gdep` from `vendor/gdep`, and
the copy, which leaves out that checkout, has an override that names it. -/
def checkAnswer (project : FilePath) (output : String) : IO Unit := do
  let some line := (output.splitOn "\n").filter (!·.isEmpty) |>.getLast?
    | throw <| IO.userError s!"the worker's load of {project} printed nothing"
  let answer ← IO.ofExcept (Json.parse line)
  let dependencies ← IO.ofExcept (answer.getObjValAs? (Array (String × String)) "dependencies")
  let overrides ← IO.ofExcept (answer.getObjValAs? (Array (String × String)) "overrides")
  let checkout ← IO.ofExcept (answer.getObjValAs? Bool "checkout")
  let vendored := (← IO.FS.realPath (project / "vendor" / "gdep")).toString
  requireChecks [
    ⟨s!"Lake loads gdep from vendor/gdep: {dependencies}",
      dependencies == #[("gdep", vendored)]⟩,
    ⟨s!"the copy's override names vendor/gdep of the project: {overrides}",
      overrides == #[("gdep", vendored)]⟩,
    ⟨"the copy leaves out the checkout in vendor", !checkout⟩]

/-- Run the worker (`loadWorker`) on the Git project at `project`, with its copy below `copies`, in
a process where Git searches for no repository above `scratch` (`GIT_CEILING_DIRECTORIES`) and
with the environment `env` besides, and check its answer (`checkAnswer`). -/
private def loadInWorker (root scratch project copies : FilePath)
    (env : Array (String × Option String)) : IO Unit := do
  let ceiling ← IO.FS.realPath scratch
  let result ← run root (← IO.appPath).toString
    #["--under-deadline", "copy-relocation-load", project.toString, copies.toString]
    (#[("GIT_CEILING_DIRECTORIES", some ceiling.toString)] ++ env)
  succeeded s!"the worker's load of {project}" result
  checkAnswer project result.stdout

/-- The control, in a copy of the fixture:
- With a package overrides file of `project` that selects `a.toml` for `dep`, Lake's load of the
  project takes `a.toml`, and the copy's manifest, whose last entry names `b.toml`, would not. The
  copy's override names `a.toml`, and Lake's load of the copy selects what the project's selects.
- Without that overrides file, Lake's load of the project takes `b.toml`, and the copy's override
  names it.
- With the manifest that `writeManifest` gives `git-project`, which records no packages directory,
  Lake's load of the project clones `gdep` into the configuration's `vendor`. The selection takes
  that directory, and a selection that took Lake's default `.lake/packages` would not agree with the
  load (`LakeSelection.checkSelection`). The copy leaves out the checkout and names it in an
  override.
- Without a manifest, in a copy of `git-project` and with `LAKE_PKG_URL_MAP` mapping `gdep` to the
  local repository, Lake's load resolves the requirement anew. It records the remote URL of the
  requirement's URL for `gdep` and writes the local repository into its entry, and the inventory
  must accept that load (`LakeSelection.RootSelection.written`).

The loads of `git-project` run in a worker (`loadWorker`), where Git searches for no repository
above the scratch directory: a directory without `.git` below it reads to Lake's Git commands as no
repository, not as the repository that encloses the scratch directory. -/
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

end Regula.Qualification.CopyRelocation
