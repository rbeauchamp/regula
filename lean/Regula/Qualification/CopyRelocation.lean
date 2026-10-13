import Regula.Qualification.Support
import Regula.Checker.Lake

/-! # The relocation of a copy's dependencies

The control of `qualify copy-relocation`. `Lake.copyProject` copies a project without its `.lake`
and without the checkout of each dependency in its packages directory, but with every other entry
there. It gives the copy an override for each dependency, to the directory and through the files
that Lake's load of the project takes (`Lake.relocateDependencies`). Lake's load of the copy must
then select what its load of the project selects (`Lake.checkCopiedWorkspace`). The copy refuses a
file that Lake's load reads for a copied package when the copy writes no file where Lake's load of
the copy reads it. The control copies `examples/fixtures/copy-relocation`, with six projects:
- `project` requires the package `dep` by path. Its manifest has two entries for `dep`: the first
  names the configuration file `a.toml`, and the last names `b.toml`.
- `git-project` keeps its dependencies' checkouts in `vendor` and requires `gdep` by Git, in the
  subdirectory `package` (`subDir`). The control commits `gdep` to a Git repository of its own,
  which Lake clones without a network, and which holds a file outside that subdirectory. Two of the
  project's libraries have owned sources in `vendor` (`ownedSources`). It requires `pdep` by the
  path `vendor/pdep/`, with a final separator (`pathDependency`). A fresh copy of it links its
  `vendor/gdep` to the first copy's checkout, and another stores `vendor/pdep` as `vendor/PDEP`.
- `lake-source` has a library whose source directory `.lake/packages/src` lies in Lake's default
  packages directory, where the control places its module from `placed`.
- `cache-config` requires the package `cdep` by path, in its own directory. The manifest entry for
  `cdep` names the configuration `.cache/package.toml`, which the control places from `placed`.
- `olean-manifest` requires the package `odep` by path, in its own directory. The manifest entry for
  `odep` names the manifest `pins.olean`, which the control places from `placed/pins.json`.
- `absolute-source` has a library whose `srcDir` is `__dir__ / "src"`, an absolute path.

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

/-- Copy the project at `project` into a new directory below `copies` named `name`, which the copy
must refuse: give the refusal's text, or `none` when the copy succeeded, and whether the copy's
tree exists afterwards. -/
private def refusedCopy (project copies : FilePath) (name : String) :
    IO (Option String × Bool) := do
  let exclude := copies / name
  IO.FS.createDirAll exclude
  let refusal ← try
      discard <| Lake.copyProject project (exclude / "tree") exclude
      pure (none : Option String)
    catch error => pure (some error.toString)
  return (refusal, ← (exclude / "tree").pathExists)

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

/-- The subdirectory of the repository of `gdep` that holds the package, as the Git project's
requirement names it. -/
def subDir : FilePath := "package"

/-- The directory, written with a final separator, at which the Git project requires `pdep` by path. -/
def pathDependency : FilePath := "vendor/pdep/"

/-- Write the manifest of the Git project at `project`: an entry that gives `gdep` by Git at the
commit `rev` of the repository `repository`, in its subdirectory `subDir`, an entry that gives
`pdep` by the path `pathDependency`, and no packages directory, so that Lake's load takes the
configuration's `vendor` (`LakeSelection.packagesDir`). -/
def writeManifest (project : FilePath) (repository rev : String) : IO Unit := do
  let entry : _root_.Lake.PackageEntry :=
    { name := `gdep, scope := "", inherited := false, configFile := "lakefile.toml"
      manifestFile? := some _root_.Lake.defaultManifestFile
      src := .git repository rev none (some subDir) }
  let pathEntry : _root_.Lake.PackageEntry :=
    { name := `pdep, scope := "", inherited := false, configFile := "lakefile.toml"
      manifestFile? := some _root_.Lake.defaultManifestFile, src := .path pathDependency }
  let manifest : _root_.Lake.Manifest :=
    { name := `git_project, lakeDir := _root_.Lake.defaultLakeDir, fixedToolchain := false
      packagesDir? := none, packages := #[entry, pathEntry] }
  manifest.save (LakeSelection.ownRootFiles project).1

/-- The owned sources of the Git project that lie in its packages directory `vendor`: the module
and a file that is not a module in the source directory `vendor/src` of the library `Vendored`,
and the module `vendor.Packaged` of the library `Packaged`, whose source directory is the
project's, with the submodule `vendor.Packaged.Child` that it imports and no glob names. -/
def ownedSources : Array String :=
  #["vendor/src/Example.lean", "vendor/src/notes.txt", "vendor/Packaged.lean",
    "vendor/Packaged/Child.lean"]

/-- The worker of `qualify copy-relocation-load PROJECT COPIES`, in the environment that its parent
gives it (`workerEnvironment`): the dependency inventory of the Git project at `project`
(`Lake.surfaceInventory`), and a copy of the project below `copies` (`copied`). It prints, as one
JSON object, each dependency with its real directory, each override of the copy with the directory
it names, whether the copy holds `vendor/gdep` or `vendor/pdep`, and which of the owned sources in
`vendor` (`ownedSources`) it holds. -/
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
    ("pathDependency", toJson (← (copy / "vendor" / "pdep").pathExists)),
    ("sources", toJson sources)]).compress

/-- Check the answer `output` that the worker (`loadWorker`) printed for the Git project at
`project`: Lake's load took the configuration's `vendor` and loaded `gdep` from its subdirectory
`subDir` of the checkout `vendor/gdep`, and `pdep` from `pathDependency`. The copy leaves out that
whole checkout, which holds a file outside the subdirectory, and the directory of `pdep`, and has an
override that names each package. It keeps each of the owned
sources in `vendor` (`ownedSources`), and Lake's load of the copy selects the libraries `Vendored`
and `Packaged` as the project's does (`copied`). -/
def checkAnswer (project : FilePath) (output : String) : IO Unit := do
  let some line := (output.splitOn "\n").filter (!·.isEmpty) |>.getLast?
    | throw <| IO.userError s!"the worker's load of {project} printed nothing"
  let answer ← IO.ofExcept (Json.parse line)
  let dependencies ← IO.ofExcept (answer.getObjValAs? (Array (String × String)) "dependencies")
  let overrides ← IO.ofExcept (answer.getObjValAs? (Array (String × String)) "overrides")
  let checkout ← IO.ofExcept (answer.getObjValAs? Bool "checkout")
  let pathCopied ← IO.ofExcept (answer.getObjValAs? Bool "pathDependency")
  let sources ← IO.ofExcept (answer.getObjValAs? (Array String) "sources")
  let expected := #[("gdep", (← IO.FS.realPath (project / "vendor" / "gdep" / subDir)).toString),
    ("pdep", (← IO.FS.realPath (project / pathDependency)).toString)]
  let sorted := fun (pairs : Array (String × String)) => pairs.qsort (·.1 < ·.1)
  requireChecks [
    ⟨s!"Lake loads gdep from vendor/gdep/{subDir} and pdep from {pathDependency}: {dependencies}",
      sorted dependencies == expected⟩,
    ⟨s!"the copy's overrides name those directories of the project: {overrides}",
      sorted overrides == expected⟩,
    ⟨"the copy leaves out the whole checkout vendor/gdep", !checkout⟩,
    ⟨s!"the copy leaves out the directory {pathDependency}", !pathCopied⟩,
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
  load (`LakeSelection.checkSelection`). The copy leaves out the whole checkout, though the package
  lies in its subdirectory `subDir`, and the directory `pathDependency` of `pdep`. It names each
  package in an override and keeps the owned sources in `vendor` (`ownedSources`).
- In a fresh copy of `git-project`, whose `vendor/gdep` is a link to that checkout, outside its own
  `vendor`, Lake's load of the project loads `gdep` through the link. The copy prunes the link
  without a refusal, and Lake's load of the copy loads `gdep` through its override (`checkAnswer`).
- In a fresh copy of `git-project` whose `vendor/pdep` is stored as `vendor/PDEP`, the control
  observes whether `vendor/pdep` names it. When it does, the volume folds case, and the copy prunes
  `vendor/PDEP` by its observed real path and passes `checkAnswer`. When it does not, Lake's load
  of the project refuses `pdep`, whose package directory it does not find.
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
  let linked := scratch / "linked-checkout"
  copyFixture (fixture / "git-project") linked
  writeManifest linked repository rev
  succeeded "link of the checkout of gdep" (← run (linked / "vendor") "ln"
    #["-s", (← IO.FS.realPath (gitProject / "vendor" / "gdep")).toString, "gdep"])
  loadInWorker root scratch linked (scratch / "copies-linked") #[]
  IO.println "copy relocation linked checkout: PASS"
  let folded := scratch / "case-folded"
  discard <| Regula.Filesystem.copy (fixture / "git-project") folded
    (· != fixture / "git-project" / "vendor" / "pdep")
  Regula.Filesystem.Construction.copyFile (fixture / "git-project" / "vendor" / "pdep" / "lakefile.toml")
    (folded / "vendor" / "PDEP" / "lakefile.toml")
  writeManifest folded repository rev
  if ← (folded / "vendor" / "pdep" / "lakefile.toml").pathExists then
    loadInWorker root scratch folded (scratch / "copies-folded") #[]
    IO.println "copy relocation path dependency stored in another case: PASS"
  else
    let result ← run root (← IO.appPath).toString #["--under-deadline", "copy-relocation-load",
      folded.toString, (scratch / "copies-folded").toString] (← workerEnvironment scratch #[])
    let output := result.stdout ++ result.stderr
    requireChecks [⟨s!"Lake's load refuses pdep, whose directory {pathDependency} is stored as \
        vendor/PDEP: {output}",
      result.exitCode != 0 && output.contains "pdep: package directory not found"⟩]
    IO.println "copy relocation path dependency stored in another case refused: PASS"
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
- A copy of `lake-source`, whose module `Example` lies below `.lake`, refuses that module by name
  and by the excluded directory, and writes nothing.
- A copy of `cache-config`, whose owned package `cdep` has its configuration below `.cache`,
  refuses that configuration file by name and by the excluded directory, and writes nothing. It
  refuses it too when `.cache/package.toml` is a link to `cdep/package.toml`.
- A copy of `olean-manifest`, whose owned package `odep` records the manifest `pins.olean`,
  refuses that manifest by name and by its compiled-module name, and writes nothing.
- A copy of `absolute-source`, whose library sets `srcDir` to the package's `src` directory as an
  absolute path, refuses that setting by name, and writes nothing.
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
    let lakeSource := source / "lake-source"
    Regula.Filesystem.Construction.copyFile (source / "placed" / "Example.lean")
      (lakeSource / _root_.Lake.defaultLakeDir / "packages" / "src" / "Example.lean")
    let (refusal, written) ← refusedCopy lakeSource copies "lake-source"
    requireChecks [
      ⟨s!"a copy refuses the module Example below .lake by name: {refusal}",
        refusal.any fun message =>
          message.contains "the source of module Example of package 'lake_source'" &&
            message.contains "as a directory named .lake"⟩,
      ⟨"the refused copy of lake-source writes nothing", !written⟩]
    IO.println "copy relocation module below an excluded directory refused: PASS"
    let cacheConfig := source / "cache-config"
    Regula.Filesystem.Construction.copyFile (source / "placed" / "package.toml")
      (cacheConfig / "cdep" / ".cache" / "package.toml")
    succeeded "git init of cache-config" (← run cacheConfig "git" #["init", "-q"])
    let (refusal, written) ← refusedCopy cacheConfig copies "cache-config"
    requireChecks [
      ⟨s!"a copy refuses the configuration of cdep below .cache by name: {refusal}",
        refusal.any fun message =>
          message.contains "the configuration file of package 'cdep'" &&
            message.contains "as a directory named .cache"⟩,
      ⟨"the refused copy of cache-config writes nothing", !written⟩]
    IO.println "copy relocation configuration below an excluded directory refused: PASS"
    -- Lake resolves the link to `cdep/package.toml` and keeps `.cache/package.toml` as the
    -- recorded path, which Lake's load of the copy reads.
    Regula.Filesystem.removePath .file (cacheConfig / "cdep" / ".cache" / "package.toml")
    Regula.Filesystem.Construction.copyFile (source / "placed" / "package.toml")
      (cacheConfig / "cdep" / "package.toml")
    succeeded "link of the configuration of cdep" (← run (cacheConfig / "cdep" / ".cache") "ln"
      #["-s", "../package.toml", "package.toml"])
    let (refusal, written) ← refusedCopy cacheConfig copies "cache-link"
    requireChecks [
      ⟨s!"a copy refuses the configuration of cdep through a link below .cache by name: {refusal}",
        refusal.any fun message =>
          message.contains "the configuration file of package 'cdep'" &&
            message.contains "as a directory named .cache"⟩,
      ⟨"the refused copy of cache-config with a link writes nothing", !written⟩]
    IO.println "copy relocation configuration linked below an excluded directory refused: PASS"
    let oleanManifest := source / "olean-manifest"
    Regula.Filesystem.Construction.copyFile (source / "placed" / "pins.json")
      (oleanManifest / "odep" / "pins.olean")
    succeeded "git init of olean-manifest" (← run oleanManifest "git" #["init", "-q"])
    let (refusal, written) ← refusedCopy oleanManifest copies "olean-manifest"
    requireChecks [
      ⟨s!"a copy refuses the manifest pins.olean of odep by name: {refusal}",
        refusal.any fun message =>
          message.contains "the manifest of package 'odep'" &&
            message.contains "a compiled-module file name"⟩,
      ⟨"the refused copy of olean-manifest writes nothing", !written⟩]
    IO.println "copy relocation manifest with a compiled-module name refused: PASS"
    let (refusal, written) ← refusedCopy (source / "absolute-source") copies "absolute-source"
    requireChecks [
      ⟨s!"a copy refuses the absolute srcDir of AbsoluteSource by name: {refusal}",
        refusal.any fun message =>
          message.contains "library AbsoluteSource of package 'absolute_source'" &&
            message.contains "sets srcDir to the absolute path"⟩,
      ⟨"the refused copy of absolute-source writes nothing", !written⟩]
    IO.println "copy relocation absolute source directory refused: PASS"
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
