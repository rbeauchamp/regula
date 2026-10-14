import Regula.Checker.Lake
import Regula.ReaderCheck
import Regula.Qualification.Support

/-! # The reader check of every package of the repository

`lake exe qualify readers` (`./scripts/verify.sh diagnostics readers`) refuses each declaration of
a module of a package of this repository that refers to `System.FilePath.readDir` or
`System.FilePath.walkDir` (`Regula.ReaderCheck.readerReferences`).

The packages are the directories of the Lake configuration files, `lakefile.lean` and
`lakefile.toml`, that Git tracks (`packages`). Lake loads the configuration of each package alone
(`Regula.Checker.Workspace.withRootWorkspace` without its dependencies), and the modules of the
package are those of each `lean_lib` and `lean_exe` it declares, by Lake's own module resolution
(`Regula.Checker.Lake.packageModules`): each module that the globs of a library select, whether or
not a module imports it, and the root of each executable. Lake builds these modules in the package
(`lake build +MODULE ...`), and the check reads every part of each compiled module
(`Regula.Checker.readModuleCensus`) from the package's build directory, where Lake writes it
(`Lake.Module.oleanFile`).

Two sets are not read, each with its reason, which the run prints: the root package's `Fixtures`
library, whose modules are the inputs of the checker's controls and many of which are meant not to
build, and each package below `controlInputs`, the Lake configuration fixtures of the controls. A
package that does not load, a module that does not build and a compiled module that cannot be read
refuse the check.

The step is a diagnostic of the repository's own checkout, which runs after provisioning, as each
step of `./scripts/verify.sh` does. It builds the modules of each package with Lake as those steps
build, so Lake can update or fetch a dependency there as it does in them. Before it builds anything,
it refuses a package whose Git dependency is not checked out (`requireProvisioned`). Each Lake
process runs under the Git isolation of a process tree (`read`).

Before it reads the packages, `controls` runs the same reading of a package on packages that it
writes in a scratch directory and Lake builds there: a package with no executable whose module calls
`readDir`, and a package whose library selects a module that no module imports, which calls
`walkDir`, must each be refused with exactly that declaration, and a package with no reference must
pass.

The check builds in each package, so a package needs its dependencies first: Verso for `website`,
with the MD4Lean checkout that `markdown` shares (`lean --run lean/RegulaProvision.lean verso`),
the website sources that `./scripts/verify.sh site` generates, and Mathlib for
`integration/mathlib` (`lean --run lean/RegulaProvision.lean mathlib`).

Its own assumptions are the `Assumes:` entries of `gitDependencies`, `select` and `read`. It reuses
those of `Regula.Checker.readModuleCensus` (the parts of a compiled module),
`Regula.ReaderCheck.readerReferences` (Lean's collector of the constants of a declaration),
`Regula.Filesystem.Construction.isolationEnvironment` (the Git isolation of a process tree) and
`Regula.Filesystem.Construction.gitProcessArgs` (the isolated Git of `packages`). -/

namespace Regula.Qualification.Readers

open Lean System

/-- The library of the root package whose modules are the inputs of the checker's controls. -/
def fixtures : String := "Fixtures"

/-- The directory of the repository, relative to it, that holds the Lake configuration fixtures of
the controls (`Regula.DiagnosticsGate.inputs`): each package below it is the input of a control,
which copies or generates what it needs, and many do not build in place. -/
def controlInputs : String := "examples/fixtures"

/-- Whether the package at `relative`, relative to the repository, is below `controlInputs`, so
the check does not read it. -/
def controlInput (relative : String) : Bool :=
  relative.startsWith s!"{controlInputs}/"

/-- The directories, relative to `repo` and without a repetition, of the Lake configuration files
that Git tracks there, as `git ls-files` lists them, in order; `.` is the root package. -/
def packages (repo : FilePath) : IO (List String) := do
  let listed ← Checker.runProcess repo "git"
    #["ls-files", "-z", "--", ":(glob)**/lakefile.lean", ":(glob)**/lakefile.toml"]
  unless listed.succeeded do
    throw <| IO.userError s!"readers: git ls-files failed: {listed.output}"
  let directories := (listed.stdout.splitOn "\x00").filterMap fun path =>
    if path.isEmpty then none
    else
      let parent := "/".intercalate (path.splitOn "/").dropLast
      some (if parent.isEmpty then "." else parent)
  return directories.eraseDups.mergeSort (· ≤ ·)

/-- What the check read of one package. -/
structure Outcome where
  /-- The number of modules read. -/
  modules : Nat
  /-- The number of declarations read. -/
  declarations : Nat
  /-- Each declaration that refers to a directory reader, with those readers. -/
  references : List (Name × List Name)

/-- The directory of each Git dependency of the package that `workspace` loads, by its name: each
Git entry of its manifest, replaced by the entry of the same name of its package overrides file,
in the directory `Lake.PackageEntry.dirName` below the manifest's packages directory. A package
with no manifest has none.

Assumes: Lake v4.34.1 combines the entries of the manifest (`Lake.Manifest.load?`) and of the
package overrides file (`Lake.Workspace.packageOverridesFile`) in this way, and checks a Git entry
out in that directory (`src/lake/Lake/Load/Resolve.lean:587-628`,
`src/lake/Lake/Load/Materialize.lean:250-252`). -/
def gitDependencies (workspace : _root_.Lake.Workspace) : IO (List (String × FilePath)) := do
  let some manifest ← _root_.Lake.Manifest.load? workspace.manifestFile | return []
  let overrides ← _root_.Lake.Manifest.tryLoadEntries workspace.packageOverridesFile
  let relPkgsDir := manifest.packagesDir?.getD workspace.relPkgsDir
  let combine (entries : List _root_.Lake.PackageEntry) (entry : _root_.Lake.PackageEntry) :=
    entries.filter (·.name != entry.name) ++ [entry]
  let entries := (manifest.packages ++ overrides).foldl combine []
  return entries.filterMap fun entry => match entry.src with
    | .git .. => some (entry.prettyName, workspace.dir / relPkgsDir / entry.dirName)
    | .path .. => none

/-- Refuse unless the directory of each Git dependency of `gitDependencies` exists: the step runs
after provisioning, which checks the dependencies out. -/
def requireProvisioned (workspace : _root_.Lake.Workspace) : IO Unit := do
  for (name, directory) in ← gitDependencies workspace do
    unless ← Regula.Filesystem.isDirectory directory do
      throw <| IO.userError s!"its dependency {name} is not checked out at {directory}: provision \
        the dependencies first (scripts/provision.sh, then lean --run \
        lean/RegulaProvision.lean verso or mathlib)"

/-- The modules of the package at `directory` that the check reads, with the directory Lake writes
their compiled files to: Lake loads the package's configuration alone, `requireProvisioned`
refuses a dependency that is not checked out, and the modules are those of the package's libraries
and executables (`Regula.Checker.Lake.packageModules`), other than those of the libraries
`excluded`.

Assumes: Lake v4.34.1 loads the configuration of the package as `lake build` loads it there
(`loadWorkspaceRoot`, `src/lake/Lake/Load/Workspace.lean:31-54,63`), and a library's modules are
those its globs select (`LeanLib.getModuleArray`, `src/lake/Lake/Config/Module.lean:61-66`), found
by Lake's glob reader (`Glob.forEachModuleIn`, `src/lake/Lake/Config/Glob.lean:53-59`), which
`packageModules` calls. That reader lists a directory with Lean's `readDir`
(`src/lean/Lean/Util/Path.lean:33-40`), so a failed read can leave a module out of the inventory,
the defect of issue 408 in Lean's library. -/
def select (directory : FilePath) (excluded : List String := []) : IO (FilePath × List Name) := do
  let (leanLibDir, modules) ← Checker.Workspace.withRootWorkspace directory
      (resolveDependencies := false) fun workspace => do
    requireProvisioned workspace
    let (targets, _) ← Checker.Lake.packageModules workspace.root
    let selected := targets.filter fun target =>
      !excluded.any fun library => target.target == s!"lean_lib {library}"
    return (workspace.root.leanLibDir, (selected.flatMap (·.modules)).toList.eraseDups)
  if modules.isEmpty then
    throw <| IO.userError s!"Lake selects no module of the package at {directory}"
  return (leanLibDir, modules)

/-- Read the modules `modules` of the package at `directory` (`select`): build them there with
Lake, as the other steps build, and collect the references of their compiled declarations, from
`leanLibDir`. Lake runs without the inherited `LEAN_PATH` and `LEAN_SRC_PATH`
(`Regula.Checker.scrubbedLeanPathEnv`) and under the Git isolation of a process tree
(`Regula.Filesystem.Construction.isolationEnvironment`): without Git's repository environment, so
a Git command of Lake cannot select another repository through an inherited `GIT_DIR`, and with
command-scope `core.symlinks=false`. Lake can still update or fetch a dependency, as it does in the
other steps.

Assumes: Lake v4.34.1 resolves `+M` to the module `M` of the first package of the workspace that
builds it (`src/lake/Lake/CLI/Build.lean:178-183`, `src/lake/Lake/Config/Workspace.lean:286-288`),
the root package first (`:103-105`) and an executable's root before a library's module
(`src/lake/Lake/Config/LeanExe.lean:133-135`). It builds the module's compiled files
(`src/lake/Lake/CLI/Build.lean:70-74`) and writes its `.olean` file below the package's
`leanLibDir`, at the path of its name (`src/lake/Lake/Config/Module.lean:83-84,95-102`), the path
that `Regula.Checker.modulePath?` gives. Lake and the processes it starts are trusted, not
verified. -/
def read (directory leanLibDir : FilePath) (modules : List Name) : IO Outcome := do
  let build ← Checker.runProcess directory "lake"
    (#["build"] ++ modules.toArray.map (s!"+{·}"))
    (Checker.scrubbedLeanPathEnv ++ (← Regula.Filesystem.Construction.isolationEnvironment))
  unless build.succeeded do
    throw <| IO.userError s!"the build of its modules failed: {build.output}"
  let mut references := []
  let mut declarations := 0
  for name in modules do
    let some olean := Checker.modulePath? leanLibDir name "olean"
      | throw <| IO.userError s!"the module {name} has no compiled file below {leanLibDir}"
    let constants := (← Checker.readModuleCensus olean).2
    references := references ++ ReaderCheck.readerReferences constants.toList
    declarations := declarations + constants.size
  return { modules := modules.length, declarations, references }

/-- Read the package at `directory` (`select`, `read`). -/
def readPackage (directory : FilePath) (excluded : List String := []) : IO Outcome := do
  let (leanLibDir, modules) ← select directory excluded
  read directory leanLibDir modules

/-- The files of each package of `controls`, by their path below the package. -/
def controlSources : List (String × List (String × String)) :=
  [("library", [
      ("lakefile.toml", "name = \"readers_library\"\n\n[[lean_lib]]\nname = \"Lister\"\n"),
      ("Lister.lean", "/-- The number of entries of a directory. -/\n\
        def listed (path : System.FilePath) : IO Nat := return (← path.readDir).size\n")]),
    ("unimported", [
      ("lakefile.toml", "name = \"readers_unimported\"\n\n[[lean_lib]]\nname = \"Walk\"\n\
        globs = [\"Walk.+\"]\n\n[[lean_exe]]\nname = \"walker\"\nroot = \"Main\"\n"),
      ("Main.lean", "import Walk.Clean\n\n/-- The program. -/\ndef main : IO Unit := pure ()\n"),
      ("Walk/Clean.lean", "/-- A value. -/\ndef clean : Nat := 1\n"),
      ("Walk/Hidden.lean", "/-- The number of paths below a directory. -/\n\
        def hidden (path : System.FilePath) : IO Nat := return (← path.walkDir).size\n")]),
    ("clean", [
      ("lakefile.toml", "name = \"readers_clean\"\n\n[[lean_lib]]\nname = \"Plain\"\n"),
      ("Plain.lean", "/-- A value. -/\ndef plain : Nat := 1\n")])]

/-- The references that the reading of each package of `controlSources` must give, and the number
of its modules. -/
def controlExpected : List (String × List (Name × List Name) × Nat) :=
  [("library", [(`listed, [``System.FilePath.readDir])], 1),
    ("unimported", [(`hidden, [``System.FilePath.walkDir])], 3),
    ("clean", [], 1)]

/-- Write the files `files` of a package at `package`, with the toolchain of `repo`. -/
def writePackage (repo package : FilePath) (files : List (String × String)) : IO Unit := do
  IO.FS.createDirAll package
  Regula.Filesystem.copyFile (repo / "lean-toolchain") (package / "lean-toolchain")
  for (path, text) in files do
    if let some parent := (package / path).parent then IO.FS.createDirAll parent
    Regula.Filesystem.writeFile (package / path) text

/-- Write each package of `controlSources` in a scratch directory with the toolchain of `repo`,
read it as a package of the repository is read (`readPackage`), and refuse unless each gives
exactly the references and the number of modules of `controlExpected`. -/
def controls (repo : FilePath) : IO Unit :=
  withScratch repo "readers" fun scratch => do
    for (name, files) in controlSources do
      let package := scratch / name
      writePackage repo package files
      let outcome ← readPackage package
      let some (_, references, modules) := controlExpected.find? (·.1 == name)
        | throw <| IO.userError s!"readers: no expected outcome of the control {name}"
      requireChecks [⟨s!"control {name}: the references are {references}",
          outcome.references == references⟩,
        ⟨s!"control {name}: {modules} modules are read", outcome.modules == modules⟩]
      IO.println s!"readers control {name}: {outcome.references.length} references in \
        {outcome.modules} modules: PASS"

/-- The reader check of every package of the repository (`qualify readers`). It selects the
modules of every package (`select`), which refuses a package whose Git dependency is not checked
out, before it builds anything: the scratch packages of `controls`, then the packages (`read`). -/
def check : IO Unit := do
  if let some failure := ReaderCheck.controlFailure then
    throw <| IO.userError s!"readers: {failure}"
  let repo ← Checker.repoRoot
  let directories ← packages repo
  let mut selected := []
  for relative in directories do
    if controlInput relative then
      IO.println s!"readers: {relative}: not read: a Lake configuration fixture of a control"
      continue
    let excluded := if relative == "." then [fixtures] else []
    let directory := if relative == "." then repo else repo / relative
    let (leanLibDir, chosen) ← tryCatch (select directory excluded) fun error =>
      throw <| IO.userError s!"readers: {relative}: {error}"
    selected := selected ++ [(relative, directory, excluded, leanLibDir, chosen)]
  controls repo
  let mut references := []
  let mut modules := 0
  let mut declarations := 0
  for (relative, directory, excluded, leanLibDir, chosen) in selected do
    let outcome ← tryCatch (read directory leanLibDir chosen) fun error =>
      throw <| IO.userError s!"readers: {relative}: {error}"
    let left := if excluded.isEmpty then "" else
      s!", its library {fixtures} not read: the inputs of the checker's controls"
    IO.println s!"readers: {relative}: {outcome.modules} modules, {outcome.declarations} \
      declarations{left}"
    references := references ++ outcome.references
    modules := modules + outcome.modules
    declarations := declarations + outcome.declarations
  unless references.isEmpty do
    throw <| IO.userError s!"readers: {ReaderCheck.refusal references}"
  IO.println s!"readers: PASS ({selected.length} packages, {modules} \
    modules, {declarations} declarations)"

end Regula.Qualification.Readers
