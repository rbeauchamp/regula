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
build, and the packages of `controlInputs`. Before it builds a package, the check refuses each
package that has no Lake manifest and each Git dependency that is not checked out at the revision of
its manifest (`requireLocked`), since Lake would fetch it or write a manifest. A package that does
not load, a module that does not build and a compiled module that cannot be read refuse the check.

Before it reads the packages, `controls` runs the same reading of a package on packages that it
writes in a scratch directory and Lake builds there: a package with no executable whose module calls
`readDir`, and a package whose library selects a module that no module imports, which calls
`walkDir`, must each be refused with exactly that declaration, and a package with no reference must
pass. A package with no manifest and a package whose Git dependency is at another commit must each
be refused, with no manifest written and the dependency's `HEAD`, refs and manifest unchanged
(`lockControls`).

The check builds in each package, so a package needs its dependencies first: Verso for `website`,
with the MD4Lean checkout that `markdown` shares (`lean --run lean/RegulaProvision.lean verso`),
the website sources that `./scripts/verify.sh site` generates, and Mathlib for
`integration/mathlib` (`lean --run lean/RegulaProvision.lean mathlib`). -/

namespace Regula.Qualification.Readers

open Lean System

/-- The library of the root package whose modules are the inputs of the checker's controls. -/
def fixtures : String := "Fixtures"

/-- The packages of the repository that the check does not read, by their directory relative to
the repository, each with the reason. -/
def controlInputs : List (String × String) :=
  [("examples/fixtures/generated-source", "the input of a refusal control of the lint driver: its \
    configuration generates its one module, and it requires a sibling package that the control \
    supplies, so it does not build in place")]

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

/-- Each Git entry that Lake's load of `workspace` can materialize, by its name, with the directory
Lake materializes it in and the revision Lake requires there, as `Lake.Workspace.materializeDeps`
combines them (Lake v4.34.1 `Load/Resolve.lean:587-628`): each entry of the manifest, which
`Lake.Manifest.load?` decodes, replaced by the entry of the same name of the workspace's package
overrides file (`Lake.Workspace.packageOverridesFile`), each in the directory
`Lake.PackageEntry.dirName` below the manifest's packages directory
(`Load/Materialize.lean:250-252`). Lake materializes only the entries that a package requires, and
refuses a required package that has no entry, so the list holds each Git dependency Lake
materializes. A workspace with no manifest refuses: Lake would resolve its dependencies again and
fetch them (`Load/Workspace.lean:64-69`). The `lake build` of this check gives Lake no override of
its own. -/
def lockedDependencies (workspace : _root_.Lake.Workspace) :
    IO (List (String × FilePath × String)) := do
  let some manifest ← _root_.Lake.Manifest.load? workspace.manifestFile
    | throw <| IO.userError s!"it has no Lake manifest {workspace.manifestFile}, so Lake would \
        resolve its dependencies again and fetch them"
  let overrides ← _root_.Lake.Manifest.tryLoadEntries workspace.packageOverridesFile
  let relPkgsDir := manifest.packagesDir?.getD workspace.relPkgsDir
  let combine (entries : List _root_.Lake.PackageEntry) (entry : _root_.Lake.PackageEntry) :=
    entries.filter (·.name != entry.name) ++ [entry]
  let entries := (manifest.packages ++ overrides).foldl combine []
  return entries.filterMap fun entry => match entry.src with
    | .git (rev := rev) .. =>
      some (entry.prettyName, workspace.dir / relPkgsDir / entry.dirName, rev)
    | .path .. => none

/-- Refuse unless each Git dependency of `lockedDependencies` is checked out at its directory, as
the top level of its own repository, at the revision Lake requires. Lake's materialization then
fetches nothing and writes no manifest: it fetches when the directory is missing or its `HEAD` is
another revision (`Load/Materialize.lean:255-264`). Git runs isolated
(`Regula.Checker.runProcess`). -/
def requireLocked (workspace : _root_.Lake.Workspace) : IO Unit := do
  for (name, directory, revision) in ← lockedDependencies workspace do
    unless ← directory.isDir do
      throw <| IO.userError s!"its dependency {name} is not checked out at {directory}"
    let head ← Checker.runProcess directory "git" #["rev-parse", "--show-toplevel", "HEAD"]
    let lines := head.stdout.splitOn "\n"
    let (true, some top, some commit) := (head.succeeded, lines[0]?, lines[1]?)
      | throw <| IO.userError s!"its dependency {name} at {directory} has no Git checkout: \
          {head.output}"
    unless (← IO.FS.realPath (FilePath.mk top)) == (← IO.FS.realPath directory) do
      throw <| IO.userError s!"its dependency {name} at {directory} is not the top level of a \
        Git checkout: {head.output}"
    unless commit == revision do
      throw <| IO.userError s!"its dependency {name} is at {commit}, not at the revision \
        {revision} that its manifest requires"

/-- The modules of the package at `directory` that the check reads, with the directory Lake writes
their compiled files to: Lake loads the package's configuration alone, after which
`requireLocked` refuses a dependency that a build would fetch, and the modules are those of the
package's libraries and executables (`Regula.Checker.Lake.packageModules`), other than those of the
libraries `excluded`. -/
def select (directory : FilePath) (excluded : List String := []) : IO (FilePath × List Name) := do
  let (leanLibDir, modules) ← Checker.Workspace.withRootWorkspace directory
      (resolveDependencies := false) fun workspace => do
    requireLocked workspace
    let (targets, _) ← Checker.Lake.packageModules workspace.root
    let selected := targets.filter fun target =>
      !excluded.any fun library => target.target == s!"lean_lib {library}"
    return (workspace.root.leanLibDir, (selected.flatMap (·.modules)).toList.eraseDups)
  if modules.isEmpty then
    throw <| IO.userError s!"Lake selects no module of the package at {directory}"
  return (leanLibDir, modules)

/-- Read the modules `modules` of the package at `directory` (`select`): build them there, and
collect the references of their compiled declarations, from `leanLibDir`. -/
def read (directory leanLibDir : FilePath) (modules : List Name) : IO Outcome := do
  let build ← Checker.runProcess directory "lake"
    (#["build"] ++ modules.toArray.map (s!"+{·}")) Checker.scrubbedLeanPathEnv
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

/-- The Lake manifest of a package named `name` whose dependencies are `packages`, in the form that
Lake v4.34.1 writes. -/
def manifestText (name : String) (packages : Array Json) : String :=
  (Json.mkObj [("version", toJson "1.2.0"), ("packagesDir", toJson ".lake/packages"),
    ("packages", Json.arr packages), ("name", toJson name), ("lakeDir", toJson ".lake"),
    ("fixedToolchain", toJson false)]).pretty

/-- The source of a module with no reference. -/
def plainSource : String := "/-- A value. -/\ndef plain : Nat := 1\n"

/-- The files of each package of `controls`, by their path below the package. -/
def controlSources : List (String × List (String × String)) :=
  [("library", [
      ("lakefile.toml", "name = \"readers_library\"\n\n[[lean_lib]]\nname = \"Lister\"\n"),
      ("lake-manifest.json", manifestText "readers_library" #[]),
      ("Lister.lean", "/-- The number of entries of a directory. -/\n\
        def listed (path : System.FilePath) : IO Nat := return (← path.readDir).size\n")]),
    ("unimported", [
      ("lakefile.toml", "name = \"readers_unimported\"\n\n[[lean_lib]]\nname = \"Walk\"\n\
        globs = [\"Walk.+\"]\n\n[[lean_exe]]\nname = \"walker\"\nroot = \"Main\"\n"),
      ("lake-manifest.json", manifestText "readers_unimported" #[]),
      ("Main.lean", "import Walk.Clean\n\n/-- The program. -/\ndef main : IO Unit := pure ()\n"),
      ("Walk/Clean.lean", "/-- A value. -/\ndef clean : Nat := 1\n"),
      ("Walk/Hidden.lean", "/-- The number of paths below a directory. -/\n\
        def hidden (path : System.FilePath) : IO Nat := return (← path.walkDir).size\n")]),
    ("clean", [
      ("lakefile.toml", "name = \"readers_clean\"\n\n[[lean_lib]]\nname = \"Plain\"\n"),
      ("lake-manifest.json", manifestText "readers_clean" #[]),
      ("Plain.lean", plainSource)])]

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

/-- The standard output of isolated Git (`Regula.Checker.runProcess`) in `directory`, trimmed;
refuse unless it succeeds. -/
def git (directory : FilePath) (args : Array String) : IO String := do
  let result ← Checker.runProcess directory "git" args
  unless result.succeeded do
    throw <| IO.userError s!"readers: git {args} failed: {result.output}"
  return result.stdout.trimAscii.toString

/-- Whether `outcome` is a refusal whose text contains `text`. -/
def refusedWith {α : Type} (outcome : Except IO.Error α) (text : String) : Bool :=
  match outcome with
  | .error error => (toString error).contains text
  | .ok _ => false

/-- The controls of `requireLocked`, in packages written in `scratch` with the toolchain of `repo`.
A package that requires a Git package and has no manifest is refused, and no manifest is written
and no package fetched. A package whose Git dependency is checked out at the revision of its
manifest is accepted; once that checkout is moved to another commit, it is refused, and the
checkout's `HEAD`, its refs and the manifest are unchanged after the refusal. -/
def lockControls (repo scratch : FilePath) : IO Unit := do
  let remote := scratch / "remote"
  let unlocked := scratch / "unlocked"
  writePackage repo unlocked [("lakefile.toml", s!"name = \"readers_unlocked\"\n\n[[require]]\n\
      name = \"remote\"\ngit = \"{remote}\"\nrev = \"main\"\n\n[[lean_lib]]\nname = \"Plain\"\n"),
    ("Plain.lean", plainSource)]
  let refused ← (select unlocked).toBaseIO
  requireChecks [⟨"control unlocked: a package with no manifest is refused",
      refusedWith refused "has no Lake manifest"⟩,
    ⟨"control unlocked: no manifest is written",
      !(← (unlocked / "lake-manifest.json").pathExists)⟩,
    ⟨"control unlocked: no package is fetched",
      !(← (unlocked / ".lake" / "packages").pathExists)⟩]
  IO.println "readers control unlocked: a package with no manifest is refused: PASS"
  writePackage repo remote [("lakefile.toml", "name = \"remote\"\n"),
    ("Value.lean", "/-- A value. -/\ndef value : Nat := 1\n")]
  discard <| git remote #["init", "-q"]
  let commit (message : String) : IO String := do
    discard <| git remote #["add", "-A"]
    discard <| git remote #["-c", "user.name=Regula", "-c", "user.email=regula@example.invalid",
      "-c", "commit.gpgsign=false", "commit", "-q", "-m", message]
    git remote #["rev-parse", "HEAD"]
  let first ← commit "first"
  Regula.Filesystem.writeFile (remote / "Second.lean")
    "/-- A second value. -/\ndef second : Nat := 2\n"
  let second ← commit "second"
  let moved := scratch / "moved"
  let entry := Json.mkObj [("url", toJson remote.toString), ("type", toJson "git"),
    ("subDir", Json.null), ("scope", toJson ""), ("rev", toJson first),
    ("name", toJson "remote"), ("manifestFile", toJson "lake-manifest.json"),
    ("inputRev", toJson first), ("inherited", toJson false),
    ("configFile", toJson "lakefile.toml")]
  writePackage repo moved [("lakefile.toml", s!"name = \"readers_moved\"\n\n[[require]]\n\
      name = \"remote\"\ngit = \"{remote}\"\nrev = \"{first}\"\n\n\
      [[lean_lib]]\nname = \"Plain\"\n"),
    ("lake-manifest.json", manifestText "readers_moved" #[entry]), ("Plain.lean", plainSource)]
  let checkout := moved / ".lake" / "packages" / "remote"
  IO.FS.createDirAll (moved / ".lake" / "packages")
  discard <| git scratch #["clone", "-q", remote.toString, checkout.toString]
  discard <| git checkout #["checkout", "-q", "--detach", first]
  let accepted ← (select moved).toBaseIO
  requireChecks [⟨"control moved: a dependency at the revision of its manifest is accepted",
    accepted matches .ok _⟩]
  discard <| git checkout #["checkout", "-q", "--detach", second]
  let refs ← git checkout #["for-each-ref"]
  let manifest ← IO.FS.readFile (moved / "lake-manifest.json")
  let refused ← (select moved).toBaseIO
  requireChecks [⟨"control moved: a dependency at another revision is refused",
      refusedWith refused s!"is at {second}, not at the revision {first}"⟩,
    ⟨"control moved: the dependency's HEAD is unchanged",
      (← git checkout #["rev-parse", "HEAD"]) == second⟩,
    ⟨"control moved: the dependency's refs are unchanged",
      (← git checkout #["for-each-ref"]) == refs⟩,
    ⟨"control moved: the manifest is unchanged",
      (← IO.FS.readFile (moved / "lake-manifest.json")) == manifest⟩]
  IO.println "readers control moved: a dependency at another revision is refused: PASS"

/-- Write each package of `controlSources` in a scratch directory with the toolchain of `repo`,
read it as a package of the repository is read (`readPackage`), and refuse unless each gives
exactly the references and the number of modules of `controlExpected`; then run `lockControls`. -/
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
    lockControls repo scratch

/-- The reader check of every package of the repository (`qualify readers`). It selects the
modules of every package (`select`), which refuses a package whose dependencies a build would
fetch, before it builds anything: the scratch packages of `controls`, then the packages (`read`). -/
def check : IO Unit := do
  if let some failure := ReaderCheck.controlFailure then
    throw <| IO.userError s!"readers: {failure}"
  let repo ← Checker.repoRoot
  let directories ← packages repo
  for (input, _) in controlInputs do
    unless directories.contains input do
      throw <| IO.userError s!"readers: the control input {input} is not a package Git tracks"
    let listed ← Checker.runProcess repo "git"
      #["ls-files", "-z", "--", s!":(glob){input}/**/*.lean"]
    let sources := (listed.stdout.splitOn "\x00").filter fun path =>
      !path.isEmpty && path != s!"{input}/lakefile.lean"
    unless listed.succeeded && sources.isEmpty do
      throw <| IO.userError s!"readers: the control input {input} holds the Lean sources \
        {sources}, which the check does not read: {listed.output}"
  let mut selected := []
  for relative in directories do
    if let some (_, why) := controlInputs.find? (·.1 == relative) then
      IO.println s!"readers: {relative}: not read: {why}"
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
  IO.println s!"readers: PASS ({directories.length - controlInputs.length} packages, {modules} \
    modules, {declarations} declarations)"

end Regula.Qualification.Readers
