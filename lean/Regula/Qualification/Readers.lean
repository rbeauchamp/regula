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
build, and the packages of `controlInputs`. A package that does not load or whose dependencies are
not in its packages directory, a module that does not build and a compiled module that cannot be
read refuse the check.

Before the packages, `controls` runs the same reading of a package on packages that it writes in a
scratch directory and Lake builds there: a package with no executable whose module calls `readDir`,
and a package whose library selects a module that no module imports, which calls `walkDir`, must
each be refused with exactly that declaration, and a package with no reference must pass.

The check builds in each package, so a package needs its dependencies first: Verso for `website`
(`lean --run lean/RegulaProvision.lean verso`), the website sources that
`./scripts/verify.sh site` generates, and Mathlib for `integration/mathlib`
(`lean --run lean/RegulaProvision.lean mathlib`). -/

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

/-- Refuse unless each Git dependency that the manifest of `package` records is in its packages
directory, so that its build fetches no package. -/
def requireDependencies (package : _root_.Lake.Package) : IO Unit := do
  let some manifest ← _root_.Lake.Manifest.load? package.manifestFile | return
  for entry in manifest.packages do
    if let .git .. := entry.src then
      let directory := package.pkgsDir / entry.name.toString (escape := false)
      unless ← directory.isDir do
        throw <| IO.userError s!"its dependency {entry.name} is not in {package.pkgsDir}: \
          provision it first"

/-- Read the package at `directory`: load its configuration alone, build in it the modules of its
libraries and executables, other than those of the libraries `excluded`, and collect the
references of their compiled declarations. -/
def readPackage (directory : FilePath) (excluded : List String := []) : IO Outcome := do
  let (leanLibDir, modules) ← Checker.Workspace.withRootWorkspace directory
      (resolveDependencies := false) fun workspace => do
    requireDependencies workspace.root
    let (targets, _) ← Checker.Lake.packageModules workspace.root
    let selected := targets.filter fun target =>
      !excluded.any fun library => target.target == s!"lean_lib {library}"
    return (workspace.root.leanLibDir, (selected.flatMap (·.modules)).toList.eraseDups)
  if modules.isEmpty then
    throw <| IO.userError s!"Lake selects no module of the package at {directory}"
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

/-- Write each package of `controlSources` in a scratch directory with the toolchain of `repo`,
read it as a package of the repository is read (`readPackage`), and refuse unless each gives
exactly the references and the number of modules of `controlExpected`. -/
def controls (repo : FilePath) : IO Unit :=
  withScratch repo "readers" fun scratch => do
    for (name, files) in controlSources do
      let package := scratch / name
      Regula.Filesystem.copyFile (repo / "lean-toolchain") (package / "lean-toolchain")
      for (path, text) in files do
        if let some parent := (package / path).parent then IO.FS.createDirAll parent
        Regula.Filesystem.writeFile (package / path) text
      let outcome ← readPackage package
      let some (_, references, modules) := controlExpected.find? (·.1 == name)
        | throw <| IO.userError s!"readers: no expected outcome of the control {name}"
      requireChecks [⟨s!"control {name}: the references are {references}",
          outcome.references == references⟩,
        ⟨s!"control {name}: {modules} modules are read", outcome.modules == modules⟩]
      IO.println s!"readers control {name}: {outcome.references.length} references in \
        {outcome.modules} modules: PASS"

/-- The reader check of every package of the repository (`qualify readers`). -/
def check : IO Unit := do
  if let some failure := ReaderCheck.controlFailure then
    throw <| IO.userError s!"readers: {failure}"
  let repo ← Checker.repoRoot
  controls repo
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
  let mut references := []
  let mut modules := 0
  let mut declarations := 0
  for relative in directories do
    if let some (_, why) := controlInputs.find? (·.1 == relative) then
      IO.println s!"readers: {relative}: not read: {why}"
      continue
    let excluded := if relative == "." then [fixtures] else []
    let directory := if relative == "." then repo else repo / relative
    let outcome ← tryCatch (readPackage directory excluded) fun error =>
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
