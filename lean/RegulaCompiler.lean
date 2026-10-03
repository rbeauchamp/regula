import Lean.Data.Json

/-! # Install an exact compiler

CI runs this standalone program with the fixed stable bootstrap. A snapshot selection
restores and admits the immutable source-built compiler and dependencies. Without one,
Elan installs the repository's pin. Explicit preparation of a source specification builds the
named Git commit with a pinned official bootstrap, retains the checkout and build,
and links an alias only after both compiler identity observations match. A pin or
bootstrap that Elan already lists is reused, not installed again; its checks still run.

The contracts cover decoded values and the admission decision. Git, Elan, CMake,
Make, compiler self-reports, filesystem locking and subprocesses remain trusted.
-/
namespace RegulaCompiler
open Lean System

/-- A single non-hidden component for aliases, repository owners and repositories. -/
def component (value : String) : Bool :=
  !value.isEmpty && !value.startsWith "." && !value.startsWith "-" &&
    value.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- The full lowercase Git object names used by the source and bootstrap pins. -/
def objectName (value : String) : Bool :=
  value.length == 40 && value.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- A nonempty decimal component. -/
def decimal (value : String) : Bool := !value.isEmpty && value.all Char.isDigit

/-- An exact three-component release, optionally with a numbered release candidate. -/
def releaseVersion (value : String) : Bool :=
  let parts := value.splitOn "-rc"
  let version := parts.headD ""
  let suffix := match parts with
    | [_] => true
    | [_, candidate] => decimal candidate
    | _ => false
  suffix && match version.splitOn "." with
    | [major, minor, patch] => major.startsWith "v" &&
      decimal (major.drop 1).toString && decimal minor && decimal patch
    | _ => false

/-- A pinned official release or dated nightly selector. -/
def officialSelector (value : String) : Bool :=
  match value.splitOn ":" with
  | [repo, version] =>
    (repo == "leanprover/lean4" && releaseVersion version) ||
    (repo == "leanprover/lean4-nightly" && match version.splitOn "-" with
      | ["nightly", year, month, day] => year.length == 4 && month.length == 2 &&
        day.length == 2 && decimal year && decimal month && decimal day
      | _ => false)
  | _ => false

/-- Source-build inputs committed in `.github/compiler-source.json`. -/
structure Spec where
  /-- GitHub owner; the URL is constructed without credentials or arbitrary endpoints. -/
  owner : String
  /-- GitHub repository containing the Lean source commit. -/
  repository : String
  /-- Full source commit to build. -/
  revision : String
  /-- Local Elan alias, also recorded in `lean-toolchain`. -/
  selector : String
  /-- Official compiler used as the preceding build stage. -/
  bootstrap : String
  /-- Full compiler commit expected from that bootstrap. -/
  bootstrapRevision : String
  deriving FromJson, ToJson, Repr

/-- Every path, compiler identity and bootstrap selector is checked before installation. -/
def valid (spec : Spec) : Bool :=
  component spec.owner && component spec.repository && component spec.selector &&
    objectName spec.revision && objectName spec.bootstrapRevision &&
    officialSelector spec.bootstrap

/-- An admitted source specification carries the predicate the installer requires. -/
abbrev Source := { spec : Spec // valid spec = true }

/-- Decode the installer boundary without admitting malformed specifications. -/
def source? (spec : Spec) : Option Source :=
  if h : valid spec then some ⟨spec, h⟩ else none

/-- Every admitted source retains exactly the decoded specification and its validity. -/
theorem source?_sound (spec : Spec) (source : Source) (h : source? spec = some source) :
    source.val = spec ∧ valid spec = true := by
  unfold source? at h
  split at h
  · rename_i admitted
    cases Option.some.inj h
    exact ⟨rfl, admitted⟩
  · simp at h

/-- Both independently requested self-reports must name the expected source commit. -/
def admitsIdentity (expected cli library : String) : Bool :=
  objectName expected && cli == expected && library == expected

/-- Successful identity admission fixes both supplied observations to the full expected hash. -/
theorem admitsIdentity_iff (expected cli library : String) :
    admitsIdentity expected cli library = true ↔
      objectName expected = true ∧ cli = expected ∧ library = expected := by
  simp [admitsIdentity, and_assoc]

/-- System package installation is confined to the declared Linux CI environment. -/
def installsSystemPackages (githubActions runnerOS : Option String) : Bool :=
  githubActions == some "true" && runnerOS == some "Linux"

/-- The installer admits system package changes exactly in Linux GitHub Actions jobs. -/
theorem installsSystemPackages_iff (githubActions runnerOS : Option String) :
    installsSystemPackages githubActions runnerOS = true ↔
      githubActions = some "true" ∧ runnerOS = some "Linux" := by
  simp [installsSystemPackages]

/-- macOS build tools are installed only in the dedicated hosted Actions environment. -/
def installsMacPackages (githubActions runnerOS : Option String) : Bool :=
  githubActions == some "true" && runnerOS == some "macOS"

/-- The macOS installer is confined to hosted macOS Actions jobs. -/
theorem installsMacPackages_iff (githubActions runnerOS : Option String) :
    installsMacPackages githubActions runnerOS = true ↔
      githubActions = some "true" ∧ runnerOS = some "macOS" := by
  simp [installsMacPackages]

private def require (cwd : FilePath) (cmd : String) (args : Array String) : IO String := do
  let result ← IO.Process.output { cmd, args, cwd := some cwd, stdin := .null }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"compiler setup: {cmd} failed ({result.exitCode}): {result.stderr}"
  return result.stdout.trimAscii.toString

private def stream (cwd : FilePath) (cmd : String) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd, args, cwd := some cwd, stdin := .null, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do throw <| IO.userError s!"compiler setup: {cmd} failed ({code})"

/-- Install the declared native runtime and build tools only on hosted Actions runners. -/
private def installSystemPackages (root : FilePath) : IO Unit := do
  if installsSystemPackages (← IO.getEnv "GITHUB_ACTIONS") (← IO.getEnv "RUNNER_OS") then
    stream root "sudo" #["apt-get", "update"]
    stream root "sudo" #["apt-get", "install", "--yes", "build-essential", "cmake",
      "pkg-config", "libgmp-dev", "libuv1-dev", "libssl-dev"]
  if installsMacPackages (← IO.getEnv "GITHUB_ACTIONS") (← IO.getEnv "RUNNER_OS") then
    stream root "brew" #["install", "cmake", "pkg-config", "gmp", "libuv", "openssl"]

/-- Read the selected compiler's CLI and library reports through the actual executable. -/
private def checkIdentity (root : FilePath) (cmd : String) (argv : Array String)
    (expected : String) : IO Unit := do
  let cli ← require root cmd (argv ++ #["--githash"])
  let library ← require root cmd
    (argv ++ #["--run", (root / "lean" / "RegulaCompiler.lean").toString, "identity"])
  unless admitsIdentity expected cli library do
    throw <| IO.userError s!"compiler setup: expected {expected}, CLI reported {cli}, \
      library reported {library}"

private def sourceSpec (root : FilePath) : IO (Option Source) := do
  let file := root / ".github" / "compiler-source.json"
  unless ← file.pathExists do return none
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
  let spec ← IO.ofExcept <| fromJson? json
  let some source := source? spec
    | throw <| IO.userError "compiler setup: malformed source specification"
  let selector := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  unless selector == spec.selector do
    throw <| IO.userError "compiler setup: source selector differs from lean-toolchain"
  unless (← IO.FS.readFile (root / "dependency-build-mode")).trimAscii == "source" do
    throw <| IO.userError "compiler setup: source compilers require source dependency mode"
  return source

private def installed (root : FilePath) (selector : String) : IO Bool := do
  let listing ← require root "elan" #["toolchain", "list"]
  return (listing.splitOn "\n").any fun line =>
    (line.splitOn " ").head? == some selector

private def installSource (root : FilePath) (source : Source) : IO Unit := do
  let spec := source.val
  if ← installed root spec.selector then
    checkIdentity root "elan" #["run", spec.selector, "lean"] spec.revision
    return
  let some home ← IO.getEnv "HOME" | throw <| IO.userError "compiler setup: HOME is unset"
  let parent := FilePath.mk home / ".cache" / "regula-compilers"
  IO.FS.createDirAll parent
  let lock ← IO.FS.Handle.mk (parent / "install.lock") .append
  lock.lock
  try
    if ← installed root spec.selector then
      checkIdentity root "elan" #["run", spec.selector, "lean"] spec.revision
      return
    let path := parent / s!"{spec.revision}-{spec.bootstrapRevision}"
    unless ← path.pathExists do
      let random ← IO.getRandomBytes 8
      let token := random.foldl (fun n byte => n * 256 + byte.toNat) 0
      let staging := parent / s!"{spec.revision}.fetch-{← IO.Process.getPID}-{token}"
      IO.FS.createDir staging
      IO.println s!"compiler setup: preparing {staging}; an interrupted fetch is retained there"
      let _ ← require staging "git" #["init", "--quiet"]
      let _ ← require staging "git" #["remote", "add", "origin",
        s!"https://github.com/{spec.owner}/{spec.repository}.git"]
      let _ ← require staging "git" #["fetch", "--depth=1", "origin", spec.revision]
      let _ ← require staging "git" #["checkout", "--detach", spec.revision]
      unless (← require staging "git" #["rev-parse", "HEAD"]) == spec.revision do
        throw <| IO.userError "compiler setup: fetched checkout has another commit"
      IO.FS.rename staging path
    unless (← require path "git" #["rev-parse", "HEAD"]) == spec.revision do
      throw <| IO.userError s!"compiler setup: retained checkout {path} has another commit"
    unless (← require path "git" #["status", "--porcelain"]).isEmpty do
      throw <| IO.userError s!"compiler setup: retained checkout {path} has local changes"
    unless ← installed root spec.bootstrap do
      stream root "elan" #["toolchain", "install", spec.bootstrap]
    checkIdentity root "elan" #["run", spec.bootstrap, "lean"] spec.bootstrapRevision
    let previous ← require root "elan" #["run", spec.bootstrap, "lean", "--print-prefix"]
    installSystemPackages root
    let configuration := #["--preset", "release", s!"-DSTAGE1_PREV_STAGE={previous}",
      "-DUSE_LAKE_CACHE=OFF", "-DUSE_GITHASH=ON", "-DLEANC_CC=cc"]
    let configuration := if System.Platform.isOSX then configuration ++
      #["-DCMAKE_OSX_SYSROOT=", "-DCMAKE_OSX_DEPLOYMENT_TARGET=15.0"] else configuration
    stream path "cmake" configuration
    let jobs ← if System.Platform.isOSX then require root "sysctl" #["-n", "hw.logicalcpu"]
      else require root "getconf" #["_NPROCESSORS_ONLN"]
    let some jobs := jobs.toNat? | throw <| IO.userError "compiler setup: invalid CPU count"
    if jobs == 0 then throw <| IO.userError "compiler setup: empty CPU count"
    stream path "make" #[s!"-j{jobs}", "-C", "build/release"]
    let stage := path / "build" / "release" / "stage1"
    checkIdentity root (stage / "bin" / "lean").toString #[] spec.revision
    stream root "elan" #["toolchain", "link", spec.selector, stage.toString]
    checkIdentity root "elan" #["run", spec.selector, "lean"] spec.revision
  finally
    lock.unlock

private def installDeclared (root : FilePath) : IO Unit := do
  let selector := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  match ← sourceSpec root with
  | some source => installSource root source
  | none =>
    unless officialSelector selector do
      throw <| IO.userError "compiler setup: a custom alias requires compiler-source.json"
    unless ← installed root selector do
      stream root "elan" #["toolchain", "install", selector]
  stream root "elan" #["run", selector, "lean", "--version"]

/-- Whether ordinary setup must restore the selected compiled snapshot. -/
def restoresSnapshot (selected : Bool) : Bool := selected

/--
Every snapshot selection takes the restore branch of ordinary setup.

## Intent
Refuse a missing location in that branch instead of falling back to source compilation.
-/
theorem restoresSnapshot_iff (selected : Bool) :
    restoresSnapshot selected = true ↔ selected = true := Iff.rfl

/--
Install the declared ordinary compiler, or restore the complete selected snapshot.

## Intent
Snapshot selection never reaches the source compiler builder. The restore program
admits the committed digest and receipt before activating compiler and packages.
-/
def install (root : FilePath) : IO Unit := do
  if restoresSnapshot (← (root / ".github/snapshot-compiler.json").pathExists) then
    installSystemPackages root
    stream root "elan" #["run", "leanprover/lean4:v4.34.0", "lean", "--run",
      "lean/RegulaSnapshot.lean", "restore"]
  else installDeclared root

/-- Build the selected compiler only for the explicit preparation entrypoint. -/
def prepare (root : FilePath) : IO Unit := installDeclared root

end RegulaCompiler

/-- Standalone setup and the selected compiler's compiled library identity observation. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] => RegulaCompiler.install (← IO.FS.realPath (← IO.currentDir))
  | ["setup"] =>
    let root ← IO.FS.realPath (← IO.currentDir)
    match (← IO.getEnv "REGULA_SETUP_ACQUISITION").getD "restore" with
    | "restore" => RegulaCompiler.install root
    | "prepare" => RegulaCompiler.prepare root
    | _ => throw <| IO.userError "compiler setup: unknown acquisition mode"
    if let some output ← IO.getEnv "GITHUB_OUTPUT" then
      let handle ← IO.FS.Handle.mk output .append
      handle.putStr s!"snapshot={(← (root / ".github/snapshot-compiler.json").pathExists)}\n"
  | ["prepare"] => RegulaCompiler.prepare (← IO.FS.realPath (← IO.currentDir))
  | ["identity"] => IO.println Lean.githash
  | _ => throw <| IO.userError "usage: lean --run lean/RegulaCompiler.lean [identity|prepare|setup]"
