import Lean.Data.Json
import Lean.Util.Path
import Lake.Load.Manifest

/-! # Dependency provisioning

Default setup checks the released compiler and acquires one dependency: a full Git clone of the
specification package's lean-intent (`provisionSpecification`), which the first acceptance step
builds. The website's Verso has its own command (`provisionVerso`). No package of this repository
requires Mathlib.

Git, Lake, compiler reports and filesystem effects are trusted. The rules of Lake's load that
`rootEntries` and `selectedEntry` assume are trusted, not proved.
-/
namespace RegulaProvision
open System Lean

/-! ### Lake's selection of the pinned packages

What Lake v4.35.0's load of a workspace materializes its dependencies from, given its manifest and
the entries of its package overrides file as Lake's own readers decode them (`readRoot`). Each
rule is the one that the `Assumes` lines below state of Lake v4.35.0, trusted, not proved. -/

/-- The manifest and package overrides file of the workspace that Lake loads with the package at
`dir` as its root, joined as Lake joins paths.

Assumes:
- Lake v4.35.0 gives the root package of a workspace the manifest `lake-manifest.json` of its
  directory unless its load configuration names another (`Lake/Load/Config.lean:54`,
  `Lake/Load/Package.lean:35-51`), and the `lake` command names no other
  (`Lake/CLI/Main.lean:131-145`). It reads the package overrides file
  `.lake/package-overrides.json` of that directory (`Lake/Config/Workspace.lean:212-213`,
  `Lake/Config/Package.lean:208-213`). -/
def rootFiles (dir : FilePath) : FilePath × FilePath :=
  (Lake.joinRelative dir Lake.defaultManifestFile,
    Lake.joinRelative (Lake.joinRelative dir Lake.defaultLakeDir) "package-overrides.json")

/-- The entries that Lake materializes the dependencies of a workspace with the manifest `manifest`
from, in Lake's order: the manifest's, then `overrides`, those of its package overrides file.

Assumes:
- Lake v4.35.0 materializes the dependencies of a workspace that has a manifest from these entries
  in this order (`Lake/Load/Workspace.lean:61-69`, `Lake/Load/Resolve.lean:599-605`). -/
def rootEntries (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry) :
    Array Lake.PackageEntry :=
  manifest.packages ++ overrides

/-- The entry that Lake materializes the package named `name` from, among `entries`
(`rootEntries`): the last entry with that name.

Assumes:
- Lake v4.35.0 inserts the entries into a name map in order, and materializes each dependency from
  the entry that the map holds for its name (`Lake/Load/Resolve.lean:599-613`). An insertion
  replaces the entry that the map holds for the name. -/
def selectedEntry (entries : Array Lake.PackageEntry) (name : Name) :
    Option Lake.PackageEntry :=
  entries.findRev? (·.name == name)

/-- The entry selected for a name has that name, and it is one of the entries. -/
theorem selectedEntry_some {entries : Array Lake.PackageEntry} {name : Name}
    {entry : Lake.PackageEntry} (h : selectedEntry entries name = some entry) :
    entry.name = name ∧ entry ∈ entries := by
  rw [selectedEntry, Array.findRev?_eq_find?_reverse] at h
  exact ⟨by simpa using Array.find?_some h, Array.mem_reverse.mp (Array.mem_of_find?_eq_some h)⟩

/-! ## Process and filesystem effects -/

/-- Captured result of one argv invocation; there is no shell. -/
structure Ran where
  /-- The process's exit code. -/
  exitCode : UInt32
  /-- The process's standard output. -/
  stdout : String
  /-- The process's standard error. -/
  stderr : String

/-- Shared constructor source embedded by Lean; the cold provisioner imports only the toolchain.
Assumes: Lean v4.35.0 `Lean/Elab/BuiltinTerm.lean:437-445` elabIncludeStr reads this source at elaboration,
and the pinned Lean interpreter executes it before project artifacts exist. -/
def constructionSource : String := include_str "../RegulaCore/CopyProgram.lean"

/-- Run the shared construction source's entrypoint (`Construction.sourceMain`) with `args` before
cold artifacts exist, and decode the JSON it prints; `what` names the observation in an error.
The interpreter reads its source from stdin, without a temporary file or removal.

Assumes: Lean v4.35.0 `IO.Process.output` supplies stdin and waits for the child
(`Init/System/IO.lean:1544-1557`);
`Lean/Util/Path.lean:85-86` identifies the running toolchain. `--stdin --run`
(`Lean/Shell.lean:498-519,553-561`) faithfully executes constructionSource. -/
private def construction {α : Type} [FromJson α] (what : String) (args : Array String) : IO α := do
  let out ← IO.Process.output {
    cmd := ((← Lean.getBuildDir) / "bin/lean").toString
    args := #["--stdin", "--run", "Construction.lean"] ++ args
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
    (constructionSource ++ "\n/-- Cold construction entrypoint. -/\n" ++
      "def main := Regula.Filesystem.Construction.sourceMain\n")
  unless out.exitCode == 0 do
    throw <| IO.userError s!"provisioning {what} unavailable: {out.stderr}"
  IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse out.stdout)))

/-- Obtain the shared Git environment observation before cold artifacts exist. This runs the
same gitEnvironment definition as the copy adapter, without a second Git policy or launcher.
Construction.gitEnvironment documents the Git and OS assumptions. -/
private def gitEnvironment : IO (Array (String × Option String)) :=
  construction "Git environment" #["git-environment", "", ""]

private def run (cwd : FilePath) (cmd : String) (args : Array String) : IO Ran := do
  let (args, env) ← if cmd == "git" then
      pure (#["-c", "core.symlinks=false"] ++ args, ← gitEnvironment)
    else pure (args, #[])
  let out ← IO.Process.output {
    cmd, args, cwd := some cwd, env := env.push ("GHCR_TOKEN", none), stdin := .null }
  return ⟨out.exitCode, out.stdout, out.stderr⟩

private def require (cwd : FilePath) (cmd : String) (args : Array String) : IO String := do
  let ran ← run cwd cmd args
  unless ran.exitCode == 0 do
    throw <| IO.userError s!"provisioning: `{cmd} {" ".intercalate args.toList}` in {cwd} \
      failed ({ran.exitCode}): {ran.stderr.trimAscii}"
  return ran.stdout

/-- The Git isolation of the Lake commands this program starts
(`Regula.Filesystem.Construction.isolationEnvironment`), obtained as `gitEnvironment` obtains the
Git environment, from the same embedded source (`construction`). Each Lake command receives it
(`stream`), so the Git commands that Lake starts for it, and those of the programs it runs,
inherit it.

Assumes: as for `gitEnvironment`; Construction.isolationEnvironment documents the Git and OS
assumptions. -/
private def isolationEnvironment : IO (Array (String × Option String)) :=
  construction "Git isolation" #["process-environment", "", ""]

/-- Run a Lake command with inherited output, for long steps whose progress the user should see,
under the Git isolation `isolation` (`isolationEnvironment`). -/
private def stream (isolation : Array (String × Option String)) (cwd : FilePath) (cmd : String)
    (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd, args, env := isolation.push ("GHCR_TOKEN", none), cwd := some cwd,
    stdin := .null, stdout := .inherit, stderr := .inherit }
  let exit ← child.wait
  unless exit == 0 do
    throw <|
        IO.userError
            s!"provisioning: `{cmd} {" ".intercalate args.toList}` in {cwd} failed ({exit})"

/-- Whether an entry is at `path`, following a symbolic link: `true` when `path.metadata` reads it,
`false` when that read fails with `noFileOrDirectory`, and the read's error for every other error.
Lean's `System.FilePath.pathExists` returns `false` for every error of `metadata`, so a path that
cannot be read, such as one under a directory without search permission, would read as absent.
This program cannot import `Regula.Filesystem`; `Regula.ProgramCheck.Provision.isPresent_eq`
proves this equal to `Regula.Filesystem.isPresent`. -/
def isPresent (path : System.FilePath) : IO Bool := do
  match ← path.metadata.toBaseIO with
  | .ok _ => return true
  | .error (.noFileOrDirectory ..) => return false
  | .error error => throw error

/-- The manifest of the workspace whose manifest and package overrides file are `files`
(`rootFiles`), and the entries of that overrides file, each read by Lake's own reader, or `none`
when the manifest does not exist. Any other failure of a read, and a file that Lake's reader
refuses, are thrown, as Lake's load throws them.

Assumes:
- Lake v4.35.0's load reads a workspace's manifest with `Lake.Manifest.load?`
  (`Lake/Load/Workspace.lean:61-69`) and its package overrides file with
  `Lake.Manifest.tryLoadEntries` (`Lake/Load/Resolve.lean:603`), which give no manifest and no
  entries only for a file that is absent (`Lake/Load/Manifest.lean:272-276`, `:305-309`). -/
def readRoot (files : FilePath × FilePath) :
    IO (Option (Lake.Manifest × Array Lake.PackageEntry)) := do
  let some manifest ← Lake.Manifest.load? files.1 | return none
  return some (manifest, ← Lake.Manifest.tryLoadEntries files.2)

/-- Refuse a process using a different compiler from this program. -/
def requireCompiler (repo : FilePath) : IO Unit := do
  let githash := (← require repo "lean" #["--githash"]).trimAscii.toString
  unless githash == Lean.githash do
    throw <| IO.userError s!"provisioning: this repository's toolchain is {githash}, \
      but this program runs on {Lean.githash}"

/-- The commit at which Lake's load of the package at `package` checks the Git package `name` out:
that of the entry selected for `name` (`selectedEntry`) among the entries of its manifest and
package overrides file (`rootFiles`), read by Lake's own readers (`readRoot`). A package without a
manifest is refused, and so is one that materializes `name` from no Git entry. -/
def manifestRevision (repo : FilePath) (package : String) (name : Name) : IO String := do
  let files := rootFiles (repo / package)
  let some (manifest, overrides) ← readRoot files
    | throw <| IO.userError s!"provisioning: {files.1} is absent, so Lake would resolve the \
        requirements of {package} anew, at revisions that no file records"
  match (selectedEntry (rootEntries manifest overrides) name).map Lake.PackageEntry.src with
  | some (.git _ rev _ _) => return rev
  | _ => throw <| IO.userError s!"provisioning: {files.1} with {files.2} materializes no Git \
      package {name}"

/-- Provision the website's pinned Verso with the released compiler. -/
def provisionVerso (repo : FilePath) : IO Unit := do
  requireCompiler repo
  -- The standard's examples import the `audit/` package's modules in the website's workspace.
  for package in #["audit", "website"] do
    unless (← IO.FS.readFile (repo / "lean-toolchain")) ==
        (← IO.FS.readFile (repo / package / "lean-toolchain")) do
      throw <| IO.userError s!"provisioning: {package}/lean-toolchain differs from the root"
  -- The `markdown/` package pins MD4Lean in its own manifest, and the website's manifest pins it
  -- through Verso. Lake has one lock manifest for each workspace, so the commit has two sources.
  -- The two workspaces keep one checkout in the root `.lake/packages`: two commits would make
  -- each workspace move that checkout and build it again during the timed documentation step.
  let reader ← manifestRevision repo "markdown" `MD4Lean
  let verso ← manifestRevision repo "website" `MD4Lean
  unless reader == verso do
    throw <| IO.userError s!"provisioning: markdown pins MD4Lean {reader} and website pins \
      MD4Lean {verso}, each by the entry that Lake materializes it from; the two packages keep \
      one checkout, so pin the same commit in the two manifests"
  stream (← isolationEnvironment) (repo / "website") "lake" #["build", "verso/VersoManual"]

/-- The package of the specification of the smaller Regula (`specification/README.md`). It
requires lean-intent by Git and the root package by path. -/
def specificationPackage : String := "specification"

/-- The Git source and commit from which Lake's load of the package at `package` materializes the
Git package `name`: those of the entry selected for `name` (`selectedEntry`) among the entries of its
manifest and package overrides file (`rootFiles`), read by Lake's own readers (`readRoot`). -/
def manifestSource (repo : FilePath) (package : String) (name : Name) : IO (String × String) := do
  let files := rootFiles (repo / package)
  let some (manifest, overrides) ← readRoot files
    | throw <| IO.userError s!"provisioning: {files.1} is absent, so Lake would resolve the \
        requirements of {package} anew, at revisions that no file records"
  match (selectedEntry (rootEntries manifest overrides) name).map Lake.PackageEntry.src with
  | some (.git url rev _ _) => return (url, rev)
  | _ => throw <| IO.userError s!"provisioning: {files.1} with {files.2} materializes no Git \
      package {name}"

/-- The full Git clone of the specification package's lean-intent that default provisioning keeps,
relative to the repository root. It is below the root `.lake`, which the copy of the first
acceptance step leaves out, and it is not the checkout of Lake's packages directory: Lake v4.35.0
makes that one a partial clone with `git fetch --filter=tree:0` (`Lake/Util/Git.lean:160-170`),
which cannot give its commits to a further fetch. -/
def leanIntentClone : FilePath := ".lake/regula-provision/lean-intent"

/-- Whether the Git repository at `dir` holds the commit `rev`, under the Git isolation. -/
private def hasCommit (isolation : Array (String × Option String)) (dir : FilePath) (rev : String) :
    IO Bool := do
  let out ← IO.Process.output {
    cmd := "git", args := #["cat-file", "-e", s!"{rev}^\{commit}"], cwd := some dir,
    env := isolation, stdin := .null }
  return out.exitCode == 0

/-- Provision the specification package's lean-intent with the released compiler: a full Git clone,
under the Git isolation, of the source and commit that the package's manifest records
(`manifestSource`), at `leanIntentClone`. An absent clone is cloned. A clone that lacks the commit
fetches from its source. A clone that still lacks it, or a path that holds no repository, refuses
the setup. The first acceptance step fetches its copy's lean-intent from this clone
(`RegulaVerification.specificationBuild`). -/
def provisionSpecification (repo : FilePath) : IO Unit := do
  unless (← IO.FS.readFile (repo / "lean-toolchain")) ==
      (← IO.FS.readFile (repo / specificationPackage / "lean-toolchain")) do
    throw <| IO.userError s!"provisioning: {specificationPackage}/lean-toolchain differs from the \
      root"
  let (url, rev) ← manifestSource repo specificationPackage `«lean-intent»
  let isolation ← isolationEnvironment
  let clone := repo / leanIntentClone
  unless ← isPresent clone do
    -- Git creates the leading directories itself (Git v2.54.0, builtin/clone.c:1043-1051).
    stream isolation repo "git" #["clone", "--quiet", url, clone.toString]
  unless ← hasCommit isolation clone rev do
    stream isolation clone "git" #["fetch", "--quiet", "origin"]
  unless ← hasCommit isolation clone rev do
    throw <| IO.userError s!"provisioning: {clone} does not hold commit {rev} of {url}, which \
      {specificationPackage}/lake-manifest.json pins for lean-intent"

/-- Check the exact supported compiler before provisioning any dependency artifacts. -/
def requireReleasedCompiler (repo : FilePath) : IO Unit := do
  requireCompiler repo
  let out ← IO.Process.output {
    cmd := "lean", args := #["lean/RegulaPolicy/Compiler.lean"], cwd := some repo,
    env := #[("REGULA_COMPILER_GUARD", some "1"), ("GHCR_TOKEN", none)], stdin := .null }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"provisioning: released compiler guard failed:\n{out.stdout}{out.stderr}"
  unless out.stdout.replace "\r" "" == s!"{Lean.versionString}\n{Lean.githash}\n" do
    throw <| IO.userError "provisioning: the policy guard and provisioning program report different compiler identities"

/-- Refuse retired acquisition settings without installing, restoring or rewriting anything. -/
def requireReleasedSetup (repo : FilePath) : IO Unit := do
  for path in #["dependency-build-mode", ".github/compiler-source.json",
      ".github/snapshot-preparation.json", ".github/snapshot-compiler.json",
      ".github/compiler-snapshot.json"] do
    if ← isPresent (repo / path) then
      throw <| IO.userError s!"provisioning: retired compiler setup {path}; use a clean released-toolchain checkout"
  requireReleasedCompiler repo

/-- Released-toolchain setup and explicit Verso provisioning: the cold entry point.
`lean/RegulaProvision.lean`, the launcher that `scripts/provision.sh`, the local gate, CI and the
verification driver run with `lean --run`, runs the source of this module with `main` bound to
it. -/
def entry (args : List String) : IO Unit := do
  let repo ← IO.FS.realPath (← IO.currentDir)
  unless ← RegulaProvision.isPresent (repo / "lakefile.lean") do
    throw <| IO.userError "provisioning: run from the repository root"
  RegulaProvision.requireReleasedSetup repo
  match args with
  | [] =>
    RegulaProvision.provisionSpecification repo
    IO.println s!"provisioning: the {RegulaProvision.specificationPackage} package's lean-intent \
      is at the commit of its manifest; default verification needs no other dependency"
  | ["verso"] => RegulaProvision.provisionVerso repo
  | _ =>
    throw <| IO.userError "usage: lean --run lean/RegulaProvision.lean [verso]"

end RegulaProvision
