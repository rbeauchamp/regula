import Regula.Qualification.Support
import Regula.Checker.Workspace
import Regula.TaskManager

/-! # Git isolation of Lake's own Git commands

Lake v4.34.1 starts each of its Git commands with the environment of the process that runs Lake
(`Regula.Filesystem.Construction.processEnvironment`). These controls give that environment the
selectors of a competing private repository (`GIT_DIR`, `GIT_WORK_TREE`, `GIT_COMMON_DIR`,
`GIT_INDEX_FILE`, `GIT_OBJECT_DIRECTORY`), a command configuration that conflicts with the
isolation (`GIT_CONFIG_COUNT` with `core.symlinks=true`) and a malformed one
(`GIT_CONFIG_PARAMETERS`). They compare what Lake does with an intended private repository: the
Git dependency of a fixture workspace, pinned to its last commit, which indexes one symbolic link.
The dependency is intended when its clone is at the pinned commit, Lake's own manifest parser
(`Lake.Manifest.parse`) finds exactly one entry, a Git entry named `dep` with the dependency's URL
and that commit, and the link is a regular file that holds the link's target text.

* A Lake child started as Regula's cold drivers start one, with the isolation applied after the
  inherited environment, materializes the intended dependency, and a second run finds it there.
  The competing repository is unchanged.
* The same Lake child with `core.symlinks=true` applied after the isolation makes the link a
  symbolic link, so the regular file comes from the isolation.
* The same Lake child without the isolation does not reach that outcome, so the inherited
  environment does reach Lake's Git commands.
* A compiled Regula program started with that environment starts again under the isolation
  (`Regula.TaskManager.guard`) and loads the workspace in its own process with Lake's loader
  (`Regula.Checker.Workspace.withRootWorkspace`), which materializes the intended dependency. The
  competing repository is unchanged.
* The same program started as if it had already started again (`Regula.GitIsolation.restarted`)
  refuses with the variables still to set, and loads nothing.
* The same program under another file name, a hard link to it, refuses with the variables still
  to set, and loads nothing: the guard starts a program again only in the executable that Lake
  builds for it (`Regula.GitIsolation.runsAs`).
* A program that the Lean frontend runs (`lean --run`) through the guard refuses with that
  environment, before its program runs, and names the variables to set. With the isolation
  applied after it, its program runs. In each run its refusal runs first with the reason that the
  run has not completed (`Regula.TaskManager.startedReason`), as the guard marks the destinations
  of each run before it enters the isolation.

They are counterexample aids and observations of Lake, Git, Lean and the operating system, not
proofs. The decisions that the start under isolation rests on are proved
(`Regula.GitIsolation.unisolated_eq_empty_iff`, `Regula.GitIsolation.processEnvironment_isolated`).
-/

namespace Regula.Qualification.LakeGit
open Lean System
open Regula.Filesystem

/-- The variable that selects the worker of these controls in `qualify`. -/
def workerVariable : String := "REGULA_LAKE_GIT_WORKER"

/-- The worker of `check`: load the workspace at the one path of `args` with Lake's loader in this
process, resolving its dependencies (`Regula.Checker.Workspace.withRootWorkspace`), and print the
number of its packages. -/
def worker (args : List String) : IO UInt32 := do
  let [path] := args
    | throw <| IO.userError "the Lake Git isolation worker takes one workspace path"
  let count ← Regula.Checker.Workspace.withRootWorkspace path fun ws => pure ws.packages.size
  IO.println s!"loaded {count} packages"
  return 0

/-- Run a fixture Git command in `repo`, isolated as the Git commands of `Construction.gitOutput`
are, with no automatic maintenance, so no detached writer outlives it. -/
private def git (repo : FilePath) (args : Array String) : IO String := do
  let out ← Construction.gitOutput repo (#["-c", "maintenance.auto=false",
    "-c", "user.name=Regula", "-c", "user.email=regula@example.invalid"] ++ args)
  unless out.exitCode == 0 do throw <| IO.userError s!"fixture git {args}: {out.stderr}"
  return out.stdout.trimAscii.toString

/-- A private repository at `repo` with the files `files` in one commit, and that commit. -/
private def repository (repo : FilePath) (files : List (String × String)) : IO String := do
  construct repo (files.map fun (name, text) => ⟨[name], .file text.toUTF8⟩)
  discard <| git repo #["init", "-q"]
  discard <| git repo (#["add", "--"] ++ (files.map (·.1)).toArray)
  discard <| git repo #["commit", "-q", "-m", "fixture"]
  git repo #["rev-parse", "HEAD"]

/-- Commit, in the repository at `repo`, a symbolic link `link` whose target is the text of the
file `target`, indexed with Git's mode of a symbolic link and with no entry in the work tree, and
return the new commit (`indexLink`). No setting of the fixture's Git decides that mode. -/
private def commitLink (repo : FilePath) (link : String) (target : FilePath) : IO String := do
  indexLink (git repo) link target
  discard <| git repo #["commit", "-q", "-m", "link"]
  git repo #["rev-parse", "HEAD"]

/-- A workspace at `root` whose package requires the Git package `dep` at `url`, pinned to `rev`. -/
private def workspace (toolchain : String) (root url : FilePath) (rev : String) : IO Unit :=
  construct root [⟨["lean-toolchain"], .file toolchain.toUTF8⟩,
    ⟨["lakefile.toml"], .file (s!"name = \"root\"\n\n[[require]]\nname = \"dep\"\n\
      git = {(toJson url.toString).compress}\nrev = {(toJson rev).compress}\n").toUTF8⟩]

/-- The environment of a competing repository at `other`: its selectors, a command configuration
that conflicts with the isolation, and a malformed one. -/
private def competing (other : FilePath) : Array (String × Option String) := #[
  ("GIT_DIR", some (other / ".git").toString), ("GIT_WORK_TREE", some other.toString),
  ("GIT_COMMON_DIR", some (other / ".git").toString),
  ("GIT_INDEX_FILE", some (other / ".git/index").toString),
  ("GIT_OBJECT_DIRECTORY", some (other / ".git/objects").toString),
  ("GIT_CONFIG_COUNT", some "1"), ("GIT_CONFIG_KEY_0", some "core.symlinks"),
  ("GIT_CONFIG_VALUE_0", some "true"), ("GIT_CONFIG_PARAMETERS", some "'malformed")]

/-- What a change of the repository at `repo` would alter: its head, its references, the status of
its work tree and the bytes of its index. -/
private def state (repo : FilePath) : IO (String × String × String × Array UInt8) := do
  return (← git repo #["rev-parse", "HEAD"], ← git repo #["for-each-ref"],
    ← git repo #["status", "--porcelain", "--untracked-files=all"],
    (← IO.FS.readBinFile (repo / ".git/index")).data)

/-- The name of the dependency's symbolic link, and its target text. -/
private def link : String × String := ("link", "lakefile.toml")

/-- Whether the dependency of the workspace at `root` is intended: a clone at `rev`, which Lake's
manifest (`Lake.Manifest.parse`) records as its one entry, a Git entry named `dep` with the URL
`url` and the commit `rev`, and whose link is a regular file holding the link's target text. A
clone, manifest or link where nothing is, a head that Git does not report, a manifest that does
not parse and a link of another type each give `false`. A failure to read a path that is there,
or to start Git, is thrown, so a control that requires `false` cannot pass on it. -/
private def intended (root url : FilePath) (rev : String) : IO Bool := do
  let clone := root / ".lake/packages/dep"
  unless ← Regula.Filesystem.isPresent (clone / ".git") do return false
  let head ← Construction.gitOutput clone #["-c", "maintenance.auto=false", "rev-parse", "HEAD"]
  let some text ← Regula.Filesystem.readFileIfPresent (root / "lake-manifest.json") | return false
  let pinned := match Lake.Manifest.parse text with
    | .ok manifest => match manifest.packages with
      | #[entry] => entry.name == `dep && match entry.src with
        | .git entryUrl entryRev _ _ => entryUrl == url.toString && entryRev == rev
        | .path _ => false
      | _ => false
    | .error _ => false
  unless (← Regula.Filesystem.entryIfPresent (clone / link.1)) == some .file do return false
  return head.exitCode == 0 && head.stdout.trimAscii.toString == rev && pinned &&
    (← IO.FS.readFile (clone / link.1)) == link.2

/-- The program that the Lean frontend runs in the interpreted controls: its guarded `main` prints
`ran` when its program runs, and its refusal prints the reason and returns 7. The guard runs the
refusal before each run too, with `Regula.TaskManager.startedReason`. -/
private def interpreted : String := "\n".intercalate [
  "import Regula.TaskManager",
  "def refuse (reason : String) (_ : List String) : IO UInt32 := do",
  "  IO.println s!\"refused: {reason}\"",
  "  return 7",
  "def run (_ : List String) : IO UInt32 := do",
  "  IO.println \"ran\"",
  "  return 0",
  "def main : List String → IO UInt32 := Regula.TaskManager.guard \"interpreted\" refuse run",
  ""]

/-- The controls of the module documentation, in a fresh scratch directory. -/
def check : IO Unit := do
  unless System.Platform.isWindows do
    let root ← rootDirectory
    withScratch root "lake-git" fun scratch => do
      let toolchain ← IO.FS.readFile (root / "lean-toolchain")
      let dep := scratch / "dep"
      discard <| repository dep [("lakefile.toml", "name = \"dep\"\n")]
      construct (scratch / "blob") [⟨["target"], .file link.2.toUTF8⟩]
      let rev ← commitLink dep link.1 (scratch / "blob/target")
      let other := scratch / "competing"
      discard <| repository other
        [("lakefile.toml", "name = \"competing\"\n"), ("other.txt", "another repository\n")]
      let before ← state other
      let isolation ← Construction.isolationEnvironment
      let clean : Array (String × Option String) := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)]
      -- A Lake child as the cold drivers start one: the isolation last.
      let child := scratch / "child"
      workspace toolchain child dep rev
      for phase in ["clone", "materialized"] do
        let out ← run child (.toolchain .lake) #["resolve-deps"]
          (clean ++ competing other ++ isolation)
        requireChecks [
          ⟨s!"isolated Lake child ({phase}) exits 0: {out.stdout}{out.stderr}", out.exitCode == 0⟩,
          ⟨s!"isolated Lake child ({phase}) materializes the intended dependency",
            (← intended child dep rev)⟩,
          ⟨s!"isolated Lake child ({phase}) leaves the competing repository unchanged",
            (← state other) == before⟩]
      -- The same Lake child with `core.symlinks=true` after the isolation.
      let linked := scratch / "linked"
      workspace toolchain linked dep rev
      let mutated ← run linked (.toolchain .lake) #["resolve-deps"]
        (clean ++ competing other ++ isolation ++ #[("GIT_CONFIG_VALUE_0", some "true")])
      requireChecks [
        ⟨s!"Lake child with core.symlinks=true exits 0: {mutated.stdout}{mutated.stderr}",
          mutated.exitCode == 0⟩,
        ⟨"Lake child with core.symlinks=true makes the link a symbolic link",
          (← observeMetadata (linked / ".lake/packages/dep" / link.1)).type == .symlink⟩]
      -- The same Lake child without the isolation.
      let exposed ← run child (.toolchain .lake) #["resolve-deps"] (clean ++ competing other)
      requireChecks [⟨s!"Lake's Git commands ignore the inherited environment: \
          {exposed.stdout}{exposed.stderr}",
        !(exposed.exitCode == 0 && (← intended child dep rev) && (← state other) == before)⟩]
      -- A compiled program that loads the workspace in its own process.
      let program := (← Regula.Process.appPath).toString
      let self : Regula.Process.Program :=
        .stated program "The control starts the running qualify executable itself"
      let env := clean ++ #[(workerVariable, some "1"), ("REGULA_QUALIFICATION_WRAPPER", none),
        ("REGULA_RECEIPT_TIMER", none)] ++ competing other
      let inProcess := scratch / "in-process"
      workspace toolchain inProcess dep rev
      let loaded ← Regula.Process.output self
        { cmd := program, args := #[inProcess.toString], env, stdin := .null }
      requireChecks [
        ⟨s!"restarted program loads: {loaded.stdout}{loaded.stderr}",
          loaded.exitCode == 0 && loaded.stdout.contains "loaded 2 packages"⟩,
        ⟨"restarted program materializes the intended dependency",
          (← intended inProcess dep rev)⟩,
        ⟨"restarted program leaves the competing repository unchanged",
          (← state other) == before⟩]
      -- The same program, as if it had already started again.
      let refusedRoot := scratch / "refused"
      workspace toolchain refusedRoot dep rev
      let refused ← Regula.Process.output self {
        cmd := program, args := #[Regula.GitIsolation.restarted, refusedRoot.toString], env,
        stdin := .null }
      requireChecks [
        ⟨s!"a second start without isolation refuses: {refused.stdout}{refused.stderr}",
          refused.exitCode == 1 &&
            refused.stderr.contains "Git isolation did not take effect after one restart"⟩,
        ⟨"a refused start loads nothing",
          !(← Regula.Filesystem.isPresent (refusedRoot / ".lake"))⟩]
      -- The same program under another file name: a hard link to it, which the guard does not
      -- start again.
      let renamedRoot := scratch / "renamed-root"
      workspace toolchain renamedRoot dep rev
      let renamed := scratch / "qualify-renamed"
      let linkedProgram ← run scratch
        (.stated "ln" "The control makes a hard link to the running executable under another name")
        #[program, renamed.toString] #[]
      unless linkedProgram.exitCode == 0 do
        throw <| IO.userError s!"fixture ln: {linkedProgram.stderr}"
      let renamedRun ← Regula.Process.output
        (.stated renamed "The control starts its hard link to the running executable")
        { cmd := renamed.toString, args := #[renamedRoot.toString], env, stdin := .null }
      requireChecks [
        ⟨s!"a renamed program refuses without isolation: {renamedRun.stdout}{renamedRun.stderr}",
          renamedRun.exitCode == 1 &&
            renamedRun.stderr.contains s!"Git isolation is missing, and this process is not the \
              `{Regula.GitIsolation.executableFile "qualify"}` executable that Lake builds, so it \
              cannot start again under it; start it with: " &&
            renamedRun.stderr.contains "unset GIT_DIR" &&
            renamedRun.stderr.contains "GIT_CONFIG_VALUE_0=false"⟩,
        ⟨"a renamed program loads nothing",
          !(← Regula.Filesystem.isPresent (renamedRoot / ".lake"))⟩]
      -- A program that the Lean frontend runs, without and with the isolation.
      construct (scratch / "interpreted") [⟨["Interpreted.lean"], .file interpreted.toUTF8⟩]
      let source := (scratch / "interpreted/Interpreted.lean").toString
      let leanEnv := clean ++ #[("LEAN_PATH", some (root / ".lake/build/lib/lean").toString)] ++
        competing other
      let frontend ← run scratch (.toolchain .lean) #["--run", source] leanEnv
      -- The refusal names only the entries that the environment lacks: the competing ones, not
      -- `GIT_CONFIG_NOSYSTEM`, which this isolated process passes on unchanged.
      requireChecks [⟨s!"an interpreted program refuses without isolation: \
          {frontend.stdout}{frontend.stderr}",
        frontend.exitCode == 7 && !frontend.stdout.contains "ran" &&
          frontend.stdout.startsWith s!"refused: {Regula.TaskManager.startedReason}\nrefused: " &&
          frontend.stdout.contains s!"refused: Git isolation is missing, and this process is not \
            the `{Regula.GitIsolation.executableFile "interpreted"}` executable that Lake builds, \
            so it cannot start again under it; start it with: " &&
          frontend.stdout.contains "unset GIT_DIR" &&
          frontend.stdout.contains "unset GIT_CONFIG_PARAMETERS" &&
          frontend.stdout.contains "GIT_CONFIG_VALUE_0=false" &&
          !frontend.stdout.contains "GIT_CONFIG_NOSYSTEM"⟩]
      -- Under isolation the program runs after the refusal that marks its destinations, and no
      -- other refusal runs.
      let isolated ← run scratch (.toolchain .lean) #["--run", source] (leanEnv ++ isolation)
      requireChecks [⟨s!"an interpreted program runs under isolation: \
          {isolated.stdout}{isolated.stderr}",
        isolated.exitCode == 0 &&
          isolated.stdout == s!"refused: {Regula.TaskManager.startedReason}\nran\n"⟩]
      IO.println "Lake Git isolation: isolated Lake child, symbolic-link mutation, exposed Lake \
        child, restarted in-process load, refused second start, renamed refusal and interpreted \
        refusal PASS"

end Regula.Qualification.LakeGit
