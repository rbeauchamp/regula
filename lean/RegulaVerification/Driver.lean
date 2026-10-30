import Lean
import Lake.Load.Manifest

/-! # Cold-start verification driver

Cold-start verification plan and operational interpreter. This module imports only
the pinned toolchain, so it can run before any root-package artifacts exist. Argument
selection has soundness and round-trip proofs; the interpreter consumes its proof-bearing
selection. Recipes name Lake targets, not a source-file census. The interpreter runs the
commands of the selected recipe one after another, starts a command only while every end known so
far passed, and reports success only when `passed` accepts how each of them ended
(`passed_covers`). The first acceptance step makes its builds in a private copy of the project that
this driver makes (`makeCopy`), and its last command runs Regula's checker on that copy's build.
The two acceptance steps are linked by the content identity of the files the copy construction
selects (`Copy.record`, `requireLink`).
Process effects remain trusted IO under the shell's single 420-second process-group deadline. -/
namespace RegulaVerification

/-- Closed vocabulary of supported verification invocations. -/
inductive Mode where
  /-- No argument: the first acceptance step. It makes a private copy of the project, builds
  there with warnings as errors the claimed targets of the root package, the `lint` executable and
  the modules the step type-checks, runs the registry checks, builds the specification package,
  and runs Regula's checker on the copy's own build (`lake lint`), the self-check. It records the
  content identity of the copy's files only when every command passed (`Copy.record`). -/
  | ordinary
  /-- `docs`: the second acceptance step, refused unless the files that the copy construction
  selects have the content identity that the first step recorded (`requireLink`): the controls of
  the checks of Markdown prose and the check of every tracked Markdown document, the build and the
  `lake lint` of the `audit/` package, whose modules the standard's examples import, and the build
  of the Verso standard (each of its `lean` blocks elaborated where it is written), its rendering,
  and the check of its anchors, checklist rows and rule-ID links (`lake exe site standard`). -/
  | docs
  /-- `site`: build and check the rule-reference site artifact at `_site`. -/
  | site
  deriving DecidableEq

/-- Exactly the documented arguments for each mode, with no ignored trailing arguments. -/
def arguments : Mode → List String
  | .ordinary => []
  | .docs => ["docs"]
  | .site => ["site"]

/-- Every supported mode occurs once; the parser searches only this closed vocabulary. -/
def modes : List Mode := [.ordinary, .docs, .site]

/-- Argument parsing never accepts a prefix of a supported invocation. -/
def parseMode (args : List String) : Option Mode :=
  modes.find? (fun mode => arguments mode == args)

/-- Successful parsing means exact argument equality, not a weakened prefix match. -/
theorem parseMode_sound (args : List String) (mode : Mode)
    (h : parseMode args = some mode) : args = arguments mode := by
  have exactArgs := List.find?_some h
  simpa using (eq_of_beq exactArgs).symm

/-- Every documented invocation is accepted; this excludes an always-refusing parser. -/
theorem parseMode_roundtrip (mode : Mode) : parseMode (arguments mode) = some mode := by
  cases mode <;> rfl

/-- Selection carries the argument-binding proof required by the operational caller. -/
def select (args : List String) : Option {mode : Mode // args = arguments mode} :=
  match h : parseMode args with
  | none => none
  | some mode => some ⟨mode, parseMode_sound args mode h⟩

/-- The selected mode is exactly the parser result, with no normalization or substitution. -/
theorem select_exact (args : List String) : (select args).map Subtype.val = parseMode args := by
  unfold select
  split <;> simp_all

/-- One argv invocation; there is no shell source in the recipe. -/
structure Command where
  /-- The program to run, found on `PATH`. -/
  program : String
  /-- Its arguments, passed as they are. -/
  args : Array String
  /-- Its working directory, relative to the repository root; the root itself by default. -/
  dir : String := "."
  /-- Environment variables it receives in addition to the driver's own settings (`start`). -/
  env : Array (String × String) := #[]

private def lake (args : Array String) : Command := { program := "lake", args }

/-- The package of the standard's example library (`Audit`), which imports only Lean's core
libraries and adopts the root `regula` package by relative path, as an adopting project would.
Lake commands for it run in its own directory, where its workspace is the one Lake loads. -/
def auditPackage : String := "audit"

private def lakeIn (dir : String) (args : Array String) : Command :=
  { program := "lake", args, dir }

/-- Ordinary acceptance records the content identity of the files it accepted here; the separately
timed documentation step refuses unless the files it checks have the same identity
(`requireLink`). The driver writes the record only after `passed` accepted every command of the
step, before it removes its copy and before the success line (`run`), so an accepted record here
means that every command of the step exited 0. -/
def linkPath : String := "tmp/acceptance-link.json"

/-- The text of an acceptance record that is not accepted. -/
def incompleteLink : String := "{\"schemaVersion\":1,\"status\":\"incomplete\"}\n"

/-- The package of the standard's Verso sources (`website/`), its library and its render-only
executable. -/
def websitePackage : String := "website"

/-- Where the documentation step renders the standard, relative to the repository root. -/
def standardOutput : String := "tmp/standard-render"

/-- The package of the Markdown checks: md4c's reader and the `regula-markdown` executable. It
requires only the md4c binding and the root package. -/
def markdownPackage : String := "markdown"

/-- The controls of the checks of Markdown prose (C1 to C8), of the vocabulary (C9) and of the
baseline (B1 and B2), relative to the Markdown package. -/
def proseControls : String := "../lean/Fixtures/ControlledProse"

/-- The targets that the surface manifest `foundation_manifest.json` claims, which the first
acceptance step builds with warnings as errors and checks (`buildCovers`). -/
def surfaceTargets : List String :=
  ["RegulaInterface", "RegulaPolicy", "RegulaVerification", "RegulaProvision",
    "RegulaQualification", "RegulaCore", "AuditApp", "auditApp"]

/-- The other targets of the first acceptance step's build: the excluded library `Regula`, whose
modules the checker loads with the rest, and the executables of the checker, of setup and of the
site. -/
def otherTargets : List String :=
  ["Regula", "lint", "regula", "site"]

/-- The package of the specification of the smaller Regula (`specification/README.md`), the name
`RegulaProvision.specificationPackage` written again here because this driver imports only the
toolchain. It requires lean-intent by Git and the root package by path. -/
def specificationPackage : String := "specification"

/-- The full clone of lean-intent that default provisioning keeps for the specification package
(`RegulaProvision.leanIntentClone`), relative to the repository root. -/
def leanIntentCheckout : String := ".lake/regula-provision/lean-intent"

/-- The build of the specification package of the copy with warnings as errors, started in the
checkout's root. The copy has no `.lake` of the checkout (`Construction.projectRelative`), so the
copy's specification package has no lean-intent checkout. Lake v4.35.0 then makes one: it
initializes a repository whose remote is the URL that `LAKE_PKG_URL_MAP` maps lean-intent to, here
the provisioned clone (`leanIntentCheckout`), fetches the commit of the package's manifest from it,
and checks that commit out (`Lake/Load/Materialize.lean:37-105`, `Lake/Load/Materialize.lean:270-281`
and `Lake/Config/Env.lean:205-209`). A fetch that cannot give that commit fails the build. Lake
resolves a local path from its own working directory, the checkout's root, so the relative path
names the provisioned clone, and the build reads no network. The map's keys are names, so the key
is spelled `«lean-intent»`, as the manifest spells the entry's name. Its dependency `regula` is the
copy's root, whose modules the step's first build built. -/
def specificationBuild (copy : String) : Command :=
  { program := "lake"
    args := #["-d", (System.FilePath.mk copy / specificationPackage).toString, "build", "--wfail",
      "RegulaSpecification"]
    env := #[("LAKE_PKG_URL_MAP", s!"\{\"«lean-intent»\":\"{leanIntentCheckout}\"}")] }

/-- Lean's kernel replay of the copy's build (RG2005, which the specification hands to Lean), run in
the copy. At Lean v4.35.0 `lake check` builds the default targets of the root package, imports
their modules into one environment, exports each constant in its scope whose name is not internal
with the constants that each mentions, and replays that export with `leanchecker --silent
--from-export`, in a process that loads no `.olean` file of the project. It also refuses each axiom
other than `propext`, `Classical.choice` and `Quot.sound` that an exported constant mentions
(`Lake/CLI/Main.lean:1218-1240`, `Lake/CLI/Check.lean:459-472`, `662-684` and `753-774`). Each
claimed target is a default target (RG2002), so the export holds every constant of each claimed
module. `--inadvisably-no-sandbox` runs it without its `bwrap` sandbox, on every platform: outside
Linux `lake check` refuses to start without it (`Lake/CLI/Check.lean:599-614`), and the step's
CI provisioning installs no `bwrap`; the build and the export then run outside a sandbox, as
the step's `lake build` does just before. -/
def kernelReplay (copy : String) : Command :=
  lakeIn copy #["check", "--inadvisably-no-sandbox"]

/-- The commands of each mode, run one after another inside the outer deadline. `copy` is the
root of the copy that the first acceptance step builds in (`makeCopy`); no other mode uses it. -/
def commands (copy : String) : Mode → List Command
  | .ordinary => [
      -- The build of the step, in the copy, with warnings as errors: every claimed target, the
      -- checker and the other tools, and the modules the step type-checks (RG2003 is Lean's).
      lakeIn copy (#["build", "--wfail"] ++ (surfaceTargets ++ otherTargets).toArray),
      -- Lean's kernel replays the copy's build (RG2005 is Lean's): `lake check` exports every
      -- constant in the scope of the modules of the default targets and replays the export with
      -- `leanchecker` (`kernelReplay`).
      kernelReplay copy,
      lakeIn copy #["env", "lean", "--run", "lean/Regula/RegistryChecks.lean"],
      -- The specification package of the copy, with warnings as errors, from the repository
      -- root, so that Lake clones its lean-intent from the provisioned checkout.
      specificationBuild copy,
      -- Last: Regula's checker on the copy's own build, the self-check.
      lakeIn copy #["lint"]]
  | .docs => [
      -- The controls of the checks C1 to C9, B1 and B2: each check accepts its positive controls
      -- and refuses the others, with the exact file, line and check at the start of each
      -- refusal (`markdown/MarkdownMain.lean`).
      lakeIn markdownPackage #["exe", "regula-markdown", "--controls", proseControls],
      -- Every Markdown document Git tracks, read by md4c: a rule ID in prose that is not a link
      -- to its rule page is refused, and so are the findings of the checks C1 to C9 that the
      -- baseline `prose-baseline.json` does not permit, and the changes of the baseline that
      -- checks B1 and B2 refuse. The argument is the repository root, relative to the package.
      lakeIn markdownPackage #["exe", "regula-markdown", ".."],
      -- The `audit/` package, as an adopter of `regula` builds and checks it, with the three
      -- commands of the gate: the standard's `lean` blocks import its modules.
      lakeIn auditPackage #["build", "--wfail"],
      lakeIn auditPackage #["check", "--inadvisably-no-sandbox"],
      lakeIn auditPackage #["lint"],
      -- The Verso standard: its build elaborates each `lean` block where it is written; then its
      -- rendering, and the check of what it rendered.
      lakeIn websitePackage #["build", "--wfail", "RegulaStandard", "regula-standard"],
      lakeIn websitePackage #["exe", "regula-standard", "--output", "../" ++ standardOutput],
      lake #["exe", "site", "standard", standardOutput ++ "/html-multi", "docs"]]
  | .site => [
      lake #["build", "site"],
      -- The standard's earlier build output, which the site's build refuses: Lake removes it.
      lakeIn websitePackage #["clean"],
      lake #["exe", "site", "build"]]

/-- Every mode schedules actual work rather than accepting an empty campaign. -/
theorem commands_nonempty (copy : String) (mode : Mode) : commands copy mode ≠ [] := by
  cases mode <;> simp [commands]

/-- The first acceptance step runs its build, Lean's kernel replay and the registry checks in the
copy, then the build of the copy's specification package from the repository root, and last
Regula's checker in the copy. -/
theorem ordinary_places (copy : String) :
    (commands copy .ordinary).map (·.dir) = [copy, copy, copy, ".", copy] := rfl

/-- The first acceptance step builds the specification package of its copy with warnings as
errors and runs Regula's checker on its copy's build, last; a failure of either fails the step
(`passed_iff`). -/
theorem ordinary_checks (copy : String) :
    specificationBuild copy ∈ commands copy .ordinary ∧
      (specificationBuild copy).args.toList.drop 2 = ["build", "--wfail", "RegulaSpecification"] ∧
      (commands copy .ordinary).getLast? = some (lakeIn copy #["lint"]) :=
  ⟨by simp [commands], rfl, rfl⟩

/-- The first acceptance step runs, in its copy and in this order, the three commands of the gate
of the specification of the smaller Regula: the build of every claimed target with warnings as
errors (RG2003), then Lean's kernel replay (`kernelReplay`, RG2005), and last Regula's checker.
A failure of any of them fails the step (`passed_iff`). -/
theorem ordinary_gate (copy : String) :
    (commands copy .ordinary).take 2 =
        [lakeIn copy (#["build", "--wfail"] ++ (surfaceTargets ++ otherTargets).toArray),
          kernelReplay copy] ∧
      (commands copy .ordinary).getLast? = some (lakeIn copy #["lint"]) :=
  ⟨rfl, rfl⟩

/-- Whether a step passed, from how its commands ended. An end is `some status` for a command
that ran to its end with that exit status, and `none` for one that was not run, could not be
started, or whose end could not be observed. A step passes exactly when every command ended with
exit status 0 (`passed_iff`). It is the driver's one decision about an exit status: the driver
asks it before it runs a further command, before it reports, and before it moves an acceptance
record. -/
def passed (ends : List (Option UInt32)) : Bool :=
  ends.all (· == some 0)

/-- `passed` accepts exactly the ends in which each command has exit status 0. -/
theorem passed_iff (ends : List (Option UInt32)) :
    passed ends = true ↔ ∀ ended ∈ ends, ended = some 0 := by
  simp [passed]

/-- Commands with how each ended. It has an entry for each of `commands`, in their order, so no
value of this type leaves a command out. -/
structure Ends (commands : List Command) where
  /-- Each command with how it ended (`passed`). -/
  ends : List (Command × Option UInt32)
  /-- One entry for each command, in the commands' order. -/
  complete : ends.map (·.1) = commands

/-- How the commands ended, without the commands: what `passed` reads. -/
def Ends.statuses {commands : List Command} (group : Ends commands) : List (Option UInt32) :=
  group.ends.map (·.2)

/-- The ends of two groups of commands, as the ends of both, in the order of the groups. -/
def Ends.append {first second : List Command} (early : Ends first) (late : Ends second) :
    Ends (first ++ second) :=
  ⟨early.ends ++ late.ends, by simp [early.complete, late.complete]⟩

/-- When `passed` accepts the ends of the commands, every command is recorded with exit status
0. None is left out, because an `Ends` has an entry for each of its commands. That each recorded
status is the one the command's process ended with is the trusted process runtime. -/
theorem passed_covers {commands : List Command} (group : Ends commands)
    (accepted : passed group.statuses = true) :
    ∀ command ∈ commands, (command, some 0) ∈ group.ends := by
  intro command member
  have zeros := (passed_iff _).mp accepted
  rw [← group.complete] at member
  obtain ⟨⟨recorded, ended⟩, entry, rfl⟩ := List.mem_map.mp member
  have zero := zeros ended (List.mem_map.mpr ⟨_, entry, rfl⟩)
  exact zero ▸ entry

/-- Print one line of the driver's own progress at once, so that it stands in the output where it
happened among the lines its child processes write. It cannot raise: a progress line that could
not be written changes no result. -/
def announce (line : String) : BaseIO Unit := do
  let write : IO Unit := do
    IO.println s!"verification: {line}"
    (← IO.getStdout).flush
  discard write.toBaseIO

/-- A command as the progress lines show it. -/
def Command.display (command : Command) : String :=
  " ".intercalate ((command.env.map fun (name, value) => s!"{name}={value}").toList ++
    command.program :: command.args.toList) ++
    (if command.dir = "." then "" else s!" (in {command.dir})")

/-- An end as the progress lines and the failure report show it. No end has one label for its
three causes: the command was not run after an earlier failure, could not be started, or its end
could not be observed. A `could not start` or `could not wait` line names the last two. -/
def describe : Option UInt32 → String
  | some status => s!"exit status {status}"
  | none => "not run, or no end observed"

/-- The standard streams of every command: no input, and the driver's own output. -/
def stdio : IO.Process.StdioConfig := { stdin := .null, stdout := .inherit, stderr := .inherit }

/-- The shared constructor's exact source, embedded by Lean before any root artifact exists.
Assumes: Lean v4.35.0 `Lean/Elab/BuiltinTerm.lean:437-445` elabIncludeStr reads this source at elaboration;
the pinned Lean interpreter executes it. There is no second tree-walk implementation. -/
def constructionSource : String := include_str "../RegulaCore/CopyProgram.lean"

/-- Run the shared construction source's entrypoint (`Construction.sourceMain`) with `args` before
cold artifacts exist, and decode the JSON it prints; `what` names the observation in an error.

Assumes: Lean v4.35.0 `IO.Process.output` supplies stdin and waits for the child
(`Init/System/IO.lean:1544-1557`);
`Lean/Util/Path.lean:85-86` identifies the interpreter. `--stdin --run`
(`Lean/Shell.lean:498-519,553-561`) executes the embedded source without a temporary file or
removal; interpreter execution is trusted. -/
private def construction {α : Type} [Lean.FromJson α] (what : String) (args : Array String) :
    IO α := do
  let out ← IO.Process.output {
    cmd := ((← Lean.getBuildDir) / "bin/lean").toString
    args := #["--stdin", "--run", "Construction.lean"] ++ args
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
    (constructionSource ++ "\n/-- Cold construction entrypoint. -/\n" ++
      "def main := Regula.Filesystem.Construction.sourceMain\n")
  unless out.exitCode == 0 do
    throw <| IO.userError s!"verification {what} unavailable: {out.stderr}"
  IO.ofExcept (Lean.fromJson? (← IO.ofExcept (Lean.Json.parse out.stdout)))

/-- The Git isolation of the commands this driver starts
(`Regula.Filesystem.Construction.isolationEnvironment`), obtained before cold artifacts exist by
running the shared constructor's source with the interpreter (`construction`). The driver obtains
it once, before its first command (`run`), and gives it to every command it starts (`start`), so
each Git and Lake command, and every Git command that Lake starts for it, inherits it, and a
compiled program that a command runs finds its environment isolated and does not start again.
Construction.isolationEnvironment names its pinned Git and OS assumptions. -/
def isolationEnvironment : IO (Array (String × Option String)) :=
  construction "Git isolation" #["process-environment", "", ""]

/-- The entries of the directory `path`, listed by the shared construction source
(`Construction.listNames`), so a failed read of the directory stops instead of returning fewer
entries. `Construction.ReadsNames` names the listing programs it admits and their sources. -/
def listDirectory (path : System.FilePath) : IO (Array IO.FS.DirEntry) := do
  let names : Array String ← construction s!"listing of {path}" #["list", path.toString, ""]
  return names.map fun name => { root := path, fileName := name }

/-- Each path below `root`, walked by the shared construction source (`Construction.walkDirectory`,
`walkDir`'s order and link behaviour), so a failed read of a directory stops the walk instead of
omitting its entries. -/
def walkDirectory (root : System.FilePath) : IO (Array System.FilePath) := do
  let paths : Array String ← construction s!"walk of {root}" #["walk", root.toString, ""]
  return paths.map System.FilePath.mk

/-- Start `command` without waiting for it; `none`, with a report, when it could not be started.
It cannot raise. The child stays in the driver's process group, so the outer deadline's kill
reaches it. The inherited Lean search paths are removed, so a Lake command resolves modules only
through the workspace it runs in. `LAKE_ARTIFACT_CACHE` is `false`, so Lake's artifact cache is
off for each package whose own configuration does not turn it on: a module that Lake restores from
that cache replays no warning, so `lake build --wfail` would not see it. Each variable of the
command's `env` is set before `isolation`, the shared Git isolation (`isolationEnvironment`), which
every command receives last, so the Git commands that Lake starts for it, and those of the programs
it runs, inherit it. A Git command also selects command-scope `core.symlinks=false` on its command
line; no Git policy is duplicated here. Process execution and signal delivery remain trusted. -/
def start (isolation : Array (String × Option String)) (command : Command) :
    BaseIO (Option (IO.Process.Child stdio)) := do
  announce s!"start {command.display}"
  let spawn : IO (IO.Process.Child stdio) := do
    let isolated := if command.program == "git" then
        {command with args := #["-c", "core.symlinks=false"] ++ command.args}
      else command
    let (program, args) := (isolated.program, isolated.args)
    let env := #[("GHCR_TOKEN", none), ("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
      ("LAKE_ARTIFACT_CACHE", some "false")] ++
      command.env.map (fun (name, value) => (name, some value)) ++ isolation
    IO.Process.spawn { stdio with cmd := program, args, cwd := some command.dir, env }
  match ← spawn.toBaseIO with
  | .ok child => return some child
  | .error error =>
      announce s!"could not start {command.display}: {error}"
      return none

/-- Wait for a started command and return how it ended. It cannot raise: a wait that fails is
reported and gives no observed end. -/
def await (command : Command) (child : IO.Process.Child stdio) : BaseIO (Option UInt32) := do
  match ← child.wait.toBaseIO with
  | .ok status => return some status
  | .error error =>
      announce s!"could not wait for {command.display}: {error}"
      return none

/-- Run one command to its end and return how it ended. It cannot raise. -/
def execute (isolation : Array (String × Option String)) (command : Command) :
    BaseIO (Option UInt32) := do
  let started ← IO.monoMsNow
  let some child ← start isolation command | return none
  let ended ← await command child
  let seconds := ((← IO.monoMsNow) - started) / 1000
  if passed [ended] then announce s!"done in {seconds} s: {command.display}"
  else announce s!"failed in {seconds} s ({describe ended}): {command.display}"
  return ended

/-- Run `commands` one after another and return how each ended. A command
runs only while everything that has ended so far passed: `known` holds the ends known before it.
A command after a failure is not run and has no end. It cannot raise. -/
def executeInOrder (isolation : Array (String × Option String)) :
    (known : List (Option UInt32)) →
    (commands : List Command) → BaseIO (Ends commands)
  | _, [] => return ⟨[], rfl⟩
  | known, command :: rest => do
      let ended ← if passed known then execute isolation command else pure none
      let later ← executeInOrder isolation (ended :: known) rest
      return ⟨(command, ended) :: later.ends, by simp [later.complete]⟩

/-! ## The place the driver removes

The driver removes one kind of directory: the scratch directory of the copy it made (`Copy.remove`),
or of a run that died (`reclaim`), each below its own scratch area. `IO.FS.removeDirAll` reads the
entries of the path it is given, also when that path is a symbolic link to a directory, and then
removes the entries of the link's target. So the driver removes a directory only after `removal`
decided it from an observation that follows no link at the path.

**Outside this decision:** a process that replaces an entry below the directory with a link
while the removal runs. `IO.FS.removeDirAll` examines each entry and then opens it by its path,
so such a process can make it remove the entries of a different directory. -/

/-- What is at a path, observed without following a symbolic link at the path itself. -/
inductive Place where
  /-- Nothing is there. -/
  | absent
  /-- A directory is there. -/
  | directory
  /-- Something else is there: a symbolic link, a file, or a different kind of entry. -/
  | other
  deriving DecidableEq, Repr

/-- What the driver observed of a path before it removes the directory there. -/
structure Observed where
  /-- What is at the path. -/
  place : Place
  /-- Whether a directory is there and its real path is the path itself (`observe`). -/
  sameLocation : Bool
  deriving DecidableEq, Repr

/-- What the driver does about a directory it is to remove. -/
inductive Removal where
  /-- Nothing is there: there is nothing to remove. -/
  | nothing
  /-- A directory is there, at its own place: the driver removes it. -/
  | remove
  /-- Something else is there: the driver removes nothing and stops. -/
  | refuse
  deriving DecidableEq, Repr

/-- The driver removes only a directory at its own place; it has nothing to remove when nothing
is there; and it refuses in every other case, which is each case with a symbolic link at the
path. -/
def removal (observed : Observed) : Removal :=
  match observed.place with
  | .absent => .nothing
  | .directory => if observed.sameLocation then .remove else .refuse
  | .other => .refuse

/-- The driver removes exactly when a directory is at the path and its real path is that path. -/
theorem removal_remove_iff (observed : Observed) :
    removal observed = .remove ↔ observed.place = .directory ∧ observed.sameLocation = true := by
  obtain ⟨place, sameLocation⟩ := observed
  cases place <;> cases sameLocation <;> simp [removal]

/-- The driver has nothing to remove exactly when nothing is at the path. -/
theorem removal_nothing_iff (observed : Observed) :
    removal observed = .nothing ↔ observed.place = .absent := by
  obtain ⟨place, sameLocation⟩ := observed
  cases place <;> cases sameLocation <;> simp [removal]

/-- The metadata of the entry at `path`, by a read that does not follow a symbolic link at `path`
itself: `System.FilePath.symlinkMetadata`, refused on Windows, where that function of Lean 4.35.0
follows such a link. -/
def entryMetadata (path : System.FilePath) : IO IO.FS.Metadata :=
  if System.Platform.isWindows then
    throw <| IO.userError s!"lstat {path}: refused on Windows, where Lean 4.35.0's \
      System.FilePath.symlinkMetadata follows a symbolic link at the path"
  else path.symlinkMetadata

/-- What is at `path`, by a read that does not follow a symbolic link at `path` itself
(`entryMetadata`). -/
def place (path : System.FilePath) : IO Place := do
  match ← (entryMetadata path).toBaseIO with
  | .ok metadata => return if metadata.type == .dir then .directory else .other
  | .error (.noFileOrDirectory ..) => return .absent
  | .error error => throw error

/-- Remove the directory at `path`. A caller must give the proof that `removal` decided to remove
it, so no call exists for a path that `removal` refused or found empty. -/
def removeDecided (path : System.FilePath) (observed : Observed)
    (_decided : removal observed = .remove) : IO Unit :=
  IO.FS.removeDirAll path

/-- What the driver observes of `path` before a removal: what is there, by a read that follows
no link at the path, and, when a directory is there, whether its real path is the path. Only
`place` decides that nothing is there: a failure of either read is thrown, since Lean 4.35.0's
`realPath` gives `noFileOrDirectory` for each failure of `realpath(3)`
(https://github.com/rbeauchamp/regula/issues/430). `removal` reads `sameLocation` only for a
directory. -/
def observe (path : System.FilePath) : IO Observed := do
  let place ← place path
  let sameLocation ← match place with
    | .directory => pure ((← IO.FS.realPath path) == path)
    | .absent | .other => pure false
  return { place, sameLocation }

/-- Remove the directory at `path` when one is there at its own place, do nothing when nothing
is there, and stop with nothing removed when a symbolic link or a file is there
(`removal_remove_iff`). `path` must have no symbolic link at a component above its last one: its
callers give a path below a real path. That no process changes the path between the observation
and the removal is trusted. -/
def removeOwn (path : System.FilePath) : IO Unit := do
  let observed ← observe path
  match decided : removal observed with
  | .nothing => pure ()
  | .remove => removeDecided path observed decided
  | .refuse =>
      throw <| IO.userError s!"nothing was removed: {path} is not a directory at its own place \
        (a symbolic link or a file is there)"

/-! ## The copy of the first acceptance step

The first acceptance step makes its builds in a private copy of the project, and its last command
runs the checker (`lake lint`) on the build of that copy. The checker writes no file, and this
driver is the only process of the step that runs before any project artifact exists, so it makes
the copy.

The copy is in a new scratch directory of the scratch area below the project's `.lake`: the
reclamation of the marked directories when no scratch owner lives, an ownership marker beside the
directory, and a shared lock on the area's lock file for as long as the copy is in use. So a first
step that starts while no other scratch owner of the checkout lives leaves no scratch directory of a
run that died before it, when each removal succeeds, and it removes its own at its end. A removal that
fails is reported with its path and does not fail the step. So the build output of the copy holds only
what the commands of this step made, the build reads files that no other process is given, and the
step removes nothing of the checkout. The acceptance gate cannot observe that this driver made the
copy new in this run; that statement rests on `makeCopy`. -/


/-- Construct the cold copy before any prebuild through the shared no-follow/exclusive routine.
The bootstrap wrapper only supplies its main entrypoint. Its regular-file receipt identifies the
files the same constructor emitted. `Construction.projectRelative` owns ordinary source selection;
`Construction.sourceMain` also retains the original Markdown domain and reserves the root `.lake`.
Regular files use 0644. The driver runs freshly built programs, whose executable modes Lake sets. -/
def copyTree (root target : System.FilePath) : IO (List String) := do
  let some parent := target.parent | throw <| IO.userError "copy target has no parent"
  let wrapper := parent / "regula-copy.lean"
  let handle ← IO.FS.Handle.mk wrapper .writeNew
  handle.putStr (constructionSource ++ "\n/-- Cold construction entrypoint. -/\n" ++
    "def main := Regula.Filesystem.Construction.sourceMain\n")
  handle.flush
  let result ← IO.Process.output {
    cmd := ((← Lean.getBuildDir) / "bin/lean").toString
    args := #["--run", wrapper.toString, "project", root.toString, target.toString]
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
  IO.FS.removeFile wrapper
  unless result.exitCode == 0 do
    throw <| IO.userError s!"project construction failed: {result.stdout}{result.stderr}"
  let json ← IO.ofExcept (Lean.Json.parse result.stdout)
  IO.ofExcept (Lean.fromJson? json)

/-- The copy of the project that the first acceptance step builds and audits. -/
structure Copy where
  /-- The scratch directory that holds the copy, by its real path. -/
  scratch : System.FilePath
  /-- The ownership marker beside the scratch directory. -/
  marker : System.FilePath
  /-- The root of the copy: the directory `project` of the scratch directory. -/
  project : System.FilePath
  /-- The pending acceptance record of this run, in the scratch directory beside the copy. Only
  this run has the path: the scratch directory has a new name and is created by a call that
  fails when the name exists, and the record by one that fails when the file exists. This run
  writes it (`Copy.record`) and promotes it (`run`). A record that no run promoted is removed with
  its scratch directory, by this run or by a reclamation. -/
  pending : System.FilePath
  /-- The handle that holds the shared lock of the scratch area while the copy is in use. -/
  lock : IO.FS.Handle
  /-- Each file `copyTree` wrote, by its path below `project` written with `/`. -/
  files : List String

/-- Remove each marked scratch directory of `area`, then its marker. The caller holds the lock of the
area exclusively, so no owner of a scratch directory lives, and each marked directory is one of a run
that ended without its removal. A marker counts only when it is a regular file. Its directory is
that ended without its removal. A marker counts only when it is a regular file. Its directory is
removed only as `removal` decides, a marker with no directory is removed, and with anything
else at the directory's place nothing is removed. It cannot raise: a removal that fails, or a
scratch area that cannot be read, is reported with its path and is no error of the step, and
that directory then stays. -/
def reclaim (area : System.FilePath) : BaseIO Unit := do
  let all : IO Unit := do
    for entry in ← listDirectory area do
      unless entry.path.extension == some "owner" do continue
      let some name := entry.path.fileStem | continue
      let path := area / name
      let one : IO Unit := do
        unless (← entryMetadata entry.path).type == .file do return
        let observed ← observe path
        match decided : removal observed with
        | .remove =>
            removeDecided path observed decided
            IO.FS.removeFile entry.path
            announce s!"removed the scratch directory {path} of a run that ended without \
              removing it"
        | .nothing => IO.FS.removeFile entry.path
        | .refuse => pure ()
      if let .error error ← one.toBaseIO then
        announce s!"could not remove the scratch directory {path}, which stays: {error}"
  if let .error error ← all.toBaseIO then
    announce s!"could not read the scratch area {area} for its reclamation: {error}"

/-- Make the copy of the project at the real path `root`. When the lock of Regula's scratch area can
be taken exclusively, no scratch owner lives, and the marked directories are removed first
(`reclaim`). Then: take the shared lock of the area, create the ownership marker of a new name
exclusively, create the directory of that name, which must not exist, and copy the project into
its directory `project` (`copyTree`). So the reclamation of a later driver removes the directory of a
driver that died, and removes none while this driver holds the lock.
The copy reserves an empty root `.lake`, excluding the original root's default build state.

After a reclamation the exclusive lock is converted to the shared one without an `unlock`
between them. Safety does not depend on the conversion: `flock(2)` does
not promise that it is atomic, but nothing is created before the shared lock is held, so a
window without a lock is one that a release would open too. The conversion is for progress only,
and the operating-system behaviour it relies on is trusted, not proved: XNU's release of a
`flock` lock wakes only its first waiter and moves the others onto that waiter's lock, while a
downgrade by the holder wakes every waiter, and Linux wakes every waiter in both cases. On
Windows Lean's lock is `LockFileEx`, which stacks a shared lock over the held exclusive one on the
same handle instead of converting it, so there the lock is released first. -/
def makeCopy (root : System.FilePath) : IO Copy := do
  IO.FS.createDirAll (root / ".lake" / "regula-scratch")
  let area ← IO.FS.realPath (root / ".lake" / "regula-scratch")
  let lock ← IO.FS.Handle.mk (area / ".lock") .append
  if ← lock.tryLock then
    reclaim area
    if System.Platform.isWindows then lock.unlock
  lock.lock (exclusive := false)
  let random := (← IO.getRandomBytes 8).foldl (fun value byte => value * 256 + byte.toNat) 0
  let name := s!"acceptance-{← IO.Process.getPID}-{← IO.monoNanosNow}-{random}"
  let scratch := area / name
  let marker := area / s!"{name}.owner"
  unless (← place scratch) == .absent do
    throw <| IO.userError s!"refusing to reuse scratch path {scratch}"
  discard <| IO.FS.Handle.mk marker .writeNew
  IO.FS.createDir scratch
  let project := scratch / "project"
  let files ← copyTree root project
  let pending := scratch / "acceptance-link.pending.json"
  let record ← IO.FS.Handle.mk pending .writeNew
  record.putStr incompleteLink
  record.flush
  return { scratch, marker, project, pending, lock, files }

/-- Give the build output of the copy to the project at `root`, when the project has none:
rename the copy's `.lake/build` to the project's, only when nothing is at that place by a read
that follows no link. A project with build output, or with anything else at that place, keeps
it. The rename is in one file system, deletes nothing, and does not follow a link at its target.
It returns whether it renamed. A rename that fails is reported and is no error of the step: the
documentation step then builds what it needs in the checkout, where Lake decides from its traces
what to build again. -/
def Copy.adopt (copy : Copy) (root : System.FilePath) : BaseIO Bool := do
  let made := copy.project / ".lake" / "build"
  let target := root / ".lake" / "build"
  let rename : IO Bool := do
    unless (← place target) == .absent && (← place made) == .directory do return false
    IO.FS.rename made target
    return true
  match ← rename.toBaseIO with
  | .ok true =>
      announce s!"the project had no build output: moved the copy's to {target}"
      return true
  | .ok false =>
      announce s!"the build output at {target} stays as it is"
      return false
  | .error error =>
      announce s!"could not move the copy's build output to {target}: {error}"
      return false

/-- The SHA-256 of each of `paths`, each relative to `dir` and written with `/`, by the external
`shasum -a 256` run in `dir` on at most 200 paths at a time, each given as `./` and the path, since
`shasum` reads standard input for the operand `-`; for each file it prints the digest, two spaces
and the operand, and any other line in a path's place fails. The output of
`shasum` that it reads is trusted. -/
def digests (dir : System.FilePath) (paths : List String) : IO (List (String × String)) := do
  let batches := paths.foldl (fun (batches : Array (Array String)) path =>
    match batches.back? with
    | some last => if last.size < 200 then batches.pop.push (last.push path)
        else batches.push #[path]
    | none => #[#[path]]) #[]
  let mut result := #[]
  for batch in batches do
    let run ← IO.Process.output
      { cmd := "shasum", args := #["-a", "256", "--"] ++ batch.map ("./" ++ ·), cwd := some dir }
    let lines := (run.stdout.splitOn "\n").filter (!·.isEmpty)
    unless run.exitCode == 0 && lines.length == batch.size do
      throw <| IO.userError s!"shasum gave no digest of each file: {run.stdout}{run.stderr}"
    for (path, line) in batch.toList.zip lines do
      let digest := (line.take 64).toString
      unless digest.length == 64 && digest.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) &&
          line == digest ++ "  ./" ++ path do
        throw <| IO.userError s!"shasum gave an unexpected line for {path}: {line}"
      result := result.push (path, digest)
  return result.toList

/-! ## The link between the two acceptance steps

The first step records the content identity of the files it accepted: the SHA-256 of each file of
its copy, taken before any command ran in it, by its path (`identity`). The copy holds each file
that the copy construction selects (`Construction.projectRelative`): the root package's sources
and configuration, the documents, and the sources of the other packages of the repository. The
documentation step takes the same identity of the checkout, by a copy made the same way, and
refuses unless it equals the recorded one, before its first command and again after its last
(`requireLink`). So the documentation step checks the inputs that the first step accepted. That
`shasum` and the filesystem report the files' contents is trusted, as is that no other process
writes the record. -/

/-- The content identity of a copy: the SHA-256 of each file `copyTree` wrote, by its path. -/
def identity (copy : Copy) : IO (List (String × String)) :=
  digests copy.project copy.files

/-- The accepted record of the identity `tree`. -/
def acceptedValue (tree : List (String × String)) : Lean.Json :=
  Lean.Json.mkObj [("schemaVersion", Lean.toJson (1 : Nat)),
    ("status", Lean.Json.str "accepted"), ("identity", Lean.toJson tree)]

/-- The text of the accepted record of the identity `tree` (`acceptedValue`), which
`Copy.record` writes. -/
def acceptedRecord (tree : List (String × String)) : String :=
  (acceptedValue tree).compress ++ "\n"

/-- Write the accepted record of `tree` (`acceptedRecord`) in the copy's pending record, beside it
and then renamed over it, so a failure leaves the pending record incomplete. -/
def Copy.record (copy : Copy) (tree : List (String × String)) : IO Unit := do
  let written := copy.scratch / "acceptance-link.accepted.json"
  IO.FS.writeFile written (acceptedRecord tree)
  IO.FS.rename written copy.pending

/-- Whether the accepted record `value` records the identity `tree`. -/
def linked (value : Lean.Json) (tree : List (String × String)) : Bool :=
  (value.getObjValAs? Nat "schemaVersion").toOption == some 1 &&
    (value.getObjValAs? String "status").toOption == some "accepted" &&
    (value.getObjValAs? (List (String × String)) "identity").toOption == some tree

/-- Remove the copy: its scratch directory, then its marker, then the lock. The directory is removed
only as `removeOwn` decides. A failure is reported and is no error of the step: a later reclamation
removes the directory (`reclaim`). -/
def Copy.remove (copy : Copy) : BaseIO Unit := do
  let remove : IO Unit := do
    removeOwn copy.scratch
    IO.FS.removeFile copy.marker
    copy.lock.unlock
  if let .error error ← remove.toBaseIO then
    announce s!"could not remove the copy {copy.scratch}: {error}"

/-- Refuse unless the record at `linkPath` is an accepted record of the identity of a copy of the
checkout at `root`, made and removed here. -/
def requireLink (root : System.FilePath) : IO Unit := do
  let copy ← makeCopy root
  let tree ← try identity copy finally copy.remove
  let text ← try IO.FS.readFile linkPath catch error =>
    throw <| IO.userError s!"acceptance link missing: run ordinary acceptance first ({error})"
  let value ← IO.ofExcept (Lean.Json.parse text)
  unless linked value tree do
    throw <| IO.userError s!"the acceptance link {linkPath} does not record these inputs: run \
      ordinary acceptance on them first"
  announce s!"acceptance link: the {tree.length} files the copy construction selects equal the \
    accepted ordinary inputs"

/-! ## The file of the link

The driver writes one file, at one fixed path in the project's `tmp` directory (`linkPath`): its
mark (`incompleteLink`, by `writeLink`) and the accepted record (by `promote`). Each makes the record
beside the path or in the scratch directory and renames it there, so a reader reads the earlier file
or the whole new one. The file beside the path is new by exclusive creation, which fails on anything
at its name, so that write follows no symbolic link and changes no other file. `rename(2)` follows
no symbolic link at its target, so a link at `linkPath` is replaced and its target keeps its bytes,
and it fails on a directory there, which stops the step. `tmp` being a symbolic link is a choice of
whoever made it, and the driver writes through it. -/

/-- Write `text` at `path`: make a new file beside it by exclusive creation, which fails when
anything, a symbolic link included, is at that name, write and flush it, and rename it over `path`.
Its name holds the process id and random bytes, so a file that a killed run left does not stop a
later run. A failure before the rename leaves `path` as it was and removes nothing. A reader reads
the earlier file or the whole new one. -/
def writeLink (path : System.FilePath) (text : String) : IO Unit := do
  if let some directory := path.parent then IO.FS.createDirAll directory
  let random := (← IO.getRandomBytes 8).foldl (fun value byte => value * 256 + byte.toNat) 0
  let pending : System.FilePath := s!"{path}.{← IO.Process.getPID}.{random}.pending"
  let handle ← IO.FS.Handle.mk pending .writeNew
  handle.putStr text
  handle.flush
  IO.FS.rename pending path

/-- Rename the file at `source`, a record that only this run has the path of, to `path`. -/
def promote (source path : System.FilePath) : IO Unit := do
  if let some directory := path.parent then IO.FS.createDirAll directory
  IO.FS.rename source path

/-- The failure report: each command that did not end with exit status 0, with how it ended. -/
def report (ends : List (Command × Option UInt32)) : String :=
  "\n".intercalate ("verification failed:" :: ends.filterMap fun (command, ended) =>
    if passed [ended] then none else some s!"  {command.display}: {describe ended}")

private def usage : String :=
  "usage: scripts/verify.sh [docs | site]"

/-- The earlier verdicts an attempt of `mode` invalidates, each with the constant text recording it
as incomplete. Ordinary acceptance invalidates the accepted link, so it is not accepted from then on
unless a run records the identity of its own copy in it. -/
def invalidated : Mode → List (String × String)
  | .ordinary => [(linkPath, incompleteLink)]
  | _ => []

/-- The manifest and package overrides file of the workspace that Lake loads with the package at
`dir` as its root, joined as Lake joins paths.

Assumes:
- Lake v4.35.0 gives the root package of a workspace the manifest `lake-manifest.json` of its
  directory unless its load configuration names another (`Lake/Load/Config.lean:54`,
  `Lake/Load/Package.lean:35-51`), and the `lake` command names no other
  (`Lake/CLI/Main.lean:131-145`). It reads the package overrides file
  `.lake/package-overrides.json` of that directory (`Lake/Config/Workspace.lean:212-213`,
  `Lake/Config/Package.lean:208-213`). -/
def rootFiles (dir : System.FilePath) : System.FilePath × System.FilePath :=
  (Lake.joinRelative dir Lake.defaultManifestFile,
    Lake.joinRelative (Lake.joinRelative dir Lake.defaultLakeDir) "package-overrides.json")

/-- The manifest of the workspace whose manifest and package overrides file are `files`
(`rootFiles`), and the entries of that overrides file, each read by Lake's own reader, or `none`
when the manifest does not exist; any other failure of a read, and a file that Lake's reader
refuses, are thrown.

Assumes:
- Lake v4.35.0's load reads the manifest with `Lake.Manifest.load?`
  (`Lake/Load/Workspace.lean:61-69`) and the overrides file with `Lake.Manifest.tryLoadEntries`
  (`Lake/Load/Resolve.lean:603`), which give nothing only for an absent file
  (`Lake/Load/Manifest.lean:272-276`, `:305-309`). -/
def readRoot (files : System.FilePath × System.FilePath) :
    IO (Option (Lake.Manifest × Array Lake.PackageEntry)) := do
  let some manifest ← Lake.Manifest.load? files.1 | return none
  return some (manifest, ← Lake.Manifest.tryLoadEntries files.2)

/-- The package adopters require stays dependency-free: `read`, the root package's manifest and
the entries of its package overrides file (`readRoot`), is there, and neither records a package.
Lake materializes a workspace's dependencies from those entries, and refuses a configuration that
requires a package when they are none, so an accepted build of the root package requires nothing.
Requiring `regula` then adds only `regula` to an adopter's `lake-manifest.json`. An absent manifest
is refused: Lake would resolve the requirements anew.

Assumes:
- Lake v4.35.0 materializes the dependencies of a workspace with a manifest from the manifest's
  entries and then the overrides file's, and refuses one whose configuration requires a package
  when both record none (`Lake/Load/Workspace.lean:61-69`, `Lake/Load/Resolve.lean:599-609`). -/
def dependencyFree : Option (Lake.Manifest × Array Lake.PackageEntry) → Bool
  | some (manifest, overrides) => manifest.packages.isEmpty && overrides.isEmpty
  | none => false

/-- `dependencyFree` accepts exactly a manifest that records no package with an overrides file
that records none. -/
theorem dependencyFree_iff (read : Option (Lake.Manifest × Array Lake.PackageEntry)) :
    dependencyFree read = true ↔
      ∃ manifest, read = some (manifest, #[]) ∧ manifest.packages = #[] := by
  match read with
  | none => simp [dependencyFree]
  | some (manifest, overrides) =>
    simp only [dependencyFree, Bool.and_eq_true, Array.isEmpty_iff, Option.some.injEq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hPackages, hOverrides⟩
      exact ⟨manifest, ⟨rfl, hOverrides⟩, hPackages⟩
    · rintro ⟨_, ⟨rfl, hOverrides⟩, hPackages⟩
      exact ⟨hPackages, hOverrides⟩

/-- The targets a surface manifest claims, read from its JSON: each surface's `library` and each
name of its `executables`, in the manifest's order; `none` for a manifest without that shape. A
surface without `executables` claims none; one with a field of another shape gives `none`. -/
def claimedTargets (manifest : Lean.Json) : Option (List String) := do
  let surfaces ← (manifest.getObjValAs? (Array Lean.Json) "surfaces").toOption
  let named ← surfaces.toList.mapM fun surface => do
    let library ← (surface.getObjValAs? String "library").toOption
    let executables ← match surface.getObjVal? "executables" with
      | .error _ => pure #[]
      | .ok value => (Lean.fromJson? value : Except String (Array String)).toOption
    pure (library :: executables.toList)
  pure named.flatten

/-- Whether the first acceptance step builds every target the surface manifest claims
(`buildCovers_iff`). The step's checker reads the build of the claimed targets and refuses a
module without its `.olean`, so a claimed target the step does not build would make it incomplete
rather than checked; the driver refuses the step at once when this is `false`. -/
def buildCovers (manifest : Lean.Json) : Bool :=
  match claimedTargets manifest with
  | some targets => targets.all surfaceTargets.contains
  | none => false

/-- `buildCovers` accepts exactly a manifest of the shape `claimedTargets` reads all of whose
claimed targets are targets of the step's build. -/
theorem buildCovers_iff (manifest : Lean.Json) :
    buildCovers manifest = true ↔
      ∃ targets, claimedTargets manifest = some targets ∧
        ∀ target ∈ targets, target ∈ surfaceTargets := by
  unfold buildCovers
  split
  · next targets h => simp [h, List.all_eq_true]
  · next h => simp [h]

/-- Begin an attempt: invalidate the selected mode's earlier accepted link (`invalidated`), by a new
file renamed over it (`writeLink`). `scripts/verify.sh` runs this toolchain-only step before
provisioning and before any checker is built, so a failed setup or build cannot leave it in place.
With arguments of no mode it stops with the usage.

An attempt that stops before this step, such as one with no `lean` to run, has run no code of its
own and leaves the earlier verdicts of its mode.
Assumes: `requireLink` admits the acceptance link (`linkPath`) only when it records the identity of
the current inputs, so it is the verdict for those inputs. -/
def beginAttempt (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  for (path, text) in invalidated selection.val do
    writeLink path text

/-- Cold-start driver; all builds and checks stay within the inherited outer deadline. After the
preliminary checks it runs the commands of the mode one after another, starts one only while every
end known so far passed, and reports success only when `passed` accepts how every one of them
ended (`passed_covers`). The first acceptance step refuses a surface manifest that claims a target
its build does not build (`buildCovers`), makes its copy after the preliminary checks
(`makeCopy`), takes the copy's identity before any command runs in it (`identity`), runs its
commands for that copy (`ordinary_places`), and only when every command passed records that
identity (`Copy.record`) and moves the record to `linkPath` (`promote`), before the removal of its
copy and before the success line, and only when the file at `linkPath` is one that the run may
replace. It gives the copy's build output to a project that has none when the step passed
(`Copy.adopt`), and removes the copy in each case (`Copy.remove`). The documentation step
requires the link before its first command and again after its last (`requireLink`). The driver
obtains the Git isolation once, before its first command (`isolationEnvironment`), and starts every
command under it (`start`). -/
def run (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  if selection.val == .ordinary then
    unless dependencyFree (← readRoot (rootFiles ".")) do
      throw <| IO.userError "lake-manifest.json is absent or records a dependency, or \
        .lake/package-overrides.json records one: the regula package must require nothing beyond \
        the Lean toolchain"
    let surfaces ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "foundation_manifest.json"))
    unless buildCovers surfaces do
      throw <| IO.userError s!"foundation_manifest.json claims a target that the first \
        acceptance step does not build, or its surfaces cannot be read; add it to \
        RegulaVerification.surfaceTargets (the step builds {surfaceTargets})"
  let isolation ← isolationEnvironment
  let early ← executeInOrder isolation []
    [({ program := "git", args := #["diff", "--check"] } : Command),
      { program := "git", args := #["diff", "--cached", "--check"] },
      { program := "shellcheck", args := #["scripts/verify.sh", "scripts/provision.sh"] }]
  let root ← IO.FS.realPath "."
  if selection.val == .docs && passed early.statuses then requireLink root
  let copy ← if selection.val == .ordinary && passed early.statuses then
      some <$> makeCopy root
    else pure none
  try
    -- The identity of the copy's files, before any command runs in it.
    let tree ← copy.mapM identity
    let place := (copy.map (·.project.toString)).getD "."
    let ran ← executeInOrder isolation early.statuses (commands place selection.val)
    let all := early.append ran
    if let some copy := copy then
      if let some tree := tree then
        -- The record is in the scratch directory of the copy, so the promotion is before the
        -- removal of the copy, which follows in each case.
        if passed all.statuses then
          discard <| copy.adopt root
          copy.record tree
          promote copy.pending linkPath
          announce s!"every command exited 0: recorded the identity of {tree.length} files in \
            {linkPath}"
    unless passed all.statuses do
      throw <| IO.userError (report all.ends)
  finally
    if let some copy := copy then copy.remove
  if selection.val == .docs then requireLink root
  IO.println (match selection.val with
    | .ordinary => "local verification: PASS (ordinary mechanical acceptance commands completed, \
      Lean's kernel replayed the export of the copy's default targets (`lake check`), Regula's \
      checker passed on the copy's build; semantic review is separate; run \
      `scripts/verify.sh docs` for documentation)"
    | .docs => "documentation verification: PASS (every rule ID in the prose md4c reads in each \
      tracked Markdown document links to its rule page; CONTEXT.md is the print of a vocabulary \
      whose source paths are tracked files, and the controls of that check gave the expected \
      results; the example package in audit/ built, passed Lean's kernel replay and passed \
      Regula's checker; the Verso standard built, every lean block elaborated where it is \
      written, rendered, and its anchors, checklist rows and rule-ID links checked; inputs equal \
      the accepted ordinary inputs before and after)"
    | .site => "site build and check: PASS (rule-reference artifact in _site; separate from \
      acceptance; publication is verified after deployment)")

/-- The cold-start entry point. `lean/RegulaVerification.lean`, the launcher that the timed
`scripts/verify.sh` runs with `lean --run`, runs the source of this module with `main` bound to
it. `scripts/verify.sh` first runs it with the private `--begin-attempt` protocol flag, before
setup. -/
def entry : List String → IO Unit
  | "--begin-attempt" :: args => beginAttempt args
  | args => run args

end RegulaVerification
