import Lean

/-! # Cold-start verification driver

Cold-start verification plan and operational interpreter. This module imports only
the pinned toolchain, so it can run before any root-package artifacts exist. Argument
selection has soundness and round-trip proofs; the interpreter consumes its proof-bearing
selection. Recipes name Lake targets, not a source-file census. The interpreter runs the
commands of the selected recipe one after another, starts a command only while every end known
so far passed, and reports success only when `passed` accepts how each command ended
(`passed_covers`). The first acceptance step makes its one build in a private copy of the
project that this driver makes, and the acceptance gate audits that copy (`makeCopy`).
Process effects remain trusted IO under the shell's single 420-second process-group deadline. -/
namespace RegulaVerification

/-- Closed vocabulary of supported verification invocations. -/
inductive Mode where
  /-- No argument: the first acceptance step, which makes a private copy of the project, builds
  the acceptance executables and the claimed surfaces of the root package there, runs the
  registry checks and combined qualification, and audits those surfaces in that copy. -/
  | ordinary
  /-- `docs`: the second acceptance step: the rule-ID check of every tracked Markdown document,
  the checks C1 to C8 of their prose with the baseline (checks B1 and B2, of which B2 reads the
  Git history) and the check of the vocabulary `CONTEXT.md` (check C9), with the controls of
  these checks, the fresh acceptance of the `audit/` package whose modules the standard's
  examples import, then
  the documentation audit and the Verso standard's build and render, refused unless its inputs
  have the content identity the first step recorded. -/
  | docs
  /-- `serialized-graph`: the separate serialized-graph check (`freshChecker`). -/
  | graph
  /-- `diagnostics`: the checker self-test diagnostic, not acceptance. -/
  | diagnostics
  /-- `diagnostics fixtures`: the self-test's fixtures partition. -/
  | fixtures
  /-- `diagnostics structural`: the self-test's structural partition. -/
  | structural
  /-- `diagnostics execution`: the self-test's execution partition. -/
  | execution
  /-- `diagnostics structural 1/2`: the first of the structural partition's two shards. -/
  | structuralFirst
  /-- `diagnostics structural 2/2`: the second of the structural partition's two shards. -/
  | structuralSecond
  /-- `diagnostics execution 1/2`: the first of the execution partition's two shards. -/
  | executionFirst
  /-- `diagnostics execution 2/2`: the second of the execution partition's two shards. -/
  | executionSecond
  /-- `diagnostics cli`: the self-test's command-line partition. -/
  | cli
  /-- `diagnostics environments`: the self-test's environments partition. -/
  | environments
  /-- `diagnostics build-policy`: the self-test's build-policy partition. -/
  | buildPolicy
  /-- `diagnostics lint-driver`: the self-test's `lake lint` driver partition. -/
  | lintDriver
  /-- `diagnostics producers`: the producers qualification campaign. -/
  | producers
  /-- `diagnostics history`: the history qualification campaign. -/
  | history
  /-- `diagnostics self-lint`: this repository's own `lake lint`. -/
  | selfLint
  /-- `diagnostics self-audit`: the operational self-audit of the excluded `Regula` library. -/
  | selfAudit
  /-- `diagnostics rule-examples`: the whole rule-example corpus in one run. -/
  | ruleExamples
  /-- `diagnostics rule-examples 1/2`: the first of the corpus's two shards. -/
  | ruleExamplesFirst
  /-- `diagnostics rule-examples 2/2`: the second of the corpus's two shards. -/
  | ruleExamplesSecond
  /-- `site`: build and check the rule-reference site artifact from the shards' evidence. -/
  | site
  /-- `mathlib`: the separate Mathlib integration check, never part of acceptance: the fresh
  acceptance and the lint of the Mathlib integration package, whose pinned Mathlib
  `lean --run lean/RegulaProvision.lean mathlib` provisions beforehand. It refuses a copy the
  check does not apply to (`RegulaProvision.mathlibApplies`) instead of reporting a pass. -/
  | mathlib
  deriving DecidableEq

/-- Exactly the documented arguments for each mode, with no ignored trailing arguments. -/
def arguments : Mode → List String
  | .ordinary => []
  | .docs => ["docs"]
  | .graph => ["serialized-graph"]
  | .diagnostics => ["diagnostics"]
  | .fixtures => ["diagnostics", "fixtures"]
  | .structural => ["diagnostics", "structural"]
  | .execution => ["diagnostics", "execution"]
  | .structuralFirst => ["diagnostics", "structural", "1/2"]
  | .structuralSecond => ["diagnostics", "structural", "2/2"]
  | .executionFirst => ["diagnostics", "execution", "1/2"]
  | .executionSecond => ["diagnostics", "execution", "2/2"]
  | .cli => ["diagnostics", "cli"]
  | .environments => ["diagnostics", "environments"]
  | .buildPolicy => ["diagnostics", "build-policy"]
  | .lintDriver => ["diagnostics", "lint-driver"]
  | .producers => ["diagnostics", "producers"]
  | .history => ["diagnostics", "history"]
  | .selfLint => ["diagnostics", "self-lint"]
  | .selfAudit => ["diagnostics", "self-audit"]
  | .ruleExamples => ["diagnostics", "rule-examples"]
  | .ruleExamplesFirst => ["diagnostics", "rule-examples", "1/2"]
  | .ruleExamplesSecond => ["diagnostics", "rule-examples", "2/2"]
  | .site => ["site"]
  | .mathlib => ["mathlib"]

/-- Every supported mode occurs once; the parser searches only this closed vocabulary. -/
def modes : List Mode := [.ordinary, .docs, .graph, .diagnostics, .fixtures, .structural,
  .execution, .structuralFirst, .structuralSecond, .executionFirst, .executionSecond, .cli,
  .environments, .buildPolicy, .lintDriver, .producers, .history, .selfLint,
  .selfAudit, .ruleExamples, .ruleExamplesFirst, .ruleExamplesSecond, .site, .mathlib]

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

private def lake (args : Array String) : Command := ⟨"lake", args, "."⟩

/-- The package of the standard's example library (`Audit`), which imports only Lean's core
libraries and adopts the root `regula` package by relative path, as an adopting project would.
Lake commands for it run in its own directory, where its workspace is the one Lake loads. -/
def auditPackage : String := "audit"

/-- The Mathlib integration package (`MathlibAudit`): a Mathlib adopter of the root `regula`
package by relative path, holding the Mathlib-specific behaviour Regula supports. Only the
`mathlib` mode runs Lake in it; no other mode loads its workspace, so no other mode needs
Mathlib. -/
def mathlibPackage : String := "integration/mathlib"

private def lakeIn (dir : String) (args : Array String) : Command := ⟨"lake", args, dir⟩

/-- Ordinary acceptance records its accepted input identity here; the separately timed
documentation step refuses unless its own identity is equal. The driver puts the record here
only after `passed` accepted every command, before it removes its copy and before the success
line (`run`), so an accepted record here means
that every command of the step exited 0. The gate of a run records the identity in the pending
record of that run (`Copy.pending`), and that record becomes this one only by that promotion, so
a run that fails or is killed before then leaves this record incomplete. -/
def linkPath : String := "tmp/acceptance-link.json"

/-- The text of an acceptance record that is not accepted. -/
def incompleteLink : String := "{\"schemaVersion\":1,\"status\":\"incomplete\"}\n"

/-- The standard's Verso source: package directory, library and its render-only executable.
Both acceptance steps capture its sources and the package inputs its check reads, including the
sources of the `audit/` package that its library needs, in the linked identity; the documentation step also builds (elaborating every `lean` block where it is
written) and renders it, requires every anchor the rule registry and the documentation link, and
requires the checklist's rows to be exactly `Regula.checklistRows`. -/
def versoStandard : String := "website:RegulaStandard:regula-standard"

/-- Evidence receipt of one rule-example shard. -/
def shardEvidence (index : Nat) : String := s!"tmp/rule-examples-{index}of2.json"

/-- The package of the Markdown checks: md4c's reader and the `regula-markdown` executable. It
requires only the md4c binding and the root package. -/
def markdownPackage : String := "markdown"

/-- The controls of the checks of Markdown prose (C1 to C8), of the vocabulary (C9) and of the
baseline (B1 and B2), relative to the Markdown package. -/
def proseControls : String := "../lean/Fixtures/ControlledProse"

/-- Rule-reference site artifact directory (the GitHub Pages upload). -/
def siteOutput : String := "_site"

/-- One of two disjoint corpus shards, selected by rule position in the corpus. -/
private def ruleExampleShard (index : Nat) : List Command := [
  lake #["build", "axiomGate", "ruleExamples", "ruleExampleQualification", "qualify"],
  lake #["exe", "qualify", "--under-deadline", "rule-examples", "--evidence", shardEvidence index,
    "--shard", s!"{index}/2"]]

/-- A checker self-test run with the `checkerSelftest` arguments `selection`. The first command
builds the self-test together with `axiomGate`, which the baseline build of every partition
names, and with the further checker executables `tools` of the selection's baseline, so Lake
schedules the jobs of these builds in one invocation; run one after the other, the gate's own
modules would start only once the self-test's last module is linked. That command selects
nothing: the self-test's baseline build still names and builds its targets, finds these built
and builds any it names that are not here. -/
private def selftest (selection : Array String) (tools : Array String := #[]) : List Command := [
  lake (#["build", "checkerSelftest", "axiomGate"] ++ tools),
  lake (#["exe", "checkerSelftest", "--build-bound"] ++ selection ++ #["--jobs", "4"])]

/-- Existing acceptance and diagnostic recipes, executed inside the outer deadline.
Qualification's private flag retains the already timed process group. `copy` is the root of the
copy that the first acceptance step builds in, and `pending` the pending record of that run,
which its gate writes (`makeCopy`); no other mode uses them. -/
def commands (copy pending : String) : Mode → List Command
  | .ordinary => [
      -- The one build of the step, in the copy, which has no build output: the acceptance
      -- executables, the modules the step type-checks, and every claimed target of the root
      -- package, which the gate then audits in this build output.
      lakeIn copy
          #["build", "RegulaPolicy", "RegulaVerification", "RegulaProvision",
              "RegulaQualification", "RegulaCore", "AuditApp", "auditApp", "axiomGate",
              "docFenceAudit", "qualify",
        "+Regula.Checker.CheckerSelftest:olean", "+Regula.Checker.FreshChecker:olean",
        "+Regula.RegistryChecks:olean", "+Regula.Linter:olean", "+Regula.Checker.LintMain:olean",
        "+Regula.Checker.RuleExamples:olean", "+Regula.Checker.RuleExampleQualificationMain:olean",
        "+Regula.Cli.Main:olean", "+Regula.Release:olean", "+Regula.DiagnosticsGate:olean"],
      lakeIn copy #["env", "lean", "--run", "lean/Regula/RegistryChecks.lean"],
      lakeIn copy #["exe", "qualify", "--under-deadline", "combined"],
      -- Last, and from the repository root: the gate of the copy audits the copy, reads the
      -- linked documents of the checkout and writes the pending record of the run (`pending`).
      lake #["-d", copy, "exe", "axiomGate", "--acceptance-link", pending, "--verso",
          versoStandard, "--driver-copy", copy]]
  | .docs => [
      lake #["build", "docFenceAudit"],
      -- The controls of the checks C1 to C9, B1 and B2: each check accepts its positive controls
      -- and refuses the others, with the exact file, line and check at the start of each
      -- refusal. The controls of the base revision of check B2, of an entry with no document
      -- (check B1) and of `--write-baseline` are repositories that the run makes with Git in a
      -- temporary directory (`markdown/MarkdownMain.lean`).
      lakeIn markdownPackage #["exe", "regula-markdown", "--controls", proseControls],
      -- Every Markdown document Git tracks, read by md4c: a rule ID in prose that is not a link
      -- to its rule page is refused. A link of the root `README.md` to the rule-reference site
      -- that is not a stable address is refused. So is a `CONTEXT.md` that is not the print of a
      -- vocabulary or that has a source path Git does not track (check C9). A finding of the
      -- checks C1 to C8 that the baseline `prose-baseline.json` does not permit is refused, and
      -- so is an entry of the baseline with no tracked Markdown document (check B1). A baseline
      -- with a new path, a larger number or a different class in relation to the base revision
      -- is refused, and so is the removal of the baseline (check B2). Check B2 reads the Git
      -- history: the base revision is the commit that the start of the run gives, in the
      -- variable `REGULA_PROSE_START` or as the merge base of `HEAD` and `origin/main`. The
      -- argument is the repository root, relative to the Markdown package.
      lakeIn markdownPackage #["exe", "regula-markdown", ".."],
      -- The `audit/` package's own fresh acceptance, as an adopter of `regula` runs it: the
      -- standard's `lean` blocks import its modules, and the linked identity below brackets the
      -- sources they need.
      lakeIn auditPackage #["exe", "axiomGate"],
      lake
          #["exe", "docFenceAudit", "--acceptance-link", linkPath, "--verso", versoStandard]]
  | .graph => [lake #["exe", "freshChecker", "--verbose"]]
  | .diagnostics => selftest #[]
  | .producers => [
      lake #["build", "axiomGate", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "producers"]]
  | .history => [
      lake #["build", "axiomGate", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "history"]]
  -- Regula on its own code base: the repository's own `lake lint` through `regula/lint` in both
  -- packages, and the operational self-audit of the excluded `Regula` library after its
  -- warning-free build.
  | .selfLint => [lake #["lint"], lakeIn auditPackage #["lint"]]
  | .selfAudit => [
      lake #["build", "Regula", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "self-audit"]]
  | .ruleExamples => [
      lake #["build", "axiomGate", "ruleExamples", "ruleExampleQualification", "qualify"],
      lake
          #["exe", "qualify", "--under-deadline", "rule-examples", "--evidence",
              "tmp/rule-examples.json"]]
  | .ruleExamplesFirst => ruleExampleShard 1
  | .ruleExamplesSecond => ruleExampleShard 2
  | .site => [
      lake #["build", "axiomGate", "ruleExampleQualification", "site"],
      lake
          (#["exe", "site", "build", "--out", siteOutput, "--evidence"] ++
              #[shardEvidence 1, shardEvidence 2])]
  -- The Mathlib integration check: the integration package's fresh acceptance and lint, as a
  -- Mathlib adopter of `regula` runs them. Its Mathlib is provisioned beforehand, as setup; the
  -- first command refuses a copy the check does not apply to (another toolchain than that package selects) and one whose Mathlib is not provisioned, so an
  -- excluded copy fails here and is never reported as passing.
  | .mathlib => [
      { program := "lean",
        args := #["--run", "lean/RegulaProvision.lean", "mathlib-applies", "--require"] },
      lakeIn mathlibPackage #["exe", "axiomGate"], lakeIn mathlibPackage #["lint"]]
  | .structural => selftest #["--partition", "structural"] #["docFenceAudit", "freshChecker"]
  -- A shard of a partition: the partition's name, then the shard after `--shard`. The first
  -- structural shard's controls run `axiomGate` alone; the second's also run the other two.
  | .structuralFirst => selftest #["--partition", "structural", "--shard", "1/2"]
  | .structuralSecond =>
      selftest #["--partition", "structural", "--shard", "2/2"] #["docFenceAudit", "freshChecker"]
  | .executionFirst => selftest #["--partition", "execution", "--shard", "1/2"]
  | .executionSecond => selftest #["--partition", "execution", "--shard", "2/2"]
  | mode => selftest (#["--partition"] ++ ((arguments mode).drop 1).toArray)

/-- Every mode schedules actual work rather than accepting an empty campaign. -/
theorem commands_nonempty (copy pending : String) (mode : Mode) :
    commands copy pending mode ≠ [] := by
  cases mode <;> simp [commands, ruleExampleShard, selftest]

/-- The first acceptance step runs its build, the registry checks and the combined qualification
in the copy, and then the gate from the repository root: the gate is last, and it is the only
command of the step that runs in the checkout. -/
theorem ordinary_places (copy pending : String) :
    (commands copy pending .ordinary).map (·.dir) = [copy, copy, copy, "."] := rfl

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

/-- The ends of two groups of commands that ran one after the other, as the ends of both. -/
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
  " ".intercalate (command.program :: command.args.toList) ++
    (if command.dir = "." then "" else s!" (in {command.dir})")

/-- An end as the progress lines and the failure report show it. No end has one label for its
three causes: the command was not run after an earlier failure, could not be started, or its end
could not be observed. A `could not start` or `could not wait` line names the last two. -/
def describe : Option UInt32 → String
  | some status => s!"exit status {status}"
  | none => "not run, or no end observed"

/-- The standard streams of every command: no input, and the driver's own output. -/
def stdio : IO.Process.StdioConfig := { stdin := .null, stdout := .inherit, stderr := .inherit }

/-- Start `command` without waiting for it; `none`, with a report, when it could not be started.
It cannot raise. The child stays in the driver's process group, so the outer deadline's kill
reaches it. The inherited Lean search paths are removed, so a Lake command resolves modules only
through the workspace it runs in. Process execution and signal delivery remain trusted. -/
def start (command : Command) : BaseIO (Option (IO.Process.Child stdio)) := do
  announce s!"start {command.display}"
  let spawn : IO (IO.Process.Child stdio) := IO.Process.spawn {
    stdio with
    cmd := command.program, args := command.args, cwd := some command.dir,
    env := #[("GHCR_TOKEN", none), ("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
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
def execute (command : Command) : BaseIO (Option UInt32) := do
  let started ← IO.monoMsNow
  let some child ← start command | return none
  let ended ← await command child
  let seconds := ((← IO.monoMsNow) - started) / 1000
  if passed [ended] then announce s!"done in {seconds} s: {command.display}"
  else announce s!"failed in {seconds} s ({describe ended}): {command.display}"
  return ended

/-- Run `commands` one after another and return how each ended. A command runs only while
everything that has ended so far passed: `known` holds the ends known before it. A command after
a failure is not run and has no end. It cannot raise. -/
def executeInOrder : (known : List (Option UInt32)) → (commands : List Command) →
    BaseIO (Ends commands)
  | _, [] => return ⟨[], rfl⟩
  | known, command :: rest => do
      let ended ← if passed known then execute command else pure none
      let later ← executeInOrder (ended :: known) rest
      return ⟨(command, ended) :: later.ends, by simp [later.complete]⟩

/-! ## Places the driver removes

The driver removes two directories: the site artifact of an earlier run (`siteOutput`), and the
scratch directory of the copy it made (`Copy.remove`). `IO.FS.removeDirAll` reads the entries of
the path it is given, also when that path is a symbolic link to a directory, and then removes
the entries of the link's target. So the driver removes a directory only after `removal` decided
it from an observation that follows no link at the path.

**Outside this decision:** a process that replaces an entry below the directory with a link
while the removal runs. `IO.FS.removeDirAll` examines each entry and then opens it by its path,
so such a process can make it remove the entries of a different directory. The checker removes
its own scratch directories with the same function (`Regula.Scratch`). -/

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
  /-- Whether the real path of what is there is the path itself. -/
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

/-- What is at `path`, by a read that does not follow a symbolic link at `path` itself. -/
def place (path : System.FilePath) : IO Place := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => return if metadata.type == .dir then .directory else .other
  | .error (.noFileOrDirectory ..) => return .absent
  | .error error => throw error

/-- Remove the directory at `path`. A caller must give the proof that `removal` decided to remove
it, so no call exists for a path that `removal` refused or found empty. -/
def removeDecided (path : System.FilePath) (observed : Observed)
    (_decided : removal observed = .remove) : IO Unit :=
  IO.FS.removeDirAll path

/-- What the driver observes of `path` before a removal: what is there, by a read that follows
no link at the path, and whether its real path is the path. -/
def observe (path : System.FilePath) : IO Observed := do
  return {
    place := ← place path
    sameLocation := match ← (IO.FS.realPath path).toBaseIO with
      | .ok real => real == path
      | .error _ => false }

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

The first acceptance step makes its one build in a private copy of the project, and the
acceptance gate audits that copy. The gate executable imports the claimed libraries, so those
libraries are compiled before the gate can run, and a gate that made its own copy would compile
them a second time. This driver is the only process of the step that runs before any project
artifact exists, so it makes the copy.

The copy is in a new scratch directory of the checker's scratch area, by the protocol of
`Regula.Scratch`, which this module cannot import: the reclamation of the marked directories
when no scratch owner lives, an ownership marker beside the directory, and a shared lock on the
area's lock file for as long as the copy is in use. So a first step that starts while no other
scratch owner of the checkout lives leaves no scratch directory of a run that died before it,
when each removal succeeds, and it removes its own at its end. A removal that fails is reported
with its path and does not fail the step. A scratch owner that dies during the step, which is not this
driver, leaves its directory to the next scratch user. So the build output of
the copy holds only what the commands of this step made, the build reads files that no other
process is given, and the step removes nothing of the checkout. The acceptance gate cannot
observe that this driver made the copy new in this run; that statement rests on `makeCopy`. -/

/-- Whether a path below the project root, given by its components from the root, is part of
the copy. It is the rule by which the checker makes an isolated copy of a project
(`Regula.Checker.copyProject`): VCS data, Lake's directory, artifact caches and the checker's old
scratch directory are left out at every depth, and so is the root `tmp` directory. The two
modules cannot import one another, so the rule is written twice. The copy is the project that the
gate audits, whatever this rule copied, and a missing file fails the build. -/
def walked : List String → Bool
  | "tmp" :: _ => false
  | relative => relative.all fun component =>
      !([".git", ".lake", ".cache", ".regula-scratch"].contains component)

/-- `walked` accepts exactly the paths that do not start with `tmp` and have none of the four
left-out names as a component. -/
theorem walked_iff (relative : List String) :
    walked relative = true ↔ relative.head? ≠ some "tmp" ∧ ∀ component ∈ relative,
      component ≠ ".git" ∧ component ≠ ".lake" ∧ component ≠ ".cache" ∧
        component ≠ ".regula-scratch" := by
  unfold walked
  split
  · simp
  · next notTmp =>
    have head : relative.head? ≠ some "tmp" := by
      cases relative with
      | nil => simp
      | cons first rest =>
        intro isTmp
        simp only [List.head?_cons, Option.some.injEq] at isTmp
        exact notTmp rest (isTmp ▸ rfl)
    simp [head]

/-- Copy each walked entry of the project at `root` (`walked`) to the same place below `target`.
A file's bytes are copied; a symbolic link is followed, as `Regula.Checker.copyProject` follows
it. Every write is below `target`. -/
def copyTree (root target : System.FilePath) : IO Unit := do
  let rootComponents := root.normalize.components
  let included := fun (path : System.FilePath) =>
    walked (path.normalize.components.drop rootComponents.length)
  IO.FS.createDirAll target
  for path in ← root.walkDir (fun path => pure (included path)) do
    unless included path do continue
    let destination := (path.normalize.components.drop rootComponents.length).foldl
      (· / System.FilePath.mk ·) target
    if ← path.isDir then IO.FS.createDirAll destination
    else
      if let some parent := destination.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile destination (← IO.FS.readBinFile path)

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
  fails when the name exists, and the record by one that fails when the file exists. The gate of
  this run writes it, and this run promotes it (`run`). A record that no run
  promoted is removed with its scratch directory, by this run or by a reclamation. -/
  pending : System.FilePath
  /-- The handle that holds the shared lock of the scratch area while the copy is in use. -/
  lock : IO.FS.Handle

/-- Remove each marked scratch directory of `area`, then its marker: the reclamation of
`Regula.Scratch`, with its conditions in its order. The caller holds the lock of the area
exclusively, so no owner of a scratch directory lives, and each marked directory is one of a run
that ended without its removal. A marker counts only when it is a regular file. Its directory is
removed only as `removal` decides, a marker with no directory is removed, and with anything
else at the directory's place nothing is removed. It cannot raise: a removal that fails, or a
scratch area that cannot be read, is reported with its path and is no error of the step, and
that directory then stays. -/
def reclaim (area : System.FilePath) : BaseIO Unit := do
  let all : IO Unit := do
    for entry in ← area.readDir do
      unless entry.path.extension == some "owner" do continue
      let some name := entry.path.fileStem | continue
      let path := area / name
      let one : IO Unit := do
        unless (← entry.path.symlinkMetadata).type == .file do return
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

/-- Make the copy of the project at the real path `root`, by the steps of
`Regula.Scratch.withScratch` in its order. When the lock of the checker's scratch area can be
taken exclusively, no scratch owner lives, and the marked directories are removed first
(`reclaim`). Then: take the shared lock of the area, create the ownership marker of a new name
exclusively, create the directory of that name, which must not exist, and copy the project into
its directory `project` (`copyTree`). So the checker's reclamation and that of a later driver
remove the directory of a driver that died, and remove none while this driver holds the lock.
The copy has no `.lake`, so it has no build output. -/
def makeCopy (root : System.FilePath) : IO Copy := do
  IO.FS.createDirAll (root / ".lake" / "regula-scratch")
  let area ← IO.FS.realPath (root / ".lake" / "regula-scratch")
  let lock ← IO.FS.Handle.mk (area / ".lock") .append
  if ← lock.tryLock then
    try reclaim area finally lock.unlock
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
  copyTree root project
  let pending := scratch / "acceptance-link.pending.json"
  let record ← IO.FS.Handle.mk pending .writeNew
  record.putStr incompleteLink
  record.flush
  return { scratch, marker, project, pending, lock }

/-- Give the build output of the copy to the project at `root`, when the project has none:
rename the copy's `.lake/build` to the project's, only when nothing is at that place by a read
that follows no link. A project with build output, or with anything else at that place, keeps
it. The rename is in one file system, deletes nothing, and does not follow a link at its target.
It returns whether it renamed. A rename that fails is reported and is no error of the step: the
documentation step then builds what it needs. -/
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

/-- Remove the copy: its scratch directory, then its marker, then the lock, in the order of
`Regula.Scratch.withScratch`. The directory is removed only as `removeOwn` decides. A failure is
reported and is no error of the step: the checker's reclamation removes the directory later. -/
def Copy.remove (copy : Copy) : BaseIO Unit := do
  let remove : IO Unit := do
    removeOwn copy.scratch
    IO.FS.removeFile copy.marker
    copy.lock.unlock
  if let .error error ← remove.toBaseIO then
    announce s!"could not remove the copy {copy.scratch}: {error}"

/-- The failure report: each command that did not end with exit status 0, with how it ended. -/
def report (ends : List (Command × Option UInt32)) : String :=
  "\n".intercalate ("verification failed:" :: ends.filterMap fun (command, ended) =>
    if passed [ended] then none else some s!"  {command.display}: {describe ended}")

private def usage : String :=
  "usage: scripts/verify.sh [docs | serialized-graph | site | mathlib | diagnostics \
    [fixtures|structural [1/2|2/2]|execution [1/2|2/2]|cli|environments|build-policy|\
    lint-driver|producers|history|self-lint|self-audit|rule-examples [1/2|2/2]]]"

/-- The earlier verdicts an attempt of `mode` invalidates, each with the constant text recording
it as incomplete. Ordinary acceptance invalidates the accepted link, so it is not accepted from
then on unless a run promotes the pending record of its own gate to it. -/
def invalidated : Mode → List (String × String)
  | .ordinary => [(linkPath, incompleteLink)]
  | .ruleExamples =>
      [("tmp/rule-examples.json", "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")]
  | .ruleExamplesFirst =>
      [(shardEvidence 1, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")]
  | .ruleExamplesSecond =>
      [(shardEvidence 2, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")]
  | _ => []

/-- The package adopters require stays dependency-free: its lock manifest records no package. Lake
refuses to load a workspace whose configuration requires a package that the lock manifest does not
record, so an accepted build of the root package with such a manifest requires nothing, and
requiring `regula` adds only `regula` to an adopter's `lake-manifest.json`. The Mathlib
integration package in `integration/mathlib/` records its own pins. -/
def dependencyFree (manifest : Lean.Json) : Bool :=
  match manifest.getObjValAs? (Array Lean.Json) "packages" with
  | .ok packages => packages.isEmpty
  | .error _ => false

/-- Soundness: an admitted lock manifest has a `packages` array, and it is empty. -/
theorem dependencyFree_packages (manifest : Lean.Json) (h : dependencyFree manifest = true) :
    manifest.getObjValAs? (Array Lean.Json) "packages" = .ok #[] := by
  unfold dependencyFree at h
  split at h
  · rename_i packages hp
    rw [hp, Array.isEmpty_iff.mp h]
  · simp at h

/-- Begin an attempt: invalidate the selected mode's earlier PASS or accepted link, and remove
an earlier site artifact. `scripts/verify.sh` runs this toolchain-only step before provisioning
and before any checker is built, so a failed setup or build cannot leave either in place. The
site artifact is removed only when a directory is at its own place (`removeOwn`): with a symbolic
link at `_site` the attempt stops and removes nothing. -/
def beginAttempt (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  for (path, text) in invalidated selection.val do
    IO.FS.createDirAll "tmp"
    IO.FS.writeFile path text
  if selection.val == .site then
    removeOwn ((← IO.FS.realPath ".") / siteOutput)

/-- Cold-start driver; all builds and checks stay within the inherited outer deadline. After the
preliminary checks it runs the commands of the mode one after another, starts one only while
every end known so far passed, and reports success only when `passed` accepts how every one of
those commands ended (`passed_covers`). The first acceptance step promotes the pending record of
its own gate to the accepted link only then, before the removal of its copy and before the
success line. It makes its copy
after the preliminary checks (`makeCopy`), runs its commands for that copy (`ordinary_places`),
gives the copy's build output to a project that has none when the step passed (`Copy.adopt`),
and removes the copy in each case (`Copy.remove`). -/
def run (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  if selection.val == .ordinary then
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "lake-manifest.json"))
    unless dependencyFree manifest do
      throw <| IO.userError "lake-manifest.json records a dependency: the regula package must \
        require nothing beyond the Lean toolchain (a Mathlib-dependent module belongs in \
        integration/mathlib/)"
  let early ← executeInOrder []
    [({ program := "git", args := #["diff", "--check"] } : Command),
      { program := "git", args := #["diff", "--cached", "--check"] },
      { program := "shellcheck", args := #["scripts/verify.sh", "scripts/provision.sh"] }]
  let root ← IO.FS.realPath "."
  let copy ← if selection.val == .ordinary && passed early.statuses then
      some <$> makeCopy root
    else pure none
  let later ← executeInOrder early.statuses
    (commands ((copy.map (·.project.toString)).getD ".")
      ((copy.map (·.pending.toString)).getD "") selection.val)
  let all := early.append later
  if let some copy := copy then
    -- The pending record is in the scratch directory of the copy, so the promotion is before
    -- the removal of the copy, which follows in each case.
    try
      if passed all.statuses then
        discard <| copy.adopt root
        IO.FS.rename copy.pending linkPath
        announce s!"every command exited 0: moved {copy.pending} to {linkPath}"
    finally copy.remove
  unless passed all.statuses do
    throw <| IO.userError (report all.ends)
  IO.println (match selection.val with
    | .ordinary => "local verification: PASS (ordinary mechanical acceptance commands completed; \
      semantic review is separate; run `scripts/verify.sh docs` for documentation)"
    | .docs => "documentation verification: PASS (every rule ID in the prose md4c reads in each \
      tracked Markdown document links to its rule page; CONTEXT.md is the print of a vocabulary \
      whose source paths are tracked files, and the controls of that check gave the expected \
      results; the example package in audit/ accepted \
      fresh; every docs/ Lean fence and every lean block of the Verso standard, which built \
      fresh and rendered; every rule ID in the prose `Regula.Prose` reads in the rendered \
      standard links to its rule page; inputs equal the accepted ordinary inputs)"
    | .graph => "serialized-graph diagnostic: PASS (not ordinary verification)"
    | .site => "site build and check: PASS (rule-reference artifact in _site; separate from \
      acceptance; publication is verified after deployment)"
    | .mathlib => "Mathlib integration check: PASS (the Mathlib integration package accepted fresh \
      and linted on its pinned Mathlib; separate from acceptance, which needs no Mathlib)"
    | _ => "diagnostic qualification: PASS (selected scope only; not ordinary verification)")

/-- The private `--copy-control` entry, for the controls of the checker self-test, so that they
qualify the copy, the lock and the marker of this driver and not a second implementation of
them. It makes the copy of the project in the current directory as the first acceptance step
makes it (`makeCopy`), prints the copy's root, and then obeys the lines of its standard input:
`adopt` gives the copy's build output to the project when it has none (`Copy.adopt`) and prints
`adopted` or `kept`; `remove` removes the copy (`Copy.remove`) and ends. At the end of the input
it ends and leaves the copy with its marker, as a killed run leaves it. It runs no check and
reports no verification result. -/
def copyControl : IO Unit := do
  let root ← IO.FS.realPath "."
  let copy ← makeCopy root
  let stdout ← IO.getStdout
  stdout.putStrLn copy.project.toString
  stdout.flush
  let stdin ← IO.getStdin
  repeat
    let line ← stdin.getLine
    if line.isEmpty then return
    match line.trimAscii.toString with
    | "adopt" =>
        stdout.putStrLn (if ← copy.adopt root then "adopted" else "kept")
        stdout.flush
    | "remove" =>
        copy.remove
        return
    | other => throw <| IO.userError s!"--copy-control: unknown line {other}"

end RegulaVerification

/-- Standalone cold-start entrypoint; invoke through the timed `scripts/verify.sh`, which
first runs it with the private `--begin-attempt` protocol flag before setup. The private
`--copy-control` entry is for the controls of the checker self-test. -/
def main : List String → IO Unit
  | "--begin-attempt" :: args => RegulaVerification.beginAttempt args
  | ["--copy-control"] => RegulaVerification.copyControl
  | args => RegulaVerification.run args
