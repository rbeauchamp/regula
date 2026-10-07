import Lean

/-! # Cold-start verification driver

Cold-start verification plan and operational interpreter. This module imports only
the pinned toolchain, so it can run before any root-package artifacts exist. Argument
selection has soundness and round-trip proofs; the interpreter consumes its proof-bearing
selection. Recipes name Lake targets, not a source-file census. The interpreter schedules every
command of the selected recipe (`inOrder_append_beside`), starts a command only while every end
known so far passed, waits for each command it started, and reports success only when `passed`
accepts how each scheduled command ended (`passed_covers`); it starts the gate of ordinary
acceptance beside the others once that gate is built (`prebuild`, `beside`, `beside_prebuilt`),
and starts those others at low scheduling priority while it does (`Priority`).
Process effects remain trusted IO under the shell's single 420-second process-group deadline. -/
namespace RegulaVerification

/-- Closed vocabulary of supported verification invocations. -/
inductive Mode where
  /-- No argument: the first acceptance step, which builds the acceptance executables, runs the
  registry checks and combined qualification, and audits the root package's claimed surfaces. -/
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
documentation step refuses unless its own identity is equal. The driver puts the record here as
its last action before the success line (`promoted`), so an accepted record here means that every
command of the step exited 0. -/
def linkPath : String := "tmp/acceptance-link.json"

/-- Where the gate of ordinary acceptance records that identity. The gate runs beside the step's
other commands (`beside`), so its own success does not end the step: this record becomes
`linkPath` only once every command has exited 0 (`promoted`), and a run that fails or is killed
before then leaves `linkPath` incomplete. -/
def pendingLinkPath : String := "tmp/acceptance-link.pending.json"

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
Qualification's private flag retains the already timed process group. -/
def commands : Mode → List Command
  | .ordinary => [
      lake
          #["build", "RegulaPolicy", "RegulaCore", "RegulaQualification", "axiomGate",
              "docFenceAudit", "qualify",
        "+Regula.Checker.CheckerSelftest:olean", "+Regula.Checker.FreshChecker:olean",
        "+Regula.RegistryChecks:olean", "+Regula.Linter:olean", "+Regula.Checker.LintMain:olean",
        "+Regula.Checker.RuleExamples:olean", "+Regula.Checker.RuleExampleQualificationMain:olean",
        "+Regula.Cli.Main:olean", "+Regula.Release:olean", "+Regula.DiagnosticsGate:olean"],
      lake #["env", "lean", "--run", "lean/Regula/RegistryChecks.lean"],
      lake #["exe", "qualify", "--under-deadline", "combined"],
      lake #["exe", "axiomGate", "--acceptance-link", pendingLinkPath, "--verso", versoStandard]]
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
theorem commands_nonempty (mode : Mode) : commands mode ≠ [] := by
  cases mode <;> simp [commands, ruleExampleShard, selftest]

/-- Builds the driver runs before a mode's `commands`. They decide cost, never results: each is a
`lake build` in the repository root that names a target (`prebuild_builds`), and every target one
names is named again by a build among those commands (`prebuild_named`), which still builds
whatever is missing. Ordinary acceptance builds `axiomGate` alone first, so that the gate
can start before the rest of the step's build has ended: that rest and the other checks then run
beside the gate (`beside`). How much time that saves is an estimate, not a property of this
definition. -/
def prebuild : Mode → List Command
  | .ordinary => [lake #["build", "axiomGate"]]
  | _ => []

/-- The Lake targets a command builds: the arguments after `build` of a `lake build` in the
repository root, and none for any other command. -/
def buildTargets (command : Command) : List String :=
  if command.program = "lake" ∧ command.dir = "." ∧ command.args[0]? = some "build" then
    command.args.toList.drop 1
  else []

/-- A prebuild only builds: it has a target, which `buildTargets` gives to nothing but a
`lake build` in the repository root. So `prebuild_named` speaks about every prebuild. -/
theorem prebuild_builds (mode : Mode) (command : Command) (h : command ∈ prebuild mode) :
    buildTargets command ≠ [] := by
  cases mode <;> simp [prebuild] at h
  subst h
  simp [buildTargets, lake]

/-- A prebuild selects nothing: it is a build (`prebuild_builds`), and each target it names is a
target of a build among the mode's own commands, which runs to completion before any success
report. -/
theorem prebuild_named (mode : Mode) (command : Command) (target : String)
    (h : command ∈ prebuild mode) (named : target ∈ buildTargets command) :
    ∃ later ∈ commands mode, target ∈ buildTargets later := by
  cases mode <;> simp [prebuild] at h
  subst h
  refine ⟨_, List.mem_cons_self, ?_⟩
  simp [buildTargets, lake] at named ⊢
  simp [named]

/-- How many of a mode's last `commands` run beside the others (`beside`). Ordinary acceptance
runs its gate so; every other mode runs its commands one after another. -/
def besideCount : Mode → Nat
  | .ordinary => 1
  | _ => 0

/-- The commands of `mode` that run one after another: all but its last `besideCount`. -/
def inOrder (mode : Mode) : List Command :=
  (commands mode).take ((commands mode).length - besideCount mode)

/-- The commands of `mode` that each run as a process of their own, started before `inOrder` and
joined after it: its last `besideCount`. Each runs an executable that a prebuild names
(`beside_prebuilt`). -/
def beside (mode : Mode) : List Command :=
  (commands mode).drop ((commands mode).length - besideCount mode)

/-- The two groups are the mode's commands, each once and in their order, whatever
`besideCount` is: the schedule drops no command and adds none. -/
theorem inOrder_append_beside (mode : Mode) : inOrder mode ++ beside mode = commands mode :=
  List.take_append_drop _ _

/-- A command that runs beside the others is a `lake exe` in the repository root, and a prebuild
of its mode names its executable as a target. That the prebuild has ended before the command
starts is the driver's order (`run`), and that Lake then builds nothing for the command is Lake's
behaviour; neither is this theorem. -/
theorem beside_prebuilt (mode : Mode) (command : Command) (h : command ∈ beside mode) :
    command.program = "lake" ∧ command.dir = "." ∧ command.args[0]? = some "exe" ∧
      ∃ target, command.args[1]? = some target ∧
        ∃ early ∈ prebuild mode, target ∈ buildTargets early := by
  cases mode <;> simp [beside, besideCount, commands] at h
  subst h
  simp [lake, prebuild, buildTargets]

/-- Whether a step passed, from how its commands ended: `inOrder` for those that run one after
another and `beside` for those that run beside them. An end is `some status` for a command that
ran to its end with that exit status, and `none` for one that was not run, could not be started,
or whose end could not be observed. A step passes exactly when every command of each side ended
with exit status 0 (`passed_iff`). It is the driver's one decision about an exit status: the
driver asks it before it runs a further command, before it reports, and before it moves an
acceptance record. -/
def passed (inOrder beside : List (Option UInt32)) : Bool :=
  (inOrder ++ beside).all (· == some 0)

/-- `passed` accepts exactly the ends in which each command of each side has exit status 0. -/
theorem passed_iff (inOrder beside : List (Option UInt32)) :
    passed inOrder beside = true ↔
      (∀ ended ∈ inOrder, ended = some 0) ∧ (∀ ended ∈ beside, ended = some 0) := by
  simp [passed]

/-- The commands of one side with how each ended. It has an entry for each of `commands`, in
their order, so no value of this type leaves a command out. -/
structure Ends (commands : List Command) where
  /-- Each command with how it ended (`passed`). -/
  ends : List (Command × Option UInt32)
  /-- One entry for each command, in the commands' order. -/
  complete : ends.map (·.1) = commands

/-- How the commands of a side ended, without the commands: what `passed` reads. -/
def Ends.statuses {commands : List Command} (side : Ends commands) : List (Option UInt32) :=
  side.ends.map (·.2)

/-- The ends of two groups of commands that ran one after the other, as the ends of both. -/
def Ends.append {first second : List Command} (early : Ends first) (late : Ends second) :
    Ends (first ++ second) :=
  ⟨early.ends ++ late.ends, by simp [early.complete, late.complete]⟩

/-- When `passed` accepts the ends of two sides, every command of each side is recorded with exit
status 0. None is left out, because an `Ends` has an entry for each of its commands. That each
recorded status is the one the command's process ended with is the trusted process runtime. -/
theorem passed_covers {inOrder beside : List Command} (first : Ends inOrder)
    (second : Ends beside) (accepted : passed first.statuses second.statuses = true) :
    ∀ command ∈ inOrder ++ beside, (command, some 0) ∈ first.ends ++ second.ends := by
  intro command member
  have ⟨inFirst, inSecond⟩ := (passed_iff _ _).mp accepted
  rw [← first.complete, ← second.complete] at member
  rcases List.mem_append.mp member with here | here
  · obtain ⟨⟨recorded, ended⟩, entry, rfl⟩ := List.mem_map.mp here
    have zero := inFirst ended (List.mem_map.mpr ⟨_, entry, rfl⟩)
    exact List.mem_append_left _ (zero ▸ entry)
  · obtain ⟨⟨recorded, ended⟩, entry, rfl⟩ := List.mem_map.mp here
    have zero := inSecond ended (List.mem_map.mpr ⟨_, entry, rfl⟩)
    exact List.mem_append_right _ (zero ▸ entry)

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

/-- The scheduling priority the driver asks of the operating system for a command. It changes
when a command gets a processor, never which command runs or what the driver does with its
end. -/
inductive Priority where
  /-- The driver's own priority. -/
  | normal
  /-- The lowest priority, for a command that runs while a command of `beside` runs: the
  scheduler is asked to prefer the command of `beside` whenever both ask for a processor. A
  command keeps this priority to its end, also after the command of `beside` ended, and the
  scheduler is asked to prefer any other work at normal priority in the same way. So on a machine
  that such other work fills, a command at low priority can get little processor time, and the
  schedule can then take longer than the same commands one after another. That it takes no longer
  than they do therefore assumes, as the third of three assumptions, that no other work at normal
  priority uses the machine (`executeBeside`). -/
  | low

/-- How the progress line of a start names a priority: nothing for the driver's own. -/
def Priority.display : Priority → String
  | .normal => ""
  | .low => "at low priority: "

/-- The program and the arguments that start `command` at `priority`. At low priority the program
is the POSIX utility `nice`, which is given the command's own program and arguments, unchanged
and in their order, after `-n 19`. That `nice` then runs exactly that program with those
arguments at that priority, and ends with the status the program ends with, is the utility's
behaviour and is trusted, as is the scheduler's use of the priority. POSIX gives `nice` a status
other than 0 when it could not run the program. -/
def Command.launch (command : Command) : Priority → String × Array String
  | .normal => (command.program, command.args)
  | .low => ("nice", #["-n", "19", command.program] ++ command.args)

/-- Start `command` at `priority` without waiting for it; `none`, with a report, when it could not
be started. It cannot raise. The child stays in the driver's process group, so the outer
deadline's kill reaches it. Process execution and signal delivery remain trusted. -/
def start (priority : Priority) (command : Command) :
    BaseIO (Option (IO.Process.Child stdio)) := do
  announce s!"start {priority.display}{command.display}"
  let (program, args) := command.launch priority
  let spawn : IO (IO.Process.Child stdio) := IO.Process.spawn {
    stdio with
    cmd := program, args := args, cwd := some command.dir,
    env := #[("GHCR_TOKEN", none)] }
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

/-- Run one command at `priority` to its end and return how it ended. It cannot raise. -/
def execute (priority : Priority) (command : Command) : BaseIO (Option UInt32) := do
  let started ← IO.monoMsNow
  let some child ← start priority command | return none
  let ended ← await command child
  let seconds := ((← IO.monoMsNow) - started) / 1000
  if passed [ended] [] then announce s!"done in {seconds} s: {command.display}"
  else announce s!"failed in {seconds} s ({describe ended}): {command.display}"
  return ended

/-- Run `commands` one after another, each at `priority`, and return how each ended. A command
runs only while everything that has ended so far passed: `known` holds the ends known before it,
of either side. A command after a failure is not run and has no end. It cannot raise. -/
def executeInOrder (priority : Priority) : (known : List (Option UInt32)) →
    (commands : List Command) → BaseIO (Ends commands)
  | _, [] => return ⟨[], rfl⟩
  | known, command :: rest => do
      let ended ← if passed known [] then execute priority command else pure none
      let later ← executeInOrder priority (ended :: known) rest
      return ⟨(command, ended) :: later.ends, by simp [later.complete]⟩

/-- Start each of `beside` as a process of its own, run `inOrder` one after another meanwhile,
then wait for each started command, and return how the commands of each side ended. Nothing is
started once something has failed (`known`). This is a `BaseIO` action, which has no exception,
so nothing can leave between a start and the wait for it: every started command is joined, also
when another command failed. The driver never kills a child, because that would not stop the
child's own descendants.

`priority` is the priority of the commands of `inOrder`. Each command of `beside` starts at the
driver's own priority, and the commands of `inOrder` then run at low priority, because they run
while it does. With no command in `beside`, they run at the priority the caller gives.

That priority is chosen once, before the first command of `inOrder`, and is not looked at again:
a command of `inOrder` keeps it to its end, and each later one starts at it, also after every
command of `beside` ended. That the two sides then take no longer than the same commands one
after another is an argument, not a measurement and not a theorem, and it has three assumptions:
the scheduler gives a command of `beside` every processor it can use, memory is not the limit,
and no other work at normal priority uses the machine. On a machine that such other work fills,
the commands at low priority can get little processor time, also after the commands of `beside`
ended, and the two sides can then take longer than the same commands one after another. -/
def executeBeside (priority : Priority) : (known : List (Option UInt32)) →
    (beside inOrder : List Command) → BaseIO (Ends inOrder × Ends beside)
  | known, [], inOrder => return (← executeInOrder priority known inOrder, ⟨[], rfl⟩)
  | known, command :: rest, inOrder => do
      let child ← if passed known [] then start .normal command else pure none
      let (others, later) ←
        executeBeside .low (if child.isSome then known else none :: known) rest inOrder
      let ended ← match child with
        | none => pure none
        | some child => do
            unless passed others.statuses later.statuses do
              announce s!"a command failed; waiting for {command.display}"
            let ended ← await command child
            announce s!"joined ({describe ended}): {command.display}"
            pure ended
      return (others, ⟨(command, ended) :: later.ends, by simp [later.complete]⟩)

/-- The failure report: each command that did not end with exit status 0, with how it ended. -/
def report (ends : List (Command × Option UInt32)) : String :=
  "\n".intercalate ("verification failed:" :: ends.filterMap fun (command, ended) =>
    if passed [ended] [] then none else some s!"  {command.display}: {describe ended}")

private def usage : String :=
  "usage: scripts/verify.sh [docs | serialized-graph | site | mathlib | diagnostics \
    [fixtures|structural [1/2|2/2]|execution [1/2|2/2]|cli|environments|build-policy|\
    lint-driver|producers|history|self-lint|self-audit|rule-examples [1/2|2/2]]]"

/-- The earlier verdicts an attempt of `mode` invalidates, each with the constant text recording
it as incomplete. Ordinary acceptance invalidates the accepted link and the gate's pending record
of it, so neither is accepted from then on unless this attempt wrote it. -/
def invalidated : Mode → List (String × String)
  | .ordinary => [linkPath, pendingLinkPath].map
      (·, "{\"schemaVersion\":1,\"status\":\"incomplete\"}\n")
  | .ruleExamples =>
      [("tmp/rule-examples.json", "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")]
  | .ruleExamplesFirst =>
      [(shardEvidence 1, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")]
  | .ruleExamplesSecond =>
      [(shardEvidence 2, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")]
  | _ => []

/-- The record a mode's gate writes and the place the driver moves it to once every command of
the mode has exited 0, as the driver's last action before the success line. -/
def promoted : Mode → Option (String × String)
  | .ordinary => some (pendingLinkPath, linkPath)
  | _ => none

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
and before any checker is built, so a failed setup or build cannot leave either in place. -/
def beginAttempt (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  for (path, text) in invalidated selection.val do
    IO.FS.createDirAll "tmp"
    IO.FS.writeFile path text
  if selection.val == .site then
    if ← System.FilePath.pathExists siteOutput then IO.FS.removeDirAll siteOutput

/-- Cold-start driver; all builds and checks stay within the inherited outer deadline. After the
preliminary checks and the mode's `prebuild`, it schedules every command of the mode
(`inOrder_append_beside`), starts one only while every end known so far passed, and waits for
each one it started before it reports. It reports success, and first
moves a record the mode promotes (`promoted`), only when `passed` accepts how every one of those
commands ended (`passed_covers`). -/
def run (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  if selection.val == .ordinary then
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "lake-manifest.json"))
    unless dependencyFree manifest do
      throw <| IO.userError "lake-manifest.json records a dependency: the regula package must \
        require nothing beyond the Lean toolchain (a Mathlib-dependent module belongs in \
        integration/mathlib/)"
  let early ← executeInOrder .normal []
    ([({ program := "git", args := #["diff", "--check"] } : Command),
      { program := "git", args := #["diff", "--cached", "--check"] },
      { program := "shellcheck", args := #["scripts/verify.sh", "scripts/provision.sh"] }] ++
          prebuild selection.val)
  let (others, gates) ←
    executeBeside .normal early.statuses (beside selection.val) (inOrder selection.val)
  let ordered := early.append others
  unless passed ordered.statuses gates.statuses do
    throw <| IO.userError (report (ordered.ends ++ gates.ends))
  if let some (pending, accepted) := promoted selection.val then
    IO.FS.rename pending accepted
    announce s!"every command exited 0: moved {pending} to {accepted}"
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

end RegulaVerification

/-- Standalone cold-start entrypoint; invoke through the timed `scripts/verify.sh`, which
first runs it with the private `--begin-attempt` protocol flag before setup. -/
def main : List String → IO Unit
  | "--begin-attempt" :: args => RegulaVerification.beginAttempt args
  | args => RegulaVerification.run args
