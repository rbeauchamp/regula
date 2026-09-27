import Lean

/-! # Cold-start verification driver

Cold-start verification plan and operational interpreter. This module imports only
the pinned toolchain, so it can run before any root-package artifacts exist. Argument
selection has soundness and round-trip proofs; the interpreter consumes its proof-bearing
selection. Recipes name Lake targets, not a source-file census. Process effects remain
trusted IO under the shell's single 420-second process-group deadline. -/
namespace RegulaVerification

/-- Closed vocabulary of supported verification invocations. -/
inductive Mode where
  /-- No argument: the first acceptance step, which builds the acceptance executables, runs the
  registry checks and combined qualification, and audits the claimed surfaces. -/
  | ordinary
  /-- `docs`: the second acceptance step, the documentation audit and the Verso standard's
  build and render, refused unless its inputs equal those the first step accepted. -/
  | docs
  /-- `serialized-graph`: the separate serialized-graph check (`freshChecker`). -/
  | graph
  /-- `diagnostics`: the checker self-test diagnostic, not acceptance. -/
  | diagnostics
  /-- `diagnostics fixtures`: the self-test's fixtures partition. -/
  | fixtures
  /-- `diagnostics structural`: the self-test's structural partition. -/
  | structural
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
  deriving DecidableEq

/-- Exactly the documented arguments for each mode, with no ignored trailing arguments. -/
def arguments : Mode → List String
  | .ordinary => []
  | .docs => ["docs"]
  | .graph => ["serialized-graph"]
  | .diagnostics => ["diagnostics"]
  | .fixtures => ["diagnostics", "fixtures"]
  | .structural => ["diagnostics", "structural"]
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

/-- Every supported mode occurs once; the parser searches only this closed vocabulary. -/
def modes : List Mode := [.ordinary, .docs, .graph, .diagnostics, .fixtures, .structural,
  .cli, .environments, .buildPolicy, .lintDriver, .producers, .history, .selfLint, .selfAudit, .ruleExamples, .ruleExamplesFirst,
  .ruleExamplesSecond, .site]

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

private def lake (args : Array String) : Command := ⟨"lake", args⟩

/-- Ordinary acceptance records its accepted input identity here; the separately timed
documentation step refuses unless its own identity is equal. -/
def linkPath : String := "tmp/acceptance-link.json"

/-- The standard's Verso source: package directory, library and its render-only executable.
Both acceptance steps capture its sources and the package inputs its check reads in the linked
identity; the documentation step also builds (elaborating every `lean` block where it is
written) and renders it, requires every anchor the rule registry and the documentation link, and
requires the coverage map to link exactly the checklist's rows, each labelled with its row. -/
def versoStandard : String := "website:RegulaStandard:regula-standard"

/-- Evidence receipt of one rule-example shard. -/
def shardEvidence (index : Nat) : String := s!"tmp/rule-examples-{index}of2.json"

/-- Rule-reference site artifact directory (the GitHub Pages upload). -/
def siteOutput : String := "_site"

/-- One of two disjoint corpus shards, selected by rule position in the corpus. -/
private def ruleExampleShard (index : Nat) : List Command := [
  lake #["build", "axiomGate", "ruleExamples", "ruleExampleQualification", "qualify"],
  lake #["exe", "qualify", "--under-deadline", "rule-examples", "--evidence", shardEvidence index,
    "--shard", s!"{index}/2"]]

/-- Existing acceptance and diagnostic recipes, executed inside the outer deadline.
Qualification's private flag retains the already timed process group. -/
def commands : Mode → List Command
  | .ordinary => [
      lake #["build", "RegulaPolicy", "RegulaCore", "RegulaQualification", "axiomGate", "docFenceAudit", "qualify",
        "+Regula.Checker.CheckerSelftest:olean", "+Regula.Checker.FreshChecker:olean",
        "+Regula.RegistryChecks:olean", "+Regula.Linter:olean", "+Regula.Checker.LintMain:olean",
        "+Regula.Checker.RuleExamples:olean", "+Regula.Checker.RuleExampleQualificationMain:olean",
        "+Regula.Cli.Main:olean",
        -- Type-check, never run, the opt-in network intent screen (docs/guides/intent-screening.md).
        "+Regula.Screen.Main:olean"],
      lake #["env", "lean", "--run", "lean/Regula/RegistryChecks.lean"],
      lake #["exe", "qualify", "--under-deadline", "combined"],
      lake #["exe", "axiomGate", "--acceptance-link", linkPath, "--verso", versoStandard]]
  | .docs => [
      lake #["build", "docFenceAudit"],
      lake #["exe", "docFenceAudit", "--acceptance-link", linkPath, "--verso", versoStandard]]
  | .graph => [lake #["exe", "freshChecker", "--verbose"]]
  | .diagnostics => [lake #["exe", "checkerSelftest", "--build-bound", "--jobs", "4"]]
  | .producers => [
      lake #["build", "axiomGate", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "producers"]]
  | .history => [
      lake #["build", "axiomGate", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "history"]]
  -- Regula on its own code base: the repository's own `lake lint` through `regula/lint`, and the
  -- operational self-audit of the excluded `Regula` library after its warning-free build.
  | .selfLint => [lake #["lint"]]
  | .selfAudit => [
      lake #["build", "Regula", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "self-audit"]]
  | .ruleExamples => [
      lake #["build", "axiomGate", "ruleExamples", "ruleExampleQualification", "qualify"],
      lake #["exe", "qualify", "--under-deadline", "rule-examples", "--evidence", "tmp/rule-examples.json"]]
  | .ruleExamplesFirst => ruleExampleShard 1
  | .ruleExamplesSecond => ruleExampleShard 2
  | .site => [
      lake #["build", "axiomGate", "ruleExampleQualification", "site"],
      lake (#["exe", "site", "build", "--out", siteOutput, "--evidence"] ++ #[shardEvidence 1, shardEvidence 2])]
  | mode => [lake (#["exe", "checkerSelftest", "--build-bound", "--partition"] ++
      ((arguments mode).drop 1).toArray ++ #["--jobs", "4"])]

/-- Every mode schedules actual work rather than accepting an empty campaign. -/
theorem commands_nonempty (mode : Mode) : commands mode ≠ [] := by
  cases mode <;> simp [commands, ruleExampleShard]

/-- Interpret sequentially; a nonzero process exit raises before any success report.
No theorem here purports to prove the OS's process execution or signal delivery. -/
def execute (command : Command) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := command.program, args := command.args,
    stdin := .null, stdout := .inherit, stderr := .inherit }
  let exit ← child.wait
  if exit != 0 then throw <| IO.userError s!"{command.program} {command.args} failed ({exit})"

private def usage : String :=
  "usage: scripts/verify.sh [docs | serialized-graph | site | diagnostics [fixtures|structural|cli|environments|build-policy|lint-driver|producers|history|self-lint|self-audit|rule-examples [1/2|2/2]]]"

/-- The earlier verdict an attempt of `mode` invalidates, with the constant text recording it
as incomplete. -/
def invalidated : Mode → Option (String × String)
  | .ordinary => some (linkPath, "{\"schemaVersion\":1,\"status\":\"incomplete\"}\n")
  | .ruleExamples => some ("tmp/rule-examples.json", "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")
  | .ruleExamplesFirst => some (shardEvidence 1, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")
  | .ruleExamplesSecond => some (shardEvidence 2, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")
  | _ => none

/-- Begin an attempt: invalidate the selected mode's earlier PASS or accepted link, and remove
an earlier site artifact. `scripts/verify.sh` runs this toolchain-only step before provisioning
and before any checker is built, so a failed setup or build cannot leave either in place. -/
def beginAttempt (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  if let some (path, text) := invalidated selection.val then
    IO.FS.createDirAll "tmp"
    IO.FS.writeFile path text
  if selection.val == .site then
    if ← System.FilePath.pathExists siteOutput then IO.FS.removeDirAll siteOutput

/-- Cold-start driver; all builds and checks stay within the inherited outer deadline. -/
def run (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  for command in [Command.mk "git" #["diff", "--check"],
      Command.mk "git" #["diff", "--cached", "--check"],
      Command.mk "shellcheck" #["scripts/verify.sh", "scripts/provision.sh"]] ++ commands selection.val do
    execute command
  IO.println (match selection.val with
    | .ordinary => "local verification: PASS (ordinary mechanical acceptance commands completed; semantic review is separate; run `scripts/verify.sh docs` for documentation)"
    | .docs => "documentation verification: PASS (every docs/ Lean fence and every lean block of the Verso standard, which built fresh and rendered; inputs equal the accepted ordinary inputs)"
    | .graph => "serialized-graph diagnostic: PASS (not ordinary verification)"
    | .site => "site build and check: PASS (rule-reference artifact in _site; separate from acceptance; publication is verified after deployment)"
    | _ => "diagnostic qualification: PASS (selected scope only; not ordinary verification)")

end RegulaVerification

/-- Standalone cold-start entrypoint; invoke through the timed `scripts/verify.sh`, which
first runs it with the private `--begin-attempt` protocol flag before setup. -/
def main : List String → IO Unit
  | "--begin-attempt" :: args => RegulaVerification.beginAttempt args
  | args => RegulaVerification.run args
