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
  registry checks and combined qualification, and audits the root package's claimed surfaces. -/
  | ordinary
  /-- `docs`: the second acceptance step: the fresh acceptance of the Mathlib package whose
  modules the standard's examples import, then the documentation audit and the Verso standard's
  build and render, refused unless its inputs have the content identity the first step
  recorded. -/
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

/-- Every supported mode occurs once; the parser searches only this closed vocabulary. -/
def modes : List Mode := [.ordinary, .docs, .graph, .diagnostics, .fixtures, .structural,
  .execution, .structuralFirst, .structuralSecond, .executionFirst, .executionSecond, .cli,
  .environments, .buildPolicy, .lintDriver, .producers, .history, .selfLint,
  .selfAudit, .ruleExamples, .ruleExamplesFirst, .ruleExamplesSecond, .site]

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

/-- The Mathlib-dependent package: the standard's Mathlib examples (`Audit`), which adopts the
root `regula` package by relative path, as a Mathlib project would. Lake commands for it run in
its own directory, where its workspace is the one Lake loads. -/
def auditPackage : String := "audit"

private def lakeIn (dir : String) (args : Array String) : Command := ⟨"lake", args, dir⟩

/-- Ordinary acceptance records its accepted input identity here; the separately timed
documentation step refuses unless its own identity is equal. -/
def linkPath : String := "tmp/acceptance-link.json"

/-- The standard's Verso source: package directory, library and its render-only executable.
Both acceptance steps capture its sources and the package inputs its check reads, including the
sources of the Mathlib package that its library needs, in the linked identity; the documentation step also builds (elaborating every `lean` block where it is
written) and renders it, requires every anchor the rule registry and the documentation link, and
requires the checklist's rows to be exactly `Regula.checklistRows`. -/
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
      lake #["exe", "axiomGate", "--acceptance-link", linkPath, "--verso", versoStandard]]
  | .docs => [
      lake #["build", "docFenceAudit"],
      -- The Mathlib package's own fresh acceptance, as a Mathlib adopter of `regula` runs it:
      -- the standard's `lean` blocks import its modules, and the linked identity below brackets
      -- the sources they need.
      lakeIn auditPackage #["exe", "axiomGate"],
      lake #["exe", "docFenceAudit", "--acceptance-link", linkPath, "--verso", versoStandard]]
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
  | .structural => selftest #["--partition", "structural"] #["docFenceAudit", "freshChecker"]
  -- A shard of a partition: the partition's name, then the shard after `--shard`.
  | .structuralFirst =>
      selftest #["--partition", "structural", "--shard", "1/2"] #["docFenceAudit", "freshChecker"]
  | .structuralSecond =>
      selftest #["--partition", "structural", "--shard", "2/2"] #["freshChecker"]
  | .executionFirst => selftest #["--partition", "execution", "--shard", "1/2"]
  | .executionSecond => selftest #["--partition", "execution", "--shard", "2/2"]
  | mode => selftest (#["--partition"] ++ ((arguments mode).drop 1).toArray)

/-- Every mode schedules actual work rather than accepting an empty campaign. -/
theorem commands_nonempty (mode : Mode) : commands mode ≠ [] := by
  cases mode <;> simp [commands, ruleExampleShard, selftest]

/-- Interpret sequentially; a nonzero process exit raises before any success report.
No theorem here purports to prove the OS's process execution or signal delivery. -/
def execute (command : Command) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := command.program, args := command.args, cwd := some command.dir,
    stdin := .null, stdout := .inherit, stderr := .inherit }
  let exit ← child.wait
  if exit != 0 then
    throw <| IO.userError s!"{command.program} {command.args} in {command.dir} failed ({exit})"

private def usage : String :=
  "usage: scripts/verify.sh [docs | serialized-graph | site | diagnostics \
    [fixtures|structural [1/2|2/2]|execution [1/2|2/2]|cli|environments|build-policy|\
    lint-driver|producers|history|self-lint|self-audit|rule-examples [1/2|2/2]]]"

/-- The earlier verdict an attempt of `mode` invalidates, with the constant text recording it
as incomplete. -/
def invalidated : Mode → Option (String × String)
  | .ordinary => some (linkPath, "{\"schemaVersion\":1,\"status\":\"incomplete\"}\n")
  | .ruleExamples =>
      some ("tmp/rule-examples.json", "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")
  | .ruleExamplesFirst =>
      some (shardEvidence 1, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")
  | .ruleExamplesSecond =>
      some (shardEvidence 2, "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n")
  | _ => none

/-- The package adopters require stays dependency-free: its lock manifest records no package. Lake
refuses to load a workspace whose configuration requires a package that the lock manifest does not
record, so an accepted build of the root package with such a manifest requires nothing, and
requiring `regula` adds only `regula` to an adopter's `lake-manifest.json`. The Mathlib-dependent
package in `audit/` records its own pins. -/
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
  if let some (path, text) := invalidated selection.val then
    IO.FS.createDirAll "tmp"
    IO.FS.writeFile path text
  if selection.val == .site then
    if ← System.FilePath.pathExists siteOutput then IO.FS.removeDirAll siteOutput

/-- Cold-start driver; all builds and checks stay within the inherited outer deadline. -/
def run (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  if selection.val == .ordinary then
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "lake-manifest.json"))
    unless dependencyFree manifest do
      throw <| IO.userError "lake-manifest.json records a dependency: the regula package must \
        require nothing beyond the Lean toolchain (a Mathlib-dependent module belongs in audit/)"
  for command in [({ program := "git", args := #["diff", "--check"] } : Command),
      { program := "git", args := #["diff", "--cached", "--check"] },
      { program := "shellcheck", args := #["scripts/verify.sh", "scripts/provision.sh"] }] ++
          commands selection.val do
    execute command
  IO.println (match selection.val with
    | .ordinary => "local verification: PASS (ordinary mechanical acceptance commands completed; \
      semantic review is separate; run `scripts/verify.sh docs` for documentation)"
    | .docs => "documentation verification: PASS (the Mathlib example package accepted fresh; \
      every docs/ Lean fence and every lean block of the Verso standard, which built fresh and \
      rendered; inputs equal the accepted ordinary inputs)"
    | .graph => "serialized-graph diagnostic: PASS (not ordinary verification)"
    | .site => "site build and check: PASS (rule-reference artifact in _site; separate from \
      acceptance; publication is verified after deployment)"
    | _ => "diagnostic qualification: PASS (selected scope only; not ordinary verification)")

end RegulaVerification

/-- Standalone cold-start entrypoint; invoke through the timed `scripts/verify.sh`, which
first runs it with the private `--begin-attempt` protocol flag before setup. -/
def main : List String → IO Unit
  | "--begin-attempt" :: args => RegulaVerification.beginAttempt args
  | args => RegulaVerification.run args
