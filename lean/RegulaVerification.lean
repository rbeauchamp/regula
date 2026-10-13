import Lean

/-! # Cold-start verification driver

Cold-start verification plan and operational interpreter. This module imports only
the pinned toolchain, so it can run before any root-package artifacts exist. Argument
selection has soundness and round-trip proofs; the interpreter consumes its proof-bearing
selection. Recipes name Lake targets, not a source-file census. The interpreter schedules every
command of the selected recipe (`inOrder_append_beside`), starts a command only while every end
known so far passed, waits for each command it started, and reports success only when `passed`
accepts how each scheduled command and each prebuild ended (`passed_covers`). The first
acceptance step makes its builds in a private copy of the project that this driver makes, and
the acceptance gate audits that copy (`makeCopy`). That step first builds what the gate audits
and runs (`prebuild`), then runs the gate beside the rest of the step (`beside`), whose commands
it starts at low scheduling priority (`Priority`).
Process effects remain trusted IO under the shell's single 420-second process-group deadline. -/
namespace RegulaVerification

/-- The number of shards of the self-test's lint-driver partition, which
`Regula.Checker.LintQualification.shards` states for the self-test. This module imports only the
toolchain, so it cannot read that; the self-test refuses a shard it does not have. -/
def lintDriverShards : Nat := 5

/-- The number of shards of the operational self-audit, which
`Regula.Qualification.SelfAudit.shards` states for the campaign. This module imports only the
toolchain, so it cannot read that; `qualify` refuses a shard it does not have. -/
def selfAuditShards : Nat := 4

/-- The number of shards of the self-test's structural partition, which
`Regula.Checker.CheckerSelftest.structuralShards` states for the self-test; the self-test refuses
a shard it does not have. -/
def structuralShards : Nat := 5

/-- The number of shards of the self-test's execution partition, which
`Regula.Checker.CheckerSelftest.executionShards` states for the self-test; the self-test refuses
a shard it does not have. -/
def executionShards : Nat := 4

/-- The number of shards of each of the self-test's fixtures, cli, environments and build-policy
partitions, which `Regula.Checker.SelftestArguments.Partition.shards` states for the self-test; the
self-test refuses a shard it does not have. -/
def fixturesShards : Nat := 5

@[inherit_doc fixturesShards]
def cliShards : Nat := 6

@[inherit_doc fixturesShards]
def environmentsShards : Nat := 6

@[inherit_doc fixturesShards]
def buildPolicyShards : Nat := 3

/-- The number of shards of the rule-example corpus (`Regula.Qualification.RuleExamples.check`
selects any `K/N`), each a required check of CI with its own evidence file (`shardEvidence`). -/
def ruleExampleShards : Nat := 3

/-- A group of qualification controls that neither the self-test's partitions nor another mode
runs, each run under the deadline of its own `diagnostics` invocation. -/
inductive Group where
  /-- `qualify input-inventory`: root and Markdown inventory faults injected during the checker's
  own build. -/
  | inputInventory
  /-- `qualify environments`: this repository's claimed environments and their mutations. -/
  | environmentCensus
  /-- `qualify acceptance-snapshots history`: history refusal and restoration. -/
  | snapshotHistory
  /-- `qualify acceptance fences`, the `dependencies` and `git-status` snapshot groups,
  `receipt-boundaries`, `prep-measure` and `enumeration`. -/
  | acceptanceControls
  /-- `qualify documentation-dependencies`, `configuration-capture`, `verso-recorded-paths` and
  `copy-relocation`. -/
  | documentationControls
  /-- The self-test's focused native-adopter, combined-snapshot and policy-transport controls. -/
  | focusedControls
  /-- The self-test's focused policy-domain controls: the policy transport and the public paths. -/
  | policyDomain
  /-- `qualify enumeration-failure`: a failed read of a directory, injected through device-mapper on
  a GitHub-hosted Linux runner; anywhere else it refuses as unsupported. -/
  | enumerationFailure
  /-- `qualify readers`: no declaration of a module of a package of the repository refers to
  Lean's directory readers. It builds the modules of each package with Lake, as the other modes
  build, so Lake can update or fetch a dependency there. It runs after provisioning and after the
  website sources are generated. -/
  | readers
  deriving DecidableEq

/-- The name of the group after `diagnostics`. -/
def Group.label : Group → String
  | .inputInventory => "input-inventory"
  | .environmentCensus => "environment-census"
  | .snapshotHistory => "snapshot-history"
  | .acceptanceControls => "acceptance-controls"
  | .documentationControls => "documentation-controls"
  | .focusedControls => "focused-controls"
  | .policyDomain => "policy-domain"
  | .enumerationFailure => "enumeration-failure"
  | .readers => "readers"

/-- Every group once. -/
def Group.all : List Group :=
  [.inputInventory, .environmentCensus, .snapshotHistory, .acceptanceControls,
    .documentationControls, .focusedControls, .policyDomain, .enumerationFailure, .readers]

/-- Closed vocabulary of supported verification invocations. -/
inductive Mode where
  /-- No argument: the first acceptance step, which makes a private copy of the project, builds
  the acceptance executables and the claimed surfaces of the root package there, runs the
  registry checks and combined qualification, and audits those surfaces in that copy; the audit
  runs beside the rest of the step once what it audits is built (`beside`). -/
  | ordinary
  /-- `docs`: the second acceptance step: the rule-ID check of every tracked Markdown document,
  the checks C1 to C8 of their prose with the baseline (checks B1 and B2, of which B2 reads the
  Git history) and the check of the vocabulary `CONTEXT.md` (check C9), with the controls of
  these checks, the fresh acceptance of the `audit/` package whose modules the standard's
  examples import, then
  the documentation audit and the Verso standard's build and render, refused unless its inputs
  have the content identity the first step recorded. The audit reuses the build output that the
  first step left only as `Regula.Checker.BuildReuse.reuse` decides from the record of it
  (`Copy.recordBuild`), and builds in a copy with no build output otherwise. -/
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
  /-- `diagnostics structural INDEX/5`: one of the structural partition's shards, `index` counted
  from 0 and `INDEX` from 1. -/
  | structuralShard (index : Fin structuralShards)
  /-- `diagnostics execution INDEX/4`: one of the execution partition's shards, `index` counted
  from 0 and `INDEX` from 1. -/
  | executionShard (index : Fin executionShards)
  /-- `diagnostics fixtures INDEX/5`: one of the fixtures partition's shards, `index` counted from
  0 and `INDEX` from 1. -/
  | fixturesShard (index : Fin fixturesShards)
  /-- `diagnostics cli INDEX/6`: one of the cli partition's shards. -/
  | cliShard (index : Fin cliShards)
  /-- `diagnostics environments INDEX/6`: one of the environments partition's shards. -/
  | environmentsShard (index : Fin environmentsShards)
  /-- `diagnostics build-policy INDEX/3`: one of the build-policy partition's shards. -/
  | buildPolicyShard (index : Fin buildPolicyShards)
  /-- `diagnostics cli`: the self-test's command-line partition. -/
  | cli
  /-- `diagnostics environments`: the self-test's environments partition. -/
  | environments
  /-- `diagnostics build-policy`: the self-test's build-policy partition. -/
  | buildPolicy
  /-- `diagnostics lint-driver`: the self-test's `lake lint` driver partition. -/
  | lintDriver
  /-- `diagnostics lint-driver INDEX/5`: one of the lint-driver partition's shards, `index`
  counted from 0 and `INDEX` from 1. -/
  | lintDriverShard (index : Fin lintDriverShards)
  /-- `diagnostics producers`: the producers qualification campaign. -/
  | producers
  /-- `diagnostics history`: the history qualification campaign. -/
  | history
  /-- `diagnostics self-lint`: this repository's own `lake lint`. -/
  | selfLint
  /-- `diagnostics self-lint-default`: the root package's own `lake lint` on the default path, with
  the audit-build marker. -/
  | selfLintDefault
  /-- `diagnostics self-audit`: the operational self-audit of the excluded `Regula` library. -/
  | selfAudit
  /-- `diagnostics self-audit INDEX/4`: one of the self-audit's shards, `index` counted from 0 and
  `INDEX` from 1. -/
  | selfAuditShard (index : Fin selfAuditShards)
  /-- `diagnostics rule-examples`: the whole rule-example corpus in one run. -/
  | ruleExamples
  /-- `diagnostics rule-examples INDEX/3`: one of the corpus's shards, `index` counted from 0 and
  `INDEX` from 1. -/
  | ruleExamplesShard (index : Fin ruleExampleShards)
  /-- `diagnostics GROUP`: a group of qualification controls (`Group`). -/
  | diagnostic (group : Group)
  /-- `site`: build and check the rule-reference site artifact from the shards' evidence, then
  check what the website's renderers leave when they render and when they refuse a run without
  Lean's task manager. -/
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
  | .structuralShard index =>
      ["diagnostics", "structural", s!"{index.val + 1}/{structuralShards}"]
  | .executionShard index =>
      ["diagnostics", "execution", s!"{index.val + 1}/{executionShards}"]
  | .fixturesShard index => ["diagnostics", "fixtures", s!"{index.val + 1}/{fixturesShards}"]
  | .cliShard index => ["diagnostics", "cli", s!"{index.val + 1}/{cliShards}"]
  | .environmentsShard index =>
      ["diagnostics", "environments", s!"{index.val + 1}/{environmentsShards}"]
  | .buildPolicyShard index =>
      ["diagnostics", "build-policy", s!"{index.val + 1}/{buildPolicyShards}"]
  | .cli => ["diagnostics", "cli"]
  | .environments => ["diagnostics", "environments"]
  | .buildPolicy => ["diagnostics", "build-policy"]
  | .lintDriver => ["diagnostics", "lint-driver"]
  | .lintDriverShard index =>
      ["diagnostics", "lint-driver", s!"{index.val + 1}/{lintDriverShards}"]
  | .producers => ["diagnostics", "producers"]
  | .history => ["diagnostics", "history"]
  | .selfLint => ["diagnostics", "self-lint"]
  | .selfLintDefault => ["diagnostics", "self-lint-default"]
  | .selfAudit => ["diagnostics", "self-audit"]
  | .selfAuditShard index =>
      ["diagnostics", "self-audit", s!"{index.val + 1}/{selfAuditShards}"]
  | .ruleExamples => ["diagnostics", "rule-examples"]
  | .ruleExamplesShard index =>
      ["diagnostics", "rule-examples", s!"{index.val + 1}/{ruleExampleShards}"]
  | .diagnostic group => ["diagnostics", group.label]
  | .site => ["site"]
  | .mathlib => ["mathlib"]

/-- Every supported mode occurs once; the parser searches only this closed vocabulary. -/
def modes : List Mode := [.ordinary, .docs, .graph, .diagnostics, .fixtures, .structural,
  .execution, .cli, .environments, .buildPolicy, .lintDriver, .producers, .history, .selfLint,
  .selfLintDefault, .selfAudit, .ruleExamples, .site, .mathlib] ++
  (List.finRange structuralShards).map .structuralShard ++
  (List.finRange executionShards).map .executionShard ++
  (List.finRange fixturesShards).map .fixturesShard ++
  (List.finRange cliShards).map .cliShard ++
  (List.finRange environmentsShards).map .environmentsShard ++
  (List.finRange buildPolicyShards).map .buildPolicyShard ++
  (List.finRange lintDriverShards).map .lintDriverShard ++
  (List.finRange selfAuditShards).map .selfAuditShard ++
  (List.finRange ruleExampleShards).map .ruleExamplesShard ++ Group.all.map .diagnostic

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
  cases mode with
  | structuralShard index | executionShard index | fixturesShard index | cliShard index
    | environmentsShard index | buildPolicyShard index | lintDriverShard index
    | selfAuditShard index | ruleExamplesShard index => revert index; decide
  | diagnostic group => cases group <;> rfl
  | _ => rfl

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

/-- The Mathlib integration package (`MathlibAudit`): a Mathlib adopter of the root `regula`
package by relative path, holding the Mathlib-specific behaviour Regula supports. Only the
`mathlib` mode and the `readers` group of the `diagnostics` mode run Lake in it (`lake exe qualify
readers` builds its modules); no other mode loads its workspace, so no other mode needs Mathlib. -/
def mathlibPackage : String := "integration/mathlib"

private def lakeIn (dir : String) (args : Array String) : Command :=
  { program := "lake", args, dir }

/-- The workspace owner's assertion that the lakefiles are ordinary configuration, as the `lint`
driver reads it from its environment. The name is `Regula.Checker.Lint.ordinaryLakefilesVariable`,
written again here because this driver imports only the toolchain. -/
def ownerAssertion : Array (String × String) := #[("REGULA_ORDINARY_LAKEFILES", "1")]

/-- Ordinary acceptance records its accepted input identity here; the separately timed
documentation step refuses unless its own identity is equal. The driver puts the record here
only after `passed` accepted every command, before it removes its copy and before the success
line (`run`), so an accepted record here means
that every command of the step exited 0. The gate of a run records the identity in the pending
record of that run (`Copy.pending`), and that record becomes this one only by that promotion, so
a run that fails or is killed before then leaves this record incomplete. Before the promotion the
driver may add the record of the build output it left (`Copy.recordBuild`); it changes no other
field. -/
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
def shardEvidence (index : Nat) : String := s!"tmp/rule-examples-{index}of{ruleExampleShards}.json"

/-- The package of the Markdown checks: md4c's reader and the `regula-markdown` executable. It
requires only the md4c binding and the root package. -/
def markdownPackage : String := "markdown"

/-- The controls of the checks of Markdown prose (C1 to C8), of the vocabulary (C9) and of the
baseline (B1 and B2), relative to the Markdown package. -/
def proseControls : String := "../lean/Fixtures/ControlledProse"

/-- Rule-reference site artifact directory (the GitHub Pages upload). -/
def siteOutput : String := "_site"

/-- One of `ruleExampleShards` disjoint corpus shards, selected by rule position in the corpus,
`index` counted from 1. -/
private def ruleExampleShard (index : Nat) : List Command := [
  lake #["build", "axiomGate", "ruleExamples", "ruleExampleQualification", "qualify"],
  lake #["exe", "qualify", "--under-deadline", "rule-examples", "--evidence", shardEvidence index,
    "--shard", s!"{index}/{ruleExampleShards}"]]

/-- A checker self-test run with the `checkerSelftest` arguments `selection`. The first command
builds the self-test together with `axiomGate`, which the baseline build of every partition
names, and with the further targets `tools` of the selection's baseline, so Lake
schedules the jobs of these builds in one invocation; run one after the other, the gate's own
modules would start only once the self-test's last module is linked. That command selects
nothing: the self-test's baseline build still names and builds its targets, finds these built
and builds any it names that are not here. -/
private def selftest (selection : Array String) (tools : Array String := #[]) : List Command := [
  lake (#["build", "checkerSelftest", "axiomGate"] ++ tools),
  lake (#["exe", "checkerSelftest", "--build-bound"] ++ selection ++ #["--jobs", "4"])]

/-- The further targets the lint-driver controls read from the repository's build: the `lake lint`
driver, the `regula` command whose `init` they run, the corpus producer `ruleExamples` whose
marker one control runs, and the module `Regula.Linter` that their adopters import. -/
private def lintDriverTargets : Array String :=
  #["lint", "regula", "ruleExamples", "Regula.Linter"]

/-- The targets of the first acceptance step's build that its gate audits or runs: every target
the surface manifest `foundation_manifest.json` claims (`prebuildCovers`) and the gate's own
executable. The driver builds them first (`prebuild`), so the gate can start before the rest of
that build ends. -/
def gateTargets : List String :=
  ["RegulaPolicy", "RegulaVerification", "RegulaProvision", "RegulaQualification", "RegulaCore",
    "AuditApp", "auditApp", "axiomGate"]

/-- The other targets of the first acceptance step's build: the acceptance executables of the
documentation step and of the qualification controls, and the modules the step type-checks. -/
def otherTargets : List String :=
  ["docFenceAudit", "qualify",
    "+Regula.Checker.CheckerSelftest:olean", "+Regula.Checker.FreshChecker:olean",
    "+Regula.RegistryChecks:olean", "+Regula.Linter:olean", "+Regula.Checker.LintMain:olean",
    "+Regula.Checker.RuleExamples:olean", "+Regula.Checker.RuleExampleQualificationMain:olean",
    "+Regula.Cli.Main:olean", "+Regula.Release:olean", "+Regula.DiagnosticsGate:olean",
    "+Regula.RemovalControls:olean", "+Regula.CopyControls:olean", "+Regula.ProvisionControls:olean",
    "+Regula.Campaigns.Verification:olean", "+Regula.Campaigns.Diagnostics:olean"]

/-- A `qualify` selection under the driver's deadline. -/
private def qualify (selection : Array String) : Command :=
  lake (#["exe", "qualify", "--under-deadline"] ++ selection)

/-- The commands of a group: one build of what its controls run, then its selections one after
another. The `qualify` controls run `axiomGate`, `docFenceAudit` and `ruleExamples` from the
repository's build; the focused self-test controls run `axiomGate`, and the native-adopter
control's adopter imports `Regula.Linter`. -/
def Group.commands : Group → List Command
  | .inputInventory => [lake #["build", "axiomGate", "docFenceAudit", "ruleExamples", "qualify"],
      qualify #["input-inventory"]]
  | .environmentCensus => [lake #["build", "axiomGate", "qualify"],
      qualify #["environments", "--evidence", "tmp/environment-census.json"]]
  | .snapshotHistory => [lake #["build", "axiomGate", "qualify"],
      qualify #["acceptance-snapshots", "history"]]
  | .acceptanceControls => [
      lake #["build", "axiomGate", "docFenceAudit", "ruleExamples", "qualify"],
      qualify #["acceptance", "fences", "--evidence", "tmp/acceptance-fences.json"],
      qualify #["acceptance-snapshots", "dependencies"],
      qualify #["acceptance-snapshots", "git-status"],
      qualify #["receipt-boundaries"],
      qualify #["prep-measure"],
      qualify #["enumeration"]]
  | .documentationControls => [
      lake #["build", "axiomGate", "docFenceAudit", "ruleExamples", "qualify"],
      qualify #["documentation-dependencies"],
      qualify #["configuration-capture"],
      qualify #["verso-recorded-paths"],
      qualify #["copy-relocation"]]
  | .focusedControls => [lake #["build", "checkerSelftest", "axiomGate", "Regula.Linter"],
      lake #["exe", "checkerSelftest", "--native-adopter-only"],
      lake #["exe", "checkerSelftest", "--combined-snapshot-only"],
      lake #["exe", "checkerSelftest", "--policy-transport-only"]]
  | .policyDomain => [lake #["build", "checkerSelftest", "axiomGate", "Regula.Linter"],
      lake #["exe", "checkerSelftest", "--policy-domain-only"]]
  | .enumerationFailure => [lake #["build", "qualify"], qualify #["enumeration-failure"]]
  | .readers => [lake #["build", "qualify"], qualify #["readers"]]

/-- The targets whose modules `qualify observers` reads: each library of the package except
`Fixtures`, and `auditApp`, whose root `Main` is in no library. -/
def observerTargets : Array String :=
  #["Regula", "RegulaPolicy", "RegulaVerification", "RegulaProvision", "RegulaQualification",
    "RegulaCore", "AuditApp", "auditApp", "qualify"]

/-- The self-audit shard that also runs `qualify observers`: the fourth, whose audit was the
shortest of the four on the slower CI runners. -/
def observersShard : Fin selfAuditShards := ⟨3, by decide⟩

/-- Existing acceptance and diagnostic recipes, executed inside the outer deadline.
Qualification's private flag retains the already timed process group. `copy` is the root of the
copy that the first acceptance step builds in, and `pending` the pending record of that run,
which its gate writes (`makeCopy`); no other mode uses them. -/
def commands (copy pending : String) : Mode → List Command
  | .ordinary => [
      -- The build of the step, in the copy: the acceptance executables, the modules the step
      -- type-checks, and every claimed target of the root package, which the gate audits in
      -- this build output. The prebuild built the gate's targets before it (`prebuild_named`).
      lakeIn copy ("build" :: gateTargets ++ otherTargets).toArray,
      lakeIn copy #["env", "lean", "--run", "lean/Regula/RegistryChecks.lean"],
      lakeIn copy #["exe", "qualify", "--under-deadline", "combined"],
      -- Last, and from the repository root: the gate of the copy audits the copy, reads the
      -- linked documents of the checkout and writes the pending record of the run (`pending`).
      -- It runs beside the three commands above (`beside`).
      lake #["-d", copy, "exe", "axiomGate", "--acceptance-link", pending, "--verso",
          versoStandard, "--driver-copy", copy]]
  | .docs => [
      -- `axiomGate` too, which the check of the example of the root `README.md` below runs.
      lake #["build", "docFenceAudit", "axiomGate"],
      -- The controls of the checks C1 to C9, B1 and B2: each check accepts its positive controls
      -- and refuses the others, with the exact file, line and check at the start of each
      -- refusal. The controls of the base revision of check B2, of an entry with no document
      -- (check B1) and of `--write-baseline` are repositories that the run makes with Git in a
      -- temporary directory (`markdown/MarkdownMain.lean`).
      lakeIn markdownPackage #["exe", "regula-markdown", "--controls", proseControls],
      -- Every Markdown document Git tracks, read by md4c: a rule ID in prose that is not a link
      -- to its rule page is refused. A link of the root `README.md` to the rule-reference site
      -- that is not a stable address is refused. So is a root `README.md` whose `lean` block is
      -- not the module `markdown/Readme/Shortcut.lean`, or whose `text` block does not fit what
      -- `axiomGate --file` prints for that module in a new Lake project. So is a `CONTEXT.md`
      -- that is not the print of a vocabulary or that has a source path Git does not track
      -- (check C9). A finding of the checks C1 to C8 that the baseline `prose-baseline.json` does
      -- not permit is refused, and so is an entry of the baseline with no tracked Markdown
      -- document (check B1). A baseline with a new path, a larger number or a different class in
      -- relation to the base revision is refused, and so is the removal of the baseline (check
      -- B2). Check B2 reads the Git history: the base revision is the commit that the start of
      -- the run gives, in the variable `REGULA_PROSE_START` or as the merge base of `HEAD` and
      -- `origin/main`. The argument is the repository root, relative to the Markdown package.
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
  -- warning-free build. As the owner of both packages, the repository asserts that their lakefiles
  -- are ordinary configuration (`REGULA_ORDINARY_LAKEFILES=1`, which the driver reads only from
  -- its environment), so the driver can reuse ordinary build output when the plain-shape guard
  -- admits the workspace. The first command builds, in one Lake invocation, the `lint` driver,
  -- its worker `axiomGate` and the claimed targets (`gateTargets`), which `lake lint` otherwise
  -- builds one after another: Lake's lint dispatch builds the driver, then the driver its worker,
  -- then the audit its claimed build. That command selects nothing: each of those builds still
  -- runs and builds anything not built here.
  | .selfLint => [lake ("build" :: "lint" :: gateTargets).toArray,
      { lake #["lint"] with env := ownerAssertion },
      { lakeIn auditPackage #["lint"] with env := ownerAssertion }]
  -- The root package's run on the default path that an adopter gets, without the owner's
  -- assertion, so with the audit-build marker. The `audit/` package runs the same driver code, and
  -- its default path would only add the rebuild that made the old step exceed its limit.
  | .selfLintDefault => [lake #["lint"]]
  -- The self-audit, and the record of the removal check of each program of the package, with the
  -- check of `auditApp`'s `Main` (`qualify observers`), which reads the modules of
  -- `observerTargets`.
  | .selfAudit => [
      lake (#["build"] ++ observerTargets),
      lake #["exe", "qualify", "--under-deadline", "self-audit"],
      lake #["exe", "qualify", "--under-deadline", "observers"]]
  -- A shard of the self-audit: its modules of each list the campaign deals (`SelfAudit.selected`).
  -- The shard `observersShard` also runs `qualify observers`.
  | .selfAuditShard index =>
      lake (#["build"] ++
          if index == observersShard then observerTargets else #["Regula", "qualify"])
        :: lake #["exe", "qualify", "--under-deadline", "self-audit", "--shard",
          s!"{index.val + 1}/{selfAuditShards}"]
        :: if index == observersShard then
          [lake #["exe", "qualify", "--under-deadline", "observers"]]
        else []
  | .ruleExamples => [
      lake #["build", "axiomGate", "ruleExamples", "ruleExampleQualification", "qualify"],
      lake
          #["exe", "qualify", "--under-deadline", "rule-examples", "--evidence",
              "tmp/rule-examples.json"]]
  | .ruleExamplesShard index => ruleExampleShard (index.val + 1)
  | .diagnostic group => group.commands
  | .site => [
      lake #["build", "axiomGate", "ruleExampleQualification", "site"],
      lake
          (#["exe", "site", "build", "--out", siteOutput, "--evidence"] ++
              ((List.range ruleExampleShards).map (shardEvidence <| · + 1)).toArray),
      -- After the build, which builds the website package and generates the site's sources.
      lake #["exe", "site", "renderer-refusal"]]
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
  -- structural shard holds only the self-hosted positive, whose control runs `axiomGate` alone,
  -- so its build is the self-test and the gate; the other shards also run the other two.
  | .structuralShard index =>
      selftest #["--partition", "structural", "--shard", s!"{index.val + 1}/{structuralShards}"]
        (if index.val == 0 then #[] else #["docFenceAudit", "freshChecker"])
  | .executionShard index =>
      selftest #["--partition", "execution", "--shard", s!"{index.val + 1}/{executionShards}"]
  | .fixturesShard index =>
      selftest #["--partition", "fixtures", "--shard", s!"{index.val + 1}/{fixturesShards}"]
  -- The last cli shard also runs `qualify` and `site`, in the control of a process without Lean's
  -- task manager, so its build names them.
  | .cliShard index =>
      selftest #["--partition", "cli", "--shard", s!"{index.val + 1}/{cliShards}"]
        (if index.val + 1 == cliShards then #["qualify", "site"] else #[])
  | .environmentsShard index =>
      selftest #["--partition", "environments", "--shard",
        s!"{index.val + 1}/{environmentsShards}"]
  | .buildPolicyShard index =>
      selftest #["--partition", "build-policy", "--shard", s!"{index.val + 1}/{buildPolicyShards}"]
  -- The lint-driver controls also run the `lake lint` driver, `regula init` and the corpus
  -- producer `ruleExamples`, and their adopters import `Regula.Linter`, which their baseline
  -- names.
  | .lintDriver => selftest #["--partition", "lint-driver"] lintDriverTargets
  | .lintDriverShard index =>
      selftest #["--partition", "lint-driver", "--shard", s!"{index.val + 1}/{lintDriverShards}"]
        lintDriverTargets
  | mode => selftest (#["--partition"] ++ ((arguments mode).drop 1).toArray)

/-- Every mode schedules actual work rather than accepting an empty campaign. -/
theorem commands_nonempty (copy pending : String) (mode : Mode) :
    commands copy pending mode ≠ [] := by
  cases mode with
  | diagnostic group => cases group <;> simp [commands, Group.commands]
  | _ => simp [commands, ruleExampleShard, selftest]

/-- The first acceptance step runs its build, the registry checks and the combined qualification
in the copy, and the gate from the repository root: the gate is the last of its commands, and it
is the only command of the step that runs in the checkout. It runs beside the others
(`beside_prebuilt`). -/
theorem ordinary_places (copy pending : String) :
    (commands copy pending .ordinary).map (·.dir) = [copy, copy, copy, "."] := rfl

/-! ## The schedule of the first acceptance step

The gate of the first acceptance step reads only what it audits and runs: the claimed targets
and its own executable. So the driver builds those first, in the copy (`prebuild`), and then runs
the gate beside the rest of the step (`beside`): the step's build, which builds the targets the
prebuild did not, the registry checks and the combined qualification, one after another and at
low scheduling priority (`Priority`). Meanwhile the rest of the step's build writes the build
output of the other targets, and the gate reads that of its own targets, which the prebuild
completed. A claimed target the prebuild does not name refuses the step (`prebuildCovers`), so
two Lake processes cannot build one target at the same time. That Lake rebuilds
nothing the prebuild built, because each of its traces is unchanged, is Lake's behaviour, not a
theorem; the gate compares the `.olean` parts of every claimed module before and after its
inspections, so a change to one fails the audit (`Inspection.changedArtifact?`). The step's
commands are the same in each schedule (`inOrder_append_beside`), and every target of the
prebuild is a target of the step's build (`prebuild_named`). -/

/-- The targets a command builds: the arguments after `build` of a `lake build`, and none for any
other command. -/
def buildTargets (command : Command) : List String :=
  if command.program = "lake" ∧ command.args[0]? = some "build" then command.args.toList.drop 1
  else []

/-- Builds the driver runs in the copy before a mode's `commands`, at the driver's own priority.
They decide time, never results: each is a `lake build` (`prebuild_builds`), and every target one
names is named again by a build among those commands in the same directory (`prebuild_named`),
which builds whatever is missing. The first acceptance step builds the gate's targets, so the
gate can start before the rest of the step's build has ended. -/
def prebuild (copy : String) : Mode → List Command
  | .ordinary => [lakeIn copy ("build" :: gateTargets).toArray]
  | _ => []

/-- A prebuild only builds: it has a target, which `buildTargets` gives only to a `lake build`. -/
theorem prebuild_builds (copy : String) (mode : Mode) (command : Command)
    (h : command ∈ prebuild copy mode) : buildTargets command ≠ [] := by
  cases mode <;> simp [prebuild] at h
  subst h
  simp [buildTargets, lakeIn, gateTargets]

/-- A prebuild selects nothing: each target it names is a target of a build among the mode's own
commands, in the same directory, which runs to completion before any success report. -/
theorem prebuild_named (copy pending : String) (mode : Mode) (command : Command) (target : String)
    (h : command ∈ prebuild copy mode) (named : target ∈ buildTargets command) :
    ∃ later ∈ commands copy pending mode,
      later.dir = command.dir ∧ target ∈ buildTargets later := by
  cases mode <;> simp [prebuild] at h
  subst h
  refine ⟨_, List.mem_cons_self, rfl, ?_⟩
  simp only [buildTargets, lakeIn, List.toList_toArray, List.getElem?_toArray,
    List.getElem?_cons_zero, and_self, ite_true, List.drop_succ_cons] at named ⊢
  exact List.mem_append_left _ named

/-- How many of a mode's last `commands` run beside the others (`beside`). The first acceptance
step runs its gate so; every other mode runs its commands one after another. -/
def besideCount : Mode → Nat
  | .ordinary => 1
  | _ => 0

/-- The commands of `mode` that run one after another: all but its last `besideCount`. -/
def inOrder (copy pending : String) (mode : Mode) : List Command :=
  (commands copy pending mode).take ((commands copy pending mode).length - besideCount mode)

/-- The commands of `mode` that each run as a process of their own, started before `inOrder` and
joined after it: its last `besideCount`. -/
def beside (copy pending : String) (mode : Mode) : List Command :=
  (commands copy pending mode).drop ((commands copy pending mode).length - besideCount mode)

/-- The two groups are the mode's commands, each once and in their order, whatever `besideCount`
is: the schedule drops no command and adds none. -/
theorem inOrder_append_beside (copy pending : String) (mode : Mode) :
    inOrder copy pending mode ++ beside copy pending mode = commands copy pending mode :=
  List.take_append_drop _ _

/-- The command that runs beside the others is the gate of the copy, `lake -d COPY exe
axiomGate`, and a prebuild in `COPY` names `axiomGate` and every claimed target the gate builds
(`gateTargets`). That the prebuild has ended before the gate starts is the driver's order (`run`),
and that Lake then builds nothing for the gate is Lake's behaviour; neither is this theorem. -/
theorem beside_prebuilt (copy pending : String) (mode : Mode) (command : Command)
    (h : command ∈ beside copy pending mode) :
    command.program = "lake" ∧ command.dir = "." ∧
      command.args.toList.take 4 = ["-d", copy, "exe", "axiomGate"] ∧
        ∃ early ∈ prebuild copy mode, early.dir = copy ∧
          ∀ target ∈ gateTargets, target ∈ buildTargets early := by
  cases mode <;> simp [beside, besideCount, commands, ruleExampleShard, selftest] at h
  subst h
  refine ⟨rfl, rfl, rfl, _, List.mem_singleton_self _, rfl, fun target member => ?_⟩
  simpa [buildTargets, lakeIn] using member

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
  schedule can then take longer than the same commands one after another. -/
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

/-- The shared constructor's exact source, embedded by Lean before any root artifact exists.
Assumes: Lean v4.34.1 `Lean/Elab/BuiltinTerm.lean:437-445` elabIncludeStr reads this source at elaboration;
the pinned Lean interpreter executes it. There is no second tree-walk implementation. -/
def constructionSource : String := include_str "RegulaCore/CopyProgram.lean"

/-- Run the shared construction source's entrypoint (`Construction.sourceMain`) with `args` before
cold artifacts exist, and decode the JSON it prints; `what` names the observation in an error.

Assumes: Lean v4.34.1 `IO.Process.output` supplies stdin and waits for the child
(`Init/System/IO.lean:1544-1557`);
`Lean/Util/Path.lean:85-86` identifies the interpreter. `--stdin --run`
(`Lean/Shell.lean:497-518,552-560`) executes the embedded source without a temporary file or
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

/-- Obtain the same Git environment policy as construction before cold artifacts exist.
The preliminary Git commands use this observer; Lake's own Git children remain outside it.
Construction.gitEnvironment names its pinned Git and OS assumptions. -/
private def gitEnvironment : IO (Array (String × Option String)) :=
  construction "Git environment" #["git-environment", "", ""]

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

/-- Start `command` at `priority` without waiting for it; `none`, with a report, when it could not
be started. It cannot raise. The child stays in the driver's process group, so the outer
deadline's kill reaches it. The inherited Lean search paths are removed, so a Lake command
resolves modules only through the workspace it runs in. `LAKE_ARTIFACT_CACHE` is `false`, so
Lake's artifact cache is off for each package whose own configuration does not turn it on. These
builds are not the checker's: the gate's own build of the claimed surface uses no artifact cache
whatever the configuration says (`Regula.Checker.Lake.Build.run`). An inherited
`REGULA_ORDINARY_LAKEFILES` is removed, so only a command that gives it (`ownerAssertion`) runs
with the owner's assertion. Each variable of the command's `env` is set before the shared Git
observer's removals. Git commands select command-scope core.symlinks=false before priority
wrapping; no Git policy is duplicated here. Lake-owned Git calls inherit the caller's environment.
Process execution
and signal delivery remain trusted. -/
def start (priority : Priority) (command : Command) :
    BaseIO (Option (IO.Process.Child stdio)) := do
  announce s!"start {priority.display}{command.display}"
  let spawn : IO (IO.Process.Child stdio) := do
    let isolated := if command.program == "git" then
        {command with args := #["-c", "core.symlinks=false"] ++ command.args}
      else command
    let (program, args) := isolated.launch priority
    let env := #[("GHCR_TOKEN", none), ("LEAN_PATH", none), ("LEAN_SRC_PATH", none),
      ("LAKE_ARTIFACT_CACHE", some "false"), ("REGULA_ORDINARY_LAKEFILES", none)] ++
      command.env.map fun (name, value) => (name, some value)
    let env ← if command.program == "git" then pure (env ++ (← gitEnvironment)) else pure env
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

/-- Run one command at `priority` to its end and return how it ended. It cannot raise. -/
def execute (priority : Priority) (command : Command) : BaseIO (Option UInt32) := do
  let started ← IO.monoMsNow
  let some child ← start priority command | return none
  let ended ← await command child
  let seconds := ((← IO.monoMsNow) - started) / 1000
  if passed [ended] then announce s!"done in {seconds} s: {command.display}"
  else announce s!"failed in {seconds} s ({describe ended}): {command.display}"
  return ended

/-- Run `commands` one after another, each at `priority`, and return how each ended. A command
runs only while everything that has ended so far passed: `known` holds the ends known before it.
A command after a failure is not run and has no end. It cannot raise. -/
def executeInOrder (priority : Priority) : (known : List (Option UInt32)) →
    (commands : List Command) → BaseIO (Ends commands)
  | _, [] => return ⟨[], rfl⟩
  | known, command :: rest => do
      let ended ← if passed known then execute priority command else pure none
      let later ← executeInOrder priority (ended :: known) rest
      return ⟨(command, ended) :: later.ends, by simp [later.complete]⟩

/-- Start each of `beside` as a process of its own, run `inOrder` one after another meanwhile,
then wait for each started command, and return how the commands of each side ended. Nothing is
started once something has failed (`known`); a command of `inOrder` does not see how a command
of `beside` ends, since it ends later. This is a `BaseIO` action, which has no exception, so
nothing can leave between a start and the wait for it: every started command is joined, also when
another command failed. The driver never kills a child, because that would not stop the child's
own descendants.

`priority` is the priority of the commands of `inOrder`. Each command of `beside` starts at the
driver's own priority, and the commands of `inOrder` then run at low priority, because they run
while it does. With no command in `beside`, they run at the priority the caller gives. That
priority is chosen once, before the first command of `inOrder`, and a command of `inOrder` keeps
it to its end, also after every command of `beside` ended. -/
def executeBeside (priority : Priority) : (known : List (Option UInt32)) →
    (beside inOrder : List Command) → BaseIO (Ends inOrder × Ends beside)
  | known, [], inOrder => return (← executeInOrder priority known inOrder, ⟨[], rfl⟩)
  | known, command :: rest, inOrder => do
      let started ← IO.monoMsNow
      let child ← if passed known then start .normal command else pure none
      let (others, later) ←
        executeBeside .low (if child.isSome then known else none :: known) rest inOrder
      let ended ← match child with
        | none => pure none
        | some child => do
            unless passed (others.statuses ++ later.statuses) do
              announce s!"a command failed; waiting for {command.display}"
            let waited ← IO.monoMsNow
            let ended ← await command child
            let now ← IO.monoMsNow
            announce s!"joined ({describe ended}) in {(now - started) / 1000} s, \
              {(now - waited) / 1000} s after the other commands ended: {command.display}"
            pure ended
      return (others, ⟨(command, ended) :: later.ends, by simp [later.complete]⟩)

/-! ## Places the driver removes

The driver removes two directories: the site artifact of an earlier run (`siteOutput`), only when
it is one that the site's build may replace (`siteRefusal`), and the scratch directory of the copy
it made (`Copy.remove`). `IO.FS.removeDirAll` reads the entries of
the path it is given, also when that path is a symbolic link to a directory, and then removes
the entries of the link's target. So the driver removes a directory only after `removal` decided
it from an observation that follows no link at the path.

**Outside this decision:** a process that replaces an entry below the directory with a link
while the removal runs. `IO.FS.removeDirAll` examines each entry and then opens it by its path,
so such a process can make it remove the entries of a different directory. The checker removes
its own scratch directories with the same function (`Regula.Scratch`).

The filesystem observer of the package's programs (`Regula.Filesystem`) decides its removals with
`Regula.Removal.removal`, which this module cannot import. `RegulaVerification.removal_shared`, in
the module `RegulaVerification.Decisions`, proves that `removal` is that decision for a
directory. -/

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

/-- The metadata of the entry at `path`, by a read that does not follow a symbolic link at `path`
itself: `System.FilePath.symlinkMetadata`, refused on Windows, where that function of Lean 4.34.1
follows such a link, as the package's observer refuses it (`Regula.Filesystem.observeMetadata`). -/
def entryMetadata (path : System.FilePath) : IO IO.FS.Metadata :=
  if System.Platform.isWindows then
    throw <| IO.userError s!"lstat {path}: refused on Windows, where Lean 4.34.1's \
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

The first acceptance step makes its builds in a private copy of the project, and the
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
  fails when the name exists, and the record by one that fails when the file exists. The gate of
  this run writes it, and this run promotes it (`run`). A record that no run
  promoted is removed with its scratch directory, by this run or by a reclamation. -/
  pending : System.FilePath
  /-- The handle that holds the shared lock of the scratch area while the copy is in use. -/
  lock : IO.FS.Handle
  /-- Each file `copyTree` wrote, by its path below `project` written with `/`. -/
  files : List String

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

/-- Make the copy of the project at the real path `root`, by the steps of
`Regula.Scratch.withScratch` in its order. When the lock of the checker's scratch area can be
taken exclusively, no scratch owner lives, and the marked directories are removed first
(`reclaim`). Then: take the shared lock of the area, create the ownership marker of a new name
exclusively, create the directory of that name, which must not exist, and copy the project into
its directory `project` (`copyTree`). So the checker's reclamation and that of a later driver
remove the directory of a driver that died, and remove none while this driver holds the lock.
The copy reserves an empty root `.lake`, excluding the original root's default build state.

After a reclamation the exclusive lock is converted to the shared one without an `unlock`
between them, as in `Regula.Scratch`. Safety does not depend on the conversion: `flock(2)` does
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
documentation step then builds what it needs. A rename makes the build output one that the
documentation step may reuse (`Copy.recordBuild`). -/
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

/-! ## The record of the build the step leaves

When the step passed and gave its build output to a project that had none (`Copy.adopt`), the
documentation step may use that build output instead of compiling the same modules again, but only
as `Regula.Checker.BuildReuse.reuse` decides from what the record says of it: the targets of the
step's build, the SHA-256 of every file of the copy, taken before any command ran in it, and the
SHA-256 of every file below `lib` and `ir` of the build output it moved. The record is the pending
record of the run's own gate with that `build` field added, before the driver promotes it to
`linkPath`. Nothing else of the step changes: no command, no result and no removal. A digest that
cannot be taken leaves the record without the field, and the documentation step then compiles
those modules itself. -/

/-- The SHA-256 of each of `paths`, each relative to `dir` and written with `/`, by the external
`shasum -a 256` run in `dir` on at most 200 paths at a time, each given as `./` and the path, since
`shasum` reads standard input for the operand `-`; for each file it prints the digest, two spaces
and the operand, and any other line in a path's place fails. It is
`Regula.Checker.AcceptanceLink.digests` written a second time, since this module imports only the
toolchain. It assumes the output of `shasum` that that function states. -/
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

/-- Each regular file below `lib` and `ir` of the build directory `build`, by its path relative
to `build` written with `/`. A directory missing there has none. -/
def buildFiles (build : System.FilePath) : IO (List String) := do
  let prefixLength := build.normalize.components.length
  let mut files := #[]
  for part in ["lib", "ir"] do
    unless (← place (build / part)) == .directory do continue
    for path in ← walkDirectory (build / part) do
      if (← entryMetadata path).type == .file then
        files := files.push ("/".intercalate (path.normalize.components.drop prefixLength))
  return files.toList

/-- Add the `build` field to the copy's pending record: the targets of the step's build, the
copy's digests `tree`, and the digests of the build output that `Copy.adopt` moved to `root`'s
`.lake/build`. The new record is written beside the pending one and renamed over it, so a failure
leaves the pending record as the gate wrote it; it is reported and is no error of the step. -/
def Copy.recordBuild (copy : Copy) (root : System.FilePath) (tree : List (String × String)) :
    BaseIO Unit := do
  let record : IO Unit := do
    let started ← IO.monoMsNow
    let build := root / ".lake" / "build"
    let artifacts ← digests build (← buildFiles build)
    let value ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile copy.pending))
    let value := value.setObjVal! "build" (Lean.Json.mkObj [
      ("targets", Lean.toJson (gateTargets ++ otherTargets)),
      ("tree", Lean.toJson tree), ("artifacts", Lean.toJson artifacts)])
    let written := copy.scratch / "acceptance-link.build.json"
    IO.FS.writeFile written (value.compress ++ "\n")
    IO.FS.rename written copy.pending
    announce s!"recorded the digests of {tree.length} files of the copy and {artifacts.length} \
      files of its build output in {(← IO.monoMsNow) - started} ms"
  if let .error error ← record.toBaseIO then
    announce s!"the record names no build output for the documentation step to reuse: {error}"

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

/-! ## The destinations the driver writes

The driver writes three kinds of file in the project's `tmp` directory: the acceptance link
(`linkPath`), the receipt of the whole rule-example corpus (`corpusEvidence`), and the export of
each of the corpus's shards (`shardEvidence`). It writes each by the rules of the destinations of
the package's programs (`Regula.Destination`), which this module cannot import, so the rules are
written a second time here:

- It finds the entry that a destination names before it makes anything, as the real path of its
  longest present prefix and the names below it, and stops when one of those names is `..`
  (`destinationAt`). So the entry that it checks is the one that it replaces.
- It replaces only nothing, an empty regular file, or a regular file whose text is a document of
  Regula of any kind (`regulaDocument`), by a read that follows no link at the destination
  (`ownershipRefusal`). Regula regenerates each of its documents, so replacing one loses nothing
  that a later run cannot make again.
- It makes a new file beside the destination and renames that file there (`writeDocument`), so it
  replaces the entry at the destination and does not write into the file that the entry names.

In the module `RegulaVerification.Decisions`, `regulaDocument_shared` proves that the driver's
identification of a document of Regula is `Regula.Destination.regulaDocument`, `plainNames_shared`
that its names below a present prefix are `Regula.Destination.plainNames`, and
`identifiesSiteBuild_shared` and `siteAssemblingMarker_shared` relate the site artifact that the
driver removes (`siteRefusal`) to the one that the site's build replaces. The module
`Regula.ProgramCheck.Verification` admits a write, a rename or a removal of a file in the driver
only at the places that it names, among them `writeDocument` and `promote`. -/

/-- The members that identify a kind of document: `Regula.Destination.Signature`. -/
abbrev Signature := List String × List (String × String)

/-- The signature of each kind of completed document: `Regula.Destination.completedSignatures`
(`regulaDocument_shared`). -/
def completedSignatures : List Signature :=
  [(["schemaVersion", "status", "mode", "diagnostics", "stages", "stagesCompleted", "complete",
      "stagesNotRun", "rules", "sourceTexts"], []),
    (["schemaVersion", "producerVersion", "toolchain", "sourceRevision", "rules"], []),
    (["schemaVersion", "status", "identity"], []),
    (["schema", "producer", "request", "payload"], []),
    (["receipt", "origins"], []),
    (["outcome", "schemaVersion", "selected", "completeCorpus", "checkerBefore", "checkerAfter",
      "records"], []),
    (["version", "checks", "documents"], []),
    (["status", "moduleSets", "modules", "roots", "coverage", "checks"],
      [("mode", "serializedGraph")]),
    (["schemaVersion", "examples"], []),
    (["attemptId", "schemaVersion", "status", "packets", "controls"], []),
    (["attemptId", "status", "group", "inputs", "records"], []),
    (["outcome", "equivalent", "totalMillis"], [])]

/-- The signature of each kind of mark: `Regula.Destination.markSignatures`
(`regulaDocument_shared`). -/
def markSignatures : List Signature :=
  [(["reason"], [("status", "incomplete")]),
    (["schemaVersion"], [("status", "incomplete")]),
    (["unresolved"], [("status", "incomplete"), ("mode", "serializedGraph")]),
    (["attempt", "rawDirectory"], [("outcome", "INCOMPLETE")]),
    (["phase"], [("outcome", "INCOMPLETE")]),
    (["equivalent"], [("outcome", "INCOMPLETE")])]

/-- Whether `value` is an object with the member `name`, whatever its value. -/
def has (value : Lean.Json) (name : String) : Bool :=
  (value.getObjVal? name).isOk

/-- Whether `value` is an object whose member `name` is the string `text`. -/
def holds (value : Lean.Json) (name text : String) : Bool :=
  (value.getObjValAs? String name).toOption == some text

/-- Whether `value` has the signature `signature`: it holds each member that the signature names
and each string value that it gives. -/
def hasSignature (value : Lean.Json) (signature : Signature) : Bool :=
  signature.1.all (has value) && signature.2.all fun member => holds value member.1 member.2

/-- Whether `value` is a document of Regula of some kind, completed (`completedSignatures`) or a
mark (`markSignatures`). It is `Regula.Destination.regulaDocument` (`regulaDocument_shared`). -/
def regulaDocument (value : Lean.Json) : Bool :=
  completedSignatures.any (hasSignature value) || markSignatures.any (hasSignature value)

/-- The name of a kind of entry in a reason to refuse a destination. -/
private def entryName : IO.FS.FileType → String
  | .dir => "a directory"
  | .file => "a regular file"
  | .symlink => "a symbolic link"
  | .other => "an entry that is not a directory, a regular file or a symbolic link"

/-- The reason to refuse writing at `path`, if there is one: something is at `path`, by a read that
follows no link at `path` itself (`entryMetadata`), and it is not a regular file that is empty or
whose text is a JSON document of Regula (`regulaDocument`). An error of that read other than the
absence of the entry is a reason too. It is `Regula.Destination.ownershipRefusal` written a second
time. -/
def ownershipRefusal (path : System.FilePath) : IO (Option String) := do
  let refuse (what : String) : Option String := some s!"{path} is {what}, not a document that \
    Regula wrote, so the run does not replace it"
  match ← (entryMetadata path).toBaseIO with
  | .error (.noFileOrDirectory ..) => return none
  | .error error => return some s!"{path} cannot be read without following a link ({error}), \
      so the run does not replace it"
  | .ok metadata =>
    unless metadata.type == .file do return refuse (entryName metadata.type)
    match ← (IO.FS.readBinFile path).toBaseIO with
    | .error error => return refuse s!"a regular file that cannot be read ({error})"
    | .ok bytes =>
      if bytes.isEmpty then return none
      let some text := String.fromUTF8? bytes | return refuse "a file that is not UTF-8 text"
      match Lean.Json.parse text with
      | .ok value => return if regulaDocument value then none else refuse "a JSON document"
      | .error _ => return refuse "a file that is not a JSON document"

/-- The names below the longest present prefix of a destination, as a write makes them, or `none`
when one of them is `..`: `Regula.Destination.plainNames` (`plainNames_shared`). -/
def plainNames (names : List String) : Option (List String) :=
  if names.contains ".." then none else some (names.filter fun name => name != "." && name != "")

/-- The entry that `path` names, found without making anything: the real path of the longest
prefix of its directory that is present, and the names below it (`plainNames`). It stops when a
name below the prefix is `..`, whose entry depends on what the run makes, when no name is left for
the entry, or when a prefix is there but cannot be resolved. It is `Regula.Destination.place`
written a second time. -/
def destinationAt (path : System.FilePath) : IO System.FilePath := do
  let path ← if path.isAbsolute then pure path else pure ((← IO.currentDir) / path)
  let components := path.components
  let below (real : System.FilePath) (names : List String) : IO System.FilePath :=
    match plainNames names with
    | some names@(_ :: _) =>
      pure (names.foldl (fun directory (name : String) => directory / name) real)
    | some [] => throw <| IO.userError s!"{path} names no file, so the run writes nothing there"
    | none => throw <| IO.userError s!"{path} has a `..` component below {real}, its longest \
        prefix that is present, so the entry that it names depends on what the run makes; the \
        run writes nothing there"
  for count in (List.range (components.length - 1)).reverse do
    let ancestor := System.mkFilePath (components.take (count + 1))
    let ancestor : System.FilePath := if ancestor.toString.isEmpty then ⟨"/"⟩ else ancestor
    match ← (IO.FS.realPath ancestor).toBaseIO with
    | .ok real => return ← below real (components.drop (count + 1))
    | .error (.noFileOrDirectory ..) =>
      match ← (entryMetadata ancestor).toBaseIO with
      | .error (.noFileOrDirectory ..) => continue
      | _ => throw <| IO.userError s!"{ancestor}, a prefix of {path}, is there but cannot be \
          resolved (a symbolic link whose target is absent), so the run writes nothing there"
    | .error error => throw <| IO.userError s!"{ancestor}, a prefix of {path}, cannot be resolved \
        ({error}), so the run writes nothing there"
  below ⟨"/"⟩ (components.drop 1)

/-- Write `text` at `path`: stop with nothing made or written when the entry at `path`
(`destinationAt`) holds a file that the run may not replace (`ownershipRefusal`). Otherwise make the
entry's directory, make a new file in it and rename that file to the entry. The new file's name is
`.regula-`, the process's id, a random number and `.pending`, and it is created only where no entry
is, so the write replaces the entry at `path` and does not write into the file that the entry
names. It removes the new file when it stops after making it. It is `Regula.Destination.write`
written a second time. -/
def writeDocument (path : System.FilePath) (text : String) : IO Unit := do
  let destination ← destinationAt path
  if let some reason ← ownershipRefusal destination then throw (IO.userError reason)
  let directory := destination.parent.getD "."
  IO.FS.createDirAll directory
  let random := (← IO.getRandomBytes 8).foldl (fun value byte => value * 256 + byte.toNat) 0
  let pending := directory / s!".regula-{← IO.Process.getPID}-{random}.pending"
  let handle ← IO.FS.Handle.mk pending .writeNew
  -- No `try`: its handler would be a closure of its own, which the removal check names apart.
  let written ← (handle.putStr text *> handle.flush *> IO.FS.rename pending destination).toBaseIO
  if let .error error := written then
    discard <| (IO.FS.removeFile pending).toBaseIO
    throw error

/-- Rename the file at `source`, a record that only this run has the path of, to `path`: stop with
nothing made or renamed when the entry at `path` (`destinationAt`) holds a file that the run may not
replace (`ownershipRefusal`); otherwise make the entry's directory and rename the record there. -/
def promote (source path : System.FilePath) : IO Unit := do
  let destination ← destinationAt path
  if let some reason ← ownershipRefusal destination then throw (IO.userError reason)
  IO.FS.createDirAll (destination.parent.getD ".")
  IO.FS.rename source destination

/-- The file that marks a directory that a build of the site is assembling:
`Regula.Destination.siteAssemblingMarker` (`siteAssemblingMarker_shared`). -/
def siteAssemblingMarker : String := ".regula-site-assembling"

/-- The members of the `build.json` of a site artifact whose presence identifies it, whatever
their values: `Regula.Destination.siteBuildMembers`. -/
def siteBuildMembers : List String := ["schemaVersion", "site", "producerVersion"]

/-- Whether `value` is the `build.json` of a site artifact: it holds each member of
`siteBuildMembers`, whatever its value (`identifiesSiteBuild_shared`). -/
def identifiesSiteBuild (value : Lean.Json) : Bool :=
  siteBuildMembers.all (has value)

/-- Whether a regular file is at `path`, by a read that follows no link at `path` itself. -/
def regularFile (path : System.FilePath) : BaseIO Bool := do
  match ← (entryMetadata path).toBaseIO with
  | .ok metadata => return metadata.type == .file
  | .error _ => return false

/-- The reason to refuse removing the site artifact at `out`, if there is one: something is at
`out`, by a read that follows no link at `out` itself, and it is not a directory that is empty,
that holds the marker of an assembly (`siteAssemblingMarker`), or that holds a `build.json` of an
artifact (`identifiesSiteBuild`), each a regular file. A directory that holds anything else, such
as the documentation of a repository, is thus not removed. It is
`Regula.Site.Build.artifactRefusal` written a second time. -/
def siteRefusal (out : System.FilePath) : IO (Option String) := do
  let refuse := some s!"{out} is not empty and holds neither a build.json of a site that Regula \
    built nor the marker {siteAssemblingMarker} of an assembly, so the attempt removes nothing"
  match ← (entryMetadata out).toBaseIO with
  | .error (.noFileOrDirectory ..) => return none
  | .error error => return some s!"{out} cannot be read without following a link ({error}), so \
      the attempt removes nothing"
  | .ok metadata =>
    unless metadata.type == .dir do return refuse
    if (← out.readDir).isEmpty then return none
    if ← regularFile (out / siteAssemblingMarker) then return none
    unless ← regularFile (out / "build.json") do return refuse
    match Lean.Json.parse (← IO.FS.readFile (out / "build.json")) with
    | .ok value => return if identifiesSiteBuild value then none else refuse
    | .error _ => return refuse

/-- The failure report: each command that did not end with exit status 0, with how it ended. -/
def report (ends : List (Command × Option UInt32)) : String :=
  "\n".intercalate ("verification failed:" :: ends.filterMap fun (command, ended) =>
    if passed [ended] then none else some s!"  {command.display}: {describe ended}")

private def usage : String :=
  "usage: scripts/verify.sh [docs | serialized-graph | site | mathlib | diagnostics \
    [fixtures [1/5..5/5]|structural [1/5..5/5]|execution [1/4..4/4]|cli [1/6..6/6]|\
    environments [1/6..6/6]|build-policy [1/3..3/3]|lint-driver [1/5..5/5]|producers|history|\
    self-lint|self-lint-default|self-audit [1/4..4/4]|rule-examples [1/3..3/3]|input-inventory|\
    environment-census|snapshot-history|acceptance-controls|documentation-controls|\
    focused-controls|policy-domain|enumeration-failure|readers]]\n\
  diagnostics readers builds the modules of each package with Lake, as the other modes build, so \
  Lake can update or fetch a dependency there; run it after provisioning (lean --run \
  lean/RegulaProvision.lean verso and mathlib) and ./scripts/verify.sh site"

/-- The receipt of the whole rule-example corpus, which `diagnostics rule-examples` writes and
which each attempt marks (`beginAttempt`). -/
def corpusEvidence : String := "tmp/rule-examples.json"

/-- The constant text that records rule-example evidence as incomplete before setup. -/
def setupMark : String := "{\"outcome\":\"INCOMPLETE\",\"phase\":\"setup\"}\n"

/-- The earlier verdicts an attempt of `mode` invalidates beside the corpus receipt
(`corpusEvidence`), which each attempt invalidates, each with the constant text recording it as
incomplete. Ordinary acceptance invalidates the accepted link, so it is not
accepted from then on unless a run promotes the pending record of its own gate to it. -/
def invalidated : Mode → List (String × String)
  | .ordinary => [(linkPath, incompleteLink)]
  | .ruleExamplesShard index => [(shardEvidence (index.val + 1), setupMark)]
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

/-- Whether the prebuild of the first acceptance step builds every target the surface manifest
claims (`prebuildCovers_iff`). The gate builds a claimed target that is not yet built itself,
and the rest of the step's build runs beside the gate in the same build output, so a claimed
target the prebuild does not name could be built by two Lake processes at once. The driver
refuses the step when this is `false`. -/
def prebuildCovers (manifest : Lean.Json) : Bool :=
  match claimedTargets manifest with
  | some targets => targets.all gateTargets.contains
  | none => false

/-- `prebuildCovers` accepts exactly a manifest of the shape `claimedTargets` reads all of whose
claimed targets are targets of the prebuild. -/
theorem prebuildCovers_iff (manifest : Lean.Json) :
    prebuildCovers manifest = true ↔
      ∃ targets, claimedTargets manifest = some targets ∧
        ∀ target ∈ targets, target ∈ gateTargets := by
  unfold prebuildCovers
  split
  · next targets h => simp [h, List.all_eq_true]
  · next h => simp [h]

/-- Begin an attempt: mark the corpus receipt (`corpusEvidence`) incomplete, whatever the
arguments, then invalidate the selected mode's earlier PASS or accepted link (`invalidated`), and
remove an earlier site artifact. Each mark is written as `writeDocument` writes, so it replaces
only nothing, an empty file or a document of Regula. `scripts/verify.sh` runs this
toolchain-only step before provisioning and before any checker is built, so a failed setup or
build cannot leave either in place. The site artifact is removed only when it is one that the
site's build may replace (`siteRefusal`) and a directory is at its own place (`removeOwn`): with
a symbolic link or a directory of something else at `_site` the attempt removes nothing. A
destination that the attempt may not replace keeps what it holds; the attempt marks the others,
and then stops with each reason.

An attempt that stops before this step, such as one with no `lean` to run, has run no code of its
own and leaves the earlier verdicts of its mode and the corpus receipt.
Assumes: each reader that admits one of those verdicts admits it only for the current inputs, so it
is the verdict for those inputs. `AcceptanceLink.require` admits the acceptance link (`linkPath`)
only when its identity is the digest of the current inputs. `Site.Build.admitShard` admits a shard
export (`shardEvidence`) only when it records the current sources of the checker
(`Site.Build.currentSources`), and then runs `ruleExampleQualification` on it. Only the attempt
of `diagnostics rule-examples` that writes the corpus receipt reads it, and that attempt marks it
here first. `Regula.Site.Deployment.gate` admits the site artifact (`siteOutput`) only for a clean
build of the commit it deploys. The gate of the diagnostics workflow reads the self-hosted digests
only from the artifacts of the jobs of its commit (`Regula.DiagnosticsGate.digestPath`). No reader
in this repository reads `tmp/environment-census.json` or `tmp/acceptance-fences.json`. -/
def beginAttempt (args : List String) : IO Unit := do
  let corpus ← (writeDocument corpusEvidence setupMark).toBaseIO
  let some selection := select args | throw <| IO.userError usage
  let mut refused : Array String := #[]
  if let .error error := corpus then refused := refused.push (toString error)
  for (path, text) in invalidated selection.val do
    if let .error error ← (writeDocument path text).toBaseIO then
      refused := refused.push (toString error)
  if selection.val == .site then
    let remove : IO Unit := do
      let out := (← IO.FS.realPath ".") / siteOutput
      if let some reason ← siteRefusal out then throw (IO.userError reason)
      removeOwn out
    if let .error error ← remove.toBaseIO then refused := refused.push (toString error)
  unless refused.isEmpty do throw <| IO.userError ("\n".intercalate refused.toList)

/-- Cold-start driver; all builds and checks stay within the inherited outer deadline. After the
preliminary checks and the mode's `prebuild`, it schedules every command of the mode
(`inOrder_append_beside`), starts one only while every end known so far passed, waits for each
one it started, and reports success only when `passed` accepts how every one of those commands
and of the prebuilds ended (`passed_covers`). The first acceptance step promotes the pending
record of its own gate to the accepted link only then, before the removal of its copy and before
the success line, and only when the record is an acceptance link and the file at `linkPath` is one
that the run may replace (`promote`). It refuses a surface manifest that claims a target its
prebuild does not build (`prebuildCovers`), makes its copy after the preliminary checks
(`makeCopy`), runs its prebuild and its commands for that copy (`ordinary_places`), gives the
copy's build output to a project that has none when the step passed (`Copy.adopt`) and then
records it (`Copy.recordBuild`), and removes the copy in each case (`Copy.remove`). -/
def run (args : List String) : IO Unit := do
  let some selection := select args | throw <| IO.userError usage
  if selection.val == .ordinary then
    let manifest ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "lake-manifest.json"))
    unless dependencyFree manifest do
      throw <| IO.userError "lake-manifest.json records a dependency: the regula package must \
        require nothing beyond the Lean toolchain (a Mathlib-dependent module belongs in \
        integration/mathlib/)"
    let surfaces ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "foundation_manifest.json"))
    unless prebuildCovers surfaces do
      throw <| IO.userError s!"foundation_manifest.json claims a target that the prebuild of \
        the first acceptance step does not build, or its surfaces cannot be read: the gate would \
        build that target beside the rest of the step's build; add it to \
        RegulaVerification.gateTargets (the prebuild builds {gateTargets})"
  let early ← executeInOrder .normal []
    [({ program := "git", args := #["diff", "--check"] } : Command),
      { program := "git", args := #["diff", "--cached", "--check"] },
      { program := "shellcheck", args := #["scripts/verify.sh", "scripts/provision.sh"] }]
  let root ← IO.FS.realPath "."
  let copy ← if selection.val == .ordinary && passed early.statuses then
      some <$> makeCopy root
    else pure none
  -- The digests of the copy's files, before any command runs in it (`Copy.recordBuild`).
  let tree ← match copy with
    | none => pure none
    | some copy => do
      match ← (digests copy.project copy.files).toBaseIO with
      | .ok tree => pure (some tree)
      | .error error =>
          announce s!"could not take the digests of the copy's files: {error}"
          pure none
  let place := (copy.map (·.project.toString)).getD "."
  let pending := (copy.map (·.pending.toString)).getD ""
  let prebuilt ← executeInOrder .normal early.statuses (prebuild place selection.val)
  let (others, gates) ← executeBeside .normal (early.statuses ++ prebuilt.statuses)
    (beside place pending selection.val) (inOrder place pending selection.val)
  let all := ((early.append prebuilt).append others).append gates
  if let some copy := copy then
    -- The pending record is in the scratch directory of the copy, so the promotion is before
    -- the removal of the copy, which follows in each case.
    try
      if passed all.statuses then
        if (← copy.adopt root) then
          if let some tree := tree then copy.recordBuild root tree
        promote copy.pending linkPath
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
      fresh; every docs/ Lean fence and every lean block of the Verso standard, which built in \
      this run and rendered, against root-package build output compiled from files equal to \
      those checked: in this run, in a copy with no earlier build output or, where the \
      docFenceAudit line says so, partly by the first acceptance step in such a copy of its own, \
      every SHA-256 equal, and the rest in this run against those artifacts; every rule ID in the prose `Regula.Prose` reads in the rendered \
      standard links to its rule page; inputs equal the accepted ordinary inputs)"
    | .graph => "serialized-graph diagnostic: PASS (not ordinary verification)"
    | .site => "site build and check: PASS (rule-reference artifact in _site, and the renderers' \
      destinations after a render and a run refused without Lean's task manager; separate from \
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
