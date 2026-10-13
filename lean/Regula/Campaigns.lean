import Regula.Qualification.Command
import Regula.Checker.SelftestArguments

/-! # The inventory of campaigns

Every campaign the repository's checking programs accept, and the workflow job that runs it or the
reason no job does. A campaign is an invocation of `./scripts/verify.sh` (`Campaign.verify`, one
for each mode of `RegulaVerification`), a selection of `lake exe qualify` (`Campaign.qualify`, one
for each form of `Regula.Qualification.Command`, `form`) or a campaign of `lake exe checkerSelftest`
(`Campaign.selftest`, `SelftestCampaign`). `all` lists them, and it holds every form of `qualify`
(`qualify_mem_all`) and every campaign of the self-test (`selftest_mem_all`). `Job.invocations`
states the `verify.sh` invocations each workflow job runs, and `runsOf` the `qualify` and
`checkerSelftest` campaigns each invocation runs.

`covered_all`, which the kernel checks when this module builds, states that each campaign of
`all` runs in some job and has no reason (`reason`), or runs in none and has a reason whose
condition holds: the campaigns it names run (`Reason.holds`). The contributor guide shows `table`,
the campaigns no job runs with their reasons, which `Regula.RegistryChecks` requires verbatim.

Proved elsewhere: `Regula.Campaigns.Verification` proves that the `verify.sh` invocations here
are exactly those the verification driver accepts and that `runsOf` gives the `qualify` and
`checkerSelftest` commands the driver runs for each; `Regula.Campaigns.Diagnostics` proves that
the campaign list of the diagnostics workflow (`Regula.DiagnosticsGate.campaigns`) is that of
`Job.diagnosticsCampaign`. The `#guard` below evaluates, when this module builds, that the
self-test reads each campaign's command line as that campaign.

Checked when acceptance runs: `Regula.RegistryChecks` reads each job's `verify.sh` steps from its
workflow file and requires them to be `Job.invocations` (`Job.workflowRefusal`).

Trusted, not proved: that GitHub runs those steps when their triggers and `if:` say, and the
readings behind `Reason.within`, `Reason.together` and
`Reason.worker`: that the controls of the campaign not run are among those of the campaigns
named, and behind `Reason.partly`: that its text names the rest of them. -/
namespace Regula.Campaigns

open Regula.Qualification Regula.Checker.SelftestArguments

/-- The form of a `qualify` selection: the selection with each of its free parameters (a path, a
shard, a rule, a module or a source) replaced by the placeholder the usage shows. -/
def form : Command → Command
  | .ruleExamples _ => .ruleExamples "PATH"
  | .ruleExamplesRules _ _ => .ruleExamplesRules "PATH" ["RULE", "..."]
  | .ruleExamplesShard _ _ => .ruleExamplesShard "PATH" "K/N"
  | .producersExport _ => .producersExport "PATH"
  | .selfAuditShard _ => .selfAuditShard "K/4"
  | .selfAuditModule _ _ => .selfAuditModule "MODULE" "SOURCE"
  | .selfAuditRulesModule _ => .selfAuditRulesModule "MODULE"
  | .copyRelocationLoad _ _ => .copyRelocationLoad "PROJECT" "COPIES"
  | .copyRelocationGit _ => .copyRelocationGit "SCRATCH"
  | .environments _ => .environments "PATH"
  | .acceptance group _ => .acceptance group "PATH"
  | .enumerationCopy _ _ => .enumerationCopy "SOURCE" "TARGET"
  | command => command

/-- Every form of `qualify` selection once. -/
def qualifyForms : List Command :=
  [.registry, .native, .combined, .uniqueConstants, .nativeLauncher, form (.ruleExamples ""),
    form (.ruleExamplesRules "" []), form (.ruleExamplesShard "" ""), .producers,
    form (.producersExport ""), .producersCombined, .history, .selfAudit, form (.selfAuditShard ""),
    form (.selfAuditModule "" ""), form (.selfAuditRulesModule ""), form (.environments ""),
    form (.acceptance .fences ""), .acceptanceSnapshots .dependencies,
    .acceptanceSnapshots .history, .acceptanceSnapshots .gitStatus, .acceptanceSnapshots .all,
    .prepMeasure, .documentationDependencies, .inputInventory, .receiptBoundaries, .observers,
    .closureEvidence, .configurationCapture, .versoRecordedPaths, .copyRelocation,
    form (.copyRelocationLoad "" ""), form (.copyRelocationGit ""), .fenceEvidence, .frozenExits,
    .documentationSource, .documentationSourceReadOnly, .enumeration,
    form (.enumerationCopy "" ""), .enumerationFailure, .readers]

/-- Every selection's form is listed. -/
theorem form_mem (command : Command) : form command ∈ qualifyForms := by
  cases command with
  | acceptance group => cases group; simp [form, qualifyForms]
  | acceptanceSnapshots group => cases group <;> simp [form, qualifyForms]
  | _ => simp [form, qualifyForms]

/-- A campaign of `checkerSelftest`. -/
inductive SelftestCampaign where
  /-- A focused control, selected by its flag alone. -/
  | focused (control : Focused)
  /-- The internal transcript worker. -/
  | transcriptWorker
  /-- The suite with no tier option: the default tier. -/
  | defaultTier
  /-- `--structural-only`. -/
  | structuralOnly
  /-- `--build-bound`: every partition. -/
  | buildBound
  /-- `--build-bound --partition P`. -/
  | partition (partition : Partition)
  /-- `--build-bound --partition P --shard K/N`: shard `index` of `partition`, counted from 0. -/
  | partitionShard (partition : Partition) (index : Fin partition.shards)
  deriving DecidableEq, Repr

/-- The campaign of a selection of the self-test; none for `--help`, which runs nothing. -/
def SelftestCampaign.ofSelection : Selection → Option SelftestCampaign
  | .focused control => some (.focused control)
  | .transcriptWorker .. => some .transcriptWorker
  | .suite options =>
    if options.help then none
    else if options.structuralOnly then some .structuralOnly
    else match options.partition, options.shard with
      | some selected, none => some (.partition selected)
      | some selected, some spec => (shardOf? selected.shards spec).map (.partitionShard selected)
      | none, _ => some (if options.buildBound then .buildBound else .defaultTier)

/-- The command line of the campaign: that of the verification driver (`--jobs 4` for the suite),
and placeholders for the transcript worker's arguments. -/
def SelftestCampaign.arguments : SelftestCampaign → List String
  | .focused control => [control.flag]
  | .transcriptWorker => ["--transcript-worker", "MODULE", "SOURCE", "REJECT", "OUT"]
  | .defaultTier => ["--jobs", "4"]
  | .structuralOnly => ["--structural-only", "--jobs", "4"]
  | .buildBound => ["--build-bound", "--jobs", "4"]
  | .partition selected => ["--build-bound", "--partition", selected.label, "--jobs", "4"]
  | .partitionShard selected index =>
      ["--build-bound", "--partition", selected.label, "--shard",
        s!"{index.val + 1}/{selected.shards}", "--jobs", "4"]

/-- The shards of `partition`, in order. -/
def shardsOf (partition : Partition) : List SelftestCampaign :=
  (List.finRange partition.shards).map (.partitionShard partition)

/-- Every campaign of the self-test once. -/
def selftestCampaigns : List SelftestCampaign :=
  Focused.all.map .focused ++ [.transcriptWorker, .defaultTier, .structuralOnly, .buildBound] ++
    Partition.all.map .partition ++ Partition.all.flatMap shardsOf

/-- Every campaign of the self-test is listed. -/
theorem selftest_mem (campaign : SelftestCampaign) : campaign ∈ selftestCampaigns := by
  cases campaign with
  | focused control => simp [selftestCampaigns, Focused.all_complete]
  | partition partition => simp [selftestCampaigns, Partition.all_complete]
  | partitionShard partition index =>
    simp only [selftestCampaigns, List.mem_append, List.mem_flatMap]
    exact .inr ⟨partition, Partition.all_complete partition, by simp [shardsOf]⟩
  | _ => simp [selftestCampaigns]

-- The self-test reads each campaign's command line as that campaign: its parser is evaluated
-- here, at build time, over every campaign, since the kernel cannot reduce the well-founded
-- string functions it uses.
#guard selftestCampaigns.all fun campaign =>
  match Selection.parse campaign.arguments with
  | .ok selection => SelftestCampaign.ofSelection selection == some campaign
  | .error _ => false

/-- A campaign. -/
inductive Campaign where
  /-- `./scripts/verify.sh ARGUMENTS`. -/
  | verify (arguments : List String)
  /-- `lake exe qualify` with a selection of this form (`form`). -/
  | qualify (command : Command)
  /-- `lake exe checkerSelftest` with the command line of this campaign. -/
  | selftest (campaign : SelftestCampaign)
  deriving DecidableEq, Repr

/-- How the guide names a campaign: its command line. -/
def Campaign.spelling : Campaign → String
  | .verify arguments => " ".intercalate ("./scripts/verify.sh" :: arguments)
  | .qualify command => " ".intercalate ("lake exe qualify" :: command.arguments)
  | .selftest campaign => " ".intercalate ("lake exe checkerSelftest" :: campaign.arguments)

/-- The invocations `./scripts/verify.sh NAME K/N` of the `count` shards of `name`, in order. -/
def shardInvocations (name : String) (count : Nat) : List (List String) :=
  (List.range count).map fun index => ["diagnostics", name, s!"{index + 1}/{count}"]

/-- The groups of qualification controls that `./scripts/verify.sh diagnostics GROUP` runs. -/
def groups : List String :=
  ["input-inventory", "environment-census", "snapshot-history", "acceptance-controls",
    "documentation-controls", "focused-controls", "policy-domain", "enumeration-failure",
    "readers"]

/-- Every invocation of `./scripts/verify.sh`, in the order of the driver's modes
(`Regula.Campaigns.Verification.verifyInvocations_eq`). -/
def verifyInvocations : List (List String) :=
  [[], ["docs"], ["serialized-graph"], ["diagnostics"], ["diagnostics", "fixtures"],
    ["diagnostics", "structural"], ["diagnostics", "execution"], ["diagnostics", "cli"],
    ["diagnostics", "environments"], ["diagnostics", "build-policy"],
    ["diagnostics", "lint-driver"], ["diagnostics", "producers"], ["diagnostics", "history"],
    ["diagnostics", "self-lint"], ["diagnostics", "self-lint-default"],
    ["diagnostics", "self-audit"], ["diagnostics", "rule-examples"], ["site"], ["mathlib"]] ++
  shardInvocations "structural" Partition.structural.shards ++
  shardInvocations "execution" Partition.execution.shards ++
  shardInvocations "fixtures" Partition.fixtures.shards ++
  shardInvocations "cli" Partition.cli.shards ++
  shardInvocations "environments" Partition.environments.shards ++
  shardInvocations "build-policy" Partition.buildPolicy.shards ++
  shardInvocations "lint-driver" Partition.lintDriver.shards ++
  shardInvocations "self-audit" 4 ++ shardInvocations "rule-examples" 3 ++
  groups.map (["diagnostics", ·])

/-- The self-test campaign of `./scripts/verify.sh diagnostics NAME K/N`. -/
def partitionShardOf (name spec : String) : List Campaign :=
  match Partition.parse name with
  | none => []
  | some partition =>
    match (List.finRange partition.shards).find?
        (fun index => s!"{index.val + 1}/{partition.shards}" == spec) with
    | some index => [.selftest (.partitionShard partition index)]
    | none => []

/-- The `qualify` and `checkerSelftest` campaigns an invocation of `./scripts/verify.sh` runs, in
order (`Regula.Campaigns.Verification.runsOf_commands`). -/
def runsOf : List String → List Campaign
  | [] => [.qualify .combined]
  | ["diagnostics"] => [.selftest .buildBound]
  | ["diagnostics", "producers"] => [.qualify .producers]
  | ["diagnostics", "history"] => [.qualify .history]
  | ["diagnostics", "self-audit"] => [.qualify .selfAudit, .qualify .observers]
  -- The fourth shard also runs `qualify observers` (`RegulaVerification.observersShard`).
  | ["diagnostics", "self-audit", "4/4"] =>
      [.qualify (form (.selfAuditShard "")), .qualify .observers]
  | ["diagnostics", "self-audit", _] => [.qualify (form (.selfAuditShard ""))]
  | ["diagnostics", "rule-examples"] => [.qualify (form (.ruleExamples ""))]
  | ["diagnostics", "rule-examples", _] => [.qualify (form (.ruleExamplesShard "" ""))]
  | ["diagnostics", "input-inventory"] => [.qualify .inputInventory]
  | ["diagnostics", "environment-census"] => [.qualify (form (.environments ""))]
  | ["diagnostics", "snapshot-history"] => [.qualify (.acceptanceSnapshots .history)]
  | ["diagnostics", "acceptance-controls"] =>
      [.qualify (form (.acceptance .fences "")), .qualify (.acceptanceSnapshots .dependencies),
        .qualify (.acceptanceSnapshots .gitStatus), .qualify .receiptBoundaries,
        .qualify .prepMeasure, .qualify .enumeration]
  | ["diagnostics", "documentation-controls"] =>
      [.qualify .documentationDependencies, .qualify .configurationCapture,
        .qualify .versoRecordedPaths, .qualify .copyRelocation]
  | ["diagnostics", "focused-controls"] =>
      [.selftest (.focused .nativeAdopter), .selftest (.focused .combinedSnapshot),
        .selftest (.focused .policyTransport)]
  | ["diagnostics", "policy-domain"] => [.selftest (.focused .policyDomain)]
  | ["diagnostics", "enumeration-failure"] => [.qualify .enumerationFailure]
  | ["diagnostics", "readers"] => [.qualify .readers]
  | ["diagnostics", name] =>
      match Partition.parse name with
      | some partition => [.selftest (.partition partition)]
      | none => []
  | ["diagnostics", name, spec] => partitionShardOf name spec
  | _ => []

/-- For a partition whose shards are too long for a job, the check of its slowest shard in CI
(Diagnostics run 38200295872); none for a partition whose shards a job runs. -/
def overBudgetShard : Partition → Option String
  | .fixtures => some "Its slowest shard's check took 172 s in CI."
  | .cli => some "Its slowest shard's check took 196 s in CI."
  | .environments => some "Its first shard's check was still running after 203 s in CI, when \
      the 420-second deadline ended the job."
  | .buildPolicy => some "Its slowest shard's check took 137 s in CI."
  | .structural | .execution | .lintDriver => none

/-- The groups of `groups` a job runs. `environment-census`, `snapshot-history` and `policy-domain`
are too long for a job, and no job has the generated website sources, Verso and a provisioned
Mathlib together that `readers` needs (`reason`). -/
def jobGroups : List String :=
  ["input-inventory", "acceptance-controls", "documentation-controls", "focused-controls",
    "enumeration-failure"]

/-- The partitions whose shards a job runs. -/
def jobPartitions : List Partition := [.lintDriver, .structural, .execution]

/-- A job runs the shards of exactly the partitions that are not too long for one. -/
theorem mem_jobPartitions (partition : Partition) :
    partition ∈ jobPartitions ↔ overBudgetShard partition = none := by
  cases partition <;> simp [jobPartitions, overBudgetShard]

/-- A job of a workflow that runs `verify.sh`. -/
inductive Job where
  /-- CI's `verify`: both acceptance steps, on every pull request and push to `main`. -/
  | ciVerify
  /-- CI's `mathlib integration`, on every pull request and push to `main`. -/
  | ciMathlib
  /-- CI's `rule-examples` shards, on every pull request and push to `main`. -/
  | ciRuleExamples
  /-- CI's `site`, on every pull request and push to `main`. -/
  | ciSite
  /-- The diagnostics workflow's `campaign` jobs, on every pull request that changes an input of
  the campaigns (`Regula.DiagnosticsGate.inputs`), every push to `main`, nightly and on
  dispatch; the `diagnostics` gate, a required check, needs them. -/
  | diagnosticsCampaign
  /-- The diagnostics workflow's nightly rule-example shards. -/
  | diagnosticsNightly
  /-- The dogfood workflow's `self` jobs, when its paths change, on every push to `main` and
  nightly. -/
  | dogfoodSelf
  /-- The dogfood workflow's `default-path` job, nightly and on dispatch. -/
  | dogfoodDefaultPath
  deriving DecidableEq, Repr

/-- Every job once. -/
def Job.all : List Job :=
  [.ciVerify, .ciMathlib, .ciRuleExamples, .ciSite, .diagnosticsCampaign, .diagnosticsNightly,
    .dogfoodSelf, .dogfoodDefaultPath]

/-- The `verify.sh` invocations each job runs. -/
def Job.invocations : Job → List (List String)
  | .ciVerify => [[], ["docs"]]
  | .ciMathlib => [["mathlib"]]
  | .ciRuleExamples | .diagnosticsNightly => shardInvocations "rule-examples" 3
  | .ciSite => [["site"]]
  | .diagnosticsCampaign =>
      [["diagnostics", "producers"], ["diagnostics", "history"]] ++
      jobPartitions.flatMap (fun partition => shardInvocations partition.label partition.shards) ++
      jobGroups.map (["diagnostics", ·])
  | .dogfoodSelf => ["diagnostics", "self-lint"] :: shardInvocations "self-audit" 4
  | .dogfoodDefaultPath => [["diagnostics", "self-lint-default"]]

/-- Every campaign some job runs: each invocation of each job, and the campaigns it runs. -/
def ran : List Campaign :=
  Job.all.flatMap fun job => job.invocations.flatMap fun invocation =>
    .verify invocation :: runsOf invocation

/-- Why no job runs a campaign. -/
inductive Reason where
  /-- Its controls are among those of `campaign`, which runs; `why` says how. -/
  | within (campaign : Campaign) (why : String)
  /-- The campaigns `campaigns` run its controls between them, and each of them runs; `why` says
  how. -/
  | together (campaigns : List Campaign) (why : String)
  /-- The campaigns `campaigns` run part of its controls, and each of them runs; `why` names the
  rest and why no job runs them. -/
  | partly (campaigns : List Campaign) (why : String)
  /-- An internal entry point that `campaign`, which runs, starts for each of its items. -/
  | worker (campaign : Campaign)
  /-- No campaign that runs holds its controls, for the reason `why`. -/
  | notRun (why : String)
  deriving DecidableEq, Repr

/-- The condition of a reason: each campaign it names runs. -/
def Reason.holds : Reason → Bool
  | .within campaign _ | .worker campaign => ran.contains campaign
  | .together campaigns _ | .partly campaigns _ => !campaigns.isEmpty && campaigns.all ran.contains
  | .notRun _ => true

/-- The text the guide gives for a reason. -/
def Reason.text : Reason → String
  | .within campaign why => s!"Its controls run in `{campaign.spelling}`: {why}"
  | .together _ why | .partly _ why => why
  | .worker campaign => s!"An internal entry point that `{campaign.spelling}` starts."
  | .notRun why => why

/-- The `verify.sh` invocations of the shards of `partition`. -/
private def partitionShardInvocations (partition : Partition) : List Campaign :=
  (shardInvocations partition.label partition.shards).map .verify

/-- Where the structural shards stand in for the comparison of the self-hosted fresh inputs,
which an unsharded structural run alone makes (`Regula.Checker.CheckerSelftest.runStructural`):
two shards write the digests of the two inputs, and the `diagnostics` gate compares them. -/
private def selfHostedDigests : String :=
  let shards := Partition.structural.shards
  s!"The structural shards do not compare the self-hosted fresh inputs. Shards 1/{shards} and \
    {shards}/{shards} write their digests, and the `diagnostics` gate compares them."

/-- The text of an unsharded partition whose shards run. -/
private def shardsText (partition : Partition) : String :=
  if partition == .structural then
    s!"Its {partition.shards} shards run. Together they run each of its controls one time, but \
      for the comparison of the self-hosted fresh inputs. Shards 1/{partition.shards} and \
      {partition.shards}/{partition.shards} write the digests of those inputs, and the \
      `diagnostics` gate compares them."
  else s!"Its {partition.shards} shards run. Together they run each of its controls one time."

/-- The issue that tracks the sharding of the campaigns too long for a job. -/
private def overBudget (seconds : Nat) : Reason :=
  .notRun s!"Too long for a job. Its check took {seconds} s, and a check of more than 85 s does not \
    leave a quarter of the 420-second deadline. \
    [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it \
    into shards."

/-- The reason no job runs a partition, or one of its shards, whose shards are too long for a job;
`figure` is its slowest shard's check (`overBudgetShard`). -/
private def partitionOverBudget (partition : Partition) (figure : String) : Reason :=
  .notRun s!"The shards of the `{partition.label}` partition are too long for a job. {figure} A \
    check of more than 85 s does not leave a quarter of the 420-second deadline. \
    [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them \
    into shards that fit."

/-- The reason of an unsharded partition: its shards run, or they are too long for a job. -/
private def partitionReason (partition : Partition) : Reason :=
  match overBudgetShard partition with
  | some figure => partitionOverBudget partition figure
  | none => .together (partitionShardInvocations partition) (shardsText partition)

/-- What the partitions too long for a job leave out of a campaign over all partitions. -/
private def otherPartitions : String :=
  "The shards of the structural, execution and lint-driver partitions run. The shards of the \
    fixtures, cli, environments and build-policy partitions are too long for a job."

/-- Why no job runs the reader check of every package (`qualify readers`): it builds on what no
job has together. -/
private def readersNotRun : Reason :=
  .notRun "No job has the three things that it builds on: the website sources that \
    `./scripts/verify.sh site` generates, Verso and a provisioned Mathlib."

/-- The reason no job runs a campaign; none for a campaign that some job runs. -/
def reason : Campaign → Option Reason
  | .verify ["serialized-graph"] => some <| .notRun "The optional serialized-graph claim (§7.9), \
      which this repository does not make."
  | .verify ["diagnostics"] => some <| .partly
      (jobPartitions.flatMap partitionShardInvocations)
      s!"{otherPartitions} {selfHostedDigests}"
  | .verify ["diagnostics", "rule-examples"] => some <| .together
      ((shardInvocations "rule-examples" 3).map .verify)
      "Its 3 shards run. Together they run the records of each rule one time."
  | .verify ["diagnostics", "self-audit"] => some <| .together
      ((shardInvocations "self-audit" 4).map .verify)
      "Its 4 shards run. Together they audit each module one time."
  | .verify ["diagnostics", "environment-census"] => some (overBudget 172)
  | .verify ["diagnostics", "snapshot-history"] => some (overBudget 104)
  | .verify ["diagnostics", "policy-domain"] => some (overBudget 158)
  | .verify ["diagnostics", "readers"] => some readersNotRun
  | .verify ["diagnostics", name] => (Partition.parse name).map partitionReason
  | .verify ["diagnostics", name, _] => (Partition.parse name).bind fun partition =>
      (overBudgetShard partition).map (partitionOverBudget partition)
  | .qualify .registry => some <| .within (.qualify .combined) "`combined` runs `registry` first."
  | .qualify .native => some <| .within (.qualify .combined) "`combined` includes the `native` controls."
  | .qualify .uniqueConstants => some <|
      .within (.qualify .combined) "`combined` runs `unique-constants` beside `native`."
  | .qualify .nativeLauncher => some (overBudget 92)
  | .qualify (.ruleExamples "PATH") => some <| .within (.qualify (form (.ruleExamplesShard "" "")))
      "the shards together run the whole corpus."
  | .qualify (.ruleExamplesRules "PATH" ["RULE", "..."]) =>
      some <| .within (.qualify (form (.ruleExamplesShard "" "")))
        "each rule's records are in one shard."
  | .qualify (.producersExport "PATH") => some <| .within (.qualify .producers)
      "the same campaign, which also writes its evidence."
  | .qualify .producersCombined => some <| .together [.qualify .producers, .qualify .history]
      "`producers` and `history` run, each in a job of its own."
  | .qualify .selfAudit => some <| .within (.qualify (form (.selfAuditShard "")))
      "the four shards together audit all modules."
  | .qualify (.selfAuditModule "MODULE" "SOURCE") | .qualify (.selfAuditRulesModule "MODULE") =>
      some (.worker (.qualify (form (.selfAuditShard ""))))
  | .qualify (.enumerationCopy "SOURCE" "TARGET") => some (.worker (.qualify .enumeration))
  | .qualify .readers => some readersNotRun
  | .qualify (.copyRelocationLoad "PROJECT" "COPIES") | .qualify (.copyRelocationGit "SCRATCH") =>
      some (.worker (.qualify .copyRelocation))
  | .qualify (.acceptanceSnapshots .all) => some <| .partly
      [.qualify (.acceptanceSnapshots .dependencies), .qualify (.acceptanceSnapshots .gitStatus)]
      "Its groups `dependencies` and `git-status` run. Its group `history` is too long for a job."
  | .qualify (.acceptanceSnapshots .history) => some (overBudget 104)
  | .qualify (.environments "PATH") => some (overBudget 172)
  | .qualify .closureEvidence => some (overBudget 105)
  | .qualify .fenceEvidence => some (overBudget 140)
  | .qualify .frozenExits => some (overBudget 240)
  | .qualify .documentationSource => some (overBudget 182)
  | .qualify .documentationSourceReadOnly => some (overBudget 202)
  | .selftest (.focused .forcedCollector) => some (overBudget 336)
  | .selftest (.focused .policyDomain) => some (overBudget 158)
  | .selftest (.focused .fences) => some <| .partly [.selftest (.focused .combinedSnapshot)]
      "The focused controls include the combined snapshot. The in-process and public fence \
        corpora are controls of the fixtures and environments partitions. The shards of those \
        partitions are too long for a job."
  | .selftest (.focused .buildLint) => some <| .notRun
      "Its controls are those of the build-policy partition. The shards of that partition are \
        too long for a job."
  | .selftest (.focused .compilerPaths) => some <| .together (shardsOf .execution |>.map .selftest)
      "The execution shards run its compiler-path mutations."
  | .selftest .transcriptWorker => some <| .notRun
      "An internal entry point that the fixtures shards start, which are too long for a job."
  | .selftest .defaultTier => some <| .partly
      ([Partition.structural, .execution].flatMap shardsOf |>.map .selftest)
      s!"The shards of the structural and execution partitions run. It also runs the controls of \
        the fixtures and cli partitions, and their shards are too long for a job. \
        {selfHostedDigests}"
  | .selftest .structuralOnly => some <| .together
      ([Partition.structural, .execution].flatMap shardsOf |>.map .selftest)
      s!"The shards of the structural and execution partitions run. {selfHostedDigests}"
  | .selftest .buildBound => some <| .partly
      (jobPartitions.flatMap shardsOf |>.map .selftest)
      s!"{otherPartitions} {selfHostedDigests}"
  | .selftest (.partition partition) => some <|
      match overBudgetShard partition with
      | some figure => partitionOverBudget partition figure
      | none => .together (shardsOf partition |>.map .selftest) (shardsText partition)
  | .selftest (.partitionShard partition _) =>
      (overBudgetShard partition).map (partitionOverBudget partition)
  | _ => none

/-- Every campaign: each `verify.sh` invocation, each form of `qualify` selection and each
campaign of the self-test. -/
def all : List Campaign :=
  verifyInvocations.map .verify ++ qualifyForms.map .qualify ++ selftestCampaigns.map .selftest

/-- `all` holds the form of every `qualify` selection. -/
theorem qualify_mem_all (command : Command) : .qualify (form command) ∈ all := by
  simp only [all, List.mem_append, List.mem_map]
  exact .inl (.inr ⟨_, form_mem command, rfl⟩)

/-- `all` holds every campaign of the self-test. -/
theorem selftest_mem_all (campaign : SelftestCampaign) : .selftest campaign ∈ all := by
  simp only [all, List.mem_append, List.mem_map]
  exact .inr ⟨_, selftest_mem campaign, rfl⟩

/-- A campaign is covered when some job runs it and it has no reason, or no job runs it and its
reason holds. -/
def covered (campaign : Campaign) : Bool :=
  if ran.contains campaign then (reason campaign).isNone
  else (reason campaign).any Reason.holds

/-- Every campaign is covered: it runs in some workflow job, or no job runs it and its reason
holds. -/
theorem covered_all : ∀ campaign ∈ all, covered campaign = true := by decide +kernel

/-- The campaigns no job runs, with their reasons, in the order of `all`. -/
def notRun : List (Campaign × Reason) :=
  all.filterMap fun campaign =>
    if ran.contains campaign then none else (reason campaign).map (campaign, ·)

/-- The table of the contributor guide: each campaign no workflow job runs, and why. -/
def table : String :=
  "\n".intercalate <|
    ["| Campaign | Why no workflow job runs it |", "| --- | --- |"] ++
      notRun.map fun (campaign, why) => s!"| `{campaign.spelling}` | {why.text} |"

end Regula.Campaigns
