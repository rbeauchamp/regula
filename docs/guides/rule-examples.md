# Source-owned rule examples and diagnostic demonstrations

The corpus in [`examples/rules/`](../../examples/rules/) supplies page inputs for all twenty-two
registry IDs. `corpus.json` fixes invocation, evidence mode, expected IDs, legacy subreasons,
message patterns, subjects and full primary locations before execution. Sources are copied
verbatim into disjoint Core-only adopters. `Regula.Qualification.RuleExamples`
orchestrates processes and files in Lean; the
existing Lean detectors produce the findings and `Checker.RuleExampleQualification` admits
the canonical evidence. This is scoped qualification, not a universal detector proof or
whole-project `Accepted` construction.

## Accepted examples and separate demonstrations

`Website.ExampleExpectation` retains exactly four kinds: positive, compiler rejection,
policy rejection, and trusted teaching. Compiler rejection uses the shared restricted pattern
language on one effective error. Policy rejection can follow successful elaboration and can
list every expected finding, including generated declarations and underlying diagnostics.
No extra finding may disappear. A source-free detector keeps its module/project location;
an example adapter must not manufacture a source range.

RG2001, RG2005 and RG3001 have **diagnostic demonstrations** for unavailable analysis. They
require completed, authentic diagnostic production and exact source/configuration/mode,
registry ID, reason, primary/related location evidence. The checker result remains
`incomplete`. A crash, missing response, stale source or unrelated error is not a demonstration.
Demonstrations are outside the four accepted-example kinds and do not supply positive or
negative accepted-program evidence. Each corrected counterpart runs its applicable completed
positive checks. No rule can become conforming by expecting its unavailability.

`Website.ExampleBinding` retains an admitted snapshot, mode and typed `ExampleRequest`.
The producer captures its own parsed invocation and configuration, including absent files and
Lake package overrides. `admitExampleRequest` admits only exact expected/observed equality;
its soundness theorem concerns that data equality, not process authentication. The qualifier
also compares the actual effective configuration and file or per-surface claim/execution.
Copied configuration paths are compared relative to their explicitly recorded roots, without
rewriting source or diagnostic identities. A changed effective package override is refused;
this example qualifier does not authorize configuration relocation transformations or combined
`--with-docs` requests. After initial configuration capture succeeds, early terminal failures
retain the producer request and any effective configuration captured before failure. If the
initial configuration read itself fails, the terminal result retains the original IO diagnostic
as RG2001/incomplete with an empty source account, a request with no configuration read and a
null effective account; it cannot qualify as an example or demonstration. The [producer transport contract](engine-producers.md#transport-and-consumer-boundary)
owns source retention on terminal exits; absent source evidence refuses qualification. The shared
`admitExampleSources` guard requires every observed source to belong to the frozen snapshot
and the displayed source text to occur in that account. File requests additionally require
that text at the requested path. Its soundness/completeness proofs concern these exact data
relations; capture, JSON decoding and process authenticity remain operational trust boundaries. `validateBoundExample` checks
binding/completion and the exact diagnostic list before applying the four-kind policy.
`admitDemonstration` returns the unchanged observation with a proof of `DemonstrationOK`:
completed production, nonempty expected findings, a selected-rule incomplete finding, exact mode and
canonical diagnostic equality. The observed list itself must contain an incomplete finding for the selected rule,
without assuming injectivity of JSON rendering. Its soundness/completeness theorems concern these data, not
process authenticity. `RegulaPolicy.incomplete_example_refused` proves that an incomplete
outcome satisfies none of the existing fence expectations. The executed validator additionally proves `demonstration_not_accepted`: every admitted
demonstration fails each accepted-example classification, for any expected finding list.
All six named new guarantees
(`incomplete_example_refused`, `admitDemonstration_complete`, `admitDemonstration_sound`,
`demonstration_completed`, `demonstration_observed_incomplete`,
`demonstration_not_accepted`) currently depend exactly on
`propext`, `Classical.choice` and `Quot.sound`: Standard-Logical, not Kernel-only.
`demonstration_selected_rule` exposes the selected-rule obligation directly. Documentation
receipts retain each actual fence classification. The documentation adapter derives
`completed` from its accepted report with a nonempty, all-positive fence inventory.
The qualifier separately applies `PositiveClassifications` to require a nonempty list
with every fence positive, passing and complete before admitting a positive correction.
Successful compiler negatives and trusted teaching remain `classified`; failed and incomplete checks retain their
own outcomes. `positiveClassifications_sound` states the exact admitted relation.
The [acceptance guide](policy-acceptance.md) owns global policy assembly; a passing corpus
run is not full-standard conformance.

## Source and remediation map

Each rule's fixtures are the files in `examples/rules/<ID>/`: a `Violation` and a `Fixed`
source, or an unchanged `Example.lean` with a changed dependency (RG1003) or configuration
(RG2001, RG2002, RG2006) pair; RG2006's pair is the package's `lakefile.lean`, to which the run
appends the `require` line of its producer slot. The registry embeds each rule's `Fixed` and
`Violation` bytes as its
checked compliant and noncompliant examples (`examples` of `descriptor` in
[`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean), by `include_str`; the `RegulaCore` library
`needs` this directory, and `RegistryChecks` refuses any mismatch), so the first finding of a
rule, `lake exe regula`, the agent briefing and the rule page all show exactly these files.
The exceptions are the qualification inputs of RG1003 and RG2001 (`ExampleAudience.qualification`),
which only the rule page shows; agent-facing output states their correction instead.
What each correction preserves and changes is the pair's `correction` sentence, rendered with
the exact inputs, findings and diff on the rule's [reference page](website.md). Keep that
sentence and the fixtures in the same change.

## Authoring and export contract

Add or change source files first. Select the actual supported detector stage; do not force a
project-only rule into an editor callback. Fix the intended diagnostic specification in
`corpus.json`, including all additional findings. Its location fields are explicit expected
coordinates, checked against the exact source by the registry codec. Whole-field placeholders
refer to invocation paths or exact source-owned bytes; they never rewrite actual findings.
Markdown snippet slices are explicit fixture byte anchors, not a second Markdown detector.
The production Markdown scanner still owns classification and fence semantics.

The adapters reuse `SourceBinding.withUnchanged`, typed `SourceAudit` outcomes and the
documentation driver’s frozen project snapshots. They serialize only after snapshot
checks complete; a typed refusal or process exception cannot become a qualifying example.

The runner starts the fixed and violation phases, each in its own fresh workspace with
empty root build output, uses unique result paths and checks source/configuration readback.
A separate fresh workspace per phase replaces a restored rerun (standard §8.8). At most
five independent detector invocations run concurrently; evidence consumption stays in
registry/phase order.
File fixtures are separate from the warning-free positive library used to prepare dependencies. Its export embeds exact
sources, commands, original compiler output, canonical schema-1 results, expected locations,
mode and checker build identity, plus exact checker source bytes before and after the campaign.
The campaign additionally exercises authentic Standard-Logical output against a Kernel-only
request and actual successful negative/trusted documentation against a positive correction
expectation; the fixed phases are the fresh positives. Relabelling a demonstration's selected rule is
refused while retaining its complete findings. Authentic early RG2003/RG2005 results are also
refused against corrected caller snapshots or after removal of producer source evidence.
These controls qualify the adapters; the
universal data predicates and their proofs remain distinct from observed process behavior.
The Lean qualifier checks selected coverage against the
closed registry and requires both phases once. It is the single admission of every
canonical record; each refusal control is admitted individually. Unrun selected rules cannot be called
a complete-corpus pass. Version fields alone do not authenticate whole binaries; the producer and
filesystem remain the existing trusted operational boundary.

After provisioning pinned dependencies, build both detector executables and the qualifier executable.
The campaign invokes the compiled qualifier instead of re-elaborating it for every receipt:

```sh
lake build axiomGate ruleExamples ruleExampleQualification qualify
lake exe qualify rule-examples --evidence tmp/rule-examples.json
```

`./scripts/verify.sh diagnostics rule-examples` wraps this build and campaign under the
repository's diagnostic deadline and includes its housekeeping checks.

The `ruleExamples` and `ruleExampleQualification` executables are excluded in the root manifest solely as operational
qualification tooling, alongside the existing checker executables. Their modules belong to the
already-excluded `Regula` tooling library; no product module or detector is newly exempted
from its applicable qualification.

For development, append `--rules RG1001 RG1002` after `--evidence PATH` to produce
explicitly scoped evidence. `--shard K/N` selects every rule whose corpus position is K − 1 modulo N, except that RG5002 follows RG5001 into its shard so the shared fresh-project theorem-type check still runs (`mem_selectRules_shard`, `mem_selectRules_some_shard`, `rg5001_rg5002_same_shard`);
`./scripts/verify.sh diagnostics rule-examples 1/2` and `2/2` run the two CI shards. [Lean qualification](lean-qualification.md) specifies the
proved template transformation, Lake-discovered source snapshot and trusted IO boundary. Ordinary
[acceptance](contributing.md#develop-and-verify) remains separate.
Do not substitute the corpus campaign for that command. No website, editor-interaction,
serialized-graph or full-project completion claim follows from the corpus alone.

The [rule-reference site](website.md) renders these exports directly: `./scripts/verify.sh site`
admits both shard exports again, refuses stale or partial evidence (recorded source bytes that
differ from the checkout, a missing phase, another commit or toolchain), and shows the recorded
inputs and findings as text. The actual linter/examples use Lean 4.34.0 and the root pinned
dependencies. Verso's separate workspace uses the same Lean 4.34.0 toolchain and renders them as text.

Detectors, ranges and elaboration reuse Lean/Lake facilities; design influences are credited in
[design influences](design-influences.md).
