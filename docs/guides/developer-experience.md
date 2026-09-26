# Developer experience and implementation handoff

DESIGN-01 (#20). These are **selected production requirements**, not descriptions of
features already shipped. The [ecosystem study](ecosystem-design.md) supplies evidence,
alternatives, pins and attribution; [registry documentation](rule-registry.md) describes
the current implementation. The [policy contract](policy-acceptance.md) retains authority
over complete-result semantics. No normative rule is added or relaxed here.

## Start with the task the developer is doing

The package should be useful while editing an ordinary Lean file. Local messages belong
alongside Lean's expected types, goals and existing diagnostics. A project command should
then answer what was checked, under which configuration, and what remains unresolved.
Understanding a diagnostic must not require reading internal JSON fields or opening a
separate dashboard.

Production entry points selected for #14:

| Entry point | Contract |
| --- | --- |
| `import Regula.Linter` in the project's chosen common import | Enable available local command/module feedback using the existing Lean server. Importing it does not enable whole-project enforcement. |
| `lake lint` with `lintDriver = "regula/lint"` | Incremental inspection of the exact declared manifest scope, including current policy on cached modules. The driver runs the `axiomGate` project audit. |
| `lake lint -- --fresh` | Driver option selecting fresh project evidence through the existing producers and complete-result assembler. |
| Enabled plain `lake build` | Keep the current explicit enforcing default target. Qualify the documented adapter; explain which Lake formats support this enforcing target. |
| Existing file inspection | Retain `axiomGate --file ... --claim ...` and the distinct `freshFile` identity. Do not describe a file result as project coverage. |
| `lake lint -- --explain-config` | Read-only configuration explanation; validate and display the selected manifest, resolved Lake scope, per-surface profiles/execution mode, source of each option, and scheduled evidence mode/stages. No audit PASS or `Accepted` value. |

#14 delivered the `lake lint` driver (with `--fresh` and `--explain-config`), the build
target adapter and editor links; the [adoption guide](adoption.md) documents the shipped
commands. The driver does not take `--with-docs`: the combined documentation audit remains
`lake exe axiomGate --with-docs`. The concise human renderer below is not yet implemented.
The `regula/lint` driver dispatches into the current checker and #7's accepted-result path; it is not
another policy implementation. Preserve existing `axiomGate`, schema-1 and legacy JSON
migration interfaces until callers are deliberately migrated.

### Lake dispatch details that must be visible

At the supported pin, positional module arguments to `lake lint` affect **builtin** linting,
not the configured driver. Driver arguments follow `--`; Lake prepends `lintDriverArgs`.
The driver itself must build its claimed targets. `--builtin-only` skips it, and
`lake check-lint` only detects configuration. Neither establishes a Regula result.
The detailed evidence is [pinned Lake help][lake-help], [dispatch][lake-main] and
[driver execution][lake-actions]. #14 must qualify these actual paths, including combined
builtin/driver mode, rather than assume all invocations of the word “lint” are equivalent.

`--explain-config` has one deterministic resolution rule: explicit existing project/manifest
arguments select the manifest; otherwise use the established project-root default. No
additional nearest-file config search or inherited rule-selection layer. Package pins,
manifest origin, selected profiles, effective options and any unsupported input are visible.
Existing duplicate/unknown argument rejection remains. A recognized option cannot silently
change the requested claim into a smaller successful claim. Per-rule live visibility is a
presentation/scheduling choice; mandatory project predicates still run.

Mathlib already uses its own lint driver. Since Lake has one configured driver, adoption
must retain the existing workflow explicitly: document separate commands, or a small
user-owned composing script whose success requires both configured drivers to succeed.
Do not overwrite another driver's configuration silently or recursively call `lake lint`
from the Regula driver. #14 qualifies the recipe; upstream lint results remain
attributed to their producer and do not substitute for Regula's scope. See the
[pinned Mathlib configuration][mathlib-lake].

### Public import boundary

The neutral `Diagnostic`, `StructuralName`, `Findings`, `Collect` and native
`Linter` imports use the shared policy domain and supported Lean APIs without
transitively importing force-import-only `Report`/`Probe`. Operational callers
retain compatibility adapters. The contamination guard remains in force.
See [native-linter.md](native-linter.md) for the delivered local scope and its
qualification; the driver and editor-widget requirements below remain #14.

## Diagnostic contract

Display these in order, with details available without crowding the first line:

1. **Problem:** stable ID and a short, specific description with the relevant declaration.
2. **Why here:** authentic primary location and labelled related declarations/boundaries.
3. **Next action:** a truthful remediation step or missing-evidence explanation.
4. **Context:** current local/project mode and selected policy when it explains the finding.
5. **Details:** exact evidence, related dependencies, stages and the matching rule link.

Keep named Lean expressions interactive where the native APIs support them. Links reuse
Lean's own error-code widget with the registry URL, plus the textual HTTPS fallback; the
`logAt` path would attach the Lean-manual URL instead ([decision](linter-architecture.md#diagnostic-link-decision)). The infoview retains its own navigation
and ordering conventions; CLI/JSON order follows stable source/subject/rule keys, independent
of worker completion order. Do not impose a second file-wide infoview panel.

One source problem can produce both a compiler message and an aggregate strict-check failure.
Preserve the original compiler text/range and producer. Correlate exact snapshot/rule/subject
and source evidence to show a parent summary with related messages; never deduplicate by
matching human text alone or discard distinct policy subreasons. A source build failure may
prevent subsequent checks: report those as unavailable rather than inventing more violations.
Existing schema-1 records remain lossless; presentation grouping does not change acceptance.

The current `Diagnostic.text` deliberately exposes detailed mode/claim/arguments, the
`FILE:LINE:COLUMN` of a source selection and the rule's remedy (`RegulaCore.Feedback`); a
command-line run adds each rule's guidance once, under its first finding. #14 adds a concise
human renderer over the same value, retaining a detailed text view and complete JSON. Because
the canonical codec includes rendered text, treat any canonical rendering change as a reviewed
producer/schema compatibility change; do not silently invalidate existing transport consumers
(the agent-first text and fields moved results to schema 3).

### Snapshot lifecycle

A local result belongs to one source/configuration snapshot. New edits cancel or supersede old
work; stale findings and pending markers must not be published as current. Reuse Lean's
processing lifecycle; do not spawn a whole-project build from a command hook. Module-level
presence checks wait for completed module information. Costly project-only stages are labelled
as requiring the project command, without a warning on every declaration merely for being
pending. A clean buffer means no current local findings, not a green project certificate.

Import failures, missing configuration, cancellation and unsupported evidence are actionable
incomplete states. A completed policy violation is rejected. Current schema-1 `completed`
remains a scoped mechanical observation. The [acceptance contract](policy-acceptance.md)
owns the proof-bearing result boundary and its observation assumptions. Neither settles
residual semantic review.

## Three diagnostic-to-correction journeys

These are authored UX specifications. No new source span, native output or user observation
is invented. #13/#14/#15 must use actual fixtures and recorded evidence for qualification.

### A. A theorem depends on an unfinished proof

- **Trigger:** the collected declaration depends on `sorryAx` (RG1002). The declaration may
  elaborate with a warning while the user is still developing its proof.
- **Editor:** show the actual declaration/source location and “Proof depends on an unfinished
  proof.” If a precise hole/dependency origin is available, show it as related evidence;
  otherwise give the structural declaration/module identity without guessing a span.
- **Helper:** “Inspect the remaining goal and complete the proof.” Preserve ordinary Lean
  goals, tactics and suggestions; Regula does not invent a proof or rewrite the theorem
  to make the problem disappear.
- **Explanation page:** explain dependency-based detection, direct versus transitive holes,
  why compilation alone is insufficient for the chosen strict policy, and a checked corrected
  example with the same intended proposition. Link to the applicable normative clause.
- **CLI/build:** retain the compiler warning as evidence and the exact policy diagnostic when
  collection completed. A build that stops before collection reports that stage as incomplete,
  not a fabricated RG1002 result. The enabled strict build rejects either condition.
- **After correction:** recheck the new snapshot and complete applicable admission/policy stages.
  Removal of this one finding is not proof that every project requirement passed.

### B. Executable code crosses an unchecked boundary

- **Trigger:** a reached non-native-runtime boundary has only trusted correspondence under a
  surface selecting checked execution (RG3002), with completed boundary collection.
- **Editor:** emit a local finding only when the supported collector has the relevant evidence;
  otherwise identify that execution analysis requires the project command. Do not pretend a
  command callback reconstructed a whole-program closure.
- **Project diagnostic:** identify the actual executable root and boundary, selected execution
  policy and unavailable correspondence. Use a source range only when authentic; label the
  related root/target independently.
- **Helper/page:** show how to inspect the root and provide sufficient evidence for the exact
  supported correspondence, or revise the implementation to use an already justified path.
  Explain why a Lean equality does not prove arbitrary extern/native code correct. Do not
  offer “switch to report mode” as a fix for a checked-execution claim.
- **After correction:** completed collection/admission establishes the exact boundary state;
  rerun the unchanged claim. Show remaining native/runtime trust and residual obligations.

### C. Analysis cannot finish

- **Trigger:** missing toolchain/dependency, malformed manifest, crashed worker or stale source.
  Distinguish configuration rejection from incomplete execution using the real typed outcome.
- **Editor:** retain Lean's original import/elaboration message, and one scoped explanation
  of unavailable Regula analysis. No invented line 1 and no repeated error on every name.
- **CLI:** show what prevented checking, manifest/project origin when known, the action needed
  to retry, and completed versus uncompleted stages. Preserve recognisable-output invalidation
  so an old completed result cannot be mistaken for this attempt.
- **Helper/page:** explain environment/scope requirements and link to the pinned setup guidance;
  never equate missing results with absence of violations.
- **Recovery:** a new invocation binds fresh identity and completes required jobs. Help,
  `--explain-config`, worker completion and cancelled attempts cannot enter the audit-success
  renderer. Inspection/classification remains distinct from a positive claim.

## Rule website and accessibility

The entry page answers “What can this check, and where?” It contains a generated index with
stable ID, descriptive title, category, implementation/lifecycle status and supported evidence
modes. Search matches ID/name/message; filters cover category, mode and availability. Empty
results say no matches and allow clearing filters. Distinguish planned, implemented, retired
and temporarily unavailable documentation. Do not advertise “auto-fix available” without an
actual qualified action; the initial release has none.

A page starts with the problem, applicability and next action, followed by checked
violation/correction examples, evidence/limitations, technical exceptions, versions, normative
references and credits. Proof and executable examples preserve the intended claim; a failure
page does not recommend suppressing a mandatory obligation. Technical details can be expanded,
but keyboard and no-JavaScript readers can reach all substantive text and links.

#15 uses native HTML headings, labelled search/filter controls, visible keyboard focus, status
text independent of colour, readable narrow layouts and stable anchors. Help URLs retain the
versioned architecture; unavailable versions explain the failure and give the exact source
reference, without silently redirecting to changed semantics. Search is an enhancement over a
complete static catalog. The site remains generated from one registry and actual checked
examples, with the builder-observation trust boundary explicit.

#15 implements this in the [rule reference](website.md): a no-JavaScript catalogue whose
category, evidence-mode and availability filters are native selects driven by generated CSS, with a
form reset and an exact no-match notice; search by ID, title and page text through Verso's search box, with
find-in-page on the complete catalogue as the no-JavaScript path; and pages that start with the
problem and action. Its bounded browser observations are recorded with that delivery.

Ruff's index and fix labels, ESLint's metadata/suggestions, Microsoft’s rule explanations,
Pyrefly's scope clarity and HLS's integrated hints inform this design. They do not dictate its
visual styling or Lean semantics. See the [comparison and attribution](ecosystem-design.md).

## Implementation reconciliation and completion criteria

| Owner | Required change / preserved work | Evidence before claiming completion |
| --- | --- | --- |
| #5 | Preserve pure `RegulaPolicy` domain, one RuleId vocabulary and exact legacy policy predicates. Carry typed outcome/scope/configuration origins needed by explanation without making presentation authoritative. No renderer/server imports into pure core; arrange the neutral public-import boundary above without duplicating existing records/codecs. | Domain admission/codec/type guarantees over actual inputs; unsupported query states cannot construct a conforming claim. |
| #6 | Keep independent predicates and proofs about actual decisions. Preserve exact report identity, failed-insertion frames and observation assumptions. | Machine-checked promised laws; no theorem about UX, extraction fidelity or native effects inferred from those laws. |
| #7 | Same required-job census and Accepted assembly across all audit paths. Represent incomplete/cancelled/stale work distinctly; configuration explanation/help is non-audit completion. | Actual parent/worker/render/exit paths refuse missing or stale accepted evidence; preserve all subreasons. |
| #13 | Reuse matching Lean tests with independent mandatory scope; implement all twenty mapped conditions including two doc-presence rules (RG5003 later added a third, #71). Shared live/imported declaration construction and Lean snapshot scheduling; public adapter imports must satisfy the unchanged probe-contamination boundary. | Predicate/source/API review plus focused controls for private/generated/module boundaries, stale/cancelled data and exact rule/subreason. |
| #14 | Native import, driver/build/config-explanation contracts, concise renderer and detailed evidence, coexistence with Mathlib driver, three journeys and no automatic source edits. | Actual pinned supported editor interaction, both documented lakefile formats where claimed, dispatch matrix, Unicode and fallback/failed-help paths. No browser-only substitute for editor evidence. |
| #15 | Generated static/searchable catalog, purposeful pages, keyboard/no-JS behavior and actual source-linked examples. Keep Verso/pins/versioned artifacts. | Complete rule/page/example coverage, metadata identity, links and the bounded usability checks on the actual build, then authorized Pages publication. |
| #10 | Qualify Core-only application and Mathlib library workflows with explicit supported scope. Reconcile all residual accounts and release-facing feature claims. | Real end-to-end correction flows, supported-version matrix, no claimed user study/latency guarantee without evidence. |

No broad implementation rewrite is a prerequisite for the next unit. The shipped registry remains
useful; #15 retired the one-rule prototype. #20 is complete; its settled decisions were copied into the successor issue bodies.
The source-dependent findings in this design were inspected on Lean 4.33.1; the links
below retain that historical snapshot, not evidence for the current
[supported toolchain](../../README.md#supported-toolchain). Conventional integration and
UX were delivered by #14 and #15 and qualified by #10 ([product qualification](product-qualification.md)). The ordinary hard 420-second acceptance budget is unchanged.

[lake-help]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/lake/Lake/CLI/Help.lean
[lake-main]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/lake/Lake/CLI/Main.lean
[lake-actions]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/lake/Lake/CLI/Actions.lean
[mathlib-lake]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/lakefile.lean
