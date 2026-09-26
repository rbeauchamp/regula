# Policy proofs and their execution boundary

Regula proves its pure policy decisions over admitted observations. It does
not claim that these proofs verify the Lean compiler, source collectors, filesystem,
JSON parser, registry adapter, or a user's intended specification.

The [domain guide](policy-domain.md) describes the input types. The
[acceptance contract](policy-acceptance.md) records the concrete operational
acceptance boundary. Normative meaning comes from [chapter 8](../standard/8-tooling-and-machine-audit.md).

## What the theorems establish

All names below are in `RegulaPolicy`. Source files are under
`lean/RegulaPolicy/`. The quantifiers range over finite data values; proof fields
and stated hypotheses are part of the domain, not evidence of external execution.

| Property | Authoritative declarations | Exact meaning |
| --- | --- | --- |
| Least foundation | `Foundation.leastFoundation_spec`, `leastFoundation_ext`; `Decision.foundationFor_least` | Every axiom set contained in Standard-Logical receives its least containing profile. Membership-preserving order/duplicate changes preserve that profile. The actual public classifier uses this same result for inventory-bound roles. This does not find the weakest possible proof of a proposition. |
| Native teaching and recursive helpers | `RoleSpecification.NativeTeachingOK`, `RecursiveHelperOK`; `Decision.authorizedNativeAxioms_iff`, `authorizedUnsafeRecHelpers_iff` | A name is authorized exactly when an inventory record satisfies every named role component. Ordered groups/chains and occurrence uniqueness are retained. The predicates include the observed replay, whole-value and equation checks; they do not prove those observations truthful. |
| Classifier and diagnostic outcomes | `Decision.foundationFor_iff`, `declarationFailure_iff`, `policyFor_ordered`; `Specification.OrderedDecision.unique` | Each of the six foundation classes has its exact meaning. Declaration diagnostics select the first failed named requirement, with invalid inventory membership checked first. This does not prove renderer strings or summary counts. |
| Declaration policy | `Decision.policyFor_none_iff`, `policyFor_conforming_iff` | `policyFor` decision success is equivalent to inventory membership and the independent declaration requirements. A conforming request requires its permitted foundation, safety relation and recorded contract obligations. Teaching never relaxes a conforming profile. |
| Execution policy | `Execution.executionFailureRecords_empty_iff` | No failures is equivalent to no unresolved paths and the applicable relation at every reported boundary. Report mode permits reported trust; checked mode permits checked evidence or the typed native-runtime origin account. |
| Result insertion | `ResultState.insertResult_success_iff`, `insertResult_lookup`, `insertResult_frame` and refusal theorems | Insertion succeeds exactly for a fresh required key with a valid payload binding, installs that payload, and preserves every other lookup. Unknown keys, duplicate results and invalid bindings return a refusal, with no replacement state. |
| Concrete acceptance | `Plan.requiredJobs`, `PlanOK`; `Acceptance.accept_iff`, `accept_sound`, `accept_complete` | Acceptance requires the fixed claim/census-derived jobs, their completed result slots and each applicable policy relation. Completeness is over the supported finite observations, not elaboration, theorem search, source discovery or external liveness. |
| Report identity | `Acceptance.accepted_report_identity`, `accepted_covers_slot` | The report projects the exact claim, census, ordered jobs and result map. Every planned slot has one correctly bound policy observation. |
| Expected compiler diagnostics | `Pattern.matchesPattern_iff`, `orderedLiterals_iff` | Matching is the declared valid pattern's ordered leftmost-split relation within one effective-error message. Producer completion and effective-error extraction remain operational. |

File prefixes in this table identify the source file, not extra Lean namespaces.
For example, the actual theorem name is `RegulaPolicy.accept_iff`.

The least-foundation proof uses containment in the three permitted sets. The
collection laws reuse Std's extensional ordered structures. Generated-role
validators execute decidable component propositions, so there is no unconnected
reference evaluator. `ExactlyOne` has a proved decision procedure that considers
only the possible first-element witness and still requires equality to the complete
singleton sequence. This avoids repeated witness scans by construction; no
wall-clock performance improvement is claimed.

The prior generated-role loops and the new relations agree on the admitted
unique-name domain by guard-by-guard source review and focused qualification.
The new validator-to-relation equivalence is machine-checked. No theorem of
unrestricted equality with the prior loops on malformed duplicate-name arrays is
claimed.

## Actual consumers

Paths in this table start at `lean/Regula/`.

| Operational caller | Proved pure function | Remaining boundary |
| --- | --- | --- |
| `Checker/Policy.admitScope` | `checkedScope` (`ScopeContract`, for every coordinate check): first coordinate refusal in transcript order, then exactly `admitInventory` with `authorize`; success iff all coordinate checks and `InventoryValid` hold, retaining both input arrays. The adapter supplies `Frontend.validateCoordinates`, which runs `checkedCoordinates` (`CoordinateContract` in claimed `RegulaCore.Coordinates`): success iff `CoordinatesAgree`, refusal with the first unmet obligation in traversal order | Lean's UTF-16 column function (`FileMap.leanPosToLspPos`) and `FileMap` implementation; actual source and compiler observation acquisition. |
| `Checker/Policy.request`, `ruleFor` / `reasonFor`, `ruleForMember` (defined in claimed `RegulaCore.Policy`) | `checkedRequest` (`RequestContract`), `checkedRule` (`RuleContract`) over `policyFor`; `ruleForFailure_injective`, `reasonFor_eq_some_iff`; `checkedMemberRule` (`MemberRuleContract`: equals `ruleFor` for every inventory member) over `checkedMemberFailure` | Registry descriptor text itself; adequacy of the mapped rule set. |
| `Checker/Policy.labelOf`, `labelOfMember` (claimed `RegulaCore.Policy`) / `classify`, `classifyMember` | `foundationFor`; `checkedMemberFoundation` (`MemberFoundationContract`), `labelOf_member`, `classifyMember_eq` | Actual transitive `Lean.collectAxioms` results and module ownership. |
| `Checker/Policy.executionFailureRecords` (identity) / `executionFailures` (claimed `RegulaCore.Policy`), `executionSummary` | `executionFailureRecords`, `executionRule_injective`, `checkedSummary` (`SummaryContract`), `checkedExecutionFailures` (`ExecutionFailuresContract`: line `k` renders record `k`, none added or dropped, so the lines are empty iff `ExecutionOK`) | Root/closure collection, retained compiler edges, correspondence admission, source history and canonical runtime origins. |
| `Probe.replacementCorrespondence` (definitional comparison) | `DefeqComparison.classify` in claimed `RegulaPolicy.Domain`: `classify_checked_iff`, `classify_trusted_iff`, `classify_unresolved_iff` (a comparison that did not complete is unresolved, never trusted; standard §8.6) | Mapping the kernel result to the outcome (`kernelExhausted`, rejection, foundation check), the kernel decision itself and the incomplete theorem-candidate search. |
| `Checker/Common.admitIndexedWorkerResults`, `mapWorkQueue`, `Documentation.auditTasks` | `checkedIndexedResults` (`IndexedResultsContract`) over `ResultState.collect` | Child completion, strict packet decoding, in-process task scheduling and exact request/source binding. |
| `Checker/Documentation.matchesPattern` | `matchesPattern` | Structural fence scanning, supported-pattern diagnostic text, and completed effective-error extraction. |
| `AxiomGate.auditSurfaceAt`, `FreshChecker`, file gate (via `Checker/Acceptance`) | `checkedSurfaceAssignments` (`SurfaceAssignmentsContract`), `checkedConformingProfile` (`ConformingProfileContract`), `checkedHistories` (`HistoriesContract`), `checkedEnvironmentJob` (`EnvironmentJobContract`) and `checkedEnvironmentEvidence` (`DocumentationEvidenceContract`) in claimed `RegulaCore.Assembly` | Manifest parsing, Lake loading and producer history; the contracts concern the decoded records. |
| `Checker/Acceptance.finish`; `Documentation.finishDocuments`; `FreshChecker.finishGraph` | `finalize`, `finalize_iff`, `accepted_report_identity`, `accepted_covers_slot` | Independently supplied census and truthful actual observations remain external; each finalizer supplies all derived jobs and returns `AcceptedRun`. |
| `AxiomGate.auditSurface` combined success | `combineAccepted`, `combined_policy`, `combined_reports_same_snapshot` | Child completion/raw decoding, terminal source stability and truthful environment extraction remain operational. |
| `ResultProtocol.writeAccepted`, `acceptedJson`; project/file/build-lint/combined/docs/graph success renderers | `AcceptedRun.report`, `acceptedRun_claim`; the report account `Account.account` (`checkedAccount`, `AccountContract`) in claimed `RegulaCore.Account`, `Account.accepted`, and `Status.spelling_eq_completed_iff`/`Status.completed_accepted`: a `completed` status requires an account, and every account is the projection of an accepted run | Rendering/JSON/OS exit semantics are not universally proved. JSON is never decoded into acceptance. Adequacy of each contract requirement and the other rule-coverage residuals remain semantic review. |

Source extraction and transport qualification remain necessary. The existing
`Admission.validate`, fresh frontend attribution, canonical pinned `.olean`
origin check and conservative execution walk remain operational gates. A proof
about an exactness/replay field does not prove the underlying Lean value equality
or compiler run. A private constructor alone would not establish hostile
in-process unforgeability either.


## Complete collection and composition

For arbitrary `p : Plan c i`, `roles : CensusRoles i` and
`inputs : List (Nat × JobObservation)`, `finalize_iff` proves:
`(∃ result, finalize p roles inputs = .ok result) ↔ InputsOK p roles inputs`.
`InputsOK` requires distinct required slots with exact key/snapshot binding and a
policy-satisfying supplied observation for every slot in `List.range p.jobs.size`.
It does not assume a producer returned enough observations. `collect_success_iff`
and `collect_lookup` prove the executed fold retains exactly its supplied pairs;
`finalized_covers_input` connects every required lookup back to that input list.

`CombinedAccepted pc dc documents` carries both accepted plans, exact project/fresh
and documentation modes, the requested documents and equal snapshots.
`combined_policy` retains both completeness/policy capstones;
`combined_reports_same_snapshot` preserves report identities. File compilation
uses `FileSourceBinding.sameBytes` while retaining both actual URIs. Graph selection
is frozen in `Census.graphRoots/graphCoverage`; `GraphOK` cannot select a shorter
root set than `GraphPlanOK` admitted.

Repeated immutable requests use Lean's `withPtrEqDecEq` shortcut with the original
structural equality as fallback. This decides the same equality, without a digest
or caller-supplied identity token. The kernel sees the structural computation;
the compiled pointer shortcut has Lean's existing runtime trust boundary. No
wall-clock bound follows from these proofs.

A statement-reference audit, transitive axiom census or occurrence of an
implementation name is not proof-body semantic linkage. Review the actual executed
definition and theorem hypotheses, then trace the call through each success owner.
The caller table and collection/composition theorems supply distinct parts of that
account; neither substitutes for source/provenance qualification.

## Rule-ID linkage

These are the existing stable identities from the sole registry. Theorems operate
on typed observations; the adapter's exhaustive `failureId` mapping supplies IDs.
The table does not claim the rules' external collectors or residual review are proved.

| Rule IDs | Proved relation and actual consumer | Limit |
| --- | --- | --- |
| RG1001, RG1002, RG1003 | `declarationFailure_iff` / `policyFor_ordered` select project-axiom, hole and unknown-dependency failures; `Checker.Policy.ruleFor` maps them. `foundationFor_iff` supplies exact classification through `labelOf`/`classify`. | Actual ownership and transitive axiom acquisition remain operational. |
| RG1004 | Same declaration outcome theorems plus `authorizedNativeAxioms_iff`, consumed by `admitScope`/`ruleFor`. | Native authorization permits teaching only; transcript/replay truth is external. |
| RG1005 | `foundationFor_least`, `leastFoundation_ext`, `policyFor_conforming_iff` and ordered outcome equivalence; `labelOf`/`ruleFor`. | Least containing profile of observed axioms, not least possible axioms for the proposition. |
| RG1006 | `authorizedUnsafeRecHelpers_iff`, `policyFor_conforming_iff` and ordered outcome equivalence; `admitScope`/`ruleFor`. | Exact helper observations are checked; acquisition authenticity and execution coverage remain separate. |
| RG1007 | `ContractOK` and declaration outcome equivalence through `ruleFor`. | Recorded contract failures are enforced. Probe's proposition/root extraction, proof admission and adequacy are not proved by this relation. |
| RG2004 | `policyFor_ordered` places invalid-inventory membership refusal first; `ruleFor` maps it to coverage. `CensusOK`/`PlanOK` also contribute to executed composite acceptance. | Membership refusal does not establish complete Lake/environment ownership acquisition. |
| RG3001, RG3002 | `executionFailureRecords_empty_iff` and `boundaryFailures_empty_iff`; `Checker.Policy.executionFailureRecords`/`executionFailures`. | Theorems cover supplied unresolved paths and boundaries, not complete root/closure discovery or external runtime correctness. |
| RG4003 | `matchesPattern_iff` and `orderedLiterals_iff`; `Checker.Documentation.matchesPattern`. | One effective error under the restricted grammar; producer completion and error extraction are operational. Policy-negative source fixtures retain the separate registry-bound expectation qualifier; a rejection is not positive conformance. |
| RG5002, RG5003 | `materialDocumentationFailure_eq_none_iff`, `_eq_missingDocstring_iff` and `_eq_missingIntent_iff` partition a registered declaration's recorded docstring; `hasIntentSection_iff` shows the section scan decides `IntentSection`; `ruleForMaterialDocumentation_injective`. The native linter, project gate and `MaterialDocumentationOK` all use `materialDocumentationFailure`. | The ATX line grammar (`heading?`) is a definition with checked instances (`intentHeading_examples`), not a theorem about Markdown; `findDocString?` lookup is Lean's. Intent adequacy is R-INTENT. |
| RG2001–RG2005, RG4001–RG4004, RG5001–RG5003 | Concrete `PlanOK`, `StageOK` and named scope/build/admission/document/example/presence predicates compose through `accept_iff` and `accepted_report_identity`. | The adapters populate these relations and route audit success through `AcceptedRun`; completed ENGINE collectors retain their provenance guards. The proof remains about supplied observations, not external acquisition. |

## Complete observations and example expectations

`Census` retains the original complete request and an exact array of environment
requests. Each `EnvironmentCensus` records its full declaration/root/replay inventories,
roles' input inventory and source bindings separately from policy outcomes.
`CensusOK` checks the complete positive partition and global target classification.
Local job identities include the requested environment; `EnvironmentStageOK` resolves
the exact position and snapshot before applying the unchanged local predicates.
`requiredJobs` derives applicable
subjects from the fixed claim's mandatory stages. `Plan` requires the supplied
`JobKey` array to equal that derivation, with every key belonging to the same claim.
Natural-number result slots are positions in that exact array, not new semantic
identities or caller-selected requirements. Recorded successful executable-contract
roots must be represented in execution modes. Known root-target imports must agree
with positive target assignments; the collector must also report unclassified root
imports. History observations bind the exact environment/module/source tuple. These checks do
not establish external census completeness. The completed ENGINE producer
qualification is a separate scoped observation, not a proof of IO extraction.

`JobObservation` separates completion state, exact snapshot and stage-specific
fields. `StageOK` checks the appropriate relation for the stage and subject; an
unrelated payload constructor cannot pass. Missing, crashed, cancelled,
unsupported and incomplete observations cannot become accepted results.

`ExampleExpectationOK` distinguishes positive elaboration, completed compiler
rejection, completed policy rejection and compiler-trusting teaching. Expected
elaborated observations bind group modules and role transcripts to the fixed
fences' original bytes; policy assessment selects the current example unit. Expected
policy diagnostics retain stable identity tokens, optional subreason, exact
primary location and related locations. Matching requires the configured ordered
list with no additional diagnostics. The sole registry adapter validates identity
vocabulary and authentic locations. A completed rejection observation is not
itself proof that the external producer performed that work. Actual invocation,
strict packet decoding and source guards retain that operational linkage.

Accepting a negative or teaching expectation never supplies conforming positive
program evidence. Documentation examples retain their logical-only scope;
execution correspondence and narrower foundation claims need their own evidence.
All applicable residual semantic-review accounts remain required. A mechanically
accepted report is not full standard conformance.

## Evidence and supported domain

The implementation targets the [supported toolchain](../../README.md#supported-toolchain).
The pure policy library's import boundary is owned by
[the acceptance contract](policy-acceptance.md#5-pure-module-boundary-and-migration).

Ordinary acceptance checks each claimed declaration's exact axiom set against its profile.
Explicit theorem hypotheses are distinct from transitive logical axioms.
The manifest's Standard-Logical profile is an upper bound, not a claim that every
proof uses all three permitted axioms. Optional serialized-graph checking and
unrun broader operational campaigns are separate claims.

## Reuse and attribution

Lean supplies structural names and the observed compiler semantics; Init/Std
supplies collections, equality, string operations and their laws. The diagnostic
pattern consumer is adapted from this repository's existing implementation, with
structural termination and explicit policy linkage.

Con-leche's authors/contributors, maintained by Joachim Breitner at Lean FRO,
are credited for the design influence of [canonical semantic representations][propwhen]
and [complete indexed assembly with checked admission][installed]. No con-leche
code, model or theorem is imported, and its kernel/model guarantees are not claimed
for Regula. See the [contribution-specific attribution guide](design-influences.md).

[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean
