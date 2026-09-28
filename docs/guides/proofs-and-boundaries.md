# Proofs and boundaries

What Regula's own implementation proves, what it only observes, and what it trusts. Each checker
boundary below names its proved decision, the operational adapter that feeds it, the trusted
mechanisms under it and the qualification that observes it. Structure is in the
[architecture](architecture.md); commands and campaigns are in the
[contributor guide](contributing.md#choose-focused-diagnostics).

Three kinds of evidence are kept apart:

- **Proved:** a kernel-checked theorem about the definition the checker executes. Its quantifiers
  range over supplied Lean values (decoded records, observations, inventories), never over
  external executions.
- **Observed:** a qualification control that exercises an external boundary no Lean proof
  covers (a process, the compiler or elaborator, Lake, Git, the filesystem, serialization bytes,
  OS signals). It is a bounded observation, not correctness evidence for a universal claim.
- **Trusted:** the supported Lean compiler and process, Lake, the filesystem, Git, GNU timeout
  and imported libraries. A proof about a decoded field does not prove the field truthfully
  describes what the compiler did.

The pure libraries (`RegulaPolicy`, `RegulaCore`, `RegulaQualification`, `RegulaVerification`,
`RegulaProvision`) are claimed Standard-Logical surfaces, so acceptance reports every
declaration's exact axiom set; that profile is an upper bound, not a claim that every proof uses
choice. Theorems in the excluded operational `Regula` library are kernel-checked by its
warning-free build (`warningAsError` also rejects `sorry`); `Checker.Manifest`,
`Checker.ProducerReport` and `Checker.RuleExampleQualification` bound their theorems' axioms to
Standard-Logical with a `collectAxioms` command, and `RegistryChecks` checks the registry and
codec theorems' axioms. None of this certifies the whole operational checker as verified.

## The acceptance boundary

An audit succeeds only by constructing a proof-bearing accepted value. With `c` an admitted
claim, `i` a frozen inventory and `r` the keyed result table (notation, not compiling Lean):

```text
PlanOK(c,i)         := exact target partition and source identities, mode/stage compatibility,
                       unique job identities, required jobs derived from the independent census
CompleteFor(c,i,r)  := PlanOK(c,i) ∧ keys(r) = requiredJobs(c,i)
                       ∧ one completed result per key, each bound to c, i, its subject and stage
AllPolicyOK(c,i,r)  := ∀ k ∈ requiredJobs(c,i), PolicyOK(c,i,k,payload(r,k))
Accepted(c,i,r)     := { report with exact c,i,r projections // CompleteFor ∧ AllPolicyOK }
```

**Proved** (`RegulaPolicy`): `accept_iff`, `accept_sound` and `accept_complete` (acceptance holds
exactly for complete, policy-satisfying results; completeness is over the supported finite
observations, not elaboration, theorem search, source discovery or external liveness);
`finalize_iff` (for any plan, roles and supplied `(slot, observation)` list, finalization
succeeds exactly when every required slot has one exactly bound, policy-satisfying observation;
it does not assume a producer returned enough); `collect_success_iff`, `collect_lookup` and
`finalized_covers_input` (the executed fold keeps exactly its supplied pairs, never overwriting a
slot); `insertResult_success_iff`, `insertResult_lookup` and `insertResult_frame` (insertion
succeeds exactly for a fresh required key with a valid binding and changes nothing else; a refusal
returns no replacement state); `accepted_report_identity` and `accepted_covers_slot` (the report
projects the exact claim, census, ordered jobs and results); `combineAccepted`,
`combined_policy` and `combined_reports_same_snapshot` (a combined project and documentation run
keeps both capstones over one snapshot). File runs bind the requested and compiled sources by
`FileSourceBinding.sameBytes`; graph runs freeze their selected roots in `Census.graphRoots`, and
`GraphOK` cannot select fewer roots than `GraphPlanOK` admitted. Repeated immutable requests use
Lean's `withPtrEqDecEq` shortcut with structural equality as fallback; the kernel sees the
structural computation and the pointer shortcut has Lean's runtime trust boundary.

The stage relations `PolicyOK` combines, each a declarative relation whose decision function is
proved sound and complete against it:

| Relation | Meaning |
| --- | --- |
| `ScopeOK` (§7.1–§7.4) | Exact classified targets and modules, required ownership, source and origin bindings; no excluded import or unattributed declaration. |
| `AdmissionOK` (§7.3) | A completed logical-admission receipt matching the owned dependency census and snapshot; no skipped replay, unsupported admission or emitted warning on a positive fresh claim. |
| `FoundationOK` (§7.5) | No owned logical axiom, no `sorryAx`, unknown or compiler axiom; every axiom in the surface's permitted set. |
| `SafetyOK` (§7.4) | No unsafe or partial declaration unless the exact recursive-helper relation holds; a helper is never logical proof evidence. |
| `ContractOK` (§7.5, §7.11) | Every registered contract targets the exact supported implementation and predicate, with completed admission. Registration adequacy is review. |
| `ExecutionOK` (§7.6) | Every root's closure accounted for, no unresolved path; report mode permits reported trust, checked mode only checked evidence or origin-checked native runtime. |
| `DocumentOK` (§7.7) | Complete structural scan; warning-free, admitted Standard-Logical positives; one effective-error match per negative; classified teaching that is never positive conformance. |
| `DocumentationPresenceOK`, `MaterialDocumentationOK` (§5.1–§5.3) | A module docstring is present (`docstring ≠ none`); each registered material declaration's docstring has a nonempty Intent section. Module-docstring placement is decided by `RegulaPolicy.ModuleHeader`, outside `PolicyOK`. Registration completeness and fidelity remain R-DOC, intent adequacy R-INTENT. |
| `ExampleExpectationOK` | Exactly the configured positive, compiler-rejection, policy-rejection or trusted-teaching expectation for the exact source snapshot. |
| `StageOK` (§7.2–§7.3, §7.8–§7.11) | Every required producer completed for this mode; absence, crash, unknown or unsupported state is incomplete. |

Required jobs come from `requiredJobs` over scope, mode and fixed applicability, never a
caller-selected subset. A fresh project requires configuration and discovery, a fresh
warning-free build, logical admission, every owned declaration's policy, every execution root
and closure, the required transcripts, histories and origins, and documentation presence; an
incremental project has the same policy obligations over an incremental build; a fresh file
requires its own compilation, admission, declaration policy and closure, with no whole-project or
documentation-presence coverage; fences keep §7.7's logical-only contract; a serialized graph
requires every selected root checked. Empty modules, empty root sets and fence-free Markdown are
accepted only after their discovery, build and scan jobs complete; a project still needs a
nonempty library surface.

**The report account.** Every verdict line and every `completed` status is rendered from
`Account.account run` (claimed `RegulaCore.Account`). `Account` is the subtype of projections of
some `AcceptedRun`, and `Status.completed` takes one, so `Status.completed_accepted` proves a
`completed` status has an accepted, complete, policy-satisfying run behind it.
`AccountContract` (`checked_account`) states its meaning: mode, scope, surfaces, toolchain and job
count are the run's own; coverage is `coverageOf` the mode, whole-project exactly for a fresh
project claim (`coverage_fresh_iff`); the listed contracts are exactly the accepted inventory's;
execution counts are `executionSummary` of each environment; fence counts partition the accepted
fences; the residual identifiers stay unresolved. That the run is the current request's is each
caller's binding, checked by inspection, as is the use of `Account.pass` for project, file,
build-lint, combined and graph verdict lines. Rendered text and `acceptance` JSON are unproved
adapter output; JSON is never decoded into acceptance.

**Success owners.** Only these routes construct acceptance; help, planning, internal workers,
editor hooks, registry and site validation, self-tests and qualifiers have no audit certificate,
and an editor snapshot result is never promoted to project acceptance. A rejected policy example
or an INCOMPLETE diagnostic demonstration is not an audit-success certificate.

| Route | Accepted value and remaining boundary |
| --- | --- |
| `AxiomGate.auditSurfaceAt` (fresh, `--incremental`, `--build-lint`) | `Acceptance.freeze` reconciles Lake modules, sources, configuration, dependencies, reports, replay inventories and origins; `Acceptance.finish` returns `AcceptedRun` with checked equality to `finalize` (`finalize_collection_error`, `finalize_of_collected`). Cached build artifacts never cache a policy decision, and build-lint has no second exit-code-only PASS branch. |
| `Lint.run` (`lake lint`) | The same project audit; exit 0 only through the claimed `Lint.classify` (`checked_classify`, `accepted_sound`): a zero audit exit and a recorded `completed` account of the requested mode. Exits 1, 2, 3 classify rejected, configuration-only and incomplete statuses; a missing or disagreeing status is 3. That the recorded observation is this invocation's audit is checked by inspection. `--explain-config` and `--help` are read-only, exit 2, refuse `--json-out` and `--verbose`, and first invalidate any recognizable `--json-out` destination. An error escaping `Lint.run` is exit 3, or 2 for a `manifest-` refusal, never 0 or 1. |
| `AxiomGate.auditSurface --with-docs` | One process: the project plan and the documentation plan over the same snapshot and build, joined by `combineAccepted`; no evidence crosses a process boundary between the stages. |
| `--acceptance-link PATH` (`axiomGate`, `docFenceAudit`) | After a fresh accepted run, the SHA-256 of the accepted sources, configuration, dependency captures, `docs/` Markdown and, with `--verso`, the Verso library's inputs; `docFenceAudit` refuses unless its own fresh capture has an equal identity. `axiomGate` invalidates PATH before the audit starts and records the identity only after its outer configuration recheck passes, so any refusal leaves it incomplete. Equality establishes identical captured inputs; `shasum` and the filesystem are trusted. |
| `AxiomGate.auditFile` with a conforming profile | A `freshFile` plan and `AcceptedRun`; dependencies stay incremental. No profile or a compiler-trusting file is `CLASSIFIED`. |
| `Documentation.auditBuiltProject`, `DocFenceAudit.run` | Markdown (and Verso) bytes, fence spans and task identities frozen before compiling; `finishDocuments` calls `finalize`. With `--verso`, the fresh build and render of the standard, then `Regula.Site.missingAnchors_nil_iff` for the registry's and the docs' links into it and `rowsMismatch_eq_none_iff` for its checklist rows. |
| `RuleExamples.documentation` | Keeps the documentation driver's accepted run. Canonical positive completion additionally requires a nonempty, all-positive fence inventory; negative and teaching expectations stay classified. The adapter verifies the original requested documents before emitting accepted metadata. |
| `FreshChecker.run` | A separate `serializedGraph` claim; `leanchecker` success is an observed process result. |

Source capture keeps each prefix for failure reporting; a prefix is not a completed inventory. A
qualification receipt starts as a new incomplete attempt before timeout selection, spawn and setup reads, keeps
the records it obtained on failure, and becomes completed only after every case and restoration;
a killed process cannot promote it. Graph invocations likewise invalidate recognizable absolute
result destinations before argument parsing or root discovery, and relative ones once their
project root is resolved.

**Trusted:** the census's agreement with Lean's environment is an explicit extraction boundary,
closed by qualification and review, never by a count or hash. Private constructors are an
ergonomic boundary, not hostile in-process unforgeability. Lean/Lake extraction, compiler
admission, source reads, process completion and compiled execution remain trusted.

## Keys, census and collection

Keys use Lean `Name` structurally: anonymous, string and numeric constructors are encoded
reversibly, anonymous is refused as a module or declaration identity, and empty string components
are preserved. A declaration's identity is its requested environment, snapshot, owning module and
exact name; a module's is its snapshot and name (the same module in two claimed surfaces is
refused as ambiguous); a boundary's is its root, reached declaration, kind, optional replacement
and occurrence; a fence's is its document snapshot and byte spans (generated `DocFence_N` names
are transport only). Set-valued observations use canonical sorted duplicate-free collections from
Std's extensional structures; evaluator chains and mutual groups stay ordered. Duplicate
observations are refused even when equal.

The census is created by traversal before any policy outcome is filtered: freeze Lake targets,
sources, manifest and Markdown; complete the mode's build, import and admission stages and take
the census of owned declarations, roots and required transcripts; then freeze the required jobs
before collecting results. `Census.requests` is the ordered array of environment requests, and
`CensusOK` requires the returned requests to equal it and their positive module partition to be
the whole claim. `InventoryValid` requires unique names within each Lean environment; different
environments may each define `main`, and their inventories are never merged. `Roles.eq_authorize`
and `frozenEnvironmentRoles_eq` prove the role receipt frozen per environment equals
recomputation, so roles are not re-authorized per job and no worker flag is trusted.
`Common.mapWorkQueue`, `admitIndexedWorkerResults` and the documentation collector run
`ResultState.collect` through `checked_indexedResults`: success returns exactly the array whose
indexed pairs are a permutation of the responses over every requested slot.

**Admission by construction** (`RegulaPolicy.Domain`, `Admission`): declaration kinds, boundary
kinds, correspondence, foundation classes, profiles, modes, safety and evaluator roles are closed
types whose parsers refuse unknown tags (pretty types and messages remain open text);
`admitClaim` refuses unsupported scope/mode combinations; `admitInventory` requires unique
identities, structural references, canonical sets, agreeing safety fields and transcripts bound
to source bytes, compiler identity and valid coordinates (an inventory is still not an independent
census); `admitExecution` requires unique roots and boundary occurrences with valid native-origin
bindings; `admitBoundaryEvidence` preserves correspondence, detail and native origin, refuses
incompatible extra evidence, and every representable value round-trips. The pure codec proves
`decode (encode x) = ok x` over a tagged tree; that is not a theorem about JSON text. Worker
parsing (`Checker.PolicyCodec`, whose container recursion is adapted from Lean's JSON parser under
Apache-2.0) rejects duplicate fields before building a map, unknown and missing fields,
unsupported tags and numeric overflow; the parent waits for the child's exit and checks the
response against its own request.

**Trusted:** these relations concern supplied observations. `InfrastructureOK` binds the exact
reporter, codec and collector artifacts the IO adapter compares with the running checker's; the
public `Contract`, `Diagnostic` and `StructuralName` interfaces do not imply a library-wide
exemption.

## Declarations, foundations and roles

**Proved** (`lean/RegulaPolicy/`):

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| Least foundation | `leastFoundation_spec`, `leastFoundation_ext`, `foundationFor_least` | Every axiom set within Standard-Logical gets its least containing profile, invariant under order and duplicates. Not the weakest possible proof of the proposition. |
| Classification | `foundationFor_iff`, `declarationFailure_iff`, `policyFor_ordered`, `OrderedDecision.unique` | Each of the six foundation classes (three labels, hole, unknown axiom, compiler-trusting) has its exact meaning; a declaration's diagnostic is its first failed requirement (invalid membership, owned axiom, hole, unknown, escape hatch, compiler trust, contract failure, profile excess). Renderer strings are not proved. |
| Declaration policy | `policyFor_none_iff`, `policyFor_conforming_iff` | Success is inventory membership plus the independent requirements; teaching never relaxes a conforming profile. |
| Roles | `NativeTeachingOK`, `RecursiveHelperOK`, `authorizedNativeAxioms_iff`, `authorizedUnsafeRecHelpers_iff` | A name is authorized exactly when an inventory record meets every component (the §7.4 helper conditions; the three §7.5 native-axiom conditions). The observed replay, whole-value and equation fields are inputs; the predicates do not prove them truthful. |
| Native axiom names | `nativeAxiomOrigin?_sound`, `nativeAxiomOrigin?_nativeAxiomName`, `nativeAxiomOrigin?_isSome_iff`, `compilerTrustingAxiomName_sound`, `compilerTrustingAxiomName_iff`, `modulePrivacy_nativeAxiomName`, `generatedPrefix_iff`, `native_generated`, `native_compilerTrustingAxiomName`, `native_provenance` | A name is recognized exactly when it is `nativeAxiomName parent t idxs`, Lean's own `Name.append` and `appendIndexAfter` as `nativeEqTrue` and `DeclNameGenerator.mkUniqueName` apply them, for `native_decide`, `decide +native` or `bv_decide`, with or without module privacy. The recognition direction assumes `RuntimeStringAppend`, because `appendIndexAfter` uses the logically opaque extern `String.Internal.append`. The three tactic names and the list of `nativeEqTrue` call sites are cited from the pinned sources, not derived; hygienic and anonymous prefixes are not recognized. |
| Execution policy | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff`, `boundaryFailures_ids`, `rootFailures_ids` | No failure exactly when there is no unresolved path and every boundary meets its mode's relation; the failure kind of every boundary and path for every claim. |
| Correspondence | `DefeqComparison.classify_checked_iff`, `classify_trusted_iff`, `classify_unresolved_iff` | Checked exactly for a completed comparison with admitted evidence, trusted exactly for a completed one without, unresolved exactly for one that did not complete. |
| Expected diagnostics | `matchesPattern_iff`, `orderedLiterals_iff` | The restricted pattern's ordered leftmost-split match within one effective-error message. |

**Consumers** (paths from `lean/Regula/`):

| Operational caller | Proved pure function | Remaining boundary |
| --- | --- | --- |
| `Checker/Policy.admitScope`, with `Frontend.validateCoordinates` | `checked_scope` (first coordinate refusal in transcript order, then exactly `admitInventory` with `authorize`); `checked_coordinates` (claimed `RegulaCore.Coordinates`: success iff `CoordinatesAgree`) | Lean's UTF-16 column function (`FileMap.leanPosToLspPos`) and `FileMap`; source and compiler observation acquisition. |
| `request`, `ruleFor`/`reasonFor`, `ruleForMember` (claimed `RegulaCore.Policy`) | `checked_request`, `checked_rule`, `checked_memberRule` over `policyFor`; `ruleForFailure_injective`, `reasonFor_eq_some_iff` | Registry descriptor text; adequacy of the mapped rule set. |
| `labelOf`, `labelOfMember`, `classify`, `classifyMember` | `foundationFor`; `checked_memberFoundation`, `labelOf_member`, `classifyMember_eq` | Transitive `Lean.collectAxioms` results and module ownership. |
| `executionFailureRecords`, `executionFailures`, `executionSummary` | `checked_executionFailures` (line `k` renders record `k`, none added or dropped, so the lines are empty iff `ExecutionOK`), `executionRule_injective`, `checked_summary` | Root and closure collection, retained compiler edges, correspondence admission, source history and runtime origins. |
| `Probe.replacementCorrespondence` | `DefeqComparison.classify` (a comparison that did not complete is unresolved, never trusted) | Mapping the kernel result to the outcome, the kernel decision itself and the incomplete theorem-candidate search. |
| `Checker/Common.admitIndexedWorkerResults`, `mapWorkQueue`, `Documentation.auditTasks` | `checked_indexedResults` over `ResultState.collect` | Child completion, strict packet decoding, task scheduling and exact request and source binding. |
| `Checker/Documentation.matchesPattern` | `matchesPattern` | Structural fence scanning, pattern diagnostic text and effective-error extraction. |
| `AxiomGate.auditSurfaceAt`, `FreshChecker`, the file gate | `checked_surfaceAssignments`, `checked_conformingProfile`, `checked_histories`, `checked_environmentJob`, `checked_environmentEvidence` (claimed `RegulaCore.Assembly`) | Manifest parsing, Lake loading and producer history; the contracts concern the decoded records. |
| `Checker/Acceptance.finish`, `Documentation.finishDocuments`, `FreshChecker.finishGraph` | `finalize`, `finalize_iff`, `accepted_report_identity`, `accepted_covers_slot` | The independently supplied census and the truth of the observations; each finalizer supplies all derived jobs and returns `AcceptedRun`. |
| `AxiomGate.auditSurface` combined success | `combineAccepted`, `combined_policy`, `combined_reports_same_snapshot` | Child completion and raw decoding, terminal source stability and environment extraction. |
| `ResultProtocol.writeAccepted`, `acceptedJson` and the success renderers | `AcceptedRun.report`, `Account.account` (`checked_account`), `Status.completed_accepted` | Rendering, JSON and OS exit semantics are not universally proved; JSON is never decoded into acceptance. Each contract requirement's adequacy and the residual obligations remain review. |

`finishDocuments` is the documentation finalizer, not an arbitrary raw-occurrence admission API.
Computational helpers such as `declarationFailure`, `labelOf`, `compilerAxiom` and
`boundaryEvidenceCandidate` take caller-supplied sets and authorize nothing; `policyFor`,
`foundationFor` and their member forms require an inventory-bound `Roles` receipt, and
`admitBoundaryEvidence` preserves every observation field. Generated-role validators execute the
decidable component propositions, so there is no unconnected reference evaluator; `ExactlyOne`
has a proved decision procedure that considers only the possible first witness and still
requires equality to the complete singleton sequence (no wall-clock improvement is claimed).
A statement-reference audit, an axiom census or the occurrence of an implementation name is not
proof-body semantic linkage: review the executed definition and theorem hypotheses, then trace
the call through each success owner.

| Rules | Proved relation | Remaining boundary |
| --- | --- | --- |
| RG1001–RG1003 | `declarationFailure_iff`, `policyFor_ordered`, `foundationFor_iff` | Ownership and transitive-axiom acquisition (`Lean.collectAxioms`). |
| RG1004 | The above plus `authorizedNativeAxioms_iff`, `native_generated`, `native_provenance`, `compilerTrustingAxiomName_iff` | Transcript and replay truth; authorization permits teaching only. |
| RG1005 | `foundationFor_least`, `leastFoundation_ext`, `policyFor_conforming_iff` | The least containing profile of the observed axioms, not the least possible axioms for the proposition. |
| RG1006 | `authorizedUnsafeRecHelpers_iff`, `policyFor_conforming_iff` | Exact helper observations are checked; acquisition authenticity and execution coverage are not. |
| RG1007 | `ContractOK` through `ruleFor` | Recorded contract failures are enforced; Probe's extraction of the proposition and root, proof admission and adequacy are not proved by this relation. |
| RG2004 | `policyFor_ordered` (membership first), `CensusOK`, `PlanOK` | Complete Lake and environment ownership acquisition. |
| RG3001, RG3002 | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff` | The theorems cover the supplied unresolved paths and boundaries, not complete root and closure discovery or external runtime correctness. |
| RG4003 | `matchesPattern_iff`, `orderedLiterals_iff` | One effective error under the restricted grammar; producer completion and effective-error extraction are operational. Policy-negative source fixtures keep their separate registry-bound expectation qualifier, and a rejection is not positive conformance. |
| RG5002, RG5003 | `materialDocumentationFailure_eq_none_iff`, `_eq_missingDocstring_iff`, `_eq_missingIntent_iff`, `hasIntentSection_iff`, `ruleForMaterialDocumentation_injective` | The ATX line grammar (`heading?`) is a definition with checked instances, not a theorem about Markdown (`intentHeading_examples`); `findDocString?` lookup is Lean's. Intent adequacy is R-INTENT. |
| RG2001–RG2005, RG4001–RG4004, RG5001–RG5003 | The stage relations above, composed by `accept_iff` and `accepted_report_identity` | The adapters that populate them. |

**Correspondence resource bound.** `checkCorrespondenceProof` gives the kernel Lean's
per-declaration default heartbeats (`Core.getMaxHeartbeats` of the default options), so a
checker-added obligation costs no more than one the adopter could write, and runs under Lean's
runtime memory limit. The limit is fixed once per process, at its first correspondence check, to
the process's peak resident size then plus 1 GiB; it is set only while a check runs, never
exceeds a `max_memory` the shell set, and is restored afterward. Argued from the Lean runtime
source, not observed: the kernel throws only when current resident memory reaches the limit, so
the first check never fires on memory already held, and because the limit never re-reads the
peak, an exhausted check cannot raise the next one's limit. The 1 GiB is shared by every later
check and other growth in the worker, so after one exhaustion later checks may exhaust at once;
they fail closed as unresolved. At most three report workers run, so checks add at most 3 GiB
above those workers' first-check peaks; that increment does not by itself bound the audit's
total memory. Supplied and discovered theorem candidates are tried before the kernel-defeq check,
and kernel resource exhaustion is never conflated with rejection. Mapping the kernel result to
the observed outcome is checked by inspection, and the kernel decision itself is trusted.

## Producers

The producers turn a completed Lean environment into observations; their correctness is not
inferred from any pure proof.

- **Census.** `Probe.environmentReport` freezes `(owning module, declaration)` keys from
  `Probe.ownedConstants`, and ordinary and registered executable roots (private or imported),
  before building observations. No policy-success filter defines either census. An inspected empty
  root set is `some #[]`, an uninspected one `none`.
- **Admission.** `Admission.validate` replays safe, nonpartial owned declarations and their owned
  dependencies with the pinned `Environment.replay`, checks every required entry is in the
  resulting kernel and returns a typed receipt. Imported unowned modules remain trusted; the
  receipt records the completed operation and does not authenticate replay.
- **Documentation.** `Environment.loadReportCoreAtSearchPath` freezes the `@[regula_material]`
  selector from the completed owned environment and reads module docs (Markdown and Verso) and
  docstrings with `Lean.findDocString?`, the same lookup as native feedback, so the project gate's
  RG5001–RG5003 findings do not depend on whether native feedback was imported. Observed RG5003
  evidence is the fresh-project corpus pair and the native `MissingIntent` control; no incremental
  or build-lint RG5003 run is claimed.
- **Transport.** **Proved:** `ProducerReport.validate_sound` shows every report
  `Environment.validate` admits is `Environment.Admissible`, restating every executed guard (the
  census, execution results for exactly the requested roots, `ExecutionValid` closures, unique
  located source bindings, the replay receipt, documentation observations, and histories exactly
  for the requested modules, completed ones located and source-stable, unavailable ones leaving
  every requesting root unresolved); `validate_eq_ok` decomposes the guard sequence,
  `validate_nonvacuous` exhibits an admitted report and `fromJson_admissible` extends soundness to
  the decoder. Producers, documentation groups and acceptance call `checked_validate.run`; the
  coordinator's decoder keeps its success as a `ProducerReport.Admitted` proof
  (`fromJson_admitted`), which `Acceptance.freezeEnvironment` requires
  (`Admitted.admitExecution_eq`). These do not authenticate the observations; a direct interactive
  dump has no loader receipt and cannot pass the decoder. Replay and source-evidence failures cross
  workers as typed `ProducerReport.Outcome.admissionFailed` (the shared
  `Environment.validateSourceEvidence` guard) and surface as RG2005, incomplete; initial setup
  failures stay RG2001.
- **Replacement histories.** The walk registers each `(root, module)` history request first; the
  loader keeps the Lean-resolved path, the exact bytes before and after an isolated worker and the
  ordered replacement edges, so earlier choices overwritten by later attributes are kept. A
  changed source or unsupported evaluator yields `unavailable`, never a completed receipt.
- **Closure.** `ExecutionRoot.closure` records the actual `Probe.executionWalk`: each first visit
  with its owning module and the earlier visit that queued it, and separate edge channels
  (`compilerEdges` from retained IR; `logicalEdges`; `candidateEdges`, every constant-equality
  candidate; `historyEdges`; `currentReplacementEdges`; `activeSimplificationEdges`;
  `helperEdges`; `requiredCode` and `unavailableCode`). Their union is a conservative traversal,
  not a selected or minimal call graph. Retained IR edges use the declaration step of Lean's
  pinned `IR.CollectUsedDecls.collectDecl`, a specialized API that a toolchain upgrade must
  requalify. **Proved:** `ExecutionClosure.discovery_induction`, `nodes_induction` and
  `admitExecution_preserves` (over the executed admission, not a separate graph model): for a
  closure satisfying `DiscoveryOK` (respectively `Valid`), a predicate true at the root and
  preserved by each recorded edge holds at every visit (respectively every admitted node), and a
  successful admission retains exactly its roots and proves `ExecutionValid`. They establish
  connectedness and structural admission, not completeness or authenticity of IR extraction or
  that a candidate edge executes. An active `csimp` self-edge stays an unresolved
  replacement-only cycle (RG3001).
- **Source binding.** `ProducerReport.SourceBinding` keeps module, path and exact text. Project
  checks capture Lake's source map and configuration before building; the loader checks source
  before import and after inspection, and transcripts, histories and every declaration range must
  match the frozen text. `SourceBinding.withUnchanged` rechecks sources and configuration around
  every frozen-input operation, including failed builds, crashed workers and decoding failures,
  and returns a typed refusal (RG2005, incomplete) on a change while preserving the original
  outcome otherwise. Terminal results keep captured sources (`sourceAccount`) even on failure;
  an absent or partial account does not establish coverage.

**Trusted:** Lake build semantics, compiler and imported-dependency authenticity, filesystem
reads, and the absence of a change restored between two observations. Byte equality is an
observation, not a filesystem lock or a source-to-`.olean` theorem.

## Inputs and dependency identity

Every acceptance route freezes the inputs it consumes before building: Lake's root inventory and
canonical source paths, root bytes, the manifest, Lake configuration, lock and toolchain files,
and each dependency's declared inputs (Lake's buildable library domains and executable roots,
with submodules a glob admits). `Snapshot.inputsUnchanged` rediscovers and rereads them all once
at the end, refusing any addition, removal or change; the combined route rechecks after its
documentation stage. No Markdown is a refusal; no whole-workspace scan substitutes for the Lake
inventory. Standalone and rule-example documentation callers capture dependencies before their
prerequisite build and pass that observation into `auditBuiltProject`, which performs no
replacement capture and rechecks the supplied observation before finalization. Source identities
keep exact snapshot bytes and logical URI; a digest may index storage, but digest equality alone
is not byte equality. Dependency Git pins do not prove an unmodified checkout, so the actual
dirty and path state is recorded as an observation.

A dependency's Git revision is observed once, and its dirty bit is decided from one
unrestricted `git status --porcelain=v1 -z --untracked-files=all --ignored=matching` by the pure
`Snapshot.dirtyOf`. Declared inputs are spelled as Git spells a literal pathspec from the
canonical root (the leading directory that is the root, lexically or by `realPath`, is removed
and the rest kept literally); an input outside the root refuses. **Proved:** `dirtyOf_iff`
(dirty exactly when some reported path, or a rename's original, equals a declared input or is a
directory above it) and `dirtyOf_eq_restricted`. **Trusted** Git behavior that makes this agree
with a literal-pathspec status:

- G1. Directory collapsing precedes pathspec filtering: an ignored directory without tracked
  files is reported as `dir/`; one containing tracked files is descended.
- G2. A rename is reported as `XY new` followed by its original path.
- G3. With `--untracked-files=all`, untracked directories are listed per file, except an
  untracked nested repository, reported as `dir/`.
- G4. A modified submodule is reported as its gitlink path.

Under G3 and G4 an input inside an untracked nested repository or a modified submodule reads
dirty, which is conservative. Otherwise the two decisions agree on the trusted premise that Git
reports a path with the same case and Unicode form as the declared input; membership compares
bytes exactly. On a case-insensitive filesystem, an input under an untracked directory whose
spelling differs from the disk's only by case reads clean; only the reported bit, never a
captured byte, is affected. Non-UTF-8 fields are dropped, since they cannot equal a declared
input. Every declared input's bytes are still read and UTF-8-decoded, and the terminal recheck
recaptures them.

Project census construction keeps failures until the policy diagnostic pass has completed.
Unavailable history prevents acceptance, while its execution findings keep RG3001,
`execution-unresolved` and root locations in fresh, incremental and build-lint modes. A stored
census error is raised if no typed policy failure already refuses the run; it is never replaced
by an empty census.

## Editor feedback

The native linter observes one Lean snapshot. Its public import supports legacy and `module`
files and imports Lean, Std and Regula's policy modules, never Mathlib, `Regula.Report` or
`Regula.Probe`. Lean owns asynchronous snapshots, cancellation and message replacement; Regula
keeps no global last-seen cursor. It has no `Accepted` or project-PASS constructor; fresh
admission, ownership reconciliation, execution closure, mandatory documentation jobs and complete
assembly belong to the project routes.

| Interface | Establishes | Outside it |
| --- | --- | --- |
| Command hook (`Collect.commandDeclarations`) | Records for the constant binders in this command's information trees; RG1001–RG1007 when evidence is available. | Constants added without binder information; not a census. |
| `Collect.currentModule` | Every constant in the current module's map, including private, generated and unused ones. | Completion is the caller's; a partial environment is partial. |
| Module hook | RG5001 (module docstring present and first, no repeated import), RG5002 and RG5003 for registered public declarations. | Complete local declaration-policy coverage. |
| `Collect.declaration` (`.snapshot`, `.replayCandidate`) | The canonical facts `Probe` uses, with replay and helper observations in the second form. | Replay and role authentication. |

The adapter runs the same pure policy and total failure-to-ID mapping as the project checker
(`Regula.Checker.Policy.editor_decision_rule`); a potential generated-role exception is deferred
as RG2005 rather than guessed. Recoverable compiler errors can leave hole-bearing declarations,
which still yield RG1002 while the original compiler error is preserved; unavailable collection is
reported as such. A module or project finding keeps its module or project location: Lean hosts
module findings at the end of the in-memory file and configuration refusals at the owning
command, never at an invented declaration. An unsupported `regula.localFoundation` request is a
configuration violation on each affected nonterminal command snapshot, including
declaration-free commands, and is intentionally not deduplicated across independent snapshots.
`liveFeedback_auditBuild` proves `liveFeedback true scopeValue = false`: under the audit build's
import-time marker the feedback switch is off whatever a command scope sets `linter.regula` to;
that every local finding is gated by that switch is checked by inspection. Disabling local
feedback cannot disable a mandatory project predicate.

**Documentation presence.** `Lean.findDocString?` accepts ordinary, Verso and inherited
docstrings; private names follow Lean's visibility and never enter the public `@[regula_material]`
selector. RG5001 reads Markdown and Verso module-doc metadata loaded with `importAll := true`,
`loadExts := true` and `level := .private`; an empty loaded array means absence, an unknown module
identity is unavailable evidence rather than an absent doc comment, and current metadata is
checked only after module completion by the module hook. Presence alone does not discharge
module 5's requirements.

The production linter reuses Lean's `getNewDecls`, `getDeclsInCurrModule`, the linter hooks,
declaration ranges, axiom collection and docstring APIs; no upstream code is copied. The project
reporter force-loads the shared collector from the exact checker artifact. Its presence is not an
import by the claimed source: the excluded-library scan omits it only when no non-probe module
imports it, real source imports keep their exclusion checks, the forbidden Report/Probe scan still
inspects it, and neither the linter nor manifest scope is exempted. `qualify native` and the
`checkerSelftest --policy-domain-only`, `--native-adopter-only` and `--forced-collector-only`
controls are bounded observations of this API behavior, not proofs about arbitrary plugins,
native machine code or editor interaction. VS Code behavior (opening the link, the Problems-panel
fallback, non-BMP and CRLF ranges, stale and cancelled snapshots) was observed, not proved.

## Registry, feedback and output

**Proved:** `RuleId.parse_spelling`, `spelling_injective`, `mem_all`, `all_nodup` and
`route_injective` (the closed vocabulary and its routes); `RegistryCodec.mode_roundtrip`,
`rule_roundtrip`, `nameParts_roundtrip` and `name_roundtrip`. `RegulaCore.Feedback`: every
finding is printed exactly once (`sortEntries_perm`, `render_length`) in run order
(`sortEntries_sorted`, `sortEntries_eq_of_perm`), carrying its rule's guidance exactly when no
earlier finding has that rule (`tag_of_prefix`, `mem_firsts`, `firsts_nodup`, `firsts_length_le`);
the streaming emitter executes `Feedback.step` (`renderFrom_cons`) and JSON lists findings in the
same order (`sortFindings_entries`). `RegulaCore.Guidance`: the briefing lists every rule once
(`writingSections_perm`) and the `regula` parser admits exactly its documented commands
(`parseCommand_arguments`, `parseCommand_sound`). Result stages: `stagesOf_required`,
`stagesOf_ordered`, `withDocs_ordered`, `notRun_completedStages_eq_nil_iff`,
`completedStages_idem`, `guidanceFields_recorded`, `parseStage_stageName`. Snapshot size:
`snapshotJson_configuration_independent`, `environmentJson_imports_independent` and
`Environment.resultJson_imports_independent` (`rfl`) show the rendering does not depend on
dependency text or import lists; the resulting size bound is an argument from construction, not a
theorem about byte counts.

These theorems concern text and data as functions of their inputs: that the checker supplies
every finding, and that the process writes the lines, are operational. `admitGuidance` checks a
result's consistency against writer regressions, not authenticity: a report edited to be
self-consistent passes. `RegistryChecks` exhaustively checks the 22 descriptors, the embedded
examples and the committed skill file, and exercises malformed transport, routes, modes and
Unicode/CRLF coordinates as observations of those boundaries. JSON text parsing, `FileMap`, and
the compiler's collection of names, ranges and source identity are trusted.

## Rule examples and the corpus runner

**Proved:** `admitExampleRequest` admits exactly expected/observed request equality;
`admitExampleSources` requires every observed source in the frozen snapshot and the displayed
text in it; `admitDemonstration_sound` and `_complete`, `demonstration_completed`,
`demonstration_observed_incomplete`, `demonstration_selected_rule` and
`demonstration_not_accepted` (an admitted demonstration fails every accepted-example kind);
`RegulaPolicy.incomplete_example_refused` (an incomplete outcome satisfies no fence
expectation); `positiveClassifications_sound`. `Checker.RuleExampleQualification.qualify_sound`:
every record `qualify` admits is `RecordAdmissible` (current producer identity, parsed mode, equal
before/after snapshots, the observed request decoding to the frozen one, exit at most 1, sources
in the bound snapshot, findings equal to the parsed diagnostics, one of three kinds, and
`DemonstrationOK` for a demonstration); it proves nothing about the producer that wrote the
record. `RuleExampleProjection.qualify_record` and `qualifyCorpus_records` give exact equality at
the adapter's canonical record constructor and over the full corpus.

The runner's schedule is the pure `RegulaQualification.CorpusWindow`: `launched_le` (launched but
unconsumed tasks within the width), `launch_order` (every job launched once, in order),
`launched_eq_total` (under the window invariant, `s.consumed = s.total` gives
`s.launched = s.total`: no task is launched but never awaited) and
`productions_nodup` (for a duplicate-free `selected` rule list, distinct `(rule, phase)`
workspaces). Task scheduling, `IO.asTask`/`IO.wait` and process reaping are trusted. The
runner shares one private copy of the root package and the captured dependency roots with every
producer and records a content identity of every entry (path, `lstat` kind, length, 64-bit native
hash) before any producer and after all are joined; equality shows the end state equals the start,
not that no write occurred. Git facts are captured once and injected into producers by exact
request (`ruleExamples --injected-git-facts`; results carry `"gitFacts": "injected"`, and
`axiomGate` rejects the flag): `Snapshot.assemble_facts_eq` and `stateOfCore_congruence` show
equal facts give identical captures and bytes, and the campaign rechecks the shared trees once at
the end. Root processes, concurrent external writers, filesystem honesty, hash collisions and
writes restored before the terminal check are trusted. The final export's only writer,
`saveCompleted`, requires the `Cleaned` witness that `withScratchCleaned` constructs after
scratch removal; `COMPLETED` attests what finished, while the run's verdict is its exit status.

## Qualification ledger

Each control is classified by what it can establish (standard §0 "The Role of Testing").
**Proved** controls sampled a pure function the checker executes and are replaced by a theorem
over every input; **External** controls observe a boundary no proof covers and are kept at the
smallest set exercising it; **Counterexample aids** remain only where the universal statement is
not yet proved, and are labelled so at their definition.

| Campaign | Control | Property | Class | Evidence |
| --- | --- | --- | --- | --- |
| producers | 12 documented-source runs, 2 standalone executables | real incremental and build-lint detection, stale-artifact handling | External | observed |
| producers | 8 transport mutations | `Environment.validate` refusals | Proved | `ProducerReport.validate_sound` |
| history | 10 project and file invocations | replacement history, unsupported evaluators, source changes | External | observed |
| history | 17 history, closure and source transport mutations | `Environment.validate` refusals | Proved | `ProducerReport.validate_sound` |
| history | 7 oracle mutations | refusal of missing imported ownership or execution evidence | Proved | `History.validate_importedRootExecuted`, `validate_unsupported_unresolved` |
| rule-examples | 44 Fixed/Violation productions | every published example yields exactly its documented findings | External | observed |
| rule-examples | 3 refusal productions | the producer's own request and classification account | External | observed |
| rule-examples | 7 record mutations, 7 admission subprocesses | `qualify` refusals | Proved | `RuleExampleQualification.qualify_sound` |
| checkerSelftest fixtures | in-process and CLI fixture verdicts; fence corpus | compiler, elaborator, CLI and fence workers | External | observed |
| checkerSelftest fixtures | 11 execution-policy cases | failure kind per boundary and claim | Proved | `boundaryFailures_ids`, `rootFailures_ids`, `executionFailureRecords_empty_iff` |
| checkerSelftest fixtures | 12 scanner cases | `Documentation.scan` marker and fence problems | Counterexample aid | open: a step-function scanner with proved problem coverage |
| checkerSelftest structural | in-process manifest cases | `Manifest.parse` acceptance, decoding and the classified refusal classes | Proved in part | `Manifest.parse_sound`, `parse_input`, `parse_emptyExclusions`, refusal-class theorems; other refusals (a missing required field, an unknown exclusion key) are unclassified |
| checkerSelftest structural | real manifests, CLI refusal rendering, Lake discovery, executable classification | file IO, CLI rendering, Lake inventory | External | observed |
| checkerSelftest cli, environments, build-policy, lint-driver | CLI sweep, adopters, clean checkout, ordinary build, `lake lint` exit classes | packaging, Lake and build integration | External | observed |
| ordinary | `qualify registry`, `qualify native` | CLI output invalidation, registry and site validators; compiler messages and ranges | External | observed |
| ordinary | `RegistryChecks` codec and source cases | registry, diagnostic and source codecs | Proved in part | round-trip theorems; open: state the remaining refusals as theorems |
| standalone | `qualify environments` finalize mutations | `finalize` refusals | Proved relation | `finalize_iff`; instance membership sampled |
| standalone | `qualify acceptance fences` packet mutations | worker-packet admission through a real proxy | External transport | admission proved (`checked_indexedResults`) |
| standalone | snapshots, input inventory, receipts, frozen exits, documentation source, closure, configuration and fence evidence | Git, Lake, filesystem, elaboration-time IO, signals | External | observed |

The `qualify` campaigns and what they observe: `registry` (malformed invocations invalidate stale
output; the validators accept real exports and refuse each removed field, the previous schema and
a missing page); `native` (42 compiler controls for identity, multiplicity, severity, ranges,
documentation and ownership, four at a time in dependency order) and `native-launcher` (42 paired
baseline/cached-environment controls with exact equality); `producers`, `history` and
`rule-examples` (above); `closure-evidence`, `configuration-capture`, `documentation-source`,
`fence-evidence`, `frozen-exits`, `input-inventory`, `documentation-dependencies`,
`receipt-boundaries`, `acceptance fences`, `acceptance-snapshots dependencies|history|git-status`
(the dirty decision against a literal-pathspec status for G1–G3), `environments` and
`self-audit`. `checkerSelftest --policy-domain-only`, `--native-adopter-only` and
`--forced-collector-only` qualify public adopter imports, forbidden probe imports, the production
linter import and the force-loaded collector.

**The manifest** (`Checker.Manifest`, excluded library; axioms bounded to Standard-Logical by
the module's `collectAxioms` command). `parse_sound` and `parse_input`: every manifest the executed
`parse` accepts satisfies `Manifest.Valid` (nonempty surfaces, duplicate-free library and
executable names across surfaces and exclusions, well-formed target names, no compiler-trusting
claim, a nonempty rationale for every entry) and comes from JSON whose keys are all allowed and
whose schema version is 2, each array decoding element by element in order. The refusal-class
theorems (`parse_malformed`, `objectWithKeys_unknown`, `topLevel_unknownKey`,
`topLevel_schemaVersion`, `topLevel_emptySurfaces`, `parseSurface_unknownKey`,
`surfaceExecution_unknown`, `surfaceExecution_nonString`) give the documented message of each
isolated defect under their stated preconditions; other refusals, including a missing required
field and an unknown key in an exclusion entry, are not classified by a theorem, and the public
CLI controls remain external observations of how each class renders. `parse_emptyExclusions`:
JSON meeting the top-level conditions with empty exclusion arrays is accepted with exactly its
surfaces whenever they parse; it does not prove that any particular surface is accepted.
`parse_ok` (`parse` accepts `m` exactly when `PolicyCodec.parse` returns a value `parseValue`
accepts with `m`), `parseValue_ok` (`parseValue` accepts a value with `m` exactly when
`m.Valid` and the value `Encodes` `m`, so `Manifest.Valid` is exactly what the parser admits) and
`toJson_encodes` give `parseValue_toJson`; `structuralManifest_valid` shows the structural copy
of a valid manifest is valid whenever it claims an actual surface. The schema-version check
compares `JsonNumber` fields with derived equality (`schemaVersion2`) rather than `Json`'s
`partial` `BEq`, with the same runtime meaning.

**The structural partition.** `Manifest.structuralManifest` derives each structural copy's
manifests from the repository's; `structural_libraries` and `structural_executables` prove the
base classifies exactly the actual targets, and `structural_roundtrip` (with `parseValue_toJson`:
`parseValue (toJson m) = .ok m ↔ m.Valid`) covers what the gate reads at the `Json` value
boundary for any accepted manifest and claim set selecting an actual surface. `structuralBase`
checks that claim hypothesis at run time, and no theorem links that check to the hypothesis. The text boundary is trusted: `Json.compress` is `partial` and `PolicyCodec.parse` runs
core `partial` parsers, so no theorem describes them; `parse_of_encodes` names what they must
deliver. The variants that rewrite the `AuditApp` surface after derivation are not covered.
`diagnostics structural` passed locally in 572 s without the deadline (observed 2026-09-27); it
exceeds the 420-second budget, so it is not a CI job.

**Other proved oracles:** `Checks.evaluate_success`, `evaluate_error` and `evaluate_append`
(`checked_evaluation`); `Registry.validate_exact`; `Native.validate_exact`,
`nativeMatches_exact`, `compilerMatches_exact`; `Json.validateDecoded_exact` with
`History.requirements` and `Producer.requirements` (not a proof that Lean's JSON parser matches a
formal JSON specification); `Evidence.checked_validation` and `checked_documentation`;
`Launcher.admit` and `checked_equivalence`; `Template.instantiate` (the required `Maps` proof for
the recursive JSON transformation, refusing at depth 64); `RegulaVerification.parseMode_sound`,
`parseMode_roundtrip`, `select_exact` and `commands_nonempty`; `dependencyFree` (the root lock
manifest records no dependency). The IO drivers call each `ExecutableContract.run`, so the
evidence is required by their source linkage and erased at execution.

## Operational assumptions

The supported compiler, filesystem, process runtime and GNU timeout are trusted. Each supported
public invocation runs under one non-foreground GNU timeout owning the whole process group,
including descendants with inherited output handles; OS scheduling and signal delivery are
trusted, not a real-time theorem. Acceptance passes an internal `--under-deadline` flag to
`qualify` so it does not detach a nested timer; the flag is not a bounded standalone invocation.
Direct `lake exe qualify` campaigns have one 420-second process-group deadline. Each public
invocation replaces its receipt with a fresh incomplete attempt before any fallible timeout
selection or spawn, and `qualify receipt-boundaries` exercises those failures. Scratch
directories are removed on normal or exceptional return; a killed run's directory is reclaimed by
the next scratch user once no live process holds the scratch lock (`Regula.Scratch`). Helpers
invoke external programs with argument arrays, never generated shell programs. The operator's
narrow shell exceptions are recorded in [`AGENTS.md`](../../AGENTS.md).
