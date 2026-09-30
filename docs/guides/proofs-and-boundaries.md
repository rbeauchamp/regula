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

None of these proofs verifies the Lean compiler, the source collectors, the filesystem, the JSON
parser, the registry adapter or a user's intended specification.

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
observations, not elaboration, theorem search, source discovery, external liveness or detection of
arbitrary intended specifications);
`finalize_iff` (for any plan, roles and supplied `(slot, observation)` list, finalization
succeeds exactly when every required slot has one exactly bound, policy-satisfying observation;
it does not assume a producer returned enough); `collect_success_iff`, `collect_lookup` and
`finalized_covers_input` (the executed fold keeps exactly its supplied pairs, never overwriting a
slot); `insertResult_success_iff`, `insertResult_lookup` and `insertResult_frame` (insertion
succeeds exactly for a fresh required key with a valid binding and changes nothing else; a refusal
returns no replacement state); `accepted_report_identity` and `accepted_covers_slot` (the report
projects the exact claim, census, ordered jobs and results); `combineAccepted`,
`combined_policy` and `combined_reports_same_snapshot` (a combined project and documentation run
keeps both capstones over one snapshot). `CombinedAccepted pc dc documents` carries both accepted
plans, exact project/fresh and documentation modes, the requested documents and equal snapshots.
The conditional transfer lemmas `finalize_reindexed`, `finalize_singleton_transfer`,
`LocalEvidenceTransfer.sound` and `GlobalEvidenceTransfer.sound` are not used by the acceptance
path; their coherence hypotheses are not instantiated for the operational collector, and no
operational equivalence is claimed. File runs bind the requested and compiled sources by
`FileSourceBinding.sameBytes`; graph runs freeze their selected roots in `Census.graphRoots`, and
`GraphOK` cannot select fewer roots than `GraphPlanOK` admitted. Repeated immutable requests use
Lean's `withPtrEqDecEq` shortcut with structural equality as fallback; the kernel sees the
structural computation and the pointer shortcut has Lean's runtime trust boundary. No wall-clock
bound follows from these proofs.

The stage relations `PolicyOK` combines, each a declarative relation whose decision function is
proved sound and complete against it:

| Relation | Meaning |
| --- | --- |
| `ScopeOK` (§7.1–§7.4) | Exact classified targets and modules, required ownership, source and origin bindings; no excluded import or unattributed declaration. |
| `AdmissionOK` (§7.3) | A completed logical-admission receipt matching the owned dependency census and snapshot; no skipped replay, unsupported admission or emitted warning on a positive fresh claim. |
| `FoundationOK` (§7.5) | No owned logical axiom, no `sorryAx`, unknown or compiler axiom; every axiom in the surface's permitted set. |
| `SafetyOK` (§7.4) | No unsafe or partial declaration unless the exact recursive-helper relation holds; a helper is never logical proof evidence. The helper of a `partial def` (an opaque declaration Lean compiles through it) never holds it, and its finding names that declaration. |
| `ContractOK` (§7.5, §7.11) | Every registered contract targets the exact supported implementation and predicate, with completed admission. Registration adequacy is review. |
| `ExecutionOK` (§7.6) | Every root's closure accounted for, no unresolved path; report mode permits reported trust, checked mode only checked evidence or origin-checked native runtime. |
| `DocumentOK` (§7.7) | Complete structural scan; warning-free, admitted Standard-Logical positives; one effective-error match per negative; classified teaching that is never positive conformance. |
| `DocumentationPresenceOK`, `MaterialDocumentationOK` (§5.1–§5.3) | A module docstring is present (`docstring ≠ none`); each registered material declaration's docstring has a nonempty Intent section. For a module's `documentationPresence` job the unproved adapter computes the RG5001 header decision (`RegulaPolicy.ModuleHeader.failures`, characterized by `failures_eq_nil_iff`: presence, placement first after the imports and no repeated import) as that evidence, and `checked_environmentEvidence` proves only the selection of that frozen record. Registration completeness and fidelity remain R-DOC, intent adequacy R-INTENT. |
| `ExampleExpectationOK` | Exactly the configured positive, compiler-rejection, policy-rejection or trusted-teaching expectation for the exact source snapshot. Elaborated observations bind group modules and role transcripts to the fixed fences' original bytes, and policy assessment selects the current example unit. Expected policy diagnostics keep stable identity tokens, optional subreason, and exact primary and related locations; matching requires the configured ordered list with no additional diagnostics. The sole registry adapter validates the identity vocabulary and authentic locations, and a completed rejection observation is not itself proof that the external producer did that work. |
| `StageOK` (§7.2–§7.3, §7.8–§7.11) | `StageOK` checks the appropriate relation for the stage and subject; an unrelated payload constructor cannot pass. Every required producer completed for this mode; absence, crash, unknown or unsupported state is incomplete. |

Required jobs come from `requiredJobs` over scope, mode and fixed applicability, never a
caller-selected subset. `Plan` requires the supplied `JobKey` array to equal that derivation, with
every key belonging to the same claim; natural-number result slots are positions in that exact
array, not new semantic identities or caller-selected requirements. In execution modes, every
recorded successful executable-contract root must be represented among the environment's
execution roots. A fresh project requires configuration and discovery, a fresh
warning-free build, logical admission, every owned declaration's policy, every execution root
and closure, the required transcripts, histories and origins, and documentation presence; an
incremental project has the same policy obligations over an incremental build; a fresh file
requires its own compilation, admission, declaration policy and closure, with no whole-project or
documentation-presence coverage; fences keep §7.7's logical-only contract; a serialized graph
requires every selected root checked. Empty modules, empty root sets and fence-free Markdown are
accepted only after their discovery, build and scan jobs complete; a project still needs a
nonempty library surface. A discovered root-package library with no modules is refused, even
when it is excluded.

**The report account.** Every verdict line and every `completed` status is rendered from
`Account.account run` (claimed `RegulaCore.Account`). `Account` is the subtype of projections of
some `AcceptedRun`; `Status.completed` takes one and the refusal statuses carry none, so
`Status.completed_accepted` proves a `completed` status has an accepted, complete, policy-satisfying
run behind it.  `AccountContract` (`checked_account`) states its meaning: mode, scope, surfaces,
toolchain and job count are the run's own; coverage is `coverageOf` the mode, whole-project exactly
for a fresh project claim (`coverage_fresh_iff`); the listed contracts are exactly the accepted
inventory's; execution counts are `executionSummary` of each environment; fence counts partition the
accepted fences; the residual identifiers stay unresolved. That the run is the current request's is
each caller's binding, checked by inspection, as is the use of `Account.pass` for project, file,
build-lint, combined and graph verdict lines. The documentation audit prints no PASS verdict, and
its per-fence labels come from task results once an `AcceptedRun` exists. Rendered text and
`acceptance` JSON are unproved adapter output; JSON is never decoded into acceptance.

**Success owners.** Only these routes construct acceptance; help, planning, internal workers,
editor hooks, registry and site validation, self-tests and qualifiers have no audit certificate,
and an editor snapshot result is never promoted to project acceptance. A rejected policy example
or an INCOMPLETE diagnostic demonstration is not an audit-success certificate.

| Route | Accepted value and remaining boundary |
| --- | --- |
| `AxiomGate.auditSurfaceAt` (fresh, `--incremental`, `--build-lint`) | `Acceptance.freeze` reconciles Lake modules, sources, configuration, dependencies, reports, replay inventories and origins; `Acceptance.finish` returns `AcceptedRun` with checked equality to `finalize` (`finalize_collection_error`, `finalize_of_collected`). Cached build artifacts never cache a policy decision, and build-lint has no second exit-code-only PASS branch. |
| `Lint.run` (`lake lint`) | The same project audit; exit 0 only through the claimed `Lint.classify` (`checked_classify`, `accepted_sound`): a zero audit exit and a recorded `completed` account of the requested mode. Exits 1, 2, 3 classify rejected, configuration-only and incomplete statuses; a missing or disagreeing status is 3. That the recorded observation is this invocation's audit is checked by inspection. `--explain-config` validates the manifest and Lake scope with the audit's own functions (`Manifest.load`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`) and issues no audit certificate; it and `--help` are read-only, exit 2, refuse `--json-out` and `--verbose`, and first invalidate any recognizable `--json-out` destination. An error escaping `Lint.run` is exit 3, or 2 for a `manifest-` refusal, never 0 or 1. |
| `AxiomGate.auditSurface --with-docs` | One process: the project plan and the documentation plan over the same snapshot and build, joined by `combineAccepted`; no evidence crosses a process boundary between the stages. |
| `--acceptance-link PATH` (`axiomGate`, `docFenceAudit`) | `axiomGate` records the link for fresh project success only (no `--with-docs`): after `AcceptedRun`, the SHA-256 of the copy-relative accepted sources, configuration, dependency captures, `docs/` Markdown and, with `--verso`, the Verso library's inputs; `docFenceAudit` computes the same identity from its own fresh capture before building and refuses unless it is equal. `axiomGate` invalidates PATH before the audit starts and records the identity only after its outer configuration recheck passes, so any refusal leaves it incomplete. Equality establishes identical captured inputs; `shasum` and the filesystem are trusted. |
| `AxiomGate.auditFile` with a conforming profile | A `freshFile` plan and `AcceptedRun`; dependencies stay incremental. No profile or a compiler-trusting file is `CLASSIFIED`. |
| `Documentation.auditBuiltProject`, `DocFenceAudit.run` | Markdown (and Verso) bytes, fence spans and task identities frozen before compiling; `finishDocuments` calls `finalize`. A corpus with a structural problem has no request plan: it reports each located problem and is refused. Group observations retain every unit and authenticate roles against the whole reconciled inventory; policy selection is per original fence. With `--verso`, the fresh build and render of the standard, then `Regula.Site.missingAnchors_nil_iff` for the registry's and the docs' links into it and `rowsMismatch_eq_none_iff` for its checklist rows. `Documentation.Sources.check` compares the documentation inventory and bytes before fence work and before `finishDocuments`; with `--verso`, `Sources.checkLinked` rechecks the linked inputs after the Verso build. |
| `RuleExamples.documentation` | Keeps the documentation driver's accepted run. Canonical positive completion additionally requires a nonempty, all-positive fence inventory; negative and teaching expectations stay classified; failed and incomplete checks retain their own outcomes, and the receipt retains each actual fence classification. The qualifier separately applies `PositiveClassifications` to require a nonempty list with every fence positive, passing and complete before admitting a positive correction. The adapter verifies the original requested documents before emitting accepted metadata. |
| `FreshChecker.run` | A separate `serializedGraph` claim; `leanchecker` success is an observed process result. |

**`lake lint` dispatch.** Lake's lint dispatch builds only the driver, so the driver first builds its
audit worker `regula/axiomGate` in the workspace `lake lint` ran in (never the `--project`
directory). That workspace built the driver, so it resolves the same `regula`, dependencies and
toolchain; a failed worker build is `INCOMPLETE`. Lake v4.34.0 does not change the driver's working
directory, and passes the dispatching workspace's package library directories, then
`LEAN_SYSROOT/lib/lean`, then any inherited `LEAN_PATH`, as its `LEAN_PATH`. The driver requires
the working-directory workspace's library directories and that directory to begin it
(`Regula.Checker.Lint.dispatchedFrom_iff`) and otherwise refuses with exit 2, so a driver started
outside Lake, by a Lake not collocated with the toolchain, or with `-d` from another project is
refused. The claimed targets are built with the audit-build marker `weak.regula.auditBuild`
([editor feedback](#editor-feedback)); Lake scopes it to the whole package in its module trace, so
modules last built with ordinary options are rebuilt for the audit and their replayed logs never
enter its warning check.

`./scripts/verify.sh` runs `axiomGate --acceptance-link tmp/acceptance-link.json --verso
website:RegulaStandard:regula-standard` after its builds and other required checks, and
`./scripts/verify.sh docs` runs `docFenceAudit` with the same arguments over every `docs/` fence and
every `lean` block of the standard. The shell's zero exit records completed execution of those
commands, not a separate Lean proof.

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
are preserved; a nonanonymous identity does not establish ownership or extraction authenticity.
A declaration's identity is its requested environment, snapshot, owning module and
exact name; a module's is its snapshot and name, and its source mapping must be functional (the
same module in two claimed surfaces is refused as ambiguous); a boundary's is its root, reached
declaration, kind, optional replacement and occurrence; a fence's is its document snapshot,
opening, body and closing byte spans, and its marker kind and expected pattern (generated
`DocFence_N` names are transport only). An executable root's identity is its requested
environment, snapshot and root module and name; multiple valid registrations within that
environment share closure work, but each registration remains a required declaration and contract
obligation. A job's identity is its claim, stage tag and exact subject key, including the
requested environment for local stages; attempts are transport metadata, not new required jobs.
Set-valued observations use canonical sorted duplicate-free collections from Std's extensional
structures; mutual groups and transcript commands stay ordered. Axiom lists, module sets and closure
edges have set semantics, with proved lookup and membership laws independent of storage order;
canonicalization preserves membership. Duplicate observations are refused even when equal.
`ResultState` carries unique keys, a subset of the fixed plan and valid payload bindings; empty
construction and every insertion preserve that invariant, and no unchecked mutation or raw JSON
constructor returns this state.

The census is created by traversal before any policy outcome is filtered: freeze Lake targets,
sources, manifest and Markdown; complete the mode's build, import and admission stages and take
the census of owned declarations, roots and required transcripts; then freeze the required jobs
before collecting results. `Census.requests` is the ordered array of environment requests, and
`CensusOK` requires the returned requests to equal it and their positive module partition to be
the whole claim. An ordinary (non-serialized-graph) project claim requests
`SurfaceAssignment.environments` for each surface in order: the library's modules, then each
claimed executable's root alone (`census_executable_alone`; `acceptedRun_executable_alone` for
every accepted ordinary project run), because two roots that each define `main` cannot share one
environment. `InventoryValid`
requires unique names within each Lean environment; different environments may each define
`main`, and their inventories are never merged. Each
`EnvironmentCensus` retains its complete admitted policy inventory, transcripts, execution roots,
replay arrays, sources and origins. No entrypoint is renamed, filtered or exempted. Configuration,
discovery and build jobs occur once. File and graph paths use one environment; document plans use
no project environment and retain their exact fence inventory and modes. `Roles.eq_authorize`
and `frozenEnvironmentRoles_eq` prove the role receipt frozen per environment equals
recomputation, so roles are not re-authorized per job and no worker flag is trusted.
`Common.mapWorkQueue`, `admitIndexedWorkerResults` and the documentation collector run
`ResultState.collect` through `checked_indexedResults`: success returns exactly the array whose
indexed pairs are a permutation of the responses over every requested slot. Group reconciliation
preserves each requested environment separately and never deduplicates job responses, replay
occurrences or positive owned declarations; the full admission module, required and admitted
inventories survive the infrastructure partition.

**Admission by construction** (`RegulaPolicy.Domain`, `Admission`): declaration kinds, boundary
kinds, correspondence, foundation classes, profiles, modes, safety and evaluator roles are closed
types whose parsers refuse unknown tags (pretty types and messages remain open text);
`admitClaim` refuses unsupported scope/mode combinations; `admitInventory` requires unique
identities, structural references, canonical sets, agreeing safety fields and transcripts bound
to source bytes, compiler identity and valid coordinates (an inventory is still not an independent
census); `admitExecution` requires unique roots and boundary occurrences with valid native-origin
bindings; `BoundaryEvidence kind` keeps replacement equality, simplification equality and
opaque-body admission distinct, and a trusted native-runtime observation carries matching origin
data; `admitBoundaryEvidence` preserves correspondence, detail and native origin, refuses
incompatible extra evidence, and every representable value round-trips. Accepted canonical
external spellings re-encode identically. The pure codec proves
`decode (encode x) = ok x` over a tagged tree; that is not a theorem about JSON text. Worker
parsing (`Checker.PolicyCodec`, whose container recursion is adapted from Lean's JSON parser under
Apache-2.0) rejects duplicate fields before building a map, unknown and missing fields,
unsupported tags and numeric overflow; the parent waits for the child's exit and checks the
response against its own request.

**Trusted:** these relations concern supplied observations. `InfrastructureOK` binds the exact
reporter, codec and collector artifacts the IO adapter compares with the running checker's, their
receipts, ownership disjoint from owned and imported modules, and all observed incoming imports;
the public `Contract`, `Diagnostic` and `StructuralName`
interfaces do not imply a library-wide exemption.

## Declarations, foundations and roles

**Proved** (`lean/RegulaPolicy/`):

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| Least foundation | `leastFoundation_spec`, `leastFoundation_ext`, `foundationFor_least` | Every axiom set within Standard-Logical gets its least containing profile, invariant under order and duplicates. The actual public classifier (`foundationFor` with inventory-bound roles) uses this same result. Not the weakest possible proof of the proposition. |
| Classification | `foundationFor_iff`, `declarationFailure_iff`, `policyFor_ordered`, `OrderedDecision.unique` | Each of the six foundation classes (three labels, hole, unknown axiom, compiler-trusting) has its exact meaning; a declaration's diagnostic is its first failed requirement (invalid membership, owned axiom, hole, unknown, escape hatch, compiler trust, contract failure, profile excess). For an axiom set outside Standard-Logical, classification keeps the diagnostic precedence hole, then unknown axiom, then compiler-trusting. Renderer strings are not proved. |
| Declaration policy | `policyFor_none_iff`, `policyFor_conforming_iff` | Success is inventory membership plus the independent requirements; teaching never relaxes a conforming profile. A conforming request requires its permitted foundation, safety relation and recorded contract obligations. |
| Roles | `NativeTeachingOK`, `RecursiveHelperOK`, `authorizedNativeAxioms_iff`, `authorizedUnsafeRecHelpers_iff` | A name is authorized exactly when an inventory record meets every component (the §7.4 helper conditions; the three §7.5 native-axiom conditions). `RecursiveHelperOK` reads no transcript: it requires the regeneration observation (`unsafeRecRegenerated`), the helper's exact metadata, and a safe base of the same module and type whose axioms are within Standard-Logical, with the exact group mapping. `authorizedUnsafeRecHelpers_base` states those facts for every authorized helper; `partialParent_not_authorized` excludes the helper of an opaque (`partial def`) base. The observed replay and regeneration fields are inputs; the predicates do not prove them truthful. |
| Native axiom names | `nativeAxiomOrigin?_sound`, `nativeAxiomOrigin?_nativeAxiomName`, `nativeAxiomOrigin?_isSome_iff`, `compilerTrustingAxiomName_sound`, `compilerTrustingAxiomName_iff`, `modulePrivacy_nativeAxiomName`, `generatedPrefix_iff`, `native_generated`, `native_compilerTrustingAxiomName`, `native_provenance` | A name is recognized exactly when it is `nativeAxiomName parent t idxs`, Lean's own `Name.append` and `appendIndexAfter` as `nativeEqTrue` and `DeclNameGenerator.mkUniqueName` apply them, for `native_decide`, `decide +native` or `bv_decide`, with or without module privacy. `compilerTrustingAxiomName`, the execution probe's classification, holds exactly for these names and Lean's three compiler axioms. The prefix is nonanonymous without macro scopes and the generator indices are a nonempty list of positive numbers. For a declaration name without macro scopes in a module without macro scopes, a recognized prefix related to it by `GeneratedPrefix` (the name itself, or its `mkPrivateNameCore` form when it is public) gives exactly the names `DeclNameGenerator.mkUniqueName.curr` gives its native axioms, whether or not the module elaborates the proof without exporting (`modulePrivacy`). The recognition direction and that characterization assume `RuntimeStringAppend`, because `appendIndexAfter` uses the logically opaque extern `String.Internal.append`. The three tactic names and the list of `nativeEqTrue` call sites are cited from the pinned sources, not derived; hygienic and anonymous prefixes are not recognized. |
| Execution policy | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff`, `boundaryFailures_ids`, `rootFailures_ids` | No failure exactly when there is no unresolved path and every boundary meets its mode's relation; the failure kind of every boundary and path for every claim. |
| Correspondence | `DefeqComparison.classify_checked_iff`, `classify_trusted_iff`, `classify_unresolved_iff` | Checked exactly for a completed comparison with admitted evidence, trusted exactly for a completed one without, unresolved exactly for one that did not complete. |
| Expected diagnostics | `matchesPattern_iff`, `orderedLiterals_iff` | The restricted pattern's ordered leftmost-split match within one effective-error message. |

**Consumers** (paths from `lean/Regula/`):

| Operational caller | Proved pure function | Remaining boundary |
| --- | --- | --- |
| `Checker/Policy.admitScope`, with `Frontend.validateCoordinates` | `checked_scope` (first coordinate refusal in transcript order, then exactly `admitInventory` with `authorize`; success iff all coordinate checks and `InventoryValid` hold, retaining both input arrays); `checked_coordinates` (claimed `RegulaCore.Coordinates`: success iff `CoordinatesAgree`, refusal with the first unmet obligation in traversal order) | Lean's UTF-16 column function (`FileMap.leanPosToLspPos`) and `FileMap`; source and compiler observation acquisition. |
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
`boundaryEvidenceCandidate` take caller-supplied sets and authorize nothing; proof-facing
dependencies expose their existing definitions so exported proofs and downstream reduction keep
their meaning, which gives these helpers public bodies; `policyFor`, `foundationFor` and their
member forms require an inventory-bound `Roles` receipt, and the member forms
`memberFailure`/`memberFoundation` also require a proof that the declaration belongs to that
inventory, with registrations stating agreement on every member (`checked_memberRule` equals
`ruleFor` for every inventory member). `boundaryEvidenceCandidate` may discard incompatible fields,
while `admitBoundaryEvidence` preserves every supplied observation field, so use it when that
preservation is required. Generated-role validators execute the
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
| RG1006 | `authorizedUnsafeRecHelpers_iff`, `authorizedUnsafeRecHelpers_base`, `policyFor_conforming_iff`, `subject_contract`, `partialParent_rule` | Exact helper metadata, the regeneration observation and the base's axioms are checked, and a `partial def`'s helper always has a finding that names the `partial def` (its opaque declaration) when that declaration is in the inventory. The regeneration itself (Lean's recursion compiler rerun by `Collect`) and its erasure comparison, compiled-code correspondence and execution coverage are not proved. Admission does not establish that the helper terminates whenever the base does: Lean compiles the base from a body its `wf_preprocess` rules rewrote, which Lean documents can remove a subterm the compiled helper still evaluates, so the helper's termination trusts that preprocessing (standard §7.4). |
| RG1007 | `ContractOK` through `ruleFor` | Recorded contract failures are enforced; Probe's extraction of the proposition and root, proof admission and adequacy are not proved by this relation. |
| RG2004 | `policyFor_ordered` (membership first), `CensusOK`, `PlanOK` | Complete Lake and environment ownership acquisition. |
| RG3001, RG3002 | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff` | The theorems cover the supplied unresolved paths and boundaries, not complete root and closure discovery or external runtime correctness. |
| RG4003 | `matchesPattern_iff`, `orderedLiterals_iff` | One effective error under the restricted grammar; producer completion and effective-error extraction are operational. Policy-negative source fixtures keep their separate registry-bound expectation qualifier, and a rejection is not positive conformance. |
| RG5002, RG5003 | `materialDocumentationFailure_eq_none_iff`, `_eq_missingDocstring_iff`, `_eq_missingIntent_iff` (which docstrings each rule reports; the two never both fire), `hasIntentSection_iff`, `ruleForMaterialDocumentation_injective`; the native linter and the project gate both execute `RegulaPolicy.materialDocumentationFailure`, which `materialDocumentationFailure_eq_none_iff` ties to `MaterialDocumentationOK` | The ATX line grammar (`heading?`) is a definition with checked instances, not a theorem about Markdown (`intentHeading_examples`); `findDocString?` lookup is Lean's. Intent adequacy is R-INTENT. |
| RG2001–RG2005, RG4001–RG4004, RG5001–RG5003 | The stage relations above, composed by `accept_iff` and `accepted_report_identity` | The adapters that populate them. |

RG2006 checks the Lake options with a proved decision over Lake's resolved configuration
(`RegulaPolicy.Community.failures`, `failures_eq_nil_iff`), not by re-implementing any linter.
It admits Mathlib's header linter on only when the target configures the linter's license option
(`conforming_header`, `header_on_unlicensed_fails`); every other required option admits only its
required value (`admits_of_ne`). The license option counts as configured only when `leanOptions`
gives it (`licensed_iff`); a `-D` extra argument that gives it a value can only make the target
fail. That the linter compares the header with that option is read from Mathlib's source and
assumed.

**Correspondence resource bound.** `checkCorrespondenceProof` gives the kernel Lean's
per-declaration default heartbeats (`Core.getMaxHeartbeats` of the default options), so a
checker-added obligation costs no more than one the adopter could write, and runs under Lean's
runtime memory limit. The limit is fixed once per process, at its first correspondence check, to the
process's peak resident size then plus 1 GiB; it is set only while a check runs, never exceeds a
`max_memory` the shell set, and is restored afterward. Argued from the Lean runtime source, not
observed: the kernel throws only when current resident memory reaches the limit, so the first check
never fires on memory already held, and because the limit never re-reads the peak, an exhausted
check cannot raise the next one's limit. The 1 GiB is shared by every later check and other growth
in the worker, so after one exhaustion later checks may exhaust at once; they fail closed as
unresolved. At most three report workers run, each running its checks sequentially, so checks add at
most 3 GiB above those workers' first-check peaks; that increment does not by itself bound the
audit's total memory. Supplied and then discovered theorem candidates are tried before the
kernel-defeq check, to keep a kernel-exhausting unfolding within one comparison from consuming the
headroom a supplied proof needs, so a replacement with both reports `proved:` evidence; kernel
resource exhaustion is never conflated with rejection; a theorem candidate whose admission exhausts
the kernel supplies no evidence, like any candidate the deliberately incomplete search cannot use.
The correspondence cache in `Probe.environmentReport` stores checked results by name pair within one
fixed environment, and replacement-history worker output is shared within one audit only under
identical inputs (standard §7.6); no cache crosses environments. A cross-environment cache would
need equality of all relevant inputs, revalidated evidence and a proof that varying candidate data
cannot weaken acceptance. Generated-role and canonical runtime recognition determine policy
authority and are not untrusted acceleration hints; profiles, scope and pins are normative
configuration, not freely variable candidate data. An incomplete comparison is unresolved with the
reason that the kernel ran out of resources before deciding definitional correspondence; mapping the
kernel result to the outcome (`kernelExhausted` for an incomplete comparison, a rejection or a proof
beyond Standard-Logical for a completed negative one) is checked by inspection, and the kernel
decision itself is trusted.

## Producers

The producers turn a completed Lean environment into observations; their correctness is not
inferred from any pure proof.

- **Census.** `Probe.environmentReport` freezes `(owning module, declaration)` keys from
  `Probe.ownedConstants`, and ordinary and registered executable roots (private or imported),
  before building observations. No policy-success filter defines either census.
  `Probe.ownedConstants` traverses imported module indices, so it is not a current-document
  inventory. An inspected empty root set is `some #[]`, an uninspected one `none`. Only valid
  registrations add executable roots, and all registrations remain in the declaration observations
  even when several registrations share one root.
- **Admission.** `Admission.validate` replays safe, nonpartial owned declarations and their owned
  dependencies with the pinned `Environment.replay`, checks every required entry is in the
  resulting kernel and returns a typed receipt. It returns
  `IO (Except ProducerReport.AdmissionFailure ProducerReport.AdmissionReceipt)`: a successful
  receipt's required keys come from safe, nonpartial original kernel entries in the replay scope,
  and it records the admitted keys. Replay scope includes owned dependencies and the existing
  reporter closure where required; it may exceed the reported surface. Imported unowned modules
  remain trusted; the receipt records the completed operation and does not authenticate replay.
- **Admission reuse.** The project audit inspects every library environment before any
  executable's, and hands the executables the libraries' completed admissions
  (`Admission.PriorAdmission`). An executable's environment keeps an owned module other than its
  root in the replay base instead of replaying it (`Admission.reusedModules`; the receipt's
  `reused`) only when (1) a handed-out library admission replayed it over the identical import
  closure (`Admission.importClosure`: the same modules, canonical `.olean` paths and import
  edges); (2) every owned module of that closure is a claimed library module all of whose
  `.olean` parts (the `.olean` and, for a module-system file, the `.olean.server` and the
  `.olean.private` Lean takes its kernel constants from) the coordinator read before the first
  inspection and compares, presence and bytes, after the last (a change is RG2005, incomplete);
  (3) each declaration of each owned module of the closure refers only to constants of its own
  closure (`Admission.referencesWithin` over `ConstantInfo.getUsedConstantsAsSet`, the
  dependencies `Kernel.Environment.replay` replays first); and (4) every owned module of the
  closure is reused too. If the filtered set misses (4), nothing is reused. Every other owned
  module is replayed. **Proved** about the executed definitions: `Admission.mem_reusedModules`
  (a reused module is owned, unrequested and satisfies (1), (3) and (4)) and
  `Admission.reuseJustified_sound` (the coordinator's recheck of a report accepts only
  unrequested modules a handed-out admission offers over the report's own closure). **Checked
  at run time, not proved:** that the handed-out admissions list only replayed modules whose
  closures are frozen, (2), and that a closure contains every module its members import
  (`Admission.validate` still refuses a base module that imports a replayed one). **Derived, not
  machine-checked:** the kernel's check of a declaration depends only on the declaration and the
  constants it consults, which its references and their values reach. By (3), (4) and the
  imported base's own references, a reused module's declarations consult only its closure; by
  (1) and (2) that closure is the same bytes in both environments, so the library environment's
  successful replay is the one this environment would repeat. This rests on the stated trusted
  boundary: authentic imported artifacts unchanged during the audit (as the history memo already
  assumes), filesystem reads, and no change restored between the two byte observations. No
  theorem models the kernel. Reuse is scoped to executable environments: library environments
  still replay every owned module they load, including one another library environment also
  replays, a cost that predates per-executable environments and this reuse does not address.
- **Documentation.** `Environment.loadReportCoreAtSearchPath` freezes the `@[regula_material]`
  selector from the completed owned environment and reads module docs (Markdown and Verso) and
  docstrings with `Lean.findDocString?`, the same lookup as native feedback, so the project gate's
  RG5001–RG5003 findings do not depend on whether native feedback was imported. Observed RG5003
  evidence is the fresh-project corpus pair and the native `MissingIntent` control; no incremental
  or build-lint RG5003 run is claimed.
- **Transport.** `Report.Collected` adds extraction keys to the pure policy report;
  `Checker.ProducerReport.Environment` adds the operational receipts and owns their JSON decoder:
  `census` (requested modules, declaration keys, optional execution root keys and root/module
  history requests), `admission` (replay modules, required keys, observed admitted keys and
  reused modules),
  `documentation` (every module's presence, including declaration-free modules, frozen material
  keys and exact optional docstrings), `histories` (one completed source receipt or explicit
  unavailable outcome for every requested module) and `sourceBindings` (exact loaded-owned
  module/path/text snapshots). Use `--json-out` to consume producer evidence. **Proved:**
  `ProducerReport.validate_sound` shows every report `Environment.validate` admits is
  `Environment.Admissible`, restating every executed guard (a nonempty, unique, loaded module
  census; a declaration census equal to the reported keys in order and duplicate-free; execution
  results exactly for the requested roots; `ExecutionValid` closures; unique located source
  bindings covering every claimed module and range; a replay receipt admitting exactly its unique
  requirements and requiring every safe, total declaration; documentation observations for
  exactly the claimed modules and unique material selection; unique history requests with exactly
  one history per requested module; completed histories located, source-stable, bound to the
  owned snapshot when the module has one and free of anonymous edge endpoints; unavailable
  histories leaving every requested root unresolved; requested runtime replacements whose
  resolved edges appear in completed histories; root/boundary module attribution with exact
  replacement-edge channels; and, for every current replacement reference, a reached,
  attributed, requested and recorded module history, with the root's historical edges the
  canonical form of exactly those completed-history edges); `validate_eq_ok` decomposes the guard
  sequence, `validate_nonvacuous` exhibits an admitted report and `fromJson_admissible` extends
  soundness to the decoder. Producers, documentation groups and acceptance call
  `checked_validate.run`; the project report worker skips its own call: the coordinator's decoder
  runs the same check once and keeps its success as a `ProducerReport.Admitted` proof
  (`fromJson_admitted` shows it accepts and refuses exactly as the plain decoder), and
  `Acceptance.freezeEnvironment` requires that proof instead of re-running the check and takes
  the execution inventory from it (`Admitted.admitExecution_eq`). These do not authenticate the
  observations; a direct interactive dump has no loader receipt and cannot pass the decoder.
  Replay and source-evidence failures cross workers as typed
  `ProducerReport.Outcome.admissionFailed` (the shared `Environment.validateSourceEvidence` guard)
  and surface as RG2005, incomplete; initial setup failures stay RG2001. A transported refusal is
  consumed only after worker-packet validation; the parent's own snapshot check can return a typed
  refusal even when a worker crashes or a packet is malformed, and this does not accept or
  authenticate that worker result. Documentation retains its fence finding alongside the typed
  refusal, using fence context without manufacturing a valid declaration range.
- **Replacement histories.** The walk registers each `(root, module)` history request first; the
  loader keeps the Lean-resolved path, the exact bytes before and after an isolated worker and the
  ordered replacement edges, so earlier choices overwritten by later attributes are kept. A
  changed source or unsupported evaluator yields `unavailable`, never a completed receipt. A
  runtime-replacement boundary must have a registered request, and completed execution requires
  its replacement edge in a completed history. Logical-only inspection has no execution roots,
  requests or history receipts.
- **Closure.** `ExecutionRoot.closure` records the actual `Probe.executionWalk`: each first visit
  with its owning module and the earlier visit that queued it, and separate edge channels
  (`logicalEdges`, constants used by the logical bodies the walk follows; `candidateEdges`, every
  inspected constant-equality candidate; `historyEdges`, replacement choices from completed,
  source-bound module histories; `currentReplacementEdges`, current `implemented_by` choices
  retained even when history is unavailable; `activeSimplificationEdges`, active simplifications
  used by the replacement-only cycle check, each also a candidate; `helperEdges`, explicit
  opaque-to-partial-helper traversal; `requiredCode` and `unavailableCode`, where a nonempty
  unavailable subset requires unresolved execution). `ExecutionRoot` itself carries
  `compilerEdges`, the retained IR calls, closures and initialization dependencies. Their union is
  a conservative traversal, not a selected or minimal call graph; a missing closure never yields an
  empty boundary set. Every enqueue site records its edge and parent visit together, and
  visited-name suppression stops recursion without deleting self edges. Retained IR edges use the
  declaration step of Lean's pinned `IR.CollectUsedDecls.collectDecl`, because `collectUsedDecls`
  also inserts the declaration itself and filtering its result would discard genuine recursive
  calls; this specialized API is requalified on a toolchain upgrade. `Environment.validate` calls
  `admitExecution` at producer and decoder boundaries, reconciles visits with available module
  attribution, requires exact candidate/replacement boundary coverage and binds each historical
  edge set to its actual module receipt; missing or inconsistent observations refuse inspection, so
  no omitted record becomes a clean result. The initial visit is the root, and the sorted `nodes`
  census is exactly the set of these visits, with no duplicate visits.
  `RegulaPolicy.ExecutionClosure.Valid` checks the supplied census, discovery witnesses, canonical
  edge channels, endpoints, code obligations and unresolved requirement; `ExecutionRoot.Valid`
  additionally reconciles boundary names, replacement targets and compiler callers, and the
  induction uses the strictly earlier parent index, not another graph search. **Proved:**
  `ExecutionClosure.discovery_induction`, `nodes_induction` and `admitExecution_preserves` (over
  the executed admission, not a separate graph model): for a closure satisfying `DiscoveryOK`
  (respectively `Valid`), a predicate true at the root and preserved by each recorded edge holds at
  every visit (respectively every admitted node), and a successful admission retains exactly its
  roots and proves `ExecutionValid`. They establish connectedness and structural admission, not
  completeness or authenticity of IR extraction, that a candidate edge executes, machine-code
  correspondence or intended-specification adequacy. An active `csimp` self-edge stays an
  unresolved replacement-only cycle (RG3001). Reflexive constant equalities remain in the candidate
  set, so that self-edge satisfies the active-edge subset invariant; an inactive reflexive
  candidate does not create an active cycle, and ordinary recursive IR self-edges remain a separate
  channel.
- **Source binding.** `ProducerReport.SourceBinding` keeps module, path and exact text. Project
  checks capture Lake's source map and configuration before building; the loader checks source
  before import and after inspection, and transcripts, histories and every declaration range must
  match the frozen text. Requests carry the frozen sources; producer and parent compare the
  report's loaded-owned subset with that request, worker requests use `sourceBindings` as their
  sole source map, and loader module/path pairs are projections of those bindings. Locations and
  result exports reuse the frozen text; they do not recapture newer text as if it had been
  checked. Grouped documentation and fixture inspection receive the exact
  `Compilation.spec.source` values instead of recapturing them after compilation, and batch
  compilation creates snippet files in its parent before dispatch, which workers consume without
  rewriting. `SourceBinding.withUnchanged` rechecks sources and configuration around every
  frozen-input operation, including failed builds, crashed workers and decoding failures, and
  returns a typed refusal (RG2005, incomplete) on a change while preserving the original outcome
  otherwise. This includes missing or unreadable previously frozen source or configuration, and
  read failures preserve the underlying IO reason; initial environment and setup failures remain
  RG2001, and only re-reading existing frozen evidence receives this normalization. Terminal
  results keep captured sources (`sourceAccount`) even on failure; an absent or partial account
  does not establish coverage. Capture callbacks retain the growing account in memory, and
  serialization occurs at terminal success/error boundaries; when an outer handler has no
  captured sources, it preserves any account already serialized by the worker.

**Trusted:** Lake build semantics, compiler and imported-dependency authenticity, filesystem
reads, and the absence of a change restored between two observations. Byte equality is an
observation, not a filesystem lock or a source-to-`.olean` theorem. Imported unowned source is
inspected only when required by an existing history obligation; this does not add full-Mathlib
analysis to Core-only adopters.

## Inputs and dependency identity

Every acceptance route freezes the inputs it consumes before building: Lake's root inventory and
canonical source paths, root bytes, the manifest, Lake configuration, lock and toolchain files,
and each dependency's declared inputs (Lake's buildable library domains and executable roots,
with submodules a glob admits). `Snapshot.inputsUnchanged` rediscovers and rereads them all once
at the end, refusing any addition, removal or change; the combined route rechecks after its
documentation stage. This rediscovery runs even when the dependency array is empty; it compares
against the original records and never replaces the accepted request. Configuration observations
retain presence and exact bytes for the selected manifest, Lake configuration, lock and
toolchain. No Markdown is a refusal; no whole-workspace scan substitutes for the Lake inventory.
Dependency inputs are captured independently of Git ignore rules. Unused dependency executables
need not ship source files, while root-package targets remain required and terminal rediscovery
detects executable source additions and removals. Configuration paths come from Lake's actual
package configuration and manifest, plus toolchain and default-config presence checks.
Standalone and rule-example documentation callers capture dependencies before their
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
bytes exactly. Observed with Git 2.54 and `core.ignorecase`, literal pathspecs also matched
tracked paths and final components byte for byte, and the one divergence was an input under an
untracked directory whose leading components differ from the on-disk spelling only by case on a
case-insensitive filesystem: the unrestricted status spells the on-disk path, so that input reads
clean. Only the reported bit, never a captured byte, is affected. Non-UTF-8 fields are dropped,
since they cannot equal a declared input. Every declared input's bytes are still read and
UTF-8-decoded, and the terminal recheck recaptures them. The status output itself is not
retained, nor is any Git diff, untracked-file content list or directory-wide bytes; unrelated
files and build outputs are not inputs merely because they share a dependency directory.

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

`Collect.declaration` reduces a declared type only when the reduction could produce
`Regula.ExecutableContract` (`ContractScope.mayReach`). That holds when the contract type is among
the type's constants, closed under unfolding, and only modules that import `Regula.Contract`
contribute constants. For a recursion helper it reruns Lean's own recursion compiler on the
helper's group (structural recursion first, then well-founded recursion with every decreasing proof
elided), with only the toolchain's own `wf_preprocess` rules and the checker's built-in macros,
tactic and term elaborators, generating no code for the fresh definitions, and compares each
regenerated definition with the observed one up to compilation erasure: proofs and types, each
classified in its own side's context, are erased and a well-founded fixpoint is compared without its
relation or measure (`Declaration.unsafeRecRegenerated`). It never uses
`Meta.isDefEq`: where two values differ under a recursive call, its lazy unfolding of the
self-referential helper does not terminate. The regeneration runs Lean's elaborator in the report
worker and is undone before the comparison, which reads the observed definitions and decides erasure
in the inspected environment; a comparison that throws counts as no regeneration. The report's
other elaborator observations (`Meta.isProp`, the pretty-printed type, and `Probe`'s
executable-root classification) run under Lean's default limits. When one fails,
the report worker's error names the module, the declaration (for an execution walk, its root) and
the failing stage: `declaration record` (any observation of `Collect.declaration`),
`executable-root classification`, `proposition test` or `execution walk`. When the failure is one
of those limits, or a kernel limit (deterministic timeout, deep recursion or excessive memory,
recognized by its pinned Lean v4.34.0 message), it says the limit is the checker's own, that
options set in the source, such as `maxRecDepth`, do not apply to the checker, and to report it
as a Regula issue; the audit is still incomplete. The recursion helper's regeneration and native
replay, which otherwise record their own failure as missing evidence, rethrow such a limit
instead. A replacement's correspondence search rethrows an elaborator limit, but its kernel check
runs under its own budget and records exhaustion as an unresolved correspondence (standard §7.6).

The adapter runs the same pure policy and total failure-to-ID mapping as the project checker
(`Regula.Checker.Policy.editor_decision_rule`); a potential generated-role exception is deferred
as RG2005 rather than guessed. Recoverable compiler errors can leave hole-bearing declarations,
which still yield RG1002 while the original compiler error is preserved; unavailable collection is
reported as such. A module or project finding keeps its module or project location: Lean hosts
module findings at the end of the in-memory file and configuration refusals at the owning
command, never at an invented declaration. An unsupported `regula.localFoundation` request is a
configuration violation on each affected nonterminal command snapshot, including
declaration-free commands, and is intentionally not deduplicated across independent snapshots.
The module hook owns only the imports-only configuration fallback. This ownership uses the normal
Lean language frontend's preceding-command array, and the low-level
`Frontend.elabCommandAtFrontend` API is not a supported feedback driver.
`liveFeedback_auditBuild` proves `liveFeedback true scopeValue = false`: under the audit build's
import-time marker the feedback switch is off whatever a command scope sets `linter.regula` to;
that every local finding is gated by that switch is checked by inspection. Disabling local
feedback cannot disable a mandatory project predicate. Enabling it cannot reach a project audit's
own build: `lake lint`'s claimed build and the audit's fresh elaboration pass the unregistered
command-line marker `weak.regula.auditBuild`, which the linter reads only from a module's
import-time options and under which it emits nothing.

**Documentation presence.** `Lean.findDocString?` accepts ordinary, Verso and inherited
docstrings; private names follow Lean's visibility and never enter the public `@[regula_material]`
selector. RG5001 reads Markdown and Verso module-doc metadata loaded with `importAll := true`,
`loadExts := true` and `level := .private`; an empty loaded array means absence, an unknown module
identity is unavailable evidence rather than an absent doc comment, and current metadata is
checked only after module completion by the module hook. RG5001 reads the header's imports with
Lean's `parseHeader` (`HeaderSyntax.imports` without the implicit `Init`) and parses the first
command once with `topLevelCommandParserFn`; a first command that does not parse is not a module
docstring. Presence alone does not discharge module 5's requirements.

The production linter reuses Lean's `getNewDecls`, `getDeclsInCurrModule`, the linter hooks,
declaration ranges, axiom collection and docstring APIs; no upstream code is copied. The project
reporter force-loads the shared collector from the exact checker artifact. Its presence is not an
import by the claimed source: the excluded-library scan omits it only when no non-probe module
imports it, real source imports keep their exclusion checks, the forbidden Report/Probe scan still
inspects it, and neither the linter nor manifest scope is exempted. `qualify native` and the
`checkerSelftest --policy-domain-only`, `--native-adopter-only` and `--forced-collector-only`
controls are bounded observations of this API behavior, not proofs about arbitrary plugins,
native machine code or editor interaction. VS Code behavior (opening the link, the Problems-panel
fallback, code serialization, non-BMP and CRLF ranges, stale and cancelled snapshots, and the
absence of any Lean-manual link) was observed, not proved. An ordinary browser link check is not
editor acceptance.

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
(`parseCommand_arguments`, `parseCommand_sound`, `parseInvocation_arguments`,
`parseInvocation_sound`). Result stages: `stagesOf_required`,
`stagesOf_ordered`, `withDocs_ordered`, `notRun_completedStages_eq_nil_iff`,
`completedStages_idem`, `guidanceFields_recorded`, `parseStage_stageName`. Snapshot size:
`snapshotJson_configuration_independent`, `environmentJson_imports_independent` and
`Environment.resultJson_imports_independent` (`rfl`) show the rendering does not depend on
dependency text or import lists; the resulting size bound is an argument from construction, not a
theorem about byte counts. In the excluded library, `RegistryCodec.mode_roundtrip`,
`mem_firedRules` and `firedRules_nodup` depend on `propext` alone, and `rule_roundtrip`,
`nameParts_roundtrip`, `name_roundtrip` and `Regula.sortFindings_entries` on `propext`,
`Classical.choice` and `Quot.sound`; `RegistryChecks` bounds them to Standard-Logical.

These theorems concern text and data as functions of their inputs: that the checker supplies
every finding, and that the process writes the lines, are operational. `admitGuidance` checks a
result's consistency against writer regressions, not authenticity: a report edited to be
self-consistent passes. `RegistryChecks` exhaustively checks the 22 descriptors, the embedded
examples and the committed skill file, and exercises malformed transport, missing and duplicate
routes, unsupported modes, Unicode/CRLF coordinates, native/text agreement and incomplete
negative outcomes as observations of those boundaries, not sampled evidence for the universal
theorems. JSON text parsing, `FileMap`, and the compiler's collection of names, ranges and source
identity are trusted.

## Project setup and releases

**Proved** (`RegulaCore.Setup`, over the observation `regula init` and `regula doctor` read):
`plan_idempotent`, applying `init`'s plan leaves an empty plan, so a second run writes nothing;
`plan_eq_nil_iff`, the plan is empty exactly when every setup issue is one `init` does not fix;
`issues_run`, the plan removes exactly the fixable issues and adds none. The option check covers
exactly the claimed targets (the root targets the manifest does not exclude, and none while an
existing manifest fails RG2002), as RG2006 does: `run_sets`, every required option a claimed
target built without is then set to its required value as `RegulaPolicy.Community.sets` reads
it, which meets RG2006's requirement on that option (`meets_of_sets`); `resolved_run`, every
claimed target then has a value for every required option; `run_options_unclaimed`, when a root target is excluded the package's options
are unchanged, the options going into each claimed target's own configuration
(`run_plan_targets`), so none reaches an excluded target; and `run_options_prefix` and
`withAdded_prefix`, the options the package and each claimed target already give are kept. An
edit adds a missing piece and has no form that replaces a lint driver or an option value. The
starter manifest is planned exactly when there is no manifest and the package has a `lean_lib`
for it to claim (`plan_manifest_mem`); a package with none has a setup issue `init` does not fix.

**Checked when it runs:** `init` observes the project again after writing and restores every
file it wrote unless the new plan is empty, and it writes the starter manifest only after
`Manifest.parse` reads the text back as exactly that manifest. That the lakefile edits realize
the model's `apply` is this check, not a theorem. `doctor` runs the audit's own RG2002 functions
(`Manifest.load`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`) and RG2006
decision (`Community.failures`) over Lake's resolved options of each claimed target. It applies
Mathlib's options when the workspace contains Mathlib, where the audit applies them to a target
whose modules import Mathlib: by `conforming_of_mathlib` a target `doctor` accepts also passes the
audit, while `doctor` may ask a target that imports no Mathlib for Mathlib's options, which
`init` writes under `weak.` so they are then ignored. A module below a library root that no
library includes is a failing setup issue only when a claimed module (of a library or executable
the manifest does not exclude) reaches it by import through the package's modules, which the
audit rejects as outside every library; any other such module is a `note` that does not count
toward `doctor`'s exit status. That reachability is read from the sources' import headers, not
from a build.

**Trusted:** Lake's loader, its TOML grammar, Lean's import-header parser and Lean's frontend,
which elaborates a `lakefile.lean` as Lake does to locate the `package`, `lean_lib` and
`lean_exe` declarations, and the filesystem. Runs of `init` and `doctor` on scratch projects in
both formats (fresh, template, inline-table, structure-instance, bare-`package` and
computed-`leanOptions` shapes, another driver, a contradicting option, a stale skill, a library
without globs, left-out modules that a claimed module does and does not import, a library the
manifest excludes, with options written into bare and configured claimed targets, and a package
with no `lean_lib`) are bounded observations.

**Releases** ([procedure](contributing.md#release)): **Proved** in `lean/Regula/Release.lean`,
and checked by the kernel each time a step elaborates it: `tagAction`, the decision of the
candidate and publish steps, proceeds exactly for the head of `main` of an unpublished release
whose tag is absent or names the release commit (`tagAction_release_iff`), so publication, which
creates the tag, never leaves it naming another commit; it changes nothing once the release is
published (`tagAction_published`, `tagAction_skip_iff`), always proceeds on the head of `main` of
an unpublished release that no tag names elsewhere (`tagAction_converges`), and
`tagAction_refuse_iff` gives the remaining case. **Proved** in `RegulaCore.Edition`: a build
labelled a release is admitted exactly while its tag is absent or names its commit
(`labelAdmitted_release_iff`), and an artifact is deployable exactly when no release edition in
it was rendered from source (`publishable_iff`). The rest of `Release.lean` is operational,
including its check that a commit of `main` or of a pull request is unreleased and `adopt`, which
checks, with `git` trusted, that the release commit is the content CI derived from `main`'s
commit before CI records it as that commit. Its edits of
`RegulaCore/Edition.lean` are read back before use; its stamp of `RegulaCore/Rule.lean` is a
convenience that reads text. The kernel checks the edited modules' theorems when the release pull
request's checks and CI's checks of the release commit build them: `releases_ascending`,
`installed_listed`, `release_attributes_rules` (when `installed` is a release, no lifecycle
position of any rule is `.unreleased`; on the release commit this is the gate before anything is
published) and `lifecycle_listed` (every release a rule's lifecycle names is in `releases`). What
the steps observe (whether the release is published, the head of `main`, the tag), GitHub's
signature verification, that publishing a release creates its tag at the given commit, tags,
immutable releases, pull requests and workflow ordering are trusted.

## Rule examples and the corpus runner

**Proved:** `admitExampleRequest` admits exactly expected/observed request equality;
`admitExampleSources` admits exactly when every observed source is in the frozen snapshot and the
displayed text is in it (soundness and completeness), and file requests additionally require that
text at the requested path; `admitDemonstration_sound` and `_complete`, `demonstration_completed`,
`demonstration_observed_incomplete`, `demonstration_selected_rule` and `demonstration_not_accepted`
(an admitted demonstration fails every accepted-example kind, for any expected finding list);
`RegulaPolicy.incomplete_example_refused` (an incomplete outcome satisfies no fence expectation);
`positiveClassifications_sound`. `admitDemonstration` returns the unchanged observation with a proof
of `DemonstrationOK`: completed production, nonempty expected findings, a selected-rule incomplete
finding, exact mode and canonical diagnostic equality; the observed list itself must contain an
incomplete finding for the selected rule, without assuming injectivity of JSON rendering.
`Checker.RuleExampleQualification.qualify_sound`: every record `qualify` admits is
`RecordAdmissible` (current producer identity, parsed mode, equal before/after snapshots, the
observed request decoding to the frozen one, exit at most 1, sources in the bound snapshot with one
having the displayed text, for a file or diagnostic-only request one being the requested subject
with the displayed text, a result source account unless the request is diagnostic-only or
documentation, findings equal to the parsed diagnostics, one of three kinds, and `DemonstrationOK`
for a demonstration); it proves nothing about the producer that wrote the record.
`RuleExampleProjection.qualify_record` and `qualifyCorpus_records` give exact equality at the
adapter's canonical record constructor and over the full corpus, including ordered scans,
completeness and first refusals; their structural raw-tree laws avoid assuming parser
well-formedness, and they do not authenticate parsing, duplicate-key handling, serialization,
hashes, filesystem custody or subprocesses.

The runner's schedule is the pure `RegulaQualification.CorpusWindow`: `launched_le` (launched but
unconsumed tasks within the width), `launch_order` (every job launched once, in order),
`launched_eq_total` (under the window invariant, `s.consumed = s.total` gives `s.launched =
s.total`: no task is launched but never awaited) and `productions_nodup` (for a duplicate-free
`selected` rule list, distinct `(rule, phase)` workspaces). Task scheduling, `IO.asTask`/`IO.wait`
and process reaping are trusted. The runner shares one private copy of the root package and the
captured dependency roots with every producer and records a content identity of every entry (path,
`lstat` kind, length, 64-bit native hash) before any producer and after all are joined, and a
difference refuses the run; equality shows the end state equals the start, not that no write
occurred. Producers must not write the shared copy or dependency roots; no permission enforces this,
and nothing prevents a write, so `Slot.sharedIdentity` checks it only by content identity, recording
symlinks by resolution and never following them. The runner never changes shared dependency
permissions, so a deadline kill cannot leave the dependency trees read-only. Before any producer
starts, the runner makes one complete `Snapshot.dependenciesCaptures` and exports only its Git facts
(revision and dirty bit), injected into producers through the internal `ruleExamples
--injected-git-facts` entry, which `axiomGate` rejects, and each keyed by the exact capture request
(package, canonical root, and ordered source and configuration paths), as `injected-git-facts.json`
retained with the attempt's raw evidence and named by every producer registration. A producer reads
every source and configuration byte itself and uses an injected pair only for an exactly matching
request, so the private `regula` copy and fixture dependencies are always observed fresh.
`Snapshot.assemble_facts_eq` and `stateOfCore_congruence` show equal facts give identical captures
and bytes. Producers do not recheck an injected dependency at their own end; the campaign rechecks
the shared trees once, at run end, where `Snapshot.inputsUnchanged` rechecks the once-captured value
with fresh reads and fresh Git. Every producer still rechecks each non-injected dependency and its
own inputs; results carry `"gitFacts": "injected"`, which admission ignores. Root processes,
concurrent external writers, other file owners, filesystem honesty, hash collisions and writes
restored before the terminal check are trusted.  Records use a qualification-only view (top-level
`acceptance` and `documentationAcceptance` payloads null, every key and raw-tree shape kept), with
the exact detector bytes in `PATH.raw/ATTEMPT/RULE/PHASE/result.json`. Beside it are the registered
command/request/snapshots, stream files, terminal metadata and the compact original record; during
production the `INCOMPLETE` receipt points to these sidecars, and the full aggregate is written once
all records and controls are ready. The runner consumes records in fixed order and drains every
launched task before ordinary or exceptional scratch cleanup. Partial exports remain `INCOMPLETE`.
The runner does not re-read its own sidecars and requires unchanged terminal checker sources before
the final export, whose only writer, `saveCompleted`, requires the `Cleaned` witness that
`withScratchCleaned` constructs after scratch removal. `COMPLETED` attests what finished; the run's
verdict is its exit status: a deadline kill before the final save leaves `INCOMPLETE` and partial
files, a kill after it still fails the run, and every write inside the killed process group is
followed by an exit tail, so no such file is itself a verdict. Stream retention on kill covers
completed lines already read; only terminal observations claim complete streams.

## Qualification ledger

Each control is classified by what it can establish (standard §0 "The Role of Testing").
**Proved** controls sampled a pure function the checker executes and are replaced by a theorem
over every input; **External** controls observe a boundary no proof covers and are kept at the
smallest set exercising it; **Counterexample aids** remain only where the universal statement is
not yet proved, and are labelled so at their definition; they are not correctness evidence.

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
| checkerSelftest fixtures | in-process and CLI fixture verdicts; fence corpus; diagnostic-setup controls | compiler, elaborator, CLI and fence workers | External | observed |
| checkerSelftest fixtures | 11 execution-policy cases | failure kind per boundary and claim | Proved | `boundaryFailures_ids`, `rootFailures_ids`, `executionFailureRecords_empty_iff` |
| checkerSelftest fixtures | 12 scanner cases | `Documentation.scan` marker and fence problems | Counterexample aid | open: a step-function scanner with proved problem coverage |
| checkerSelftest structural | in-process manifest cases | `Manifest.parse` acceptance, decoding and the classified refusal classes | Proved in part | `Manifest.parse_sound`, `parse_input`, `parse_emptyExclusions`, refusal-class theorems; other refusals (a missing required field, an unknown exclusion key) are unclassified |
| checkerSelftest structural | real manifests, missing file, unlisted modules, fresh-checker coverage, CLI refusal rendering, Lake discovery, executable classification | file IO, CLI rendering, Lake inventory | External | observed |
| checkerSelftest cli, environments, build-policy, lint-driver | CLI sweep, adopters, clean checkout, ordinary build, `lake lint` exit classes | packaging, Lake and build integration | External | observed |
| ordinary | `qualify registry`, `qualify native` | CLI output invalidation, registry and site validators; compiler messages and ranges | External | observed |
| ordinary | `RegistryChecks` codec and source cases | registry, diagnostic and source codecs | Proved in part | round-trip theorems; open: state the remaining refusals as theorems |
| standalone | `qualify environments` finalize mutations | `finalize` refusals | Proved relation | `finalize_iff`; instance membership sampled |
| standalone | `qualify acceptance fences` packet mutations | worker-packet admission through a real proxy | External transport | admission proved (`checked_indexedResults`) |
| standalone | snapshots, input inventory, receipts, frozen exits, documentation source, closure, configuration and fence evidence | Git, Lake, filesystem, elaboration-time IO, signals | External | observed |
| project audit | executable admission reuse recheck | a report reusing an admission no library environment offered is refused | Proved | `Admission.reuseJustified_sound` |
| project audit | none | a frozen `.olean` part that changes during the audit is RG2005 | External | open: MUT-02 not yet evidenced; no intended-reason control rewrites a part between the freeze and the final comparison |

The `qualify` campaigns and what they observe:

- `registry`: six malformed invocations invalidate stale output; the validators accept real
  exports and refuse each removed field, the previous schema and a missing page.
- `native`: 42 compiler controls for identity, multiplicity, severity and warning promotion,
  ranges, current and imported ownership, private and generated coverage and both documentation
  formats. Each control is its own compiler process with its own source path, run four at a time
  in dependency order: imported-artifact controls after the artifacts they import, restored
  controls after every malformed one.
- `native-launcher`: 42 paired baseline/cached-environment controls with exact equality.
- `producers`: for the incremental and build-lint entrypoints and each of RG5001/RG5002, one
  workspace runs Fixed, then Violation over that Fixed build (so a stale build must not hide the
  violation), then Fixed again from a cleared build. A standalone executable additionally has
  positive and owned-axiom controls, each in its own fresh workspace, and each carries module
  documentation so the intended axiom violation is isolated. Each invocation checks exact stable
  ID, detail, primary location, related locations and result status, and requires unique output
  and exact embedded source/selector/type/axiom evidence. The fresh-project RG5001/RG5002
  observations are the rule-example corpus records, validated there by the same producer oracle.
  Optional raw export: `lake exe qualify producers --evidence tmp/producer-examples.json`; the
  export embeds exact source bytes and canonical diagnostic/result data, including the checker
  build identity, and supplies scoped source/evidence inputs, not the site's complete typed
  expectation validator.
- `history`: ten project and file invocations, each in its own fresh workspace, covering private
  and imported roots, reached-closure and source accounts, unsupported-evaluator refusal and
  source-snapshot changes.
- `rule-examples`: above.
- `closure-evidence`: reflexive candidate versus active cycle, retained recursive IR edges and
  range refusals through four invocation paths.
- `configuration-capture`: initial configuration IO failure through the project and file result
  protocols.
- `documentation-source`: both public documentation paths with changed and missing
  dependency/configuration inputs and fresh restored positives. Its `--source-read-only`
  selection adds original-file and declaration-build read failures, initial setup classification
  and restored positives. These observations do not establish universal IO correctness.
- `fence-evidence`: independent range, admission, policy and compiler failures inside positive
  fences, plus restoration.
- `frozen-exits`: frozen-input rechecks after imports and failed build and compilation
  operations.
- `input-inventory`: root additions and Markdown edit or removal during the prerequisite build, an
  actual new-module build and restored fresh controls.
- `documentation-dependencies`: both documentation commands retain pre-build dependency
  observations, and the combined project/documentation positive remains distinct.
- `receipt-boundaries`: timeout-selection and spawn failures (see
  [Operational assumptions](#operational-assumptions)).
- `acceptance fences`: fence-compilation packet mutations with positive restoration.
- `acceptance-snapshots`: `dependencies` (ignored Git and non-Git dependency input coverage and
  mutation), `history` (RG3001 fresh, incremental and build-lint history refusal and restoration)
  and `git-status` (the dirty decision against a literal-pathspec status for G1–G3, plus the
  symlinked-root and outside-root cases); `all` runs all three under one deadline. It checks typed
  root/source attribution and absence of acceptance on unavailable history; these are scoped
  operational controls, not a proof of IO extraction or a full acceptance run.
- `environments` and `self-audit`.

`producers` accepts an optional `--evidence PATH`; `environments --evidence PATH` and
`acceptance GROUP --evidence PATH` (group `fences`) take an evidence path.
`checkerSelftest --policy-domain-only` qualifies strict transport, external-adopter
public imports, forbidden probe imports, recursion-helper execution coverage and positive-file
warnings (a positive `freshFile` claim rejects warnings, including those emitted after a source
disables `warningAsError`); `--policy-transport-only` repeats just its parser, decoder and
admission controls; `--native-adopter-only` and `--forced-collector-only` qualify the production
linter import and the force-loaded collector. The pinned compiler leaves some generated
recursive-datatype helpers without standalone IR: the probe recognizes the inductive and recursor
relationship for that specific absence while keeping the helper as a root with its full source,
runtime-boundary and replacement-history checks, and retained compiler edges still require IR;
the public controls include both an authored tagged lookalike and a runtime-modified genuine
helper.

**The manifest** (`Checker.Manifest`, excluded library; axioms bounded to Standard-Logical by
the module's `collectAxioms` command). `parse_sound` and `parse_input`: every manifest the executed
`parse` accepts satisfies `Manifest.Valid` (nonempty surfaces, duplicate-free library and
executable names across surfaces and exclusions, well-formed target names, no compiler-trusting
claim, a nonempty rationale for every entry) and comes from JSON whose keys are all allowed and
whose schema version is 2, each array decoding element by element in order. Every name and
rationale is the JSON string, the claim is `Profile.parse?` of the JSON string, an absent
`executables` is empty and a present one is exactly its string array, and an absent `execution`
is `report` while a present one is `ExecutionClaim.parse?` of the JSON string (`SurfaceDecodes`,
`ExcludedLibraryDecodes`, `ExcludedExecutableDecodes`). `load` adds only the missing-file check
and the read. The refusal-class theorems (`parse_malformed`, `objectWithKeys_unknown`,
`topLevel_unknownKey`, `topLevel_schemaVersion`, `topLevel_emptySurfaces`,
`parseSurface_unknownKey`, `surfaceExecution_unknown`, `surfaceExecution_nonString`) give the
documented message of each isolated defect under their stated preconditions (unparseable JSON
gives `manifest-malformed`; a key outside the allowed set gives
`manifest-schema: LOCATION has unknown key(s): KEYS` at the top level, or for a surface after
accepted earlier surfaces; a wrong version with allowed keys gives
`manifest-schema: schema-version must be exactly 2`; an empty surfaces array with the rest of the
top level accepted gives `manifest-incomplete: surfaces must be a nonempty array`; an
unrecognized or non-string `execution`, once every earlier surface check accepts it
(`SurfacePrefixOK`), gives the `manifest-schema` execution message); other refusals, including a
missing required field and an unknown key in an exclusion entry, are not classified by a theorem,
and the public CLI controls remain external observations of how each class renders.
`parse_emptyExclusions`: JSON meeting the top-level conditions with empty exclusion arrays is
accepted with exactly its surfaces whenever they parse; it does not prove that any particular
surface is accepted.
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
checks that claim hypothesis at run time, and no theorem links that check to the hypothesis. The
text boundary is trusted: `Json.compress` is `partial` and `PolicyCodec.parse` runs core `partial`
parsers, so no theorem describes them; `parse_of_encodes` names what they must deliver. The
variants that rewrite the `AuditApp` surface after derivation are not covered. The lib-only
variant excludes every actual `AuditApp` executable it stops claiming, and app-omitted-exe
leaves them unclassified on purpose; claimed-exe keeps claiming them beside its added
executable, so two claimed roots each define `main`. `RegulaPolicy` stays
claimed in each copy because the checker probe's own imports resolve to it in a self-hosted copy.
`diagnostics structural` passed locally in 572 s without the deadline (observed 2026-09-27);
meeting the 420-second budget remains open, so it is not a CI job.

**Other proved oracles.** Quantifiers range over supplied Lean values; the IO drivers call each
`ExecutableContract.run`, so the evidence is required by their source linkage and erased at
execution, and calling a proved oracle does not prove the driver or its IO effects.

- `Checks.evaluate_success`: evaluation succeeds exactly when every supplied assertion holds;
  `evaluate_error` identifies the satisfied prefix and first false assertion, and
  `evaluate_append` specifies composition (`checked_evaluation` requires all three). An empty
  conjunction is permitted; each protocol supplies its own nonempty, explicit requirements.
- `Registry.validate_exact`: success exactly when the exit is nonzero, the root is an object,
  status is explicitly `incomplete` and the seeded `old` key is absent (present-null is not
  absent).
- `Native.validate_exact`: success exactly when compiler messages match in order and length,
  native identities match with multiplicity, exit outcome and stderr agree, native file,
  severity and help fields agree and any requested detail is present; `nativeMatches_exact` and
  `compilerMatches_exact` state the field and ordered-list relations.
- `Json.validateDecoded_exact`: a decoding error always refuses; success exactly when decoding
  yields assertions that all hold. `History.requirements` and `Producer.requirements` spell out
  the mandatory fields and their exact comparisons, and their registered contracts apply this
  equivalence to the actual decoders; neither proves the observations were extracted truthfully
  or that Lean's JSON parser matches a formal JSON specification.
- `History.validate_importedRootExecuted` and `validate_unsupported_unresolved`: every report the
  history oracle admits executes the imported registered root with a foreign module, and, for an
  unsupported evaluator, leaves every root requested from the audited module with nonempty
  unresolved evidence.
- `Evidence.checked_validation` and `checked_documentation`: exact conjunctions of decoded status,
  diagnostic, exit and transcript requirements, including distinct fence and project admission
  messages and the underlying IO reason.
- `Launcher.admit`: a proof-bearing mapping with nonempty unique names and both required search
  paths, admitting every valid decoded mapping; `checked_equivalence` requires exactly 42
  observations and full ordered equality of source, arguments, streams, exit, environment and
  resolved executable. Lake's environment is cached only within one fixed parent and workspace
  invocation, separately for the imported-control search-path override; neither observations nor
  compiled artifacts are reused, environment values are not exported, and durations are
  observations, not a speed guarantee or compiler-equivalence theorem.
- `Template.instantiate`: the required `Maps` proof for the recursive JSON transformation (array
  order, object keys and scalar kinds preserved; only entire matching string values change;
  depth exhaustion refuses, and the corpus uses 64 levels). Checker snapshots discover modules
  through Lake's elaborated inventory, not a source glob.
- `RegulaVerification.parseMode_sound`, `parseMode_roundtrip` and `select_exact`: exact argument
  binding and acceptance of every documented invocation; the caller consumes the proof-bearing
  selection, and recipes name the intended commands explicitly; `commands_nonempty` rules out an
  empty selected campaign; `dependencyFree_packages`: a root lock manifest that `dependencyFree`
  accepts has an empty `packages` array. Process execution remains IO.

## Operational assumptions

The supported compiler, filesystem, process runtime and GNU timeout are trusted. Each supported
public invocation runs under one non-foreground GNU timeout owning the whole process group,
including descendants with inherited output handles; OS scheduling and signal delivery are
trusted, not a real-time theorem. Acceptance passes an internal `--under-deadline` flag to
`qualify` so it does not detach a nested timer; the private flag is not a bounded standalone
invocation or an alternative acceptance command. Direct `lake exe qualify` campaigns have one
420-second process-group deadline. Before provisioning and any checker build, `scripts/verify.sh`
has `RegulaVerification` invalidate the selected mode's earlier PASS or accepted link and remove
an earlier site artifact (the private `--begin-attempt` flag), so a failed setup or build cannot
leave either in place. Each public invocation replaces its receipt with a fresh incomplete attempt
before any fallible timeout selection or spawn, and `qualify receipt-boundaries` seeds completed
evidence and exercises actual missing or unusable timeout selection and selected-timer spawn
failures for both `acceptance` and `environments`; the timed child carries the same attempt and
adds no new deadline. Acceptance keeps existing raw result/trace sidecars before parsing and
records partial file locations on the active case, and completed command records contain
executable plus argv; these are diagnostic receipt guarantees under trusted filesystem and process
IO. Scratch directories are removed on normal or exceptional return; a killed run's directory is
reclaimed by the next scratch user once no live process holds the scratch lock (`Regula.Scratch`).
Helpers invoke external programs with argument arrays, never generated shell programs. The
operator's narrow shell exceptions are recorded in [`AGENTS.md`](../../AGENTS.md).
