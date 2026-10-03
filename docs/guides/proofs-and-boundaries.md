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
| `ExecutionOK` (§7.6) | Every root's closure accounted for, no unresolved path; report mode permits reported trust, checked mode only checked evidence or a boundary of the toolchain's origin-checked trusted base. |
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
when it is excluded. A transcript job is derived only for a module declaring a native-proof axiom,
which every declaration-policy job refuses under its conforming profile, and every mode that
requires transcripts also requires declaration policy; so an accepted run plans no transcript job
(`accepted_no_transcript_subjects`), and a run with a transcript job is never accepted.

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
| `Lint.run` (`lake lint`) | The same project audit; exit 0 only through the claimed `Lint.classify` (`checked_classify`, `accepted_sound`): a zero audit exit and a recorded `completed` account of the requested mode. Exits 1, 2, 3 classify rejected, configuration-only and incomplete statuses; a missing or disagreeing status is 3. The audit's own exit code is the recorded `Lint.Observation`'s, or 3 when it recorded none or failed after recording a success (`gateExitCode`, `gateExitCode_some`, `gateExitCode_eq_zero`); an error escaping the audit discards any recorded result, so both sides are 3 (`AxiomGate.entry`). The driver reports the code the audit returned for its recorded result (`classify_gateExitCode`); the observation also decides the result status and the summary counts, each the number of findings of its impact (`Observation.status`, `Observation.tally`, `tally_eq`), and an incomplete finding exits 3 (`exitCode_incomplete`). Which findings a run records is operational. That the recorded observation is this invocation's audit is checked by inspection. `--explain-config` validates the manifest and Lake scope with the audit's own functions (`Manifest.loadFor`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`) and issues no audit certificate; it and `--help` are read-only, exit 2, refuse `--json-out` and `--verbose`, and first invalidate any recognizable `--json-out` destination. An error escaping `Lint.run` is exit 3, or 2 for a `manifest-` refusal, never 0 or 1. |
| `AxiomGate.auditSurface --with-docs` | One process: the project plan and the documentation plan over the same snapshot and build, joined by `combineAccepted`; no evidence crosses a process boundary between the stages. The documentation stage runs inside the project's frozen-input guard (`withSourceEvidenceOr`): a source or configuration change during it is the project's RG2005 refusal, which replaces the stage's result. |
| `--acceptance-link PATH` (`axiomGate`, `docFenceAudit`) | `axiomGate` records the link for fresh project success only (no `--with-docs`): after `AcceptedRun`, the SHA-256 of the copy-relative accepted sources, configuration, dependency captures, `docs/` Markdown and, with `--verso`, the Verso library's inputs; `docFenceAudit` computes the same identity from its own fresh capture before building and refuses unless it is equal. `axiomGate` invalidates PATH before the audit starts and records the identity only after its outer configuration recheck passes, so any refusal leaves it incomplete. Equality establishes identical captured inputs; `shasum` and the filesystem are trusted. |
| `AxiomGate.auditFile` with a conforming profile | A `freshFile` plan and `AcceptedRun`; dependencies stay incremental. No profile or a compiler-trusting file without a finding is `CLASSIFIED` (exit 0); the file audit's other exits follow its recorded observation as a project audit's do. |
| `Documentation.auditBuiltProject`, `DocFenceAudit.run` | Markdown (and Verso) bytes, fence spans and task identities frozen before compiling; `finishDocuments` calls `finalize`. A corpus with a structural problem has no request plan: it reports each located problem and is refused. Group observations retain every unit and authenticate roles against the whole reconciled inventory; policy selection is per original fence. With `--verso`, the fresh build and render of the standard, then `Regula.Site.missingAnchors_nil_iff` for the registry's and the docs' links into it and `rowsMismatch_eq_none_iff` for its checklist rows. `Documentation.Sources.check` compares the documentation inventory and bytes before fence work and before `finishDocuments`; that terminal recheck (with `Snapshot.inputsUnchanged`) and the fence audit run in `BaseIO`, so a failure of either is rethrown only after the structural problems and the fence results obtained are reported. With `--verso`, `Sources.checkLinked` rechecks the linked inputs after the Verso build. |
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
`SurfaceAssignment.environments` for each surface in order: the library's modules other than its
claimed executables' roots, then each claimed executable's root alone (`census_executable_alone`;
`acceptedRun_executable_alone` for every accepted ordinary project run), because two roots that
each define `main` cannot share one environment. A root inside its library is thus assigned once
(`SurfaceAssigned.disjoint`), and `surfaceAssignments_covers` proves of the executed assignment
that every module of a claimed library is assigned to one of its surface's environments, and
`census_covers_claimed_targets` proves of every valid project census that each module of a claimed
Lake target is one of its positive modules. An
executable's root may lie in a library only when the manifest classifies the two alike
(`RootsClassifiedAlike`, a conjunct of `TargetPartitionOK` that `checkClassification` also decides
before the project audit's build, and in `doctor`). `InventoryValid`
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
census); `admitExecution` requires unique roots and boundary occurrences with valid toolchain-origin
bindings; `BoundaryEvidence kind` keeps replacement equality, simplification equality and
opaque-body admission distinct, a trusted native-runtime observation carries matching origin
data, and only a trusted replacement or unsafe or partial computation can also carry one
(`TrustedEvidence`, `correspondence_of_toolchainOrigin`); `admitBoundaryEvidence` preserves
correspondence, detail and toolchain origin, refuses
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
| Execution policy | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff`, `boundaryFailures_ids`, `rootFailures_ids`, `boundaryFailures_toolchain`, `project_boundary_reported`, `checked_toolchainBase` | No failure exactly when there is no unresolved path and every boundary meets its mode's relation; the failure kind of every boundary and path for every claim. A toolchain-owned boundary never fails; every boundary without an admitted toolchain origin or checked evidence has its own failure record, in every root whose account contains it, under a checked claim; the audit's toolchain trusted base has each toolchain-owned boundary (constant and kind) of every labeled environment account in exactly one entry, which lists exactly the environments and roots that reach it. |
| Execution findings | `executionFindings_empty_iff`, `failure_reported`, `unresolved_reported`, `executionFindings_sound`, `rootFindings_ids`, `executionFindings_unresolved`, `ExecutionRoot.boundary_reported`, `ExecutionRoot.first_record`, `ExecutionRoot.folded_trusted`, `ExecutionRoot.carries_spec`, `ExecutionBoundary.restates_spec`, `boundaryFailures_restates`, `ExecutionInventory.reported_or_folded` | The findings the gate reports are the failure records with each folded boundary's record reported in the finding of the boundary it is reported with. A boundary is folded in two cases only. It repeats an earlier record: a boundary of the same root with a smaller occurrence number is trusted like it and has the same constant, kind, replacement and toolchain origin, so the two have the same failures for every claim. Or it is a trusted partial-computation boundary without a toolchain origin whose constant is the source of no helper edge, and a boundary of the same root that is trusted, not toolchain-owned and not itself foldable names its constant, by its `replacement` or, as a partial-computation boundary, by a helper edge. Every folded boundary is trusted, and every boundary of a root is, or restates, one that is reported on its own or is an implementation of one reported on its own. So the findings are empty exactly when `ExecutionOK` holds; every failure record is its boundary's own finding, is named in the finding of a boundary whose implementations include it, or is a later record of a boundary that is; every unresolved path is a finding unchanged; every finding has the kind, root and detail of a record, followed by its implementations; a root has one finding per failing boundary reported on its own; the unresolved findings are as many as the unresolved records; and every boundary of the account is counted by the coverage counts or folded. These are statements about the supplied account: that the collector records a `partial` definition and the constant compiled to it, and two candidates of one equality, in this form is its observation of the environment, not proved. |
| Correspondence | `DefeqComparison.classify_checked_iff`, `classify_trusted_iff`, `classify_unresolved_iff` | Checked exactly for a completed comparison with admitted evidence, trusted exactly for a completed one without, unresolved exactly for one that did not complete. |
| Expected diagnostics | `matchesPattern_iff`, `orderedLiterals_iff` | The restricted pattern's ordered leftmost-split match within one effective-error message. |

**Consumers** (paths from `lean/Regula/`):

| Operational caller | Proved pure function | Remaining boundary |
| --- | --- | --- |
| `Checker/Policy.admitScope`, with `Frontend.validateCoordinates` | `checked_scope` (first coordinate refusal in transcript order, then exactly `admitInventory` with `authorize`; success iff all coordinate checks and `InventoryValid` hold, retaining both input arrays); `checked_coordinates` (claimed `RegulaCore.Coordinates`: success iff `CoordinatesAgree`, refusal with the first unmet obligation in traversal order) | Lean's UTF-16 column function (`FileMap.leanPosToLspPos`) and `FileMap`; source and compiler observation acquisition. |
| `request`, `ruleFor`/`reasonFor`, `ruleForMember` (claimed `RegulaCore.Policy`) | `checked_request`, `checked_rule`, `checked_memberRule` over `policyFor`; `ruleForFailure_injective`, `reasonFor_eq_some_iff` | Registry descriptor text; adequacy of the mapped rule set. |
| `labelOf`, `labelOfMember`, `classify`, `classifyMember` | `foundationFor`; `checked_memberFoundation`, `labelOf_member`, `classifyMember_eq` | Transitive `Lean.collectAxioms` results and module ownership. |
| `executionFindings`, `executionFailures`, `executionSummary`, `toolchainBase` | `checked_executionFailures` (line `k` renders finding `k`, none added or dropped, so the lines are empty iff `ExecutionOK`), `executionRule_injective`, `checked_summary` (the boundary counts range over the boundaries reported on their own: a later record of one trusted boundary of a root, and a `partial` implementation reported with the boundary that runs it, are counted with that boundary, not again), `checked_toolchainBase` | Root and closure collection, retained compiler edges, correspondence admission, source history, module origins and the text and JSON rendering of the toolchain trusted base. |
| `Probe.replacementCorrespondence` | `DefeqComparison.classify` (a comparison that did not complete is unresolved, never trusted) | Mapping the kernel result to the outcome, the kernel decision itself and the incomplete theorem-candidate search. |
| `Checker/Common.admitIndexedWorkerResults`, `mapWorkQueue`, `Documentation.auditTasks` | `checked_indexedResults` over `ResultState.collect` | Child completion, strict packet decoding, task scheduling and exact request and source binding. |
| `Checker/Documentation.matchesPattern` | `matchesPattern` | Structural fence scanning, pattern diagnostic text and effective-error extraction. |
| `AxiomGate.auditSurfaceAt`, `FreshChecker`, the file gate | `checked_surfaceAssignments` (with `surfaceAssignments_covers`), `checked_conformingProfile`, `checked_histories`, `checked_environmentJob`, `checked_environmentEvidence` (claimed `RegulaCore.Assembly`) | Manifest parsing, Lake loading and producer history; the contracts concern the decoded records. |
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
| RG1006 | `authorizedUnsafeRecHelpers_iff`, `authorizedUnsafeRecHelpers_base`, `policyFor_conforming_iff`, `subject_contract`, `partialParent_rule` | Exact helper metadata, the regeneration observation and the base's axioms are checked, and a `partial def`'s helper always has a finding that names the `partial def` (its opaque declaration) when that declaration is in the inventory. The regeneration itself (Lean's recursion compiler rerun by `Collect`) and its erasure comparison, compiled-code correspondence and execution coverage are not proved. Admission does not establish that the helper terminates whenever the base does: Lean compiles the base from a body its `wf_preprocess` rules rewrote, which Lean documents can remove a subterm the compiled helper still evaluates or delay one under a binder, so the helper's termination trusts that preprocessing (standard §7.4). |
| RG1007 | `ContractOK` through `ruleFor` | Recorded contract failures are enforced; Probe's extraction of the proposition and root, proof admission and adequacy are not proved by this relation. |
| RG2004 | `policyFor_ordered` (membership first), `CensusOK`, `PlanOK` | Complete Lake and environment ownership acquisition. |
| RG3001, RG3002 | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff`, `boundaryFailures_toolchain`, `project_boundary_reported`, `executionFindings_empty_iff`, `failure_reported`, `executionFindings_sound`, `checked_toolchainBase` | The theorems cover the supplied unresolved paths and boundaries and their supplied origins, not complete root and closure discovery, the truth of the origin observation, the collector's record of which constant is compiled to which `partial` definition, or the correctness of the toolchain's or external runtime code. |
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
audit's total memory. Because the allowance is per process, a process that has inspected one
environment is not fresh for the next, whose checks may then exhaust at once; the audit and the
`qualify environments` census therefore acquire every claimed environment's report through the same
code, `Inspection.inspect`, each in its own report worker. Supplied and then discovered theorem
candidates are tried before the kernel-defeq check, to keep a kernel-exhausting unfolding within one
comparison from consuming the headroom a supplied proof needs, so a replacement with both reports
`proved:` evidence; kernel resource exhaustion is never conflated with rejection; a theorem
candidate whose admission exhausts the kernel supplies no evidence, like any candidate the
deliberately incomplete search cannot use.
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
  dependencies with the pinned `Kernel.Environment.replay`, checks every required entry is in the
  resulting kernel and returns a typed receipt. It returns
  `IO (Except ProducerReport.AdmissionFailure ProducerReport.AdmissionReceipt)`: a successful
  receipt's required keys are the safe, nonpartial constants of the replayed modules' own
  `.olean` data, one key per module and name, then those of each reused module among the
  environment's requested modules (**Admission reuse** below), and it records the admitted keys.
  Replay scope includes owned dependencies and the existing reporter closure where required; it
  may exceed the reported surface. Imported unowned modules remain trusted; the receipt records
  the completed operation and does not authenticate replay. Admission failures carry the
  `[INCOMPLETE[kernel-admission]]` tag (`Admission.failureTag`), since RG2005 reports them as
  incomplete.
- **Several copies of one name.** Lean realizes equation, unfolding and match-equation lemmas,
  functional induction and case principles, and congruence and injectivity lemmas in the module
  that first needs them, so two modules that do not import each other can each contain the same
  one. Lean's import keeps one copy: `Environment.find?` returns the last one loaded, whose
  statement and value reports read, while the name is attributed to the first module, and
  `collectAxioms` reports for it the axioms that module computed for its own copy when compiled,
  or walks the kept copy where that module did not export the name (observed on the pinned
  toolchain and read from `Lean.Util.CollectAxioms`).
  `Kernel.Environment.replay` skips, unchecked, a theorem whose name and statement it already
  holds. Admission therefore reads each replayed module's own constants (`Admission.Copy`). It
  replays, under each such name the replay base lacks, the constant `find?` returns
  (`Admission.replayMap`), so there the replayed kernel holds exactly the audited environment's
  constants, and replay itself rejects a kept copy whose proof uses its own name.
  `Admission.checkCopies` then checks every copy against the constant the replayed kernel holds
  under its name. An `unsafe` or `partial` copy, which `replay` does not check and the receipt does
  not require, only must not share its name. For every other copy: a copy of a name the base or
  another replayed module also declares must form, with the held constant, two theorems of the
  same name, type (`Expr.eqv`, in either direction), universe parameters and mutual block
  (`Admission.sameTheorem`). A copy `identical` to the held constant (same kind and fields, proof
  included) needs nothing more: it is that replayed constant or that trusted base constant. Any
  other copy must pass `Admission.checkProof` in the replayed kernel: the kernel accepts it under
  `Admission.proofCheckName`, and the names its proof reaches (`Admission.reachSet`, through the
  types and values of the constants used) exclude its own name and include exactly the axioms the
  held constant reaches. Equal axioms make the reported axioms right whichever copy a declaration
  or the attribution used. Where the audited environment keeps an owned copy over a different base
  constant, that kept copy must also pass `checkProof`, its reach computed in the audited
  environment. A copy the audited environment discards is checked in the replayed kernel, where
  the names its proof uses denote the replayed kernel's constants (the base's, where the base
  declares them). Modules containing any copy of such a shared name are listed in the receipt's
  `shared` and never offered for reuse, since their admission depends on which copy an environment
  keeps. **Proved** about the executed definitions: `Admission.sameTheorem_iff_subsumesInfo`
  (private in the `module` file `Regula.Checker.SharedName`, whose `import all Lean.Environment`
  reaches Lean's private `subsumesInfo`: on two theorems the condition equals `subsumesInfo` in
  either direction, which the pinned `Lean.finalizeImport` requires of a second constant of one
  name, as read from its source; every other pair it accepts involves an axiom, which admission
  refuses); `Admission.replayMap_sound` and `Admission.replayMap_complete` (the replayed constants
  are exactly the audited environment's constants of the copies' names the base lacks);
  `Admission.reachSet_some` (a completed search holds exactly the names reachable from the
  constants the start uses, along `Admission.successors`); `Admission.checkProof_ok`; and
  `Admission.checkCopies_sound` (a success gives every copy the `Admission.CopyAdmitted`
  conditions above, stated with the reachability relation `Admission.Reach`). **Argued, not
  machine-checked:** `validate` passes these checks the replayed module data, the base's and the
  audited environment's `find?` and the replayed kernel, and admits no key when one fails, all
  read from the code (`Admission.mem_offers` proves that no offered admission lists a `shared`
  module). Every cycle among the audited environment's non-inductive constants that involves an
  owned name passes through a name whose kept constant differs from the replayed one (or through
  the trusted base), because replay admits each declaration only after the constants its type and
  value use, and the replayed kernel agrees with the audited environment on the other owned names;
  the checks exclude a cycle through such a name, so the audited environment's constants form a
  well-founded development. Every copy in a replayed module reaches the same axioms in the
  replayed kernel as the constant held under its name, so, by induction over the modules, each
  replayed module's precomputed axioms for a declaration equal those of its replayed kernel
  development whichever copy of a shared name its own build used, given the trusted agreement
  below for unreplayed modules. **Trusted:** Lean's import and module data, including the axioms
  each module precomputed, and that an unreplayed module's precomputed axioms equal those of its
  constants in the replay base (two unreplayed copies of one name are not compared); the kernel,
  and `replay` adding each map entry unchanged while leaving the base as imported; that the
  kernel's theorem check consults the declaration's name only to require it undeclared, so a
  renamed check is a check of the copy; and, as in Lean's own duplicate-theorem design, that the
  value of a theorem does not change what typechecks where copies of one statement are exchanged.
  Report attribution is unchanged: `Probe.ownedConstants` attributes a shared name to the first
  module Lean's import loaded it from, so the name's claim is that module's.
- **Admission reuse.** One contract covers every environment of a project audit, a library's
  and an executable's alike. Each environment waits for the environments that replay the claimed
  library modules it loads. What a library's environment loads is read from the import headers
  of the bound sources, starting at its own modules and the force-imported probe; the
  environments are ordered so that a library comes after the libraries whose modules it loads
  (`Inspection.libraryNeeds`, `Inspection.startOrder`), and the first environment in that order
  to load a module is the one that replays it (`Inspection.replayers`): its own library's, unless
  claimed libraries import one another. An executable's environment waits for every library. No
  environments wait for one another (`Inspection.prerequisites`), and environments that wait for
  nothing, or for the same ones, run side by side, three at a time. A worker publishes its
  completed admission (`Admission.Completed`: the receipt and the module origins) as soon as
  kernel admission succeeds, so the environments waiting for it start while it builds its report.
  The coordinator offers a starting environment the admissions of the environments it waited for
  (`Admission.currentOffers`, `Admission.PriorAdmission`). That environment keeps an owned module
  in the replay base instead of replaying it (`Admission.reusedModules`; the receipt's `reused`)
  only when (1) an offered admission replayed it over the identical import closure
  (`Admission.importClosure`: the same modules, canonical `.olean` paths and import edges) and
  did not list it as `shared` (a module containing a copy of a name another module of that
  environment declares); (2) the module and every owned module of that closure is a claimed
  library module all of whose `.olean` parts (the `.olean` and, for a module-system file, the
  `.olean.server` and the `.olean.private` Lean takes its kernel constants from) the coordinator
  read before the first inspection, read again as this environment started with the frozen
  presence and bytes (`Inspection.readings`, `Admission.Unchanged`), and compares again after the
  last inspection (a change is RG2005, incomplete); (3) each declaration of each owned module of
  the closure refers only to constants of its own closure (`Admission.referencesWithin` over
  `ConstantInfo.getUsedConstantsAsSet`, the dependencies `Kernel.Environment.replay` replays
  first); (4) every constant of the module is attributed to it in this environment and is the
  copy this environment keeps (`Admission.uniquelyKept`), so no module here declares a different
  copy of its names; and (5) every owned module of the closure is reused too: a candidate
  (`Admission.candidates`, a module meeting (1) to (4)) whose closure contains an owned module
  that is not a candidate is removed, so a module that cannot be reused takes the modules above
  it out with it. One pass settles this: a member's closure lies within the closure
  (`Admission.importClosure_trans`), so every owned module of a kept candidate's closure is a
  candidate that is kept too. Every other owned module is
  replayed (`Admission.replaySet`). A module of the environment's own request is reused under the
  same conditions, which arises only when an earlier environment loaded it first (claimed
  libraries that import one another): the receipt then still requires the key of each of its
  safe, total constants, read from the module's own data, and those keys are admitted by the
  environment that replayed it. The coordinator accepts a report only when its offers justify
  every module it reused and every key it requires in a reused module (`Admission.reuseJustified`),
  its receipt lists every owned module its environment loaded as replayed or reused
  (`Admission.accountsFor`), no module as both (`ProducerReport.Environment.receiptOK`), and the
  admission its worker published is the one the report records (`Completed.ofReport`, compared by
  decidable equality); otherwise the environment is RG2005, incomplete. **Proved** about the
  executed definitions: `Admission.mem_reusedModules` (a reused module is owned and satisfies the
  offer of (1), (3), (4) and (5)); `Admission.importClosure_some` and
  `Admission.importClosure_trans` (over an index that holds every origin under its own name, as
  `Admission.originIndex_keyed` proves of the executed index: each origin of a closure is the one
  the index holds under its name, its name has every property of the module's name that passes
  from a name to the imports its origin records, so it is the module or one it transitively
  imports, and every import it records is the name of an origin of the closure; and the closure
  of a member's name lies within the closure, which is why one pass decides (5));
  `Admission.mem_replaySet` (every owned module that is not
  reused is in the set `Admission.validate` replays); `Admission.replayed_unless_offered` (a
  changed import forces a replay: an owned module is replayed unless an offer covers it over
  exactly the closure it has here); `Admission.unchanged?_eq_some`, `Admission.mem_unchangedOf`
  and `Admission.frozenIndex_unchanged` (an offer rests only on an artifact whose reading, the
  one the coordinator took, equals its frozen parts: `Admission.Unchanged` carries that equality,
  so an artifact that was not read again cannot be passed where an offer needs one);
  `Admission.replayed_of_changed` and `Admission.replayed_of_changed_import` (a changed `.olean`,
  `.olean.server` or `.olean.private` forces a replay: an owned module is replayed when every
  reading of its artifact, or of the artifact of an owned module of its closure in every completed
  admission, differs from the frozen parts or failed); `Admission.mem_offers` and
  `Admission.frozenClosure_sound` (an offered module is one a completed admission replayed,
  outside its `shared` and `reused` modules, loaded with every owned module of its closure from
  the canonical path of such an artifact, and an offered key is one that admission admitted);
  `Admission.reuseJustified_sound` and `Admission.reuseJustified_frozen` (an accepted report
  reused only modules that a completed admission replayed, outside its `shared` modules, over
  the report's own closure, whose owned modules and the module itself have artifacts read with
  their frozen parts); `Admission.reuseJustified_admitted` (every key an accepted report requires
  in a module it reused was admitted by a completed admission that replayed that module);
  `Admission.replayed_of_loaded` (every owned module an accepted report's environment loaded is
  in that environment's own replay set, or in the replay set, and not among the reused modules,
  of a completed admission whose environment loaded it, so no accepted report rests on a module
  no environment replayed; a receipt's `modules` alone does not show a replay, since it lists
  every owned module the environment did not reuse, loaded or not);
  `ProducerReport.validate_sound`
  (an admitted report's receipt requires the key of every safe, total declaration it reports, in
  a module it lists as replayed or reused, never both); and `Inspection.prerequisites_earlier`
  (every environment waits only for environments strictly before it in the start order, so the
  waits have no cycle). **Checked at run time, not proved:** the equality of the published and
  reported admission, and that no base module imports a replayed one (`Admission.validate` reads
  this from each module's own data: a closure contains every import its origins record,
  `Admission.importClosure_some`, but that an origin records its loaded module's imports is not
  proved).
  **Observed,
  an external boundary:** reading the `.olean` parts (`Inspection.readings`; the `checkerSelftest`
  structural partition observes, through `Admission.currentOffers`, that a changed, removed or
  added `.olean`, `.olean.server` or `.olean.private` withdraws the offer and a restored part
  returns it), and the reuse of a requested module through the report workers and the kernel (the
  same partition audits two claimed libraries that import one another). **Argued, not
  machine-checked:** `Inspection.inspect` passes these definitions the admissions published by
  the environments it waited for and the readings it took as the environment started, and
  `Admission.validate` replays the modules of `Admission.replaySet` that its environment loaded,
  and no other, and takes the keys of a reused requested module from that module's data, all
  read from the code; the workers finish because
  the first environment not yet started in the start order waits only for started ones
  (`prerequisites_earlier`) and a started environment always publishes its admission or ends.
  **Derived, not machine-checked:** the kernel's check of a declaration depends only on the
  declaration and the constants it consults, which its references and their values reach. By
  (3), (5) and the imported base's own references, a reused module's declarations consult only
  its closure; by (4) for each owned module of the closure (all reused by (5)), no module here
  declares a different copy of their names, and another copy here of a base module's name is
  checked by this environment when a replayed module holds it (`Admission.checkCopies`) and
  trusted when another unreplayed module does; by (1) and (2) that closure is the same bytes in
  both environments, and by (1) none of its names had a second copy in the earlier environment,
  so the earlier environment's successful replay is the one this environment would repeat. This
  rests on the stated trusted boundary: authentic imported artifacts unchanged during the audit
  (as the history memo already assumes), filesystem reads, and no change restored between two
  byte observations. No theorem models the kernel. Where the conditions fail, a module is
  replayed more than once: a `shared` module and the modules that import it, in every environment
  that loads them (so a claimed module that realizes its own copy of a toolchain lemma, as
  `simp only [Except.mapError]` does for `Except.mapError.eq_1`, is replayed wherever it is
  loaded); an owned module outside every claimed library (one of an excluded library that the
  probe loads, such as `Regula.StructuralName` in this repository), whose `.olean` is not frozen,
  with the reporter modules that import it; and a claimed library that an environment reaches
  only through a module without a bound source, which the import headers do not show.
- **Documentation.** `Environment.loadReportCoreAtSearchPath` freezes the `@[regula_material]`
  selector from the completed owned environment and reads module docs (Markdown and Verso) and
  docstrings with `Lean.findDocString?`, the same lookup as native feedback, so the project gate's
  RG5001–RG5003 findings do not depend on whether native feedback was imported. Observed RG5003
  evidence is the fresh-project corpus pair and the native `MissingIntent` control; no incremental
  or build-lint RG5003 run is claimed.
- **Transport.** `Report.Collected` adds extraction keys to the pure policy report;
  `Checker.ProducerReport.Environment` adds the operational receipts and owns their JSON decoder:
  `census` (requested modules, declaration keys, optional execution root keys and root/module
  history requests), `admission` (replay modules, required keys, observed admitted keys, reused
  modules and `shared` modules),
  `documentation` (every module's presence, including declaration-free modules, frozen material
  keys and exact optional docstrings), `histories` (one completed source receipt or explicit
  unavailable outcome for every requested module) and `sourceBindings` (exact loaded-owned
  module/path/text snapshots). Use `--json-out` to consume producer evidence. **Proved:**
  `ProducerReport.validate_sound` shows every report `Environment.validate` admits is
  `Environment.Admissible`, restating every executed guard (a nonempty, unique, loaded module
  census; a declaration census equal to the reported keys in order and duplicate-free; execution
  results exactly for the requested roots; `ExecutionValid` closures; unique located source
  bindings covering every claimed module and range; each declaration's recorded full range and
  recorded selection range valid in its module's source; a replay receipt admitting exactly its
  unique requirements and requiring every safe, total declaration; documentation observations for
  exactly the claimed modules and unique material selection; unique history requests with exactly
  one history per requested module; completed histories located, source-stable, bound to the
  owned snapshot when the module has one and free of anonymous edge endpoints; unavailable
  histories leaving every requested root unresolved; requested runtime replacements the toolchain
  does not own whose resolved edges appear in completed histories; root/boundary module
  attribution with exact replacement-edge channels; and, for every current replacement reference
  the toolchain does not own, a reached, attributed, requested and recorded module history, with
  the root's historical edges the canonical form of exactly those completed-history edges);
  `validate_eq_ok` decomposes the guard sequence, `validate_nonvacuous` exhibits an admitted
  report and `fromJson_admissible` extends soundness to the decoder. Producers, documentation
  groups and acceptance call `checked_validate.run`; the project report worker skips its own call:
  the coordinator's decoder runs the same check once and keeps its success as a
  `ProducerReport.Admitted` proof (`fromJson_admitted` shows it accepts and refuses exactly as the
  plain decoder), and `Acceptance.freezeEnvironment` requires that proof instead of re-running the
  check and takes the execution inventory from it (`Admitted.admitExecution_eq`). These do not
  authenticate the observations; a direct interactive dump has no loader receipt and cannot pass
  the decoder.
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
  runtime-replacement boundary the toolchain does not own (`ExecutionBoundary.needsHistory`) must
  have a registered request, and completed execution requires its replacement edge in a completed
  history. A toolchain replacement, whose module has an admitted toolchain origin, requests no
  history: the walk follows its current target, and `historyReplacementEdges` leaves its edge out
  of the history account. Logical-only inspection has no execution roots, requests or history
  receipts.
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
helper's group (structural recursion with Lean's automatic choice, then on the argument position
Lean recorded for each base, which admits a definition recursing on an argument
`termination_by structural` selects, then well-founded recursion with the relation the base's
fixpoint applies and every decreasing proof elided; where none of these reproduces the base, the
same attempts once more with no definition irreducible, below), with only the toolchain's own
`wf_preprocess` rules and the checker's built-in macros, tactic and term elaborators, generating
no code for the fresh definitions, and compares each regenerated definition with the observed one
up to compilation erasure: proofs and types, each classified in its own side's context, are erased,
a well-founded fixpoint is compared without its relation or measure, and a `match` that passes a
variable through is taken as the direct one where the kernel checks the two equal, below
(`Declaration.unsafeRecRegenerated`). Each theorem the regeneration abstracted from a nested proof
is first put back as its value, so the comparison uses no such theorem's name:
Lean names it from a counter and from the propositions it already abstracted in the same process,
and privately where a `module` file does not export the body, so the observed module need not hold
a theorem of that name. `unfoldTheorems_free` proves that the value so unfolded mentions none of
those theorems; it proves nothing about `Expr.replace`, the renaming of the regenerated definitions
that follows, or the comparison. The invariant is that a helper of a definition the checker admits
is admitted exactly when it adds no trust beyond that definition. Its machine-checked part is over
the recorded observations only: `policyFor_none_iff`, `authorizedUnsafeRecHelpers_iff` and
`authorizedUnsafeRecHelpers_base` (the Roles and Declaration policy rows above). That the comparison
does not depend on the names of those theorems is observed, not proved: `checkerSelftest fixtures`
admits every helper of `Fixtures.Positive.SharedProofRecursion` (the shapes of issue #162) and of
`Fixtures.Positive.ModulePublicRecursion` (`public` definitions of a `module` file, exposed or not),
and in `Fixtures.Mutations.SharedProofUnsafeRecForge` admits a faithful copy of a helper and rejects
one that computes with another function. That the regeneration reproduces a base whose compiled
value depends on its termination argument is observed too: the same command admits every helper of
`Fixtures.Positive.MeasuredRecursion` (the shapes of issue #183: a `match` on the measured argument
after an argument that also changes, lexicographic and computed measures, a `mutual` block, a
measure under a `WellFoundedRelation` instance local to its section, structural recursion on a
later argument, and structural recursion Lean's automatic choice compiles through another
argument's nested type former), and in `Fixtures.Mutations.MeasuredMatchUnsafeRecForge` admits a
faithful copy of such a helper and rejects one that computes with another function. For
well-founded recursion `Collect.wfRegeneration` runs the steps of Lean's `wfRecursion` in its order
up to the definitions it adds, with the base's own relation in place of one elaborated from
termination measures; that it follows Lean's compiler is read from Lean 4.34.0's source, not
checked. The termination argument read only selects which regeneration runs
(`Collect.unsafeRecRegeneration` returns an origin only when the definitions that regeneration
added match the observed ones), so what is read cannot admit a helper the comparison rejects; this
is read from the code, with no theorem.
That admission does not depend on which definitions were irreducible where a definition was
elaborated is observed as well, for the shapes of issue #188: the same command admits every helper
of `Fixtures.Positive.ReducibilityChange` (a measure through a function that is irreducible only in
the definition's section, only after the definition, or everywhere except at the definition,
structural recursion on an argument whose type is a definition made irreducible afterwards, also
where the definition's own type is one, a `match` applied to a recursive call, and the first shape
over a `casesOn`, overlapping alternatives, a named equation and numeric literals), and in
`Fixtures.Mutations.ReducibilityChangeUnsafeRecForge` admits a faithful copy of such a helper and
rejects one that computes with another function, on each of the two paths. Lean records no
reducibility with a definition, so nothing is restored. The first path is the comparison:
`Collect.equalErased` takes a `match` that passes a variable through (`Collect.threadedMatch?`: the
same constant, applied to the variable as one more argument, every alternative binding it once
more) as the `match` that uses the variable directly, comparing each alternative's body with the
bound variable standing for the one passed. Lean's compilers choose between these two forms by
`isDefEq` on the type of the recursive-call function (`MatcherApp.addArg`), so the choice depends
on what unfolds. The comparison takes that step only after `Collect.threadingLawChecked`: for the
constant `M`, parameters and motive `fun ds => A ds → R ds` at hand, it states

`∀ ds alts (w : A ds), M ps (fun ds => A ds → R ds) ds alts w = M ps R ds (fun xs => altsᵢ xs w)`

over the variables in scope, finds a proof (`Split.splitMatch`, or `cases` on the major premise,
then `rfl`), and has Lean's kernel check it (`Environment.addDeclCore`) with no axiom outside
Standard-Logical; the theorem and every constant the search realizes are then discarded. What Lean
records about `M` (that it is a matcher or a `casesOn`, how many pattern variables an alternative
binds) is metadata the audited module can write, and decides nothing: it says where to look and how
to search, and the kernel decides. `Fixtures.Mutations.FakeMatcherUnsafeRecForge` registers two
functions that return their last argument as matchers; under that description two leaves that
compute different values are the two forms of one `match`, and a helper forged with the other leaf
is rejected, where the law cannot be stated for the constant and where it can and is false
(without the kernel check both forged helpers are admitted; observed). The second path is the
regeneration: where nothing it generates in the inspected environment matches,
`Collect.unsafeRecRegeneration` runs it once more with no definition irreducible, each irreducible
definition given the status its declaration shows (`Collect.withoutIrreducible`: `reducible` for an
`abbrev`, by the kernel's reducibility hint, and semireducible otherwise), reading the recorded
structural argument against the
parameters the helper's value binds, since the observed type need not show them. What is
machine-checked: at each use of the first path, the kernel's check of the threading law, relative
to the inspected environment, whose owned declarations the gate replays (standard §7.3); and
`mem_standingFor_left` and `mem_standingFor_right`, by which the pairs under which the bound
variable stands for the passed one relate the bound variable alone, and to exactly the variables
the passed one was paired with. Neither states anything about the comparison as a whole. The rest
is argued, with no theorem: that comparing an alternative's body with the bound variable standing
for the passed one is the comparison, up to erasure, of the law's right-hand side with the other
side; that ignoring the motive's universe level of the matcher loses nothing, universe levels
being erased; and that the second environment, like the termination argument, only selects which
regeneration runs. That the two paths admit every definition for which the only difference is
that ordinary (semireducible) definitions are irreducible at one of the two points, or that an
`abbrev` is irreducible at the end of the audit, is argued from Lean 4.34.0's source (with those
given back their declared status Lean unfolds at least what it unfolded where the definition was
elaborated), not checked; the `abbrev` made irreducible afterwards was found in review as a
rejection and is a control (`fixtures_abbrev_irreducible`). A matcher for
which the search finds no proof is compared strictly, which rejects and never admits; a resource
limit of the kernel reached while it checks the law (its deterministic timeout, deep recursion or
excessive memory) is rethrown as the checker's limit, so the helper is then undecided, not
rejected.
That admission does not depend on a global reducibility attribute given after a definition is
observed for the shapes of issue #196: the same command admits every helper of
`Fixtures.Positive.ReducibleAfter` (a parameter passed through a function made `reducible`
afterwards, under well-founded and under structural recursion; a `List.map` behind such a function,
which the toolchain's `wf_preprocess` rule then sees through; a second parameter passed through a
function that is `@[reducible]` from its declaration; a `@[reducible]` function made irreducible
afterwards, under `allowUnsafeReducibility`; a function an instance-implicit argument goes through,
made `instance_reducible` or `implicit_reducible` afterwards, or `instance_reducible` first and
irreducible afterwards; an `abbrev` that is irreducible at both points, beside a type made
irreducible afterwards; and a definition whose six candidates allow exactly the 63 assignments the
search tries, of which one that changes two of them reproduces the base). The parameter under well-founded and under structural recursion, the
`List.map` form and the `@[reducible]` function made irreducible afterwards were observed
rejections before the search below, pinned as such by the fixture this one replaces. For the forms
with an instance-implicit argument, that Lean finds the parameter fixed at only one of the two
points was observed on Lean 4.34.0 from the fixed parameters it records; their rejection, and that
of the form with a second parameter and of the `abbrev` form, without the search was not run.
Lean's fixed-parameter analysis (`getFixedParamPerms`) compares each argument of a recursive call
with the parameter by `withReducible <| isDefEq`, which checks an instance-implicit argument at
implicit transparency, and the preprocessing `simp` matches through reducible definitions, so both
depend on which definitions are `reducible`, `instance_reducible` or `implicit_reducible`. Lean
keeps no history of a status (`reducibilityCoreExt` holds the last one), and the kernel's
reducibility hint tells only an `abbrev` apart.

Where neither environment reproduces the base, `Collect.unsafeRecRegeneration` therefore searches.
`Collect.earlierStatusOptions` collects the definitions of the helper's module that the values of
the helper's group reach through that module's constants, and pairs each that is not an `abbrev`
with the statuses `Collect.earlierStatuses` gives for its status at the end of the audit:
semireducible for `reducible` and for `instance_reducible`, semireducible or `instance_reducible`
for `implicit_reducible`, and `reducible`, `instance_reducible` or `implicit_reducible` for
irreducible. Those are the statuses from which `ReducibilityAttrs.validate` of Lean 4.34.0 admits a
global attribute that gives the final one, and `reducible` before irreducible is the one change
taken from `allowUnsafeReducibility`, under which it checks nothing. An `abbrev` that is
irreducible at the end is paired with irreducible, so that an assignment can keep it so in the
environment with no definition irreducible. `Collect.candidates` then enumerates the assignments:
every way to give one or more of those definitions one of its statuses, when there are at most
`Collect.candidateLimit` (63), and otherwise the first 63 single changes. Each assignment is
installed (`Collect.withStatuses`) over the inspected environment and over the one with no
definition irreducible, and all attempts run under it, each regeneration with the heartbeat budget
of one declaration (`withCurrHeartbeats`): at most 2 + 2 × 63 = 128 regenerations for one helper,
of at most three compiler runs each.

What is machine-checked is the enumeration: `Collect.mem_candidates` (where `candidates` reports
that it is exhaustive, it holds every nonempty list that takes one status each from some of the
definitions, the relation `Collect.Picks`) and `Collect.candidates_length_le` (it never holds more
than the limit). Neither states anything about what a regeneration does with an assignment, or
that the definitions and statuses collected are the ones Lean consulted. The rest is argued, with
no theorem:

- Soundness. An assignment only selects which regeneration runs.
  `Collect.unsafeRecRegeneration` returns an origin only when `Collect.regenerationMatches` accepts
  the definitions a regeneration added, and that comparison takes those definitions alone as its
  argument and runs after the saved state, environment included, is restored and Lean's caches are
  emptied, so it reads the observed definitions in the inspected environment whatever assignment
  the regeneration ran under. The comparison does consult state the audited module can write (the
  inspected environment's own statuses, where it decides what is a proof or a type, and matcher
  metadata), as it did before the search; an assignment adds nothing to that. That a regeneration
  under any assignment is Lean's compilation of the helper's recursion is the same trust as for the
  environment with no definition irreducible: the fixed-parameter analysis keeps a parameter
  outside the fixpoint only where `isDefEq` accepts that every recursive call passes it unchanged,
  `isDefEq` proceeds by unfolding definitions to their values, and a status decides only whether a
  definition is unfolded; the preprocessing rewrites by the toolchain's proved equations.
  `Fixtures.Mutations.ReducibleAfterUnsafeRecForge` is the control: with a candidate assignment
  available in each direction, a faithful copy of the helper is admitted and one that calls another
  function at its non-recursive leaf is rejected.
- Completeness, for a definition of the helper's module, other than an `abbrev`, whose status a
  global attribute changed after the helper's definition in a way `validate` admits, or from
  `reducible` to irreducible. By `validate`, a global `reducible` or `instance_reducible` is
  admitted only on a semireducible definition of the same file, `implicit_reducible` only on a
  semireducible or `instance_reducible` one, `irreducible` on any of those three, and no global
  attribute on a `reducible` or an irreducible one; so the status a definition had where the helper's
  definition was compiled is its final status or one of `earlierStatuses` (or semireducible, for an
  irreducible one, which the environment with no definition irreducible gives). A definition of
  another module had its final status already, since its module was compiled first. And a constant
  of the helper's module whose status the compilers consult is among those the helper's values
  reach: the compilers work on those values, on the types of the constants they mention and on what
  unfolding them introduces, which is the closure `earlierStatusOptions` computes; a constant of an
  imported module mentions none of the helper's module. An instance of the helper's module that
  Lean's instance resolution selects without the values mentioning it is outside that argument.
- Termination and cost. `earlierStatusOptions` visits each constant of the module at most once, in
  at most as many steps as the environment has constants, and reports it if it stops before the
  reached constants are exhausted, which that bound does not allow. `assignments?` stops as soon as
  more than 64 assignments exist, deciding list by list, so it never builds more than 64 times one
  definition's statuses plus one.

What the search does not try, it does not admit (standard §7.4), and
`Fixtures.Mutations.KnownLimitReducibleWhereCompiled` pins those forms as observed rejections on
Lean 4.34.0, each a false rejection of a helper Lean generated, for the fixed parameters under
well-founded recursion: a function that is `reducible` only for the definition
(`attribute [local reducible]`) or `@[reducible]` and made semireducible afterwards, both of which
leave it semireducible at the end, a status no global attribute gives; an `abbrev` that is
irreducible only for the definition; a function that is `instance_reducible` only for the
definition (`attribute [local instance_reducible]`, which Lean allows without
`allowUnsafeReducibility`, as it does `attribute [local implicit_reducible]`, not run); a
function of an imported module made `reducible` after the definition; and an `instance_reducible`
function made `reducible` after the definition, a change `validate` does not admit, so that
semireducible, the one earlier status tried for a `reducible` definition, is not the status it
had (found in review). All but the fourth need `set_option allowUnsafeReducibility true`. Each has the same remedy: give the function its
reducibility where it is declared. Covering them would need every definition a helper reaches, of
any module, as a candidate for every status, which no bound on the search allows.
`Fixtures.Mutations.KnownLimitReducibilitySearchBound` pins the bound: a helper whose seven
candidates allow 127 assignments, and whose base only a change of two of them reproduces, is
neither admitted nor rejected. `unsafeRecRegeneration` throws, naming the helper as undecided, and
the audit fails as incomplete, with no violation reported for the helper, as it does at a resource
limit of the checker (observed: `axiomGate --file` reports one incomplete finding whose detail is
that error, exit class 3, and `checkerSelftest fixtures` requires that outcome with no violation
before it matches the text).

Every observation the checker takes from Lean's reduction runs with smart unfolding off
(`Collect.withoutSmartUnfolding`, applied by `Collect.declaration` and by `Probe`'s observations).
With `smartUnfolding` on, `Meta.unfoldDefinition?` of Lean 4.34.0 unfolds an application of `g`
through the declaration named `g._sunfold`, looked up by that name, without comparing its type
or body with `g`'s. Lean generates that declaration for a structurally recursive definition; an
audited module can write one for any function. `Fixtures.Mutations.AuthoredSmartUnfoldingUnsafeRecForge`
holds the two forgeries found in review ([#209](https://github.com/rbeauchamp/regula/issues/209)),
both admitted before this change, on Regula v0.4.2 too (observed): an authored identity `_sunfold` for a `reducible` successor function, under which the
fixed-parameter analysis takes `next a` for `a`, drops the argument and reproduces a base that
returns `a` from a helper that returns `a + n`; and an authored `_sunfold` of value `Type` for a
type-valued function, under which `Meta.isType` takes a value of that type for a type and the
comparison erases a leaf that differs. With the option off both are rejected and the honest
helpers are admitted (observed). That Lean reads no `_sunfold` declaration with the option off is
read from its source (the name is used behind the option in `Meta.unfoldDefinition?`, and
otherwise only where `simp` unfolds declarations it is told to unfold, which the regeneration's
`simp` is not), not proved. The `_sunfold`
definition the structural compiler adds for a regenerated base is still compared with the observed
one, like every definition a regeneration adds.

What the admission of a helper reads by a derived name or from metadata the audited module can
write, and what authenticates each:

| Name or record | Read by | Authenticated by |
| --- | --- | --- |
| `f._unsafe_rec` → `f` | `Compiler.isUnsafeRecName?` | Selection only: the helper is admitted only where the regeneration from its value reproduces `f` and every auxiliary definition. |
| `f._unary`, `f._mutual`, and `f._f` and `f._sunfold` of the helper's base | Added by the regeneration under its root; `Collect.wfRegeneration` reads the observed unary definition's relation | Each regenerated definition must equal the observed one of its name. The relation only selects: the comparison drops it, and the well-foundedness proof is the observed kernel-checked one. |
| `g._sunfold` of any other constant | Lean's smart unfolding | Not read: every observation runs with smart unfolding off. |
| Matcher and `casesOn` metadata, in the comparison | `Collect.threadedMatch?` | The kernel-checked threading law of each application (`Collect.threadingLawChecked`). |
| Matcher metadata, in reduction | `Meta.whnfMatcher`, `Meta.reduceMatcher` | The constant's own value is unfolded. |
| A matcher's equations and splitter | The proof search of `threadingLawChecked` | Guidance only: the kernel checks the theorem found. |
| Projection metadata | The `paramProj` preprocessing step; unfolding a projection function | `paramProj` moves only `wfParam`, the identity; the function's own value is unfolded. |
| `Structural.eqnInfoExt`, `WF.eqnInfoExt`, reducibility statuses | The regeneration | Selection only, never an argument of the comparison. |
| `T.rec` | The structural compiler | A recursor is created by the kernel with its inductive type. |
| Matcher and `casesOn` metadata, in Lean's compilers during the regeneration | `MatcherApp.addArg`, which passes the function standing for the recursive calls through a `match` | Open ([#210](https://github.com/rbeauchamp/regula/issues/210)): only the kernel's type check of the regenerated definition. That the passing is right rests on the threading law, which is not checked for these applications. No exploit is reproduced. |
| `T.below`, `T.brecOn` of an inductive type of the audited module | The structural compiler, by name | Open ([#210](https://github.com/rbeauchamp/regula/issues/210)): only the kernel's type check. Lean generates them with an `inductive`; a module that adds an inductive type by metaprogram can declare others. No exploit is reproduced. |
No theorem covers the regeneration itself, which runs in Lean's elaborator. The comparison
never uses `Meta.isDefEq`: where two values differ under a recursive call, its lazy unfolding of
the self-referential helper does not terminate. The regeneration runs Lean's elaborator in the
report worker and is undone before the comparison, which reads the observed definitions and decides
erasure in the inspected environment; a comparison that throws counts as no regeneration. The
report's other elaborator observations (`Meta.isProp`, the pretty-printed type, and `Probe`'s
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
`rule_roundtrip`, `nameParts_roundtrip` and `name_roundtrip`; `printedNameJson_roundtrip`: every
name survives the one form a result document and a producer report write it in, the text Lean's
`Name.toString` prints where Lean's `String.toName` reads that text back as the name and its
structural components otherwise (`printsExactly_iff`, `printedNameJson_eq_str_iff`), and the reader
admits a string only as the printed text of the name it reads (`parsePrintedNameJson_str`). Which
names Lean's printer and parser agree on is decided per name by executing them, not proved.
`RegulaCore.Feedback`:
`render` prints every entry exactly once (`sortEntries_perm`, `render_length`) in run order
(`sortEntries_sorted`, `sortEntries_eq_of_perm`), and the entries it or the streaming emitter,
which executes `Feedback.step` (`renderFrom_cons`), prints carry their rule's guidance exactly
when no earlier entry has that rule (`tag_of_prefix`, `mem_firsts`, `firsts_nodup`,
`firsts_length_le`). The emitter prints one entry per group of findings, in the order of
`sortFindings` (`sortFindings_entries`), and grouping loses no finding: flattened, the groups are
exactly the findings in that order (`flatten_runs`, `groupFindings_flatten`,
`groupFindings_perm`), the order the JSON lists them in. No theorem relates a group's printed
entry to `render`. A finding alone in its group that is not attributed to another
declaration prints exactly its own entry (`groupEntry_alone`); that a group's text lists every
member's subject and detail holds by construction and is inspected, not proved. The declaration
a finding is attributed to (`Findings.sourceName?`) is exactly the name the generation relation the
audited declarations record (`Declaration.generatedFrom`, or for an admitted recursion helper its
base: `stepOf`, `stepOf_eq_some_iff`) leads to from it and relates to nothing further
(`sourceName?_eq_some_iff`, over `chainEnd_eq_some_iff`: the executed walk is bounded by the number
of declarations, which the proof shows no such chain exceeds), so the declaration it names
is not itself attributed to another (`sourceName?_source`); the executed index equals the
inventory search it replaces (`declarationIndex_get`), and an RG1005 finding built with that
attribution groups under it (`declarationFinding_groupUnder?`). Which declaration Lean generated a
declaration from is read from the environment by `Collect.generatedFrom?`, one clause per family
of `GeneratedFamily`: from the marks Lean's generators leave, from a recursive definition's
equation information, from the uses in a declaration's type or value, in the types, constructor
types or field defaults of an inductive type's mutual block, in the statement of a definition's
`eq_def`, in a helper named under the declaration or in an auxiliary declaration that is itself
related, from Lean's own field-default lookup, and, for constructor lemmas and type constructions,
from their generator's precondition or a sibling's mark, checked under Lean's default options. No
clause rests on a name alone, and a clause that reads the relation from the declaration's name
applies only to a declaration with no recorded declaration range (`findDeclarationRangesCore?`):
Lean records one for every declaration an author writes and none for those generated ones, so a
theorem an author names like a generated declaration, such as `f._proof_8` or `f.eq_7`, keeps its
own location. A missed relation only leaves a finding at its own location; a wrong one would
report what the author wrote as generated, so these clauses are narrowed, not widened. A compiled
recursion helper `f._unsafe_rec`, which the environment ties to `f` only by its name, is related
to `f` only when the admitted scope authorizes it
(`authorizedUnsafeRecHelpers`), and `helperStep_base` proves `f` is then an audited definition of
the helper's module and type, and that Lean's recursion compiler was observed to regenerate the
helper; the observation itself is the boundary module 7 states, not proved.
`GeneratedFamily.mem_all` proves the list the checker tries and the RG1005 guidance names holds
every family, `generatedBy?` matches every family by construction (Lean's exhaustiveness check),
and `RegistryChecks` requires the adoption guide to quote the guidance verbatim. That the clauses
match Lean's generators is read from Lean's source and observed, not proved: the `cli` self-test's
source-attribution controls attribute a declaration of every family and keep a metaprogram
theorem, a user-written `ofNat`, an elaborator named `«_aux_…»` in a structure's namespace and
user-written theorems named like auxiliary proofs or an equation lemma on their own:
`middle._proof_8`, which `middle._proof_9` and the sibling `middle.spec` use, `middle._proof_9`,
`Util._proof_8`, which `Util.spec` uses, and `later._proof_8` and `later.eq_7`, declared before
`later`, which uses the first. They do not exercise every member of every family: for example,
not `f._mutual`,
`S.x._inherited_default`, `t.ctorElimType` or a matcher's splitter; the
[enumeration](#generated-declaration-families) marks the members they observe. Derived instances,
whose relation Lean does not record, are not related.
`RegulaCore.Guidance`: the briefing lists every rule once (`writingSections_perm`), the link it
gives for citing a rule is the installed build's `helpUrl` (`citation_installed`), an unreleased
build's skill is the development edition's, which the committed skill is compared with
(`skill_unreleased`), and the `regula`
parser admits exactly its documented commands (`parseCommand_arguments`, `parseCommand_sound`,
`parseInvocation_arguments`, `parseInvocation_sound`). Result stages: `stagesOf_required`,
`stagesOf_ordered`, `withDocs_ordered`, `notRun_completedStages_eq_nil_iff`,
`completedStages_idem`, `guidanceFields_recorded`, `parseStage_stageName`. Snapshot size:
`snapshotJson_configuration_independent`, `environmentJson_imports_independent` and
`Environment.resultJson_imports_independent` (`rfl`) show the rendering does not depend on
dependency text or import lists; the resulting size bound is an argument from construction, not a
theorem about byte counts. Source texts: `SourceTexts.expand_intern` (the reader's `expand` of what
`intern` wrote is the document it was given), `intern_table` (the written `sourceTexts` has no
text twice and exactly the texts of the document's `sourceText` members, and each such member of
the written document is an index into it), `intern_isOk_iff` (`intern` writes exactly the
documents with one `null` `sourceTexts` member and string `sourceText` members) and
`expand_texts` (every `sourceText` member of a document `expand` admits is a string), for every
`Json` value, without assuming its object trees well formed, and
`ResultProtocol.resultJson_slots` (every document `resultJson` builds has that one `null`
member); they depend on `propext`, `Classical.choice` and `Quot.sound`, and `RegistryChecks`
bounds them to Standard-Logical. They do not cover JSON text, the file, a member added to the
document after `resultJson` built it, or that a writer marks every source text as a `sourceText`
member: the members that do are listed in the
[architecture guide](architecture.md#output-schemas), and `RegistryChecks` and the rule-example
and producer campaigns observe written documents. Execution accounts:
`SharedExecution.restore?_internValue` (the reader's `restore?` of the written form of an
`execution` value is that value), `expand_intern` (`expand` of what `intern` wrote is the
document it was given), `read_write` (the same through `SourceTexts.intern` and `expand`, which
is what a result file's writer and readers run), `same_eq` (the comparison the writer decides
with answers `true` only for equal values) and `slots_intern` (writing the accounts keeps the
`null` `sourceTexts` member), for every `Json` value and every list of writer proposals, bounded
to Standard-Logical by `RegistryChecks`. The equality is of `Json` values, object trees
included, and `read_write` is about the value the writer wrote: any function of `read` of that
value is that function of the document the writer was given. It is not about the value a reader
parses from the file. The JSON implementation is trusted, as for every earlier schema, to parse
the file's text to a value with the members of the written one, but in general not with its
object trees: the printer lists an object's members in key order and the parser inserts them in
that order, while `Json.mkObj` inserts them as listed. So the `history` oracle's theorems
(`History.validate_importedRootExecuted`, `validate_unsupported_unresolved`) are about the
document `readResult` returns, and that this document has the members of the document the writer
was given, with the account the collector produced, is a further correspondence the laws do not
give. It is not proved and does not reduce to a JSON round trip; it is observed, by
`RegistryChecks` on one account (`expand` of a parsed shared form is the built account) and by
the `history` qualification, which reads the collector's real output through `readResult` and
validates the document it gets, without the writer's to compare it with. The laws do not prove
either that the written form is smaller than the logical one. That holds when the writer's
proposal is kept, which is checked at each write and observed on the collector's real output by
the `history` qualification (`derivedOnly`) and on built and parsed accounts by
`RegistryChecks`, not proved. In the excluded library, `RegistryCodec.mode_roundtrip`,
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

## Generated declaration families

Every family of declarations Lean v4.34.0 adds to the environment on its own, read from its source
(`src/lean` of the toolchain; paths below are relative to it), with the `GeneratedFamily` that
relates it to the declaration it was generated from and the environment fact that clause reads
(`Collect.generatedBy?`), or why it is reported at its own location. `Std/`, `Init/` and `lake/`
add no generator of their own: no `addDecl`, `mkAuxName`, `mkAuxDeclName` or `mkAuxLemma` call.
"Control" marks the members the `cli` self-test's source-attribution controls observe. A
clause that reads the relation from the declaration's name (every row below related by
`equationLemma`, `reservedName`, `structural`, `constructorLemma`, `typeConstruction` or
`fieldDefault`, a matcher's equation or splitter, a `brecOn`'s `go` or `eq`, and the `kind_N` rows
of `auxiliaryLemma`) relates only a declaration with no recorded declaration range: Lean records
none for these generated declarations and one for each declaration an author writes. A
declaration related to one that is itself related (such as `T.c.injEq` to `T.c`, or
`f._unary.eq_def` to `f._unary`) follows the chain to its end (`sourceName?`).

| Declarations | Generator | Related by | Control |
| --- | --- | --- | --- |
| constructor `T.c`, structure `S.mk` | kernel `inductDecl`, `Lean/Elab/MutualInductive.lean:1429` | `constructor`: `ConstructorVal.induct` | `Channel.mk` |
| `T.rec`, nested `T.rec_N` | kernel; `Lean/Elab/MutualInductive.lean:1241-1252` | `recursor`: `isRecCore` | `Channel.rec` |
| `T.recOn`, `T.casesOn`, `T.below[_N]`, `T.brecOn[_N]`, `T.ctorElim`, `T.c.elim` | `Lean/Meta/Constructions/RecOn.lean:18-39`, `CasesOn.lean:19-26`, `BRecOn.lean:59-326`, `CtorElim.lean:108-210` | `recursor`: `isAuxRecursor` | `Channel.casesOn` |
| `T.brecOn.go`, `T.brecOn.eq` | `Lean/Meta/Constructions/BRecOn.lean:193-308` | `recursor`: generated with the marked `T.brecOn` (`isBRecOnRecursor`) | |
| `T.noConfusion`, `T.c.noConfusion` | `Lean/Meta/Constructions/NoConfusion.lean:210-354, 402-430` | `recursor`: `isNoConfusion` | |
| `T.noConfusionType` | `Lean/Meta/Constructions/NoConfusion.lean:72-145, 375-400` | `typeConstruction`: `T.noConfusion` is marked | `Channel.noConfusionType` |
| `T.ctorIdx` | `Lean/Meta/Constructions/CtorIdx.lean:41-96` | `typeConstruction`: its precondition (`ctorIdxGenerated`) | `Channel.ctorIdx` |
| `T.ctorElimType` | `Lean/Meta/Constructions/CtorElim.lean:80-106` | `typeConstruction`: `T.ctorElim` is marked | |
| `T._sizeOf_N`, `T._sizeOf_inst` | `Lean/Meta/SizeOf.lean:126-187, 513-528` | `typeConstruction`: its precondition (`sizeOfGenerated`) | `Channel._sizeOf_1`, `Channel._sizeOf_inst` |
| `T.c.sizeOf_spec` | `Lean/Meta/SizeOf.lean:424-473` | `constructorLemma`: its precondition (`sizeOfGenerated`) | `Channel.mk.sizeOf_spec` |
| `T._sizeOf_N_eq` | `Lean/Meta/SizeOf.lean:350-388` | own location: generated only for some nested types while proving the spec theorems, and nothing records which | |
| `T.c.inj`, `T.c.injEq` | `Lean/Meta/Injective.lean:108-178` | `constructorLemma`: its precondition (`injectivityGenerated`) | `Channel.mk.injEq` |
| `T.c.hinj`, `T.ctorIdx.hinj` | `Lean/Meta/Injective.lean:280-303`, `Lean/Meta/CtorIdxHInj.lean:14-71` | `reservedName`: `isReservedName` | |
| field projection `S.x`, subobject parent projection `S.toP` | `Lean/Meta/Structure.lean:50-119` | `projection`: `getProjectionFnInfo?` | `Channel.value` |
| parent projection `S.toP` that is not a subobject | `Lean/Elab/Structure.lean:1409-1440` | `projection`: `getAuxParentProjectionInfo?` | |
| `S.mk._flat_ctor` | `Lean/Elab/Structure.lean:1229-1240` | `constructorLemma`: its precondition (a registered structure) | `Channel.mk._flat_ctor` |
| `S.x._default`, `S.x._inherited_default` | `Lean/Elab/Structure.lean:1354-1392` | `fieldDefault`: Lean's own lookup (`getEffectiveDefaultFnForField?`) | `Rec.x._default` |
| `S.x._autoParam` | `Lean/Elab/Structure.lean:1120-1123` | own location: a `Syntax` value, which uses no axiom, so it has no RG1005 finding | |
| an inductive predicate's `T.below` (an inductive type) and `T.brecOn` (a theorem) | `Lean/Meta/IndPredBelow.lean:83-234` | own location: Lean marks only `T.below.casesOn`; `T.below`'s constructors and recursors are related to `T.below` | |
| computed fields: `T._impl` and its constructions, `T.casesOn._override`, `T.c._override`, `T.f._override` | `Lean/Elab/ComputedFields.lean:107-205` | own location: `T._impl` is tied to `T` by its name alone; an `_override` is recorded only as an `implemented_by` target, which an author can write too | |
| coinductive `T._functor`, its constructions and `T.functor_unfold` | `Lean/Elab/MutualInductive.lean:1359-1409`, `Lean/Elab/Coinductive.lean:118-495` | own location: tied to `T` by its name alone | |
| `S.ext`, `S.ext_iff` | `Lean/Elab/Tactic/Ext.lean:104-176` | own location: requested by the `@[ext]` attribute the author writes, which records the theorem, not the structure; it has the attribute's range | |
| derived instance `instCT` and its handler functions (`instCT.decEq`, `.beq`, `.repr`, `.hash`, `.ord`, `.toJson`, `.fromJson`, `.default`, `.toExpr`) | `Lean/Elab/Deriving/Util.lean:95-163`, `Lean/Elab/Deriving/Basic.lean:178-272` | own location: Lean records the instance, not the type it derives it for | |
| enumeration `T.ofNat`, `T.ofNat_ctorIdx` | `Lean/Elab/Deriving/DecEq.lean:222-262` | own location: tied to `T` by its name alone | `Word.ofNat` (a user-written one, not related) |
| `T.match_on_same_ctor` and its `.het` | `Lean/Meta/Constructions/CasesOnSameCtor.lean:29-229` | `matcher` (`isMatcherCore`) and `recursor` (`isAuxRecursor`) | |
| `instBEqT.beq_spec`, `instOrdT.ord_spec`, `inst.field_spec` | `Lean/Meta/MethodSpecs.lean:126-227` | `reservedName`, to the instance | |
| `TypeName`'s `instImpl`, `RpcEncodable`'s packet type | `Lean/Elab/Deriving/TypeName.lean:17-27`, `Lean/Server/Rpc/Deriving.lean:100-141` | own location: hygienic names that nothing records a relation for | |
| matcher `f.match_N` | `Lean/Meta/Match/Match.lean:1087-1125` | `matcher`: `isMatcherCore` | `firstIndex.match_1` |
| `f.match_N.eq_K`, `.splitter`, `.congr_eq_K` | `Lean/Meta/Match/MatchEqs.lean:151-322` | `reservedName` or `matcher`: `isMatchEqName?` | |
| `f.match_N._arg_pusher` | `Lean/Elab/PreDefinition/WF/Unfold.lean:98-165` | own location: tied to the matcher by its name alone | |
| `f._sparseCasesOn_N`, its `.else_eq` | `Lean/Meta/Constructions/SparseCasesOn.lean:65-145`, `SparseCasesOnEq.lean:86-92` | `recursor`: `isSparseCasesOn`; `.else_eq` by `reservedName` | |
| `f.eq_K`, `f.eq_def`, `f.eq_unfold` | `Lean/Elab/PreDefinition/Eqns.lean:366-399`, `Lean/Meta/Eqns.lean:326-327`, `Lean/Elab/PreDefinition/EqUnfold.lean:26-70` | `equationLemma`: `Meta.declFromEqLikeName` | `countdown.eq_1`; the user-written `later.eq_7`, declared before `later` (not related) |
| `f._f`, `f._sunfold` | `Lean/Elab/PreDefinition/Structural/Main.lean:95-106`, `SmartUnfolding.lean:17-74` | `structural`: `Structural.eqnInfoExt`, or `f`'s value uses `f._f` | `walkDown._f`, `walkDown._sunfold` |
| `f._unary`, `f._mutual` | `Lean/Elab/PreDefinition/WF/PackMutual.lean:66-104` | `wellFounded`: `WF.eqnInfoExt`'s `declNameNonRec` | `countPair._unary` |
| `partial_fixpoint`'s `f.mutual` | `Lean/Elab/PreDefinition/PartialFixpoint/Main.lean:193-217` | `wellFounded`: `PartialFixpoint.eqnInfoExt`'s `declNameNonRec` | |
| `f.induct`, `.induct_unfolding`, `.mutual_induct`, `.fun_cases`, `partial_fixpoint`'s `.fixpoint_induct`, `.coinduct`, `.partial_correctness`, `f.congr_simp`, `f.hcongr_N`, `T.enumToBitVec` and its lemmas | `Lean/Meta/Tactic/FunInd.lean:910-1548`, `Lean/Elab/PreDefinition/PartialFixpoint/Induction.lean:105-426`, `Lean/Meta/CongrTheorems.lean:392-480`, `Lean/Meta/Tactic/BVDecide/Normalize/Enums.lean:41-379` | `reservedName`: `isReservedName` | `countPair.induct` |
| `f._unsafe_rec` | `Lean/Elab/PreDefinition/Basic.lean:255-295` | `recursionHelper`: the admitted helper authorization, which observed Lean's recursion compiler regenerate it (`Findings.stepOf`) | `countUp._unsafe_rec` |
| `f._proof_N` | `Lean/Meta/Tactic/AuxLemma.lean:43-79`, `Lean/Meta/Closure.lean:457-460`; in a `module` file, a `by` proof Lean elaborates in the exporting context (`Lean/Elab/SyntheticMVars.lean:475-527`): in a declaration's header, or in the body of an exposed definition, including its `where` and `let rec` helpers, whose tactic blocks run under the definition's name (`Lean/Elab/MutualDef.lean:551`, `Lean/Elab/LetRec.lean:66-67, 101`) | `auxiliaryLemma`: a constituent of `f`'s declaration (its type or value, or, for an inductive type, the type, a constructor's type or a field's default value of any type of its mutual block, which Lean elaborates under its first type's name: `Lean/Elab/MutualInductive.lean:1566, 1588`), its equation information's value, or the function its well-founded equation information names uses it, or else the statement of `f.eq_def` (`Meta.declFromEqLikeName`), which `WF.mkUnfoldEq` states from the pre-definition it cleans separately (`Lean/Elab/PreDefinition/WF/Main.lean:84-89`); or else the value of `f._unsafe_rec` uses it, and its chain runs through that admitted helper; or else the type or value of a declaration of its module uses it, and its chain runs through that declaration: one named under `f` at any depth that is not itself a generated auxiliary declaration (it is not auxiliary-named, or it has a recorded declaration range), such as a `where` or `let rec` helper `f.go`, or another auxiliary declaration with no recorded range that is itself related in one of these ways, under whatever declaration that one is named (Lean abstracts a proof nested in a proof); one nothing related uses, as `GuessLex` can leave, keeps its own location | `countdown._proof_1`, `countUp._proof_3` (through `countUp.eq_def`), `sumButLast._proof_1` (through `sumButLast._unsafe_rec`), `middle._proof_1` (through `middle._proof_2`), the `_proof_N` of `initialize counter`'s action; the user-written `middle._proof_8`, `middle._proof_9`, `Util._proof_8` and `later._proof_8`, which have declaration ranges (not related); a header proof and a helper's proof of a `module` file are not observed |
| `f._simp_N`, `f._cbv_eval_N` | `Lean/Meta/Tactic/Simp/SimpTheorems.lean:453-471`, `Lean/Meta/Tactic/Cbv/CbvEvalExt.lean:61-64` | `auxiliaryLemma`: as for `f._proof_N` (a tactic's lemma), or it uses `f` (an attribute's lemma) | |
| `f._private_N`, `f.grind_N`, `f._impossible_N`, `inst._aux_N`, `f.unsafe_impl_N`, `f._expr_def_N`, `f._cert_def_N`, `f._reflection_def_N` | `Lean/Elab/BuiltinTerm.lean:451-465`, `Lean/Meta/Tactic/Grind/Main.lean:497-498`, `Lean/Elab/Tactic/Impossible.lean:88-92`, `Lean/Meta/WrapInstance.lean:185-283`, `Lean/Elab/BuiltinNotation.lean:556-579`, `Lean/Meta/Tactic/BVDecide/TacticContext.lean:40-42` | `auxiliaryLemma`: as for `f._proof_N` | |
| `f.unsafe_N` | `Lean/Elab/BuiltinNotation.lean:556-579` | own location: recorded only as the `implemented_by` target of `f.unsafe_impl_N` | |
| RPC wrapper `f._rpc_wrapped` | `Lean/Server/Rpc/RequestHandling.lean:113-139` | `auxiliaryLemma`: `Server.userRpcProcedures` | |
| the action `initFn` of `initialize id : T ← e` | `Lean/Elab/Declaration.lean:342-369` | `auxiliaryLemma`: `id`'s init attribute (`getInitFnNameFor?`); an unnamed `initialize` keeps its own location | `counter`'s action |
| `native_decide`'s and `bv_decide`'s axiom `f._native.….ax_N` | `Lean/Meta/Native.lean:75-84` | own location: it has the tactic's range | |
| `f._auto_N` | `Lean/Elab/Binders.lean:92-105` | own location: a `Syntax` value, which uses no axiom | |
| `let rec` and `where` helper `f.go` | `Lean/Elab/LetRec.lean:49-63` | own location: the author wrote it, and it has its own range; an auxiliary declaration named under `f` that only the helper uses is related to the helper (the `f._proof_N` row) | |
| parser declarations of `syntax`, `macro`, `notation`, mixfix and `declare_syntax_cat` | `Lean/Elab/Syntax.lean:293-451` | own location: generated by a command, not from a declaration; it has the command's range | |
| `_aux_…___macroRules_…`, `…___elabRules_…`, `…___unexpand_…` | `Lean/Elab/AuxDef.lean:26-39`, `Lean/Elab/MacroRules.lean:46-70`, `Lean/Elab/ElabRules.lean:48-84`, `Lean/Elab/Notation.lean:106-161` | own location: named in the current namespace only (an unexpander is keyed by the constant it prints, but generated by the `notation` command); it has the command's range, and a selection range Lean takes from the name suggestions the command passes to `aux_def` (`Lean/Elab/AuxDef.lean:39`), which need not lie within that range: `macro_rules` over several syntax kinds is split by kind (`Lean/Elab/Syntax.lean:483-496`), and each kind's definition has the range up to that kind's last alternative and a selection range up to the last alternative of the kinds not yet split off (`Lean/Elab/MacroRules.lean:52, 73`). Its admitted selection range is then its range (`Ranges.admitted`) | the `vzero` elaborator in `Channel` (not related); the first definition of a `macro_rules` command over two syntax kinds (selection range past its range) |
| `p.formatter`, `p.parenthesizer` | `Lean/ParserCompiler.lean:93-125` | own location: the combinator attributes that record them are declared `unsafe`, so the checker's safe code cannot read them | |
| `decl._regBuiltin.…` | `Lean/Compiler/InitAttr.lean:149-157` | own location: only Lean's own builtin attributes create it | |
| declarations of `register_option`, `register_simp_attr`, `register_label_attr`, `register_linter_set` | `Lean/Data/Options.lean:230-255`, `Lean/Meta/Tactic/Simp/RegisterCommand.lean:15-30`, `Lean/LabelAttribute.lean:84-91`, `Lean/Linter/Sets.lean:35-37` | own location: generated by a command, not from a declaration | |
| doc role wrappers `decl.getArgs`, `decl.mdRenderer` | `Lean/Elab/DocString.lean:601-654, 1120-1148` | own location: its extension records it under the role it implements, not the declaration it wraps | |
| `show_panel_widgets`, `set_library_suggestions`, `register_try?_tactic`, unnamed `unif_hint`, `declare_config_elab`, `store_traces_as`, `reprove` and `init_quot` declarations | `Lean/Widget/Commands.lean:79-94`, `Lean/LibrarySuggestions/Basic.lean:441-447`, `Lean/Elab/Tactic/Try.lean:316-347`, `Init/NotationExtra.lean:69-82`, `Lean/Elab/ConfigEval/DeriveEvalTerm.lean:100-125`, `Lean/PostprocessTraces/StoredTraces.lean:127-155`, `Lean/Util/Reprove.lean:28-50`, `Lean/Elab/BuiltinCommand.lean:286-287` | own location: generated by a command, not from a declaration | |

Not declarations of the environment: `_example` and `#eval` temporaries
(`Lean/Elab/MutualDef.lean:1196-1204`, `Lean/Elab/BuiltinEvalCommand.lean:232`), the compiler's
`_boxed`, `_lam_N`, `_elam_N`, `_redArg`, `_closed_N` and `_spec` names (`Lean/Compiler/LCNF/`),
and the `_private.<Mod>.0.` and `._@.…_hyg.N` spellings of other declarations
(`Lean/PrivateName.lean:27-64`, `Init/Prelude.lean:5756-5846`), which the clauses read through
`extractMacroScopes` and `privateToUserName`. Not generated in v4.34.0: `binductionOn`,
`toCtorIdx`, `_binary`, `_auxLemma`, `_cstage1` and `_cstage2`.

## Project setup and releases

**Proved** (`RegulaCore.Setup`, over the observation `regula init` and `regula doctor` read):
`plan_idempotent`, applying `init`'s plan leaves an empty plan, so a second run writes nothing;
`plan_eq_nil_iff`, the plan is empty exactly when every setup issue is one `init` does not fix;
`issues_run`, the plan removes exactly the fixable issues and adds none. The option check covers
exactly the claimed targets (the root targets the manifest does not exclude, and none while an
existing manifest fails RG2002), as RG2006 does: `run_sets`, every required option a claimed
target built without is then set to its required value as `RegulaPolicy.Community.sets` reads
it, which meets RG2006's requirement on that option (`meets_of_sets`); `resolved_run`, every
claimed target then has a value for every required option or a `-D` candidate of its own extra
`lean` arguments names it; `added_unargued`, no option the plan adds to the package or to a
claimed target's own configuration names an option that a `-D` candidate of that target sets
(the candidates of `RegulaPolicy.Community.argumentSettings`, RG2006's own reading, which
includes every `-D` that `lean` reads only under the command-line assumption stated in
`RegulaPolicy.Community`); `argued_run`, the plan leaves unchanged the required options that
claimed targets set only with such a `-D`, which `doctor` reports once as a setup issue `init`
does not fix, and `arguedBy_run` those of each claimed target; `run_options_unclaimed`, when a
root target is excluded the package's options are unchanged, the options going into each claimed
target's own configuration (`run_plan_targets`), so none reaches an excluded target, and an option
some claimed target's `-D` sets likewise goes only into the configuration of each target that
builds without it; and `run_options_prefix` and `withAdded_prefix`, the options and extra `lean`
arguments the package and each claimed target already give are kept. An edit adds a missing
piece and has no form that replaces a lint driver or an option value. The starter manifest is
planned exactly when there is no manifest and the package has a `lean_lib` for it to claim
(`plan_manifest_mem`); a package with none has a setup issue `init` does not fix.

**Checked when it runs:** `init` observes the project again after writing and restores every
file it wrote unless the new plan is empty and each claimed target of both observations, matched
by kind and name, sets the same required options only with a `-D` as before (`arguedBy_run`'s
executable counterpart, which catches an added option that reaches such a target; a target the
new observation does not claim, as while a starter manifest fails RG2002, is not compared), and it
writes the starter manifest only after `Manifest.parse` reads the text back as exactly that
manifest. That the lakefile edits realize
the model's `apply` is this check, not a theorem. That `allClaimed` holds only when the observed
targets are every root `lean_lib` and `lean_exe` is how `observe` builds the observation, and the
extra `lean` arguments it reads are those of the audit's inventory, read by the same
`Lake.libraryOptions` and `Lake.executableOptions`. `doctor` runs the audit's own RG2002 functions
(`Manifest.loadFor`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`) and RG2006
decision (`Community.failures`) over Lake's resolved options of each claimed target. It applies
Mathlib's options when the workspace contains Mathlib, where the audit applies them to a target
whose modules import Mathlib: by `conforming_of_mathlib` a target `doctor` accepts also passes the
audit, while `doctor` may ask a target that imports no Mathlib for Mathlib's options, which
`init` writes under `weak.` so they are then ignored. A module below a library root that no
library includes is a failing setup issue only when a claimed module (of a library or executable
the manifest does not exclude) reaches it by import through the package's modules, which the
audit rejects as outside every library; any other such module is a `note` that does not count
toward `doctor`'s exit status. That reachability is read from the sources' import headers, not
from a build. Each such finding states how many modules the library leaves out and names at most
`shownModules` of them, wrapped (`moduleLines`, which prints `moduleSummary`'s names grouped by
`wrapFrom`): `moduleSummary_complete` proves those names are a prefix of the modules and the
count is exactly the rest, and `wrapFrom_flatten` that grouping keeps each name, in order; that
the finding text is `moduleLines` is by definition, and the line width is layout. The starter
manifest lists each `lean_exe` with the first library containing its root module, so, by its
definition rather than a theorem, it meets `RootsClassifiedAlike` unless a root lies in two
libraries; a library whose modules are all such roots is refused as RG2002 by `doctor`. `doctor`
prints one RG2006 finding for the claimed targets that share a claim and the same failure
detail, where the audit prints one per target. The agent-guidance file is found operationally:
from the Lake root up to the nearest directory holding a `.git` entry (Git itself is not run),
the nearest `AGENTS.md` with the section, else the nearest that exists, else the repository
root's; the skill files are read and written at that repository root (the Lake root outside a Git
repository).

Regula's own `lakefile.lean` refuses to load, before any module compiles, when the running Lean's
`Lean.versionString` is not the release its `lean-toolchain` names. This is an elaboration-time
check, not a theorem; Lake reuses an elaborated configuration while the file's text and the
running Lean are unchanged, and `lake update` elaborates it again.

**Trusted:** Lake's loader, its TOML grammar, Lean's import-header parser and Lean's frontend,
which elaborates a `lakefile.lean` as Lake does to locate the `package`, `lean_lib` and
`lean_exe` declarations, and the filesystem. Runs of `init` and `doctor` on scratch projects in
both formats (fresh, template, inline-table, structure-instance, bare-`package` and
computed-`leanOptions` shapes, another driver, a contradicting option, a stale skill, a library
without globs, left-out modules that a claimed module does and does not import, a library the
manifest excludes, with options written into bare and configured claimed targets, a package
with no `lean_lib`, a package-level `-D` setting Mathlib's options as in the first adopter, a
`-D` in one library's own `moreLeanArgs` in both formats, and a Lake project in a subdirectory of
a Git repository with and without a root `AGENTS.md`) are bounded observations, as are the
lakefile's refusal of Lean 4.33.0 and 4.34.1 through the `lake` command line and when a checker
executable loads the workspace.

**Releases** ([procedure](contributing.md#release)): **Proved** in `lean/Regula/Release.lean`,
and checked by the kernel each time a step elaborates it: `tagAction`, the decision of the
candidate and publish steps, proceeds exactly for the head of `main` of an unpublished release
whose tag is absent or names the release commit (`tagAction_release_iff`), so publication, which
creates the tag, never leaves it naming another commit; it changes nothing once the release is
published (`tagAction_published`, `tagAction_skip_iff`), always proceeds on the head of `main` of
an unpublished release that no tag names elsewhere (`tagAction_converges`), and
`tagAction_refuse_iff` gives the remaining case. The derivation over the Conventional Commits
headers of the commits of `main` since the previous release (`parseCommit`) alone, `derive`, is
at least each commit's bump (`derive_ge`), calls for no release exactly when every commit's type
calls for none (`derive_eq_none_bump`), and is undecided exactly when a subject is not a header
(`derive_eq_none`). `nextVersion`, the version the open step derives from those headers,
`lean-toolchain` and the workflow's requested bump, bumps from its predecessor at least as much
as each header calls for, whatever was requested and also when the derivation is undecided
(`nextVersion_ge`); its bump is never less than the headers' greatest bump or the requested bump
(`nextBump_ge_called`, `nextBump_ge_requested`) and at least minor for a toolchain move
(`nextBump_moved`), so a toolchain move or a request releases even when every commit's type calls
for none, and an undecided derivation yields a version only for a requested bump
(`nextBump_undecided`). The version it yields follows its predecessor (`nextVersion_follows`):
later, on its toolchain for a patch release, with the lower components reset on a new line.
`covers`, which the candidate step checks on the commits of `main` since the release listed
before the one it releases up to the commit it releases, holds exactly when that release's bump
from its predecessor (`Version.bumpTo`) is at least each such header's bump, and at least minor
for a toolchain move (`covers_iff`); it holds for the release the open step derived from the same
commits (`nextVersion_covers`, with `Version.bumpTo_bump`). `publishedExactly`, which the
candidate step checks before it creates a release commit and the open step when it starts and
again just before it pushes, holds exactly when every release listed before the one the step
handles is published and every published release is one of them (`publishedExactly_iff`); when
it holds, that release's listed predecessor is the latest published release
(`publishedExactly_latest`), and a release whose listed predecessor is unpublished, or is earlier
than a published release, is refused (`publishedExactly_refuses`), both given the releases before
it listed in ascending order, which `releases_ascending` checks. So once a release is published,
no release listed in its place is released. `admits`, which the open step also
checks, characterizes a new release exactly (`admits_iff`); an admitted release's tag is new
(`admits_new`), and once the legacy release `v4.34.0` is listed, Lake's order of the versions
the releases' lakefiles declare puts an admitted release above every listed one
(`admits_lake`, `Version.lakeLt_declared`). A release that follows its predecessor has patch `0`
exactly when it starts a new line (`follows_patch_iff`), and a release on another toolchain
starts one (`follows_toolchain`). **Proved** in `RegulaCore.Edition`: a build
labelled a release is admitted exactly while its tag is absent or names its commit
(`labelAdmitted_release_iff`), an unreleased build previews a release's edition exactly while
that release is the latest listed and has neither asset nor tag (`releaseSource_preview_iff`),
an artifact is deployable exactly when every release edition in it is its release asset
(`publishable_iff`), and a release that follows its predecessor has
patch `0` exactly when it starts a new line (`follows_startsLine_iff`). The rest of
`Release.lean` is operational: the text reading of a Conventional Commits header (`parseHeader`)
and of the edited files, its check that a commit of `main` or of a pull request is unreleased,
`agree`, and `adopt`, which checks, with `git` trusted, that the release commit is the content CI
derived from `main`'s commit before CI records it as that commit. Its edits of
`RegulaCore/Edition.lean`, `lakefile.lean` and the adoption guide's compatibility table are read
back before use; its stamps of `RegulaCore/Rule.lean` are a convenience that reads text. `agree`,
a step of `verify` before acceptance, refuses a `lakefile.lean` version, as Lake reads it
(`lake reservoir-config`), other than the latest listed release's, and a compatibility table
other than the one `Regula.releases` gives. The kernel checks the edited modules' theorems when
the release pull request's checks and CI's checks of the release commit build them:
`releases_ascending`, `releases_follow`, `installed_listed`, `release_attributes_rules` (when
`installed` is a release, no lifecycle position of any rule is `.unreleased`; on the release
commit this is the gate before anything is published), `lifecycle_listed` (every release a rule's
lifecycle names is in `versions`) and `introduced_startsLine` (the release that introduces a rule
has patch `0`, so it is not a patch release). What the steps observe (whether the release is
published, the versions of the published releases, read from the tags of the releases GitHub
lists that are not drafts, the head of `main`, the tag, the commits since the previous release,
a pull request's title and head), GitHub's signature verification, that publishing a release
creates its tag at the given commit, tags, immutable releases, pull requests, squash merges
taking the pull request's title and description, workflow ordering, and that Lake and Reservoir
read and order versions as their source shows ([Reservoir](contributing.md#reservoir)) are
trusted.

## The diagnostics gate

**Proved** in `lean/Regula/DiagnosticsGate.lean`, checked by the kernel in ordinary acceptance's
build and each time a step of the [diagnostics workflow](../../.github/workflows/diagnostics.yml)
elaborates it (its `applies` and `diagnostics` jobs, on every pull request): `verdict`, the
decision of the required `diagnostics` check over the workflow's `needs` context, passes exactly
when the job `applies` succeeded, every job it decided is one the gate needs, and every job the
gate needs passed when it was decided to apply and was skipped when it was decided not to
(`verdict_iff`, with `admits_iff`). So a failed or cancelled job is refused, as is one that ran
out of time, which GitHub reports as one of the two, and as is a job decided to apply that was
skipped, as the jobs not yet started are when a run is cancelled. `decisions`, the decision
`applies` writes and each partition job's `if:` reads, runs the campaigns on every run other than
a pull request's (`campaign_of_ne`) and on a pull request's exactly when an input of `inputs`,
the only statement of the campaigns' paths, covers one of its changed paths
(`campaign_pullRequest_iff`); a pull request whose every changed path lies in `docs/` or
`website/`, or is `README.md` or `AGENTS.md`, runs none (`campaign_documentation`). A pull
request's changed paths are those at which the merge commit GitHub creates and tests differs from
its first parent, the head of the base branch, a rename as both of its paths; `applies` refuses a
checked-out commit without exactly two parents. Reading the event, the changed paths, the
context's JSON and the decisions `applies` wrote is operational, and a result, event or decision
the steps do not know fails them. **Trusted:** GitHub (the event, the merge commit, the `needs`
context and its report of a matrix job as succeeded only when every job of it did, a job's `if:`,
timeouts, cancellation, that an `always()` job runs on a cancelled run, and the ruleset that
requires `diagnostics`) and `git` (the commits it fetched and the paths `diff-tree` lists). That
every partition job of the workflow is in the gate's `needs` and has its `if:` read its own
decision is the workflow's wiring, which no step observes; a needed job without a decision and a
decided job the gate does not need fail the gate.

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
| history | 10 project and file invocations | replacement history, unsupported evaluators, source changes; the written `execution` as a shared form with every root derived | External | observed |
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
| checkerSelftest structural | a lemma realized in a claimed module and the toolchain, in both import orders; unchecked, circular, `sorry` and kept-cycle copies of one name | Lean's realization, import, kept copy and kernel check of several copies of one name | External | observed; the admission decision is `Admission.replayMap_sound`, `replayMap_complete` and `checkCopies_sound` |
| checkerSelftest execution | each compiler-path mutation and correspondence control, with its positive and fresh restoration | compiler-derived execution coverage and correspondence evidence through the public gate; the emitted-C check of reachable code on the pin | External | observed |
| checkerSelftest cli, environments, build-policy, lint-driver | CLI sweep, adopters, clean checkout, ordinary build, `lake lint` exit classes | packaging, Lake and build integration | External | observed |
| ordinary | `qualify registry`, `qualify native` | CLI output invalidation, registry and site validators; compiler messages and ranges | External | observed |
| ordinary | `RegistryChecks` codec, source and execution-account cases | registry, diagnostic and source codecs; the result file's shared execution form | Proved in part | round-trip theorems of `Json` values; that the shared form is kept, and that a parsed shared form reads back to the built account, are observed; open: state the remaining refusals as theorems |
| standalone | `qualify environments` finalize mutations | `finalize` refusals | Proved relation | `finalize_iff`; instance membership sampled; no transcript substitution: an accepted run has no transcript job (`accepted_no_transcript_subjects`) |
| standalone | `qualify acceptance fences` packet mutations | worker-packet admission through a real proxy | External transport | admission proved (`checked_indexedResults`) |
| standalone | snapshots, input inventory, receipts, frozen exits, documentation source, closure, configuration and fence evidence | Git, Lake, filesystem, elaboration-time IO, signals | External | observed |
| project audit | admission reuse recheck | a report that reuses a module, or requires a key in a reused module, that no earlier environment offered over a frozen closure, or leaves an owned module it loaded unreplayed, is refused | Proved | `Admission.reuseJustified_frozen`, `Admission.reuseJustified_admitted`, `Admission.replayed_of_loaded` |
| project audit | changed import, changed `.olean` part | an owned module is replayed unless an offer covers it over its closure here and over artifacts read again with their frozen parts | Proved | `Admission.replayed_unless_offered`, `Admission.replayed_of_changed`, `Admission.replayed_of_changed_import`; an artifact not read again with its frozen parts cannot support an offer (`Admission.Unchanged`) |
| checkerSelftest structural | a changed, removed and added `.olean`, `.olean.server` and `.olean.private`, each restored, for a module with three parts and with one, through `Inspection.readings` and `Admission.currentOffers` | reading the frozen parts: each change withdraws the offer and `Inspection.changedArtifact?` reports it | External | observed |
| checkerSelftest structural | a fresh audit of two claimed libraries that import one another | the report workers, Lean's import and the kernel reuse a requested module: accepted, each module replayed in one environment, the reused module's key required | External | observed; the decision is `Admission.reuseJustified_admitted` and `Admission.replayed_of_loaded` |
| project audit | none | a frozen `.olean` part that changes during the audit is RG2005 | External | open: MUT-02 not yet evidenced through the gate; reading the parts is observed directly (two rows above), and no intended-reason control rewrites a part between the freeze and the final comparison |

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
  source-snapshot changes. The six invocations the oracle validates (positive and
  unsupported-evaluator) also require the `execution` the file holds to be a shared form whose
  every root entry is derived (`SharedExecution.derivedOnly`).
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
- `environments`: this repository's claimed environments, each report acquired as the audit
  acquires it (`Inspection.inspect`); the complete and restored positives must be accepted, and
  each omitted, duplicated, rebound, substituted or mis-bound mutation refused for its intended
  reason.
- `self-audit`.

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
whose schema version is 2, each array decoding element by element in order. Every rationale is
the JSON string, the claim is `Profile.parse?` of the JSON string, an absent
`executables` is empty and a present one is its string array, and an absent `execution`
is `report` while a present one is `ExecutionClaim.parse?` of the JSON string (`SurfaceDecodes`,
`ExcludedLibraryDecodes`, `ExcludedExecutableDecodes`). Every library and executable name is
`recordedName` of the JSON string (`parse_input`, `recordTargets_ok`): Lake's own reading of a
target name (`Lake.stringToLegalOrSimpleName`, which its TOML loader applies to a `lean_lib` and
a `lean_exe` name and `lake build` to a target argument), spelled as Lean prints a name. The
Lake inventory records the same spelling of each library's and each executable's name
(`targetSpelling`), so the `name` a `lakefile.toml` gives a `lean_lib` or a `lean_exe` is
recorded as that target's name by definition. `parse_recorded`: every library and executable
name of an accepted manifest is its own recorded spelling, so with `parse_sound`'s distinctness
no accepted manifest names one library, or one executable, under two spellings. That Lean reads
a name it printed back as that name, which is what accepts the spelling `init` writes for a name
that is not an identifier (`«widget-tool»`), is trusted and not proved; the identity stage
checks only that each recorded spelling is its own recorded spelling and refuses a spelling
whose recorded spelling is not, which does not show that the name was read back. `loadFor` is
the module's only file reader: it takes the project's Lake inventory, adds the missing-file
check and the read, and parses the text with `parseFor` and the inventory's libraries and
executables. Every
command that reads the manifest with the inventory at hand uses it: the project audit, the file
audit (`axiomGate --file`), the documentation audit, the rule examples, `doctor`,
`--explain-config`, the fresh checker and the environment census. Two readers have no inventory
where they read and apply the pure `parse` to the file's text: the self-test harness, to derive
its control manifests and build targets, and `doctor`'s observation of the project
(`Setup.observe`), to scope which targets the manifest excludes. Neither classifies the manifest
against Lake; `doctor` does that through `loadFor` (`validManifest`), and each self-test control
through the gate it runs. `parseFor_ok`: `parseFor` accepts exactly the manifests `parse`
accepts that name only those libraries and executables, so the theorems about `parse` hold of
the manifest those commands use. `parseFor_unknownLibrary`, `parseFor_unknownExecutable` and
`unknownEntry?_some`: when the text parses, its target names are recorded and some library
entry, claimed or excluded, has a recorded spelling that is not an inventory library, it refuses
with `unknownTarget` of the first such entry, quoting the entry in the spelling the decoded text
gives it; when every library entry is an inventory library and some executable entry is not an
inventory executable, it refuses with `unknownTarget` of the first such executable entry in the
same way; a text `parse` refuses keeps that earlier refusal. One message function writes both
refusals, so they differ only in the kind's words. This is the only refusal of such an entry: of
the two inclusions between the manifest's and the inventory's targets,
`AxiomGate.checkClassification` checks only that every root library and every root executable is
classified. The refusal lists each inventory target of the entry's kind by
`lakeTargetName`: its name without escaping when that text has the same recorded spelling, and
the recorded spelling otherwise, so a manifest that copies a listed name records that target
whenever the inventory's spelling is its own recorded spelling
(`recordedName_lakeTargetName`); that hypothesis is the same trusted read-back. That the
inventory passed is the project's is the caller's linkage, not a theorem. The refusal-class
theorems (`parse_malformed`,
`objectWithKeys_unknown`, `topLevel_unknownKey`, `topLevel_schemaVersion`, `topLevel_emptySurfaces`,
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
`parse_emptyExclusions`: for JSON meeting the top-level conditions with empty exclusion arrays
whose surfaces parse, `parse` is the identity stage (`recordTargets`) of exactly those
surfaces; it does not prove that any particular surface is accepted.
`parse_ok` (`parse` accepts `m` exactly when `PolicyCodec.parse` returns a value `parseValue`
accepts with some `raw` from which `recordTargets` returns `m`), `parseValue_ok`
(`parseValue` accepts a value with `m` exactly when `m.Valid` and the value `Encodes` `m`, so
`Manifest.Valid` is exactly what the value stage admits) and
`toJson_encodes` give `parseValue_toJson`; `structuralManifest_valid` shows the structural copy
of a valid manifest is valid whenever it claims an actual surface, and `restrict_valid` the
same of a restriction that keeps a surface. The schema-version check
compares `JsonNumber` fields with derived equality (`schemaVersion2`) rather than `Json`'s
`partial` `BEq`, with the same runtime meaning.

**The structural and execution partitions.** The structural clusters, and the correspondence
clusters of the execution partition, run in the structural project: this repository's package
restricted to its application. `structuralProject` (in
`CheckerSelftest.lean`) derives it from the workspace Lake loads: the `AuditApp` library, the
executables the manifest claims on it, the fixture module the contamination controls import,
and every root-package module those import (`Lean.parseImports'`, `Workspace.findModule?`),
each kept target with its configured roots, globs, source directory and Lean options. That
derivation is IO over Lake's data with no theorem; it refuses a missing library, module or
claimed executable, a source outside the repository and a target built with extra `lean`
arguments. The project has no `RegulaPolicy` library and requires no package, so a gate in it
builds and inspects the application alone, and the checker probe's own imports resolve to the
running checker's artifacts. `Manifest.restrict` derives the project's manifest from the
repository's: `restrict_libraries` proves it classifies exactly the kept libraries the actual
manifest classifies, `restrict_executables` that it names only actual executables, and
`restrict_roundtrip` (with `parseValue_toJson`: `parseValue (toJson m) = .ok m ↔ m.Valid`, and
the identity stage returning the restriction unchanged) covers what the gate reads at the `Json`
value boundary for any accepted manifest whose restriction keeps a surface. `structuralBase`
checks that hypothesis at run time, and that the application is the project's only claimed
library; no theorem links those checks to the hypothesis. The
text boundary is trusted: `Json.compress` is `partial` and `PolicyCodec.parse` runs core `partial`
parsers, so no theorem describes them; `parse_of_encodes` names what they must deliver. The
variants that rewrite the `AuditApp` surface after derivation are not covered. The lib-only
variant excludes every actual `AuditApp` executable it stops claiming, and app-omitted-exe
leaves them unclassified on purpose; claimed-exe keeps claiming them beside its added
executable, so two claimed roots each define `main`.

One structural control needs the checker's own package as the audited project: a claimed module
that imports the probe's report records must be refused as contamination although the force
import brings those modules into every report. It runs in a copy of the repository whose
manifest `Manifest.structuralManifest` derives (`structural_libraries`,
`structural_executables` and `structural_roundtrip`, under the claim hypothesis its guard
checks at run time). `RegulaPolicy` stays claimed there because the checker probe's own imports
resolve to it in a self-hosted copy;
`Regula.Checker.Environment` does not elaborate unless every module in the probe's import closure
outside the toolchain is a `RegulaPolicy` module or one of
`RegulaPolicy.infrastructureModuleNames` (the command beside `probeModuleNames`, whose docstring
states what it does not see). The control was changed when the structural partition was
divided into shards, and is now two clusters. `structuralSelfHosted` builds the copy, runs the
incremental gate on the mutation and restores it. No fresh gate runs on that mutated and
restored copy any more: the accepting gate there is replaced by a checked identity of the
restored copy's fresh input with that of a copy prepared anew, and by the accepting fresh gate
of `structuralSelfHostedPositive` on a copy prepared the same way (`prepareSelfHosted`), which
is in the other shard. `freshInput` takes what the gate's copy operation copies from each of
the two copies, and any differing path or byte fails the first cluster. That the two together
stand for the replaced gate rests on two facts, neither of them a theorem. First, a fresh gate
reads the audited project only through `copyProject`, which prunes the project's `.lake`, and
builds that copy from empty output; without `--with-docs`, as here, it reads no other file of
the project, and the packages directory it links is the repository's for every copy. So equal
fresh input gives the same gate run, and the setup build, the incremental gate and the
restoration are observed to leave the prepared input. Second, the two shards are jobs of one
workflow matrix, so whenever the diagnostics workflow runs them it starts both on the one commit
it checks out. That both pass before merging is enforced by the ruleset of `main`, not by the
self-test, which observes nothing of the other job: the workflow runs the matrix on a pull
request exactly when it changes one of the paths `Regula.DiagnosticsGate.inputs` lists, and its
required `diagnostics` check, which reports on every pull request, passes on a run where the
matrix applies only when the matrix job succeeded in that run
([the diagnostics gate](#the-diagnostics-gate)). That GitHub reports a matrix job succeeded
only when every job of it did is GitHub's behaviour, trusted.

Each partition's baseline build names what its controls read from the repository's own build
(`Partition.baseline`, and `baselineOf` for a shard). The gates of these two partitions run in
projects of their own, where the gate builds that project's targets itself, and the manifest
controls run `axiomGate` on the repository with a manifest it refuses before any build. So the
structural baseline is `axiomGate`, `docFenceAudit` and `freshChecker` (its second shard runs
no `docFenceAudit`), the execution baseline is `axiomGate` alone, and neither builds the
repository's claimed surface; the other partitions keep the complete baseline. That is a
reading of the controls' code, not a theorem. Two guards bound it: after the baseline build,
`toolPath` refuses an executable that build did not name (for every checker executable the
self-test's own module runs, other than itself), and `baselineOf_axiomGate` proves that every
baseline names `axiomGate`, which `CompilerPaths` and `PolicyQualification` run by its path. A
claimed-surface `.olean` that a control read from the repository's build without the baseline
naming it would be absent on a clean checkout and fail that control there; on a warm local
build it is not detected. `scripts/verify.sh` builds the self-test, `axiomGate` and, for a
structural selection, its other checker executables in one Lake invocation
(`RegulaVerification.commands`), so the gate's own modules compile beside the self-test's last
ones instead of after its link; that command selects nothing, and the baseline build still
names and builds its targets. The frozen-artifact, library cycle and manifest
controls run in the structural clusters' queue, so no more of them run at once than the queue
has workers.

The controls of each of these two partitions are divided into two shards, `1/2` and `2/2`
(`--shard`), which the diagnostics workflow runs as separate jobs. Every control carries its one
shard where the partition lists it, and a shard runs the controls that carry it (`inShard`);
`inShard_cover` proves that the two selections together are a rearrangement of the whole list,
so each control runs in exactly one shard. Both shards list the same controls because they run
the same sources, which no theorem states. The structural shards are the mutation clusters
`self-hosted`, `a` and `b` with the frozen-artifact controls, and `self-hosted-positive`, `c`
and `d` with the library cycle and manifest controls; the execution shards hold one
correspondence cluster each and alternate compiler-path cases. A shard's PASS names the
controls it ran and is not the partition's.

Before the structural project, every cluster ran in a copy of the whole repository claiming
`RegulaPolicy`, and one partition held the structural, correspondence and compiler-path
controls: an instrumented run took 513 s, in which 21 gate runs each inspected the unchanged
`RegulaPolicy` library (about 475 s of roughly 1,200 s of control work). `diagnostics
structural` and `diagnostics execution` then each ran under the 420-second deadline, locally
and as jobs of the diagnostics workflow, where the slowest hosted `structural` run observed
(2026-10-02) took 413 s; the workflow now runs each partition as two shards, a job each.
Observed on 2026-10-01 on a 14-core machine that other
builds kept at a load average of 10 to 13, `structural` passed in 96 s and `execution` in 90 s
(102 s and 94 s for the whole `verify.sh` invocation). These are observations of two runs, not
a bound: the deadline itself is what refuses a slower run. The `structural` run predates that
partition's frozen-artifact and library-cycle controls (the admission reuse rows of the table
above); with them, one run the same day on that machine, at a load average of 7 to 11, passed
in 85 s.

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
  messages and the underlying IO reason, which the caller supplies as the runtime's own message
  for a read that fails the same way (`readFailure`: an absent file, or a directory in a file's
  place) instead of a copied operating-system text. That read is of another path than the
  checker's; that the first line of the `IO.Error` text does not depend on the path is trusted
  runtime behavior, which `checked_documentation` does not cover: it quantifies over arbitrary
  reason strings.
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
IO. Scratch directories live under the project's `.lake/regula-scratch/` and are removed on normal
or exceptional return; a killed run's directory is reclaimed by the next scratch user once no live
process holds the scratch lock (`Regula.Scratch`).
Helpers invoke external programs with argument arrays, never generated shell programs. The
operator's narrow shell exceptions are recorded in [`AGENTS.md`](../../AGENTS.md).
