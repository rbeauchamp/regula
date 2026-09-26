# Policy acceptance and implementation linkage

The POLICY-01 design is implemented by the pure `RegulaPolicy` contracts and
operational adapters described below. The [domain guide](policy-domain.md) identifies
admitted data; the [proof guide](policy-proofs.md) gives theorem hypotheses and caller
linkage. The [architecture](linter-architecture.md) owns the product and the
[coverage map](rule-coverage.md) owns the twenty-one rules and nine residual accounts.
Normative meaning remains [chapter 8](../standard/8-tooling-and-machine-audit.md)
and the [chapter 9 checklist](../standard/9-compliance-audit.md).

Con-leche and its authors/contributors, maintained by Joachim Breitner at Lean FRO,
are credited for [complete indexed result assembly][installed] and
[canonical representations with semantic equality][propwhen]. These are design
influences, not imported proofs or copied code. The Regula guarantee
is conditional on observations; it is not con-leche's kernel/model theorem.

## 1. Observed call flow and every success boundary

Paths below start at `lean/Regula/`. This source inventory covers actual audit
successes and the intentional non-audit routes. It is not a proof that external
acquisition or the compiled executable is correct. `Checker/Acceptance` is now the
operational bridge, re-exporting the pure API without duplicating policy decisions.

| Invocation / success owner | Required evidence and external boundary |
| --- | --- |
| `AxiomGate.auditSurfaceAt`: fresh project | `Acceptance.freeze` reconciles coordinator-selected Lake modules, source/configuration/dependency state, completed report/replay inventories and origins. `Acceptance.finish` times collection and acceptance separately, carrying checked equality of every outcome to `finalize` through `finalize_collection_error` and `finalize_of_collected`; success text and `ResultProtocol.writeAccepted` consume its `AcceptedRun.report` through the report account `Account.account`. Fresh isolated source build and all existing warning, ownership, exclusion, source and replay guards remain. |
| Same function: `--incremental`, `--build-lint` | The same full policy plan uses `incrementalProject`; cached Lake build artifacts do not cache policy decisions. Build-lint has no second exit-code-only PASS branch. |
| `Lint.run` (`lint`, the `lake lint` driver) | Calls the same `AxiomGate.entry` project audit (`--incremental`, or fresh with `--fresh`). Exit 0 only through the claimed `Lint.classify` (`checkedClassify`): `accepted_sound` requires a zero audit exit and a recorded `Status.completed` account of the requested mode, hence an `AcceptedRun` with `CompleteFor ∧ AllPolicyOK`. The success line is that account's `Account.pass`. Exit codes 1, 2 and 3 classify recorded rejected, configuration-only and incomplete statuses; a missing or disagreeing status is 3. That the recorded observation is this invocation's audit is checked by inspection. No second PASS branch. |
| `Lint.run`: `--explain-config`, `--help` | Read-only manifest/Lake-scope validation with the audit's own functions (`Manifest.load`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`), and help; no audit certificate. Both return the non-success configuration class (exit 2), refuse `--json-out`/`--verbose`, and invalidate any recognisable `--json-out` destination first (`AxiomGate.invalidateResults`). An error escaping `Lint.run` is exit 3, or 2 for a `manifest-` refusal, never 0 or 1. |
| `AxiomGate.auditSurface`: `--with-docs` | One process: `auditSurfaceAt` accepts the project plan over a snapshot that includes the copied Markdown, then `auditBuiltProject` accepts the documentation plan over that same snapshot and build, and `combineAccepted` joins them. No evidence crosses a process boundary between the two stages. `CombinedAccepted` is required before combined success. |
| `AxiomGate.auditSurface`: `--acceptance-link PATH` | Fresh project success only (no `--with-docs`). After `AcceptedRun`, computes the SHA-256 of the copy-relative accepted sources, configuration, dependency captures and `docs/` Markdown; records it in PATH only after `run`'s outer configuration recheck passed with exit code 0. The path is invalidated before the audit starts, so any refusal leaves it `incomplete`. |
| `DocFenceAudit.run`: `--acceptance-link PATH` | Before building, computes the same identity from its own fresh captures and refuses unless PATH records an accepted ordinary result with an equal identity. Equality establishes identical captured inputs; `shasum` and the filesystem remain trusted. |
| `AxiomGate.auditFile`: explicit conforming profile | Actual compilation and full source/replay/execution observations yield a `freshFile` plan and `AcceptedRun`. `FileSourceBinding` retains both the requested URI and the temporary compiled URI with exact byte equality. Producer/transcript paths are not rewritten. Dependencies remain incremental; this is no whole-project claim. |
| Same function: no profile / compiler-trusting | `CLASSIFIED`, with no conforming `Claim` or accepted-positive receipt. Teaching does not supply logical conformance. |
| `Documentation.auditBuiltProject` and `DocFenceAudit.run` | Freeze all Markdown bytes, original fence spans and task identities before compiling. A corpus with a structural problem has no request plan: it reports each located problem and is refused. Group observations retain every unit and authenticate roles against the whole reconciled inventory; policy selection is per original fence. `finishDocuments` calls `finalize`; zero-fence documents still need discovery/build/scan jobs. Terminal inventory/source/configuration/dependency checks remain. |
| `RuleExamples.documentation` | Retains the documentation driver's dependent accepted package. Canonical positive completion additionally requires a nonempty all-positive fence inventory; negative/teaching expectations remain classified. The adapter verifies the original requested documents before emitting accepted metadata. |
| `RuleExamples.inspectNegative`, `RuleExampleQualification`, `Website` | Diagnostic production and exact source/configuration/mode/registry/location qualification retain their separate proof-bearing example APIs. A rejected policy example or an INCOMPLETE diagnostic demonstration is not an audit-success certificate. The four example kinds remain distinct; demonstrations discharge none of them. |
| `FreshChecker.run` | Separate `serializedGraph` claim. `GraphPlanOK` freezes selected roots and supplied import coverage before checker processes; `finishGraph` finalizes actual checked roots against that inventory. External `leanchecker` success remains an observed process result, not a kernel proof of its semantics. |
| `FreshChecker --plan-only`; all help branches | Planning/help completion only, explicitly no audit certificate. |
| `AxiomGate.run`: `--declaration-report-worker`, `--frontend-worker`, `--replacement-history-worker`, `--compile-batch-worker`, `--inspection-group-worker`, `--diagnostic-worker` | Completed raw production only. Strict request/schema/producer/source binding, indexed collection and joins remain. No decoder constructs `Accepted`. |
| Native editor hooks, registry export/validation, site validation, selftests and qualifiers | Existing local observations or scoped diagnostics; no fresh/incremental whole-project certificate. Editor snapshot results are not promoted to global acceptance. |
| `scripts/verify.sh`, `scripts/verify.sh docs` | Ordinary: fixed public `axiomGate --acceptance-link tmp/acceptance-link.json` follows builds and other required checks. Docs: `docFenceAudit --acceptance-link tmp/acceptance-link.json`, every `docs/` fence. The shell's zero exit records completed execution of those commands, not a separate Lean proof. Each keeps its own hard 420-second deadline; cold-root acceptance stays in the ordinary run. |

Source capture retains each prefix for failure reporting; a prefix is not a completed
inventory. Terminal source/configuration guards remain separate.
Its evidence destination is initialized as a new incomplete attempt before timeout
discovery/spawn and binary/setup reads. The timed child carries that same attempt.
Raw result/trace sidecars and their partial-file locations are retained before parsing;
completed case commands retain both executable and argv. The receipt retains obtained
records on failure, and becomes completed only after every case
and restoration. A killed process cannot promote the current incomplete receipt. Graph
invocations likewise invalidate recognizable absolute result destinations before argument
parsing or root discovery, and relative destinations once their project root is resolved.

Dependency snapshots use Lake's buildable library domains and existing executable roots to retain
module identities, canonical source paths and exact bytes independently of Git ignore
rules. Unused dependency executables need not ship source files; root-package targets
remain required, and terminal rediscovery detects executable source additions/removals.
Library roots whose globs admit their submodules include those submodules even
when the configured target array selects only the root. Nominal Git revision is observed
once per dependency root; dirty status is decided only for the declared inputs, by
membership in one unrestricted porcelain status of that root (an ignored or untracked
directory entry covers every declared input beneath it, and a rename covers both its
paths); the status output itself is not retained. Configuration paths come from Lake's
actual package configuration/manifest plus toolchain and default-config presence checks.
No Git diff, untracked-file content list or directory-wide bytes are retained; unrelated
files and build outputs are not inputs merely because they share a dependency directory. Terminal checks rediscover the Lake domain and reread
these same inputs, refusing newly added or removed sources; filesystem acquisition and change-and-restore races remain trusted
boundaries. No whole-workspace file scan substitutes for this Lake source inventory.

The dirty decision replaces a literal-pathspec status over the declared inputs, whose
cost grew with the pathspec count (about 1.5 s per Mathlib capture inside the checker),
with one unrestricted `git status --porcelain=v1 -z --untracked-files=all
--ignored=matching` of the root and the pure `Snapshot.dirtyOf` decision. `dirtyOf` is
proved to hold exactly when some reported path, or a rename's original path, equals a
declared root-relative input or is a directory above it (`dirtyOf_iff`), and to equal
non-emptiness of the entries so restricted (`dirtyOf_eq_restricted`). Declared inputs
are spelled as Git spells a literal pathspec from the canonical root: the leading
directory that is the root, lexically or by `realPath`, is removed and the rest is kept
literally; an input outside the root refuses, as the pathspec status did. That this
restriction models Git's pathspec-limited output is trusted Git behavior, not a theorem:

- G1. Directory collapsing precedes pathspec filtering. An ignored directory without
  tracked files is reported as `dir/` even for a file pathspec beneath it; a directory
  containing tracked files is descended, so a clean tracked file there is reported by
  neither status.
- G2. A rename on either side is reported as `XY new` followed by its original path;
  with only the original declared, the pathspec status reports it as deleted.
- G3. With `--untracked-files=all`, untracked directories are listed per file, except an
  untracked nested repository, which the unrestricted status reports as `dir/` and the
  pathspec status omits.
- G4. A modified submodule, including one with only untracked content, is reported by
  the unrestricted status as its gitlink path `sub`; a pathspec beneath it such as
  `sub/x.lean` does not descend into the submodule, so the pathspec status omits it.

Under G1 and G2 both decisions agree. Under G3 a declared input inside an untracked
nested repository, and under G4 a declared input inside a modified submodule, is now
dirty where the pathspec status called it clean. Neither input's bytes are part of the
dependency's own revision, so the change only makes the reported bit conservative.
Outside these two cases, request and report bytes are unchanged, on the trusted premise
that Git reports a path with the same case and Unicode form as the declared input.
Membership compares bytes exactly. With Git 2.54 and `core.ignorecase`, literal
pathspecs also matched tracked paths and final components byte for byte; the one
observed divergence is an input under an untracked directory whose leading components
differ from the on-disk spelling only by case on a case-insensitive filesystem. The
pathspec status reported it dirty in the input's spelling, while the unrestricted status
spells the on-disk path, so it now reads clean. This affects only the reported dirty
bit, never the captured bytes. Fields that are not UTF-8 are dropped: they cannot equal
a declared input, and no `dir/` prefix of a UTF-8 input contains them.
`lake exe qualify acceptance-snapshots git-status` checks G1-G3 against the retired pathspec decision.

Only the Git status cost changes. Every declared input's bytes are still read and
UTF-8-decoded, and the terminal recheck still recaptures them. Both are retained on
purpose: the exact bytes carry per-source attribution in the request, and the recheck
carries run freshness. Removing dependency bytes from the request is a separate contract
decision that this change does not make.

Standalone documentation and rule-example documentation callers capture dependencies
before their prerequisite build and pass that observation into `auditBuiltProject`.
The combined project/documentation route passes its existing pre-build observation
alongside its shared snapshot. The documentation adapter performs no replacement
capture; it rechecks the supplied dependency observation before finalization.

Project census construction retains failures until the existing policy diagnostic pass
has completed. Unavailable history still prevents acceptance, while its producer-linked
execution findings retain RG3001, `execution-unresolved` and root locations in fresh,
incremental and build-lint modes. A stored census error is raised if no typed policy
failure already refuses the run; it is never replaced by an empty census.

The focused `lake exe qualify acceptance-snapshots all` diagnostic exercises ignored
Git-backed dependency source/configuration mutations with restoration, and the RG3001
project control through fresh, incremental and build-lint invocations. It checks typed
root/source attribution and absence of acceptance on unavailable history. Its
`git-status` group compares the dirty decision with the retired pathspec status for a
clean root, unrelated ignored/untracked/NUL-framed siblings, inputs under an ignored
directory with tracked files, a collapsed ignored directory and an untracked directory,
staged and worktree renames, a deleted input, an untracked nested repository, a
symlinked root spelling, a relative input and an input outside the root. These are
scoped operational controls, not a proof of IO extraction or a full acceptance run.

`Common.mapWorkQueue`, `admitIndexedWorkerResults` and documentation's task collector
execute `ResultState.collect`; no result slot is overwritten. All three call
`checkedIndexedResults`: success returns exactly the array whose indexed pairs are a
permutation of the responses over every requested slot, each payload bound to its slot. Group reconciliation
preserves each requested environment separately and never deduplicates job
responses, replay occurrences or positive owned declarations. The full admission module/required/admitted
inventories survive the infrastructure partition.

### Environment-indexed project census

The original project `Claim` remains the index of `AcceptedRun` and of the project
component of `CombinedAccepted`. `Census.requests` is the coordinator's ordered
environment request array; each request contains its snapshot, ordinal and exact
positive module assignment. `CensusOK` requires the returned environment requests
to equal that array, its ordinals to match their positions, and its positive module
partition to equal the full original claim. Target discovery and classification
remain global, including excluded and unclassified imports.

Each `EnvironmentCensus` retains its complete admitted policy inventory, transcripts,
execution roots, replay arrays, sources and origins. `InventoryValid` still requires
bare-name uniqueness within each Lean environment. Distinct environments may contain
different declarations named `main`; concatenating their inventories is not a Lean
environment. No entrypoint is renamed, filtered or exempted.

Configuration, discovery and build jobs occur once. Local jobs carry an
`EnvironmentKey` and local subject; admission, declaration policy, execution,
transcript, history, origin and documentation-presence observations resolve only
inside that environment. `CensusRoles` supplies roles indexed by that same inventory.
`freezeEnvironment` retains the role receipt computed by `Policy.admitScope`;
`frozenEnvironmentRoles` selects it at the exact environment index.
`Roles.eq_authorize` and `frozenEnvironmentRoles_eq` prove exact equality to
recomputation, including both ordered role arrays. This avoids repeated role
authorization per job without caching an acceptance verdict or trusting a worker flag.
All execution requests for a root come from registrations in its bound environment.
The existing collector and `finalize` still require exact input occurrence coverage
and every policy obligation. File and graph paths use one environment; document
plans use no project environment and retain their exact fence inventory and modes.

The current executed guarantee uses this full census, environment-local roles/jobs,
actual result collection and `finalize_iff`, including checked equality for split
collection/finalization. Conditional legacy transfer lemmas are not used by the
acceptance path. Their coherence hypotheses have not been instantiated to establish
operational equivalence with the former flattened IO collector; no such equivalence
is claimed. The private `finishDocuments` helper consumes unchanged `auditTasks`
output, whose collector has already refused unknown, duplicate and missing task
occurrences. The helper alone is not an arbitrary raw-occurrence admission API.

This establishes relations among supplied observations. Lean/Lake extraction,
compiler admission, source reads, process completion, and compiled execution retain
their existing trusted boundaries.

`InfrastructureOrigin` is limited to exact reporter, codec and conditional collector
identities. The IO adapter compares canonical actual artifacts with the running
checker's artifacts; `InfrastructureOK` binds receipts, disjoint ownership and all
observed incoming imports. Public Contract/Diagnostic/StructuralName interfaces do
not imply a whole-library exemption. Ordinary excluded imports remain forbidden.

The pure `Accepted`, `Finalized`, `AcceptedRun` and `CombinedAccepted` constructors
require their stated proofs. Operational raw records, `AcceptedReport`, renderer
strings and generic diagnostic JSON remain data APIs; they do not authorize success.
The success owners above consume the dependent package, and typed
`ResultProtocol.writeAccepted` cannot take a raw report. Constructor visibility is
an ergonomic boundary, not hostile in-process unforgeability. `acceptance` JSON is
rendered metadata only: a parent decodes raw production and recomputes evidence.

Every checker verdict line and every `completed` status is rendered from one report account,
`Account.account run` in claimed `RegulaCore.Account`. `Account` is the subtype of
account data that is the projection of some `AcceptedRun`, and `Status.completed`
takes an `Account`; the refusal statuses carry none. `Status.completed_accepted`
therefore proves that a `completed` status has an accepted run, complete for its plan
and meeting every stage policy, behind it. That this run is the current request's is each
caller's binding, checked by inspection, and a completed envelope takes its `mode` from the
account. `AccountContract` (`checkedAccount`) states
the account's meaning: mode, scope, surfaces, toolchain and job count are the run's
own; coverage is `coverageOf` the claim's mode, so fresh whole-project exactly for a fresh
project claim (`coverage_fresh_iff`); the listed
`ExecutableContract` registrations are exactly the accepted inventory's; execution
counts are `executionSummary` of each accepted environment; the fence counts partition
the accepted fences by expectation; and the residual identifiers stay unresolved. The
human lines (`Account.lines`, `Account.pass`) and `acceptance.account` JSON render its
fields; they are unproved adapter text. Project, file, build-lint, combined and graph verdict
lines use `Account.pass` by inspection of the call sites; the documentation audit prints no
PASS verdict, and its per-fence labels come from task results once an `AcceptedRun` exists.

### Frozen input coverage at operational entry points

Each row concerns the effective workspace actually consumed. Fresh project audits own
an isolated copy; incremental/file/graph modes consume their selected workspace.
`Lake.surfaceInventory` fixes target/module/source identities, with canonical source
paths; `SourceBinding.capture` fixes root bytes. `Snapshot.inputsUnchanged` rediscovers
root targets/modules/paths and dependencies even when the dependency array is empty.
It compares against the original records; it never replaces the accepted request.
Configuration observations retain presence and exact bytes for the selected manifest,
Lake configuration, lock and toolchain. These checks are IO observations, not filesystem
or compiler proofs; changes restored between observations remain outside the guarantee.

| Entry point / claim | Frozen before consuming build/import/replay | Carried to success | Terminal inventory and byte checks |
| --- | --- | --- | --- |
| `AxiomGate.auditSurfaceAt`, fresh/incremental/build-lint | Lake root inventory, root bytes, configuration, dependency source/configuration (one capture); copied docs when combined | Existing inventory/source/configuration/dependency records and raw inspections feed the same claim and frozen census | `SourceBinding` checks bytes/configuration; one terminal `Snapshot.inputsUnchanged` checks root and dependency inventories/canonical paths/bytes before `Acceptance.finish` (combined: after documentation, below). |
| `AxiomGate.auditSurface --with-docs` | The project stage freezes copied root inventory/bytes/configuration, dependency inputs and complete copied Markdown | `auditBuiltProject` receives the same inventory, sources, configuration, dependencies, documents, build and snapshot in process | Documentation inventory/bytes before document finalization; the run's one terminal dependency recheck after the fences, before combined success |
| `DocFenceAudit.run` | Original requested Markdown inventory/bytes before the prerequisite build; copied root/configuration/dependencies before that build | Required `documents` and `dependencies` arguments plus existing inventory/source/configuration/build records | `checkMarkdown` compares inventory/bytes before fence work and before `finishDocuments`; root/dependency and source/configuration checks remain |
| `RuleExamples.documentation` | Original Markdown inventory/bytes before copying/building; copied root/configuration/dependencies before build | Same required documentation arguments; original requested documents also retained for result binding | Same adapter checks; original Markdown inventory/bytes rechecked before emitting the bound result |
| `AxiomGate.auditFile`, accepted fresh-file claim | Selected file bytes, root inventory/bytes/configuration and dependencies before prerequisite build and temporary compilation | Existing source bindings and dependency observations feed file claim/finalizer | Root/dependency inventory and bytes plus selected/root file/configuration checks before acceptance; no project-wide documentation claim |
| `FreshChecker.run`, optional serialized-graph claim | Root inventory/bytes/configuration and dependencies before build/checker processes | Existing frozen graph plan and snapshot | Same root/dependency inventory and root/configuration byte checks before `finishGraph`; plan-only has no certificate |
| `ruleExamples --injected-git-facts FACTS [axiomGate] ARGS`, internal corpus-producer entry only | The same frozen inputs as the wrapped row above, except that for a dependency whose exact capture request (package, canonical root, ordered source and configuration paths) matches an entry in FACTS, the Git revision and dirty bit come from the corpus runner's single capture instead of this process. Every source and configuration byte is still read here. | Same carried records as the wrapped row | Same terminal checks, except that an injected dependency is rechecked once per campaign by the runner instead: it captures once, requires equal content identity of the shared trees before any producer and after all are joined, and reruns `Snapshot.inputsUnchanged` on that capture at run end. Results carry `"gitFacts": "injected"`. User-facing `axiomGate` rejects the flag. |
| SourceAudit workers, `Documentation.auditTasks`, policy-negative examples, help, native editor | Parent requests / mode-local observations | Raw completion, diagnostic classification or explicitly partial editor observations | No standalone whole-audit success claim; acceptance-owning parents above retain the relevant input checks |

Zero declarations or executable roots do not skip root input reconciliation. Projects
still require a nonempty library surface. No Markdown files is a refusal; Markdown with
zero fences can be accepted only after its inventory/bytes and scan/build evidence are
checked. Negative and teaching fences retain their existing classified meanings and
cannot stand in for conforming positive evidence.

## 2. Claim, identity and completeness

### Claim domain

`Claim` contains `Scope`, positive profile assignments, execution assignments,
`EvidenceMode`, requested stages, source/configuration snapshot and supported
toolchain/dependency identity. A project may assign different profiles to different
surfaces: do not collapse its manifest to one maximum profile. `ConformingProfile`
has exactly Kernel-only, Choice-Free, Standard-Logical. Separate `InspectionRequest`
constructors cover no-profile classification and compiler-trusting teaching inspection;
neither constructs a conforming claim.

`EvidenceMode` retains architecture spellings `editorSnapshot`, `incrementalProject`,
`freshProject`, `documentationExample`, `serializedGraph` and adds **`freshFile`**.
`Scope` distinguishes project, file, documentation set and editor module snapshot.
A fresh single-file audit retains its own mandatory stages, scope, mode and renderer.
Registry/result schema1 already includes `freshFile`.
Unsupported scope/mode/stage combinations are rejected by `admitClaim`, not coerced.

Project policy, documentation results and semantic review are separate components.
A completed mechanically accepted project report keeps R-INTENT, R-INVARIANT,
R-LAWS, R-BOUNDARY, R-NONVACUITY, R-DOC, R-COST and R-QUALIFY explicitly unresolved
where applicable; it is not full standard conformance. R-GRAPH is requested separately.
The report account (`RegulaCore.Account`, below) renders exactly this: every
accepted account lists these identifiers as unresolved, adding R-GRAPH only for a
`serializedGraph` claim. An identifier is an open obligation, not a completed review.
Editor mode admits only its declared completed snapshot checks and lists pending
stages. It has no conversion to fresh/incremental project acceptance.

### Keys and collection meaning

Use Lean `Name` structurally, not `toString`/`String.toName` round trips. Encode the
anonymous/str/num constructor tree reversibly, with tagged components and natural
numbers; anonymous is allowed as a prefix, refused as a module/declaration identity.
Empty string components are preserved for declaration names (Lean can construct them),
not trimmed or conflated with anonymous. Source identities retain exact snapshot bytes
and logical URI; a digest may index storage but digest equality alone is not byte equality.
Dependency Git pins do not prove an unmodified checkout: record actual dirty/path state
as an IO observation. Full filesystem/process authenticity is outside the pure theorem.

| Key | Equality / multiplicity |
| --- | --- |
| Module | Snapshot identity + exact module `Name`; source mapping must be functional. Same module in two claimed surfaces is refused as ambiguous ownership, even with equal profiles. Excluded/excluded overlap may be deduplicated only for the module inventory; target classifications remain distinct. |
| Declaration | Requested environment + snapshot + owning module + exact constant `Name`; one record within that environment. Equal names across independent environments remain distinct. |
| Executable root | Requested environment + snapshot + root module/name. Multiple valid registrations within that environment share closure work but each registration remains a required declaration/contract obligation. |
| Boundary | Root key + reached declaration + kind + optional replacement target + evidence occurrence. Multiple candidates/history observations are legitimate; preserve their distinct occurrence identities. |
| Fence | Document snapshot + opening/body/closing byte spans + marker kind and expected pattern. Synthesized `DocFence_N` names are temporary transport names, never permanent identity. |
| Job | Claim identity + stage tag + exact subject key, including the requested environment for local stages; group transport contains individual job keys. Attempts are transport metadata, not new required jobs. |

Required-key sets use canonical duplicate-free sorted collections backed by existing
Std ordered structures, with proved lookup/membership laws. The semantic specification
uses finite membership and unique lookup, independent of storage order. Serialization
sorts by structural keys; work order is separately retained for deterministic diagnostics.
Transcript evaluator chains and mutual-group sequences are **ordered**, not sets.
Axiom lists, module sets and closure edges have set semantics; canonicalization preserves
membership. Duplicate observations for one job are rejected even when payloads match;
retries must discard the prior attempt before admitting a single completed result.
Malformed names/tags/schema, unknown jobs, extra results, contradictory observations,
stale snapshots and unmatched source ranges fail admission. Never overwrite a filled slot.

A project requires at least one claimed nonempty library; retain the baseline refusal
of empty discovered libraries, even exclusions. A real module with zero declarations,
a valid source file with zero declarations, an empty execution-root set, and Markdown
with no Lean fences are allowed **only after their discovery/build/scan jobs complete**.
An empty worker response cannot substitute for an empty authoritative census.

### Independent census and fixed plan

Collection proceeds in explicit phases. (1) Freeze Lake targets, sources, manifest and
Markdown domain. (2) Complete the mode's build/import/admission stages and obtain a census
of owned declaration keys, registered/ordinary roots, and required source/transcript jobs
from the completed environment and source scan. (3) Freeze the required policy jobs before
collecting their results. Closure discovery retains the complete reached-node/edge census
and explicit unresolved paths; a missing closure does not yield an empty boundary set.

Census and policy observations may be extracted in the same process, but the census is
created by traversal before filtering or mapping policy outcomes. It is never computed
from returned successful results. A discovery worker itself has a predeclared required
job; missing/crashed discovery prevents plan finalization. A group worker sends its
census and keyed observations separately and the coordinator reconciles both against
its already requested modules/jobs. That comparison does not independently prove that
the census equals Lean's environment: the extraction linkage is an explicit IO/Lean
boundary, with qualification and source review. No count or hash closes that boundary.

## 3. Independent predicates and executable APIs

The following is mathematical interface notation, **not compiling Lean**. `c` is an
admitted claim, `i` a frozen inventory, `r` the raw keyed result table. `payload(r,k)`
is defined only at its unique completed entry. All quantifiers range over these exact
values; no predicate below is defined as “the checker returned true.”

```text
PlanOK(c,i) := exact configured target partition and source identities
             ∧ mode/stage compatibility ∧ unique subject/job identities
             ∧ required jobs derived from the independent census
CompleteFor(c,i,r) := PlanOK(c,i)
             ∧ keys(r) = requiredJobs(c,i)
             ∧ each key has exactly one terminal completed result
             ∧ every payload binds to c, i, its subject and requested stage
PolicyOK(c,i,k,o) := the applicable conjuncts in the table below
AllPolicyOK(c,i,r) := ∀ k ∈ requiredJobs(c,i), PolicyOK(c,i,k,payload(r,k))
Accepted(c,i,r) := { report with exact c,i,r projections
                  // CompleteFor(c,i,r) ∧ AllPolicyOK(c,i,r) }
accept(c,i,r) : Except AcceptanceFailure (Accepted(c,i,r))
accept_sound : accept(c,i,r) = ok a → CompleteFor(c,i,r) ∧ AllPolicyOK(c,i,r)
accept_complete : CompleteFor(c,i,r) ∧ AllPolicyOK(c,i,r)
                  → ∃ a, accept(c,i,r) = ok a
insertResult(c,i,s,k,o) : Except AdmissionFailure (ResultState(c,i))
```

`ResultState` carries unique keys, a subset of the fixed plan and valid payload bindings;
empty construction and every insertion preserve that invariant. No unchecked mutation
or generic raw JSON constructor returns this state. Failure preserves the prior state;
completion cannot discard an error, unknown or pending slot. `accept_complete` concerns
the fully supported finite data domain, **not** completeness of elaboration, theorem
search, source discovery or detection of arbitrary intended specifications.

| Predicate / normative requirement | Meaning independent of decision code | Actual adapter to change |
| --- | --- | --- |
| `ScopeOK` (§8.1–8.4) | Exact classified targets/modules, required ownership/source/origin bindings; no excluded imports or unattributed requested declarations. | Lake/Manifest → `auditSurfaceAt`; file and grouped inspection admission. |
| `AdmissionOK` (§8.3) | Completed logical admission receipt matches owned dependency census and snapshot; no skipped replay, unsupported admission or emitted warning for a positive fresh claim. | `Environment`/`Admission`, build/compiler receipts. Receipt truth beyond its decoded contents is an explicit operational assumption. |
| `FoundationOK` (§8.5) | No owned logical axiom; no `sorryAx`, unknown or compiler axiom; each exact axiom member belongs to the surface's permitted set. | Typed replacement of `reasonFor`, `labelOf`. Teaching native evidence is a separate result predicate. |
| `SafetyOK` (§8.4) | No unsafe/partial flag unless the exact supported recursive-helper relation holds; helper is not logical proof evidence. | Shared role validator and declaration decision. |
| `ContractOK` (§8.5, §8.12) | Every registered obligation targets the exact supported implementation/predicate, with completed admission and no recorded contract failure. Registration adequacy remains review. | `Probe.executableContract?` → domain adapter; no weakened predicate synthesized in policy. |
| `ExecutionOK` (§8.6) | Every required root's closure is accounted for, no unresolved paths/states; report mode permits reported trusted boundaries, checked mode permits only checked evidence or authenticated native-runtime substrate. | `executionWalk`/origin/correspondence adapters → pure execution decision. |
| `DocumentOK` (§8.7) | Complete structural scan; positives warning-free with logical admission/Standard-Logical policy; negative source rejection has one effective-error match; trusted teaching has compiler evidence and is not positive conformance. | `Documentation.auditTasks` and final aggregation. Execution is not implied. |
| `DocumentationPresenceOK`, `MaterialDocumentationOK` (§5.1–§5.3; RG5001–RG5003) | Every claimed completed module has module-doc metadata; each public declaration explicitly registered as material-claim evidence has a docstring carrying a nonempty labelled Intent section (`materialDocumentationFailure_eq_none_iff` links the executed classification). Registration completeness and prose fidelity remain R-DOC; intent adequacy remains R-INTENT. | #13 collects module-doc metadata and `findDocString?` for the independently frozen module/registration census; #7 requires those jobs for project and applicable completed-editor scope. |
| `ExampleExpectationOK` (website checked examples) | Exactly the configured positive, compiler-rejection, policy-diagnostic or trusted-teaching expectation holds for the exact source snapshot; see below. | #12 typed expectations → #13 checker → #15 example aggregation; same #7 keyed acceptance contract. |
| `StageOK` (§8.2–8.3, §8.8–8.12) | Required producers completed for this exact mode; absence, crash, unknown or unsupported state is incomplete. | All worker returns and audit/render/exit adapters in §1. Optional graph stages only when requested. |

Mandatory stages are derived by `requiredJobs` from scope/mode and the fixed rule
applicability predicates, never a caller-selected subset for a whole-project claim.
Fresh project requires configuration/discovery, fresh warning-free build, logical
admission, every owned declaration's policy, all execution roots/closures, required
transcripts/history/origins, and documentation-presence jobs. Incremental project has
the same policy obligations with incremental build evidence. FreshFile requires its
fresh warning-free unit compilation/admission, declaration policy and execution closure;
it does not acquire whole-project or documentation-presence coverage. Ordinary fences
retain §8.7's narrower logical-only contract. Editor completion lists its completed
applicable checks and pending stages; module-doc presence waits for module completion,
and registered-public-declaration presence waits for that declaration and its registration.
Serialized graph requires every selected graph root checked, never mere planning.

For website fixtures, `ExampleExpectation` is a tagged sum: positive acceptance;
compiler rejection with a nonempty effective-error pattern; policy rejection with a
nonempty typed expected-diagnostic specification; or authenticated trusted teaching.
A policy-negative source may elaborate successfully (for example RG1001). Its job
requires completed real checker rejection for the exact source/configuration/mode,
an exact match to expected stable rule ID, subreason where specified, and the expected
primary/related source ranges or explicit module/project location. Reject additional
unexpected diagnostics unless the typed expectation explicitly lists them. #12 owns
the only RuleId vocabulary and validates expectation IDs; the core compares transported
stable identity values supplied by that adapter, not a second registry. A pure equality
check on those values does not prove the adapter's ID mapping. Compiler crashes, wrong
source, missing locations, malformed output or incomplete checks satisfy neither negative
variant. These outcomes construct accepted **example expectations**, never conforming
positive program evidence. Docs aggregation fixes the kind of each expected job before
execution, and keeps negative/trusted counts separate from positives.

Unavailable-analysis rules also have separately labelled **diagnostic demonstrations**:
completed authentic production with exact source/configuration/mode, registry ID, reason and
primary/related locations, while the audit result remains INCOMPLETE. These are outside the
four accepted-example kinds and cannot discharge `ExampleExpectationOK`, positive conformance,
or an accepted rejection. Crashes, stale sources, cancellation, missing responses and unrelated
failures do not qualify. Each correction requires its applicable completed positive checks.
The [source-owned corpus contract](rule-examples.md) records concrete page inputs and limits.

Each predicate must be elaborated as a declarative relation over data, with named
components corresponding to these requirements; its decision function is proved sound
and complete against it. Data-level evidence can be constructed with proof fields by
any Lean client that supplies the proof. Private constructors are an ergonomic boundary,
not a claim of adversarial in-process unforgeability. Operational receipt constructors
stay in the trusted adapter; the pure theorem explicitly assumes their interpretation.

## 4. Domain and role proofs

`DeclarationKind` covers all eight `ConstantInfo` variants. `BoundaryKind` covers the
eight §8.6 kinds and `Correspondence` has checked/trusted/unresolved, with evidence
indexed by kind. Use a separate six-way `FoundationClass`: the three logical labels,
hole, unknown-axiom, compiler-trusting. Parse failures are errors, never a new permitted
constructor. `ConformingProfile` cannot contain compiler-trusting. Codecs prove
`decode(encode x) = ok x`; accepted canonical external spellings re-encode identically.
Legacy pretty names are display only; do not promise reversible identity for them.

For axiom set A, define K = ∅, C = {propext, Quot.sound},
S = C ∪ {Classical.choice}. Logical classification returns the least of K ⊆ C ⊆ S
containing A. Prove containment and minimality for every A ⊆ S, not by enumerating
sample programs. Empty A is Kernel-only; duplicate/order changes do not alter the label.
For other A retain diagnostic precedence: hole, then unknown, then compiler-trusting.
Declaration refusal precedence stays: owned axiom (authorized teaching exception only),
hole, unknown, escape hatch, compiler trust, executable-contract failure, profile excess.
Malformed input is refused **before** policy precedence. Execution reports every
unresolved path; deterministic rendering follows frozen plan order, not worker timing.

`RecursiveHelperOK(decls,transcripts,h)` is the conjunction of **all** guards currently
in `authorizedUnsafeRecHelpers`: same-module def/base linkage; range-less internal partial
opaque-hinted safe helper with no extern/replacement; structural/well-founded whole-value
and generated-equation exactness and defeq observations; equation axiom bound; safe regular
recursive base, identical type/universes; helper axiom subset; nonempty mutual group and
exact ordered helper-name transform, self-reference; unique same introducing command,
exact literal/nested binder attribution, pinned evaluators and complete introduced group.
Do not collapse exactness and definitional comparison, or set-normalize ordered groups.

`NativeTeachingOK(decls,transcripts,a)` retains **all** guards in
`authorizedNativeAxioms`: internal safe proposition axiom, exact Boolean shape and successful
replay, permitted dependency set; same-module safe proposition parent of supported kind,
exact parent-use shape, unique direct user; nested exact ranges; unique introducing command
shared with parent; literal declaration, pinned complete evaluator chain and one native
range. Names only locate candidates. This evidence only permits teaching classification;
it never relaxes a conforming profile.

Freeze these relations as independently written component predicates, then prove the
**executed** typed validators return evidence iff the relation holds on supported records.
Their input records include the actual data-level observations presently tested (including
exact-value/equation/replay flags). A proof about those flags does not prove they truthfully
represent an environment: `Probe`, fresh `Frontend`, canonical artifact checks and completed
kernel admission retain responsibility for that linkage. A free Bool/name array supplied
by a consumer is not an authenticated role. `Policy.reasonFor` must consume validated
role evidence bound to the whole declaration/transcript inventory, not caller whitelists.

## 5. Pure module boundary and migration

The root namespace and Lake library **`RegulaPolicy`** use the umbrella
`lean/RegulaPolicy.lean`. Imports are acyclic and remain within Init/Std, the pure
library and the import-free `Regula.Contract` registration type. Foundation and
role specifications support declaration decisions; Plan derives required jobs,
Observation defines stage predicates, and Acceptance assembles complete results. Codec defines a pure tagged wire tree.
JSON parsing/printing stays in `Checker/PolicyCodec.lean`; prove decoded-tree codec laws
in Codec and qualify the operational parser, including duplicate-field rejection.
A tree-codec theorem is not a theorem about JSON text parsing. No Environment, Meta,
Frontend, IO execution, native evaluation, partial/unsafe, Report, RuleDescriptor or
Mathlib import belongs in the pure policy library.

`Checker/PolicyDomain.lean` remains a compatibility import. `Checker/Acceptance.lean`
re-exports the pure definitions and assembles observations through them; it defines no
duplicate policy. The claimed `RegulaCore.Policy` holds the checker's pure claim,
scope-admission, rule and execution-rule projections, `RegulaCore.Coordinates` and
`RegulaCore.Source` the transcript-coordinate and source-range admission, and
`RegulaCore.Assembly` the pure census assembly; operational `Checker/Policy.lean`
only binds scope admission to the frontend coordinate check and renders text;
`Checker/PolicyCodec.lean` handles worker/report JSON. Move transcript **data** shapes
into the pure domain (including source/range/evaluator keys); `Frontend` imports them,
never vice versa. `Report` can serialize typed domain observations; pretty strings are
non-authoritative. Registry ID/payload/rendering stays owned by #12; it maps typed policy
failures to the existing twenty-one IDs and preserves subreasons. The pure core does not
import the registry, so no cycle forms when diagnostics import policy types. The claimed
`RegulaCore` library holds that registry (`RuleId`, `Rule`) and imports the policy
library, never the reverse; it shares this section's import restrictions except the
registry itself and Lean's pure `Lean.Data.Position` (`FileMap`), whose import closure has
no `Lean.Environment`, `Lean.Meta` or `Lean.Elab` module. It does not import
`Lean.Data.Lsp.Utf16`, whose closure contains `Lean.Environment`; the operational
`Regula.Diagnostic` supplies that UTF-16 column function.

The `lean_lib RegulaPolicy` has `.andSubmodules` discovery, a positive
Standard-Logical manifest entry as an initial upper bound, and explicit ordinary
acceptance build coverage. Report every declaration's **actual** least label and exact
axioms; reduce the upper bound only after checking the complete import/proof closure.
This root, like `RegulaCore`'s `.submodules` root, is separate from the excluded
`Regula` glob. The narrow operational infrastructure partition and its
authentication obligations are described in §1.
Audit, AuditApp/Main and the operational Regula exclusion remain. Teach tooling and
guides the new library via Lake discovery, not hardcoded declaration/file lists.

| Owner | Deliverable and gate |
| --- | --- |
| #5 POLICY-02 | Domain/codec admission and universal representation/codec/collection laws, typed roles/claims/records, canonical keys, invariant-preserving state API, compatibility adapters. Wire every policy caller to typed input; preserve detector behavior on supported baseline data, with explicit fail-closed extensions for malformed/duplicate data and positive file warnings. Record unavailable #6 theorems as pending, not proved. |
| #6 POLICY-03 | Remaining Specification/Decision/Acceptance theorems: least-label proof, decision iff predicates, exact role evidence, insertion/frame laws, accepted soundness/completeness and report identity. Check actual functions used by #5; no duplicate reference evaluator assumed equivalent. |
| #7 POLICY-04 | Freeze census/plan, validate all worker packets and every success boundary in §1, consume Accepted values in renderers/exit adapters, compose project+docs under one snapshot. Refuse empty/missing/duplicate/mismatched responses through public paths. Remove obsolete raw success APIs only after accounting for all callers. |
| #12 CATALOG | Keep one registry; add `freshFile`, share scope/status identities with core; accepted diagnostics export is read-only projection, never certificate input. |
| #13 ENGINE | Shared semantic collectors for current-document and imported modules; complete census/roots/role extraction and typed outcomes for all twenty initial rules (RG5003 was added later by #71); two scoped doc-presence checks retained. |
| #14 ADOPTION | All actual Lake lint/build/editor adapters consume the same outcome; cached policy re-evaluation and source-located links retained; freshFile and snapshot modes honestly labeled. Delivered: `lint` driver and exit classes, upstream-widget editor links, adopter fixtures in both lakefile formats. |
| #10 DELIVERY / #15 WEBSITE | Reconcile residual semantic accounts and same-revision rule/example/status exports. No accepted data report is full conformance; site consumes status, not exit code alone. |
| #8/#9 optional | Separate requested graph/export jobs and result type; absence cannot block core policy/site delivery. #8 ended in a [no-go](con-leche-research.md) and #9 is not planned, so no export format or adapter is selected. |

Native dependency refinements: #13 requires #5’s shared domain as well as #12;
#15 requires #7’s complete example-result boundary as well as #12/#13. Both edges
are acyclic and leave optional #8/#9 outside core prerequisites.

Manifest schema stays 2. Freeze new worker transport schema 1, independent of #12's
registry/result schema 1: schemaVersion, producer/toolchain identity, claim/snapshot,
job key, stage and raw payload; require exact keys, tags, types and supported versions.
All parent and worker executables must use that protocol together; reject mixed versions.
Reject duplicate JSON object fields before map construction (ordinary parsed maps may
lose duplicates), unknown fields, duplicate identities and out-of-range machine values.
Use Nat for semantic indices; checked conversion for UInt32 exit codes and byte offsets.
Wire results carry observations, never serialized Lean proofs or an authoritative accepted
flag. Revalidate and rerun the pure decision after decoding. Bind path remapping to display
fields, replacing `writeRemappedJson`'s text-wide replacement; immutable identity stays intact.

Preserve legacy text subreasons on supported inputs. Introduce the versioned result format
explicitly, not as a silent reinterpretation of old optional `--json-out`; retain old output through `--legacy-json-out PATH`, mutually exclusive with the new
`--json-out PATH`, with no certificate import. #12/#7 document the transition and update
consumers together before removing any legacy output option.
No promise of exact legacy JSON bytes, broader supported inputs or improved runtime is made.

## 6. Cache/pin decision, evidence and remaining obligations

**No new acceleration/certificate API is selected.** The existing replacement correspondence
cache in `Probe.environmentReport` stores checked results by name pair in one fixed environment;
replacement-history worker output is shared within one audit only under the identical-input
condition of [standard §8.6](../standard/8-tooling-and-machine-audit.md#86-classify-lean-computation-mechanisms-exactly).
Preserve these scopes. A future
cross-environment cache would need equality of all relevant inputs plus revalidated evidence
and a proof that varying candidate data cannot weaken acceptance. None is justified here.
Generated-role and canonical runtime recognition determine policy authority; they are not
untrusted acceleration hints. Profiles, scope and pins likewise are normative configuration,
not freely variable candidate data. Con-leche's [parameterized pin/check pattern][installed]
is a reference for separating these roles, not a reason to make our trust pins optional.
No speculative scheduling or fast/reference implementation is proposed.

The [issue 7 verification record](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-7-verification.md) holds the
implementation's compiler results, axiom coverage and qualification at its 2026-09-23
closeout, including the gates still open then.
Earlier PRODUCT-01 runtime results remain historical, scoped evidence; they do
not validate later implementation changes. Use the [contributor guide](contributing.md)
for the complete acceptance command and setup requirements.

The original POLICY-01 design review covered SCOPE-01–05, TYPE-01–03/06,
THEOREM-01/03/06/07, FOUND-01–05, DECL-01–04, COMP-01–04, BUILD-01–04,
DOC-01–05 and DOGFOOD-03/05 for the proposed contracts and linkage only. That historical
scope is not a PASS claim for the implementation or all repository surfaces. Current
review must account for changed inputs and dependencies under the chapter 9 checklist;
all residual accounts still apply to full conformance.

#5–#7 must retain §8.8 positive/intended-reason/restored controls for profiles,
holes/axioms, generated-role forgeries, owned-module attribution, replay bypass,
correspondence, warnings and fence protocol. Pure universal proofs replace neither
source extraction nor process/transport integration qualification. Changed worker
protocols require public-entrypoint controls for omitted/duplicate/substituted keys,
wrong modes/snapshots, worker crash and malformed versions. Changed Library/overlay
coverage requires a fresh imported-client control and exact Lake inventory checks.
Use `./scripts/verify.sh diagnostics` with an applicable existing partition
(`fixtures`, `structural`, `cli`, `environments`, `build-policy`, `lint-driver`) and add focused
controls where absent; do not report an unrun campaign PASS. `serialized-graph`
remains separate. If implementation cost becomes decision-bearing, define the
measurement and resource budget before evaluating it.

Implemented proof coverage is recorded in the [domain](policy-domain.md) and
[proof](policy-proofs.md) guides; ordinary acceptance checks each claimed declaration's exact
axiom set against its profile. The success map in §1 owns implemented collector/worker linkage
and acceptance routes. Editor/adopter and website integration
were delivered by #14 and #15; the [product qualification](product-qualification.md) records
their integrated evidence. Unsupported compiler versions, incomplete census/admission,
ambiguous role origin and unresolved execution are refusals. Any failed proof or pin
capability blocks its specific guarantee and must be reported.

[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean
[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
