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

The root [foundation manifest](../../foundation_manifest.json) owns the policy and toolchain libraries' foundation claims. Acceptance reports every claimed
declaration's exact axiom set; Standard-Logical is an upper bound, not a claim that every proof uses
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
Lean's `withPtrEqDecEq` shortcut with structural equality as fallback where the compiler
elaborates that shortcut, as Lean 4.34.0 does, and the generated structural equality alone
otherwise; the kernel sees the structural computation and the pointer shortcut has Lean's
runtime trust boundary. No wall-clock
bound follows from these proofs.

The stage relations `PolicyOK` combines, each a declarative relation whose decision function is
proved sound and complete against it:

| Relation | Meaning |
| --- | --- |
| `ScopeOK` (§7.1–§7.4) | Exact classified targets and modules, required ownership, source and origin bindings; no excluded import or unattributed declaration. |
| `AdmissionOK` (§7.3) | A completed logical-admission receipt matching the owned dependency census and snapshot; no skipped replay, unsupported admission or emitted warning on a positive fresh claim. |
| `FoundationOK` (§7.5) | No owned logical axiom, no `sorryAx`, unknown or compiler axiom; every axiom in the surface's permitted set. |
| `SafetyOK` (§7.4) | No unsafe or partial declaration unless the exact recursion-helper relation holds; a helper is never logical proof evidence. The helper of a `partial def` (an opaque declaration Lean compiles through it) does not satisfy it, and its finding names that declaration. |
| `ContractOK` (§7.5, §7.11) | Every registered contract targets the exact supported implementation and predicate, with completed admission. Registration adequacy is review. |
| `ExecutionOK` (§7.6) | Every root's closure accounted for, no unresolved path; report mode permits reported trust, checked mode only checked evidence or a boundary of the toolchain's origin-checked trusted base. |
| `DocumentOK` (§7.7) | Complete structural scan; warning-free, admitted Standard-Logical positives; one effective-error match per negative; classified teaching that is never positive conformance. |
| `DocumentationPresenceOK`, `MaterialDocumentationOK` (§5.1–§5.3) | A module docstring is present (`docstring ≠ none`); each registered material declaration's docstring has a nonempty Intent section. For a module's `documentationPresence` job the unproved adapter computes the [RG5001] header decision (`RegulaPolicy.ModuleHeader.failures`, characterized by `failures_eq_nil_iff`: presence, placement first after the imports and no repeated import) as that evidence, and `checked_environmentEvidence` proves only the selection of that frozen record. Registration completeness and fidelity remain R-DOC, intent adequacy R-INTENT. |
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
inventory's, each with the decision kind and the shared functions the collector recorded;
execution counts are
`executionSummary` of each environment; fence counts partition the
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
| `AxiomGate.auditSurfaceAt` (fresh, `--driver-copy`, `--incremental`, `--build-lint`) | `Acceptance.freeze` reconciles Lake modules, sources, configuration, dependencies, reports, replay inventories and origins; `Acceptance.finish` returns `AcceptedRun` with checked equality to `finalize` (`finalize_collection_error`, `finalize_of_collected`). Cached build artifacts never cache a policy decision, and build-lint has no second exit-code-only PASS branch. |
| `Lint.run` (`lake lint`) | The same project audit; exit 0 only through the claimed `Lint.classify` (`checked_classify`, `accepted_sound`): a zero audit exit and a recorded `completed` account of the requested mode. Exits 1, 2, 3 classify rejected, configuration-only and incomplete statuses; a missing or disagreeing status is 3. The audit's own exit code is the recorded `Lint.Observation`'s, or 3 when it recorded none or failed after recording a success (`gateExitCode`, `gateExitCode_some`, `gateExitCode_eq_zero`); an error escaping the audit discards any recorded result, so both sides are 3 (`AxiomGate.entry`). The driver reports the code the audit returned for its recorded result (`classify_gateExitCode`); the observation also decides the result status and the summary counts, each the number of findings of its impact (`Observation.status`, `Observation.tally`, `tally_eq`), and an incomplete finding exits 3 (`exitCode_incomplete`). Which findings a run records is operational. That the recorded observation is this invocation's audit is checked by inspection. `--explain-config` validates the manifest and Lake scope with the audit's own functions (`Manifest.loadFor`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`) and issues no audit certificate; it and `--help` are read-only, exit 2, refuse `--json-out` and `--verbose`, and first invalidate any recognizable `--json-out` destination. An error escaping `Lint.run` is exit 3, or 2 for a `manifest-` refusal, never 0 or 1. |
| `AxiomGate.auditSurface --with-docs` | One process: the project plan and the documentation plan over the same snapshot and build, joined by `combineAccepted`; no evidence crosses a process boundary between the stages. The documentation stage runs inside the project's frozen-input guard (`withSourceEvidenceOr`): a source or configuration change during it is the project's [RG2005] refusal, which replaces the stage's result. |
| `--acceptance-link PATH` (`axiomGate`, `docFenceAudit`) | `axiomGate` records the link for fresh project success only (no `--with-docs`): after `AcceptedRun`, the SHA-256 of the copy-relative accepted sources, configuration, dependency captures, `docs/` Markdown and, with `--verso`, the Verso library's inputs; `docFenceAudit` computes the same identity from its own fresh capture before building and refuses unless it is equal. `axiomGate` invalidates PATH before the audit starts and records the identity only after its outer configuration recheck passes, so any refusal leaves it incomplete. Equality establishes identical captured inputs; `shasum` and the filesystem are trusted. |
| `--driver-copy DIR` (`axiomGate`, internal to `scripts/verify.sh`) | The gate audits the build output of `DIR` and makes no copy of its own. It admits `DIR` only by the facts that [the acceptance boundary](#the-acceptance-boundary) gives. The result names that origin, and the statement that the copy was new rests on the driver. |
| `AxiomGate.auditFile` with a conforming profile | A `freshFile` plan and `AcceptedRun`; dependencies stay incremental. No profile or a compiler-trusting file without a finding is `CLASSIFIED` (exit 0); the file audit's other exits follow its recorded observation as a project audit's do. |
| `Documentation.auditBuiltProject`, `DocFenceAudit.run` | Markdown (and Verso) bytes, fence spans and task identities frozen before compiling; `finishDocuments` calls `finalize`. A corpus with a structural problem has no request plan: it reports each located problem and is refused. Group observations retain every unit and authenticate roles against the whole reconciled inventory; policy selection is per original fence. With `--verso`, the fresh build and render of the standard, then `Regula.Site.missingAnchors_nil_iff` for the registry's and the docs' links into it and `rowsMismatch_eq_none_iff` for its checklist rows. Also with `--verso`, `Regula.Prose.htmlErrors_nil_iff` for the rule IDs in the prose of the rendered pages: each is a registered rule linked to its page, for the runs the HTML scanner extracts, which is operational. `Documentation.Sources.check` compares the documentation inventory and bytes before fence work and before `finishDocuments`; that terminal recheck (with `Snapshot.inputsUnchanged`) and the fence audit run in `BaseIO`, so a failure of either is rethrown only after the structural problems and the fence results obtained are reported. With `--verso`, `Sources.checkLinked` rechecks the linked inputs after the Verso build. |
| `RuleExamples.documentation` | Keeps the documentation driver's accepted run. Canonical positive completion additionally requires a nonempty, all-positive fence inventory; negative and teaching expectations stay classified; failed and incomplete checks retain their own outcomes, and the receipt retains each actual fence classification. The qualifier separately applies `PositiveClassifications` to require a nonempty list with every fence positive, passing and complete before admitting a positive correction. The adapter verifies the original requested documents before emitting accepted metadata. |
| `FreshChecker.run` | A separate `serializedGraph` claim; `leanchecker` success is an observed process result. |

**Project build order.** Before the refusal-only module-scope preflight, a project audit builds
the original claimed library targets, preserving their custom facets, and each claimed
executable's actual root `leanArts` facet. If preflight clears, it builds every original
claimed target, including the executable links, before full inspection. Only that complete
build's successful, warning-free process observation reaches `Acceptance.buildObservation`.
`Lake.ClaimedBuildPlan.completionTargets_exact` binds the deferred build to the original
target array; `build_completed_iff` records the build stage before preflight exactly when no
target build remains. A library-only claim keeps one original build
(`claimedBuildPlan_without_executables`). The plan names each executable root by its module,
not by Lake target syntax. Both phases use the selected build adapter and warning checks,
including the lint driver's options. A deferred build is followed by the source,
configuration and frozen-artifact checks before the unchanged full inspection and terminal
freshness checks.

The preflight reads the first module graphs of three environments at a time, each in a worker
process of its own. The rest of each environment's scope, which in a copy can build owned modules
there, runs one environment at a time in claim order. After an environment asked for such a
build, each later environment reads its graph again. Thus the builds, the findings and their
order do not change.

**No build uses Lake's artifact cache.** Lake writes no compiler messages in the build trace of
a module that it restores from its artifact cache. Thus a check of the build output for warnings
would accept such a module. Each checker build is a `Lake.Build`, and its only runner,
`Lake.Build.run`, builds in the checker's process on `Workspace.uncachedWorkspace`. In that
workspace, each package and each package that it records as a dependency has the cache off in
its own configuration.

The checker starts Lake as a process only for `lake env` and for `lake query` of transitive
imports. That query reads module headers and builds no module, as does the query of the lint
driver's marker decision (`Lake.moduleImports`), which runs in its process. The documentation
audit does not use `lake exe` to run the Verso renderer. It runs the renderer that its own build
made, with the environment that Lake gives the uncached workspace.

`uncachedWorkspace_unreadable` and `uncachedWorkspace_unwritable` prove that Lake's predicates
`Package.isArtifactCacheReadable` and `isArtifactCacheWritable` then give `false` for these
packages. The settings of the workspace and `LAKE_ARTIFACT_CACHE` do not change this result.
Lake `v4.34.1` uses these predicates to decide each read and each write of the cache. A build
finds its packages only through the workspace and these dependency records. These two
facts come from the source code of Lake, not from a proof. Before the build,
`dropRestoredTraces` removes the trace of each root-package module that records a restore from
the cache, so Lake elaborates that module again.

**Each claimed module has messages from the audit's build.** A library's default facets can
leave its modules out of a build of the library. Then the build replays none of their messages.
Thus `Lake.Build.run` also requests the Lean artifacts of each module of a library that a target
names. It also requests the artifacts of the root module of each executable that a target names.
After the build, the trace of each of these modules must record an elaboration, or the build
fails.

`Lake.Build.run` finds each claimed library and executable among the root package's own
targets, with the relation that checks the names of the manifest. It does not read a name as Lake
target syntax, in which a `/` names a package. A name of no such target, and a library with no
module, make the build fail. The check of a trace is `Workspace.elaborationTrace`. The audit's
build names each claimed library and each claimed executable, so its output holds the messages of
the elaboration of each claimed module.

The repository's verification driver, `lean/RegulaVerification.lean`, is not the checker. It
starts its Lake commands with `LAKE_ARTIFACT_CACHE=false`, and a package's own configuration can
override that setting. The gate's own build of the driver's copy is a `Lake.Build`. Thus that
build elaborates again each claimed module that a driver build restored from the cache.

Preflight can now report an excluded-module violation before a native link that would fail;
that run can therefore report [RG2004]/exit 1 instead of the later [RG2003]/incomplete/exit 3.
Its build stage remains unfinished and it is never accepted. An incomplete finding actually
observed by preflight still takes precedence over a violation. This is an ordering change
for refusals, not a proof that arbitrary custom build effects commute or that any execution
meets a wall-clock limit. Lake's facets, parsing, traces and process effects remain trusted.

**`lake lint` dispatch.** Lake's lint dispatch builds only the driver, so the driver first builds its
audit worker `regula/axiomGate` in the workspace `lake lint` ran in (never the `--project`
directory). That workspace built the driver, so it resolves the same `regula`, dependencies and
toolchain; a failed worker build is `INCOMPLETE`. Lake v4.34.0 does not change the driver's working
directory, and passes the dispatching workspace's package library directories, then
`LEAN_SYSROOT/lib/lean`, then any inherited `LEAN_PATH`, as its `LEAN_PATH`. The driver requires
the working-directory workspace's library directories and that directory to begin it
(`Regula.Checker.Lint.dispatchedFrom_iff`) and otherwise refuses with exit 2, so a driver started
outside Lake, by a Lake not collocated with the toolchain, or with `-d` from another project is
refused. The driver builds the claimed targets with the audit-build marker
`weak.regula.auditBuild` ([editor feedback](#editor-feedback)), except in the case below.

Lake scopes the marker to the whole package in its module trace. Thus with the marker, the audit
rebuilds the modules that an ordinary build made, and their replayed logs do not enter its
warning check. The driver omits the marker only for a workspace of the plain shape. It omits it
only if the owner of the workspace asks for it with `lake lint -- --ordinary-lakefiles`. Without
the option, the driver always builds with the marker.

With the option, the owner asserts that the lakefiles of the workspace are ordinary configuration.
The plain shape is a conservative guard under that assertion. It is not a guarantee against a
lakefile that someone wrote to defeat it. The verification of Regula uses the option in the timed
check of its own code (`diagnostics self-lint`). A nightly check of its root package,
`diagnostics self-lint-default`, runs without the option.

The driver takes the option only from the command line. It refuses the option in the
`lintDriverArgs` of a package, because the audited project could give it there. The banner of the
run names the assertion, and the JSON result records it (`scope.ordinaryLakefiles`). Before the
build, the run prints if the build omits the marker, or keeps it and why.

In the plain shape, each package declares only `lean_lib`, `lean_exe`, `input_file` and
`input_dir` targets. Each field of the configuration of a package or a target has the default
value of Lake, except for a short list of fields. Lake gives the fields of each type of
configuration (`Lake.ConfigFields`). Thus a field that a different release of Lake adds keeps the
marker.

A library can change its source directory, roots, globs, `needs` and Lean options. An executable
can also change its root, its file name and its interpreter support. An input target can change
its path and its text mode. Each `needs` entry must name an `input_file` or an `input_dir` of the
same package. A package can change its source directory, its Lean options, its lint and test
drivers and its metadata.

Lake runs no code from these fields in a build. The function `nativeFacets` of a library or an
executable and the filter of an `input_dir` are also fields. Regula reads them from the compiled
configuration file in `.lake/config/` (`leanConfigReading`). Each must be the whole default term
of Lake, for the filter `Pattern.star`, except for its proofs. Any other term keeps the marker.

The compiled configuration file also records each facet that the file declares, new or in place
of a facet of Lake. The driver counts these declarations, and it keeps the marker if there is
one. A file `lakefile.toml` declares no facet and cannot set `nativeFacets`. Its filter of an
`input_dir` is the default only if it omits the filter or writes `"*"`. Lake only reads and hashes
an input target. Thus a build in the plain shape runs no custom build step.

A file `lakefile.lean` must also declare only what the commands of Lake generate. These are the
definitions of the package, its targets and their configurations, `require` and the name of the
package. The commands link each of them in a fixed form (`configurationNames`). The others are
theorems and axioms that state a `Lake.FamilyDef` or an equation between types.

The entries of the file itself must be in a list of extensions that the commands of Lake and their
compilation fill (`configExtensions`). Its entries of the attribute `inline` must be the same as
the entries that the commands give. Thus a compiler replacement (`csimp`), `implemented_by`,
`extern`, `init` or `noinline` keeps the marker.

The file must import only modules of Lean and of Lake. Its syntax must have no `attribute` command
and no local or scoped attribute. A local registration leaves no entry, so the syntax is the place
to find it.

The driver also reads each buildable module of the root package and each executable root, with
the imports from Lake's `transImports` facet (`markerInputs`). Each name must have one source
file, and Lake must resolve the name to that file (`ModuleEntry.Resolved`). The driver omits the
marker only if none of these modules imports `Regula.Linter`, directly or transitively.

Then the build compiles no module that loads the only reader of the marker in Regula. Thus the
marker can change no elaboration, if no module of the project reads the marker itself. The driver
then reuses the modules that an ordinary build made, for example the modules of the driver itself
in this repository.

The decision is `Regula.Checker.Lake.auditMarkerNeeded`, two-way against its specification
(`checked_auditMarkerNeeded`). The specification is the negation of the plain shape
(`PackageShape.Plain`), or a module that is not resolved or that has `Regula.Linter` among its
imports. The driver keeps the marker if it cannot read the workspace, by an exception or an
unknown. The same verdict with and without the marker is a claim for the plain shape only.

That `Regula.Linter` is the only reader of the marker in Regula is by inspection. That no module
of the project reads the marker itself is an assumption. That Lake runs no code from the fields
of the list is read from the source of Lake. The source of Lake also shows that a build in the
plain shape runs no custom build step. That the listed declarations and extensions add no code to
a build is read from the source of Lean and of Lake. Lake's discovery of the modules and of their
imports, and its compiled configuration files, are trusted.

The command `./scripts/verify.sh` makes one copy of the checkout, and its first step operates in
that copy. The driver of that command, `lean/RegulaVerification.lean`, makes the copy before it
starts a Lake command. The function `RegulaVerification.makeCopy` makes it. The copy is a new
directory in `.lake/regula-scratch/` of the checkout.

The copy has the files of the checkout, but not the directories `.git`, `.lake`, `.cache` and
`.regula-scratch`, and not the root directory `tmp`. The theorem `walked_iff` gives that set of
names. Thus the copy starts with no build output, and the builds in it compile each module.

The step has four commands, which the function `RegulaVerification.commands` gives. The build,
the registry checks and the qualification controls operate in the copy. The last command is the
gate that the copy built. The theorem `ordinary_places` gives the directory of each command.

Before these commands, the driver builds what the gate audits and runs. The function
`RegulaVerification.prebuild` gives that build, in the copy. Its targets are the list
`RegulaVerification.gateTargets`: each target that `foundation_manifest.json` claims and the
executable `axiomGate`. The step refuses a manifest that claims a target outside that list, by
the decision `prebuildCovers`. Then the gate runs beside the other three commands, which run one
after the other at low priority. The theorem `inOrder_append_beside` shows that the two groups are
the four commands, each one time.

The step's build is the first of the three commands. It names each target of the prebuild again,
as the theorem `prebuild_named` shows, and it builds the targets that the prebuild did not build.

The driver starts the gate in the root of the checkout as `lake -d COPY exe axiomGate
--acceptance-link PENDING --verso website:RegulaStandard:regula-standard --driver-copy COPY`.
`PENDING` is the pending record of the run.

With `--driver-copy`, the gate audits the build output of that copy. It makes no copy of its
own, and it does not compile the claimed libraries a second time. The gate keeps its own Lake
builds, its check of the build output and its inspection of each declaration. In one local
measurement, those builds compiled no module, and Lake gave the stored warnings again. That is
the behavior of Lake, and no theorem shows it.

The gate admits the directory of `--driver-copy` only by facts that it can read. The function
`AxiomGate.driverCopy` reads them:

- The directory is the directory `project` of a scratch directory of the checkout
  (`ScratchCopy.checked_name?`).
- That scratch directory has its ownership marker, and the marker is a regular file.
- The executable of the gate is in the build directory that Lake gives for the copy
  (`ScratchCopy.checked_inside`).

The gate refuses each other directory. It also refuses the option together with
`--incremental`, `--with-docs`, `--project` or a file. Thus only the fresh audit of the current
project can use a copy of the driver.

One statement stays trusted: the driver made the copy new in this run. The gate cannot read
that fact. A directory that a person made with the same name, the marker and a build of the gate
passes the three checks. Thus the result names the origin of its build output. It does not give
that statement as a result of the gate.

The origin is a value of the type `AxiomGate.Origin`. It is the copy of the gate, the copy of
the driver or the incremental build. The theorem `Origin.mode_fresh_iff` proves that the gate
reports the fresh mode only for the first two. Each of those two holds a value of the type
`Copied`. The constructor of that type is private to the module of the gate, and there only
`isolatedCopy` and `driverCopy` use it. That use is read from the code.

In the JSON result, `scope.buildOrigin` is `isolatedCopy`, `driverCopy` or `incrementalBuild`.
For a copy of the driver, the success line also says that the statement rests on the driver.
The pending record has the same word in its field `origin`.

The gate audits a project in its isolated copy as before, if it has none of the options
`--driver-copy`, `--incremental` and `--build-lint`. The `lint` driver gives `--incremental` to
the gate unless it has `--fresh`. Thus the `lint` driver uses that isolated copy only with
`--fresh`. This change does not alter the fence audit and the gates of `audit/` and
`integration/mathlib/`.

The driver cannot import the checker before the build. Thus it has its own code for the protocol
of `Regula.Scratch`, with the same steps in the same sequence. First it tries to get the
exclusive lock on the file `.lock` of the scratch area. If it gets that lock, no scratch owner
is alive, and it removes each marked directory and its marker (`reclaim`). Then it holds a
shared lock, makes the ownership marker, and makes the directory.

An owner removes its own marked directory while it holds the shared lock. The checker and the
driver remove the marked directory of a different run only with the exclusive lock. Thus no run
removes the live copy of a different run. A first step can start while no other scratch owner of the checkout is
alive. After such a step ends, the scratch area has no directory of a run that died before the
step, if each removal was successful. A scratch owner that dies during the step leaves its
directory for the next scratch user.

The driver reports a removal that failed, with the path of the directory. The step does not
fail for it, and that directory stays.

That code is a second implementation of the protocol, and no theorem relates the two. A control
of the checker self-test operates the driver itself with its private entry `--copy-control`. It
shows that a scratch user of the checker keeps the copy of a live driver. It also shows that the
next scratch user removes the copy of a killed driver. The next driver also removes such a copy
before it makes its own.

After the commands of an accepted step, the driver gives the build output of the copy to the
checkout if the checkout has none. The function `Copy.adopt` reads the place `.lake/build` of
the checkout and does not follow a link there. If nothing is at that place, it renames the build
directory of the copy to that place. If something is there, it changes nothing.

An entry can come to that place after the read. The `rename` call of the operating system does
not follow a link at its target. It does not replace a directory that has an entry. That
behavior is trusted. A rename that fails does not make the step fail. The driver reports it, and
the documentation step then builds what it uses.

In one local measurement, Lake compiled no Lean module again after that rename. The driver then
removes the copy. It also removes the copy after a step that failed.

The driver removes a directory only by one decision, `RegulaVerification.removal`. The decision
uses a read of the place that follows no link. It also uses a comparison of the real path of the
place with the place itself. The driver removes the place only if a directory is there at its
own place (`removal_remove_iff`). The theorem `checked_removal` is the decision contract of that
function.

The driver uses that decision for its copy and for the directory `_site` of the site mode.
Before this decision, the site mode removed `_site` with no such read. With a link at `_site`,
it deleted the content of the target of the link
([issue 260](https://github.com/rbeauchamp/regula/issues/260)). At this time, the site mode
stops there and removes nothing.

One case stays outside that decision. A process can replace an entry in the directory with a
link during the removal. `IO.FS.removeDirAll` examines an entry and then opens it by its path.
Thus it can then remove the entries of a different directory. The checker removes its own
scratch directories with the same function.

The driver moves the pending record to `tmp/acceptance-link.json` only if
`RegulaVerification.passed` accepts the exit status of each command. The driver does that move
before it removes its copy and before the success line. The command `./scripts/verify.sh docs` operates `docFenceAudit --acceptance-link
tmp/acceptance-link.json` with the same `--verso` argument for each `docs/` fence and each `lean`
block of the standard.

Thus an accepted record at `tmp/acceptance-link.json` shows that the gate accepted. It also shows
that each other command of the first step ended with exit status 0. If an attempt fails or is
killed before the move, the record at that path stays incomplete. It is the incomplete record
that the begin-attempt of the step wrote. The shell's zero exit records completed execution of
those commands, not a separate Lean proof.

The safety of the two steps is the identity that the documentation step compares. That step
accepts only a record with the status `accepted` and with the identity of its own inputs (`AcceptanceLink.require`).
Only a gate that accepted the root-package inputs of that identity writes such a record. The
function `AcceptanceLink.record` has one caller in the code, which is the gate after its
accepted result. The identity also has the `docs/` Markdown and the Verso
sources, which the gate does not audit.

Each run has its own pending record. The driver makes it in the scratch directory of its copy,
with a call that fails if the file is there (`Copy.pending`). It gives that path to its gate,
and it moves that path to `tmp/acceptance-link.json`. Thus the record that a run moves is the
record of its own gate, by the names. A gate that continues after a kill of its driver writes a
path that no other run reads.

The driver removes a pending record that it did not move, together with its copy. For a killed
run, the reclamation of the scratch area removes it.

Thus two ordinary attempts in one checkout at the same time can cause a refusal of the
documentation step or a confusing message. They cannot cause an acceptance that no gate gave.
Two such attempts at the same time are not a supported use.

The evidence files, the site directories and the build output of a checkout have no lock. Two
rule-example attempts of the same mode write the same evidence file, and two site builds write the same directories. Each Lake command in the
checkout writes `.lake/build`, and this project found no lock of Lake for that directory. The
first acceptance step writes there only with the one rename, because its build is in its copy.
Do not operate two of those other commands in one checkout at the same time.

The result of the driver is one decision. The driver keeps an entry for each command, and the
preliminary checks are included. An entry has the exit status of its command, if the driver got
one. The driver gets no exit status for a command that it did not operate, could not start or
could not wait for.

The function `passed` accepts the entries if, and only if, each entry has exit status 0
(`passed_iff`). The theorem `checked_passed` is the decision contract of that function. The
driver uses that function before it operates one more command, before the success line and
before the move.

By its type (`Ends`), a result has one entry for each of its commands. Thus the theorem
`passed_covers` proves that an accepted result has an entry with exit status 0 for each command.
Lean does not prove that the exit status of an entry is the exit status of the process. The
process runtime is trusted for that relation.

From the start of a command until the driver waits for it, the driver operates only `BaseIO`
actions. A `BaseIO` action has no exception. Thus no failure can stop the driver before it waits
for that command. This includes the failure to write a progress line.

The gate and the step's build operate in the same copy at the same time. The rest of the step's
build writes only the build output of the targets that the prebuild did not build. The gate
reads the build output of its own targets, which the prebuild completed. The `lake exe` that
starts the gate and the gate's own builds find those targets built, and they build nothing.

In a copy, the gate also builds an owned module that an environment loads and that no build
made. The environments load the claimed modules and the modules of the reporter. The executable
`axiomGate` imports the reporter, so the prebuild built each of those modules, and the gate asks
for no such build.

That Lake then writes none of their files is read from the source of Lake, not proved. Lake
compares the trace of each target, and it writes a hash file only when the file is not there.
The gate reads each `.olean` part of each claimed module before its inspections and compares the
parts after them. A change of one part fails the audit as incomplete.

A claimed target that the prebuild did not build would be built by two Lake processes at the
same time. The driver refuses that case before it makes the copy.

An earlier schedule of [pull request 252](https://github.com/rbeauchamp/regula/pull/252)
operated the gate at the same time as the build and the other checks. In that schedule the gate
built the claimed libraries again in its own copy, while the step built them in the checkout.
The sequence of [pull request 262](https://github.com/rbeauchamp/regula/pull/262) removed that
second build, and with it the concurrent schedule. Its gate audited the build output of its
first command, so the gate started only after the complete build. The present schedule keeps the
one build and starts the gate when its own targets are built.

The sequence of pull request 262 removed work from the step. Before it, the step built the
claimed libraries in the checkout, and the gate built them again in its own copy. That second
build took 55 s to 76 s in the hosted runs of the sequential schedule on the same tree. That is
approximately 18 percent of the step.

The [evidence notes](../../.agents/skills/lean-ci/references/evidence.md) give those runs and
the calculation of the time of this sequence. They also give the criterion for the hosted
result, which was set before a hosted run of this sequence. Two hosted runs then had ratios of
1.38 and 1.39, which confirms the prediction by that criterion. The notes also give the parts of
the step before the present schedule, and the criterion for its hosted result.

The driver writes each line that starts with `verification:`. It writes such a line at the start
of each command and a second line when the command ends. For a command that operates in the
copy, the line gives the directory of the copy. The start line of a command at low priority
says so. The other `verification:` lines are for these events:

- The driver could not start a command.
- The driver could not wait for a command.
- A command failed while the gate operated beside it, and the driver waits for the gate.
- The gate ended. The line gives its time and the time that it operated after the other commands.
- The driver removed the scratch directory of a run that died, or it could not remove that
  directory.
- The driver could not read the scratch area for its reclamation.
- The driver moved the build output of the copy, or it left the build output of the checkout.
- The driver could not move the build output of the copy.
- The driver could not remove the copy.
- The driver moved the pending record.

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

**Compiler capability** (`RegulaPolicy.Compiler`, `Decision`): every admitted inventory contains
`Compiler.Capability`, whose `agrees` field equates the supplied legacy-family observation with
the capability used by the compiled classifier. `admitCapability_iff` proves that admission
exists exactly on a match. `Regula.Collect` obtains the observation from the isolated Core
observer after checking the resolved compiler identity; both report decoders and the native
linter feed it into admission. This linkage trusts compiler execution, installation integrity,
import loading and canonical filesystem paths. It does not prove those IO mechanisms.
`ProducerReport.validate_sound` and `fromJson_admissible` also require this agreement for every
raw or decoded admitted report, without relying on sampled transport mutations. When the
capability is absent (unsatisfiable on this stable revision, whose compiled capability is
`present`; it holds once a prepared revision compiles `absent`), the checked decision
theorems show that a retired name cannot become a compiler axiom or an authenticated native
axiom and its singleton axiom set is unknown. A dependent non-axiom declaration without an
earlier proof-hole failure receives the unknown-axiom refusal even in teaching mode.
Native-proof authentication retains its separate statement, replay and command-provenance
requirements.

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
| Classification | `foundationFor_iff`, `declarationFailure_iff`, `policyFor_ordered`, `OrderedDecision.unique` | Each of the six foundation classes (three labels, hole, unknown axiom, compiler-trusting) has its exact meaning; a declaration's diagnostic is its first failed requirement (invalid membership, owned axiom, hole, unknown, escape hatch, compiler trust, contract failure, profile excess, missing decision contract). For an axiom set outside Standard-Logical, classification keeps the diagnostic precedence hole, then unknown axiom, then compiler-trusting. Renderer strings are not proved. |
| Declaration policy | `policyFor_none_iff`, `policyFor_conforming_iff` | Success is inventory membership plus the independent requirements; teaching never relaxes a conforming profile. A conforming request requires its permitted foundation, safety relation and recorded contract obligations, and the decision requirement of the next row. |
| Decision requirement | `DecisionOK`, `DecisionRegistered`, `decisionFailure_none_iff`, `decidedImplementations_iff`, `Roles.decided_iff`, `Inventory.decisionContracts_iff`, `policyFor_decisionContract_iff`, `census_decided_iff`, `census_decided_iff_of_unrelated`, `accepted_counted_judgment`, `declarationFailure_ne_decisionContract` | A declaration recorded as registered with `@[regula_decision]` whose result type is not `Decidable _` must be the implementation of a recorded contract that the inventory counts. That contract states a decision kind and was not refused. The inventory counts its own recorded contracts. In a project census it also counts the records of each surface that names its surface in `decides` (`census_decided_iff`). It counts a record only for a function in a module of its surface that the other environment loaded with the same origin. Each counted registration met its own requirements in an accepted run (`accepted_counted_judgment`). If no surface names its surface, the inventory reads its own contracts only (`census_decided_iff_of_unrelated`). `policyFor` reports the decision failure exactly for an inventory member that meets every requirement of its own record, is so recorded, and has no such contract; no other requirement reports that failure, and it is decided last (`policyFor_ordered`). No other recorded field enters the requirement, so the generated-from relation the collector records for a finding's location, which a project can write, does not waive it. The registration, the result type and each contract record are observations. That every checker is registered is not checked. |
| Roles | `NativeTeachingOK`, `RecursiveHelperOK`, the two authorization `_iff` theorems, `authorizedUnsafeRecHelpers_base`, `Roles.safetyHelpers_iff` | Each name has its full relation in this inventory. `RecursiveHelperOK` reads no transcript: it requires the recorded observation (`unsafeRecRegenerated`: the regeneration, and the kernel's check of the base's recursion equation), exact metadata, a safe base with the same module/type and Standard-Logical axioms, and the exact group mapping. `authorizedUnsafeRecHelpers_base` states a narrower part of that for every authorized helper: the recorded observation, and a base that is an inventory definition of the same module and type, neither `partial` nor `unsafe`, with axioms within Standard-Logical. `Roles.safetyHelpers_iff` states that a name is a safety helper exactly when that full relation holds for it; no constructor-index wrapper is one. Native roles retain the three §7.5 conditions. `Roles.partialParent_not_safetyHelper` excludes a `partial def`'s helper from the safety exception. The observations are inputs; these predicates do not prove them truthful. |
| Native axiom names | `nativeAxiomOrigin?_sound`, `nativeAxiomOrigin?_nativeAxiomName`, `nativeAxiomOrigin?_isSome_iff`, `compilerTrustingAxiomName_sound`, `compilerTrustingAxiomName_iff`, `modulePrivacy_nativeAxiomName`, `generatedPrefix_iff`, `native_generated`, `native_compilerTrustingAxiomName`, `native_provenance` | A name is recognized exactly when it is `nativeAxiomName parent t idxs`, Lean's own `Name.append` and `appendIndexAfter` as `nativeEqTrue` and `DeclNameGenerator.mkUniqueName` apply them, for `native_decide`, `decide +native` or `bv_decide`, with or without module privacy. `compilerTrustingAxiomName`, the execution probe's classification, holds exactly for these names and the enabled legacy compiler axioms. The prefix is nonanonymous without macro scopes and the generator indices are a nonempty list of positive numbers. For a declaration name without macro scopes in a module without macro scopes, a recognized prefix related to it by `GeneratedPrefix` (the name itself, or its `mkPrivateNameCore` form when it is public) gives exactly the names `DeclNameGenerator.mkUniqueName.curr` gives its native axioms, whether or not the module elaborates the proof without exporting (`modulePrivacy`). The recognition direction and that characterization assume `RuntimeStringAppend`, because `appendIndexAfter` uses the logically opaque extern `String.Internal.append`. The three tactic names and the list of `nativeEqTrue` call sites are cited from the pinned sources, not derived; hygienic and anonymous prefixes are not recognized. |
| Execution policy | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff`, `boundaryFailures_ids`, `rootFailures_ids`, `boundaryFailures_toolchain`, `project_boundary_reported`, `checked_toolchainBase` | No failure exactly when there is no unresolved path and every boundary meets its mode's relation; the failure kind of every boundary and path for every claim. A toolchain-owned boundary never fails; every boundary without an admitted toolchain origin or checked evidence has its own failure record, in every root whose account contains it, under a checked claim; the audit's toolchain trusted base has each toolchain-owned boundary (constant and kind) of every labeled environment account in exactly one entry, which lists exactly the environments and roots that reach it. |
| Execution findings | `executionFindings_empty_iff`, `failure_reported`, `unresolved_reported`, `executionFindings_sound`, `rootFindings_ids`, `executionFindings_unresolved`, `ExecutionRoot.boundary_reported`, `ExecutionRoot.first_record`, `ExecutionRoot.folded_trusted`, `ExecutionRoot.carries_spec`, `ExecutionBoundary.restates_spec`, `boundaryFailures_restates`, `ExecutionInventory.reported_or_folded` | The findings the gate reports are the failure records with each folded boundary's record reported in the finding of the boundary it is reported with. A boundary is folded in two cases only. It repeats an earlier record: a boundary of the same root with a smaller occurrence number is trusted like it and has the same constant, kind, replacement and toolchain origin, so the two have the same failures for every claim. Or it is a trusted partial-computation boundary without a toolchain origin whose constant is the source of no helper edge, and a boundary of the same root that is trusted, not toolchain-owned and not itself foldable names its constant, by its `replacement` or, as a partial-computation boundary, by a helper edge. Every folded boundary is trusted, and every boundary of a root is, or restates, one that is reported on its own or is an implementation of one reported on its own. So the findings are empty exactly when `ExecutionOK` holds; every failure record is its boundary's own finding, is named in the finding of a boundary whose implementations include it, or is a later record of a boundary that is; every unresolved path is a finding unchanged; every finding has the kind, root and detail of a record, followed by its implementations; a root has one finding per failing boundary reported on its own; the unresolved findings are as many as the unresolved records; and every boundary of the account is counted by the coverage counts or folded. These are statements about the supplied account: that the collector records a `partial` definition and the constant compiled to it, and two candidates of one equality, in this form is its observation of the environment, not proved. |
| Correspondence | `DefeqComparison.classify_checked_iff`, `classify_trusted_iff`, `classify_unresolved_iff`, `DefeqComparison.ofAttempt_checked_iff`, `ofAttempt_negative_iff`, `ofAttempt_incomplete_iff`, `ofAttempt_error` | Checked exactly for a completed comparison with admitted evidence, trusted exactly for a completed one without, unresolved exactly for one that did not complete. A comparison is completed exactly when the attempt recorded the answer of a kernel that decided. It has evidence when that answer is an admission with only Standard-Logical axioms. It has no evidence when the answer is a refusal, or an admission with a different axiom. An attempt that raised an error is incomplete, also after the kernel admitted the proof, for example when printing the proof failed. That `Probe.kernelAnswer` records the answer of the kernel is observed. |
| Expected diagnostics | `matchesPattern_iff`, `orderedLiterals_iff` | The restricted pattern's ordered leftmost-split match within one effective-error message. |

### Where each field of a declaration's record comes from

`RegulaPolicy.Declaration` is the record the collector builds for one constant
(`Collect.declaration`), and the policy theorems above take it as given. Its type has three parts,
and each field is declared in the part that says where its value comes from
([`RegulaPolicy/Domain.lean`](../../lean/RegulaPolicy/Domain.lean)):

| Part of the record | Source of its fields | Fields |
| --- | --- | --- |
| `Declaration.KernelChecked` | Kernel-checked declaration data: a field of the constant's `ConstantInfo`, or a pure function of such fields. | `name`, `kind`, `type`, `isUnsafe`, `isPartial`, `safety`, `internal`, `private`, `unsafeRecBase`, `levelParams`, `all`, `hints`, `valueConstants`, `nativeStatement` |
| `Declaration.ToolchainObserved` | A toolchain observation: the answer of Lean's elaborator, compiler or kernel, or of the checker's own observing code, at inspection. No mark a project writes decides one of these fields. | `module`, `prettyType`, `isProp`, `axioms`, `unsafeRecRegenerated`, `nativeReplay` |
| `Declaration.ProjectWritten` | Environment state an audited project can write, or an observation such state decides: an extension's entry, an attribute, a declaration range, and the two observations of the checker that read such marks directly. | `instance`, `noncomputable`, `implementedBy`, `extern`, `projection`, `matcher`, `recursive`, `recordedRanges`, `generatedFrom`, `executableContract`, `decisionResult`, `tableOmissions` |

`Declaration.Inspected` is the first two parts, and `Declaration` adds the third. A decision or a
relation takes the part whose fields it reads, so its signature shows where its inputs come from:
Lean rejects a reference to a field of another part, and reading one takes a change of the
signature that every caller sees. Moving a field to another part is rejected the same way at each
use that takes a narrower part. What takes which part:

| Decision or relation | Argument | Fields it can read |
| --- | --- | --- |
| `SafetyOK` | `Declaration.KernelChecked` | Kernel-checked data alone (`isUnsafe`, `isPartial`, `name`). The helper set is a separate argument. |
| `KnownDependencies`, `CompilerPolicyOK`, `ProfileOK` | `Declaration.ToolchainObserved` | Toolchain observations alone (`axioms`). |
| `FoundationOK` | `Declaration.Inspected` | Kernel-checked data and toolchain observations (`kind`, `axioms`). |
| `ContractOK`, `SharedTestOK`, `sharedTestFailure` | The recorded contract (`RecordedContract`) | The recorded contract alone: its refusals, which a project-written mark can decide, and the names of its shared tests. |
| `DecisionRegistered`, `decidedImplementations` | The recorded contracts an inventory counts (`Inventory.decisionContracts`: its own `recordedContracts`, then `Inventory.counted`) | The recorded contracts alone: the kind, the refusals and the implementation of each. |
| `Erasure.reproduces` ([below](#the-recursion-helper-comparison-decision-and-observing-pass)) | No record: two values, `Erasure.Observations` and whether the pass finished | Toolchain observations of the terms of the two values, and the pass's report of its own run. |
| `NativeStatement.recognize?` ([below](#the-native-axiom-statement-decision-and-observing-pass)) | No record: a `NativeStatement.Candidate` | The tactic and the prefix that `nativeAxiomOrigin?` reads from the name, and the kernel-checked type. |
| `declarationFailure`, `DeclarationOK`, `declarationRequirements` and their theorems | `Declaration.Assessed` | The inspected part and the recorded contract: they join the relations above, so through `ContractOK` and `SharedTestOK` they read the recorded contract. |
| `decisionFailure`, `DecisionOK` | `Declaration.Registration` | The name and `decisionResult`, the project's own registration, alone. |
| `NativeTeachingOK`, `RecursiveHelperOK` and the `authorized…` validators | `Declaration.Role`, and the role parts of an inventory (`roleRecords`), with the observed parts of its transcripts (`observedTranscripts`) | The inspected part and three project-written marks: the replacement, the `extern` mark and the recorded ranges. A native-proof axiom must have no replacement and no `extern` implementation. A recursion helper must have no replacement, no `extern` implementation and no recorded range, and its base no replacement and no `extern` implementation. These marks can refuse a role but do not grant one: `authorizedNativeAxioms_neutral` and `authorizedUnsafeRecHelpers_neutral` prove that each name the executed validator admits is admitted with all marks of the inventory at their neutral values (`Declaration.Role.neutral`). |
| `policyFor`, `memberFailure`, the editor decision, `policyRequirements` | `Declaration` | Membership of the inventory, which is of the whole record. `policyFor` checks it at its admission boundary (`recordFailure`), and `memberFailure` and the editor decision take a proof of it. The decision on an admitted record is `policyForName`, which takes its name alone. `policyFor`, `memberFailure` and `policyRequirements` join the assessed part and the registration part. The editor decision reads only the assessed part: `declarationFailure` takes `Declaration.Assessed` and `needsRoleEvidence` takes `Declaration.Inspected`. |
| `operationalFailure`, `OperationalOK`, `operationalView`, `operationalAxioms` | `Declaration.Assessed` | `kind`, `isProp`, `axioms` and, through `ContractOK` and `SharedTestOK`, the recorded contract. The view also clears `isUnsafe` and `isPartial`. |

**Transcripts.** `Transcript.ToolchainObserved` holds the module and the source file that Lake
resolves, the toolchain's identity, the imports and the commands. `Transcript.ProjectWritten` holds
the source text and the runtime replacements that its commands recorded. The frontend observes each
field of a command's record, `Command`, in the fresh elaboration, and the records of added
constants copy fields of their `ConstantInfo`. Lean's kernel admitted such a constant only if the
source left kernel checking on, and the transcript does not replay it. The native role validator
and `validCoordinates` take the observed parts alone, and admission and the coordinate check read
the source text only for comparison.

**Limits.** The parts classify the source of a value but do not make an observation truthful.
That `Collect.declaration` and `Frontend.buildCore` fill each field from the source its part names
is by inspection of those functions, not proved. State a project writes can still enter a toolchain
observation, and the docstring of each such field says how: `isProp` is Lean's answer, which does
not unfold an irreducible definition; `prettyType` is Lean's printer, which uses the notations in
force; `nativeReplay` runs compiled code; and what a project writes selects which regeneration
`unsafeRecRegenerated` reports, while the pure comparison and the kernel decide it. The two
observations of the checker that a project-written mark decides are fields of
`Declaration.ProjectWritten` for that reason. `executableContract` reads Lean's `noncomputable`
mark for one refusal. `tableOmissions` compares the axioms of Lean's module table, which a
project can write, with the axioms that the replayed kernel gives. The decisions of [RG1007]
and [RG1009] take the recorded contract and no other field, so they read the `noncomputable` mark
only through it. The decision requirement of [RG1008] takes the name and the registration alone
(`Declaration.Registration`). The role validators take the role part (`Declaration.Role`):
the inspected part and the three marks that they read. The declaration decision and the
operational decision take the assessed part (`Declaration.Assessed`): the inspected part and the
recorded contract. `policyFor`, `memberFailure` and the editor decision take the whole
`Declaration` because membership of the inventory is a property of the whole record. `policyFor`
checks it at the admission boundary `recordFailure`, and the other two take a proof of it.
`policyFor`, `memberFailure` and `policyRequirements` join the assessed part and the registration
part. The editor decision reads only the assessed part: it joins the declaration decision with
`needsRoleEvidence`, which takes `Declaration.Inspected`.

**No project-written mark admits.** The marks of the role part and the refusals of the recorded
contract can refuse but do not admit. `NativeTeachingOK.neutral` and
`RecursiveHelperOK.neutral` show that a role still holds with all marks of the inventory at their
neutral values. The `_neutral` theorems of the two validators carry that to the executed
functions. For the refusals of the recorded contract, `DeclarationOK.neutral` and
`OperationalOK.neutral` show the same. `declarationFailure_neutral` and
`operationalFailure_neutral` carry it to the executed declaration and operational decisions.

`declarationFailure_marks_refuse_only` joins the role validators and the declaration decision
through `DeclarationOK.of_subset`: a role that a mark removes can only refuse.
`decidedImplementations_neutral` shows that the refusal of a contract can remove a decided
implementation but does not add one. `decisionFailure_marks_refuse_only` carries that to the
executed decision requirement of [RG1008] through `DecisionOK.of_subset`. No theorem states this
for `policyFor`, `policyForName` or `memberFailure`, which take an inventory.

`policyFor` is the admission boundary `recordFailure` followed by `policyForName`, the policy
decision on the record's name. The boundary refuses a record that is not one of the inventory's
records.
`policyForName` takes the name alone, so `policyForName_identity` gives two records with one name
one decision. `policyFor_of_mem` and `memberFailure_eq_name` show that a member's decision is the
one on its name. `editorDecisionImpl_identity` shows that two members with one name get one editor
decision. The whole record enters these decisions only through the admission boundary, which can
refuse a record but admits none.

The registration that the decision requirement of [RG1008] reads is the rule's subject, not
evidence. The rule applies to the functions a project marks as decisions, so the mark selects what
the rule checks. A function without the mark is outside that rule by its definition, and all
other rules still check it.

**Consumers** (paths from `lean/Regula/`):

| Operational caller | Proved pure function | Remaining boundary |
| --- | --- | --- |
| `Checker/Policy.admitScope`, with `Frontend.validateCoordinates` | `checked_scope` (first coordinate refusal in transcript order, then exactly `admitInventory` with `authorize`; success iff all coordinate checks and `InventoryValid` hold, retaining both input arrays); `checked_coordinates` (claimed `RegulaCore.Coordinates`: success iff `CoordinatesAgree`, refusal with the first unmet obligation in traversal order) | Lean's UTF-16 column function (`FileMap.leanPosToLspPos`) and `FileMap`; source and compiler observation acquisition. |
| `request`, `ruleFor`/`reasonFor`, `ruleForMember` (claimed `RegulaCore.Policy`) | `checked_request`, `checked_rule`, `checked_memberRule` over `policyFor`; `ruleForFailure_injective`, `reasonFor_eq_some_iff` | Registry descriptor text; adequacy of the mapped rule set. |
| `labelOf`, `labelOfMember`, `classify`, `classifyMember` | `foundationFor`; `checked_memberFoundation`, `labelOf_member`, `classifyMember_eq` | Transitive axiom sets from the replayed kernel (`KernelAxioms.axiomTable`) and module ownership. |
| `executionFindings`, `executionFailures`, `executionSummary`, `toolchainBase` | `checked_executionFailures` (line `k` renders finding `k`, none added or dropped, so the lines are empty iff `ExecutionOK`), `executionRule_injective`, `checked_summary` (the boundary counts range over the boundaries reported on their own: a later record of one trusted boundary of a root, and a `partial` implementation reported with the boundary that runs it, are counted with that boundary, not again), `checked_toolchainBase` | Root collection, retained compiler edges, correspondence admission, source history, module origins and the text and JSON rendering of the toolchain trusted base. The records of the execution walk are observed, and the account that `ExecutionWalk.assemble` builds from them is not proved. |
| `Probe.replacementCorrespondence` | `DefeqComparison.classify` of `DefeqComparison.ofAttempt` (an attempt that the kernel did not decide, or that raised an error, is unresolved and not trusted) | The kernel decision itself, the record of its answer (`Probe.kernelAnswer`), the capture of an error (`Probe.comparison`) and the incomplete theorem-candidate search. Lean's Core-based monads rethrow a runtime resource exception or an interruption. Such an exception records no comparison and stops the report. |
| `Checker/Common.admitIndexedWorkerResults`, `mapWorkQueue`, `Documentation.auditTasks` | `checked_indexedResults` over `ResultState.collect` | Child completion, strict packet decoding, task scheduling and exact request and source binding. |
| `Checker/FenceScan.scanLines`, `scanVersoLines`, `matchesPattern` | `checked_scanLines`, `checked_scanVersoLines` (no violation exactly for a clean document), `fence_of_leanShaped`, `example_of_leanShaped` (a returned fence for each line of Lean shape), `toList_linesOf` (the lines of a text), `matchesPattern` | The body and the byte ranges of a returned fence, pattern diagnostic text and effective-error extraction. |
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
| [RG1001]–[RG1003] | `declarationFailure_iff`, `policyFor_ordered`, `foundationFor_iff` | Ownership and transitive-axiom acquisition in the replayed kernel (`KernelAxioms.axiomTable`). The [deliberate changes](#changes-to-leans-environment-compiler-or-build) to Lean's environment, compiler or build are trusted boundaries. |
| [RG1004] | The above plus `authorizedNativeAxioms_iff`, `native_generated`, `native_provenance`, `compilerTrustingAxiomName_iff`. For the statement that the replay reads: `NativeStatement.asserted?_sound`, `NativeStatement.asserted?_complete` and the kind `NativeStatement.checked_recognize` ([below](#the-native-axiom-statement-decision-and-observing-pass)). | Transcript and replay truth; authorization permits teaching only. The replay evaluates compiled code, and its result is an observation. The recorded text of a statement is not proved to identify its expression. The [deliberate changes](#changes-to-leans-environment-compiler-or-build) to Lean's environment, compiler or build are trusted boundaries. |
| [RG1005] | `foundationFor_least`, `leastFoundation_ext`, `policyFor_conforming_iff` | The least containing profile of the observed axioms, not the least possible axioms for the proposition. The [deliberate changes](#changes-to-leans-environment-compiler-or-build) to Lean's environment, compiler or build are trusted boundaries. |
| [RG1006] | The helper authorization `_iff` theorems, `Roles.safetyHelpers_iff`, `policyFor_conforming_iff`, `subject_contract`, `partialParent_rule`; for the comparison that records a recursion helper's observation, `Erasure.equalWithin_iff`, `Erasure.reproduces_iff` and the kind `Erasure.checked_reproduces` ([below](#the-recursion-helper-comparison-decision-and-observing-pass)) | Exact helper metadata, the recorded recursion-helper observation and the base's axioms are checked. A `partial def`'s helper always has a finding naming its opaque parent when that parent is in the inventory. A recursion helper's observation is recorded only where Lean's kernel checked, at that audit, the base's recursion equation for each helper of the group (`Collect.recursionEquationChecked`); that check is the collector's, not a theorem of the policy. The collector observations, the step from the recursion equation to the values the helper returns, compiled-code correspondence and execution coverage are not proved. A recursion helper's termination still trusts Lean's well-founded preprocessing (standard §7.4). No constructor-index wrapper is admitted. |
| [RG1007] | `ContractOK` through `ruleFor`; `DecisionKind.ofStructureName?_eq_some_iff` (a head constant is read as a decision kind exactly when it is that kind's structure); `DecidedFunction.covers_iff` with `FieldPacking.covers_iff` (a decided function of a form that is read is accepted exactly when the kind's result type has no leading binder and, for a field application, the type has one constructor and no index and the arguments are its fields, each once and in order), with `Regula.Decides.of_packing` and its one-way forms (a kind on a packing that reaches every tuple of arguments is the kind of the function) and `Regula.Decides.iff_slice` (a kind with an argument left whose acceptance predicate reads the result at one fixed value of that argument is the kind of one slice). For the searches that guard each reduction and find a mention of the implementation: `MentionSearch.search_sound`, `search_complete` and the kind `MentionSearch.checked_search`. | Recorded contract failures are enforced; Probe's extraction of the proposition and root, the reduction that exposes a requirement's head constant, the reading of the decided function as the implementation on its arguments, on every field of one structure or on a product (`Function.uncurry`), or with its result erased (`Regula.Dependent.isSome`, `isOk`), the reading of each field from the kernel-checked definition of its projection and of the constructor and index counts from the kernel-checked inductive type, and of the number of leading binders of the kind's result type, which give `DecidedFunction.covers` its input, the two steps from those numbers to "every tuple of arguments is the fields of a value" and "no argument is left", which are argued and not machine-checked ([below](#decision-kinds-of-regulas-own-decisions)), the reading of the universe levels, what each record of the searches lists, that a constant with no record leads to no target, proof admission and adequacy are not proved by this relation. |
| [RG1008] | `policyFor_decisionContract_iff`, `Roles.decided_iff`, `policyFor_ordered` through `ruleFor`; `decisionFailure_none_iff` for the self-audit's direct use; `editor_decision_ne_decisionContract` (the editor never renders it) | The rule reports a registered decision without a `Decidable` result or an accepted decision contract that its inventory counts. It reports only declarations that meet their other requirements. The two environments of a counted contract must load the module of the function with the same origin (`census_decided_iff`), and the collector gives these origins. Reading the registrations of every loaded module and the result type by reduction (`Regula.decisionRegistrations`, `Collect.decisionResult?`, `returnsDecidable`) is the collector's, and so are each recorded contract and the refusal of a registration that names a declaration outside the inventory (`Collect.ownedDecisionRegistrations`). A result type the reduction does not unfold to `Decidable _` counts as another form, which fails closed. Which functions are registered, and each specification's adequacy, are review. |
| [RG1009] | `sharedTestFailure_none_iff` with the kind `checked_sharedTestFailure`, `declarationFailure_ordered` through `ruleFor`, and `mem_sharedNames_booleans` with `SharedDefinition.class_eq_boolean_iff` for the recorded names. For what the search follows from the specification and the acceptance predicate: `StatementReading.reads_iff`, the kind `StatementReading.checked_reads`, `reading_some`, `read_subset_withTypes`, `through_input` and `no_shared_test` ([below](#the-reading-of-a-statement-decision-and-observing-pass)). | A decision registration is reported when its record names a shared function with a result of `Bool` or `BEq`. Its place is after the recorded refusals of its contract. The observing pass, the search of the implementation and the reading of each shared function (`Collect.sharedReading`, `Collect.sharedDefinition`) are the collector's and are not proved. That a test that only the declaration of the input type names is no part of a specification is an argument, not a theorem. The search compares names. A copy of a test under a second name passes. A shared function with a different result type is named in the account and is not refused. A file with a `module` header gives the editor an imported function with no exported value as an axiom. The editor reads its class from its type. It reports a reading that could miss a test below such a function as incomplete ([RG2005]). |
| [RG2004] | `policyFor_ordered` (membership first), `CensusOK`, `PlanOK` | Complete Lake and environment ownership acquisition. |
| [RG3001], [RG3002] | `executionFailureRecords_empty_iff`, `boundaryFailures_empty_iff`, `boundaryFailures_toolchain`, `project_boundary_reported`, `executionFindings_empty_iff`, `failure_reported`, `executionFindings_sound`, `checked_toolchainBase`. For the walk of a root, `ExecutionWalk.walk_sound`, `walk_complete`, `walk_nodup` and the kind `ExecutionWalk.checked_walk` ([below](#root-and-closure-discovery-decision-and-observing-pass)) | The theorems cover the supplied unresolved paths and boundaries and their supplied origins, and the visits of the walk over the records of the pass. They do not cover root discovery, the truth of a record or of the origin observation, or the toolchain's or external runtime code. They also do not cover the account that `ExecutionWalk.assemble` builds from the visits, or that the reader's walk (`SharedExecution.walkLoop`) gives the same visits and parents. The collector's record of the `partial` definition to which a constant is compiled is also not proved. The [deliberate changes](#changes-to-leans-environment-compiler-or-build) to Lean's environment, compiler or build are trusted boundaries. |
| [RG4001] | `checked_scanLines`, `checked_scanVersoLines`, `fence_of_leanShaped`, `example_of_leanShaped`, `toList_linesOf` | A document has no violation exactly when each of its lines is a permitted transition of the fence protocol and keeps the shape rule ([the fence scanners](#the-fence-scanners-decisions-and-observing-pass)). A clean document has a returned fence for each line of Lean shape. The body and the byte ranges of a returned fence, the text of a violation and the adequacy of the relation are not proved. That a Markdown reader opens a Lean block only at a line of Lean shape is by reading CommonMark. |
| [RG4003] | `matchesPattern_iff`, `orderedLiterals_iff` | One effective error under the restricted grammar; producer completion and effective-error extraction are operational. Policy-negative source fixtures keep their separate registry-bound expectation qualifier, and a rejection is not positive conformance. |
| [RG5002], [RG5003] | `materialDocumentationFailure_eq_none_iff`, `_eq_missingDocstring_iff`, `_eq_missingIntent_iff` (which docstrings each rule reports; the two never both fire), `hasIntentSection_iff`, `ruleForMaterialDocumentation_injective`; the native linter and the project gate both execute `RegulaPolicy.materialDocumentationFailure`, which `materialDocumentationFailure_eq_none_iff` ties to `MaterialDocumentationOK` | The ATX line grammar (`heading?`) is a definition with checked instances, not a theorem about Markdown (`intentHeading_examples`); `findDocString?` lookup is Lean's. Intent adequacy is R-INTENT. |
| [RG2001]–[RG2005], [RG4001]–[RG4004], [RG5001]–[RG5003] | The stage relations above, composed by `accept_iff` and `accepted_report_identity` | The adapters that populate them. |

[RG2006] checks the Lake options with a proved decision over Lake's resolved configuration
(`RegulaPolicy.Community.failures`, `failures_eq_nil_iff`), not by re-implementing any linter.
It admits Mathlib's header linter on only when the target configures the linter's license option
(`conforming_header`, `header_on_unlicensed_fails`); every other required option admits only its
required value (`admits_of_ne`). The license option counts as configured only when `leanOptions`
gives it (`licensed_iff`); a `-D` extra argument that gives it a value can only make the target
fail. That the linter compares the header with that option is read from Mathlib's source and
assumed.

**Correspondence resource bound.** `kernelAnswer` gives the kernel Lean's
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

**Correspondence theorems from replayed modules.** `Probe.replacementCorrespondence` tries a
theorem only when the predicate `admits` of `Probe.environmentReport` accepts it. `admits` accepts
a theorem of a module that the admission of the environment replayed or reused, or of an
origin-checked module of the toolchain. Thus the kernel checked the theorem in this audit, or the
theorem is part of the trusted base of the toolchain. A theorem of a dependency that the audit
does not own supplies no evidence, so its boundary falls to the kernel comparison. That `admits`
is applied to each candidate is read from the code, and the module of a name is the one Lean
records for it.

## Decision kinds of Regula's own decisions

A decision kind (`Regula.DecidesSoundly`, `Regula.DecidesCompletely`, `Regula.Decides`, standard
§3.8) states which directions of a decision are proved against a written specification, with a
witness about the function itself. A function with
an argument type that depends on an earlier argument, or with a type, instance or proof
argument, is decided on a structure whose fields are its arguments: the kind is stated about the
function applied to every field, in order. A function whose result type depends on its arguments
states the same kinds about an erasure of its result, `Regula.Dependent.isSome` or
`Regula.Dependent.isOk`. A result of a subtype type that depends on the input has no kind until
[#243](https://github.com/rbeauchamp/regula/issues/243) is decided: such a function returns
`Decidable p`, or is registered with an ordinary requirement.

A kind about the function on a structure is the kind about the function when every tuple of
arguments is the fields of some value of the structure (`Regula.Decides.of_packing` and its
one-way forms). A type with one constructor and no index has that property: its constructor takes
every tuple of fields to a value, and each projection of that value reduces to the field. A type
with an index does not: its values are only the tuples of fields that compute the index, so a kind
on it is a kind on part of the domain. Lean's `structure` command refuses an index, but Lean's
kernel admits a primitive projection on any type with one constructor, and a metaprogram can add
such a declaration. So the collector reads the number of constructors and of indices from the
kernel-checked inductive type and does not rely on the `structure` command. The decision on those
numbers and on the fields a statement gives is the pure function `FieldPacking.covers`, exact by
`FieldPacking.covers_iff`.

A kind is about the function applied to every one of its arguments. With an argument left, the
result of the decided function is a function, and how much of it the kind constrains depends on
the acceptance predicate. One that reads the result at one fixed value of that argument gives
the kind of one slice of the function (`Regula.Decides.iff_slice`), which says nothing of the
function at another value. One that quantifies over that argument can constrain every value. The
released checker accepted a kind with an argument left about the function itself and about
`Function.uncurry` of it. The refusal is a conservative structural restriction: the collector
does not read the acceptance predicate, so it refuses both forms, and the remedy for both is to
supply the argument. The collector now reads the number of leading binders of the kind's result type, with every
definition unfolded, and the pure function `DecidedFunction.covers` (exact by
`DecidedFunction.covers_iff`) accepts a decided function only when its field application covers
and that number is zero. It decides every form that is read: the function itself,
`Function.uncurry` and a field application. An argument that is left is supplied by one more
`Function.uncurry` (`Regula.packing_uncurry_covers`) or as one more field.

Two steps from what the collector reads to the claim are the trusted part of this decision. Each
is argued from Lean's typing rules and is not machine-checked:

- **No leading binder means no argument is left.** A term can be applied only when its type
  reduces to a function type. So a result of a type with no leading binder takes no argument,
  and the implementation has no argument after those that the decided function supplies. That a
  type is not a function type is not a proposition of Lean's logic, so no theorem can take it as
  a hypothesis.
- **One constructor and no index means the packing reaches every tuple.** The constructor takes
  every tuple of fields to a value of the type, and each projection of that value reduces to the
  field. That is the hypothesis of `Regula.Decides.of_packing`, which is proved for every packing
  that has it and not for every such type.

The collector's reading of those numbers from Lean's declarations is operational code, as the
[RG1007] row above says.

Regula registers its own pure decisions with a kind, so a
one-way guarantee is a declared choice. It also registers each of those functions with
`@[regula_decision]`, so deleting a decision's contract while the function stays registered is
rejected under [RG1008]; [the decisions without that registration](#decisions-not-registered-with-regula_decision)
are listed with the reason for each.
A kind is evidence about the function between the supplied values and the written
specification; it does not make the observations truthful, and it is not a verdict on the
specification.

Which report states a kind depends on the library that holds the registration:

- **Claimed libraries** (`RegulaPolicy`, `RegulaCore`, `RegulaQualification`, `AuditApp`, and the
  standalone programs' libraries `RegulaProvision` and
  `RegulaVerification`). Their
  registrations are contracts of the accepted inventory, so an accepted account of Regula states
  the kind of each and, for a one-way kind, the direction it leaves open.
- **The excluded `Regula` library.** Acceptance does not report its declarations, so no report
  states the kind of its registrations, named here with their modules: `checked_same`
  and `checked_read` (`Regula.SharedExecution`), `checked_intern` and `checked_expand`
  (`Regula.SourceTexts`), `checked_agrees` and `checked_canonical` (`Regula.JsonAgreement`),
  `checked_parseLocation` and `checked_parseDiagnostic` (`Regula.DiagnosticCodec`),
  `checked_exactFields` (`Regula.Checker.PolicyCodec`), `checked_scanLines` and
  `checked_scanVersoLines` (`Regula.Checker.FenceScan`), `checked_parseMode` and `checked_parseRule`
  (`Regula.RegistryCodec`), `checked_parseName` and `checked_parsePrintedNameJson`
  (`Regula.StructuralName`), `checked_checkCopies`, `checked_checkHeader`,
  `checked_admitReplay` and `checked_checkTable` (`Regula.Checker.Admission`),
  `checked_parseValue` (`Regula.Checker.Manifest`), `checked_auditMarkerNeeded`
  (`Regula.Checker.LintBuild`), `checked_validate`
  (`Regula.Checker.ProducerReport`), and `checked_admitExampleRequest`,
  `checked_admitExampleSources` and `checked_admitDemonstration` (`Regula.Website`). Lean's kernel checks each kind's proof in the library's
  warning-free build, and the `self-audit` diagnostic holds each registration to [RG1007],
  including that the kind is stated about the implementation and that neither its acceptance
  predicate nor its specification mentions it, to [RG1009], and each registered decision to [RG1008] against
  the decision contracts of its own module, since that diagnostic audits each module in its own
  environment. It is not part of acceptance and prints the number of registrations, not their
  kinds.

The tables below cover the decisions of both groups.

The inventory is the pure functions whose result is a verdict of the checker: the decision
behind a rule, the admission of a decoded record, the reader of a written form, a qualification
validator, and the decisions of the example application. A helper that only computes part of
such a verdict (`Community.admits`, `orderedLiterals`, `hasIntentLines` and the like) is covered
through the proof of the decision that calls it. Functions whose result is a plan, a label or a parsed
command for Regula's own tooling (`RegulaCore.Setup`, `RegulaCore.Edition`,
`RegulaCore.Toolchain`, `RegulaCore.Guidance`) are not verdicts about audited code and are not
in it. That this inventory is every function of Regula that acts as a checker is by inspection:
[RG1008] holds the registered functions to a contract and does not find unregistered ones.

Two-way decisions (`Regula.Decides`), each with an accepted and a refused input:

| Decision | Specification | Used by |
| --- | --- | --- |
| `RegulaPolicy.declarationFailure`, `decisionFailure`, `operationalFailure` (accept on `none`) | `DeclarationOK`, `DecisionOK`, `OperationalOK` | The declaration decision of [RG1001]–[RG1007] and [RG1009], over the inspected part and the recorded contract of the recorded declaration (`Declaration.Assessed`) and the supplied role sets; the decision requirement of [RG1008], over the name and registration of the recorded declaration (`Declaration.Registration`) and a supplied set of decided implementations; and the operational self-audit's, over the assessed part. |
| `RegulaPolicy.sharedTestFailure` (accepts on `none`) | `SharedTestOK`: the record of each contract names no function of the class `boolean` (`sharedTestFailure_none_iff`) | The requirement of [RG1009], over the recorded contract of a declaration. It accepts a declaration with no recorded contract, and it refuses the record of a decision registration that names one test. `declarationFailure` runs it after the recorded refusals of the contract. |
| `RegulaPolicy.boundaryFailures`, `executionFailureRecords`, `executionFindings` (accept on `#[]`) | `BoundaryOK`, `ExecutionOK` | [RG3001], [RG3002], for one supplied boundary and for an admitted inventory. |
| `RegulaPolicy.Intent.hasIntentSection`, `RegulaPolicy.materialDocumentationFailure` | `IntentSection`, `MaterialDocumentationOK` | [RG5002], [RG5003]. |
| `RegulaPolicy.ModuleHeader.failures`, `RegulaPolicy.Community.failures` (accept on `[]`) | `ModuleHeader.OK`, `Conforming` | [RG5001], [RG2006]. |
| `admitSnapshot`, `admitClaim`, `admitInventory`, `admitExecution`, `admitJobKey`, `admitInfrastructureOrigin`, `admitIdentity`, `admitToolchainOrigin`, `admitToolchainAxioms`, `Compiler.admitCapability`, and the scope admission `admitScopeImpl` (accept on `.ok`) | The validity relation each names (`Snapshot.Valid`, `ClaimCandidate.Valid`, `InventoryValid`, `ExecutionValid` and so on) | Admission of decoded records. Which value is returned is each function's `_exact` theorem. |
| `Compiler.accepts` | `Compiler.Supports` | The compiler-identity guard. |
| `Regula.Checker.Frontend.coordinateCheck` (accepts on `.ok`) | `CoordinatesAgree` | Transcript coordinates, checked before inventory admission (`checked_scope`). |
| The spelling parsers `DeclarationKind.parse?`, `BoundaryKind.parse?`, `Correspondence.parse?`, `FoundationClass.parse?`, `ConformingProfile.parse?`, `ExecutionClaim.parse?`, `EvidenceMode.parse?`, `Safety.parse?`, `Reducibility.parse?`, `RecursionOrigin.parse?`, `DecisionKind.parse?`, `DecisionResult.parse?`, `EvaluatorRole.parse?`, `Profile.parse?` and `RuleId.parse?` | The text is the spelling of a value (`roundtrip`, `canonical`) | Transport of closed vocabularies. |
| `RegulaPolicy.DecisionKind.ofStructureName?` | The name is a kind's structure | Reading a registration's kind ([RG1007]). |
| `RegulaPolicy.Erasure.reproduces` | `Erasure.Reproduction`: the observing pass finished, the regeneration added a definition, and each value is related by `Erasure.EqualWithin` to the observed value of its name | The recursion-helper comparison of [RG1006], over the two values and the recorded observations of their terms ([below](#the-recursion-helper-comparison-decision-and-observing-pass)). |
| `Regula.JsonAgreement.agrees` | `JsonAgreement.Agree` (`agrees_iff`). The two values have one constructor and equal scalars. The elements of two arrays agree in order. Two objects have the same number of members. Each member of the first is found by its name in the second, with a value that it agrees with. | The comparison of an input with the encoding of the decoded value ([below](#the-diagnostic-and-policy-codecs-decisions-and-observing-pass)). |
| `Regula.JsonAgreement.canonical` (accepts on `.ok`) | The reader returns a value, and the input agrees with the encoding of that value (`canonical_eq_ok_iff`). | The decoders `DiagnosticCodec.parseLocation` and `parseDiagnostic`. The reader and the encoder are arguments, so the kind is about each reader and each encoder. |
| `Regula.Checker.PolicyCodec.exactFields` (accepts on `.ok`) | `ExactFields` (`exactFields_iff`). The value is an object, and its member names are the expected names in some order. | The decoders of the worker protocol and of the producer reports. The proof that the expected names are distinct is an argument of the function. |
| `Regula.Checker.Lake.auditMarkerNeeded` (accepts on `true`) | A package is not `PackageShape.Plain`, or some entry is not `ModuleEntry.Resolved` or has `Regula.Linter` among its imports (`auditMarkerNeeded_iff`). | The choice of the `lake lint` driver's claimed build, with or without the audit-build marker, when the owner passes `--ordinary-lakefiles` ([acceptance boundary](#the-acceptance-boundary)). The shape of each package is read from the configuration of Lake and from its compiled configuration file. Each entry is a module of the root package with its source files and the modules that Lake's `transImports` facet reports it imports (`markerInputs`). That `Regula.Linter` is the only reader of the marker in Regula is by inspection. That no module of the project reads the marker itself is an assumption. |
| `Regula.Checker.Documentation.scanLines`, `scanVersoLines` (accept on a result with no violation) | `Clean`, `VersoClean`: the lines are a run of transitions from the first line to the end of the document. The fence protocol permits each transition, and each keeps the shape rule (`scanLines_problems_eq_empty_iff`, `scanVersoLines_problems_eq_empty_iff`). | The fence protocol and the shape rule of [RG4001] ([below](#the-fence-scanners-decisions-and-observing-pass)). The input is a `Source`: a document with the lines of its text. The kinds say nothing about the fences of a result. |
| `Regula.Checker.Admission.checkHeader` (accepts on `.ok ()`) | `HeaderOK` (`checkHeader_eq_ok_iff`). Each replayed or reported module lists its constants under their own names. No module of the replay base imports a replayed module. | The decision on the header of [RG2005] ([below](#receipt-validation-decisions-and-observing-pass)). |
| `Regula.Checker.Admission.checkTable` (accepts on `.ok ()`) | `TableWithin` (`checkTable_eq_ok_iff`). Each axiom that `collectAxioms` gives for a declaration is an axiom that the declaration reaches in the replayed kernel. | The decision on the axiom tables of [RG2005] ([below](#receipt-validation-decisions-and-observing-pass)). |
| `RegulaPolicy.ExecutionWalk.walk` (accepts on `.ok`) | `Recorded` (`walk_ok`, `walk_complete`, `walk_recorded`). Each name that the edges of the records reach from the root has a record. | The walk of an execution root of [RG3001] and [RG3002] ([below](#root-and-closure-discovery-decision-and-observing-pass)). The visits are exactly the reached names (`walk_sound`, `walk_complete`). |
| `RegulaPolicy.MentionSearch.search` (accepts on a route) | `Found` (`found_of_search`, `search_complete`). A constant that the term mentions leads to a target through the records. | Contract recognition and reach of [RG1007] ([below](#contract-recognition-and-reach-decision-and-observing-pass)). A returned route follows the records (`search_sound`). |
| `RegulaPolicy.StatementReading.reads` (accepts on `true`) | `Read` (`reads_iff`). The reading of a statement follows the constant from the record of the constant that mentions it. It does not follow a projection of the input type back to it. | What [RG1009] follows from the specification and the acceptance predicate ([below](#the-reading-of-a-statement-decision-and-observing-pass)). The closure over the records is exact (`reading_some`). |
| `Regula.SourceTexts.intern` | One `sourceTexts` member, `null`, and string `sourceText` members (`intern_isOk_iff`) | Writing a result document. |
| `Regula.Markdown.documentErrors`, `Regula.Markdown.siteLinkErrors`, `Regula.Prose.bareMentions`, `Regula.Site.linkErrors`, `Regula.Site.missingAnchors`, `Regula.Site.rowsMismatch` | Their `_nil_iff` and `_eq_none_iff` relations | The rule-ID checks of Markdown and of the rendered standard, and the site's link, anchor and checklist checks. `siteLinkErrors` is the check of the links of the root `README.md` to the rule-reference site. |
| `Regula.Controlled.parse` | The text is the text that `write` gives for a vocabulary (`parse_write`, `write_of_parse`). A vocabulary is a draft with `Draft.WellFormed` (`Draft.defects_nil_iff`). | The vocabulary `CONTEXT.md` (check C9) of the [writing rules](writing.md). The file system gives the text. |
| `Regula.Controlled.untracked`, `Regula.Controlled.adopt` | Each source path is a tracked path of the repository of its row. `adopt` accepts two vocabularies if, and only if, three conditions are correct (`checked_adopt`). The vocabulary of the project has the line `Shared vocabulary:`. The vocabulary of the package does not have that line. The rows of the project and the `Shared` tables of the package together have `Draft.WellFormed`. | The other parts of check C9. Git gives the tracked paths. |
| `Regula.Controlled.longSentences`, `longSteps`, `longParagraphs`, `semicolons`, `contractions`, `replacedNames`, `replacedWords`, `abbreviations` (accept on `[]`) | `ShortSentences`, `ShortSteps`, `ShortParagraphs`, `NoSemicolon`, `NoContraction`, `NoReplacedName`, `NoReplacedWord`, `NoAbbreviation`. Each statement is about the blocks (`Blocks`) and the sentences (`Divided`) of the pieces. The statements of C5 to C8 use the form of a word (`Normal`). | The checks C1 to C8 of the prose of a Markdown document. The md4c reader gives the pieces, and that reader has no theorem. |
| `Regula.Controlled.Baseline.parse`, `Regula.Controlled.gate`, `Regula.Controlled.ratchet` (the last two accept on `[]`) | The text is the text that `Baseline.write` gives for a baseline. `Observed.Admitted` is correct for each document. `Baseline.Documented` is correct: each entry has a document. `Shrinks` is correct in relation to the baseline of the base revision, or to the documents of a base revision that has no baseline. | The baseline `prose-baseline.json` and the checks B1 and B2 of the [writing rules](writing.md). The md4c reader gives the pieces from which the functions of C1 to C8 count the tallies, and that reader has no theorem. `shasum` gives the digests. Git and the file system give the two baselines and the text of each document, also for the base revision. |
| `Regula.Controlled.baseOf` | `Start.Base` gives a base revision for the start of the check and for the data that Git gives. | The base revision of check B2. Git gives the parents of the commit, the commit of a name and the merge base, and the workflow gives the start. |
| `RegulaQualification.evaluate`, `validateDecoded`, `Registry.validate`, `Native.validate`, `Launcher.equivalent` | `Satisfied` and their `_exact` relations | Qualification evidence. |
| `AuditApp.admit`, `AuditApp.grant`, `AuditApp.runChecked` | Positive capacity, a free slot, `Fits` | The example application (standard §3.7). |
| `RegulaProvision.mathlibStep` (accepts on `.keep`), `component?`, `retires`, `mathlibApplies` | The path already links the shared checkout (`mathlibStep_keep_iff`); the text is one path component (`IsComponent`, which `isComponent_iff` connects to the test `isComponent`); a registered link still links its shared directory, is the copy's retired link and is not the link the run provisions (`retires_iff`); the root and integration toolchain selectors are equal (`mathlibApplies_iff`) | Local provisioning: keeping Mathlib's link, admitting directory names as single path components, retiring registered links, and the integration preflight. |
| `RegulaVerification.parseMode`, `select` | The argument list of a supported invocation (`parseMode_sound`, `parseMode_roundtrip`, and `select_exact` for `select`) | Argument selection of `scripts/verify.sh`. `select` returns the mode with the proof that the arguments are that mode's, so its kind is stated about `Regula.Dependent.isSome select`. |
| `accept`, `finalize` (accept on `.ok`) | `CompleteFor` with `AllPolicyOK`; `InputsOK` (`accept_iff`, `finalize_iff`) | Acceptance of a result table and of a response sequence, for every claim, census, plan and role receipt. The type of each argument depends on an earlier one and the result type on all of them, so each kind is stated about `Regula.Dependent.isOk` of the function on a structure whose fields are the five arguments (`AcceptInput`, `FinalizeInput`). The witnesses are over `witnessPlan`, the plan of a documentation claim with no environment: the table collected from one completed observation of each of its three jobs is accepted, and the empty table and the empty response sequence are refused. |
| `admitPlan` (accepts on `.ok`) | `PlanJobsOK`: the proof fields of `Plan` (`admitPlan_isOk_iff`) | Plan admission, for every claim and census, on the structure of the three arguments (`PlanInput`). It accepts the three required jobs of `witnessPlan` and refuses no jobs. |
| `ResultState.insertResult`, `ResultState.collect`, `admitIndexedResults` (accept on `.ok`) | `InsertOK`, `BatchOK`, `IndexedResultsOK` (`insertResult_success_iff`, `collect_success_iff`, `admitIndexedResults_ok_iff`) | Result admission, for every key type, payload type, order, required set and binding relation: the types and instances are fields of the structure of the arguments (`InsertInput`, `CollectInput`, `IndexedResultsInput`). The first two are stated at their own universe parameters, with witnesses over the one-point type `PUnit`; the third takes a payload type of `Type`, with witnesses over `Unit`. |
| `policyFor`, `memberFailure`, `Regula.Linter.editorDecisionImpl` (accept on `none`) | `DeclarationOK` and `DecisionOK` under the inventory's own roles, together with membership in the inventory for `policyFor` (`policyFor_none_iff`); the other two take the membership proof as an argument, and the specification of the editor decision is `DeclarationOK` alone, since the editor does not decide the decision requirement | The public declaration decision of [RG1001]–[RG1009] for an inventory, its member-indexed form, and the editor's. The type of the roles depends on the inventory, and the membership proof of the last two on both, so each is decided on a structure of its arguments (`PolicyInput`, `MemberInput`). The witnesses are over `witnessInventory`, the inventory of one recorded declaration: an axiom-free definition passes under Kernel-only, and an authored axiom, or a declaration of another inventory, does not. |
| `policyForName`, `recordFailure` (accept on `none`) | `DeclarationOK` and `DecisionOK` on the inventory's record with the name (`policyForName_none_iff`), and membership of a supplied record in the inventory (`recordFailure_none_iff`) | The policy decision keyed by a declaration's identity and the admission boundary of a supplied record, which `policyFor` composes (`policyFor_eq`, `policyFor_of_mem`). `policyForName` is decided on a structure of its arguments (`NameInput`). The witnesses are over `witnessInventory`. Its definition's name passes the decision and a name it lacks does not. Its own record passes the boundary and the axiom record of the same name does not. |
| `admitBoundaryEvidence` (accepts on `.ok`) | `BoundaryFieldsOK`: the fields are those of some evidence of the kind (`boundaryEvidence_admission_preserves`, `boundaryEvidence_roundtrip`) | Admission of a boundary's correspondence fields ([RG3001], [RG3002]), on the structure of the four arguments (`BoundaryFields`). The result type depends on the boundary kind. |
| `FieldPacking.covers` | `FieldPacking.Covers`: one constructor, no index, and the arguments are the fields, each once and in order (`FieldPacking.covers_iff`) | Whether a decision registration's statement applies its implementation to every argument ([RG1007]). It accepts a type with one constructor, no index and two fields given in order, and refuses a type with one constructor, one index and its one field given. The collector's reading of those numbers from Lean's declarations is not part of this kind. |
| `DecidedFunction.covers` | `DecidedFunction.Covers`: a field application covers (`FieldPacking.Covers`), and the number of arguments that a result takes is zero (`DecidedFunction.covers_iff`) | Whether a decision registration's statement is about its implementation on every argument ([RG1007]). It accepts the function itself when no result takes an argument, and refuses it when a result takes one more, which is a kind about a partially applied function. The collector's reading of that number from the kind's result type is not part of this kind. |
| `Regula.Website.admitExampleRequest`, `admitExampleSources`, `admitDemonstration` (accept on `.ok`) | The observed request is the frozen one; `ExampleSourcesOK`; `DemonstrationOK` | Admission of a rule-example producer's request, sources and diagnostic demonstration. Each returns the admitted value with its proof, so each result type depends on the arguments. The first and the third are decided on the pair of their two arguments, and the second on the structure of its three (`ExampleSourcesInput`). |
| `RegulaVerification.passed` | Each command of a step ended with exit status 0 (`passed_iff`). | The driver of `scripts/verify.sh` uses it before it operates one more command, before its success line and before it moves the acceptance record. |
| `RegulaVerification.walked` | The path does not start with `tmp`, and no component of it is `.git`, `.lake`, `.cache` or `.regula-scratch` (`walked_iff`). | The files that the driver copies for the first acceptance step. No theorem relates it to the rule of the isolated copy of the checker. |
| `RegulaVerification.removal` (accepts on `.remove`) | A directory is at the place by a read that follows no link, and its real path is the place (`removal_remove_iff`). | The driver removes its copy and the `_site` directory only by this decision. The two reads of the file system are trusted. |
| `RegulaVerification.prebuildCovers` | The surface manifest has the shape that `claimedTargets` reads, and each target it claims is in `gateTargets` (`prebuildCovers_iff`). | The driver runs the first acceptance step only on such a manifest. Thus the gate does not build a claimed target beside the step's build. No theorem relates `claimedTargets` to the manifest reader of the checker. |
| `ScratchCopy.name?` (accepts on `some`) | The path is the scratch area, then one name, then `project` (`name?_eq_some_iff`). | The gate admits a copy of the driver only at such a path. The components come from real paths, which the file system gives. |
| `ScratchCopy.inside` | The path is the directory with one or more components after it (`inside_iff`). | The gate requires its own executable in the build directory of a copy of the driver. |

Sound only, each a declared choice:

| Decision | Specification | Left open, and why |
| --- | --- | --- |
| `Regula.SharedExecution.same` | The two values are equal (`same_eq`) | That it accepts every pair of equal values is not proved, and nothing depends on it. The equality is `=`: two objects with the same members whose trees are balanced differently are different values, which `same` refuses and Lean's runtime `Json` comparison identifies. |
| `Regula.Checker.Admission.checkCopies` | Every copy is `CopyAdmitted` (`checkCopies_sound`) | It may refuse admissible copies: the search for a proof's axioms is bounded by fuel, and a refusal fails closed ([RG2005]). |
| `Regula.Checker.Admission.admitReplay` (accepts on `.ok`) | `AdmitOK` (`admitReplay_eq_ok`). Each copy is `CopyAdmitted`, and the replayed kernel holds a constant under the name of each required key. The receipt is the receipt of the request. | Completeness. It runs `checkCopies`, which bounds the search for a proof's axioms by fuel, so a refusal fails closed ([RG2005]). |
| `RegulaPolicy.NativeStatement.recognize?` (accepts on `some`) | `NativeStatement.Stated`: the type is the statement of the tactic under the prefix (`asserted?_sound`) | Completeness for `bv_decide` has the hypothesis `RuntimeStringAppend` (`asserted?_complete`), and a kind has no hypothesis. A refusal fails closed ([RG1004]). The result holds the proof about the candidate, so the kind is about `Regula.Dependent.isSome recognize?`. |
| `Regula.Checker.ProducerReport.Environment.validate` | `Admissible` (`validate_sound`) | It may refuse an admissible report; `validate_eq_ok` is two-way against the guard Booleans, not against `Admissible`. |
| `RegulaProvision.admits` | `Admitted`: the receipt records the requested revision and compiler, zero artifact policy and empty source, and holds no package at another revision than a pin (`admits_sound`) | It refuses an `Admitted` receipt of another schema version. |
| `RegulaProvision.cloneStep` (accepts on `.replace`), `found` (accepts on a result other than `.foreign`), `prunes` | The path is a link or a clean Git checkout (`cloneStep_replace`); the directory's receipt names it (`found_identified`); the directory is not the current one and no registered copy links it (`prunes_sound`) | `cloneStep` keeps a clean checkout at the pinned revision; the program states no converse for the other two. |
| `RegulaVerification.dependencyFree` | The lock manifest's `packages` array is present and empty (`dependencyFree_packages`) | The driver states no converse. |

Complete only. A sound kind requires an input the function accepts, with a proof:

| Decision | Specification | Why the kind is one-way, and what covers soundness |
| --- | --- | --- |
| `Regula.RegistryCodec.parseMode`, `parseRule`, `parseName`, `parsePrintedNameJson`, `RegulaPolicy.Codec.parseName`, `parseIdentity`, `Regula.SourceTexts.expand`, `Regula.SharedExecution.read` | The input is a form its writer writes (their `_roundtrip` theorems, `expand_intern`, `read_write`) | No theorem says a reader accepts only written forms, so each may accept a value its writer does not write. |
| `nativeAxiomOrigin?`, `compilerTrustingAxiomName` | A generated native-axiom name, where `RuntimeStringAppend` holds (and, for the second, an enabled legacy compiler axiom) | Soundness holds with no hypothesis (`nativeAxiomOrigin?_sound`, `compilerTrustingAxiomName_sound`), but accepting a generated name evaluates `String.Internal.append`, an `extern` that no kernel proof evaluates. The hypothesis is part of the specification; that the runtime satisfies it is trusted. |
| `Regula.DiagnosticCodec.parseLocation`, `parseDiagnostic` (accept on `.ok`) | `LocationWire`, `FindingWire`: the object has the members of a location, or of a finding, and each member has its meaning (`parseLocation_of_wire`, `parseDiagnostic_of_wire`) | The converse is proved for an input with search trees as its object trees (`parseLocation_wire`, `parseDiagnostic_wire`). It is false for some other `Json` values: the decoder accepts the object tree of [#269](https://github.com/rbeauchamp/regula/issues/269), which has no member `remedy`. |
| `matchesPattern`, `Regula.Checker.Manifest.parseValue`, `RegulaQualification.Evidence.validate`, `Evidence.validateDocumentation` | `PatternMatch`; the value encodes a valid manifest; the decoded requirements hold | Soundness is proved (`matchesPattern_iff`, `parseValue_ok`, the registered equivalences `checked_validation` and `checked_documentation`), but every acceptance evaluates `String.splitOn`, `String.contains` or a JSON object lookup that the kernel does not reduce. Accepted inputs are observed by the fence corpus, this repository's manifest and the qualification campaigns. |
| `RegulaQualification.History.validate`, `Producer.validate` | The decoded requirements hold | Soundness is proved (the registered equivalences `checked_validation`), but an accepted report is a result document that only an audit produces. Accepted reports are observed by the `history` and `producers` diagnostics. |

Decisions with no kind, and what stands instead:

| Decision | Why no kind applies | Evidence that stands |
| --- | --- | --- |
| `Regula.Checker.Admission.checkProof` | Its theorem is soundness, and a sound kind requires an accepted input; it succeeds only after `checkRenamed`, which asks Lean's kernel to accept a declaration, and no proof evaluates that call. | `checkProof_ok`, and the kind of `checkCopies`, which calls it. |
| `Regula.Checker.Manifest.parse` | It adds the JSON text parser, about which nothing is proved, so only soundness is stated, and an accepted input would evaluate that parser. | `parse_sound`, and the kind of `parseValue`, the stage it runs after parsing. |
| `Regula.SharedExecution.restore?` | Its writer `internValue` chooses a written form by running the reader (`recovers`), so "a form the writer writes" is stated through `restore?` itself, and a kind's specification must not mention its implementation. | `restore?_internValue`, which holds for every value and proposal list, and the kind of `read`, the document reader that calls it. |
| `labelOf`, `foundationFor`, `authorizedNativeAxioms`, `authorizedUnsafeRecHelpers`, `DefeqComparison.classify`, `DefeqComparison.ofAttempt`, `Regula.Checker.Lint.classify` | These classify into several classes or select a set; they do not accept or refuse an input. | Their exact-value theorems (`labelOf_iff`, `foundationFor_iff`, the `authorized…_iff` theorems, `classify_checked_iff` and its companions, `ofAttempt_checked_iff` and its companions, `ClassifyContract`). |
| The other registered contracts (`checked_request`, `checked_rule`, `checked_subject`, `checked_account`, `checked_summary`, `checked_executionFailures` and the census assembly contracts) | Each fixes a computed value, such as a rendered line or an assembled record, not a verdict. `checked_executionFailures` renders `executionFindings`, which has a kind. | The registered requirement, reported with no kind. |
| `RegulaProvision.isObjectName`, `isComponent` | `isObjectName` defines the written form that it admits, and no separate relation is stated for it. `IsComponent` states a path component over the text and its characters. The text is not empty. It does not start with a period. Each character is an ASCII letter, an ASCII digit, `-`, `_` or `.`. The theorem `isComponent_iff` connects it to the test `isComponent`. | `IsComponent` is the specification of the kind of `component?`. A reviewer examines if the written forms are the intended ones. |

**Inputs with a proof field.** Issue [#270](https://github.com/rbeauchamp/regula/issues/270)
changed how [RG1009] reads a specification over an input with a proof field. It asks which
registrations of Regula with no kind take such an input, and if a kind is now possible for each.
A probe of the collector read the 57 modules of Regula that hold registrations:

- There are 133 registrations, 110 with a kind and 23 with no kind. No record of the 110 names a
  shared test, or a test shared only through the input type.
- 11 of the 23 take an input with a proof field.
- 4 of the 11 stand beside a kinded registration of the same function, which the two readings
  accept: `editorDecisionImpl`, `admitScopeImpl`, `memberFailure` and `operationalFailure`.
- 5 of the 11 are no decisions: `accountImpl`, `executionFailuresImpl`, `subjectImpl`,
  `memberFoundation` and `executionSummary`.
- 2 of the 11 have no kind for reasons that #270 does not change. The proof field of
  `editorRequestImpl` is `String.isValidUTF8` of Lean's own library, which no reading follows.
  `ruleForMemberImpl` selects a rule, and it reduces to `memberFailure`, which has a kind.

So this change makes no new kind of Regula possible. Before it, [RG1009] refused no kind of
Regula for this reason. Which registrations have no kind does not depend on the reading.

The probe ran on the first, broader reading of this change. The final reading reads the other
side as before #270. That is the implementation by the rule of a function and the acceptance
predicate by the rule of a statement. The rule reach `withTypes` of the specification reaches at
most what the specification reached before #270. So each test that the final reading shares, by
the reading or by the rule, the search shared before #270.

The `main` branch accepted the 109 kinded registrations that it has. So none of them names a
shared test or a test shared only through the input type. This change adds one more,
`RegulaPolicy.StatementReading.reads` with the kind `checked_reads`. Its acceptance predicate
`(· = true)` reaches nothing outside Lean's own library. The acceptance check of this change
claims `RegulaPolicy`, so it decides [RG1009] for that registration too.

### Decisions not registered with `regula_decision`

Every decision of the three tables with a kind is registered with `@[regula_decision]`, so
[RG1008] requires its contract. They are functions of `RegulaPolicy`, `RegulaCore`,
`RegulaQualification`, `AuditApp`, `RegulaProvision`, `RegulaVerification` and the excluded
`Regula` library, where the `self-audit` diagnostic decides the rule. The functions below are
registered from another module of their library, with
`attribute [regula_decision]` beside their contracts, because the module that declares them
imports only the toolchain:

- `RegulaPolicy.Compiler` imports only `Init`, because the compiler guard elaborates it alone
  before the package is built, so `RegulaPolicy.Claim` registers `Compiler.accepts` and
  `Compiler.admitCapability`.
- Each standalone program runs with `lean --run` before the package is built, so its library has
  a second module that imports the program with `Regula.Contract` and `Regula.Decision`, and that
  no program imports: `RegulaProvision.Decisions` registers `component?`, `admits`, `mathlibStep`, `cloneStep`, `found`, `prunes`, `retires` and
  `mathlibApplies`;
  `RegulaVerification.Decisions` registers `parseMode`, `dependencyFree`, `select`, `passed`,
  `walked`, `removal` and `prebuildCovers`.
  Each kind restates a theorem the program proves about the same definition, except that of
  `component?` (`checked_component`).

Deleting one of those contracts, such as `checked_compilerAccepts` or `checked_admits`, is then
rejected under [RG1008] like any other registered decision's contract. The decisions below carry
no registration. A registration is a requirement that the function has a decision contract or a
`Decidable` result, so registering a function that can have neither would only make the rule fail.

| Decision | Why it is not registered | What stands instead |
| --- | --- | --- |
| Every decision of the table "Decisions with no kind" above | None has a decision kind, for the reason that table gives for each, and none returns `Decidable _`. | The evidence that table names for each. |

A registered function can have a second registration, of an ordinary requirement that states more
than its kind does, and the account reports both. Among the functions decided on a structure of
their arguments these are `memberFailure`
(`checked_memberFailure`, equality with `policyFor`), `Regula.Linter.editorDecisionImpl`
(`checked_editorDecision`, which outcome each failure gives) and `admitIndexedResults`
(`checked_indexedResults`, which array is returned).

Two registrations moved so that each registered function has its contract in its own library, the
inventory [RG1008] reads: the contract of `RuleId.parse?` from `Regula.RegistryCodec` to
`RegulaCore.RuleId` (`RuleId.checked_parse`), and that of `RegulaPolicy.Community.failures` from
`RegulaCore.Assembly` to `RegulaPolicy.Claim`, a file of its own library in which its two
witnesses reduce. Their requirements and proofs are unchanged.

A registration is kept by the module that writes it (`Regula.decisionExtension`), and the
collector reads the registrations of every module the audited environment loaded, once for the
environment (`Regula.decisionRegistrations`), so a function registered from another module of its
inventory has the same requirement as one registered where it is declared. Lean's own tag attribute refuses a
declaration of an imported module, so the registration has its own extension, and nothing in it
knows which declarations an audit owns. That is decided where the inventory is built: an audit
stops without a verdict on a registration that one of its modules writes for a declaration outside
its inventory (`Regula.Collect.ownedDecisionRegistrations`,
`Fixtures.Mutations.DecisionForeignRegistration`), since it records no declaration to decide the
requirement for. Reading the registrations and that check are operational, not proved; the
decision over the recorded declarations is (`policyFor_decisionContract_iff`). The self-test's
structural partition observes the reading in a project of two modules, one declaring a function
and the other registering it: the audit reports the function under [RG1008] while no contract
decides it and accepts it, recorded as registered, with the contract. It runs both for plain
files and for `module`s, where the registering module imports the declaring one privately, so
Lean saves the registration with that module's private data.

In a project audit a registration also counts the decision contracts of each claimed surface that
names its surface in `decides`. Thus a library that imports only the toolchain and
`Regula.Decision` can hold the function, and a library with a proof dependency can state its kind.
In a file that is a `module`, that import can be `meta import Regula.Decision`, an
elaboration-time import.

The census binds the counted contracts of each inventory to the records of those environments in
the same run. It counts a record only if the other environment loaded the module of the function
with the same origin. `census_decided_iff` states the decided implementations over exactly those records.
`accepted_counted_judgment` proves that each counted registration met its own requirements in its
own environment of the accepted run.

The relation is configuration, and the parser refuses one that names its own surface or no claimed
surface (`Manifest.parse_relations`). The structural partition observes the decision in a project
of two libraries. The first library marks a function, and only the second library has its
contract. With the relation the audit accepts the function, and the account names the surface of
the contract. Without the relation, or with the relation and with no contract, the audit reports
it under [RG1008].

`@[regula_decision]` is applied after compilation. Lean applies an
attribute of the earlier application time to the `_unary` or `_mutual` definition it generates
for a function defined by well-founded recursion too, as `Regula.SharedExecution.same` is, and
that definition is not the function the project registered. Applied after compilation, the
registration is on the declaration that carries the attribute and on no other; that is Lean's
behaviour (`addNonRec` with `applyAttrAfterCompilation := false`), read from its source and
observed by the fixtures, not proved. The policy therefore has no exemption: every registered
declaration has the requirement (`DecisionOK`), including a structure projection a project
registers explicitly and a declaration whose
[generated-from relation](#generated-declaration-families) a project wrote
(`Fixtures.Mutations.DecisionProjection`, `Fixtures.Mutations.DecisionForgedAttribution`).

### The recursion-helper comparison: decision and observing pass

A producer that runs in `MetaM` or `IO` is not a pure decision and has no kind. The comparison of
[RG1006], which decides whether a regenerated definition is the observed one up to compilation
erasure, is split into an observing pass and a pure decision that has one.

- **The decision** is `RegulaPolicy.Erasure.reproduces`, a pure, total function of the claimed
  policy library ([`RegulaPolicy/Erasure.lean`](../../lean/RegulaPolicy/Erasure.lean)). Its one
  argument, `Erasure.Regeneration`, holds, for each definition a regeneration added, its value and
  the value of the observed definition of its name (or that the inspected environment holds
  none), the `Erasure.Observations` of the terms of each side, and `finished`, what the observing
  pass reports of its own run. It takes nothing else: no environment, reducibility status,
  attribute, matcher record or termination argument is among its arguments, so whatever selected
  the regeneration cannot enter the decision without a change of that signature. It is registered
  with `@[regula_decision]`, `Erasure.checked_reproduces` registers the kind `Regula.Decides`, and
  the collector takes the verdict from `checked_reproduces.run` (`Collect.regenerationMatches`).
- **The observing pass** is `Collect.observeEqual` with `Collect.observe`, in `MetaM`. It takes the
  comparison's own steps (`Erasure.step`) in the comparison's order and, where a step asks for an
  observation it was not given (`Erasure.Need`), records it: whether a term is a proof or a type
  (`Meta.isProof`, `Meta.isType`), a fresh variable for a binder, or a decomposition of a `match`
  application whose threading law Lean's kernel checked (`Collect.threadingLawChecked`). The pass
  holds no comparison rule, and an observation of a term never reads the other side's term. What
  the pass returns says whether it finished: `false` where it stopped at a part the comparison
  refuses, at exhausted depth, or at its bound on the observations one step may ask for
  (`Collect.stepNeeds`, 1,000,000). The decision takes that answer as `Regeneration.finished` and
  refuses a pass that did not finish, and it also refuses whatever the pass left unobserved.

**Proved**, about `Erasure.equalWithin` and `Erasure.reproduces`, the functions the collector runs
(kernel-checked in the claimed library, with `propext` and `Quot.sound` only):

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| Exact relation | `Erasure.equalWithin_iff` | For every two terms, pairing of variables, depth and pair of observations, the executed comparison answers `true` exactly when `Erasure.EqualWithin` relates the terms within that depth. |
| The registered decision | `Erasure.reproduces_iff`, `Erasure.checked_reproduces` | `reproduces` accepts exactly a regeneration whose pass finished, that added a definition, and whose every value is related, within `Erasure.depthLimit` (100000), to the observed value of its name. It accepts one whose two values are erased and refuses one that added no definition. |
| A pass that stops is refused | `Erasure.reproduces_eq_false_of_unfinished` | A regeneration whose `finished` is `false` is refused, whatever the pass recorded: a bound, exhausted depth or a refused part cannot be followed by an acceptance. It does not prove that the pass reports its own run truthfully. |
| One constructor for each rule | The constructors of `Erasure.EqualWithin` | `closed` (Lean's expression equality, no free variable), `erased` (both a proof or a type), `mdataLeft`, `mdataRight`, `fvar`, `const`, `lit`, `sort`, `proj`, `fixpoint` (the arguments of a well-founded fixpoint that carry its computation, `Erasure.Fixpoint`), `threadedLeft` and `threadedRight` (a `match` that passes a variable through against the direct one, only under a recorded kernel-checked law, `Erasure.Threads`), `app`, `lam`, `forallE` and `letE`. A new case of `Erasure.step`, `Erasure.structural` or `Erasure.application` without a constructor, or a constructor without its case, makes `equalWithin_iff` fail to check. The two threading rules name `threadedParts` and not the parts themselves, so a change of which parts it selects adds no constructor; it fails `Erasure.threadedParts_eq_ok_iff` and `Erasure.alternative_eq_ok_iff`, which state the selection, and a change of the pairs under which the further variable stands for the passed one fails `Erasure.mem_standingFor_left` and `Erasure.mem_standingFor_right`. A change inside another definition the relation shares with the comparison fails a theorem only where one states the changed part: the row "What the relation shares with the comparison" says which. |
| The parts of a fixpoint | `Erasure.Fixpoint`, `Erasure.fixpointArguments?_eq_some_iff`, `Erasure.fixpointArguments?_eq_none_iff` | The `fixpoint` rule states which arguments it compares without the executed selection: the domain, the motive, the functional and the arguments after it of `WellFounded.fix` or `WellFounded.Nat.fix`. The executed `fixpointArguments?` selects exactly those, so a change of the selection fails these theorems. The rule does not compare the combinator or its universe levels: an application of `WellFounded.fix` is related to one of `WellFounded.Nat.fix` with equal such arguments, as the comparison on `main` did. |
| A variable stands for one binder | `Erasure.newVariables`, `Erasure.NewVariables`, `Erasure.newVariables_iff`, `Erasure.newVariables_eq_true_iff`, `Erasure.unpaired_eq_true_iff`, `Erasure.under_eq_ok_iff`, `Erasure.under_eq_error_of_reused`, `Erasure.alternative_eq_ok_iff`, `Erasure.alternative_eq_error_of_reused`, `Erasure.alternative_eq_error_of_unpaired`, `Erasure.threadedParts_eq_ok_iff`, `Erasure.unpaired_push`, `Erasure.alternative_holds`, `Erasure.step_keeps_pairs`, `Erasure.Reached.newVariables_eq_false` | A binder rule and each alternative of a threaded `match` read a body only with variables that no pair holds, on either side, and that differ from each other (`newVariables_eq_true_iff` and `unpaired_eq_true_iff` state that test exactly). The binder rules of the relation name the proposition `NewVariables`, and `newVariables_iff` connects it to the test. A binder whose variable is not new is refused, whatever `Observations.bound` answers. For a threaded pair the two threading rules take their parts from `threadedParts`; `threadedParts_eq_ok_iff` proves that those parts are the kept arguments position by position and then one part of `alternative` for every alternative, and `alternative_eq_ok_iff` that each such part is read with new variables. Those theorems are the test of one rule against the pairs it is given. For a path, three more hold. The part for a body holds, in a pair, each variable the body is read with (`unpaired_push` for a binder rule, `alternative_holds` for an alternative). For the further variable of an alternative that is so because `alternative` refuses a passed variable that no pair holds (`alternative_eq_error_of_unpaired`): its pairs are those of the passed variable. Every part of a step keeps the pairs of the step (`step_keeps_pairs`). So a variable that a pair holds at one part is not new at any part the comparison comes to from it (`Reached.newVariables_eq_false`, over `Erasure.Reached`: a part, and each part of a step from a part it comes to), and no answer of the pass makes the relation pair one variable with two binders on one path, as `fun a b => a` against `fun a b => b` would need. This is about the binders the comparison opens. A free variable of the two values it starts from is in no pair; a regenerated or observed value has none. |
| Outside `closed`, unobserved is refused, and so is an erased term against a kept one | `Erasure.equalWithin_unobserved_left`, `Erasure.equalWithin_unobserved_right`, `Erasure.equalWithin_erased_kept`, `Erasure.equalWithin_kept_erased` (each for two terms the `closed` rule does not relate) | A term the pass was not asked about has no observation, and no rule relates it by its erasure or its structure. A structural rule applies only where both terms are observed not to be erased, so no rule but `closed` relates an erased term to a kept one. `closed` reads no observation: it relates only two terms that Lean's expression equality identifies and that have no free variable, and for two such terms the erasure of one is the erasure of the other when the observations are truthful. That is argued, not proved: `equalWithin_iff` holds for every pair of observations. With truthful observations the relation is the standard's sentence: the two values are the same once every proof and every type of each is erased. |
| Threading pairs | `Erasure.mem_standingFor_left`, `Erasure.mem_standingFor_right` | The pairs under which the variable an alternative binds stands for the variable passed relate that variable alone, and to exactly the variables the passed one was paired with. |
| What the relation shares with the comparison | `Erasure.threadedParts_eq_ok_iff`, `Erasure.alternative_eq_ok_iff`, `Erasure.mem_standingFor_left`, `Erasure.mem_standingFor_right`, `Erasure.newVariables_eq_true_iff`, `Erasure.unpaired_eq_true_iff`, `Erasure.Side.orient_pairs`, `Erasure.pairs_of_mem_paired` | `Erasure.EqualWithin` is stated with definitions the comparison runs, so a change inside one changes the relation and the comparison together. Stated exactly, so that a change fails a theorem: when `threadedParts` and `alternative` yield parts and which; the pairs of `standingFor`; and the test of `newVariables` and of `unpaired` (no pair holds a variable, on either side, and no two variables are the same). The binder rules name the proposition `NewVariables`, and the rule of a threaded `match` names the proposition `Threading.SameLevels`. `alternative` and `under` decide `NewVariables` through its `Decidable` instance and do not call the test, so the relation names no test of the module. `Threading.SameLevels` states the two lists of levels without the level of the motive (`WithoutLevel`) and their agreement at each position (`LevelsAgree`). The theorems `newVariables_iff` and `Threading.sameLevels_iff` connect each proposition to the test that the comparison uses. Stated in part: of `Side.orient` and `paired`, only the pairs of their parts, not which term is on which side or which terms are paired. Not stated: `openLambdas` (how the leading binders of an alternative are opened), `Side.pair` (which component of a pair holds the variable of which side), and `Threading.head` (how many arguments come before the alternatives). The theorems name those three, and the relation means what they are written to compute. `Side.other` only names the side in a refusal, and no rule reads it. A change inside a shared definition, in a part that no theorem states, is a review item. |

**Hypotheses and trusted boundary.** The theorems start from the observations and the two values.
They do not prove:

- that an observation is what Lean answers. Erasure is `Meta.isProof` or `Meta.isType` of the
  term in the context of the variables the pass bound; a recorded decomposition is one for which
  `Environment.addDeclCore` accepted the threading law, where what Lean records about the applied
  constant gave the decomposition; and `finished` is what the pass reports of its own run. All are
  the pass's, and a wrong answer is a wrong observation, not a refuted theorem. The variable the
  pass gives a binder is not among these hypotheses: the comparison refuses one that is not new.
  That the pass's fresh variables are new, and that a pair holds each variable passed to a
  threaded `match` where the two values have no free variable, is argued in
  `Collect.observeEqual` and is not proved. Where either argument fails, the comparison refuses
  the pair (`Erasure.under_eq_error_of_reused`, `Erasure.alternative_eq_error_of_reused`,
  `Erasure.alternative_eq_error_of_unpaired`): the failure cannot make it accept;
- anything about Lean's own functions the comparison runs and the relation names as it runs them:
  expression equality (`Expr.eqv`), the free-variable test, `Expr.instantiate1`, the head and
  arguments of an application, and the equality of names, universe levels and literals. Several
  are implemented in C++ and have no specification to state a rule by, so the leaf rules are
  stated as those Boolean tests;
- the adequacy of the relation: that two related values compile to code that computes the same.
  That is argued, with no theorem, rule by rule: a proof or a type has no code; a well-founded
  fixpoint's relation, measure and well-foundedness proof have none either, and the rule takes the
  two fixpoint combinators as one, on the claim, which is not checked, that each computes the
  same from its domain, motive, functional and remaining arguments; the kernel-checked law makes
  a threaded `match` equal to the direct one with each alternative applied to the variable
  passed, and the alternatives are compared with the bound variable standing for it; and every
  other rule compares the same constructor part by part. For the threaded rules, which parts are
  compared is `threadedParts`, the definition the relation shares with the comparison.
  `threadedParts_eq_ok_iff` and `alternative_eq_ok_iff` state that selection as theorems about
  the definition: the kept arguments position by position, and for every alternative the two
  bodies under its opened binders, with new variables. The relation shares more definitions with
  the comparison, and no theorem states all of what each computes: the row "What the relation
  shares with the comparison" of the table above names each one and the part a theorem states. A
  change inside one, in a part that no theorem states, is a review item
  ([#199](https://github.com/rbeauchamp/regula/issues/199));
- the regeneration that supplies the values, the selection of the observed definitions by name,
  or the kernel's check of the recursion equation, which are as described under
  [editor feedback](#editor-feedback).

**What the pass reads that a project can write.** Reducibility statuses, where Lean decides
whether a term is a proof or a type: an irreducible definition can make Lean answer that a proof
or a type is neither, which sends the comparison to the structural rules or, where the other term
is erased, refuses the pair, and it cannot make Lean answer that a term with code is erased, since
a reduction step is a definitional equality under every assignment of statuses (argued from Lean's
source, not checked). And matcher and `casesOn` metadata, which gives the decomposition whose law
the kernel then checks or refuses: what the pass records is that check. Neither is an argument of
the decision.

**The counterexample that narrowed the rule.** Standard §7.4 says the two values are the same
once every proof and every type of each is erased. Until this split the comparison accepted two
terms outright only where both were erased, and where exactly one was erased it went on to compare
the two by their structure, as it does where neither is. So it accepted
`fun (h : 0 = 0) => h` against `fun (n : Nat) => n`: the binder types are both types, and the
bodies are paired variables, of which the first is a proof and the second is not. Stating the
relation exposed that case. Outside the `closed` rule, the comparison now reads the erasure of both
terms, compares structure only where compilation keeps both (`Erasure.Kept`), and refuses a pair of
which exactly one is erased (`Erasure.equalWithin_erased_kept`, `Erasure.equalWithin_kept_erased`).
`closed` is the exception because it reads no observation. It relates only two terms that Lean's
expression equality identifies and that have no free variable, and for two such terms the erasure
of one is the erasure of the other when the observations are truthful: Lean would answer alike
for both in the inspected environment, since its answer for a term with no free variable does not
depend on the variables the term is under. That is an argument, not an observation the pass made:
for two such terms the comparison asks for no observation. It is not proved, because
`equalWithin_iff` holds for every pair of observations. With truthful observations `Erasure.EqualWithin` is therefore the standard's
sentence.

What the narrowing changes is this. For one regeneration it only refuses more: a pair of values
the comparison accepts now, the earlier comparison accepted too. That does not hold for the search
over regenerations. The first regeneration the comparison accepts decides
(`Collect.unsafeRecRegeneration`): where the kernel then does not check the recursion equation,
the helper is not admitted and no other regeneration is tried. A regeneration that the earlier
comparison accepted through a pair with one erased term, and whose equation the kernel did not
check, is refused now, so the search goes on to a later regeneration, which can reproduce the base
and pass the equation check. Such a helper is admitted now and was not before, and a recorded
origin can change in the same way. What holds in every case is that each admitted helper has a
regeneration the relation accepts and a kernel-checked recursion equation for each helper of its
group. No such helper is known: the recorded origin of every recursion helper of the fixtures and
of Regula's own libraries is the same as with the earlier comparison (observed; the pull request
that made the change gives the numbers).

**Observed.** `checkerSelftest fixtures` exercises the pass and the regeneration against the pinned
toolchain: every helper of the positive recursion fixtures is admitted, each completed mutation
control rejects its forged helper, and the two bound controls
(`Fixtures.Mutations.ReducibilitySearchBoundUnsafeRecForge` and
`Fixtures.Mutations.ReducibilityFallbackBoundUnsafeRecForge`) leave theirs undecided, with the
audit incomplete. Those fixtures test this external boundary. They are not tests of the comparison
rules: the theorem proves that the executed comparison accepts exactly the related terms, and the
adequacy of the rules stays argued.

### The native-axiom statement: decision and observing pass

The producer of [RG1004] reads a generated native-proof axiom in three steps. The second step is
a pure decision with a kind.

- **The name.** `RegulaPolicy.nativeAxiomOrigin?` reads the owning prefix and the tactic from the
  name of the axiom. Its kind is in the table of the complete decisions above.
- **The decision** is `RegulaPolicy.NativeStatement.recognize?`, a pure, total function of the
  claimed policy library
  ([`RegulaPolicy/NativeStatement.lean`](../../lean/RegulaPolicy/NativeStatement.lean)). Its one
  argument, `NativeStatement.Candidate`, holds that tactic, that prefix and the kernel-checked
  type of the axiom. It takes nothing else: no environment, attribute or reducibility status is
  among its arguments. It is registered with `@[regula_decision]`, and
  `NativeStatement.checked_recognize` registers the kind `Regula.DecidesSoundly`.
  `Collect.nativeRecognition?` takes the verdict from `checked_recognize.run`.
- **The observing pass** is `Collect.replayNative`. It evaluates the recognized expression with
  compiled code, through `Meta.nativeEqTrue`, and records if the result is `true`. Its argument
  is a `NativeStatement.Recognition` of the candidate: the expression and the proof that
  `asserted?` returns it for that candidate. Thus the link from the candidate to the expression
  that the pass evaluates follows from the type of the result. Each value of that type is the
  result of the decision for that candidate, by the theorem `recognize?_eq_some`.

**Proved**, about `NativeStatement.asserted?` and `NativeStatement.recognize?`, the functions that
the collector runs. Lean's kernel checked each theorem in the claimed library, with `propext`,
`Classical.choice` and `Quot.sound` only.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| Sound, with no hypothesis | `NativeStatement.asserted?_sound`, `NativeStatement.checked_recognize` | An accepted type is the statement of the tactic under the prefix (`NativeStatement.Statement`). The returned expression is the one that the statement asserts. |
| Complete | `NativeStatement.asserted?_complete`, `NativeStatement.asserted?_eq_some_iff` | A type that is such a statement is accepted, with its expression. For `bv_decide` the theorem has the hypothesis `RuntimeStringAppend`. For the two `decide` tactics it has no hypothesis. `NativeStatement.asserted?_eq_some_iff` has that hypothesis for each tactic. |
| One constructor for each tactic | The constructors of `NativeStatement.Statement` | `nativeDecide` and `decideNative`: the type asserts `Decidable.decide p inst`. `bvDecide`: the type asserts `verifyBVExpr expr cert`, and the generator made the names of `expr` and `cert` under the same prefix (`GeneratedAux`). |
| The statement `e = true` | `NativeStatement.AssertsTrue`, `NativeStatement.assertedBool?_eq_some_iff` | The type is the constant `Eq` applied to the constant `Bool`, to `e` and to the constant `Bool.true`. The theorem is about the functions `Expr.getAppFn` and `Expr.getAppArgs` of Lean, which the decision runs. |
| One expression | `NativeStatement.Statement.unique` | A type is the statement of one expression at most, for all tactics and prefixes. |
| The names of the auxiliary definitions | `generatedAuxParent?_sound`, `generatedAuxParent?_of_generatedAux` | A recognized name is a name of the generator under the recovered prefix. The converse has two hypotheses. The first is `RuntimeStringAppend`. The second is that no text that starts with the infix is the macro-scope marker `_hyg`. The two infixes of `bv_decide`, `_expr_def` and `_cert_def`, satisfy the second hypothesis. |
| The record of the pass | `NativeStatement.Recognition`, `NativeStatement.recognize?_eq_some`, `NativeStatement.Recognition.statement`, `NativeStatement.Recognition.not_refused` | A recognition has its candidate as an index. It holds the expression and the proof that `asserted?` returns it for that candidate. Each recognition of a candidate is the result of `recognize?` for that candidate. Thus a candidate that the decision refuses has no recognition, and the statement of a recognition is a theorem. |

**The kind is one-way.** The decision regenerates the names of the two auxiliary definitions of
`bv_decide` with `String.Internal.append`. Lean's logic does not say what that function returns.
Thus completeness for that tactic has the hypothesis `RuntimeStringAppend`, and a two-way kind has
no hypothesis. A refusal fails closed: an axiom with no recognized statement is not
authenticated (`NativeTeachingOK`).

**Hypotheses and trusted boundary.** The theorems start from the tactic, the prefix and the type.
They do not prove these items:

- That the evaluation returns what the pass records, or that compiled code computes the meaning
  of the expression. The field `nativeReplay` is a toolchain observation.
- That the tactic and the prefix are those of the name of the axiom. `Collect.nativeRecognition?`
  gives the result of `nativeAxiomOrigin?` to the decision, and that step is read from the code.
  The type of a recognition states the candidate, and it does not state the name of the axiom.
- That the name and the type are those of the axiom. The collector reads them from the constant
  map of the environment.
- That `generatedName` is the name that the generator of Lean gives. That is read from the source
  of Lean, as [`RegulaPolicy/NativeAxiom.lean`](../../lean/RegulaPolicy/NativeAxiom.lean) says.
  The relation and the decision share that definition.
- The universe levels of the constants of a statement. The decision does not compare them, and
  the relation does not state them. Lean's kernel checked the type of the axiom.
- The recorded text `nativeStatement`. It is the `repr` of the expression, with the unindexed
  name of each auxiliary definition (`Collect.nativeStatementText`). No theorem says that two
  different expressions have different texts, and the transcript match compares the texts.
- The adequacy of the relation: that these shapes are the statements that the pinned tactics
  make. That is read from the source of Lean.

**The verdicts are the same.** No theorem of the repository compares the producer before this
split with the producer after it. The decision has the guards of the old collector, with the same
arguments, and a reader can compare the two texts. Only the place of one `bind` changed: the
collector reads the name, and the decision reads the type. The controls show the same results for
those controls only.

**Observed.** `checkerSelftest fixtures` does the pass and the decision on the pinned toolchain.
The seven native controls of `lean/Fixtures/Mutations` each get the reason that `fixtures.json`
gives. Those fixtures are tests of the boundary to the compiler. They are not tests of the
statement shapes, which the theorems decide.

### The diagnostic and policy codecs: decisions and observing pass

The reader of a result file, and the reader of the reply of a worker, each have two steps. The
second step is pure decisions with a kind.

- **The observing pass** turns a text into a `Json` value. The callers use two parsers, and no
  theorem says what a parser returns. `Checker.PolicyCodec.parse` uses the scalar parsers of Lean,
  which are `partial`. It refuses an object that gives one name twice, and it builds each object
  with `Json.mkObj`. `Json.parse` of Lean runs parsers that are `partial`, and it does not refuse
  a repeated name. It starts each object from the empty tree and adds each member with `insert`.
- **Between the two steps**, a reader of a result file gives the value to `SharedExecution.read`.
  That function puts the source texts and the execution accounts back in the document. It
  rebuilds the objects of the document with maps that keep each name and the shape of each tree.
  The maps replace only the value of a member `sourceText`, `sourceTexts` or `execution`.
- **The decisions** read the `Json` value that a caller gives, and they read nothing else.
  `PolicyCodec.exactFields` decides if a value is an object with the expected members and no
  other. `JsonAgreement.agrees` decides if a value agrees with an encoding.
  `JsonAgreement.canonical` accepts what a reader returns only when the input agrees with the
  encoding of that value. `DiagnosticCodec.parseLocation` and `parseDiagnostic` are `canonical`
  of a reader of the members and of an encoder of `Regula.RegistryCodec`. Each of the five is
  registered with `@[regula_decision]`.

**The comparison.** The decoders compared with the runtime equality of `Json` before this split.
Lean has that equality as a `partial` function, so no theorem is about it. `agrees` is its
procedure as a total function by structural recursion. For two objects it compares the numbers of
members, then it reads each member of the first and looks the name up in the second. The relation
`JsonAgreement.Agree` states that procedure, with one constructor for each case.

**The form of an encoded value.** `LocationWire` and `FindingWire` say which members an object
has and what the value of each member is (`JsonAgreement.Shaped`). They do not mention an
encoder of a location, of a payload or of a finding.

Three meanings name a written form that a different codec states. They are the form of a name,
of a natural number and of an LSP range. The form of a name is the form that `printedNameJson`
writes (`printedNameJson_roundtrip`).

A finding is an object with eleven members. Eight members carry the finding: `id`, `arguments`,
`location`, `related`, `mode`, `claim`, `impact` and `severity`. Three members are redundant:
`text`, `remedy` and `helpUrl`.

**Proved**, about the functions that the checker runs. Lean's kernel checked each theorem in the
build of the excluded `Regula` library, with `propext`, `Classical.choice` and `Quot.sound` only.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| The comparison is exact | `JsonAgreement.agrees_iff`, `checked_agrees` | `agrees` returns `true` exactly for two values that `JsonAgreement.Agree` relates. |
| A canonical decoder fails closed | `JsonAgreement.canonical_eq_ok_iff`, `checked_canonical` | The decoder returns a value exactly when the reader returns it and the input agrees with the encoding of that value. The theorem is for each reader and each encoder. |
| The encoders write the form | `locationJson_wire`, `diagnosticJson_wire` | The encoding of each location has the form of that location, and the encoding of each finding has the form of that finding. A change that removes a member from an encoder makes the theorem fail. |
| The decoders accept the form | `parseLocation_of_wire`, `parseDiagnostic_of_wire`, `checked_parseLocation`, `checked_parseDiagnostic` | A decoder accepts each value of the form, and it returns the location or the finding of that form. The theorem is for each `Json` value. |
| Each value is read back | `parseLocation_roundtrip`, `parseDiagnostic_roundtrip` | The decoder reads the encoding of each location back to that location. It reads the encoding of each finding back to that finding, for each number of related locations. |
| An accepted value has the form, for search trees | `parseLocation_wire`, `parseDiagnostic_wire`, `parseLocation_iff`, `parseDiagnostic_iff` | The input has the form of the value that the decoder returns, when each object tree of the input is a search tree (`JsonAgreement.Regular`). |
| An accepted value agrees with its encoding | `parseLocation_canonical`, `parseDiagnostic_canonical` | The theorem is for each `Json` value. It names the encoder that the decoder runs. |
| In a search tree, each member is found by its name | `JsonAgreement.get?_of_mem`, `mem_of_get?` | The first theorem is about `Std.TreeMap.Raw.get?`, the lookup that `Json.getObjVal?` runs. The second is for each tree: a name that is found is the name of a member. |
| Exact members | `PolicyCodec.exactFields_iff`, `checked_exactFields` | `exactFields` accepts exactly an object that has the expected names as its member names, in some order (`ExactFields`). The proof that the expected names are distinct is an argument. Thus Lean rejects a call with a list that gives one name twice. |

**The kinds.** `agrees`, `canonical` and `exactFields` are two-way decisions. `parseLocation` and
`parseDiagnostic` are complete decisions of the form. The converse holds for an input with search
trees, and it is false for some other `Json` values.

The comparison does not look a name up in the input. Thus the decoders accept an object tree
that gives one name twice and does not give a second name. The issue
[#269](https://github.com/rbeauchamp/regula/issues/269) has such a tree, with no member `remedy`,
and it states the decision that is open.

**Hypotheses and trusted boundary.** The theorems start from a `Json` value. They do not prove
these items:

- What a parser returns for a text, and what a file contains.
- That each object tree of a value that a caller gives is a search tree. That is read from the
  code. `PolicyCodec.parse` builds each object with `Json.mkObj`, and `Json.parse` builds each
  object by insertion from the empty tree. The maps of `SharedExecution.read` keep each name and
  the shape of each tree. No theorem says that a value of these functions has search trees.
- That the form is the intended one. A reviewer examines `LocationWire` and `FindingWire`.
- That `agrees` returns what the runtime equality of `Json` returns. The two definitions have the
  same cases, which a reader can compare. The agreement of the two is by reading, and a
  comparison of the two over pairs of values is evidence for those pairs only.
- What the other comparisons of `Json` values accept. `RegistryCodec.parseDescriptor`,
  `RegistryCodec.validateRegistry` and the guidance members of `ResultProtocol` use the runtime
  equality. These named comparisons are those of the registry codec and of the result protocol.
  Other modules of the library also compare `Json` values with the runtime equality. This item
  is not a complete list, and no theorem says what one of these comparisons accepts.

**The callers.** These paths give a value to the diagnostic decoder. They are read from the code
of the callers.

- `AxiomGate` reads a result file with `ResultProtocol.readDocument`. That function runs
  `PolicyCodec.parse` and then `SharedExecution.read`.
- The runner of the rule examples (`Regula.Qualification.RuleExamples`) reads a result file with
  `Qualification.readResult`. That function runs `Json.parse` of Lean and then
  `SharedExecution.read`. The runner gives the document to `ResultProtocol.admitGuidance`.
- The executable `ruleExampleQualification` reads an evidence file with `PolicyCodec.parse`. A
  record of that file contains a result document. The executable does not run
  `SharedExecution.read`.
- `RegistryChecks` gives values that it builds with the encoders, `Json.mkObj` and
  `Json.setObjVal!`.

`SharedExecution.read` builds each object tree node by node, with the names and the shape of the
tree that it reads.

**The verdicts are the same.** No theorem compares the decoders before this split with the
decoders after it: the old comparison is the runtime equality. The readers of the members have
the text of the old decoders, and `exactFields` has its old text with one more argument.
`agrees` has the cases of the runtime equality. The controls show the same results for those
controls only.

**Observed.** `RegistryChecks` runs in the first acceptance step. The diagnostic decoder accepts
two written findings there. It refuses a finding with an unknown member, with a changed remedy,
with an unsupported mode, with an unknown impact or with an unknown severity. It also refuses a
name in a form that the encoder does not write for that name. Those cases are tests of the
boundary to the encoders, and they are not tests of the comparison, which the theorems decide.

### The fence scanners: decisions and observing pass

The documentation audit finds the Lean examples of a Markdown document and of a Verso source. A
violation of the fence protocol or of the shape rule is a finding of [RG4001]. The reader has
two steps, and the second step is a pure decision with a kind.

- **The observing pass** reads the bytes of each document. `Documentation.auditBuiltProject`
  gives each text to `scan` or to `scanVerso`. No theorem says what a file contains.
- **The decisions** read a document with its lines, and they read nothing else. `scanLines` is
  the scanner of a Markdown document, and `scanVersoLines` is the scanner of a Verso source.
  Each is registered with `@[regula_decision]`.

The two decisions are in
[`Regula/Checker/FenceScan.lean`](../../lean/Regula/Checker/FenceScan.lean). Each is a machine
with one state.

A step function reads one line by the fence protocol (`step`, `versoStep`). A second function
adds the shape rule to that step (`shapedStep`, `shapedVersoStep`). A last function reads the
end of the document (`finish`, `versoFinish`).

**The input and the result are bound by their types.** The input of a decision is a `Source`: a
document, its name in a violation, and its lines. The field `divided` is the proof that the
lines are the characters of the text of the document, divided at each line break. Thus no value
of the type has the lines of a different text. `Source.of` makes the lines with `linesOf`, and
`toList_linesOf` is the proof for that function.

`scan` and `scanVerso` return a `Scanned`: the form of the document, the `Source` and the result.
The field `executed` is the proof that the result is what the scanner of that form returns for
that `Source`. The audit takes its fences and its violations from a `Scanned`.

**The protocol.** The specification of each scanner is a relation, and it names no function of
the scanner. `Mode` is what the protocol knows between two lines: outside a fence, with or
without a marker that waits, or inside a fence. `Permitted` gives the transitions that the
protocol permits for one line.

`Follows` is a run of permitted transitions from the first line. The run ends outside a fence,
with no marker that waits. The Verso protocol has the same parts, which are `VersoMode`,
`VersoPermitted` and `VersoFollows`.

The statements about one line are about its characters. They are `FenceLine`, `ClosingLine`,
`TrustedMarker`, `FailMarker`, `MarkerLike` and `FirstWord`. Each gives the line as parts, one
after the other: whitespace, the characters of a delimiter, and the characters between two
delimiters. `Trimmed` states what a text is without the whitespace at its two ends, and a text
has one such form only (`Trimmed.unique`).

`LineIs` gives the class of a line outside a fence: the first class of five that the line has.
`BlockKind` gives the supported info strings of a Verso block, each with its kind. The
statements about the characters of a line use `Char.isWhitespace` of Lean. They use no function
of Lean that trims a text or that takes a part of a text.

`BlockKind` also names `RegulaPolicy.PatternValid`, the relation of the policy library for a
valid pattern. `Permitted` takes the valid patterns as a parameter, and the kind of `scanLines`
gives it that relation. That relation divides a pattern with `String.splitOn`.

**The shape rule.** The scanner reads lines, and a Markdown reader reads blocks. Thus a block
of the reader can be at a place where the protocol sees no fence. Such a place is a quotation,
a list item, or the lines after a line that only the scanner reads as a fence line. The shape
rule does not make the two agree. It refuses each line that can open a Lean block at such a
place.

Four statements are about one line, with no state. `LeanShaped` is a line with three back-ticks
or three tildes at some place. The characters after them name Lean (`NamesLean`), or they have
`&` or a backslash in their first word (`EscapeInWord`). The three can be any three of a longer
run, because back-ticks and tildes change neither statement.

`NamesLean` says that the first run of letters is `lean`, without regard to case. It has no
notion of white space. Markdown readers differ in the characters that they remove before the
language of a fence. One reader removes a form feed, and a different reader removes a no-break
space.

`EscapeInWord` reads the first word after the run. That word starts at the first letter, `&` or
backslash after the run, and it ends at a space. The statement says that the word has a `&` or a
backslash.

A reader decodes a character reference and a backslash escape in an info string, and it takes
the first word as the language. No reader removes a letter, a `&` or a backslash before that
word, and each reader ends the word at a space. Thus a reader reads a first word without `&` and
backslash as it is written. Its first run of letters is then the one that `NamesLean` reads. A
`&` in a later word, as in the info string `sh title="a&b"`, does not change the language. A tab
does not end the word for each reader, so a `&` after a tab still gives the line Lean shape.

`LeanOpening` is a line that opens a Lean fence in the first column. `RawCodeTag` is a line
with the start tag of `pre`, `code`, `xmp`, `listing` or `plaintext`. `LoneReturn` is a line
with a carriage return before its last character.

`ShapeRule` gives the rule for one line of a Markdown document. No line is a `LoneReturn`, has
the character U+0000 or is a `RawCodeTag`. Outside a fence, a line of Lean shape is a
`LeanOpening`. Inside a fence, no line has Lean shape, and a line that closes a Lean fence
starts with the run.

`VersoShapeRule` is the rule for a Verso source. It has no part about raw HTML. It permits no
carriage return and no U+0000, because no theorem says what a Verso reader or its page does with
them.

`Clean` is the relation of the kind: a run of lines, each a permitted transition that keeps the
shape rule. `LeanAfter` says after each line if the open fence is a Lean fence. `VersoClean` and
`VersoLeanAfter` are the same for a Verso source.

**The shape is conservative.** `LeanShaped` does not read the inline structure of Markdown.
Thus the rule refuses a line of text where an inline span of three back-ticks comes before the
word `lean`. An author writes that span with fewer back-ticks, or uses different words. Two
controls pin this result.

**What a line is.** A line of the scanner is the text between two line feeds. For a Markdown
reader a line ends at a line feed, at a carriage return before a line feed, and at a carriage
return alone. A clean document has no `LoneReturn`. Thus each line of the scanner is a line of
the reader, with one carriage return after it when the line ending has one.

`clean_iff_withoutReturn` connects the two. A document is clean exactly when its lines without
that carriage return have no carriage return left and are clean. The condition on the carriage
return left is needed. The line `prose` with two carriage returns after it is not clean. Without
its last carriage return, it is `prose` with one carriage return, and that line keeps each other
statement about a line. Thus the verdict of the scanner is the verdict on the lines of a reader.

The body of a returned fence ends before the line ending of its last line. Its other lines keep
the carriage returns of their line endings, and a clean document has no other carriage return.
Lean reads a carriage return before a line feed as a line feed (`Lean.Parser.mkInputContext`).
Thus Lean reads the lines of the body as a reader divides them.

This rests on the front end of the compiler, which the audit trusts, and no theorem of Regula
states it. Three controls pin it. A body with these line endings passes, also with a string over
two lines. A negative example fails when its pattern names a carriage return that no line feed
follows.

A reader shows U+FFFD in place of the character U+0000, and the audit compiles the text of the
document. Thus at that character the example that a reader shows is not the example that the
audit checks. The shape rule refuses U+0000 at each place. An author writes `\x00` in a Lean
string or character literal.

**From the shape rule to a Markdown reader.** This part is an argument, and it is not a
theorem. By the syntax of CommonMark, a fenced block opens with a line of four parts. The parts
are a container prefix, at most three spaces, a fence run and an info string. The language of
the block is the first word of the info string. Thus each Lean block of a reader opens at a
line of Lean shape.

In a clean document that line is a `LeanOpening` outside a fence. A fence line in the first
column is not in a container, and a reader removes no indentation from its body. A reader
closes the block at the first run of the same character, of that length or more, with at most
three spaces before it. In a clean document that run is in the first column, where the scanner
closes the fence too.

**Proved**, about the functions that the checker runs. Lean's kernel checked each theorem in the
build of the excluded `Regula` library, with `propext`, `Classical.choice` and `Quot.sound` only.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| The Markdown scanner is exact | `scanLines_problems_eq_empty_iff`, `checked_scanLines` | `scanLines` reports no violation exactly for a document with lines that `Clean` admits. The line numbers start at 1, and the valid patterns are those of the policy library. The theorem is for each `Source`. |
| The Verso scanner is exact | `scanVersoLines_problems_eq_empty_iff`, `checked_scanVersoLines` | `scanVersoLines` reports no violation exactly for a source with lines that `VersoClean` admits. The theorem is for each `Source`. |
| A line of Lean shape is a returned fence | `fence_of_leanShaped`, `example_of_leanShaped` | In a clean document, each line of Lean shape is the opening line of a returned fence. The fence has the number of that line. The theorems say nothing about the body or the byte ranges of that fence. |
| The lines of a Markdown reader | `clean_iff_withoutReturn`, `permitted_withoutReturn`, `shapeRule_withoutReturn`, `leanAfter_withoutReturn` | A Markdown document is clean exactly when its lines without the carriage return of a line ending have no carriage return and are clean. Each statement about a line is the same with and without that carriage return. |
| A scan with its input | `Scanned.problems_eq_empty_iff`, `Scanned.versoProblems_eq_empty_iff` | The first two theorems, for the result and the document that a `Scanned` carries. |
| The lines of a text | `toList_linesOf` | The lines that `linesOf` gives are the characters of the text, divided at each line break by `List.splitOn` of Lean. |
| The layout of the lines | `layoutLoop_toList`, `layout_eq` | The scanner numbers the lines in a loop that keeps no stack frame for a line. The loop gives the lines of `layoutFrom`, the definition that the theorems read. |
| The protocol alone | `problems_eq_iff_follows`, `versoProblems_eq_iff_follows` | The steps of the protocol, without the shape rule, keep the violations exactly on a run of permitted transitions (`Follows`, `VersoFollows`). |
| One step follows the protocol | `step_quiet_or_loud`, `permitted_of_quiet`, `quiet_of_permitted`, `coherent_step` | A step keeps the list of violations, or it makes that list longer. A step that keeps the list is a permitted transition. From a state with `Scan.Coherent`, a permitted transition keeps the list. A step keeps `Scan.Coherent`. The Verso scanner has the same three theorems with no such condition. |
| The class of a line | `lineIs_classify`, `lineIs_unique`, `classify_eq_of_lineIs` | `classify` returns the class that the line has, and a line has one class only. The proof includes that the trimming and the extraction of the scanner give the parts that the statements name. |
| The pattern of a marker | `validatePattern_eq_ok_iff` | The validator of the scanner accepts exactly the patterns that `RegulaPolicy.PatternValid` admits. The matcher of [RG4003] uses the same relation (`matchesPattern_iff`). The validator and the relation divide a pattern with the same `String.splitOn`, and Lean's library has no theorem about that function. Thus the theorem does not say what a division gives. |
| The info string of a Verso block | `versoBlockKind_eq_ok_iff` | `versoBlockKind` returns a kind exactly for an info string that `BlockKind` relates to that kind. |

The tests of the shape rule are private functions, and each has a private theorem that it
accepts exactly the lines of its statement. Those theorems are part of the proof of the two
kinds.

**The kinds.** `scanLines` and `scanVersoLines` are two-way decisions. A result is accepted when
it has no violation. The accepted input is the document with no character, which has one line.
The refused input is the document of one line that opens a fence.

**Hypotheses and trusted boundary.** The theorems start from a `Source`. They do not prove these
items:

- What a file contains.
- The body, the marker and the byte ranges of a returned fence, which is the open proof
  obligation below.
- The text of a violation, and the number of violations of a document that is not clean.
- That the protocol is the intended one. A reviewer examines `Permitted`, `VersoPermitted`,
  `BlockKind`, `ShapeRule` and the statements about one line.
- That a Markdown reader follows CommonMark for the end of a line and for the opening line and
  the closing line of a fenced block. The argument above is by reading its sections on line
  endings, on fenced code blocks and on container blocks.
- That the five names are the elements of raw HTML that a browser shows as preformatted text or
  as code. This is by reading the HTML standard.

The protocol alone has two defects, which the shape rule closes. It does not see a fence in a
Markdown block quote ([#273](https://github.com/rbeauchamp/regula/issues/273)). It permits a
Lean block of a Verso source after a tab
([#274](https://github.com/rbeauchamp/regula/issues/274)).

**The open proof obligation: the body and the place of a returned fence.** The audit compiles
the fences that a scanner returns. The verdicts of [RG4002], [RG4003] and [RG4004] are about
those fences. One part is proved: a clean document has a returned fence for each line of Lean
shape. No theorem is about the body, the marker or the byte ranges of a fence. A scanner that
returned a fence with a changed body satisfies the same theorems.

A statement of the rest of that obligation says these things for a clean document. Each
returned fence opens at a line of Lean shape. The body of a fence is the text of its lines,
without the line ending of the last line. The marker of a fence is the marker on the line before
its opening line. The byte ranges of a fence are the ranges of those lines in the text. `layout`
counts one byte for the line break after each line but the last, and no theorem relates those
offsets to the text.

**The scanners before the split.** The audit ran two loops over the lines, with local variables,
and it divided a text with `String.splitOn "\n"`. No theorem relates those loops to the steps of
the protocol (`step`, `versoStep`), and Lean's library has no theorem about that
`String.splitOn`.

The agreement of the two is by reading. Each step function has the cases of its loop, with the
same tests of a line in the same order. A comparison of the results of the two on a set of texts
is evidence for those texts only. The shape rule is a later change: it refuses documents that
those loops accepted.

**Observed.** The scanner cases of `checkerSelftest fixtures` run the scanners on texts about
the protocol and on texts about the shape rule. For the clean text of the protocol, the cases
read that the result has one fence and no violation. For each other text of the protocol, they
read that a violation contains the expected words.

The texts about the shape rule are for a Markdown document and for a Verso source. For each form
that the rule refuses, the cases read words of the violation. For each text that the rule
accepts, they read one fence and no violation. The Markdown texts are also part of the fence
corpus, which the audit reads in that diagnostic. The diagnostic prints the number of corpus
cases that it read.

The theorems say when a result has no violation. They do not say which text a violation has,
and they do not say which body a fence has. The controls read a part of those two things for
their texts: words of a violation, and the number of fences.

The fence audit of `./scripts/verify.sh docs` runs the two scanners on each Markdown document
of `docs/` and on the Verso sources of the standard. It compiles each fence that they return.

### Receipt validation: decisions and observing pass

[RG2005] reports an environment as incomplete when `Admission.validate` does not admit it.
`validate` is an observing pass around three pure decisions with a kind.

- **The decision on the header** is `Admission.checkHeader`. Its argument,
  `Admission.ReplayRequest`, holds the modules of the header of the audited environment with
  their data, the replay set and the reported modules. Each module that is replayed or reported
  must list its constants under their own names (`Admission.ListsOwnNames`). No module of the
  replay base may import a replayed module. `checked_checkHeader` registers the kind
  `Regula.Decides` against `Admission.HeaderOK`.
- **The decision on the replay** is `Admission.admitReplay`. Its argument,
  `Admission.AdmitRequest`, holds a request, the proof that `checkHeader` accepted it, and the
  kernel that the replay gave. The decision runs `checkCopies` on the copies of the request. It
  then requires that the kernel holds a constant under the name of each required key, and it
  returns the receipt of the request. `checked_admitReplay` registers the kind
  `Regula.DecidesSoundly` against `Admission.AdmitOK`.
- **The decision on the axiom tables** is `Admission.checkTable`. Its argument holds, for each
  owned declaration, the axioms that `collectAxioms` gives and the axioms that the declaration
  reaches in the replayed kernel. It refuses the first declaration with an axiom of the first set
  that is not in the second. `checked_checkTable` registers the kind `Regula.Decides` against
  `Admission.TableWithin`.
- **The observing pass** is the rest of `validate`. It computes the replay set (`replaySet`) and
  the reported modules, imports the replay base and replays the copies (`replayMap`). It computes
  the axioms of the owned declarations, gives a failure of a decision its text and catches the
  exceptions of the replay.

The import of the replay base runs before the handler of `validate`, as before this split. Thus an
exception of the import goes to the caller of `validate`, without the tag of an admission failure.

The copies, the required keys and the modules of the replay base are definitions of the request
(`ReplayRequest.copies`, `ReplayRequest.required`, `ReplayRequest.imports`). The receipt of an
`AdmitRequest` is a definition of its fields too (`AdmitRequest.receipt`). Thus a receipt has the
keys of a header that `checkHeader` accepted, by the type of the argument of `admitReplay`.

**Proved**, about the functions that `validate` runs. Lean's kernel checked each theorem in the
build of the excluded `Regula` library, with `propext`, `Classical.choice` and `Quot.sound` only.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| The decision on the header is exact | `Admission.checkHeader_eq_ok_iff`, `Admission.checked_checkHeader` | `checkHeader` accepts exactly a request that `HeaderOK` admits. The theorem is for each list of modules, replay set and list of reported modules. |
| One condition for each module | `Admission.checkModule_eq_ok_iff`, `Admission.checkListing_eq_ok_iff`, `Admission.checkBase_eq_ok_iff` | A module lists its constants under their own names exactly when its list of names is the names of its constants. A module of the base passes exactly when it imports no module of the replay set. |
| The required keys | `Admission.mem_required` | A key is required exactly when it names a replayed or reported module and a constant of that module that is neither `unsafe` nor `partial`. |
| A receipt is admitted | `Admission.admitReplay_eq_ok`, `Admission.checked_admitReplay` | A receipt of `admitReplay` is the receipt of its request. Each copy has the conditions of `CopyAdmitted`, and the kernel holds a constant under the name of each required key. |
| The axiom tables are exact | `Admission.checkTable_eq_ok_iff`, `Admission.checked_checkTable` | `checkTable` accepts exactly the entries that `TableWithin` admits. The theorem does not tell that the entries come from the replayed kernel and from `collectAxioms`. |

**The kind of `admitReplay` is one-way.** The decision runs `checkCopies`, which bounds the
search of the axioms of a proof by `fuel`. Thus a refusal fails closed, as for `checkCopies`.

**Hypotheses and trusted boundary.** The theorems start from the request. They do not prove these
items:

- That the kernel of an `AdmitRequest` is the kernel that `Kernel.Environment.replay` of Lean gave
  for the copies, and that the replay checked each declaration. The pass gives the result of the
  replay to the decision, and that step is read from the code.
- That the modules of a request are those of the header of the audited environment, and that
  `kept` is the lookup of that environment. The pass reads them, and that step is read from the
  code.
- That the replay set, the reported modules and the reused modules of a request are those that
  the pass computes. The replay set is `replaySet` of the header, `ownedModules`, `reused` and
  `checker`. The argument `checker` holds the modules of an owned dependency under the prefixes
  `Regula` and `RegulaPolicy` that the environment does not own. The reported modules are the
  modules of `reused` that are in `requested` and not in the replay set. The reused modules are
  the argument `reused` of `validate`, and these steps are read from the code. `mem_replaySet`
  proves only that each owned module that is not reused is in the replay set.
- That the replay base is what the pass imports. `importModules` of Lean reads the `.olean` files.
- That `shared` names the copies of a name that the base or a different replayed module also
  declares. The pass computes it from the base and from `nameCounts`, and that step is read from
  the code.
- The text of a failure.

**The verdicts are the same.** No theorem compares the producer before this split with the
producer after it. The old producer was one loop in `IO`. The decisions have the tests of that
loop, in the same order and with the same texts, and a reader can compare the two texts.

One test has a different form. Membership in the replay set is now `Array.contains`, in the place
of `NameSet.contains`. By reading, the two give the same answer for each name. The controls show
the same results for those controls only.

**Observed.** The structural diagnostic runs the gate on projects with a declaration that the
kernel refuses and with two copies of one name that admission refuses. Each control gets the
reason that it expects. The `fixtures` diagnostic does the same for the fixtures of
`lean/Fixtures/fixtures.json` that expect `kernel-admission`. Those controls are tests of the
boundary to the kernel and to the import of Lean. They are not tests of the decisions, which the
theorems decide.

### Root and closure discovery: decision and observing pass

[RG3001] and [RG3002] read the execution account of each executable root.
`Probe.executionWalk` builds that account with an observing pass and a pure decision with a kind.

- **The observing pass** is `Probe.observeNode` and the loop of `executionWalk`. For each name
  that the walk reaches, the pass reads the environment one time and gives a record
  (`ExecutionWalk.NodeRecord`). The record has the names that the retained compiler body calls and
  the targets of the edge channels of the name. It also has the boundaries at the name, the paths
  that the pass could not resolve and the status of the compiler body. The loop queues the
  successors of each record and does not read a name two times.
- **The decision** is `ExecutionWalk.walk`. Its argument, `ExecutionWalk.WalkRequest`, holds the
  records and the root. It returns the visits in the order of a stack of queued names, each with
  the position of the visit that queued it. `checked_walk` registers the kind `Regula.Decides`
  against `ExecutionWalk.Recorded`: each name that the edges of the records reach from the root has
  a record.
- **The account** is `ExecutionWalk.assemble`. Its argument, `ExecutionWalk.Walked`, holds the
  request, the visits and the proof that `walk` returned those visits for the request. It reads the
  record of each visit through that proof (`Walked.record`), with no default record. It builds the
  boundaries, the unresolved paths, the compiler edges and the closure from those records, in the
  order of the visits. A required name with no record is reported as unavailable code, which fails
  closed.

The type of a record is indexed by its name (`NodeRecord name`), so the map of records holds a
record only under its own name. A record holds the targets of the edges from its name, and not the
edges. Thus each edge that `assemble` builds starts at the name of a visit, by the type of the
record.

The successors of a record are a definition of its targets (`NodeRecord.successors`,
`mem_successors`). They are the compiler calls, then the targets of the candidates, the history,
the current replacement, the logical value and the recursion helper. Thus each step of the walk is
an edge of the account. The reader of a result file queues the same channels in the same order
(`SharedExecution.walkLoop`).

**Proved**, about the functions that `executionWalk` runs. They are in the claimed library
`RegulaPolicy` (`RegulaPolicy.ExecutionWalk`), so acceptance admits each theorem with Lean's
kernel and reports its axioms: `propext`, `Classical.choice` and `Quot.sound`.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| The visits are the reached names | `ExecutionWalk.walk_sound`, `ExecutionWalk.walk_complete` | Each visit of a walk that returns visits is a name that the edges of the records reach from the root (`Reach`, over `Follows`). Each such name is a visit. |
| One visit for each name | `ExecutionWalk.walk_nodup` | A walk that returns visits has no name two times. |
| Each step is an edge | `ExecutionWalk.mem_successors` | A name that the walk queues after a record is a target of one of the edge channels of the record. |
| The bound is sufficient | `ExecutionWalk.walk_ok` | A walk returns visits when each reached name has a record. The bound of the steps is one more than the number of successors of all records. |
| The decision is exact | `ExecutionWalk.checked_walk` | `walk` returns visits exactly when `Recorded` is true. It accepts a root with a record that has no successor, and it refuses a root with no record. |

**Hypotheses and trusted boundary.** The theorems start from the records. They do not prove these
items:

- That a record is what the environment holds for its name. This includes the compiler calls, the
  targets, the boundaries with their correspondence, the unresolved paths and the status of the
  compiler body. The type binds a record to its name, but not to the pass: other code can make a
  value of `NodeRecord name`. The pass reads the environment, and that step is read from the code.
- That the pass gives a record for each name that the walk reaches. If a name has no record, the
  walk refuses, and the pass stops with an error. Thus a missing record fails closed.
- That `assemble` builds the correct account from the records of the visits. No theorem is about
  that account. At the admission of a report, `ExecutionClosure.Valid` and `ExecutionRoot.Valid`
  check the closure that it builds (**Closure** in [Producers](#producers)).
- That the reader of a result file gives the visits and the parents of the producer.
  `SharedExecution.walkLoop` queues the same channels in the same order as `NodeRecord.successors`,
  by the two definitions. No theorem relates the two walks. Their match is by reading, and the
  `history` qualification and `RegistryChecks` observe it.
- The text of an unresolved path.

**Root discovery has no decision.** `Probe.executableRoots` selects the owned definitions and
opaque constants that are not internal, `unsafe`, `partial` or `noncomputable`. It also refuses a
constant with a proposition as its type or a sort as its result. Lean gives each of these facts
(`Name.isInternal`, the safety of the constant, `isNoncomputable`, `Meta.isProp`, and the reduction
of the type in `Collect.returnsSort`).

The census then adds the action of each initializer that an owned module records, whatever its
name or safety (`Probe.initializerActions`). Lean records these actions in the entries of the
attributes `[init]` and `[builtin_init]`.

The selection of roots is the conjunction of these facts, together with these entries. A kind on
it would state the expression of the function as its specification. Thus the census of roots
is observed, and `environmentReport` adds the root of each valid registration to it.

**The verdicts are the same.** No theorem compares the producer before this split with the
producer after it. The pass reads each name with the tests and the texts of the old loop, in the
same order. Each part of the account is the parts of the records in the order of the visits, as
the old loop added them.

A comparison read the reports of the fixtures and of the claimed libraries `RegulaPolicy` and
`RegulaCore`, before and after the split. Only the list of modules was different. This is an
observation for those environments only.

### Contract recognition and reach: decision and observing pass

[RG1007] reads the `ExecutableContract` registration of a declaration
(`Collect.executableContract?`). There, the collector asks three questions of one form. Each
question is an observing pass and one pure decision with a kind.

- **The questions.** Before the collector reduces a declared type, `ContractScope.mayReach` asks if
  `Regula.ExecutableContract` can be among the constants of the reduction. Before the collector
  reduces the requirement of a registration, `ContractScope.mayReachDecision` asks the same about the
  structures of the three decision kinds. For a decision registration, `mentionChain?` asks if the
  acceptance predicate or the specification mentions the implementation, and through which
  constants.
- **The observing pass** is `Collect.mentionRecords`. It takes the constants in the order of a
  stack. The constants of the term go on the stack first, and no constant goes on the stack two
  times. For each constant that the pass takes before a target, it gives a record of the constants
  that the constant mentions (`MentionSearch.References`). A constant that the question does not
  expand has no record.
- **The decision** is `MentionSearch.search`. Its argument, `MentionSearch.SearchRequest`, holds
  the records, the constants of the term and the targets. It returns the route to the first target
  that it takes from the stack, or `none`. The stack holds each route in reverse order and shares
  the route of the constant that pushed it. `checked_search` registers the kind `Regula.Decides`
  against `MentionSearch.Found`: a constant of the term leads to a target through the records.

Each question gives the constants that a record lists, and the constants that have no record:

| Question | A record lists | No record |
| --- | --- | --- |
| `mayReach`, `mayReachDecision` | The constants of the type, of the value and of the constructors or the recursor rules (`unfoldReferences`). | A constant of a module that does not import `Regula.Contract`. A constant of the memo of the same targets. A constant that the environment does not have. |
| `mentionChain?` | The constants of the type, and of the value of a definition. The constructors of an inductive type, and the constructors and the constants of the rules of a recursor (`statusReferences`). | A constant of a module that does not import the module of the implementation. A constant that the environment does not have. |

The type of a record is indexed by its constant (`References name`), so the map of records holds a
record only under its own constant. The pass takes the constants in the order of the decision.
Thus the decision takes the same constants and returns at the same target. If the pass finds no
target, it read each constant that the search reaches. A guard that finds no target adds each
constant with a record to the memo of its targets.

**Proved**, about the function that the three questions run. It is in the claimed library
`RegulaPolicy` (`RegulaPolicy.MentionSearch`), so acceptance admits each theorem with Lean's kernel
and reports its axioms: `propext`, `Classical.choice` and `Quot.sound`.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| A route follows the records | `MentionSearch.search_sound` | A returned route starts at a constant of the term and stops at a target. Each constant before the target has a record that lists the next constant (`Route`). |
| No route is lost | `MentionSearch.search_complete` | The search returns a route when a constant of the term leads to a target (`Leads`). The bound of the steps is one more than the number of constants that the term and all records list. |
| The decision is exact | `MentionSearch.checked_search` | `search` returns a route exactly when `Found` is true. It accepts a term that mentions a target, and it refuses a term that mentions no constant. |

**Hypotheses and trusted boundary.** The theorems start from the records. They do not prove these
items:

- That a record lists what the environment holds for its constant. The type binds a record to its
  constant, but not to the pass. The pass reads the environment, and that step is read from the
  code.
- That a constant with no record leads to no target in the environment. For a constant of a
  module that does not import the module of a target, Lean's imports give this (`importersOf`). A
  constant of the memo had no route in an earlier search of the same targets. A constant that the
  environment does not have mentions no constant there.
- That the reduction of a type adds only constants to which the constants of the type lead. This
  is the argument of `ContractScope.mayReach`, read from Lean's reduction.
- That the route in a message is the shortest route. It is the first route that the search takes.

**The other parts of recognition have no new decision.** The eligibility of a registration is a
conjunction of facts that Lean gives. The type is closed, and the implementation is a named
constant. The implementation is computable, safe and not `partial`, and it is not a proposition
and not a type. A kind on that conjunction would state the expression of the function as its
specification. The reading of a kind and of the decided function already has its decisions,
`DecisionKind.ofStructureName?` and `DecidedFunction.covers`.

**The verdicts are the same.** No theorem compares the searches before this split with the
searches after it. `mentionChain?` takes the constants in the same order as before, so it gives the
same route. The guards marked a constant when they took it from the stack, and now they mark it
when it goes on the stack. That changes which constants a guard reads before a target, but not if
it finds one. Before this split, the memo also held the constants that the environment does not
have, which lead to no target.

### The reading of a statement: decision and observing pass

[RG1009] searches the two sides of a decision registration for the functions that they share. It
reads the implementation by the rule of a function, and the acceptance predicate by the rule of a
statement. It reads the specification by the rule of a statement, with one exception. That
reading is an observing pass and one pure decision with a kind.

- **The exception.** The reading does not enter the declaration of the input type of the kind
  from the input. It starts at the body of the specification's function abstraction under its
  variable. When the specification is a definition, alone or applied to its variable alone, the
  search reads the body of that definition's value. From a field's projection function of the
  input type, also through an `abbrev`, it does not follow the edge back to that type.
- **The observing pass** is `Collect.readStatement`. It starts at the constants of the input type
  and of the body. It reads each constant outside Lean's own library that the rule of a statement
  reaches, `StatementReading.Observed.references`. For each such constant it gives a record,
  `StatementReading.Observed`, with the kind and the form of the result type. The record also
  holds the constants of the type, of the value and of the declaration, and the structure of a
  projection function.
- **The decision** is `StatementReading.reads`. Its argument, `StatementReading.Mention`, holds
  the record of a constant, a constant that it mentions and the constants of the input type. It
  accepts when the reading follows the mention. `checked_reads` registers the kind
  `Regula.Decides` against `StatementReading.Read`.
- **The closure** is `StatementReading.reading`. It runs `KernelAxioms.search` two times over the
  records. One search follows `reads` from the body of the term. The other search follows the rule
  of a statement from the input type and the body.

**The argument.** A kind compares `accepts (f x)` with `spec x` for each input `x`. A test that
only the declaration of the input type names is not a part of `spec x` for any `x`. A change of
the test changes which values the input type has. The two sides range over the same values, so
the comparison at each input is the one that it was. A specification that names the input type
in a different way can depend on the test at an input, so the reading follows that name.

This argument is not a theorem about Lean's semantics. Section 7.11 of the standard states it.
The theorem `through_input` gives the property of the reading on which the argument depends.

**The acceptance predicate.** The search reads it by the rule of a statement, the declaration of
the result type included. The argument above holds for the input type only. A value of the result
type occurs on one side of the kind only, in `accepts (f x)`. So a specification that names a test
of that declaration shares it with the acceptance predicate. The control `flaggedOf_decides` shows
this case.

**Proved**, about the functions that the reading runs. They are in the claimed library
`RegulaPolicy`, so acceptance admits each theorem with Lean's kernel and reports its axioms.

| Property | Declarations | Meaning and limit |
| --- | --- | --- |
| The decision is exact | `StatementReading.reads_iff`, `checked_reads` | `reads` accepts a mention exactly when `Read` holds. It follows a projection of the input type to the type of its field, and not back to the input type. |
| A record follows the decision | `StatementReading.mem_read`, `dropped` | The constants that a record gives to the closure are exactly those that `Read` relates to it. A constant that the rule follows and the reading does not is the structure of a projection, of the input type. |
| The reading follows less | `StatementReading.read_subset_withTypes` | The rule reaches each constant that the reading reaches. So the reading refuses no registration that the rule accepts. |
| The closure is exact | `StatementReading.reading_some` | A constant is in `read` exactly when it has a record and the body of the term reaches it by `reads`. The same holds of `withTypes` and the rule. |
| Only through the input type | `StatementReading.through_input` | A constant that the rule reaches and the reading does not, the rule reaches from a constant of the input type. The reading reaches that constant of the input type in no way. |
| The names through types | `mem_sharedNames_throughTypes` | A name is in `throughTypes` exactly when the rule shares a test with that name and the reading does not. |
| The rule holds of what is read | `StatementReading.no_shared_test` | Take a record that names no test of the class `boolean`. No constant of that class is then read in the specification and reached by the other side. The other side is the implementation or the acceptance predicate. |
| What the change accepts | `StatementReading.accepted_throughTypes`, `sharedConstants_read_subset` | A registration that the reading accepts and the rule refuses has each such test in `throughTypes`. The specification does not read it, or neither the implementation nor the acceptance predicate reaches it. |

**Hypotheses and trusted boundary.** The theorems start from the records. They do not prove these
items:

- That a record holds the constants of each part of its constant. The pass reads them with
  `Lean.Expr.getUsedConstants`, a function of Lean's library.
- That a projection function is a constant with a kernel-checked value that is the field of its
  last argument. The pass reads this from the value, as it does for a decided function.
- That the domain and the body are those of the input type and of what the term states. For a
  function abstraction, the pass reads its binder type and its body. A term can name a
  definition, alone or applied to its variable, with a function abstraction as its value. For
  such a term, the pass reads the binder type and the body of that value. For a term of a
  different form, it reads the domain of its type and the term. It adds the constants of the
  input type with its reducible definitions unfolded at its head.
- That a constant with no record leads to no shared test. A constant of Lean's own library is not
  read, as before this change. The editor snapshot of a file with a `module` header gives no
  record to one more constant. That is a specification that is an imported definition with no
  exported value. The editor then reports the reading as incomplete
  with `Unread.shared`, where a shared test could be below that definition.
- That a test that only the declaration of the input type names is no part of a specification.
  This is the argument above.

**The limits.** A specification that reads a field of a field of the input
reads the type of the first field, with its declaration. So does a specification that names a
component type of the input as a parameter, as the projections of a pair do. A type that the
specification passes to a function that is no projection is read too. An example is the element
type that `xs[i]` passes to the instance of `GetElem`. The controls `admitBelow_decides`, `admitPair_decides` and
`admitAt_decides` show these limits.

A definition that the body names among other terms has its type read. So does a definition that
the value of a named specification names. When that type names the input type, the search enters
the declaration of the input type there. An example is
`fun input => AdmitSpec input ∧ 0 < input.amount`, where the type of `AdmitSpec` names the input
type. The control `admitAnd_decides` shows this limit.

**The verdicts.** The rule of a statement is the reading of the search before
[#270](https://github.com/rbeauchamp/regula/issues/270). The reading reaches part of what the rule
reaches, so no registration is newly refused. A registration is newly accepted only when its
specification reached each shared test only through the input type. The record names each such
test after `shared-through-types=`. The acceptance predicate is read as before #270.

### Open obligations of the split producers

Each producer that [#199](https://github.com/rbeauchamp/regula/issues/199) lists is now an
observing pass and pure decisions with kinds. The sections above state what is proved and what is
observed for each of them.

These proof obligations of the producers that are split are open:

- The body and the place of the fences that a fence scanner returns
  ([above](#the-fence-scanners-decisions-and-observing-pass)).
- The account that `ExecutionWalk.assemble` builds from the visits, and the match of the reader's
  walk with the producer's walk ([above](#root-and-closure-discovery-decision-and-observing-pass)).

## Producers

The producers turn a completed Lean environment into observations; their correctness is not
inferred from any pure proof.

- **Census.** `Probe.environmentReport` freezes `(owning module, declaration)` keys from
  `Probe.ownedConstants`, and ordinary and registered executable roots (private or imported),
  before building observations. No policy-success filter defines either census.
  `Probe.ownedConstants` traverses imported module indices, so it is not a current-document
  inventory. An inspected empty root set is `some #[]`, an uninspected one `none`. Only valid
  registrations add executable roots, and all registrations remain in the declaration observations
  even when several registrations share one root. The ordinary roots include the action of each
  initializer that an owned module records, named or anonymous (`Probe.initializerActions`). Lean
  runs that action at startup or import, and no other root has to reference it. The census reads
  the entries of the attributes `[init]` and `[builtin_init]` of each owned module, as Lean reads
  them to run the initializers. It does not read the names of declarations. This census is
  observed. No theorem states that these entries are all the code that an owned module runs at
  import.
- **Admission.** `Admission.validate` replays safe, nonpartial owned declarations and their owned
  dependencies with the pinned `Kernel.Environment.replay`, checks every required entry is in the
  resulting kernel and returns a typed receipt with the axioms of the owned declarations
  (**Axioms** below). It returns `IO (Except ProducerReport.AdmissionFailure Admission.Admitted)`: a
  successful receipt's required keys are the safe, nonpartial constants of the replayed modules' own
  `.olean` data, one key per module and name, then those of each reused module among the
  environment's requested modules (**Admission reuse** below), and it records the admitted keys.
  Replay scope includes owned dependencies and the existing reporter closure where required; it
  may exceed the reported surface. Imported unowned modules remain trusted; the receipt records
  the completed operation and does not authenticate replay. Admission failures carry the
  `[INCOMPLETE[kernel-admission]]` tag (`Admission.failureTag`), since [RG2005] reports them as
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
  (`Admission.SameTheorem`, which `sameTheorem_iff` connects to the test `sameTheorem`). A copy
  that is `Identical` to the held constant (same kind and fields, proof included) needs nothing
  more: it is that replayed constant or that trusted base constant. `Identical` states each field
  of the two records. It has the comparison of Lean only for an expression field. The theorem
  `identical_iff` connects it to the test `identical`. Any
  other copy must pass `Admission.checkProof` in the replayed kernel: the kernel accepts it under
  `Admission.proofCheckName`, and the names its proof reaches (`KernelAxioms.reachSet`, through the
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
  `KernelAxioms.reachSet_some` (a completed search holds exactly the names reachable from the
  constants the start uses, along `KernelAxioms.successors`); `Admission.checkProof_ok`; and
  `Admission.checkCopies_sound` (a success gives every copy the `Admission.CopyAdmitted`
  conditions above, stated with the reachability relation `KernelAxioms.Reach`), and
  `Admission.admitReplay_eq_ok` (a receipt has each copy admitted and a constant of the replayed
  kernel under the name of each required key,
  [above](#receipt-validation-decisions-and-observing-pass)). **Argued, not
  machine-checked:** `validate` gives these checks the replayed module data, the base's and the
  audited environment's `find?` and the replayed kernel, read from the code
  (`Admission.mem_offers` proves that no offered admission lists a `shared` module). Every cycle
  among the audited environment's non-inductive constants that involves an
  owned name passes through a name whose kept constant differs from the replayed one (or through
  the trusted base), because replay admits each declaration only after the constants its type and
  value use, and the replayed kernel agrees with the audited environment on the other owned names;
  the checks exclude a cycle through such a name, so the audited environment's constants form a
  well-founded development. Every copy in a replayed module reaches the same axioms in the
  replayed kernel as the constant held under its name, so the axioms that the checker computes
  for a declaration there ([**Axioms**](#producers) below) do not change with the copy of a shared
  name that its own build used. **Trusted:** Lean's import and module data (two unreplayed copies
  of one name are not compared); the kernel,
  and `replay` adding each map entry unchanged while leaving the base as imported; that the
  kernel's theorem check consults the declaration's name only to require it undeclared, so a
  renamed check is a check of the copy; and, as in Lean's own duplicate-theorem design, that the
  value of a theorem does not change what typechecks where copies of one statement are exchanged.
  Report attribution is unchanged: `Probe.ownedConstants` attributes a shared name to the first
  module Lean's import loaded it from, so the name's claim is that module's.
- **Axioms.** The record of an owned declaration has the axioms that the declaration reaches in the
  replayed kernel. It does not have the axioms of the table that Lean writes for each module, which
  `collectAxioms` reads first for an imported name. After the replay, `Admission.validate` starts
  the search `KernelAxioms.axiomTable` from the owned declarations of `Probe.ownedConstants`. A step
  of the search `KernelAxioms.successors` goes from a constant to each constant of its type and its
  value. A step also goes from an inductive type to its constructors, and from a recursor to its inductive
  types.

  The search reads the constants of the replayed kernel through `Admission.walkFind`. Replay does
  not check an `unsafe` or `partial` constant, and under such a name the search reads the constant
  that the audited environment keeps. The search goes forward one time from all the owned declarations.
  Then it goes back one time from each axiom that it found, along the steps that it recorded. Thus
  the search reads the type and the value of each constant only one time for each environment.

  `Admission.checkTable` then refuses a declaration for which `collectAxioms` gives an axiom that
  the search did not find. Such a module table was not calculated from the constants that the
  kernel checked. The refusal names the declaration and the two axiom sets, and [RG2005] reports
  it as incomplete. The records go to the report of `Probe.environmentReport` and to the self-audit
  of `Qualification.SelfAudit`. The axiom names come from the audited environment, because
  `validate` releases the regions of the replay base.

  An axiom that the search found and that `collectAxioms` does not give is reported, not failed.
  The record of the declaration has it in `tableOmissions`. A project audit gives the number of
  these declarations in the line `axiom tables:`, and the `--verbose` line of each declaration
  gives the two sets. The self-audit lists each of them.

  **Proved** about the executed definitions: `KernelAxioms.axiomTable_some` (each name of the
  closure has exactly the axioms that `KernelAxioms.ReachesAxiom` relates to it). Also proved:
  `KernelAxioms.searchEdges_some` and `KernelAxioms.search_some` (a completed search holds exactly
  the names reachable from its start), and `Admission.checkTable_eq_ok_iff` with the two-way kind
  `Admission.checked_checkTable`. Also proved: `KernelAxioms.axiomsWith_some` and the omission part
  of `Account.checked_account`.

  **Argued, not machine-checked:** each step of `collectAxioms` is a step of
  `KernelAxioms.successors`, as read from `Lean.Util.CollectAxioms` of the pinned toolchain. Thus
  a table that Lean calculated from the replayed constants has no axiom that the search does not
  find. `checkTable` refuses only a table from other constants. A table can have fewer axioms, for
  example none for `Float`. **Observed:** of the 208,024 constants that `import Lean` loads, the
  pinned `collectAxioms` gives fewer axioms than the search for 970, and more for none. The rules
  then use the axioms that the search found.

  A constant of the replayed kernel refers only to constants of that kernel, so the search from a
  safe declaration reads only the replayed kernel. **Trusted:** the kernel and `replay` as above,
  and the constants of the imported, unowned dependencies, which replay does not check. The editor
  has no replayed kernel, thus it reads `collectAxioms`.

  The checks of proofs that the checker makes use `KernelAxioms.axiomsWith`: the recursion equation
  of a recursion helper and an execution correspondence. It starts at the new theorem, stops at
  each name of the table that admission calculated and reads the entry of that name. With a correct
  table, it gives exactly the axioms that the theorem reaches, as `axiomsWith_some` tells. **Argued,
  not machine-checked:** the table is correct for the environment that holds the new theorem. The
  replayed kernel and the audited environment give each name of the table the same axioms. No
  constant of the audited environment uses the new theorem.
- **Admission reuse.** One contract covers every environment of a project audit, a library's
  and an executable's alike. Each environment waits for the environments that replay the claimed
  library modules it loads. What a library's environment loads is read from the import headers
  of the bound sources, starting at its own modules and the force-imported probe; the
  environments are ordered so that a library comes after the libraries whose modules it loads
  (`Inspection.libraryNeeds`, `Inspection.startOrder`). Of the environments that can start, the
  one with the most owned modules comes first. The first environment in that order to load a
  module replays it (`Inspection.replayers`). That is its own library's environment, unless claimed
  libraries import one another. An executable's environment waits for every library. No
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
  last inspection (a change is [RG2005], incomplete); (3) each declaration of each owned module of
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
  decidable equality); otherwise the environment is [RG2005], incomplete. **Proved** about the
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
  every owned module the environment did not reuse, loaded or not, and the modules the
  environment owns by `Environment.ownedModuleSet` can differ from those the offers were made over);
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
  [RG5001]–[RG5003] findings do not depend on whether native feedback was imported. Observed [RG5003]
  evidence is the fresh-project corpus pair and the native `MissingIntent` control; no incremental
  or build-lint [RG5003] run is claimed.
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
  and surface as [RG2005], incomplete; initial setup failures stay [RG2001]. A transported refusal is
  consumed only after worker-packet validation; the parent's own snapshot check can return a typed
  refusal even when a worker crashes or a packet is malformed, and this does not accept or
  authenticate that worker result. Documentation retains its fence finding alongside the typed
  refusal, using fence context without manufacturing a valid declaration range.
- **Replacement histories.** The walk registers each `(root, module)` history request first; the
  loader keeps the Lean-resolved path, the exact bytes before and after an isolated worker and the
  ordered replacement edges, so earlier choices overwritten by later attributes are kept. A
  changed source or unsupported evaluator yields `unavailable`, never a completed receipt. A
  runtime-replacement boundary the toolchain does not own (`ExecutionBoundary.NeedsHistory`, which
  the test `needsHistory` decides) must
  have a registered request, and completed execution requires its replacement edge in a completed
  history. A toolchain replacement, whose module has an admitted toolchain origin, requests no
  history: the walk follows its current target, and `historyReplacementEdges` leaves its edge out
  of the history account. Logical-only inspection has no execution roots, requests or history
  receipts.
- **Closure.** `ExecutionRoot.closure` records `Probe.executionWalk` (the decision
  `ExecutionWalk.walk`, [above](#root-and-closure-discovery-decision-and-observing-pass)): each
  first visit with its owning module and the earlier visit that queued it, and separate edge channels
  (`logicalEdges`, constants used by the logical bodies the walk follows; `candidateEdges`, every
  inspected constant-equality candidate; `historyEdges`, replacement choices from completed,
  source-bound module histories; `currentReplacementEdges`, current `implemented_by` choices
  retained even when history is unavailable; `activeSimplificationEdges`, active simplifications
  used by the replacement-only cycle check, each also a candidate; `helperEdges`, explicit
  opaque-to-partial-helper traversal; `requiredCode` and `unavailableCode`, where a nonempty
  unavailable subset requires unresolved execution). `ExecutionRoot` itself carries
  `compilerEdges`, the retained IR calls, closures and initialization dependencies. Their union is
  a conservative traversal, not a selected or minimal call graph; a missing closure never yields an
  empty boundary set. Each queued name is the target of an edge of its record
  (`NodeRecord.successors`). The walk gives each visit the earlier visit that queued it, and
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
  unresolved replacement-only cycle ([RG3001]). Reflexive constant equalities remain in the candidate
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
  returns a typed refusal ([RG2005], incomplete) on a change while preserving the original outcome
  otherwise. This includes missing or unreadable previously frozen source or configuration, and
  read failures preserve the underlying IO reason; initial environment and setup failures remain
  [RG2001], and only re-reading existing frozen evidence receives this normalization. Terminal
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

The audit owns a dependency when its directory is in the Git work tree of the root package.
`Lake.surfaceInventory` decides it with `ownedDirectory`: `git rev-parse --show-toplevel`, run
without `GIT_DIR` and `GIT_WORK_TREE`, gives the same real directory for the two. **Proved:**
`sameWorkTree_iff` (owned exactly when one known work tree holds the root package and the
dependency), so a dependency in an unknown work tree, or of a root package outside each work tree,
is not owned. **Trusted:** Git finds that work tree, and the filesystem resolves the real paths.
A Git dependency that Lake clones has a work tree of its own, and so does a submodule, thus
neither is owned.

Ownership has a supported scope. Each audit, incremental or fresh, refuses two things before it
builds the project or a copy. `checkDefaultLayout` refuses an owned package, the root package
included, that sets an output directory other than Lake's default. It compares the configured
values, with no path resolved.

`checkOneProvider` refuses a module name that two packages provide, as `lake-query-malformed`,
if one of the two is the root package or an owned dependency. Two trusted
packages can provide the same name, because the audit attributes and owns no module of a trusted
package. It counts the library modules of each package, and the executable roots of the root
package and of each owned dependency. Lake refuses an import of such a name only when it
finds the two definitions distinct, and otherwise the search path decides which artifact loads.
Lake resolves an import only to a library module, thus the executable roots of a trusted package
are not counted.

A module name is unsafe when one of its components is an absolute path. It is also unsafe when a
segment of a component between separators is empty, `.` or `..`. `FilePath.join` discards its base for an
absolute component, so such a name could put a checker source or an owned artifact outside its
directory. The audit keeps one invariant: each module name that it handles has passed
`safeModuleComponents?` at the entry where the name reaches the audit. It refuses an unsafe name
there, before it builds a path from the name.

The entries are these, in `Regula.Checker.ModuleName` and its callers:

- The configuration of each package of each Lake workspace that the audit reads, before a module
  is resolved (`Lake.checkWorkspaceModuleNames`). The readers are `surfaceInventory`, the setup
  commands, the build marker decision and the Verso readers.
- The modules that a package provides, as each package resolves them (`Lake.packageModules`).
- The requested modules of each environment, and each module of the environment that the toolchain
  loaded for them, its imports included (`importReportEnvironment`).
- The import lines that the audit parses, of bound sources, project sources, Verso sources,
  sources to compile and Lean configurations.
- The module of a source specification, and the modules of a serialized graph.

Lake builds a module of any name below the root or a glob of a library. So an import alone can name
a module that no configuration gives, thus the loaded environment is an entry of its own.
`attributeLoaded` also refuses each loaded module with an unsafe name. The paths of checker
sources, package sources and owned artifacts come from `modulePath?`, which refuses an empty base.
**Proved:** `modulePath?_below` and `modulePath?_strict_prefix`. The lexical segments of the base
are a strict prefix of those of the path, and no further segment is empty, `.` or `..`.

Two builds of Regula's own package come before these checks. Lake builds the program
that runs the audit, such as the `lake lint` driver, before it starts that program. The
verification driver of this repository builds its own copy before the gate audits it with
`--driver-copy`. The `lake lint` driver builds its audit worker only after `surfaceInventory`
accepts the workspace that `lake lint` ran in. If it refuses that workspace and `--project` names a
different project, the driver stops with that refusal as `INCOMPLETE`, before the audit.

A loaded module belongs to an owned package only if its `.olean` is exactly that package's
artifact of it below `.lake/build/lib/lean`, on real paths. `Environment.attributeLoaded` decides
it, and the module then binds that package's source. It refuses a loaded module that an owned
package provides and that is no such artifact. A module of the prefixes `Regula` or `RegulaPolicy`
that is the checker's own artifact is the one exception. It belongs to the owned dependency that
alone provides it, and to no package if the root package provides it.

An owned dependency is audited like the root package. Each environment computes what it owns one
time, in `Environment.EnvironmentOwnership.of`, and each job that works module by module takes its
modules from that value. It owns and replays each module of an owned dependency that a requested
module imports, directly or not, or that imports an owned module. The modules of an owned
dependency with the prefix `Regula` or `RegulaPolicy` are not in that set (`projectModules`).
`EnvironmentOwnership.reserved_not_owned` proves that it does not own them, and
`contains_ownedModuleSet` proves that it owns each module of the root package that is not
infrastructure.

The checker's infrastructure modules are not owned, because the gate authenticates them as the
running checker's own. A module of an owned dependency with the prefix `Regula` or `RegulaPolicy`
is not owned either. It is the checker's own code: its source is the checker's own text, and
Regula's own audit checks it with its whole library. `Admission.replaySet` replays each of these
modules that imports a replayed module, such as an owned `RegulaCore` module of `regula`.

A module of a dependency's build output that no library of the package has is refused as
[RG2004]. The account names each dependency that is not owned. It also names each dependency
that provides a module under the reserved prefixes, as `DependencyState.reserved` records. The
snapshot records `owned` for each dependency.

A project audit also inspects each module of an owned dependency that its environment owns and
loads, as `EnvironmentOwnership.mem_dependencies` states. It inspects their declarations,
executable roots and documentation, and the census binds their sources through
`EnvironmentCensus.inspectedModules`. `EnvironmentOwnership.dependencies_replayed` proves that
each of them is in `EnvironmentOwnership.modules`, the owned set. `Admission.validate` replays
`Admission.replaySet`, and `Admission.mem_replaySet` proves that this set holds each module of the
owned set that is not reused.

The coordinator and the declaration worker compute the ownership from the same inputs, and the
worker must report the same modules. The claim lists them as
`ClaimCandidate.dependencies`, so `profileForModule` gives them Standard-Logical and
`executionForModule` gives them report. Thus a project axiom, a hole or authored `unsafe` code in
such a module is refused, but `Classical.choice` is permitted.

The coordinator's findings use the claim's own assignments, from the same surfaces and
dependencies that the claim admits. A declaration meets `projectProfile` of its own module. A root
meets the strongest execution claim that `rootRequestsAmong` finds for it. In a project claim,
`profileForModule_project` and `executionForModule_project` prove that these are the claim's
assignments. With each root requested, `executionFindingsFor_empty_iff` proves that the execution
findings are empty exactly when each root meets each claim requested of it. A declaration of a
dependency that two environments inspect is reported one time, and file and fence audits do not
inspect these modules.

Under `--fresh`, `copyProject` copies each owned dependency with the project, at its place
relative to the project, and the copy builds it. It takes what Lake's own load of the project
selects for each dependency, through `surfaceInventory`. Lake keeps the last entry of a name in
`.lake/package-overrides.json` over the manifest's entry. `relocateDependencies` gives an override
to each dependency that the copy's manifest would load from a different directory or through
different configuration or manifest files.

`Lake.checkCopiedWorkspace` then compares the copy's Lake load with the original's, so a mistake
in the overrides is refused, not trusted. Each dependency must have the same files, configuration
text, output directories, module sources and ownership. Each library and executable of each
package, the root package included, must have the same modules, Lean options and arguments. With
the default layout required, no build of the copy reads or writes a directory elsewhere.

`checkReservedModules` refuses a package module under the prefixes `Regula` or `RegulaPolicy` unless
its source is byte-identical to the running checker's own source of that module. It reads each
package's own library and executable modules before Lake resolves a name to one package. So the
artifact that the overlay loads in place of such a module is compiled from the same text.

The copy holds no compiled module until it builds one, and each owned module of a fresh audit must
resolve inside it on real paths. `ModuleGraph.outsideCopy` finds each one that does not, whatever
directory a configuration gives for build output, and the reporter's overlay cannot serve one. The
coordinator builds each such module in the copy, and the worker refuses one that still resolves
elsewhere. No build of the copy uses Lake's artifact cache, so Lake does not restore a module into
the copy without compiling its source. **Trusted:** the filesystem resolves the real paths, and
only the copy's build writes compiled modules into the copy.

The force-imported reporter loads modules of the prefixes `Regula` and `RegulaPolicy`, and Lean
resolves a whole prefix at the first search directory that has it. So a copy that builds a part of
an owned package with these prefixes could hide the checker's other modules.
`Environment.withProbeSearch` therefore puts an overlay first that links each such module from one
directory. An infrastructure module comes from the checker's library, and each other module from
the first search directory that holds it. That the overlay holds each module that the reporter
loads is read from the code.

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
Unavailable history prevents acceptance, while its execution findings keep [RG3001],
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
| Command hook (`Collect.commandDeclarations`) | Records for the constant binders in this command's information trees; [RG1001]–[RG1007] and [RG1009] when evidence is available. [RG1008] is never rendered: a decision contract normally follows its function, so one command's snapshot cannot decide whether the inventory has one (`editor_decision_none_iff`, `editor_decision_ne_decisionContract`). | Constants added without binder information; not a census. |
| `Collect.currentModule` | Every constant in the current module's map, including private, generated and unused ones. | Completion is the caller's; a partial environment is partial. |
| Module hook | [RG5001] (module docstring present and first, no repeated import), [RG5002] and [RG5003] for registered public declarations. | Complete local declaration-policy coverage. |
| `Collect.declaration` (`.snapshot`, `.replayCandidate`) | The canonical facts `Probe` uses, with replay and helper observations in the second form. | Replay and role authentication. |

**The constructor-index exception is removed.** No unsafe constructor-index wrapper `T.ctorIdx._impl`
is admitted. The supported compiler, Lean 4.34.1, generates none: it builds `T.ctorIdx` by
`casesOn` and has no `getObjTagNat`. The exception admitted such a wrapper on a compiler that
generates one. Its observation, `Collect.constructorIndexObservation`, took the base's runtime
replacement as positive evidence, and an audited project can write that mark. So the exception was
removed with the observer, the `constructorIndex` field, `ConstructorIndexHelperOK` and
`authorizedConstructorIndexHelpers`.

An unsafe `T.ctorIdx._impl` is now an escape hatch like any other unsafe declaration. The mutation
fixture `Fixtures.Mutations.ConstructorIndexHelperForge` is the control. A port to a compiler that
generates the wrapper must establish its admission from kernel-checked data and toolchain
observations alone. Those are the parent's constructors and their indices, the base's and the
wrapper's values compared with the kernel's `casesOn`, and the primitive's origin. Each mark the
project writes, the runtime replacement included, may then only refuse it.

`Collect.declaration` reduces a declared type only when the reduction could produce
`Regula.ExecutableContract` (`ContractScope.mayReach`). That holds when the contract type is among
the type's constants, closed under unfolding, and only modules that import `Regula.Contract`
contribute constants. The search is the decision `MentionSearch.search`
([above](#contract-recognition-and-reach-decision-and-observing-pass)). It reduces a registration's
requirement, to read its decision kind from the head constant, under the same condition for the three kinds
(`ContractScope.mayReachDecision`), so a registration whose requirement cannot reach a kind is
recorded as before, without that reduction. For a recursion helper it reruns Lean's own recursion compiler on the
helper's group (structural recursion with Lean's automatic choice, then on the argument position
Lean recorded for each base, which admits a definition recursing on an argument
`termination_by structural` selects, then well-founded recursion with the relation the base's
fixpoint applies and every decreasing proof elided; where none of these reproduces the base, the
same attempts once more with no definition irreducible, and then in both environments under the
reducibility assignments it searches, both below), with only the toolchain's own
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
added match the observed ones, and then only when the kernel checks the recursion equation of each
base of the group, below), so what is read cannot admit a helper the comparison rejects; this
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
`Erasure.equalWithin` takes a `match` that passes a variable through (`Erasure.Threads`: the
same constant, applied to the variable as one more argument, every alternative binding it once
more) as the `match` that uses the variable directly, comparing each alternative's body with the
bound variable standing for the one passed (`Erasure.threadedParts`). Lean's compilers choose
between these two forms by `isDefEq` on the type of the recursive-call function
(`MatcherApp.addArg`), so the choice depends on what unfolds. The comparison takes that step only
where its observing pass recorded that `Collect.threadingLawChecked` succeeded for the application
(`Erasure.Observations.threading`): for the
constant `M`, parameters and motive `fun ds => A ds → R ds` at hand, the pass states

`∀ ds alts (w : A ds), M ps (fun ds => A ds → R ds) ds alts w = M ps R ds (fun xs => altsᵢ xs w)`

over the variables the application's terms mention (`Collect.scopeOf`), finds a proof
(`Split.splitMatch`, or `cases` on the major premise, then `rfl`), and has Lean's kernel check it
(`Environment.addDeclCore`) with no axiom outside Standard-Logical; the theorem and every constant
the search realizes are then discarded. What Lean records about `M` (that it is a matcher or a
`casesOn`, how many pattern variables an alternative binds) is metadata the audited module can
write, and decides nothing: it proposes the decomposition the law is stated for, and the pass
records a decomposition only where the kernel checked that law (`Collect.observe`). The pure
comparison reads that record and never the metadata. `Fixtures.Mutations.FakeMatcherUnsafeRecForge` registers two
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
to the inspected environment, whose owned declarations the gate replays (standard §7.3);
`Erasure.mem_standingFor_left` and `Erasure.mem_standingFor_right`, by which the pairs under which
the bound variable stands for the passed one relate the bound variable alone, and to exactly the
variables the passed one was paired with; and `Erasure.equalWithin_iff`, by which the executed
comparison accepts exactly the terms `Erasure.EqualWithin` relates, whose two rules for this path
(`threadedLeft`, `threadedRight`) apply only under a recorded law
([the comparison's decision](#the-recursion-helper-comparison-decision-and-observing-pass)). The
rest is argued, with no theorem: that comparing an alternative's body with the bound variable standing
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
That admission does not depend on the reducibility status a called function had where a definition
was compiled is observed for the shapes of [#196](https://github.com/rbeauchamp/regula/issues/196):
the same command admits every helper of `Fixtures.Positive.ReducibleAfter` (a parameter passed
through a function made `reducible` afterwards, under well-founded and under structural recursion; a
`List.map` behind such a function, which the toolchain's `wf_preprocess` rule then sees through; a
second parameter passed through a function that is `@[reducible]` from its declaration; a
`@[reducible]` function made irreducible afterwards, under `allowUnsafeReducibility`; a function an
instance-implicit argument goes through, made `instance_reducible` or `implicit_reducible`
afterwards, or `instance_reducible` first and irreducible afterwards; an `abbrev` that is
irreducible at both points, beside a type made irreducible afterwards; a definition whose base needs
two changes, beside four further `@[reducible]` functions at its leaf, beside an authored `_sunfold`
declaration of its helper that mentions five more, or whose helper cites a theorem whose proof
mentions five more and that is applied to no function of the group, none of which Lean's compilers
ask about; and a definition with a proof that calls it with a parameter passed through a function
made `reducible` afterwards, abstracted by `as_aux_lemma` into a theorem applied to the function,
which the structural compiler unfolds before its fixed-parameter analysis) and of
`Fixtures.Positive.ReducibleWhereCompiled` (a status that holds only where the definition is
compiled: `attribute [local reducible]` under well-founded and under structural recursion, on the
two functions of two recursive calls that pass one parameter, on a function the `List.map` rule then
matches through, on two functions of which one unfolds to the other and that one to `List.map`, also
where the definition calls the second directly as well, on six functions of which each unfolds to
the next and the last to `List.map`, on a
function that a `@[reducible]` function the definition calls unfolds to, on two functions that the
rule matches through only together, on three such functions under a definition with one varying
argument, which Lean does not pack, and on the discriminant of a `match` in a recursive call's
argument, also behind a function that unfolds to that `match`; a `@[reducible]` function made
semireducible afterwards; `attribute [local irreducible]` on an `abbrev`; `attribute [local
instance_reducible]` and `attribute [local implicit_reducible]`, which need no
`allowUnsafeReducibility`; a function of an imported module made `reducible` after the definition;
an `instance_reducible` function made `reducible` after it; a definition that reaches seven
definitions of its module, of which two change a decision; and one that passes seven parameters
through seven functions made `reducible` afterwards; a definition with an `Acc` argument, which
Lean compiles by well-founded recursion; a parameter passed through a `match` whose discriminant is
made `reducible` afterwards, also beside one passed through a function made `reducible` afterwards;
under structural recursion, a parameter passed through a `match` whose discriminant goes through a
function of another module made `reducible` afterwards, is an `abbrev` that is irreducible only
where the definition is compiled, or is made `reducible` afterwards beside a parameter passed
through a function that is `reducible` only where the definition is compiled; a `List.map` behind a
function, over an argument whose type goes through two more, all three `reducible` only where the
definition is compiled; and definitions by structural recursion over an inductive predicate that
pass seven parameters through seven functions, made `reducible` afterwards or `reducible` only
where the definition is compiled). The
search this one replaces enumerated the definitions of the helper's
module that the helper reaches and gave each the statuses a global attribute could have replaced.
Under it the forms that the second fixture's comment names as such were observed rejections on
Lean 4.34.0, and the definition that reaches seven definitions an audit that stopped without a
verdict; the forms it marks as new were not run under that search, and of those found in review
the comment states what was observed. Its assignments are
still tried, after those of the search described here (the fallback below). Lean's fixed-parameter
analysis (`getFixedParamPerms`) compares each argument of a recursive call with the parameter by
`withReducible <| isDefEq`, which checks an instance-implicit argument at implicit transparency, and
the preprocessing `simp` matches through reducible definitions, so both depend on which definitions
are `reducible`, `instance_reducible` or `implicit_reducible`. Lean keeps no history of a status
(`reducibilityCoreExt` holds the last one, and a `local` attribute leaves nothing behind), and the
kernel's reducibility hint tells only an `abbrev` apart.

Where neither environment reproduces the base, `Collect.unsafeRecRegeneration` therefore searches,
and `Collect.statusCandidates` proposes what it tries in each of the two environments:

- Which definitions. `Collect.recordConsults` is installed as `Meta`'s unfolding predicate
  (`Meta.withCanUnfoldPred`) around Lean's own function and records each definition Lean asks about
  at reducible, instance or implicit transparency, whatever module declares it, and for each what
  the answers came to (`Collect.Consults`): whether the answer was, each time, that the definition
  unfolds, and how often, at each of the three transparencies, it was that it does not. The answer
  is Lean's own (`Meta.canUnfoldDefault`), except in the second recording of the preprocessing
  below. Lean 4.34.0 decides such an unfolding from the status alone
  (`Meta/GetUnfoldableConst.lean:17-31`): `reducible` unfolds
  at all three, `instance_reducible` at instance and implicit, `implicit_reducible` at implicit, and
  semireducible and irreducible at none. To decide what a status changes the checker does not
  use that rule: it gives a
  definition each of the four statuses of `Collect.triedStatuses` (semireducible,
  `implicit_reducible`, `instance_reducible`, `reducible`, the one that unfolds least first), runs
  Lean's function under each, and keeps one status for each result. Irreducible is left out, since
  it answers there as semireducible does. It restates the rule in one place,
  `Collect.unfoldsBelowDefault`, for the two uses named below: the answers of the second recording
  of the preprocessing, and the statuses that answer a question a change newly raises.
- The discriminant of a `match`. Lean 4.34.0 puts the predicate aside while it reduces the
  discriminant of a `match` below default transparency (`Meta.whnfMatcher`, through
  `Meta.withCanUnfoldAtMatcherPred`, which sets the custom predicate to none) and reads the status
  itself (`Meta.canUnfoldAtMatcher`), so a definition it asks about only there is not recorded
  where the discriminant reduces. Each decision is therefore recorded a second time in
  `Collect.withoutReducible`, the environment in which every `reducible`, `instance_reducible` and
  `implicit_reducible` definition is semireducible: there no discriminant reduces for a status, the
  `match` is stuck, and a run that goes on to unfold the matcher asks about the discriminant again
  under the predicate. That run decides nothing; it only adds the definitions it asks about to
  those the search gives another status.
- The fixed parameters (`Collect.fixedParameterStatuses`). The group is given to
  `getFixedParamPerms` as each compiler gives it: after `Structural.preprocess` for the structural
  compiler, which replaces each theorem applied to a bare function of the group with the theorem's
  value (`Meta.unfoldIfArgIsAppOf`, `Meta/Transform.lean:266-288` of Lean 4.34.0), and after
  `WF.floatRecApp` for the well-founded one; the one the observed bases show, and both where their
  kind is not read. A first run answers that every definition asked about unfolds, so that every
  comparison runs to its end and the definitions any comparison unfolds are recorded; the second
  recording does the same with no definition unfolding for its status, where the comparison
  unfolds the matcher of a stuck `match` and asks about its discriminant. Each is then
  given each of the four statuses, and its own where that is irreducible, while the others are
  `reducible`, and is a candidate where another status than its own changes which parameters are
  fixed.
- The preprocessing (`Collect.preprocessingStatuses`), where the recursion can be well-founded. The
  first steps of Lean's `wfRecursion` run as in the regeneration (`Collect.wfPacked`), and
  `WF.preprocess` runs on the packed definition under the recording predicate with Lean's own
  answers. Each definition recorded is given each of the four statuses but its own, alone, whether
  the helpers' values mention it or another definition unfolds to it (found in review: a function
  behind a `@[reducible]` one was left out, and its helper rejected, `FixturesWhereTree.hidden`). A
  change that changes the preprocessed body is a candidate. The second recording runs with the
  answers of the inspected environment and with matchers unfolding (`Reading.discriminants`), and
  adds the definitions Lean asks about only in a discriminant. Where a change leaves the body as it
  was, it is followed (`Collect.followChange`): the definitions the preprocessing then asks about,
  without their unfolding, more often than it does before any change (`Collect.newlyStuck`) are
  given a status that answers the question, and each extended change is followed in the same way,
  until a run changes the body or raises no such question. There are three kinds of extension.
  The first path gives all of those definitions that no toolchain rule's left-hand side mentions
  (`Collect.patternConstants`, the constants of the keys Lean indexes the rules under) the status
  `reducible` at once. The second gives those same definitions, at once, the status that unfolds
  least among those that unfold at the transparency asked (`Collect.unfoldingStatuses`), where
  that is another assignment. The third gives all of them `reducible`, where a rule's left-hand
  side mentions one. A rule matches through a function only where the
  function unfolds, and with it unfolded Lean's matching goes on to the next function that does
  not, which it asks about once more than before: following those questions reaches a rule that
  needs several functions together, whether one unfolds to another
  (`FixturesWhereTree.chained`, six functions; found in review, when the search stopped after five
  runs and left that helper undecided) or the definition calls each directly
  (`fixtures_where_typed_size`, three definitions the preprocessing asks about before any change,
  two of them in a type). A constant a rule's left-hand side mentions has to stay as it is for
  that rule to match: `List.map` itself is asked about once a function unfolds to it, and
  unfolding it too keeps the rule from matching, so the first path leaves such a constant alone.
  What a change is extended with depends on the change alone, not on the changes it was reached
  through, so a change is run and extended once, whichever change reached it, and every change
  that extends it is reached from it (found in the second review of this search: the questions
  were once counted against the run of the change extended, so what a change was extended with
  depended on the route, while a change was still run once). A change
  that still leaves the body as it was
  is then paired with each other definition its own run asked about without that definition
  unfolding each time: that definition is given each status that answers the question beside the
  change, one at a time, and the pair is
  followed in the same way. A change found below the first is a candidate, of the definition whose
  status was changed first; one found through a pair only where it gives a body that no change
  found before it gives, since a pair whose body one of its two changes gives alone says nothing
  about the other; and one that only adds statuses to another change with the same body is
  dropped.
- The assignment tried first. `Collect.observedFixedParameters?` reads which parameters each
  observed base keeps outside its recursion, from the shape Lean's compilers give it: the parameters
  passed to the `_unary` or `_mutual` definition a well-founded group is packed into, the ones bound
  before the fixpoint where the base is that definition itself, the ones passed to the functional
  `_f` of a structural definition, or, where the base applies `brecOn` itself, as Lean writes a
  definition by structural recursion over an inductive predicate, the ones it does not pass to
  `brecOn` after the inductive type's own parameters (`Collect.belowRecursionArguments?`). Each
  candidate of the fixed parameters is given the status that
  unfolds least among those under which the analysis still fixes all of them.
  `Collect.survivingMentions` counts the mentions of a constant that compilation keeps (outside
  proofs, types, and the relation and measure of a fixpoint). Where the preprocessed body keeps
  another number of mentions of some constant than the observed definitions do, the change selected
  is one after which it keeps the observed number of each. Tried first for that is one change for
  all the functions concerned, each made `reducible` where the body keeps more mentions of it and
  semireducible where it keeps fewer, since a rule can need several functions to unfold together,
  and that change is followed and paired in the same way;
  then each candidate's own changes. The numbers only order the candidates and select that change:
  no candidate is left out for them.
- The enumeration. `Collect.candidates` then enumerates the assignments: every way to give one or
  more of the candidates another of its changes, when there are at most `Collect.candidateLimit`
  (63), and otherwise only the first 63 single candidate changes, each of which gives one candidate
  another status and, where it was followed or paired, the functions it was followed through and the
  one it was paired with theirs. Each assignment
  is installed (`Collect.withStatuses`) over the environment it was found in, and all attempts run
  under it, each regeneration with the heartbeat budget of one declaration (`withCurrHeartbeats`).
- The fallback. Where none of those assignments reproduces the base, `unsafeRecRegeneration` tries
  the assignments of the search this one replaces. `Collect.earlierStatusOptions` visits the
  definitions of the helper's own module that the group reaches, from the members' types and from
  their values after `Meta.unfoldIfArgIsAppOf`, closed under `Collect.statusReferences`, and pairs
  each with the statuses a global attribute can have replaced (`Collect.earlierStatuses`):
  semireducible for a `reducible` or an `instance_reducible` definition, semireducible or
  `instance_reducible` for an `implicit_reducible` one, and `reducible`, `instance_reducible` or
  `implicit_reducible` for an irreducible one. An `abbrev` is left out, except that one that is
  irreducible at the end of the audit is kept irreducible in the environment with no definition
  irreducible. `Collect.candidates` enumerates them under the same limit, and each assignment is
  tried in both environments. The options, the limit and the order are those of the replaced
  search, so each assignment it tried is tried. It once was what reached a definition Lean asks
  about only while it reduces the discriminant of a `match` that reduces at the end of the audit
  (found in review, `fixtures_where_later` and `fixtures_where_both`), which the second recording
  now finds. What it still reaches that nothing records is a status Lean reads without asking its
  predicate and outside a `match`: Lean 4.34.0 does so where it tests whether a type is a class
  (`Meta.isClassQuickConst?`, through `getDefInfoTemp`) and where instance resolution meets a
  `reducible` head it did not unfold in a term with a metavariable (`DiscrTree.getKeyArgs`), read
  from its source.

One helper's search therefore runs at most 2 + 2 × (1 + 63) + 2 × 63 = 256 regenerations, of at
most three compiler runs each.

What is machine-checked is the enumeration, `Collect.mem_candidates` (where `candidates` reports
that it is exhaustive, it holds every nonempty list that takes one alternative each from some of the
candidates, the relation `Collect.Picks`) and `Collect.candidates_length_le` (it never holds more
than the limit). Neither states anything about what a regeneration does with an
assignment, about Lean's own `canUnfoldDefault`, or that the definitions recorded are all that Lean
consulted. The rest is argued, with no theorem:

- Soundness. An assignment only selects which regeneration runs. `Collect.unsafeRecRegeneration`
  returns an origin only when `Collect.regenerationMatches` accepts the definitions a regeneration
  added and the kernel then checks the recursion equation. The verdict of that comparison is the
  pure decision `Erasure.reproduces`, whose only arguments are those definitions' values, the
  observed values of their names, the observations of their terms and whether the observing pass
  finished: no assignment, status or environment is among them, which its signature shows. Its observing pass runs after the saved
  state, environment included, is restored and Lean's caches are emptied, so it reads the observed
  definitions in the inspected environment whatever assignment the regeneration ran under. Every question the search asks
  (`Collect.decisionIn`) is undone the same way, and its answers reach nothing but the list of
  assignments. The fallback's assignments are read from statuses, kernel
  hints and module membership, and select a regeneration like the others.
  So no assignment, and no failure to find one, admits a helper whose value differs
  from its base: a search that finds nothing returns no origin, and one that stops at its bound
  throws. The observing pass does consult state the audited module can write (the inspected
  environment's own statuses, where Lean decides what is a proof or a type, and matcher metadata,
  which proposes a decomposition for the kernel to check), as the comparison did before the search;
  an assignment adds nothing to that, and the decision reads the pass's answers, not that state. That a regeneration under any
  assignment is Lean's compilation of the helper's recursion is the same trust as for the
  environment with no definition irreducible: the fixed-parameter analysis keeps a parameter outside
  the fixpoint only where `isDefEq` accepts that every recursive call passes it unchanged, `isDefEq`
  proceeds by unfolding definitions to their values, and a status decides only whether a definition
  is unfolded; the preprocessing rewrites by the toolchain's proved equations.
  `Fixtures.Mutations.ReducibleAfterUnsafeRecForge` is the control: with a candidate assignment
  available in each direction, a faithful copy of the helper is admitted and one that calls another
  function at its non-recursive leaf is rejected.
- Completeness, for a status that changes which parameters Lean finds fixed or which toolchain rule
  applies. The two decisions are the steps that the source of Lean 4.34.0's recursion compilers
  shows to unfold below default transparency (`Elab/PreDefinition/FixedParams.lean:205-226` and the
  `simp` call of `Elab/PreDefinition/WF/Preprocess.lean`); the other steps unfold at default
  transparency, where only an irreducible status decides, which the environment with no definition
  irreducible gives back. Below default transparency a status decides only through Lean's answers,
  so two assignments that answer alike for every definition a decision asks about run it alike, and
  the four statuses a definition is given cover every way its status can answer there, since
  irreducible, the one left out, answers as semireducible does (read from
  `Meta/GetUnfoldableConst.lean:17-31`, not checked). For the fixed parameters, a
  parameter is fixed exactly where each comparison for it succeeds, and a comparison succeeds where
  the definitions on its way unfold at the transparency asked. With every definition unfolding, each
  comparison runs to its end, so each such definition is recorded, and with every other one
  unfolding each such need shows as a change of the result. The assignment that gives each candidate
  the status that unfolds least while the observed fixed parameters stay fixed therefore meets every
  need of those parameters and no other, wherever more unfolding never makes a comparison fail. For
  the preprocessing, a rule that matches through a function replaces the application it matches, so
  the number of mentions the base keeps tells whether it applied.
- What was observed for the three forms that remained of
  [#196](https://github.com/rbeauchamp/regula/issues/196), on Lean 4.34.0 before the second
  recording, the following of newly raised questions and the fourth shape were added. A status
  Lean asks about only in a discriminant that reduces at the end of the audit, and that the
  fallback does not reach: `fixtures_where_elsewhere_match` (a function of another module),
  `fixtures_where_sealed_match` (an `abbrev`) and `fixtures_where_mixed` (beside a status only the
  recorded questions find, which the fallback's assignments were not joined with) were rejections,
  under structural recursion; under well-founded recursion the preprocessing asks about such a
  discriminant on its own, as a term it simplifies, and the last two shapes were admitted. A rule
  that needs three definitions the preprocessing asks about before any change, where the mentions
  the base keeps do not tell them apart: `fixtures_where_typed_size` was a rejection. A definition
  by structural recursion over an inductive predicate: `fixtures_where_predicate`, whose seven
  functions are made `reducible` afterwards, was admitted by the regeneration in the inspected
  environment, and `fixtures_where_predicate_local`, whose seven functions are `reducible` only
  where it is compiled, was an audit that stopped without a verdict, its 127 assignments being
  more than the enumeration tries and no assignment being selected for a base of its shape. All
  five are admitted now, and `Fixtures.Mutations.ReducibleWhereCompiledUnsafeRecForge` holds the
  controls for the first two paths: a faithful copy of the helper is admitted, and one that calls
  another function at its non-recursive leaf is a violation. `fixtures_where_accessible`, which
  takes an `Acc` argument, is no definition of the third kind: its type is no proposition, and
  Lean compiles it by well-founded recursion (observed).
- What that argument leaves out. The second recording asks about a discriminant only where a run
  goes on to unfold the stuck matcher: the fixed-parameter analysis does so with every definition
  unfolding, and the preprocessing because the recording answers that a matcher unfolds, which
  Lean's own run does not, so that run can differ from Lean's where a discriminant is stuck at the
  end of the audit too. Its questions only add definitions to try. A status Lean reads without
  the predicate and outside a `match` (the two places named at the fallback) is found only by the
  fallback: a base that depends on such a status of a definition the fallback does not reach
  would be rejected, which was traced from Lean 4.34.0's source and not observed.
  The candidates the enumeration has for the preprocessing are found from one definition at a time
  and followed through the questions a change newly raises. A rule that needs several definitions
  of which none, unfolded, makes the preprocessing ask about another more often than it does
  before any change, and
  that no pair with a definition the run asked about reaches, is found only through the assignment
  the observed bases select, where the mentions the bases keep tell those functions apart
  (`FixturesWhereTree.size`, with three functions and one varying argument, is selected that
  way). The count of questions is of the answers that a definition does not unfold, at each of
  the three transparencies: a change that raises one such question about a definition and removes
  another leaves the count as it was, and that definition is not followed. Neither was observed.
  The constants whose mentions are counted leave out the group's own functions:
  Lean packs nothing for one function with one varying argument (`WF.packMutual`), so the
  preprocessed body keeps its calls to the function itself, which a base, calling itself through
  its fixpoint's argument, never mentions (found in review: with those calls counted no change was
  selected for that definition, and it was a rejection, observed).
- Termination and cost. Each question is one run of Lean's own function with the heartbeat budget of
  one declaration, and the counts below are for one environment, of the two searched. The fixed
  parameters take, for each input (one, or two where the kind of the bases is not read), two runs
  and then four for each definition recorded, five where that definition is irreducible there. The
  preprocessing takes three runs, and then for each definition recorded three changes, four where
  it is irreducible there. A change is followed along its first path to that path's end: each run
  on it gives at least one more definition of the environment a status, so there are fewer of them
  than the environment has constants. Beside that path it is followed through at most 64 runs
  (`Collect.followLimit`). A change that leaves the body as it was takes, beside that, one such
  followed change for each definition it is paired with and each status that answers, so the runs
  grow with the square of the number of definitions recorded. The change made for several
  functions at once is one more change, followed and paired in the same way. `followChange`
  recurses on a depth one above the number of constants, counts the runs beside the first path in
  its state, and records a change it would have run with none left (`Collect.Followed.unrun`),
  which the search reports as undecided, not as
  unchanged; a change so recorded that a later change reaches with runs left is run then, and no
  longer counts. No fixture reaches that bound: that it ends in an incomplete audit is read from
  `followChange`, `preprocessingStatuses` and `unsafeRecRegeneration`, which throws before it can
  answer that the helper is not regenerated, not observed. `assignments?` stops as soon as more
  than 64 assignments exist, deciding list by list, so it never builds more than 64 times one
  candidate's alternatives plus one.
  `earlierStatusOptions` takes one step for each constant of the environment at most, and each
  step visits a constant of the helper's module that no earlier step visited, so the visit ends;
  it answers that it did not, and the helper is undecided, if constants were still pending. The 256
  regenerations bound the regenerations alone, not these runs.

`Fixtures.Mutations.ReducibilitySearchBoundUnsafeRecForge` pins the bound of the enumeration: a
forged helper whose seven candidates allow 127 assignments, and that neither the assignment its base
selects nor any of the seven single changes reproduces, is neither admitted nor rejected. The
fallback stops at its bound for this helper too, since the same seven functions are the definitions
of its module that it reaches, so the error names both bounds; the fixture's expected pattern
requires the text of the enumeration's (`assignments of another status`), which the fallback's
message does not hold.
Every bound the search stops at ends the same way. `unsafeRecRegeneration` throws, naming the
helper as undecided and the bound it stopped at, and the audit fails as incomplete, with no
violation reported for
the helper, as it does at a resource limit of the checker (`checkerSelftest fixtures` requires that
outcome with no violation before it matches the text). Incomplete, not a violation, is the verdict
the checker has: a helper no attempt within the bound reproduces may still be what Lean generated,
so reporting it as a violation of the rule would assert what the checker has not established, and
the helper is not admitted either way. The helper Lean generated for a definition of the
seven-candidate shape does not need the enumeration (`fixtures_where_seven`), and the helper Lean
generated for the shape that the replaced search left undecided is now admitted:
`fixtures_bound_searched`, and in `Fixtures.Mutations.ReducibleAfterUnsafeRecForge` the helper of
that shape and its faithful copy.

The fallback has the same bound. Where the definitions it gives a status allow more than 63
assignments, only the first 63 single changes are tried, and a helper none of them reproduces is
undecided in the same way, as is one for which `earlierStatusOptions` did not visit every
definition reached. `Fixtures.Mutations.ReducibilityFallbackBoundUnsafeRecForge` pins it: the
divergent copy of a helper of that shape reaches seven definitions of its module with a status a
global attribute can have replaced, none of the three assignments of the two that change a
decision reproduces it, and neither does any of the fallback's seven single changes, so it is
neither admitted nor rejected, as it was under the replaced search.

Every observation the checker takes from Lean's reduction runs with smart unfolding off
(`Collect.withoutSmartUnfolding`, applied by `Collect.declaration` and by `Probe`'s observations).
With `smartUnfolding` on, `Meta.unfoldDefinition?` of Lean 4.34.0 unfolds an application of `g`
through the declaration named `g._sunfold`, looked up by that name, without comparing its type
or body with `g`'s. Lean generates that declaration for a structurally recursive definition; an
audited module can write one for any function.
`Fixtures.Mutations.AuthoredSmartUnfoldingUnsafeRecForge` holds the two forgeries found in review
([#209](https://github.com/rbeauchamp/regula/issues/209)), both admitted while the checker's
observations ran with smart unfolding on, on Regula v0.4.2 too (observed): an authored identity
`_sunfold` for a `reducible` successor function, under which the fixed-parameter analysis takes
`next a` for `a`, drops the argument and reproduces a base that returns `a` from a helper that
returns `a + n`; and an authored `_sunfold` of value `Type` for a type-valued function, under
which `Meta.isType` takes a value of that type for a type and the comparison erases a leaf that
differs. With the option off both are rejected and the honest
helpers are admitted (observed). That Lean reads no `_sunfold` declaration with the option off is
read from its source (the name is used behind the option in `Meta.unfoldDefinition?`, and
otherwise only where `simp` unfolds declarations it is told to unfold, which the regeneration's
`simp` is not), not proved. The `_sunfold`
definition the structural compiler adds for a regenerated base is still compared with the observed
one, like every definition a regeneration adds.

That a helper admitted under [RG1006](https://rbeauchamp.github.io/regula/dev/rules/RG1006/)
computes its base rests on a theorem Lean's kernel checks, not on the regeneration
([#210](https://github.com/rbeauchamp/regula/issues/210)). After a regeneration
reproduces the base, `Collect.recursionEquationChecked` states, for each helper of the group, the
recursion equation of its base: with the helper's value `fun xs => body`, every helper of the
group replaced by its base `f`, the theorem

`∀ xs, f xs = body`

It builds the statement from the constant `f` and the helper's value alone, confirms its form by
`Expr` equality (`Collect.isRecursionEquation`: every leading binder of the value is taken, the
binder types and the body are the value's own, and `f` is applied to the bound variables in
order), and gives it to the kernel of the inspected environment as the type of a theorem
(`Collect.kernelChecked`: `Environment.addDeclCore`, then every axiom within Standard-Logical).
The type of the equality is read from `body` by Lean's elaborator and is not compared: the kernel
checks that the statement is well typed before it checks a proof, which leaves the equality only
the type of `f xs`, up to definitional equality. No theorem is trusted for its name, and no
statement is compared with one found in the environment: a name only selects a candidate, and the
kernel checks the candidate as a proof of the statement the checker built. Who declared a
candidate is not consulted. The candidates are these, tried in this order:

- `Eq.refl (f xs)` where `body` is a proof: Lean states no unfolding theorem for a definition
  whose type is a proposition, under structural or well-founded recursion, and the kernel accepts
  reflexivity by proof irrelevance;
- any constant of the inspected environment named `f.eq_def`, or by that name made private to the
  module of `f` as a `module` file has it (`Collect.unfoldingTheoremNames`). Lean's well-founded
  compiler adds a theorem of that name with the definition, and a module can declare one itself;
- what `Meta.getUnfoldEqnFor?` returns for `f`: a constant of the name Lean computes for the
  unfolding theorem where the environment holds one, and otherwise the theorem Lean realizes on
  demand for a structural definition; and
- the theorem it realizes for the regenerated definition, in the environment the regeneration
  left, under the reducibility in which Lean's compiler reproduced the base. A definition whose
  own type is a definition made irreducible afterwards (`fixtures_alias_binary` of
  `Fixtures.Positive.ReducibilityChange`) is admitted by this one alone (observed).

Lean realizes such a theorem with its kernel check deferred: `Environment.realizeConst` of Lean
4.34.0 runs the realization with `debug.skipKernelTC` set and replays the result into the kernel
afterwards, keeping a constant the kernel rejects out of the kernel environment but not out of the
elaborator's. No constant a search adds is therefore trusted. `Collect.closedOver` replaces each
constant the inspected environment does not hold by its value (a realized theorem by its proof, a
regenerated definition by its body), and the kernel of the inspected environment checks the
resulting term against the statement, so it checks every step that is not a constant of that
environment. `closedOver_closed` proves that the term submitted mentions no other constant; it
proves nothing about `Expr.replace` or the values put back, and the kernel rejects a term that
mentions an unknown constant in any case. A constant the kernel of the inspected environment
holds is one the gate's admission replays, one of the trusted import base (standard §7.3), or one
Lean realized earlier in the checker's process and its kernel accepted on replay.

What this establishes, and what it does not:

- Kernel-checked, at each audit: the base satisfies the recursion equation of each helper of its
  group, with every axiom within Standard-Logical. That holds whatever the regeneration or the
  search read. Matcher and `casesOn` metadata, the `below` and `brecOn` declarations of an
  inductive type, `_sunfold` declarations, reducibility statuses and Lean's equation records are
  inputs of a selection or of a proof search; a statement the checker built and a proof the kernel
  accepted do not depend on them.
- Argued, with no theorem: whenever the helper returns, it returns the base's value. The compiled
  helper evaluates its value, its recursive calls evaluating the helper again. By induction on
  that evaluation, each recursive call that returns has returned the base's value, so the helper
  returns what its value yields with each helper of the group replaced by its base, and the
  equation says that is the base's value. The argument takes the compiled code to run the helper's
  value (the trusted compiler, as for every definition) and to use a function it is given only by
  calling it. A helper that calls a `partial` or `unsafe` constant outside its group is not
  admitted: the kernel refuses a theorem whose statement mentions one (observed for a `partial`
  helper on Lean 4.34.0: "safe declaration must not contain partial declaration").
- Not established: that the helper returns whenever the base does (standard §7.4), or anything
  about a helper for which the search finds no proof.

The search restricts where a proof is looked for, not who wrote it. It tries only reflexivity, the
constants of those names and what Lean realizes, so a helper is rejected where none of these is
accepted, even where the equation holds and could be proved another way. It does not restrict a
candidate's origin: `recursionEquationChecked` submits whatever constant has the name, and the
kernel checks that constant's proof against the statement the checker built, with every axiom
within Standard-Logical. A metaprogram that adds a well-founded definition and its helper can
therefore supply `f.eq_def` by copying the theorem Lean proved or by proving the equation itself,
and either is accepted exactly when the kernel accepts it for that statement; the statement
checked, not the author of the proof, carries the guarantee. This is read from the code, and the
copied theorems of the faithful-copy fixtures, which the fixture's metaprogram declares and not
Lean's compiler, are accepted (observed); a proof written independently was not run.
`fixtures_forged_measured_bare` of `Fixtures.Mutations.MeasuredMatchUnsafeRecForge` pins the
rejection: a faithful copy of a well-founded definition and its helper, added by a metaprogram
with no theorem named `eq_def`, is rejected, and the same copy with theorems of that name is
admitted (observed). A faithful copy of a structural definition needs no theorem of its own, since
Lean realizes one for the regenerated definition (`fixtures_forged_alias_faithful` of
`Fixtures.Mutations.ReducibilityChangeUnsafeRecForge`, observed).
`Fixtures.Positive.ProofValuedRecursion` pins a structural and a well-founded definition whose
type is a proposition, both admitted by reflexivity (observed). A resource limit of the checker
reached in the search or in the kernel leaves the helper undecided and the audit incomplete, as
for the regeneration.

Two forgeries show what the equation closes. Each is an ordinary definition that Lean's own
compiler turns into a base and a helper that disagree, and `axiomGate --file` accepted each on
`main` at `2e741c6`, before this check (observed; the regeneration paths they use are those of
Regula v0.4.2, whose [RG1006](https://rbeauchamp.github.io/regula/dev/rules/RG1006/)
([as released](https://rbeauchamp.github.io/regula/v/0.4.2/rules/RG1006/)) they were not run
against):

- `Fixtures.Mutations.AuthoredCompanionUnsafeRecForge`. A metaprogram adds an inductive type of
  unary numbers with Lean's `casesOn` and `below`, and writes `brecOn` itself, as a function that
  ignores its arguments and returns `0`. Lean's structural compiler finds `brecOn` by name and
  checks only the type of the application it builds, so the base of a definition by recursion on
  that type is `0` everywhere (a kernel-checked theorem of the fixture) while its helper returns
  `1` at `zero`. The regeneration runs the same compiler over the same `brecOn` and reproduces the
  base.
- `Fixtures.Mutations.MatcherMetadataUnsafeRecForge`. A function that applies its one alternative
  to a constant function is registered as a matcher whose alternative binds no pattern variable.
  `MatcherApp.addArg` then puts the binder for the recursive-call function before the
  alternative's own argument, where Lean's test that the type was refined succeeds because a
  definition in it is irreducible and the kernel accepts the two argument types as one. The
  recursive call becomes a call of the constant function: the base is `42` at `1` (a
  kernel-checked theorem of the fixture) and the helper returns `0`. Lean itself reports that it
  cannot prove `eq_def` for the definition, after it has added the base and the helper; the
  fixture drops that error, as a metaprogram that adds both declarations would. The regenerated
  base is the observed one, with no application left for the threading law to check.

With the check, each forged helper is rejected and the honest helper beside it is admitted
(observed, `checkerSelftest fixtures`): the equation is false at `zero` and at `1`, so no proof
exists within Standard-Logical unless Lean's logic is inconsistent, and what Lean's search does in
each case (it finds no `brecOn` application; it finds no unfolding theorem) only saves the kernel
the attempt.

What the admission of a helper reads by a derived name or from metadata the audited module can
write, and what authenticates each:

| Name or record | Read by | Authenticated by |
| --- | --- | --- |
| `f._unsafe_rec` → `f` | `Compiler.isUnsafeRecName?` | Selection only: the helper is admitted only where the regeneration from its value reproduces `f` and every auxiliary definition, and the kernel checks the recursion equation of `f` for that value. |
| `f._unary`, `f._mutual`, and `f._f` and `f._sunfold` of the helper's base | Added by the regeneration under its root; `Collect.wfRegeneration` reads the observed unary definition's relation | Each regenerated definition must equal the observed one of its name. The relation only selects: the comparison drops it, and the well-foundedness proof is the observed kernel-checked one. |
| `g._sunfold` of any other constant | Lean's smart unfolding; formerly also `Collect.unfoldReferences` | Not read: every observation runs with smart unfolding off, and the search's closure follows no `_sunfold` declaration. |
| Matcher and `casesOn` metadata, in the comparison's observing pass | `Collect.observe` | The kernel-checked threading law of each application (`Collect.threadingLawChecked`): the pass records a decomposition only where the law is checked, and the pure comparison reads that record alone (`Erasure.Threads.law`). |
| Matcher metadata, in reduction | `Meta.whnfMatcher`, `Meta.reduceMatcher` | The constant's own value is unfolded. |
| A matcher's equations and splitter | The proof search of `threadingLawChecked` | Guidance only: the kernel checks the theorem found. |
| Projection metadata | The `paramProj` preprocessing step; unfolding a projection function | `paramProj` moves only `wfParam`, the identity; the function's own value is unfolded. |
| `Structural.eqnInfoExt`, `WF.eqnInfoExt`, reducibility statuses | The regeneration | Selection only, never an argument of the comparison: `Erasure.reproduces` takes the two values, their observations and whether the pass finished, and nothing else. |
| `T.rec` | The structural compiler | A recursor is created by the kernel with its inductive type. |
| Matcher and `casesOn` metadata, in Lean's compilers during the regeneration | `MatcherApp.addArg`, which passes the function standing for the recursive calls through a `match` | Selection only: the kernel checks the recursion equation of the base (`Collect.recursionEquationChecked`). The regeneration alone admitted `Fixtures.Mutations.MatcherMetadataUnsafeRecForge`. |
| `T.below`, `T.brecOn` of an inductive type of the audited module | The structural compiler, by name | Selection only: the kernel checks the recursion equation of the base. Lean generates them with an `inductive`; a module that adds an inductive type by metaprogram can declare others, and the regeneration alone admitted `Fixtures.Mutations.AuthoredCompanionUnsafeRecForge`. |
| `f.eq_def`, by name; `Structural.eqnInfoExt` and the other records from which `Meta.getUnfoldEqnFor?` realizes a theorem, for the base and for the regenerated definition | The proof search of `recursionEquationChecked` | Guidance only: every constant the search adds is replaced by its value (`Collect.closedOver`), and the kernel of the inspected environment checks the proof against the statement the checker built. |
No theorem covers the regeneration itself, which runs in Lean's elaborator; since the equation
check, it selects the base and carries no claim about what the helper computes. The comparison's
verdict is a pure decision with a kind
([above](#the-recursion-helper-comparison-decision-and-observing-pass)); its observing pass
does not compare the two values with `Meta.isDefEq`: where two values differ under a recursive
call, its lazy unfolding of the self-referential helper does not terminate. The pass does use
Lean's definitional equality inside the check of a threading law (`Collect.threadingLawChecked`
type-checks the law's left-hand side and closes its cases with `rfl`), where the kernel then
decides. The regeneration runs Lean's elaborator in the
report worker and is undone before the comparison, whose pass reads the observed definitions and
observes erasure in the inspected environment; a pass that throws counts as no regeneration. The
report's other elaborator observations (`Meta.isProp`, the pretty-printed type, and `Probe`'s
executable-root classification) run under Lean's default limits. When one fails,
the report worker's error names the module, the declaration (for an execution walk, its root) and
the failing stage: `declaration record` (any observation of `Collect.declaration`),
`executable-root classification`, `proposition test` or `execution walk`. When the failure is one
of those limits, or a kernel limit (deterministic timeout, deep recursion or excessive memory,
recognized by the renderings in [`Collect.kernelLimits`](../../lean/Regula/Collect.lean)), it says
the limit is the checker's own, that options set in the source, such as `maxRecDepth`, do not apply
to the checker, and to report it as a Regula issue; the audit is still incomplete. The recursion helper's regeneration and native
replay, which otherwise record their own failure as missing evidence, rethrow such a limit
instead. A replacement's correspondence search rethrows an elaborator limit, but its kernel check
runs under its own budget and records exhaustion as an unresolved correspondence (standard §7.6).

The adapter runs the same pure policy and total failure-to-ID mapping as the project checker
(`Regula.Checker.Policy.editor_decision_rule`); a potential generated-role exception is deferred
as [RG2005] rather than guessed. A decision kind that the snapshot cannot read is deferred the
same way. Lean gives a file with a `module` header an imported theorem, such as the projection
function of a proof field, as an axiom, so that environment cannot say whether an argument of the
decided function is a field. The collector then records the registration with no failure of its
kind, and the adapter reports the reading as incomplete and names `lake lint`, which reads the
kind from an environment that has every declaration. This deferral is operational collector code
(`hiddenField?` in `Regula.Collect`): the pure policy finds no contract failure in that record,
and no theorem about the editor decision covers the deferral. Recoverable compiler errors can leave
hole-bearing declarations, which still yield [RG1002] while the original compiler error is preserved; unavailable collection is
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
own build. The audit's fresh elaboration passes the unregistered command-line marker
`weak.regula.auditBuild`. The linter reads the marker only from the import-time options of a
module, and under it the linter emits nothing. `lake lint`'s claimed build also passes the marker,
except under the owner's `--ordinary-lakefiles` for a workspace of the plain shape
([acceptance boundary](#the-acceptance-boundary)). There no module of the root package imports
`Regula.Linter`, so the linter runs on none of them.

**Documentation presence.** `Lean.findDocString?` accepts ordinary, Verso and inherited
docstrings; private names follow Lean's visibility and never enter the public `@[regula_material]`
selector. [RG5001] reads Markdown and Verso module-doc metadata loaded with `importAll := true`,
`loadExts := true` and `level := .private`; an empty loaded array means absence, an unknown module
identity is unavailable evidence rather than an absent doc comment, and current metadata is
checked only after module completion by the module hook. [RG5001] reads the header's imports with
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
inventory search it replaces (`declarationIndex_get`), and an [RG1005] finding built with that
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
`GeneratedFamily.mem_all` proves the list the checker tries and the [RG1005] guidance names holds
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
self-consistent passes. `RegistryChecks` exhaustively checks the 24 descriptors, the embedded
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
| `S.x._autoParam` | `Lean/Elab/Structure.lean:1120-1123` | own location: a `Syntax` value, which uses no axiom, so it has no [RG1005] finding | |
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
existing manifest fails [RG2002]), as [RG2006] does: `run_sets`, every required option a claimed
target built without is then set to its required value as `RegulaPolicy.Community.sets` reads
it, which meets [RG2006]'s requirement on that option (`meets_of_sets`); `resolved_run`, every
claimed target then has a value for every required option or a `-D` candidate of its own extra
`lean` arguments names it; `added_unargued`, no option the plan adds to the package or to a
claimed target's own configuration names an option that a `-D` candidate of that target sets
(the candidates of `RegulaPolicy.Community.argumentSettings`, [RG2006]'s own reading, which
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
new observation does not claim, as while a starter manifest fails [RG2002], is not compared), and it
writes the starter manifest only after `Manifest.parse` reads the text back as exactly that
manifest. That the lakefile edits realize
the model's `apply` is this check, not a theorem. That `allClaimed` holds only when the observed
targets are every root `lean_lib` and `lean_exe` is how `observe` builds the observation, and the
extra `lean` arguments it reads are those of the audit's inventory, read by the same
`Lake.libraryOptions` and `Lake.executableOptions`. `doctor` runs the audit's own [RG2002] functions
(`Manifest.loadFor`, `Acceptance.surfaceAssignments`, `AxiomGate.checkClassification`) and [RG2006]
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
libraries; a library whose modules are all such roots is refused as [RG2002] by `doctor`. `doctor`
prints one [RG2006] finding for the claimed targets that share a claim and the same failure
detail, where the audit prints one per target. The agent-guidance file is found operationally:
from the Lake root up to the nearest directory holding a `.git` entry (Git itself is not run),
the nearest `AGENTS.md` with the section, else the nearest that exists, else the repository
root's; the skill files are read and written at that repository root (the Lake root outside a Git
repository).

Regula's `lakefile.lean` executes the core-only source `RegulaPolicy.Compiler` when its
configuration is elaborated, in a child `lean` that `LEAN_SYSROOT` or `PATH` selects. The
source guard compares that child's version and full commit with the revision's declared
identity and then prints them; the lakefile passes only when the child succeeds and the
printed pair is the `Lean.versionString` and `Lean.githash` of the Lean elaborating the
lakefile, so a child that is another compiler, fails or cannot be run is refused, with the
adopter's remedy. That comparison is an elaboration-time check, not a theorem. The compiled
probe, inventory admission, and plan admission use the same declared pair.
`Compiler.accepts_iff` proves the executed Boolean matches the predicate;
`transcript_plan_compiler` proves admitted transcripts and a valid plan agree on both fields.
Compiler self-reports and locating and launching the compiler are trusted IO, and a
self-report names the Git commit of a build's source tree, not uncommitted source edits or the
executable's bytes. Lake may reuse an elaborated configuration; `lake update` elaborates it
again. The compiled admission guards remain in force when a configuration is cached.

`doctor` reads the project's own `lean-toolchain`, resolves it to a toolchain
`elan toolchain list` names, and reads the version and commit that compiler reports,
independently of the compiler running `regula`. Only a listed name is run, without Elan's
`--install`, and no channel is resolved: `Regula.Toolchain.installedName?_spec` proves that the
name is one of those supplied as listed and equals the selector.
`Regula.Setup.toolchainIssues_eq_nil_iff` proves that the
decision reports no toolchain issue exactly when that resolved identity
`RegulaPolicy.Compiler.Supports`, under any selector; an unresolved selector or a failed probe
is an issue `init` does not fix. Elan's listing, that it runs a listed toolchain without
installing, and the report are trusted.

Only the exact [supported toolchain](toolchains.md) is admitted. Historical diagnostic
envelopes with `purpose: compiler-qualification` are refused by ordinary result readers;
there is no runtime qualification switch or candidate publication mode.

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
historical version-string guard's refusal of Lean 4.33.0 and 4.34.1 through the `lake` command
line and when a checker executable loaded the workspace. Those historical observations do not
qualify the new exact-identity guard. Its retained control, in the `lint-driver` partition,
loads a fresh copy of the lakefile and policy source through `lake`: an inherited
`LEAN_SYSROOT` whose `lean` fails on the policy source is refused, one whose `lean` exits
successfully without printing the running compiler's identity is refused by the identity
comparison, and the same package then loads with the inherited environment. Neither child is
a compiler. A compiler the policy refuses, an in-process load by a checker executable and
`doctor`'s resolution of a pin need a second installed compiler or current observations and
have no retained control.

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
again just before it creates the branch, holds exactly when every release listed before the one
the step
handles is published and every published release is one of them (`publishedExactly_iff`); when
it holds, that release's listed predecessor is the latest published release
(`publishedExactly_latest`), and a release whose listed predecessor is unpublished, or is earlier
than a published release, is refused (`publishedExactly_refuses`), both given the releases before
it listed in ascending order, which `releases_ascending` checks. So once a release is published,
no release listed in its place is released. `pullBranch`, the name of the branch the open step
creates for the release pull request, is the same for two builds of a release only when they are
the same commit (`pullBranch_inj`), so builds with different commits never share one.
`releasePulls` selects, from the pull requests GitHub reports open, exactly those whose head is
a branch `pullBranch` names for the release's version in the repository (`mem_releasePulls`,
`isPullHead_iff`). `branchAction`, the decision of the open step over them, creates the branch
exactly when there is none (`branchAction_create_iff`) and otherwise refuses, naming the first
(`branchAction_refuse_iff`). `branchStep`, the program the step runs on that observation, is,
while one is open, exactly the refusal `refuseOpen` that names one of them, whatever the commit
(`branchStep_open`), and with none it is the creation (`branchStep_unopened`). These hold for
what the step observed just before it writes: a release pull request opened after the
observation is not excluded. That `refuseOpen` writes no reference is read from its definition,
which writes the job summary and fails; it is not a theorem. Separately, that the open step
never moves a branch that exists, and so never changes the branch of a pull request that is
open, whatever it observed, is by construction and not a theorem: its only write of a branch is
`createBranch`, GitHub's request that creates a reference, and that GitHub refuses that request
when the reference exists is trusted. `admits`,
which the open step also
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
`RegulaCore/Edition.lean`, `lakefile.lean`, the adoption guide's compatibility table and each
`require` of Regula in the tracked Markdown documents are read back before use; its stamps of
`RegulaCore/Rule.lean` are a convenience that reads text. `agree`,
a step of `verify` before acceptance, refuses a `lakefile.lean` version, as Lake reads it
(`lake reservoir-config`), other than the latest listed release's, a compatibility table
other than the one `Regula.releases` gives, and a `require` of Regula in a tracked Markdown
document that names a different release than the latest listed one, as the text reading
`setPins` reads it (`pinsAgree_iff`). That reading finds a `require` only on a line with the
repository's address in quotation marks, exactly as `gitUrl` writes it. Thus `agree` also refuses
unless the root `README.md` and the adoption guide each have a `require` of each form
(`unpinned_eq_nil_iff`). The kernel checks the edited modules' theorems when
the release pull request's checks and CI's checks of the release commit build them:
`releases_ascending`, `releases_follow`, `installed_listed`, `release_attributes_rules` (when
`installed` is a release, no lifecycle position of any rule is `.unreleased`; on the release
commit this is the gate before anything is published), `lifecycle_listed` (every release a rule's
lifecycle names is in `versions`) and `introduced_startsLine` (the release that introduces a rule
has patch `0`, so it is not a patch release). What the steps observe (whether the release is
published, the versions of the published releases, read from the tags of the releases GitHub
lists that are not drafts, the head of `main`, the tag, the commits since the previous release,
the pull requests open and their heads, observed just before the open step writes its branch and
not again afterwards, a pull request's title), GitHub's signature verification, that GitHub
refuses to create a
reference that exists, that publishing a release
creates its tag at the given commit, tags, immutable releases, pull requests, squash merges
taking the pull request's title and description, workflow ordering, and that Lake and Reservoir
read and order versions as their source shows ([Reservoir](contributing.md#reservoir)) are
trusted.

## The diagnostics gate

**Proved** in `lean/Regula/DiagnosticsGate.lean`, checked by the kernel in ordinary acceptance's
build and each time a step of the [diagnostics workflow](../../.github/workflows/diagnostics.yml)
elaborates it (its `diagnostics` job on every pull request, and `applies` whenever it runs):
`verdict`, the decision of the required `diagnostics` check over the workflow's `needs` context,
passes exactly when the job `applies` succeeded, every job it decided is one the gate needs, and
every job the gate needs passed when it was decided to apply and was skipped when it was decided
not to (`verdict_iff`, with `admits_iff`). So a failed or cancelled job is refused, as is one
that ran out of time, which GitHub reports as one of the two, and as is a job decided to apply that
was skipped, as the jobs not yet started are when a run is cancelled. `decisions`, the decision
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
decided job the gate does not need fail the gate. The
compiler-preparation job `compiler` is not a partition job: `applies` needs it and has no `if:`,
so `applies` runs, and the gate can pass, only once `compiler` succeeded (GitHub's implicit
`success()`, trusted, and also the workflow's wiring).

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
| rule-examples | 48 Fixed/Violation productions | every published example yields exactly its documented findings | External | observed |
| rule-examples | 3 refusal productions | the producer's own request and classification account | External | observed |
| rule-examples | 7 record mutations, 7 admission subprocesses | `qualify` refusals | Proved | `RuleExampleQualification.qualify_sound` |
| checkerSelftest fixtures | in-process and CLI fixture verdicts; fence corpus; diagnostic-setup controls | compiler, elaborator, CLI and fence workers | External | observed |
| checkerSelftest fixtures | 11 execution-policy cases | failure kind per boundary and claim | Proved | `boundaryFailures_ids`, `rootFailures_ids`, `executionFailureRecords_empty_iff` |
| checkerSelftest fixtures | scanner cases of the protocol and of the shape rule, for Markdown and for Verso | `Documentation.scan` and `scanVerso` marker, fence and shape problems | Counterexample aid | `checked_scanLines` and `checked_scanVersoLines` prove that a result has no violation exactly for a clean document. The cases observe words of a violation and the number of fences of the clean texts. |
| checkerSelftest structural | in-process manifest cases | `Manifest.parse` acceptance, decoding and the classified refusal classes | Proved in part | `Manifest.parse_sound`, `parse_input`, `parse_emptyExclusions`, refusal-class theorems; other refusals (a missing required field, an unknown exclusion key) are unclassified |
| checkerSelftest structural | real manifests, missing file, unlisted modules, fresh-checker coverage, CLI refusal rendering, Lake discovery, executable classification | file IO, CLI rendering, Lake inventory | External | observed |
| checkerSelftest structural | a lemma realized in a claimed module and the toolchain, in both import orders; unchecked, circular, `sorry` and kept-cycle copies of one name | Lean's realization, import, kept copy and kernel check of several copies of one name | External | observed; the copies are checked by `Admission.checkCopies` (`checkCopies_sound`) in the decision `admitReplay` (`admitReplay_eq_ok`), over the replayed constants of `replayMap` (`replayMap_sound`, `replayMap_complete`) |
| checkerSelftest structural | a function declared in one claimed module and registered with `attribute [regula_decision]` in another, without and with its decision contract, as plain files and as `module`s | Lean's saving and loading of the registration, and the collector's reading of it | External | observed; the decision over the recorded declaration is `policyFor_decisionContract_iff` |
| checkerSelftest structural | a function that one claimed library marks, with its only contract in a second library that imports it: with the manifest relation, without it, and with the relation and with no contract, each in a fresh project of its own | the manifest field, the freeze of the counted records and the account through the public gate | External | observed. The decided implementations over the census are `census_decided_iff`, and the parser refuses a relation to no claimed surface (`parse_relations`). |
| checkerSelftest execution | each compiler-path mutation and correspondence control, with its positive and fresh restoration | compiler-derived execution coverage and correspondence evidence through the public gate; the emitted-C check of reachable code on the pin | External | observed |
| checkerSelftest cli, environments, build-policy, lint-driver | CLI sweep, adopters, clean checkout, ordinary build, `lake lint` exit classes, its claimed build with and without the audit-build marker, cold compiler guard refusal of a failing and of a successful unidentified child process with its restored load, a forged correspondence theorem of an owned path dependency refused by replay and one of a dependency in a Git work tree of its own refused as evidence ([RG3002]) | packaging, Lake and build integration | External | observed |
| ordinary | `qualify registry`, `qualify native` | CLI output invalidation, registry and site validators; compiler messages and ranges | External | observed |
| ordinary | `RegistryChecks` codec, source and execution-account cases | registry, diagnostic and source codecs; the result file's shared execution form | Proved in part | round-trip theorems of `Json` values, with those of each finding and each location (`parseDiagnostic_roundtrip`, `parseLocation_roundtrip`); that the shared form is kept, and that a parsed shared form reads back to the built account, are observed; open: state the remaining refusals as theorems |
| standalone | `qualify environments` finalize mutations | `finalize` refusals | Proved relation | `finalize_iff`; instance membership sampled; no transcript substitution: an accepted run has no transcript job (`accepted_no_transcript_subjects`) |
| standalone | `qualify acceptance fences` packet mutations | worker-packet admission through a real proxy | External transport | admission proved (`checked_indexedResults`) |
| standalone | snapshots, input inventory, receipts, frozen exits, documentation source, closure, configuration and fence evidence | Git, Lake, filesystem, elaboration-time IO, signals | External | observed |
| project audit | admission reuse recheck | a report that reuses a module, or requires a key in a reused module, that no earlier environment offered over a frozen closure, or leaves an owned module it loaded unreplayed, is refused | Proved | `Admission.reuseJustified_frozen`, `Admission.reuseJustified_admitted`, `Admission.replayed_of_loaded` |
| project audit | changed import, changed `.olean` part | an owned module is replayed unless an offer covers it over its closure here and over artifacts read again with their frozen parts | Proved | `Admission.replayed_unless_offered`, `Admission.replayed_of_changed`, `Admission.replayed_of_changed_import`; an artifact not read again with its frozen parts cannot support an offer (`Admission.Unchanged`) |
| checkerSelftest structural | a changed, removed and added `.olean`, `.olean.server` and `.olean.private`, each restored, for a module with three parts and with one, through `Inspection.readings` and `Admission.currentOffers` | reading the frozen parts: each change withdraws the offer and `Inspection.changedArtifact?` reports it | External | observed |
| checkerSelftest structural | a fresh audit of two claimed libraries that import one another | the report workers, Lean's import and the kernel reuse a requested module: accepted, each module replayed in one environment, the reused module's key required | External | observed; the decision is `Admission.reuseJustified_admitted` and `Admission.replayed_of_loaded` |
| project audit | none | a frozen `.olean` part that changes during the audit is [RG2005] | External | open: MUT-02 not yet evidenced through the gate; reading the parts is observed directly (two rows above), and no intended-reason control rewrites a part between the freeze and the final comparison |

The `qualify` campaigns and what they observe:

- `registry`: six malformed invocations invalidate stale output; the validators accept real
  exports and refuse each removed field, the previous schema and a missing page.
- `native`: 42 compiler controls for identity, multiplicity, severity and warning promotion,
  ranges, current and imported ownership, private and generated coverage and both documentation
  formats. Each control is its own compiler process with its own source path, run four at a time
  in dependency order: imported-artifact controls after the artifacts they import, restored
  controls after every malformed one.
- `native-launcher`: 42 paired baseline/cached-environment controls with exact equality.
- `producers`: for the incremental and build-lint entrypoints and each of [RG5001]/[RG5002], one
  workspace runs Fixed, then Violation over that Fixed build (so a stale build must not hide the
  violation), then Fixed again from a cleared build. A standalone executable additionally has
  positive and owned-axiom controls, each in its own fresh workspace, and each carries module
  documentation so the intended axiom violation is isolated. Each invocation checks exact stable
  ID, detail, primary location, related locations and result status, and requires unique output
  and exact embedded source/selector/type/axiom evidence. The fresh-project [RG5001]/[RG5002]
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
  mutation), `history` ([RG3001] fresh, incremental and build-lint history refusal and restoration)
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
the JSON string, the JSON string of the claim is its written form (`Profile.toString`), an absent
`executables` is empty and a present one is its string array, and an absent `execution`
is `report` while the JSON string of a present one is its spelling (`ExecutionClaim.spelling`) (`SurfaceDecodes`,
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

The infrastructure controls need the checker's own package as the audited project: a claimed module
that imports the probe's report records, collector or compiler observer must be refused as
contamination although the force import brings those modules into every report. They run in a copy of the repository whose
manifest `Manifest.structuralManifest` derives (`structural_libraries`,
`structural_executables` and `structural_roundtrip`, under the claim hypothesis its guard
checks at run time). `RegulaPolicy` stays claimed there because the checker probe's own imports
resolve to it in a self-hosted copy;
`Regula.Checker.Environment` does not elaborate unless every module in the probe's import closure
outside the toolchain is a `RegulaPolicy` module or one of
`RegulaPolicy.infrastructureModuleNames` (the command beside `probeModuleNames`, whose docstring
states what it does not see). The controls are two clusters, both in the first shard, whose
queue runs them beside one another.

`structuralSelfHosted` builds its copy and runs the incremental gate on each of the three
contaminations. It restores each contamination before the next. Then it records the fresh input
of the restored copy with `freshInput`: the files that the copy operation of a fresh gate copies
from it. `structuralSelfHostedPositive` prepares a different copy with `prepareSelfHosted`,
records its fresh input and then runs the accepting fresh gate on that copy.

After the queue of the first shard stops, `selfHostedIdentity` compares the two fresh inputs
path by path and byte by byte. A difference fails the shard. This comparison takes the place of
an accepting fresh gate on the restored copy. It shows that the restorations gave the copy the
same fresh input as the copy that the positive gate accepted.

The comparison does not prove that a fresh gate accepts the restored copy. That result also
rests on a fact that is not a theorem. A fresh gate reads the audited project only through
`copyProject` and builds that copy from empty output. `copyProject` does not copy `.lake`, so
the gate does not read the output of the setup build, of the seed or of the incremental gates.
Without `--with-docs`, as here, the gate reads no other file of the project, and it links the
packages directory of the repository for each copy. The restored fresh gates of the clusters in
the structural project run the same path on a project with such output in its `.lake`.

The copy of the first cluster starts with the module artifacts of the build of the repository
(`seedModuleArtifacts`). Thus its contamination gates do not build `RegulaPolicy` and the probe
modules again from empty output. The verdict of each such gate comes from its build, the
manifest, the Lake inventory and the module graph. The graph worker reads each `Regula` module
from the library of the running checker, before the output of the copy. Thus the files of the
copy for the probe modules have no effect on the graph.

Lake uses a seeded `RegulaPolicy` or `AuditApp` artifact only if its saved trace agrees with the
hash of the inputs of its module. The bytes of the source are one of these inputs. Thus Lake
always builds the contaminated root from its contaminated source. This statement is a reading of
the module build of Lake, not a theorem. The fresh gates do not read the seed, because
`copyProject` does not copy `.lake`.

A fresh gate on a self-hosted copy builds and inspects `RegulaPolicy` from empty output, and
the first cluster is a serial chain, which was the first shard's longest item, so each fresh gate
in it added its whole duration to that shard. With an accepting fresh gate before the mutations and
another after their restoration both in that chain, in one instrumented local run (2026-10-03,
14 cores) those two gates took 47 s and 43 s of the cluster's 117 s and the three contamination
gates 23 s, and on the slower hosted runners the cluster took 262 to 266 s beside 100 to 108 s
for cluster `a`, so that the shard's timed step took 394 to 414 s and once reached its
420-second deadline. The
gate on the unmutated copy therefore runs as the positive cluster, beside the chain, and the four
clusters in the structural project (`a`, `b`, `c` and `d`) run in the second shard, which no
longer holds the positive. With cluster `a` still in the first shard, beside the chain and the
positive, that shard's timed step took 354 s and 362 s on the slower hosted runners
(Diagnostics run 37178141571, attempts 1 and 2): the chain took 205 and 208 s there, beside 162
and 163 s for the positive and 139 and 142 s for `a`. The target for each structural
shard is a timed step (the `Qualify` step of its job in the diagnostics workflow) of at most
360 s on every run, a margin of at least 60 s (14 %) under the unchanged 420-second deadline.
That step includes the build of the self-test and its checker executables: on the slower
hosted runners (Diagnostics runs 37170060453 and 37171425583, both shards), 147 to 157 s of it
had passed when the first control started. That is a target, not a bound, and the timings above
are observations: the deadline alone refuses a run.

On the slower hosted runners, the timed step of the first shard took 405 s at commit `e6c4c996`,
with 242 s for the chain. With the seed, Diagnostics run 37979063520 took 368 s, with 198 s for
the chain and 156 s for its restored fresh gate. The chain now holds no fresh gate, so the
positive is the longest item of the first shard. Without that gate, the timed step took 295 to
308 s on the slower hosted runners (Diagnostics run 38015750002, attempts 2, 4 and 6). The chain
took 40 to 41 s there and the positive 133 to 138 s.

Each partition's baseline build names what its controls read from the repository's own build
(`Partition.baseline`, and `baselineOf` for a shard). The gates of these two partitions run in
projects of their own, where the gate builds that project's targets itself, and the manifest
controls run `axiomGate` on the repository with a manifest it refuses before any build. So the
structural baseline is `axiomGate`, `docFenceAudit` and `freshChecker` (its first shard, whose
controls run `axiomGate` alone, names only that; its second keeps the partition's baseline),
the execution baseline is `axiomGate` alone, and neither builds the
repository's claimed surface; the lint-driver baseline is `axiomGate` and `lint`, and the other
partitions keep the complete baseline. That is a reading of the controls' code, not a theorem.
For the structural and execution partitions, two guards bound it: after the baseline build,
`toolPath` refuses an executable that build did not name (for every checker executable the
self-test's own module runs, other than itself), and `baselineOf_axiomGate` proves that every
baseline names `axiomGate`, which `CompilerPaths` and `PolicyQualification` run by its path. A
claimed-surface `.olean` that a control of these two partitions read from the repository's build
without the baseline naming it would be absent on a clean checkout and fail that control there;
on a warm local build it is not detected. `scripts/verify.sh` builds the self-test, `axiomGate`
and, for a structural or lint-driver selection, the other checker executables its baseline names
(none for the first shard) in one Lake invocation
(`RegulaVerification.commands`), so the gate's own modules compile beside the self-test's last
ones instead of after its link; that command selects nothing, and the baseline build still
names and builds its targets. The frozen-artifact, cross-surface decision, library cycle, driver
copy and manifest controls run in the structural clusters' queue, so no more of them run at
once than the queue has workers.

The lint-driver controls run `lake lint` in adopters of their own, which require `regula` as a
Lake path dependency of the checkout. The two guards and the clean-checkout argument above do not
cover the modules that these adopters read from the repository's build. If the baseline did not
build such a module, an adopter's Lake builds it there instead of a refusal, possibly in several
concurrent groups. No guard detects that. Each module that the adopters import is one that
`axiomGate` or `lint` imports, apart from `Regula.Linter` and `Regula.Linter.Rules`, by a reading
of import lines. The control `toml/absent-worker` runs alone before the other controls, and it
builds those two because its adopter's `examples/lake-lint-toml/Gadget/Double.lean` imports
`Regula.Linter`.

The controls of each of these two partitions are divided into two shards, `1/2` and `2/2`
(`--shard`), which the diagnostics workflow runs as separate jobs. Every control carries its one
shard where the partition lists it, and a shard runs the controls that carry it (`inShard`);
`inShard_cover` proves that the two selections together are a rearrangement of the whole list,
so each control runs in exactly one shard. Both shards list the same controls because they run
the same sources, which no theorem states. The structural shards are the mutation clusters
`self-hosted` and `self-hosted-positive` with the frozen-artifact and cross-surface decision
controls, and `a`, `b`, `c` and `d` with the library cycle, driver copy and manifest controls; the
execution shards hold one correspondence cluster each and alternate compiler-path cases. A
shard's PASS names the controls it ran and is not the partition's.

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

The lint-driver partition runs the control `toml/absent-worker` first and alone, because it
removes the `axiomGate` of the repository's build. Then four workers run the other controls in
groups, and each worker takes the next group when it is free (`LintQualification.qualify`). The
groups are listed longest first, by the times below. Each group writes its start and its time to
the job log. The path-dependency controls are one chain in one adopter, which the queue runs as
three groups.

Each of these three groups starts from the same files of the adopter. The chain is cut at the
two points where it has restored each file that it changed. At these points, the files differ
from the start only in build output and in one module that the next control writes again. Thus
each control reads the files that it read in the chain. Only the first control of a later group
that builds starts with no build output. In the chain, it started with the output of the
controls before it.

On the slower hosted runners, the timed step of `diagnostics lint-driver` reached its
420-second deadline after the path-dependency and owned-checker controls were added
(Diagnostics runs 38073121895, 38074694772 and 38077207189, jobs 114274540988, 114279196648 and
114289264598). In these job logs, the prologue from the start of the deadline to the build took
about 3.5 s. Then the build of the self-test took 160 to 169 s, the baseline build 42 to 46 s and
`toml/absent-worker` 10 to 12 s. That baseline build also built the fixtures, the claimed
surface, `docFenceAudit` and `freshChecker`, which no lint-driver control reads.

From the end of `toml/absent-worker`, where the groups start, `lean` took 140 to 153 s and `toml`
121 to 133 s. The group `owned-checker` took 84 to 93 s, and the part of the path chain that is
now `path-owned` 85 to 93 s (up to `path/owned-standard-logical`). The deadline killed each run
190 to 202 s after the groups started, while the path chain was still running. Its last complete
control was `path/override-last-fresh` in run 38073121895 and `path/owned-override` in the other
two. The groups `cache`, `empty-facets`, `dependency-cache`, `escaped-name` and `guard` did not
start in these runs.

Two faster runs passed under the old schedule (Diagnostics runs 38071832852 and 38077102864, jobs
114270714472 and 114289843134). Their builds of the self-test took 110 and 135 s. There, `lean`
took 105 and 118 s and the whole path chain 162 and 179 s. After the chain, in later batches,
`cache` took 18.7 and 20.7 s and `empty-facets` 17.1 and 19.2 s. Also, `dependency-cache` took
14.9 and 17.1 s, `escaped-name` 14.7 and 16.5 s and `guard` 3.1 and 3.5 s.

The next numbers are derived, not logged. In the faster runs, the chain took 1.52 to 1.54 times
as long as `lean`. With that ratio, the times of `lean` in the runs that reached the deadline give
a chain of about 213 to 236 s. Thus `path-names` and `path-layout` share about 120 to 151 s. The
time of `lean` in the runs that reached the deadline is 1.19 to 1.46 times that of the faster
runs. Scaled by that factor, `cache` takes at most about 30 s, `empty-facets` 28 s,
`dependency-cache` 25 s, `escaped-name` 24 s and `guard` 5 s.

The order of the first four groups comes from the runs that reached the deadline. The order of
the five short groups comes from the faster runs. The order of `path-names` and `path-layout`
comes from local runs on a developer machine. In these local runs, `path-names` took a half to
three fifths of the time of the two. No other source gives that division.

No worker of the queue is idle while a group waits. Thus a group starts not later than a quarter
of the summed times of the groups listed before it. It ends not later than that time plus its own
time. The four groups listed first start together. No schedule of four workers ends before the
longest group or before a quarter of the total time of the groups.

With these inputs, the groups take about 640 to 727 s together. Thus the lower end is about 160
to 182 s, more than the time of `lean`. At the upper inputs, each group listed after the three
path groups ends by about 199 s. The two later path groups end by about 261 s at most, and by
about 208 s with the division of the local runs. At the lower inputs, the groups end by about
188 s with that division.

Before the groups, the timed step has about 3.5 s of prologue and the build of the self-test, 160
to 169 s. Then the baseline build takes about 0.5 s, because the build of the self-test also made
its targets. That time comes from local runs of the new schedule. The control
`toml/absent-worker` takes 10 to 12 s. With the groups, the prediction for the timed step is
about 362 to 393 s.

The times other than that of the baseline build are from the old schedule. Thus the result is an
estimate, not a bound on the new schedule. The target is a timed step of at most 390 s on three
runs on the slower hosted runners, 30 s under the deadline. The prediction straddles that target,
thus the margin rests on the CI observations of this change. The job logs of these runs print the
start and the time of each group. That is a target, not a bound, and the deadline alone refuses a
run.

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
  accepts has an empty `packages` array. `RegulaVerification.Decisions` registers the kinds of
  the driver's decisions ([above](#decisions-not-registered-with-regula_decision)). Process
  execution remains IO.
- The theorem `RegulaVerification.ordinary_places` gives the directory of each command of the
  first step. Three commands operate in the copy, and the gate starts in the root of the
  checkout.
- The theorem `RegulaVerification.inOrder_append_beside` shows that the schedule runs each
  command of a mode one time. The theorem `beside_prebuilt` shows that the command beside the
  others is the gate of the copy. It also shows that a prebuild in the copy names `axiomGate` and
  each of `gateTargets`.
- The theorem `RegulaVerification.prebuild_builds` shows that a prebuild is a build. The theorem
  `prebuild_named` shows that the build of the mode names each target of a prebuild again.
  The theorem `prebuildCovers_iff` shows that the driver accepts only a surface manifest with no
  claimed target outside the prebuild. That Lake then builds nothing again is the behaviour of
  Lake. The use of `nice` by the operating system is trusted.
- The theorems `walked_iff`, `removal_remove_iff` and `removal_nothing_iff` of
  `RegulaVerification` state the decisions of the copy and of the removal. The theorems
  `ScratchCopy.name?_eq_some_iff` and `ScratchCopy.inside_iff` state the two decisions with which
  the gate admits a copy of the driver. The reads of the file system that give their arguments
  are trusted.
- The theorems `RegulaVerification.passed_iff` and `passed_covers` are about the function
  `passed`. If `passed` accepts the entries of the commands of a step, each command has an entry
  with exit status 0. The driver reports success only after `passed` accepts. That
  caller is read from the code and is not proved.

## Changes to Lean's environment, compiler or build

Regula's guarantees are for honest code, as the [scope](../../SECURITY.md#scope) of the security
policy tells. Honest code does not deliberately change Lean's environment, compiler or build to
make a check pass. Code that makes such a change through a mechanism for which the standard or a
rule page states a check is also honest code. Ordinary declarations, attributes such as
`implemented_by`, `extern` and `csimp`, and `initialize` are honest code. Standard §7.6 tells how
the execution account treats each of them.

The axiom collection and the execution account ([RG3001], [RG3002]) trust that the project makes
no such change. Where the standard or a rule page states a check for a mechanism, that statement
governs, and the mechanism is in scope. The examples below are out of scope only where no such
statement covers them. Each one is a trusted boundary of the axiom collection, of the execution
account or of the two:

- **A direct write to the state of an environment extension that no rule or section of the standard
  checks.** Such a write goes around the command or attribute that Lean gives for that extension.
  The axiom table `exportedAxiomsExt` that Lean calculates when it writes a module is not such an
  extension, because [RG2005] states its check. The rules [RG1001]–[RG1005] use the axioms that
  each owned declaration reaches in the replayed kernel, as [**Axioms**](#producers) tells. A write
  to that table cannot remove an axiom from them, and admission refuses a table with an axiom that the
  declaration does not reach. The controls `Fixtures.Mutations.ForgedAxiomTableOmission` and
  `Fixtures.Mutations.ForgedAxiomTableAddition` are observations of the two cases.
- **A declaration of a dependency that a metaprogram adds with `debug.skipKernelTC`.** [RG2005]
  states the check for an owned declaration, thus an owned declaration is in scope.
  [Admission](#producers) replays the owned declarations that are not `unsafe` or `partial`
  through the kernel. It refuses such a declaration that the kernel does not accept, and the control
  `Fixtures.Mutations.LocalUncheckedAdmission` is an observation of one refusal. Admission does
  not replay an `unsafe` or `partial` declaration or a declaration of a dependency that the audit
  does not own. The axiom collection trusts each declaration that admission does not replay.
- **A user compiler pass, or a direct write that stores a compiled body that Lean's compiler did
  not make.** A declaration with the attribute `@[cpass]` can add, remove or replace a pass of
  Lean's compiler. A direct write to the IR or LCNF extensions can store a body that the compiler
  did not make, for example an `fdecl` body. The execution account reads the compiled code in those
  extensions. It trusts that the passes of the pinned compiler made each body that it reads.
  [RG3001] reports a write that leaves a retained compiled body missing, or that leaves an opaque
  export placeholder, as unresolved.
- **An `f._unsafe_rec` companion that [RG1006] does not inspect, for example one in a dependency.**
  Lean's compiler compiles `f` from the value of `f._unsafe_rec` if that constant exists, in
  `Lean.Compiler.LCNF.toDecl`. [RG1006] admits an owned recursion helper only where Lean's
  recursion compiler regenerates its base from it, as
  [the recursion-helper comparison](#the-recursion-helper-comparison-decision-and-observing-pass)
  tells. Controls such as `Fixtures.Mutations.ByElabUnsafeRecForge` are observations of refusals.
  The execution account trusts that each other `_unsafe_rec` constant, for example one of a
  dependency, is the helper that Lean's recursion compiler made.
- **A native build setting: `extern_lib`, `moreLinkArgs` or `moreLeancArgs`.** These give native
  code or options to the C compiler and to the linker. The execution account reads the compiled
  Lean code, not the native objects that the build links. It trusts that the linked program runs
  that code.

Regula finds some changes of this kind, where the standard or a rule page states the check. An
accepted result makes no claim that the project has none of the changes in the list. The
[README](../../README.md) puts Regula at the `#print axioms` step of
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

The later steps of that page, `lean4checker` and comparator, replay declarations through Lean's
kernel. Thus the two refuse a declaration that `debug.skipKernelTC` adds and that the kernel does
not accept. `lean4checker` does not calculate or compare axiom sets, thus it does not find a direct
write to the axiom table. Comparator calculates the axioms from the declarations that it exports,
not from that table. It refuses each axiom that is not one of its permitted axioms.

No step of that page checks the changes to compiled code. These are a compiler pass, a direct
write that stores a compiled body that Lean's compiler did not make and a native build setting. An
`_unsafe_rec` companion that [RG1006] does not inspect is also such a change. Thus these changes
stay trusted boundaries of the execution account of [RG3001] and [RG3002] and of the native replay
of [RG1004]. To check a proof from a source that you do not trust, use
[comparator](https://github.com/leanprover/comparator).

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

[RG1001]: https://rbeauchamp.github.io/regula/dev/rules/RG1001/
[RG1002]: https://rbeauchamp.github.io/regula/dev/rules/RG1002/
[RG1003]: https://rbeauchamp.github.io/regula/dev/rules/RG1003/
[RG1004]: https://rbeauchamp.github.io/regula/dev/rules/RG1004/
[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
[RG1006]: https://rbeauchamp.github.io/regula/dev/rules/RG1006/
[RG1007]: https://rbeauchamp.github.io/regula/dev/rules/RG1007/
[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG1009]: https://rbeauchamp.github.io/regula/dev/rules/RG1009/
[RG2001]: https://rbeauchamp.github.io/regula/dev/rules/RG2001/
[RG2002]: https://rbeauchamp.github.io/regula/dev/rules/RG2002/
[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/
[RG2004]: https://rbeauchamp.github.io/regula/dev/rules/RG2004/
[RG2005]: https://rbeauchamp.github.io/regula/dev/rules/RG2005/
[RG2006]: https://rbeauchamp.github.io/regula/dev/rules/RG2006/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
[RG4001]: https://rbeauchamp.github.io/regula/dev/rules/RG4001/
[RG4002]: https://rbeauchamp.github.io/regula/dev/rules/RG4002/
[RG4003]: https://rbeauchamp.github.io/regula/dev/rules/RG4003/
[RG4004]: https://rbeauchamp.github.io/regula/dev/rules/RG4004/
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
