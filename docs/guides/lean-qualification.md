# Lean qualification tooling

Project-owned implementation follows the Lean 4 policy in `AGENTS.md`, not
in the universal standard. The sixteen former Python entrypoints listed below have Lean
replacements; ordinary acceptance, the producer/history/corpus CI campaigns and the
site build do not need a Python interpreter. The four remaining acceptance, snapshot,
documentation-dependency and input-inventory drivers were retired after their native
controls passed; the [earlier receipt](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/ci-environment-census.md) and
[completion receipt](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/ci-role-retention.md) record the control mapping and
runtime results. Historical implementations remain in Git history; use the Lean commands below.
The former prototype's project-owned JavaScript widget was also removed. External Lean, Lake,
Verso, runtime libraries and generated browser assets remain external dependencies, not
claims of a wholly Lean or formally verified toolchain.

## Why retain these controls?

They are integration qualification, not alternative implementations of policy. A theorem
about a pure policy function cannot establish that the CLI called it, that warnings were
promoted, that the compiler supplied the right source range, or that a static renderer
produced a page. Deleting those observations would lose real coverage under standard §8.8.
Conversely, passing these controls never proves arbitrary compiler or OS behavior.

The converse also holds: a property of a pure Lean function the checker executes is
proved over every input, not sampled by mutating one real output. Producer and history
transport admission (`ProducerReport.validate_sound`) and the history oracle
(`History.validate_importedRootExecuted`, `validate_unsupported_unresolved`) replaced
their former mutation campaigns this way; the retained controls above are each kept for
the external process, compiler or filesystem boundary they observe.

| Former entrypoint | Lean replacement | Retained purpose |
| --- | --- | --- |
| `registry_cli_checks.py` | `lake exe qualify registry` | Seven malformed CLI invocations must invalidate seeded stale output. |
| `native_linter_checks.py` | `lake exe qualify native` | 37 real compiler controls: identity, multiplicity, severity, source ranges, documentation, Intent-section and metadata ownership. |
| `producer_checks.py` | `lake exe qualify producers` | Twelve source-owned documentation controls: for incremental and build-lint and each of RG5001/RG5002, one workspace runs Fixed, then Violation over that Fixed build (stale-artifact detection), then Fixed again from a cleared build. Also two standalone-executable controls, each in its own fresh workspace. The fresh-project RG5001/RG5002 observations are the rule-example corpus records, validated there by the same producer oracle. |
| `history_checks.py` | `lake exe qualify history` | Ten project/file invocations, each in its own fresh workspace: private/imported roots, reached-closure/source accounts, unsupported-evaluator refusal and source-snapshot changes. |
| `closure_evidence_checks.py` | `lake exe qualify closure-evidence` | Reflexive candidate versus active cycle, retained recursive IR edges, and range refusals through four invocation paths. |
| `configuration_capture_checks.py` | `lake exe qualify configuration-capture` | Initial configuration IO failure through project/file result protocols. |
| `documentation_source_checks.py` | `lake exe qualify documentation-source` | Frozen dependency/configuration changes through both documentation commands; `--source-read-only` adds file/build read-failure controls. |
| `fence_evidence_checks.py` | `lake exe qualify fence-evidence` | Independent range, admission, policy and compiler failures inside positive fences, plus restoration. |
| `frozen_exit_checks.py` | `lake exe qualify frozen-exits` | Frozen-input rechecks after imports and failed build/compilation operations. |
| `native_launcher_diagnostic.py` | `lake exe qualify native-launcher` | 37 paired baseline/cached-environment controls; exact source, argv, outputs and in-memory environment/executable equality. |
| `rule_example_checks.py` | `lake exe qualify rule-examples --evidence PATH` | Forty-two source-owned phases for twenty-one rules (Fixed and Violation, each in its own fresh workspace), plus authentic wrong-claim/classification refusal controls: 45 productions and 3 individual control admissions, then one corpus admission of every record. What admission concludes from any record is proved (`RuleExampleQualification.qualify_sound`), not sampled by mutation. `--shard K/N` selects every Nth rule by corpus position, keeping RG5001 and RG5002 in one shard. |
| prototype `run.py` | Retired with the one-rule prototype: `./scripts/verify.sh site` ([website guide](website.md)) replaces its Verso integration and page checks; `diagnostics lint-driver` and `qualify native` replace its Lake dispatch and native-message checks. | — |
| `acceptance_checks.py` | `lake exe qualify acceptance GROUP --evidence PATH` | Fence-compilation packet mutations with positive restoration. Group: `fences`. The former `surface`, `evidence`, `sources` and `process` groups mutated the removed surface-worker packet; project and documentation acceptance now run in one process with nothing serialized between them. |
| `acceptance_snapshot_checks.py` | `lake exe qualify acceptance-snapshots dependencies`, `lake exe qualify acceptance-snapshots history` and `lake exe qualify acceptance-snapshots git-status` | Ignored Git/non-Git dependency input coverage and mutation; RG3001 fresh/incremental/build-lint history refusal and restoration; dependency dirty decision against the retired pathspec status across Git collapse, rename, nested-repository, symlinked-root and outside-root cases. `all` runs all three under one deadline. |
| `documentation_dependency_checks.py` | `lake exe qualify documentation-dependencies` | Both documentation commands retain pre-build dependency observations; combined project/documentation positive remains distinct. |
| `input_inventory_checks.py` | `lake exe qualify input-inventory` | Root additions and Markdown edit/removal during prerequisite build; actual new-module build and restored fresh controls. |

The producer command retains `--evidence PATH`. `scripts/verify.sh` runs registry and native
controls; `scripts/verify.sh diagnostics producers`, `scripts/verify.sh diagnostics history`
run as parallel
capability-triggered CI jobs, and the two `scripts/verify.sh diagnostics rule-examples K/2` shards
run in CI on every change, feeding `scripts/verify.sh site`. Each invocation retains its own hard 420-second deadline. Direct `lake exe qualify`
campaigns have a single 420-second process-group deadline. These replace the old per-child timers, which cannot
safely enforce descendant termination while sharing acceptance's outer process group.
Neither the corpus nor the site build substitutes for acceptance. `diagnostics rule-examples` retains the
upstream corpus selection; optional `--rules RULE ...` or `--shard K/N` follows
`--evidence PATH` on the standalone command and never claims full-corpus coverage; the two
CI shards together select every rule once. The corpus runner retains at most five
concurrent producer detector invocations, each in its own fresh workspace. Each invocation
may launch subprocesses. Every launch and the consumption order come from the pure
`RegulaQualification.CorpusWindow` definitions the runner calls: `launched_le` bounds
the launched but unconsumed Tasks by the width, `launch_order` shows that the launches of
a complete run name every job once in index order, `launched_eq_total` shows that every
launched Task has been awaited once every record is taken, and `productions_nodup` gives
every production a distinct `(rule, phase)` workspace given the checked duplicate-free
selection. Task scheduling, `IO.asTask`/`IO.wait` semantics and process reaping remain
trusted runtime mechanisms that these theorems do not describe. The runner prepares one private copy of the root package, shared
by every producer, which must not write it (no permission enforces this; `sharedIdentity`
checks it by content identity); its manifest names the captured original Lake dependency
roots, which are shared too. The runner records a content-level identity of every entry
under every shared root, including the root copy,
(path, `lstat` kind, exact length and a 64-bit native content hash; symlinks recorded by
resolution, never followed) before any producer starts, and requires an equal identity
after all producers have been joined. A difference refuses the run. Equality establishes
only that the recorded content at the end equals the content at the start, not that no
write occurred: a write later restored to the same content, or a rewrite with identical
bytes, is not detected, and nothing prevents a write. The runner never changes shared dependency permissions, so a
deadline SIGKILL cannot leave the dependency trees read-only.

Dependency snapshots are captured once per run. Before any producer starts, the runner
makes one complete `Snapshot.dependenciesCaptures` and exports only its Git facts
(revision and dirty bit), each keyed by the exact capture request: package, canonical root,
and ordered source and configuration paths. The facts file is retained with the attempt's
raw evidence as `injected-git-facts.json`, and every producer registration names that
retained path. Producers run through the internal
`ruleExamples --injected-git-facts FACTS [axiomGate] ARGS` entry. It runs the same
`axiomGate` or `ruleExamples` body, reads every source and configuration byte itself, and
uses an injected pair only for a request that matches exactly. The private
`regula` copy and fixture dependencies are always observed fresh.
`Snapshot.assemble_facts_eq` shows that equal Git facts give an identical capture, and so
(`stateOfCore_congruence`) identical request and report bytes. The no-writer premise is that
the facts stay equal throughout the producer window; the terminal checks establish only
end-state equality with the start. Producers do not recheck an injected dependency at their own end; the campaign
rechecks the shared trees once: at run end, `Snapshot.inputsUnchanged` rechecks the
once-captured value with fresh reads and fresh Git, and the content identity must be equal.
Every producer still rechecks each non-injected dependency and its own inputs. Results
produced with injected facts carry `"gitFacts": "injected"`; admission ignores the field. User-facing `axiomGate` rejects `--injected-git-facts`.
Root processes, other file owners, concurrent external writers, filesystem honesty and
non-cryptographic hash collisions and the absence of shared writes restored before the
terminal check remain trusted assumptions.
The runner consumes records in fixed order and drains launched tasks
before ordinary/exceptional scratch cleanup. Partial exports remain `INCOMPLETE`.
Corpus records use a qualification-only view: top-level `acceptance` and
`documentationAcceptance` payloads become null, while every key, required nested value
and raw-tree shape remains unchanged. Exact detector bytes remain in
`PATH.raw/ATTEMPT/RULE/PHASE/result.json`, with registered command/request/snapshots,
stream files, terminal metadata and the compact original record. During production the
INCOMPLETE receipt points to these sidecars; the full aggregate is written once all
records and controls are ready, and one corpus admission then admits every record. The
runner does not re-read its own just-written sidecars; it requires unchanged terminal
checker sources before the final export. That export records outcome `COMPLETED`, and its
only writer, `saveCompleted`, requires the `Cleaned` witness that `withScratchCleaned`
constructs only after scratch removal returns, so it follows every producer join,
admission, identity check, slot deletion and scratch removal. `COMPLETED` attests what
finished; it is not a run verdict. The run's verdict is its exit status: a deadline kill
before the final save leaves INCOMPLETE and partial files, and a kill after it still fails
the run with the `COMPLETED` file in place. Every write inside the killed process group is
followed by an exit tail, so no file written there can itself be a run verdict.
Stream retention on kill covers completed lines already read; an unterminated line
can remain buffered. Only terminal observations claim complete streams.
The former launcher's separate 180-second diagnostic timer is replaced by the same
single 420-second public qualification boundary; no timing result is a future bound.

## Control inventory

Each control is classified by what it can establish. **Proved** controls sampled a
property of a pure Lean function that the checker executes. They are replaced by a
theorem over that exact definition, which covers every input. **External** controls observe a
boundary no Lean proof covers: a process, the compiler or elaborator, Lake, Git, the
filesystem, serialization bytes or OS signals. The smallest set that exercises each such
boundary is kept. **Counterexample aids** remain only where the universal statement is
not yet proved. Each is labelled that way at its definition and is not correctness
evidence (standard §0 "The Role of Testing").

| Campaign | Control | Property it sampled | Class | Disposition |
| --- | --- | --- | --- | --- |
| producers | 12 documented-source runs, 2 standalone executables | real `axiomGate` incremental/build-lint detection and stale-artifact handling | External | kept |
| producers | 8 transport mutations | `Environment.validate` refusals | Proved | `ProducerReport.validate_sound` |
| history | 10 project/file invocations | real replacement-history, unsupported-evaluator and source-change behaviour | External | kept |
| history | 17 history/closure/source transport mutations | `Environment.validate` refusals | Proved | `ProducerReport.validate_sound` |
| history | 7 oracle mutations | history oracle refuses missing imported ownership / execution evidence | Proved | `History.validate_importedRootExecuted`, `validate_unsupported_unresolved` |
| rule-examples | 42 Fixed/Violation productions | every published example yields exactly its documented diagnostics | External | kept |
| rule-examples | 3 special productions (wrong claim, trusted and negative fences) | producer's own request/classification account | External | kept |
| rule-examples | 7 in-process mutations of each record, 7 derived admission subprocesses | `qualify` refusals | Proved | `RuleExampleQualification.qualify_sound` |
| checkerSelftest fixtures | in-process and CLI fixture verdicts | compiler, elaborator and public CLI over real fixtures | External | kept |
| checkerSelftest fixtures | 11 execution-policy cases | failure kind per boundary/claim | Proved | `boundaryFailures_ids`, `rootFailures_ids`, `executionFailureRecords_empty_iff` |
| checkerSelftest fixtures | 12 scanner cases | `Documentation.scan` marker/fence problems | Counterexample aid | follow-up: step-function scanner with proved problem coverage |
| checkerSelftest fixtures | fence corpus, diagnostic-setup controls | fence compilation through real workers | External | kept |
| checkerSelftest structural | in-process malformed, incomplete, wrong-version, unknown-key, bad-execution and excluded-empty manifest cases | `Manifest.parse` acceptance, field decoding, acceptance of empty exclusions and the diagnostic class of each refusal | Proved | `Manifest.parse_sound`, `parse_input`, `parse_emptyExclusions`, refusal-class theorems |
| checkerSelftest structural | real manifest, missing file; public CLI missing, malformed, incomplete, wrong-version, unknown-key, bad-execution and unknown-library cases | file IO, the `axiomGate` CLI rendering of each refusal class, Lake inventory | External | kept |
| checkerSelftest structural | Lake discovery, unlisted modules, executable classification, fresh-checker coverage | Lake inventory and build behaviour | External | kept |
| checkerSelftest cli, environments, build-policy | CLI sweep, adopters, clean checkout, ordinary build | packaging, Lake and build integration | External | kept |
| ordinary | `qualify registry`, `qualify native` | CLI argv/output invalidation; compiler messages and ranges | External | kept |
| ordinary | `RegistryChecks.lean` codec and source cases | registry, diagnostic and source codecs | Proved in part (roundtrip theorems) | follow-up: state the remaining refusal cases as theorems |
| standalone | `qualify environments` finalize mutations | `finalize` refusals | Proved relation (`finalize_iff`); instance membership sampled | follow-up |
| standalone | `qualify acceptance fences` packet mutations | worker-packet admission through a real proxy | External transport; admission proved by #50 (`checkedIndexedResults`) | kept |
| standalone | snapshots, input inventory, receipts, frozen exits, documentation source, closure/configuration/fence evidence, timeout | Git, Lake, filesystem, elaboration-time IO, signals | External | kept |

**Structural partition status.** Each structural copy's manifests derive from the actual
repository manifest. `Manifest.structuralManifest` builds the base manifest in memory, and
`structural_libraries` and `structural_executables` prove that this base manifest classifies
exactly the actual library and executable names. `structural_roundtrip` covers what the gate
reads at the `Json` value boundary. Take any manifest `actual` that the executed `parse`
accepted, and any claim set that selects at least one actual surface. Then `parseValue`, the
stage of `parse` after the text parser, returns exactly `structuralManifest actual claimed`
from `Manifest.toJson` of it: the same surfaces, excluded libraries and excluded executables,
in order, with their rationales. `structuralBase` checks the claim hypothesis at run time; no
theorem links that check to the hypothesis. The theorem does not cover the text boundary.
`Json.compress` renders the value and `PolicyCodec.parse` reads it back; the first is `partial`
and the second runs core `partial` parsers, so no Lean theorem can describe them. They stay
trusted to return a value that `Encodes` the manifest; `parse_of_encodes` then gives exactly that
manifest from `parse`. No theorem covers the lib-only, claimed-exe and app-omitted-exe
variants that rewrite the `AuditApp` surface after derivation. Those variants exclude every
actual `AuditApp` executable they stop claiming, except app-omitted-exe, which leaves them
unclassified on purpose. Before this, every copy failed early because the libraries
`RegulaPolicy`, `RegulaVerification`, `RegulaQualification` and `RegulaCore` and the executables
`qualify`, `ruleExamples` and `ruleExampleQualification` were unclassified, which masked a
checker defect.
`checkCorrespondenceProof` gave the kernel 200000 raw heartbeats, 1/1000 of Lean's default,
so every definitionally equal `implemented_by` replacement timed out and was reported as
trusted. Its heartbeat budget is now Lean's per-declaration default
(`Core.getMaxHeartbeats` of the default options), so a checker-added correspondence
obligation costs no more than a declaration the adopter could write. Heartbeats count small
allocations, not live memory, so the check also runs under Lean's runtime memory limit (the
limit `lean -M` sets). The kernel compares it with the process's resident memory and raises
`excessiveMemory`. The limit is fixed once per process, at its first correspondence check, to
the process's peak resident size then plus a 1 GiB allowance. It is set only while a check
runs, never exceeds a `max_memory` the shell set, and that limit is restored afterward.
Guarantee: while any correspondence check runs, the kernel stops it once the process's
resident memory exceeds its first-check peak by 1 GiB, however many checks the process runs
and whether or not earlier ones exhausted. Derivation, argued from the Lean runtime source
rather than observed on Linux: the kernel throws only when current resident memory reaches
the limit, and the first-check peak is at least the resident memory then, so the first check
never fires on memory the process already held (a file-mode audit that imports `Lean`
already peaks above 4 GiB, which an absolute limit would hit). The limit does not re-read the
peak, so a check that exhausts cannot raise the next check's limit; a limit based on the
rising lifetime peak would let each exhausted check add another 1 GiB. The remaining
limitation: the 1 GiB of headroom above the first-check peak is shared by every later check
in the worker and by any other resident growth there (pages that successful or exhausted
checks leave resident, since Lean's allocator may keep them, execution-walk caches, later
environment loads). Once one check exhausts memory, or other growth consumes the headroom,
later checks in the same worker may exhaust immediately. These fail closed: such a check is
never reported checked, and its correspondence is reported unresolved. At most
three report workers run at once, each running its checks sequentially, so while checks run
they add at most 3 × 1 = 3 GiB of resident memory above those workers' first-check peaks.
That is an increment, not a total: it does not by itself show the audit fits in 16 GiB,
because each worker's first-check peak is set by what it already holds (a worker that
imports `Lean` already peaks around 4.2 GiB on Linux), and memory used outside the checks
is not bounded by this limit. To keep a kernel-exhausting unfolding from consuming the
headroom a supplied proof needs, supplied and then discovered theorem candidates are tried
before the kernel-defeq check, so a replacement with both reports `proved:` evidence. Kernel
resource exhaustion is not conflated with rejection. As
[§8.6](../standard/8-tooling-and-machine-audit.md#86-classify-lean-computation-mechanisms-exactly)
requires, a definitional comparison that could not complete is unresolved, with the reason
that the kernel ran out of resources before deciding definitional correspondence, and only a
completed negative comparison leaves the replacement trusted. `DefeqComparison.classify` is
that classification, total over the comparison outcome, and `replacementCorrespondence`
returns its result (see the proved boundary below). A theorem candidate whose admission
exhausts the kernel supplies no evidence, like any other candidate the deliberately
incomplete search cannot use. With the manifest and heartbeat fixes, and before this
classification change,
`diagnostics structural` passed locally in 806 s, down from 1015 s (observed before the
memory bound was added). That is still over the
420-second budget, which remains follow-up work. `RegulaPolicy` stays claimed in each
copy because the checker probe's own imports resolve to it in a self-hosted copy; this
partition is not a CI job.

## Dogfooding Regula on itself

Acceptance audits the six claimed libraries freshly. Three diagnostics apply Regula to the rest
of its own code base. The [dogfood workflow](../../.github/workflows/dogfood.yml) runs them
when Lean sources, Lake configuration, manifests or the screen configuration change, on every
push to `main`, and nightly. None is part of acceptance.

- `./scripts/verify.sh diagnostics self-lint` runs `lake lint` in this repository. The root
  package sets `lintDriver := "regula/lint"`, so this is the adopter command, run through the
  `regula/lint` driver over `foundation_manifest.json` in incremental mode. It checks the same
  claimed surfaces as acceptance, through the driver's dispatch and exit classes.
- `./scripts/verify.sh diagnostics self-audit` checks the operational `Regula` library, which
  `foundation_manifest.json` excludes because it is not a conforming proof surface. The step
  `lake build Regula` builds every module warning-free (RG2003, because the package sets
  `warningAsError`). Then `qualify self-audit` inspects each module of the library as Lake
  discovers it, each in its own worker process. Several executable roots of the library define
  `main`, so its modules cannot share one environment. For every module the audit:
  - kernel-replays each owned declaration that is not `unsafe` or `partial` (RG2005,
    `Admission.validate`);
  - builds its declaration records with the live linter's shared collector
    (`Regula.Collect.declaration`) and decides each record with the proved
    `RegulaPolicy.checkedOperationalFailure` (RG1001–RG1005, RG1007);
  - checks module docs and material-claim docs with the live linter's predicates
    (`Regula.Linter.Documentation`, RG5001–RG5003).

  Operational code is held to Standard-Logical with two facts reported, not failed:
  authored `unsafe`/`partial` declarations (RG1006), and, in a definition whose type is not a
  proposition, the pinned toolchain's Lake type-family axioms (for example
  `Lake.DataType.bool`), which the in-process Lake API reaches. An axiom counts as a toolchain
  Lake axiom only when a `Lake` module resolving from the toolchain's own library directory
  declares it. `operationalFailure_none_iff` states the exact success relation.
  `operationalFailure_ne_escapeHatch` shows an escape hatch never fails a declaration.
  `operationalFailure_prop` shows a proof gets exactly the conforming decision.
  `operationalFailure_eq_conforming` shows the decision equals the conforming Standard-Logical
  decision on every declaration without a reported fact. The run prints both reported lists.

  The self-audit does not claim the library is a proof surface. It makes no execution claim for
  the library's executables. It does not attach the live linter's editor hooks to Regula's own
  modules: the modules below `Regula.Linter` cannot import it, and the editor request has no
  operational form. The audit applies the same collector and decisions to completed modules
  instead. Trusted, not verified: Lean's import and kernel replay, the collector's
  observations, the toolchain artifact paths, the worker processes and their JSON transport.
- The dogfood workflow's intent-screen job runs the opt-in
  [Jev intent screen](intent-screening.md#dogfood-screen) over every public `@[regula_material]`
  declaration in the claimed libraries. It is the only CI job that receives
  `TYPESAFE_API_KEY`.

## Organization

- `lean/RegulaQualification/`: a separate **positive Lake library**, discovered through
  its all-submodules glob. It contains pure observation requirements and checked contracts,
  not process launchers. Testing requirements are not production policy, so this library
  does not belong in `RegulaPolicy`, nor in the mathematical `Audit` examples.
- `lean/Regula/Qualification/`: operational drivers, the single `qualify` Lake executable,
  and shared process/scratch/adopter support. These remain in the existing operational
  `Regula` library, explicitly excluded from the positive proof surface. Calling a
  proved oracle does not prove the entire driver or its IO effects.
- `lean/RegulaVerification.lean`: a separately claimed cold-start runner importing only
  the pinned toolchain. It owns argument selection, command recipes, sequential execution
  and success reporting. `scripts/verify.sh` only selects the root/GNU timeout and starts
  this runner under the external deadline, including all root-package builds.
- `lean/Regula/Site/`: the rule-reference site builder (`lake exe site`) and the
  toolchain-only deployment check. Their pure decisions are proved in the claimed
  `RegulaCore.Site*` modules; see the [website guide](website.md).

This uses normal Lean module factoring and Lake targets. It does not impose a universal
`tests/` directory convention or rename scripts while hiding another interpreter inside Lean.
The helpers invoke external programs with argv arrays, never generated shell programs.

## Exact proved boundary

All quantifiers below range over supplied Lean values, not external executions.
The IO drivers call the relevant `ExecutableContract.run`, so the evidence is required
by their source-level linkage. The proof is erased at execution.

- `Checks.evaluate_success`: evaluation returns success **iff** every supplied assertion
  is true. `evaluate_error` identifies a satisfied prefix and its first false assertion;
  `evaluate_append` specifies success/error composition. `checkedEvaluation` requires all
  three properties. Empty conjunction is permitted; each protocol supplies its own
  nonempty, explicit requirements.
- `Registry.validate_exact`: for every exit code and JSON tree, success **iff** the exit
  is nonzero, the root is an object, status is explicitly `incomplete`, and the seeded
  `old` key is absent (present-null is not absent).
- `Native.validate_exact`: for every expected result and decoded message list, success
  **iff** compiler messages match in order and length, native identities match with
  multiplicity, exit outcome and stderr agree, native file/severity/help fields agree,
  and any requested detail is present. `nativeMatches_exact` and
  `compilerMatches_exact` establish the field and ordered-list relations separately.
- `Json.validateDecoded_exact`: a decoding error always refuses; success **iff** decoding
  yields an assertion list whose every assertion holds. `History.requirements` and
  `Producer.requirements` spell out mandatory fields and their exact comparisons.
  Their registered contracts apply this equivalence to the actual decoders; they do
  **not** prove that the observations were extracted truthfully or that Lean's JSON
  parser implements a separately formalized JSON specification.
- `Checker.ProducerReport.validate_sound`: every producer report that
  `Environment.validate` admits satisfies `Environment.Admissible`, which restates every
  executed guard: a nonempty, unique, loaded module census; a declaration census equal
  to the reported keys in order and duplicate-free; execution results exactly for the
  requested roots; `ExecutionValid` closures; unique located source bindings covering
  every claimed module and range; a replay receipt admitting exactly its unique
  requirements and requiring every safe, total declaration; documentation observations
  for exactly the claimed modules and unique material selection; unique history
  requests with exactly one history per requested module; completed histories that are
  located, source-stable, bound to the owned snapshot when the module has one and
  free of anonymous edge endpoints; unavailable histories that leave every requested root unresolved;
  requested runtime replacements whose resolved edges appear in completed histories;
  root/boundary module attribution with exact replacement-edge channels; and, for every
  current replacement reference, a reached, attributed, requested and recorded module
  history, with the root's historical edges the canonical form of exactly those
  completed-history edges. `validate_eq_ok` decomposes the executed guard sequence
  exactly, `validate_nonvacuous` exhibits an admitted report by kernel reduction, and
  `fromJson_admissible` extends soundness to the transport decoder. Producers,
  documentation groups and acceptance call `checkedValidate.run`, so each call site
  requires this `ExecutableContract`. The project report worker skips its own call: the
  coordinator's decoder runs the same check once and keeps its success as a
  `ProducerReport.Admitted` proof (`fromJson_admitted` shows it accepts and refuses exactly as
  the plain decoder). `Acceptance.freezeEnvironment` requires that proof instead of
  re-running the check, and takes the execution inventory from it
  (`Admitted.admitExecution_eq`). These replace the
  former 8 producer and 17 history/closure/source transport mutations. They do not
  authenticate the observations.
  They live in the excluded operational `Regula` library, so acceptance's
  claimed-surface audit neither re-elaborates nor reports them: the `lake build` kernel-checks
  them under `warningAsError` (which also rejects `sorry`), and the module's `run_cmd`
  `collectAxioms` ceiling bounds their transitive axioms to Standard-Logical.
- `History.validate_importedRootExecuted` and `validate_unsupported_unresolved`: every
  report the history oracle admits executes the imported registered root with a foreign
  module, and, for an unsupported evaluator, leaves every root requested from the
  audited module with nonempty unresolved evidence. These replace the former 7 oracle
  mutations.
- `Checker.Manifest.parse_sound` and `parse_input`: every manifest the executed `parse`
  accepts has nonempty surfaces, duplicate-free library and executable names across
  surfaces and exclusions, well-formed target names, no compiler-trusting claim and a
  nonempty rationale for every entry (`Manifest.Valid`). It comes from JSON whose top-level
  and per-entry keys are all allowed and whose schema version is 2. Each of its three arrays
  is, element by element in order, the decoding of the matching JSON array
  (`SurfaceDecodes`, `ExcludedLibraryDecodes`, `ExcludedExecutableDecodes`): every
  name and rationale is the JSON string, the claim is `Profile.parse?` of the JSON string, an
  absent `executables` is empty and a present one is exactly its string array, and an absent
  `execution` is `report` while a present one is `ExecutionClaim.parse?` of the JSON string.
  `load` adds only the missing-file check and the read. With the refusal-class theorems
  below, these replace the in-process malformed, incomplete, wrong-version, unknown-key and
  bad-execution manifest cases.
- Manifest refusal classes: each isolated defect yields exactly its documented message from
  the executed `parse`. `parse_malformed`: unparseable JSON gives `manifest-malformed`.
  `objectWithKeys_unknown` gives `manifest-schema: LOCATION has unknown key(s): KEYS` for
  any object with a key outside the allowed set. With well-formed JSON
  (`parse_topLevel_refuses`), `topLevel_unknownKey` passes that message through for the top
  level, `topLevel_schemaVersion` gives `manifest-schema: schema-version must be exactly 2`
  when the keys are allowed, and `topLevel_emptySurfaces` gives `manifest-incomplete:
  surfaces must be a nonempty array` when the rest of the top level is accepted. After
  accepted earlier surfaces (`parse_surface_refuses`), `parseSurface_unknownKey` passes the
  unknown-key message through for that surface. When every check before `execution` accepts
  it (`SurfacePrefixOK`, `parseSurface_execution_refuses`), an unrecognized execution string
  (`surfaceExecution_unknown`) or a non-string value (`surfaceExecution_nonString`) gives the
  `manifest-schema` execution message. Other refusals, including a missing required field
  and an unknown key in an exclusion entry, are not classified by a theorem. The public
  `axiomGate` CLI controls for the malformed, incomplete, wrong-version, unknown-key and
  bad-execution cases stay as external controls of how the CLI renders these classes.
- `Checker.Manifest.parse_emptyExclusions`: JSON meeting the top-level conditions above
  with empty exclusion arrays is accepted whenever its surfaces array parses
  (`parseAll parseSurface` succeeds), with exactly those surfaces. This completeness
  statement replaces the in-process excluded-empty case; it does not prove that any
  particular surface is accepted. Axioms of these theorems are bounded by the module's
  `collectAxioms` command; the module is in the excluded `Regula` library.
- Manifest completeness and round trip. `parse_ok`: `parse` accepts `m` exactly when
  `PolicyCodec.parse` returns a value that `parseValue` accepts with `m`. `parseValue_ok`:
  `parseValue` accepts a value with `m` exactly when `m` satisfies `Manifest.Valid` and the value
  `Encodes` `m`, which is the conclusion of `parse_input`. So `Manifest.Valid` is exactly what
  the parser admits, and no stronger condition is needed. `toJson_encodes`: `Manifest.toJson m`
  encodes every `m`. Together they give `parseValue_toJson`:
  `parseValue (toJson m) = .ok m ↔ m.Valid`, an exact round trip at the `Json` value boundary.
  `structuralManifest_valid` shows that the structural copy of a valid manifest is valid whenever
  it claims an actual surface, and `structural_roundtrip` combines the two for the manifest the
  structural gate reads. The text boundary is trusted: `Json.compress` is `partial`
  and `PolicyCodec.parse` runs core `partial` parsers. `parse_of_encodes` names what they must
  deliver, a value that `Encodes` the manifest. The schema-version check compares `JsonNumber`
  fields with derived equality (`schemaVersion2`) rather than `Json`'s `partial` `BEq`, which
  no theorem can evaluate. The check has the same runtime meaning, and the proofs now state the
  version as `getObjVal? "schema-version" = .ok (Json.num 2)`. Axioms are Standard-Logical
  (`propext`, `Classical.choice`, `Quot.sound`) under the same `collectAxioms` ceiling.
- `RegulaPolicy.boundaryFailures_ids` and `rootFailures_ids`: the failure kind of
  every boundary and unresolved path for every claim. With
  `executionFailureRecords_empty_iff` they replace the 11 in-memory execution-policy
  cases. They are on the claimed `RegulaPolicy` surface.
- `RegulaPolicy.DefeqComparison.classify_trusted_iff`, `classify_checked_iff` and
  `classify_unresolved_iff`: the correspondence of the kernel-definitional comparison is
  checked exactly for a completed comparison with admitted evidence, trusted exactly for a
  completed comparison without it, and unresolved exactly for a comparison that did not
  complete, so no incomplete comparison is trusted (standard §8.6). They are on the claimed
  `RegulaPolicy` surface, and `Probe.replacementCorrespondence` returns `classify` of the
  outcome it observed. Mapping the kernel result to that outcome (`kernelExhausted` for an
  incomplete comparison, a rejection or a proof beyond Standard-Logical for a completed
  negative one) is checked by inspection, not by theorem, and the kernel decision itself is
  trusted.
- `Checker.RuleExampleQualification.qualify_sound`: every rule-example record that
  `qualify` admits satisfies `RecordAdmissible`: its result carries the exact current
  producer identity fields; the result mode is the record's parsed evidence mode; the
  record's `before` and `after` source/configuration snapshots are equal; the result's
  observed request decodes to exactly the frozen request the record binds; the exit code
  is at most 1; every source in the result's own source account (`observedSources`) is
  in the bound snapshot and one has the displayed text, and for a file or diagnostic-only
  request one such source is the requested subject with the displayed text; a result
  source account is present unless the request is diagnostic-only or documentation; the
  findings are exactly the result's parsed `diagnostics`; the kind is one of positive,
  policy rejection or diagnostic demonstration; and a demonstration satisfies
  `DemonstrationOK` for the record's parsed `rule` and those findings. The terminal corpus admission and every individual
  admission run this `qualify`. It replaces the former 7 in-process mutations of each
  record and the 7 derived admission subprocesses. Its axiom ceiling is checked by the
  module's `collectAxioms` command; the module is in the excluded `Regula` library,
  so acceptance's claimed-surface audit does not re-report it. It proves nothing about
  the producer that wrote the record.
- `Evidence.checkedValidation` and `checkedDocumentation`: exact conjunctions of decoded
  status/diagnostic/exit and transcript requirements, including distinct fence/project
  admission messages and the underlying IO reason. IO-only controls also consume the
  shared assertion contract for their observed source, closure and configuration fields.
- `Launcher.admit` returns a proof-bearing mapping with nonempty unique names and both
  required search paths; its completeness theorem admits every valid decoded mapping.
  `checkedEquivalence` requires exactly 37 observations and full ordered equality,
  including source, arguments, stdout/stderr, exit, environment and resolved executable.
  Lake's actual environment is cached only within one fixed parent/workspace invocation,
  separately for the imported-control search-path override. Neither observations nor
  compiled artifacts are reused. Environment values are not exported. Durations are
  observations, not a speed guarantee or compiler-equivalence theorem.
- `Template.instantiate` returns a required `Maps` proof for the actual recursive JSON
  transformation: ordered array entries, object keys and scalar kinds are preserved;
  only entire matching string values change. Unmatched strings stay unchanged. Depth
  exhaustion explicitly refuses; the corpus uses a 64-level budget. Semantic module
  discovery for checker snapshots uses Lake's elaborated inventory, not a source glob.
- `Checker.RuleExampleProjection.qualify_record` and its checker-source
  variant prove exact `Except String Unit` equality for arbitrary producer JSON at
  the adapter's canonical record constructor. `qualifyCorpus_records` extends this
  to the unchanged full corpus qualifier, including ordered scans, completeness and
  first refusals. Structural raw-tree laws avoid assuming parser well-formedness. These
  separately checked operational-module proofs do not authenticate parsing,
  duplicate-key handling, serialization, hashes, filesystem custody or subprocesses.
- The former prototype's `RegulaQualification.Website` page and artifact contracts were
  retired with it. The production site's page, escaping, filter, diff and link-check
  guarantees are in `RegulaCore.Site*` ([website guide](website.md)). They do not establish
  Verso or browser correctness.
- `RegulaVerification.parseMode_sound`, `parseMode_roundtrip`, and `select_exact`
  prove exact argument binding and acceptance of every documented invocation. The caller
  consumes the proof-bearing selection; recipes name the intended commands explicitly.
  `commands_nonempty` rules out a selected empty campaign. Process execution remains IO.

The positive library is audited as `standard-logical`, `execution: report`. The gate
reports each declaration's exact axiom set and each reached execution boundary;
that surface profile is an upper bound, not a claim that every proof uses choice.
No `sorry`, project axiom, native proof, authored partial or unsafe definition is permitted
on that surface. The supplied-observation contracts do not certify the entire operational
checker or all project-owned Lean code as formally verified.

## Operational assumptions and approved bootstrap

The supported compiler, filesystem, process runtime and GNU timeout are trusted mechanisms.
Unique scratch directories are removed on normal or exceptional return; a killed process
cannot promise to run its cleanup handler. Each supported public invocation has one
non-foreground GNU timeout owning the whole process group, including descendants with
inherited output handles. Acceptance passes an internal `--under-deadline` protocol flag
to `qualify` so it does not detach a nested timer/group. That private flag is not a bounded
standalone invocation or an alternative acceptance command. `TimeoutControl.lean` separately
exercises positive, descendant timeout, terminated-descendant and restored controls.
These observations are not an OS scheduling theorem.

`lake exe qualify receipt-boundaries` seeds completed evidence and exercises
actual missing/unusable timeout selection and selected-timer spawn failures for
both `acceptance` and `environments`. Each public invocation replaces the old
receipt with a fresh incomplete attempt before those fallible operations. The
timed child carries the same attempt, and adds no new deadline. Acceptance keeps
existing raw result/trace sidecars before parsing and records partial file
locations on the active case; completed command records contain executable plus
argv. These are diagnostic receipt guarantees under trusted filesystem/process IO.

The operator approved a narrow exception for the existing CI bootstrap to install pinned
Elan/Lean and required system tools before Lean is available, expose their paths, and
check availability/versions. `AGENTS.md` records its exact scope: no policy decisions,
validation logic, or test orchestration in that shell step; expansion requires explicit
approval. Installation and runtime mechanisms remain trusted, not proved by Lean.
The nonessential shell resource-reporting block has been removed. Direct commands
in CI and developer setup examples are invocation recipes, not a second implementation
language for qualification logic.

No CI, publication, merge, actual VS Code interaction, or full repository semantic
conformance is implied by local acceptance or these scoped integration results.
