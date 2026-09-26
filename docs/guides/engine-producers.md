# Project producer evidence

The completed ENGINE-01 producer delivery supplies independent extraction keys, replay
receipts, completed documentation observations, closure witnesses and source bindings.
These operational observations are inputs to POLICY-04's separate global acceptance
boundary; producer correctness is not inferred from a pure data-level proof. The [coverage map](rule-coverage.md) and
[policy acceptance contract](policy-acceptance.md) retain the remaining obligations.

## Implemented paths

`Probe.environmentReport` freezes `(owning module, declaration name)` keys from
`Probe.ownedConstants` before constructing declaration observations. It freezes ordinary
and valid registered executable roots before executing their walks. Registered roots may
be private or imported. All registrations remain in the declaration observations even
when several registrations share one root. No policy-success filter defines either census.
Execution omitted for logical-only fence inspection is `none`; an inspected empty root
set is `some #[]`.

`Admission.validate` returns `IO (Except ProducerReport.AdmissionFailure ProducerReport.AdmissionReceipt)`.
A successful receipt's required keys come from
safe, nonpartial original kernel entries in the replay scope. It calls the same pinned
`Environment.replay`, checks that every required entry is present in the resulting kernel,
and records the admitted keys. Replay scope includes owned dependencies and the existing
reporter closure where required; it may exceed the reported surface. Imported unowned
modules remain trusted. The receipt records this completed operation; serialization does
not authenticate replay and carries no proof of the Lean implementation.

`Environment.loadReportCoreAtSearchPath` loads imported server/private extension data,
freezes the public `@[regula_material]` selector from the completed owned environment,
and calls the existing `Linter.Documentation` observer and `Lean.findDocString?`.
Module observations include declaration-free modules. Markdown and Verso module metadata,
Verso declaration docs and inherited docs follow the same Lean lookup semantics as native
feedback. Private declarations and unregistered public declarations do not acquire RG5002
or RG5003 obligations. Registration completeness and text fidelity remain **R-DOC** review.

The project gate now emits RG5001 for a missing claimed module doc, RG5002 for a missing
docstring on a selected declaration, and RG5003 for a selected declaration's docstring
without a nonempty `# Intent` section, in both fresh and incremental project modes. The
recorded docstring is classified by the proved `RegulaPolicy.materialDocumentationFailure`. It does
not depend on whether native feedback was imported or enabled. RG5001 uses module attribution;
RG5002 and RG5003 use authenticated declaration ranges when available, otherwise module
attribution. Only RG5003 requires a heading, the labelled Intent section; no detector imposes
lengths or a universal all-public-declarations rule.
File/fence results retain their scoped enforcement; the [acceptance guide](policy-acceptance.md)
owns global mode/job composition.

## Transport and consumer boundary

`Report.Collected` adds extraction keys to the pure policy report.
`Checker.ProducerReport.Environment` adds the operational receipts and owns their JSON decoder:

- `census`: requested modules, declaration keys, optional execution root keys and root/module history requests;
- `admission`: replay modules, required keys and observed admitted keys;
- `documentation`: every module's presence, frozen material keys and exact optional docstrings;
- `histories`: one completed source receipt or explicit unavailable outcome for every requested module;
- `sourceBindings`: exact loaded-owned module/path/text snapshots;
- each execution root now retains its `closure` account described below.

Keeping transport validation in the checker layer avoids replaying its implementation from
the force-loaded reporter in every inspection. The trusted loader validates these fields before returning. The operational JSON decoder
validates them again: no duplicate/missing keys, output-derived narrowing, unmatched selector
results, omitted replay receipt, or unmatched required/admitted entries. Project and grouped
fence consumers also compare the census's module array and execution availability with their
original request. A direct interactive `audit_dump_json` has no trusted loader receipt and
cannot pass this decoder. Unknown fields and missing fields are refused. These additional
unreleased report fields live inside the existing registry/result envelope; worker binding
and its version remain separate. `--legacy-json-out` omits the new fields and retains its
prior record shape. Use canonical `--json-out` to consume producer evidence.

`AxiomGate` also retains captured source bytes in the terminal `sourceAccount`, including
partial captures on typed failures and IO exceptions. Capture callbacks retain the growing
account in memory; serialization occurs at terminal success/error boundaries, rather than
rewriting every captured prefix. When an outer handler has no captured sources, it preserves
any account already serialized by the worker. An absent or partial account does not establish
complete source coverage; [example admission](rule-examples.md) checks its required source
against this producer evidence before constructing an observation.

These guards reconcile supplied data. They do not prove truthful external extraction, source
identity, a complete execution-edge/history census, or complete claim-indexed jobs. The
[acceptance guide](policy-acceptance.md) owns the implemented claim/snapshot binding and
success boundary; no serialized flag substitutes for that work. The
[source-owned corpus](rule-examples.md) owns example integration. An empty diagnostic
list is not `Accepted` or full semantic conformance.

## Source-bound replacement histories

The execution walk registers each `(root, module)` history request before consulting the
loader. Repeated lookups share one module receipt within that report. The loader retains the
Lean-resolved path, exact bytes before and after the isolated worker, and the returned ordered
replacement edges. Its existing worker packet binds the stage, module, path, bytes, producer
and toolchain; changed source or unsupported evaluator paths yield `unavailable`, never a
completed receipt. This also preserves earlier choices overwritten by later attributes.

Producer/decoder admission requires unique requests, exact module receipt coverage in canonical
name order, known roots/modules, nonempty source paths and byte equality. A runtime-replacement
boundary must have a registered request. Completed execution requires its replacement edge in
a completed history; unavailable history requires unresolved execution for every requesting
root. Logical-only inspection has no execution roots, requests or history receipts. Legacy
JSON omits the added history account.

These are linked operational observations under the existing Lean/process/imported-library
trust boundary. They do not authenticate arbitrary serialized source claims or establish the
complete extraction of reached nodes/edges, source authenticity, or global `Accepted`.
The closure/source account below extends the supplied observations and their binding. A
temporarily changed source restored between observations remains outside what before/after
byte equality establishes. Global claim/job composition is described in the
[acceptance guide](policy-acceptance.md).

The separate `history` diagnostic runs `Regula.Qualification.History`: real fresh/incremental
project and file invocations check overwritten history, an unsupported source evaluator, and
fresh restoration. Refusal of missing requests/receipts/edges, changed bytes, missing paths
and concealed unavailability is proved for every report by `ProducerReport.validate_sound`
([Lean qualification](lean-qualification.md#exact-proved-boundary)), not sampled by mutation.
See the [contributor guide](contributing.md#develop-and-verify) for diagnostic commands,
required CI ordering and budgets.
The existing structural campaign remains separately scoped; this does not report it PASS.

## Source-owned examples and qualification

The module/documentation source pairs are [RG5001](../../examples/rules/RG5001/),
[RG5002](../../examples/rules/RG5002/) and [RG5003](../../examples/rules/RG5003/). Each correction preserves exactly
`∀ n : Nat, n = n`, with the same proof and no new assumptions. Only documentation is added.
They are isolated from positive libraries and copied byte-for-byte into a disposable
Core-only adopter as `Example.lean`. The complete twenty-one-rule corpus and its separate
unavailable-analysis demonstrations are described in [rule examples](rule-examples.md).

Run `./scripts/verify.sh diagnostics producers` for the bounded operational campaign.
It runs twelve source-owned controls: for the incremental and build-lint entrypoints and each
of RG5001/RG5002, one workspace runs Fixed, then Violation over that Fixed build (so a stale
build must not hide the violation), then Fixed again from a cleared build. RG5003 is not in
this campaign: it shares the same gate documentation loop, whose evidence mode is a parameter,
but its observed evidence is the fresh-project [RG5003](../../examples/rules/RG5003/) corpus
pair and the native `MissingIntent` control. No incremental or build-lint RG5003 run is
claimed. Each invocation
checks exact stable ID, detail, primary location, related locations and result status,
and requires unique output and exact embedded source/selector/type/axiom evidence.
Transport admission of every report is proved rather than sampled by mutation; see
`ProducerReport.validate_sound` in [Lean qualification](lean-qualification.md#exact-proved-boundary).
A standalone executable additionally has
positive/owned-axiom controls, each in its own fresh workspace; each carries module
documentation so the intended axiom violation is isolated. The fresh-project RG5001/RG5002
observations are the [rule-example](rule-examples.md) corpus records, validated there by the
same producer oracle. Optional raw export:

```sh
lake exe qualify producers --evidence tmp/producer-examples.json
```

The export embeds exact source bytes and canonical diagnostic/result data, including the
checker build identity. Its temporary observation URIs identify the actual checked source;
consumers render the embedded source and its repository path, not a now-removed scratch file.
This supplies scoped source/evidence inputs, not the site's complete typed expectation
validator ([website guide](website.md)). CI runs this named campaign separately from the unchanged unpartitioned ordinary
420-second acceptance. No unrun broader campaign is claimed PASS. Older structural-campaign
manifests still need reconciliation with the `RegulaPolicy` root before that campaign
can establish its broader claims; the small adopter qualifies the changed standalone path.

The collectors and documentation lookups reuse Lean 4.34.0 APIs. No con-leche code is imported;
the existing complete-census design credit remains in [design influences](design-influences.md).

## Reached closure and source snapshot account

The closure increment records `ExecutionRoot.closure` from the **actual**
`Probe.executionWalk`. Each first visit retains its structural name, available owning
module and the index of the earlier visit that queued it. The initial visit is the
root. The sorted `nodes` census is exactly the set of these visits, with no duplicate
visits. The producer retains every ordinary eligible root (including unused roots), plus
explicitly registered private/imported roots. Unregistered internal/private declarations
remain in the logical declaration census; they do not become ordinary execution roots.

The following channels remain separate; their union is a conservative traversal relation,
not a selected or minimal runtime call graph. `compilerEdges` belongs to `ExecutionRoot`;
the remaining fields belong to its `closure` account:

| Field | Observation and use |
| --- | --- |
| `compilerEdges` | Retained IR calls, closures and initialization dependencies. |
| `logicalEdges` | Constants used by the logical bodies the existing walk follows. |
| `candidateEdges` | All inspected constant-equality simplification candidates, including inactive candidates. |
| `historyEdges` | Replacement choices from completed, source-bound module histories. |
| `currentReplacementEdges` | Current `implemented_by` choices, retained even when history is unavailable. |
| `activeSimplificationEdges` | Active simplifications used by the replacement-only cycle check; each is also a candidate. |
| `helperEdges` | Explicit opaque-to-partial-helper traversal. |
| `requiredCode` / `unavailableCode` | Exact retained-code obligations and the unavailable subset; a nonempty unavailable subset requires unresolved execution. |

Every enqueue site records its edge and a parent visit together. Visited-name suppression
terminates ordinary recursion without deleting self edges. Retained IR dependencies now use
the declaration step of Lean's pinned
[`IR.CollectUsedDecls.collectDecl`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Compiler/IR/EmitUtil.lean):
`collectUsedDecls` also inserts the declaration itself synthetically, so filtering its
result by inequality incorrectly discarded genuine recursive calls. This is a specialized
pinned compiler API, not a promised stable extension interface; upgrades must requalify
its semantics. No upstream code is copied. Existing source/boundary/IR obligations and
replacement-cycle refusal remain in force.

`RegulaPolicy.ExecutionClosure.Valid` checks the supplied census, discovery witnesses,
canonical edge channels, endpoints, code obligations and unresolved requirement.
`ExecutionRoot.Valid` additionally reconciles boundary names, replacement targets and
compiler callers. `ProducerReport.Environment.validate` calls `admitExecution` at producer
and decoder boundaries, reconciles visits with available module attribution, requires exact
candidate/replacement boundary coverage and binds each historical edge set to its actual
module receipt. Missing or inconsistent observations refuse inspection; no omitted record
becomes a clean result.

### Exact proof scope

All three theorems below compile over the executed admission definitions in
`RegulaPolicy/Admission.lean`. They quantify over arbitrary supplied records, not a
separate graph model:

- `ExecutionClosure.discovery_induction`: if every visit has the checked root/earlier-parent
  witness, any predicate true of the root and preserved by each recorded edge holds at
  every visit. Its transitive axioms are exactly `propext`, `Quot.sound`.
- `ExecutionClosure.nodes_induction`: with `Valid`, the same predicate holds for every
  name in `nodes`. Its transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
- `admitExecution_preserves`: a successful `admitExecution roots = .ok inventory` retains
  exactly `roots` and proves `ExecutionValid roots`. Its transitive axioms are exactly
  `propext`, `Classical.choice`, `Quot.sound`.

The induction uses the strictly earlier parent index, not another graph search. These
results establish connectedness and structural admission of supplied observations. They
**do not prove completeness or authenticity of Lean environment/IR extraction**, that a
candidate edge executes, machine-code correspondence, or intended-specification adequacy.
Reflexive constant equalities remain in the candidate set. An active `csimp` self-edge
therefore satisfies the active-edge subset invariant while its replacement-only cycle
remains unresolved (RG3001); an inactive reflexive candidate does not create an active
cycle. Ordinary recursive IR self-edges remain a separate channel.

The existing pure execution/Plan/Observation interfaces consume this strengthened admitted
inventory; the [acceptance adapter](policy-acceptance.md) freezes global required jobs
and constructs `AcceptedRun` from these observations.

### Source and configuration binding

`ProducerReport.SourceBinding` retains module, actual path and exact source text. Project
checking captures Lake's root-package source map and manifest/Lake/toolchain/dependency-lock
configuration before building. Requests carry the frozen sources; producer and parent
compare the report's loaded-owned subset with that request. The loader captures source
before importing the environment and checks it after inspection. Completed owned histories
must use the same path and text. Frontend transcripts must match that snapshot. All supplied
declaration ranges are checked against it, including declarations without diagnostics.
Locations and result exports reuse the frozen text; they do not recapture newer text as
if it had been checked. Canonical file and project results retain `scope.configuration`
as path/optional-text pairs; an absent file is represented by `null`. File inspection
additionally binds the isolated source to the original compilation input; grouped documentation and fixture inspection receive the
exact `Compilation.spec.source` values instead of recapturing them after compilation.
Both standalone documentation and combined project/documentation checking retain the
project source map and configuration frozen before dependency building through fence
compilation, grouped inspection and the final result. Worker requests use `sourceBindings`
as their sole source map; loader module/path pairs are projections of those bindings.
A detected source/configuration mismatch prevents success; the project adapter reports
RG2005/incomplete, including missing or unreadable previously frozen source/configuration.
Read failures preserve the underlying IO reason. Initial environment/setup failures remain RG2001;
only re-reading existing frozen evidence receives this normalization. The original file
path uses the shared guard, and combined mode checks its parent snapshots on declaration
worker failure as well as success.
`lake exe qualify documentation-source` qualifies both public
documentation paths with changed and missing dependency/configuration inputs and fresh
restored positives. Its `--source-read-only` selection additionally checks original-file
and declaration-build read failures, initial setup classification and restored positives;
these observations do not establish universal IO correctness.

This is exact observation equality, not a filesystem lock or source-to-olean theorem.
Lake build semantics, compiler/imported dependency authenticity, filesystem reads and the
absence of an undetected change-and-restore race remain trusted boundaries. Imported
unowned source is inspected only when required by an existing history obligation; this
does not add full-Mathlib analysis to Core-only adopters. Producer revision still identifies
its elaboration, not authenticated whole-binary provenance.

Owned logical replay failures and source coverage/range admission failures cross declaration and grouped-fence workers as typed
`ProducerReport.Outcome.admissionFailed`, carrying `AdmissionFailure.detail`. The shared
`Environment.validateSourceEvidence` guard supplies typed source-evidence refusal directly;
the producer and decoder use the same predicate, without classifying exception text. Public project,
file and documentation adapters emit RG2005/incomplete with that original reason and scope.
Documentation retains its RG4002/RG4004 finding alongside the typed refusal, using fence
context without manufacturing a valid declaration range. `SourceBinding.withUnchanged`
owns the before/after comparison around each frozen-input
operation. It retains the operation's result or IO exception, rechecks exact sources and
configuration, then returns a typed snapshot failure (rendered as RG2005/incomplete) or preserves the original
outcome when snapshots are unchanged. Initial capture still has setup semantics.
Environment imports, report workers, grouped decoding, file compilation/inspection,
project/file dependency builds and documentation use that same owner. The original
standalone file is frozen before dependency builds. Batch compilation creates snippet
files in its parent before dispatch; workers consume those files without rewriting them.
Failed builds, crashed workers and decoding failures cannot skip their owner's recheck.
A transported refusal is consumed only after worker-packet validation. Independently,
the parent's own snapshot check can return a typed refusal even when a worker crashes
or a packet is malformed; this does not accept or authenticate that worker result.
When snapshots are unchanged, the original worker or decoding failure is preserved. The selftest consumer renders the same detail as a diagnostic
fixture failure; compatibility IO wrappers have no public diagnostic consumer.
The four accepted-example kinds are unchanged. Expected INCOMPLETE diagnostics are separate
diagnostic demonstrations, never accepted conformance or accepted positive/rejection examples;
the full corpus and its matching/export adapter are documented in
[rule examples](rule-examples.md). Their qualified diagnostic result is not global Accepted.

ENGINE-01 was integrated through
[#30](https://github.com/rbeauchamp/regula/pull/30) and
[#31](https://github.com/rbeauchamp/regula/pull/31), and issue #13 closed on 2026-09-16.
