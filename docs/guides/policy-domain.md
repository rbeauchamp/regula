# Typed policy domain and admission

`RegulaPolicy` is the public, pure library used by the checker. Import
`RegulaPolicy` for its current domain and admission APIs. The normative meaning
of the rules remains in [the standard](https://rbeauchamp.github.io/regula/dev/standard/); the
[policy proofs guide](policy-proofs.md) describes the semantic guarantees. The
[acceptance contract](policy-acceptance.md) specifies complete-result integration.

Every normative requirement needs an explicit coverage disposition. Mechanically
checkable requirements become checks; other requirements need Lean proof evidence
or identified semantic review. Words such as **MUST** and **SHOULD** in a practical
guide do not create additional standard rules. A recommendation retains the
standard's stated latitude. The [coverage map](rule-coverage.md) records the
mechanical contributions and residual obligations.

## What is checked by construction

| Interface | Guarantee | Boundary |
| --- | --- | --- |
| Closed categories in `Domain` | Declaration kinds, boundary kinds, correspondence, foundation classes, conforming profiles, modes, safety, reducibility, recursion origin and evaluator roles have explicit constructors and spelling parsers. | Unsupported tags are refused. Pretty types, messages and evidence descriptions remain open text. |
| `Identity`, `canonicalNames`, `canonicalEdges` | Identities preserve Lean's actual `Name` constructors. Set-valued observations have sorted, duplicate-free projections with exact membership. | Nonanonymous identity does not establish ownership or extraction authenticity. Mutual groups and evaluator chains retain their order. |
| `BoundaryEvidence kind` | Replacement equality, simplification equality and opaque-body admission are distinct. A trusted native-runtime observation carries matching origin data. | The record observes compiler/kernel work; strings and serialized proof fields cannot authenticate that work. |
| `admitBoundaryEvidence` | Successful admission preserves correspondence, detail and native origin; incompatible extra evidence is refused. Every representable value round-trips. | Canonical path acquisition remains an operational check. |
| `Inventory`, `admitInventory` | Declaration and transcript identities are unique, references are structural, set fields are canonical, safety fields agree, and transcripts bind source bytes, supported compiler identity and valid coordinates. | An inventory is not an independently complete declaration census. |
| `Roles inventory`, `authorize` | Role arrays equal the actual validators' results for this exact admitted inventory. Declaration decisions require membership in the same inventory. | Validator success is proved equivalent to the named role predicates; observation authenticity remains external. |
| `EnvironmentRequest`, `EnvironmentCensus`, `CensusRoles` | The complete claim fixes the ordered environment/module partition. Local inventories and roles remain separate; local jobs carry that environment's snapshot and ordinal. | Equal names in different environments do not identify the same declaration or root. Extraction and source authenticity remain external. |
| `ExecutionInventory`, `admitExecution` | Root identities and boundary occurrences are unique; references and native-origin module bindings are valid. | Closure completeness still depends on the operational collector. |
| `Claim`, `admitClaim`, typed keys | Scope/mode combinations, positive profiles, exact source/configuration/dependency observations and key bindings are explicit. | A requested claim is not an accepted result. Teaching and no-profile inspection remain separate. |
| `ResultState`, `insertResult` | Each occupied key belongs to the fixed required set and satisfies its binding relation. Insertion rejects an occupied slot, including an identical repeat. | Insertion success/refusal and frame laws are proved. Whole-table acceptance additionally requires the fixed plan and every stage relation. |

The [acceptance contract](policy-acceptance.md#5-pure-module-boundary-and-migration)
owns the core's import boundary. `Specification` states
independent declaration predicates; `Plan` and `Observation`
define the concrete census, derived jobs and stage relations; `Acceptance` proves
soundness, completeness and report identity for those fixed inputs.
`Checker.PolicyDomain` is a compatibility re-export. `Checker.Acceptance` re-exports
the pure API and builds the operational census/observations without duplicating policy.

## Connection to execution

Lean/Lake observations retain structural names through discovery, reports,
transcripts and worker requests. The operational reporter converts compiler
categories directly to the closed domain. `Checker.Policy` adapts admitted data to
the sole rule-ID registry and existing text subreasons through the claimed
`RegulaCore.Policy` projections; it does not accept free arrays authorizing
generated roles. Execution failures and summaries use the same
admitted execution inventory.

Worker parsing rejects duplicate JSON fields before constructing a map. Record
parsers reject unknown and missing fields, unsupported tags and bounded numeric
overflow. Versioned response packets retain the request and producer/toolchain
identity. The parent waits for child exit before checking the response. Compilation
batches use `ResultState` to admit indexed payloads against their requested source
and artifact paths, then require all requested slots. Source workers additionally
bind their exact input text.

The project/file/documentation/optional-graph adapters populate the fixed census and
plan, execute `ResultState.collect` plus `finalize`, and retain `AcceptedRun` through
success rendering. Combined project/documentation uses `CombinedAccepted` with one
exact snapshot. The [success-owner map](policy-acceptance.md) separates these audit
routes from help, internal raw workers and local diagnostics. The core expectation
record retains exact diagnostic identities, optional subreasons and locations; the
registry adapter must validate its vocabulary and authenticate its observations.

The rendered `acceptance.environments` array retains each environment's ordinal,
module assignment, infrastructure modules, declaration/root/replay inventory and optional
file binding, not the modules it merely imports. Local job subjects contain that ordinal
and their local subject; the common snapshot is rendered once, with the audited sources
in full, the configuration by URI, a clean dependency by its pinned revision, and a dirty
dependency (including a path dependency without its own Git revision) only as
`{package, revision, dirty: true}`, with no content identity and no frozen text
([result schema 2 and later](rule-registry.md)). These fields are projections of accepted evidence,
not a wire format from which a caller can reconstruct proof authority.

## Compatibility and evidence

Positive `freshFile` claims reject warnings, including warnings emitted after a
source disables `warningAsError`. No-profile inspection remains classification.
Compiler-trusting teaching inspection cannot construct a conforming profile.

Versioned diagnostics retain structural identities.

The pure library is a separate Standard-Logical manifest surface, discovered by
Lake's `.andSubmodules`, and is included in `./scripts/verify.sh`. Its exact axiom
inventory is obtained by the same fresh declaration gate as the other positive
surfaces. Parser,
worker, generated-role, warning and execution controls qualify operational
boundaries; they do not prove universal correctness of compiler extraction or
full standard conformance.

After building the checker, `lake exe checkerSelftest --policy-domain-only`
qualifies strict transport, actual external-adopter public imports, forbidden
probe imports, recursion-helper execution coverage and positive-file warnings.
`--policy-transport-only` repeats just the parser/decoder/admission controls.
Run these diagnostics under the
[acceptance deadline](contributing.md#develop-and-verify); they do not replace ordinary
acceptance. The existing `./scripts/verify.sh diagnostics fixtures`
retains the declaration, generated-role and Markdown controls; execution-policy failure
kinds are proved instead ([control inventory](lean-qualification.md#control-inventory)).

The pinned compiler leaves some generated recursive-datatype helpers without
standalone IR. The probe recognizes the inductive/recursor relationship for that
specific absence, while retaining the helper as a root with its full source,
runtime-boundary and replacement-history checks. Retained compiler edges still
require IR. Public controls include both an authored tagged lookalike and a
runtime-modified genuine helper.

The universal results cover the actual category/name codecs, structural ordering,
canonical set projections, evidence admission, inventory/claim admission and full result
collection/finalization, least-foundation classification, role/declaration/execution decisions,
and concrete acceptance. See the [theorem and caller map](policy-proofs.md) for exact
hypotheses and limits. JSON text parsing and filesystem/process authenticity remain
operational boundaries.

## Reuse and attribution

Std supplies extensional ordered sets/maps and their laws; Lean supplies structural
names, compiler observations and operational coordinate conversion. The duplicate
JSON-field parser reuses Lean's scalar parser and adapts its container recursion
with the source's Apache-2.0 credit in `Checker.PolicyCodec`.

Con-leche's [PropWhen][propwhen] and [Installed][installed] informed canonical
representation and complete indexed assembly. This library does not import
con-leche code or claim its proofs establish Regula policy.

[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean

## Raw computations and receipt APIs

The native module import chain exposes proof-facing definitions for Lean's module
system. Computational helpers `declarationFailure`, `labelOf` and `compilerAxiom`
accept caller-supplied sets and do not authorize roles. Use `policyFor` and
`foundationFor` with the inventory-bound `Roles` receipt, or their member forms
`memberFailure`/`memberFoundation`, which also require a proof that the declaration
belongs to that inventory. Their registrations state agreement on every member:
the same decision, and `foundationFor`'s success value. Similarly,
`boundaryEvidenceCandidate` may discard incompatible fields; use
`admitBoundaryEvidence` when preserving every supplied observation field is required.
Public indexed constructors remain values, not attestations about an external producer.
