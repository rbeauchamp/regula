# Native observation and local feedback

The native component (#25, a blocker of ENGINE-01 #13) uses the root package's
[supported toolchain](../../README.md#supported-toolchain).
Its native public import supports legacy files and Lean `module` files.
Its imports require Lean/Std and Regula's neutral policy modules;
they do not import Mathlib, `Regula.Report` or `Regula.Probe`.
The root development dependency on Mathlib is locked in the
[root manifest](../../lake-manifest.json).

## Use while editing

Import `Regula.Linter` from a project's chosen common import. It registers
Lean command and module linters. No project build or external process runs in
those callbacks. Lean owns asynchronous snapshots, cancellation and replacement
of messages after edits; Regula has no global last-seen cursor.

Local messages are ordinary Lean warnings with structured codes such as
`Regula.RG1001`, actual declaration ranges and development rule-reference
URLs. Each message also carries Lean's own error-code widget (`Lean.errorDescriptionWidget`,
a builtin widget module) with the same URL, so the infoview shows **View explanation**.
The widget's text alternative is empty; the message text keeps the URL for clients
without widgets. `warningAsError` promotes these warnings uniformly. The development links
identify the intended version; this component does not publish their pages.
For module/project findings, the canonical primary location stays module/project
scoped. Lean's UI hosts module findings at the actual end of the in-memory file;
configuration refusals use the owning command's actual position. Neither assigns
the finding to an invented declaration.

`linter.regula` defaults to true. It follows Lean's `linter.all` option
semantics; an explicit per-linter setting takes precedence. Disabling local
feedback cannot disable a mandatory project predicate, and enabling it cannot reach a project
audit's own build: `lake lint`'s claimed build and the audit's fresh elaboration pass the
unregistered command-line marker `weak.regula.auditBuild`, which the linter reads only from a
module's import-time options and under which it emits nothing, whatever a command scope sets
`linter.regula` to (`RegulaCore.EditorPolicy.liveFeedback_auditBuild`). The optional string
`regula.localFoundation` accepts `classification-only` (default),
`kernel-only`, `choice-free` or `standard-logical`. It requests local foundation
feedback, not a Lake surface claim. An unsupported request is a local configuration
violation on each affected nonterminal command snapshot, including declaration-free
commands. The module hook owns only the imports-only configuration fallback. This
ownership uses the normal Lean language frontend's preceding-command array; the old
low-level `Frontend.elabCommandAtFrontend` API is not a supported feedback driver.
This intentionally does not
deduplicate an invalid region across independent asynchronous snapshots. Lean's
`withSetOptionIn` restores scoped `set_option … in` options for local analysis,
including disabling and severity. The project manifest and its whole-project
enforcement remain separate.

## Module and proof interfaces

The native import chain uses Lean's module system, with metaprogramming
initializers registered in the meta phase. Proof-facing dependencies expose their
existing definitions so exported proofs and downstream reduction retain their
meaning. This requires some computational helpers to have public
bodies. Raw helpers such as `declarationFailure`, `labelOf`, `compilerAxiom` and
`boundaryEvidenceCandidate` are computational kernels over supplied data; they
are not receipt/admission APIs. `policyFor`/`foundationFor` and their member forms
`memberFailure`/`memberFoundation` require inventory-bound Roles, and
`admitBoundaryEvidence` preserves the supplied observation fields.
The candidate helper can discard incompatible fields. No raw helper constructs
accepted project evidence or forges an inventory-bound Roles receipt.

## Exact local scope

| Interface | What it establishes | What remains outside it |
| --- | --- | --- |
| Command hook / `Collect.commandDeclarations` | Records for constant binders in this command's Lean information trees; actual policy decisions RG1001–RG1007 when required evidence is available. | Elaborators can add constants without binder information. This is not a complete declaration census. |
| `Collect.currentModule` | All constants in Lean's current-module map, including private/generated/unused and binder-less declarations. | The caller establishes completion; a partially elaborated environment is still partial. |
| Module hook | RG5001 metadata presence, and RG5002 docstring and RG5003 Intent-section presence for explicitly registered public declarations in the completed local map. | It does not repeat all command policy diagnostics or certify complete local declaration-policy coverage. |
| `Collect.declaration name .snapshot` | Canonical semantic facts for that exact current/imported declaration, with Lean ownership, ranges, transitive axioms and contract shape. | Native replay and generated-role authentication are omitted. |
| `Collect.declaration name .replayCandidate` | The same constructor with existing replay/equation/parent observations used by `Probe`. | Observations still require fresh transcripts and the existing authorization/admission checks. |

The local adapter calls the executed pure policy and shares its total failure-to-ID
mapping with the project checker. It defers potential generated-role exceptions
as RG2005 incomplete feedback, whose message names `lake lint` as the project check,
rather than guessing authorization or emitting an
unsupported violation. Recoverable compiler errors can leave real hole-bearing
declarations; those observations can still produce RG1002 while preserving the
original compiler error. Unavailable collection is reported honestly.

No local result has an `Accepted` or project-PASS constructor. Fresh source
admission, ownership reconciliation, execution closure, mandatory documentation
jobs and complete result assembly belong to the
[project acceptance paths](policy-acceptance.md#1-observed-call-flow-and-every-success-boundary).
#13 retains the complete twenty-one-rule example corpus and #15 the published
[rule reference](website.md). The `lake lint` driver and its configuration explanation are in the
[adoption guide](adoption.md#6-enforce-with-lake-lint-lake-build-and-ci); the observed
VS Code journeys are in the [editor journeys record](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-14-editor-journeys.md).

## Documentation presence

Use `@[regula_material]` on a public declaration that states a material
normative claim. Its persistent Lean tag selects the RG5002 and RG5003 obligations. Private
names follow Lean's own visibility representation and do not enter that public
selector. `Lean.findDocString?` accepts ordinary, Verso and inherited docstrings.
RG5002 reports a missing docstring. RG5003 reports a docstring without a nonempty labelled
Intent section ([standard §5.2](../standard/5-documentation-standards.md#52-faithful-explanation-of-formal-claims)):
an ATX heading whose text is exactly `Intent`, with no closing sequence (write `# Intent`; a top-level Verso
docstring header must be `#`), followed before the next heading of equal or higher level by a non-heading
line with non-whitespace text; text under deeper subsection headings counts.
The executed classification is `RegulaPolicy.materialDocumentationFailure`, and
`materialDocumentationFailure_eq_none_iff`, `_eq_missingDocstring_iff` and
`_eq_missingIntent_iff` prove which docstrings each rule reports; the two rules never both
fire. There is no minimum length, intent detector, similarity check or adequacy inference.
The separate opt-in [intent screen](intent-screening.md) asks a pinned model to judge the intent
comparison and reports its measured calibration. Its results are never checked evidence. It is
a separate executable, not an in-elaboration rule: it calls a paid network service and sends
source text off the machine, so running it here would put network, cost and nondeterminism
into every build and editor session, against its off-by-default, cached, never-in-acceptance
constraints. Its findings reuse this linter's severity vocabulary (`Regula.Severity`) and
diagnostic shape, with a per-judgment `intentScreen/<judgment>` identifier in place of a
registry rule ID, the claim's declaration range as location, and the `screened` evidence class.

RG5001 uses both Markdown and Verso module-doc metadata. The imported-module
observer requires normal server/private documentation metadata to be loaded;
project callers use Lean imports with `importAll := true`, `loadExts := true`
and `level := .private`. Unknown module identity is unavailable evidence, not
an absent doc comment. An empty loaded metadata array means absence. Current
metadata is checked only after module completion by the native module hook.

Registration completeness, the meaning of material claims, stated assumptions,
and documentation adequacy remain R-DOC semantic review; whether the intent states the
requirement, and whether the declaration meets it, remain R-INTENT review. Presence alone does
not discharge every requirement of chapter 5.

## Rule-author and verification contract

Keep detectors separate from adapters. Construct `Finding` through the sole
registry and preserve its original `Name`, supported mode, impact and genuine
location. Missing ranges fall back to module attribution; invalid supplied
ranges fail. Do not rerun a complete imported environment scan per command,
create a second policy implementation, or use parser regexes for ownership.
Add modes only for actual producer interfaces and document their partial scope.

`lake exe qualify native` qualifies the actual native bridge,
including warning promotion, codes, current/imported ownership, private/generated
coverage and both documentation formats. Each of its 37 controls is its own compiler
process with its own source path; they run four at a time in dependency order, with the
imported-artifact controls after the artifacts they import and the restored controls after
every malformed one. The existing public adopter controls
in `checkerSelftest --policy-domain-only` qualify root coverage and forbidden
imports; `checkerSelftest --native-adopter-only` checks the production linter
import through the public project gate. These are bounded observations of operational API behavior, not proofs
of arbitrary Lean plugins, native machine code or editor interaction. Pure policy
proofs are documented separately in [policy-proofs.md](policy-proofs.md).

## Reuse and attribution

The shared record constructor is extracted from Regula's existing Probe;
it retains the same pure data domain. It directly reuses Lean's
[`getNewDecls`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Linter/Util.lean),
[`getDeclsInCurrModule`](https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Linter/EnvLinter/Frontend.lean),
command/module linter hooks, declaration ranges, axiom collection and docstring
APIs. Direct message publication follows Lean's logger semantics. It bypasses `logAt`,
which would attach Lean's widget with a Lean-manual URL, and instead attaches the same
upstream widget with Regula's rule URL. No upstream code is
copied or forked. See [design-influences.md](design-influences.md) for the separate
policy-design influences and their exact attribution boundary.

The project reporter force-loads the shared collector from the exact checker
artifact. Its mere presence is not an import by the claimed source. The
excluded-library scan omits it only when no non-probe module actually imports it;
real source imports retain normal exclusion checks. The forbidden Report/Probe
scan still inspects the collector. `checkerSelftest --forced-collector-only`
qualifies this distinction with fresh positive, excluded-source and restored
project controls. This does not exempt the whole linter or change manifest scope.
