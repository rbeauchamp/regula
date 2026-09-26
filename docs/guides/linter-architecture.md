# Strict linter and rule-reference architecture

PRODUCT-01 (#11), design baseline: `f943f41c50876b25c8c5c2285e6ae4315645521e`.
This document records the implementation contract for Project 8. The registry, native
editor linter, `lake lint` driver and rule-reference [website](website.md) are implemented. DESIGN-01 supplements
this contract with [comparative ecosystem research](ecosystem-design.md) and the selected
[developer experience](developer-experience.md), including command/configuration semantics,
Mathlib-driver coexistence, presentation, search and the initial no-source-rewriting fix policy.
The retired one-rule probe (historical commit `e5bc6267fa44d03a174c10ba3711e9c32545dff2`) supplied bounded
interface evidence. The [coverage map](rule-coverage.md) accounts for the complete standard.

## Product and authority

Regula delivers an enforcing Lean linter and a linked rule-reference website, backed
by a precise standard. `docs/standard/` remains authoritative for normative meaning.
The Lean registry supplies machine metadata and diagnostic identity; checked source supplies
website examples. Neither a prose-only repository nor a green lint command establishes full
conformance. Every applicable chapter 9 row still needs its stated evidence.

Reuse the existing `Regula.Checker` implementation incrementally. Keep `Audit`, `AuditApp`
and standalone `Main` as dogfood surfaces. Operational tooling and intentionally invalid
fixtures remain separately classified. No new rule bans Float, IO, local mutation syntax,
classical erased proofs, noncomputable mathematical definitions, or arbitrary naming styles.

Con-ron is excluded. Optional con-leche export checking was researched in #8 and ended in a
[no-go](con-leche-research.md); #9 is not planned, and neither ever blocked the core linter/site
delivery. Preserve the user-selected acceptance: exactly `./scripts/verify.sh` (including cold root-package
builds after dependency setup) then `./scripts/verify.sh docs`, each under its own hard
**420-second** deadline. Website dependency provisioning, the site build and the diagnostic
campaigns are separate operations, not subdivisions or substitutes for that acceptance.

The [policy acceptance contract](policy-acceptance.md) refines the pure-core module
boundary, adds the explicit `freshFile` evidence mode, and owns complete-result semantics.
Its success-owner map records the implemented POLICY-02–04 boundary and remaining trust assumptions.

## Canonical data and package boundaries

Implement these modules under the existing root package (no mandatory Mathlib imports):

| Path | Owner and contract |
| --- | --- |
| `lean/RegulaCore/RuleId.lean` | Closed inductive `RuleId`, stable external spelling, exhaustive descriptor dispatch. |
| `lean/RegulaCore/Rule.lean` | `RuleDescriptor`, applicability, strict defaults, normative references, evidence modes, attribution, lifecycle, and the agent-facing requirement, rationale, remedy, rewrites and checked example pair every output renders. |
| `lean/RegulaCore/Feedback.lean` | Finding text generated from the registry and the proved run order and once-per-rule guidance of a command-line run. |
| `lean/RegulaCore/Guidance.lean`, `lean/Regula/Cli/Main.lean` | The offline `regula` command: rule explanation, rule index, agent briefing and Agent Skills file, with a proved command parser and a byte budget. |
| `lean/Regula/Diagnostic.lean` | Indexed diagnostic payloads, source/related locations, message rendering through `Feedback`, and run order of findings. |
| `lean/Regula/Checker/PolicyDomain.lean` | Compatibility re-export of the pure `RegulaPolicy` domain (canonical decoded inputs and typed failures, POLICY-02 #5); it holds no policy of its own. |
| `lean/Regula/Checker/Acceptance.lean` | Operational adapter to the pure acceptance API; see the [acceptance contract](policy-acceptance.md). |
| `lean/Regula/Linter.lean` | Public import for editor/command and module hooks; no full build inside a hook. |
| `lean/Regula/Linter/Rules.lean` | Adapters to existing detection, plus selected documentation-presence gaps; request and declaration decisions run the claimed `RegulaCore/EditorPolicy.lean` contracts, proved equal to the project checker's on the editor domain. |
| `lean/Regula/Checker/Lint.lean` | Whole-project `lint` driver: the `axiomGate` project audit, not another checker; its exit classification is the claimed `RegulaCore/Lint.lean` contract. |
| `lean/Regula/Contract.lean` | Preserve existing executable-proof API and admission meaning. |
| `website/` | Separate pinned Verso Lake package: the `RegulaSite` extension and site entry point. The original explanatory prose is `lean/RegulaCore/Guide.lean`; generated pages are never committed. |
| `examples/rules/<ID>/` | Actual violation/fix source plus typed expected outcome specification; isolated negatives. |
| `lean/RegulaCore/Site*.lean`, `lean/Regula/Site/` | Site generation, validation and assembly: proved pure decisions in the claimed core and the operational `site` builder, run through Lake; no Python or additional shell scripts. |

`RuleId` is the closed initial vocabulary in the coverage map, not a natural number or free
string accepted without validation. `descriptor : (id : RuleId) → RuleDescriptor id` is total by exhaustive
matching. External strings are serialized spellings (`RG1001`, etc.), not policy authority.
Never reuse an ID after changing its semantic predicate. Preserve retired descriptors as
tombstones; create a new ID for incompatible meaning. Compatible clarifications retain identity
and record the applicable implementation version. Chapter 9 IDs remain checklist rows, not
one-to-one diagnostic IDs.

Descriptor fields: `id`, title, category, normative clause references, applicability predicate
identifier, default strict severity, supported evidence modes, message form (derived from `messageLine`),
help route, requirement, rationale, remedy, compliant rewrites, checked example pair, introduced version, optional retired version/replacement, attribution records.
Attribution records identify source URL, exact revision, credited authors/project, borrowed idea
or adapted code, and applicable license notice. Derive route and ID text from `RuleId`, rather
than accepting independent arbitrary strings in each descriptor. Reject duplicate external IDs,
missing clauses/pages/examples, unknown JSON fields/versions, and invalid lifecycle references.

Use `Diagnostic (id : RuleId)` with `Payload id` for rule-specific arguments. Runtime collections
store the dependent pair `Σ id, Diagnostic id`; no invalid rule/argument combinations. A diagnostic
contains scope identity, evidence mode, severity, primary `Location` and related locations.
`Location` is a sum: actual source range (URI, start/end byte positions and validated conversion),
module location when no range exists, or project/configuration location. Never invent line 1 for
a generated declaration or use a declaration name as ownership. Validate ranges against the exact
source snapshot; convert to LSP UTF-16 using Lean's file map at the adapter boundary. Retain full
and selection ranges and label related dependencies rather than blaming a guessed source token.

Modes are `editorSnapshot`, `incrementalProject`, `freshProject`, `freshFile`, `documentationExample`;
optional `serializedGraph` is separate. A result carries its exact module/target/declaration scope,
source/configuration identity, toolchain and dependency identity, completed stages, violations and
unresolved obligations. Distinguish rejected, incomplete, and completed accepted outcomes.
Acceptance requires required coverage and completed admission, not merely an empty diagnostic list.
Cancelled/stale/unsupported/unknown results cannot construct accepted evidence. Editor snapshots
never construct a fresh whole-project result.

The implemented output schemas are versioned independently from manifest schema 2: registry
export is at schema 2 and result envelopes are at schema 3 (see [rule registry](rule-registry.md)).
Both have top-level schemaVersion, producerVersion, toolchain and sourceRevision, plus rules
(registry export) or scope/mode/status/stages/stagesCompleted/complete/stagesNotRun/diagnostics/rules/unresolved
(result export).
Encode `Name` reversibly, retain source positions, deterministically order exported collections,
reject duplicate identities at admission, and prove claimed decoder/encoder laws for actual
functions. JSON is transport; proof-bearing validated values are the in-process authority.

## Exact initial enforcement and evidence

The coverage map fixes **21 rule IDs**, including existing declaration, execution, workspace,
warning and fence capabilities and three narrowly scoped documentation-presence additions
(RG5001–RG5003; RG5003 was added for #57).
#12 introduces identity and rendering without silently changing detection. #13 connects all
existing conditions to typed IDs and implements the first two documentation gaps. Each rule page
states whether a condition is an established violation or missing evidence, what passes, and
what remains semantic review. Internal infrastructure errors are incomplete results, never
fabricated source violations or ordinary successful empty reports.

All initial rules are strict errors when applicable. Source-local options can control advisory
editor work but cannot authorize an exception in strict project mode. Keep only the technical
exceptions already in §§8.4–8.6 (authenticated generated helpers, separately classified teaching
native proofs, and origin-checked native-runtime boundaries). Excluded targets classify coverage;
imports from a positive surface do not disappear because their target was excluded. There is no
waiver or suppression policy added to the normative standard.

Proof obligations for #4/#5/#6/#7/#12: total rule metadata; injective external ID spelling;
route uniqueness; faithful decoding; exact profile set membership and least-label classification;
acceptance iff all required observations satisfy policy with complete exact scope; and extraction
of a complete accepted report preserving its original identity. Prove properties of the actual
executed policy definitions. Collection optimizations need checked correspondence, following the
con-leche pattern below. Do not claim a proof about decoded observations verifies their collection,
Lean's implementation, process integrity, source identity, or external execution. Preserve
`Admission.validate`, fresh source attribution, and conservative execution closure as explicit
boundaries while strengthening the pure core.

## Pinned Lean and Lake integration

The checker/examples use the [supported toolchain](../../README.md#supported-toolchain).
Check version/commit before pin-sensitive inspection; the compiler-dependent account
is specified in [module 8 §8.6](../standard/8-tooling-and-machine-audit.md#execution-roots-and-conservative-coverage).
Use Core/Std/Lean APIs without importing Mathlib into the linter. Adopters may use Mathlib;
transitive package resolution does not require compiling its mathematical modules.

- Command hooks: `Lean.Elab.Command.Linter` and `addLinter`; module hooks:
  `ModuleLinter` and `addModuleLinter`, from [Command.lean][command]. Their callbacks run in
  `CommandElabM`, may run asynchronously and must respect cancellation and snapshot identity.
- Environment hooks: `Lean.Linter.EnvLinter.EnvLinter`, with `test : Name → MetaM (Option
  MessageData)`, and `@[builtin_env_linter optionName]` on public meta definitions. Registration
  requires a Boolean option. [The native framework][env-lint] supports local omission/options;
  therefore its filtered default scan alone cannot establish Regula's mandatory coverage.
  Reuse compatible tests, not its suppression semantics as authority.
- Source/semantic evidence: `ConstantInfo`, `Lean.collectAxioms`, environment module indices,
  `Lean.findDeclarationRangesCore?`, file-map positions, elaboration info, and Lake's elaborated
  library arrays/executable roots. Reuse `Probe`, `Admission`, `Frontend`, `Lake` and `Policy`.
  Existing `Probe.ownedConstants` traverses imported module indices: it is **not** a ready-made
  current-document inventory. #13 must expose a shared declaration-record constructor and
  reconcile live command additions from the command environment with later imported-module
  records. Observe generated/private declarations and bind unfinished asynchronous results to
  the snapshot. Do not use source regexes or scan all imports after every command.
- Upstream reuse: Core's `linter.missingDocs` is useful but does not select exactly public
  declarations supporting material normative claims. #13 must use explicit claim registration
  plus `findDocString?` and module-doc metadata for the scoped presence checks. Text adequacy
  remains review. Reuse Batteries/Mathlib linter tests only after demonstrating their predicate
  and scope match; do not turn upstream optional style rules into universal strict rules.
- Lake [PackageConfig.lintDriver][lake-config] accepts `"regula/lint"` in either
  lakefile format. The `lint` executable is qualified end to end by the `lint-driver`
  campaign in both formats. The driver builds only explicit manifest-derived targets, never
  recursively the default policy target.
  Native `builtinLint` is separate and must not weaken strict policy.
- Preserve the existing uncached sole-default `policy` target for enabled plain `lake build`.
  `lakefile.toml` projects use the lint driver; the [adoption guide](adoption.md) documents
  which enforcing adapters are qualified. Direct `lean`, an explicit unrelated
  build target, and opting out cannot be advertised as whole-project enforcement.

Editor callbacks provide prompt local evidence and actionable diagnostics; they must not launch
nested whole-project builds. Complete `lake lint`/enabled build waits for the exact configured
modules and re-evaluates current policy/configuration even with cached `.olean` files. Fresh CI
acceptance additionally performs isolated root-source elaboration and completed kernel admission.
The driver rejects warnings even when source disables `warningAsError`. Local disabling of a
linter may prevent emission but never establishes its underlying predicate. Track pending costly
checks explicitly; do not display a project PASS while they are pending.

## Diagnostic link decision

Pinned [LSP diagnostics][lsp] have `code?` but no `codeDescription`. The native named-message
widget in [Lean.Log][log] hard-codes `Lean.manualRoot` and the manual error domain. Registering
an external error name does not redirect that widget to a project website.

The original design selected a package-owned JavaScript message widget with a textual
HTTPS fallback. The repository's Lean-only policy supersedes that implementation choice:
the textual URL remains. The production linter reuses the upstream
interface instead: `Lean.errorDescriptionWidget`, the builtin widget module behind Lean's
named errors, instantiated with `code = Regula.<ID>` and `explanationUrl = helpUrl id`
from the registry. It renders `Error code` and a **View explanation** anchor
(`target=_blank`, `rel=noreferrer noopener`) with no project JavaScript. Its text
alternative is empty, so plain renderers show the message text and its URL. Render tagged
`MessageData` with name `Regula.<ID>` through `logMessage`, supplying the actual file/range
and message context, rather than the `logAt` path that appends the wrong built-in widget.
The [interactive diagnostic adapter][interactive] derives `code?` from the named message kind.
The retired prototype verified serialized named kind, source location, policy rejection and
fallback URL; the former package-owned widget has been removed. The supported VS Code infoview interaction
was observed for opening the URL, the Problems-panel text fallback, code serialization,
non-BMP and CRLF ranges, stale and cancelled snapshots, and the absence of any Lean-manual
link ([record](https://github.com/rbeauchamp/regula/blob/11e05c682ee76ddf9b7cd81fdb827b572469ed57/session/evidence/issue-14-editor-journeys.md)). An ordinary browser
link check is not editor acceptance. No Lean fork or new
language server is selected.

## Website, versions, and synchronization

The rule reference is implemented (#15); the [website guide](website.md) is the maintained
account of its sources, guarantees, commands and publication. **Verso** is pinned in the
[website package](../../website/lakefile.toml) with its complete
[lock manifest](../../website/lake-manifest.json); do not resolve moving dependency branches
in CI. The documentation package and checker/examples use the same supported Lean release.
The separate documentation workspace follows the [package-docs template][template] at
`76c9edf5a70f14d272af0f0f354ec833ac22c350`; rendering remains distinct from checking examples.

The site builder (`lake exe site`, in the root package) generates Verso source from the registry
(`descriptor`, including the requirement, rationale, remedy, rewrites and example pair that
every finding also prints), the typed explanations (`RegulaCore.Guide`, one exhaustive definition over
`RuleId`, the explicit prose input the design allowed in place of `website/Rules/<ID>.lean`) and
the admitted rule-example exports of the same commit. Generation runs in the root package
because the website package cannot import the registry without resolving the root package's
Mathlib dependency. Checked sources render as escaped text; no re-elaboration by the documentation
compiler is claimed. Optional SubVerso highlighting may replace presentation only with exact
source/output correspondence. Generated Verso files are never edited or committed. Current
Markdown stays authoritative; the site links the standard at the build commit rather than
republishing it. No GitHub Wiki source repository is used.

Each page contains identity/category/default behavior, applicability and exact cause, normative
clauses, violation and fixed examples, the checked findings and their real locations, rationale,
fix guidance, permitted technical exceptions/configuration, limitations/false-positive conditions,
version availability, and credits. It does not imply that every violating Lean file fails
elaboration: the RG1001 axiom fixture elaborates and is then rejected by the actual policy.

Canonical public base: `https://rbeauchamp.github.io/regula/`.
Paths: `/regula/dev/rules/<ID>/` for latest successfully deployed development documentation;
`/regula/v/<package-version>/rules/<ID>/` for immutable released-package help (none exists);
`/regula/rev/<commit>/rules/<ID>/` for each published commit's snapshot. Every page states its
commit; a local preview with uncommitted changes says so and has no snapshot route. Publishing a
release is a separate authorized action. Each GitHub Pages deployment replaces the whole site, so
published `rev/` snapshots are retained in the append-only `site-archive-regula` branch and copied
verbatim into every later artifact ([website guide](website.md#routes-and-versions));
released-version pages will need the same kind of retention when releases exist. Retire IDs with explanatory tombstones; never redirect an old ID to
changed semantics. Unpublished routes get the not-available page, which names the GitHub source of
every revision and never falls back to the latest rules.

The builder admits the evidence, generates and renders the manual, assembles byte-identical
`dev/` and `rev/<commit>/` editions and every archived snapshot with `index.html`, `404.html` and
`build.json`, and checks the tree: size budget, exact layout, archived snapshots unchanged, one page per registered rule, admitted example text in each page, every
scanned link resolving under the base path, and the registry's `--validate-site`. Pinned
dependencies are cached by toolchain and lock digest; no accepted verdict is cached. Assets are
relative to each edition (Verso's `<base href>`).

CI runs the ordinary 420-second acceptance job, the two rule-example shards and the site
build/check on every PR and `main`, saving the validated artifact as `site-<commit>`. On `main`,
after the same revision's acceptance and site jobs pass, it uploads that artifact with
`actions/upload-pages-artifact` and deploys it with `actions/deploy-pages` in the `github-pages`
environment, after an unprivileged gate has checked the artifact against the site archive and a
provisioning-free `archive` job has pushed its snapshot there; only the deploy job has `pages:
write` and `id-token: write`, and only the `archive` job has `contents: write`. Action SHAs are pinned
to the current official releases. One run per ref (a newer `main` run cancels an older one), an
unprivileged gate and a dependency-free re-check in the deploy job that refuse a revision no
longer at the head of `main`, and a serialized deployment group keep an
older run from overwriting a newer one; a final job compares the live site with the artifact. A site lagging pending or failed CI is expected: the invariant
is same-revision consistency, not instantaneous agreement with latest main. No custom domain,
paid hosting, release or visibility change is involved.

## Delivery sequence and remaining decisions

1. #11: this design, full map, working one-rule slice, mission/navigation changes.
2. #4: pure acceptance design; #12: typed registry and diagnostics. Both require #11.
3. #20 after the #4/#12 delivery establishes comparative design; #5 after #4/#12/#20: canonical domain; #6 after #5: proofs about actual policy.
4. #13 after #12/#5: complete selected engine and current-document bridge; #7 after #6/#13:
   complete proof-bearing accepted reports.
5. #14 after #7/#13: conventional adoption and editor interaction; #15 after #12/#13/#7:
   complete rule site and publication workflow.
6. #10 after #7/#14/#15: integrated exact-scope product acceptance and documentation.
7. Optional #8 after #11 investigated con-leche export compatibility and ended in a
   [no-go](con-leche-research.md), so #9 is closed as not planned.

Open implementation details belong to their named issue: exact proof decomposition (#4/#6),
efficient live scheduling/current-document extraction and qualification (#13), supported client
widget interaction (#14), complete-site layout/accessibility and current action SHA selection (#15).
These are not permission to weaken the contracts above. Copy all newly settled requirements into
successor bodies before unblocking them. The linter cannot infer arbitrary intended specifications,
prove natural-language adequacy, or report unexecuted checks as PASS.

## Sources and credit

Canonical semantics, accepted values carrying evidence, and proved equality between an executed
form and its reference definition are informed by **Lean FRO's con-leche** at `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0`:
[Installed.lean][installed] (`CheckedRecord`, `FullyChecked`),
[PropWhen.lean][propwhen] and [scanner equivalence][equiv]. These are design precedents, not a
proof of Regula or an adoption of con-leche's kernel/model. The
[attribution account](design-influences.md) distinguishes these specific precedents from actual
code dependencies and optional exports. Cite influences at the relevant component boundary;
copied code preserves its actual license notices. Lean authors supply the linter, elaboration and message APIs; Verso authors
supply rendering and the template. [Microsoft CA1416][ca1416], Ruff and Pyrefly are illustrative
references, not exclusive templates. The [comparative study](ecosystem-design.md) records
Lean, Clippy, ESLint and HLint/HLS influences and their exact limits; no external tool defines
Lean policy or permits suppressing mandatory requirements. The archived comparative reference
is [issue #3](https://github.com/rbeauchamp/regula/issues/3); its con-ron discussion is historical.

[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean
[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
[equiv]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Frontend/Scan/Equiv.lean
[command]: https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Elab/Command.lean
[env-lint]: https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Linter/EnvLinter/Basic.lean
[lake-config]: https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/lake/Lake/Config/PackageConfig.lean
[lsp]: https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Data/Lsp/Diagnostics.lean
[log]: https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Log.lean
[interactive]: https://github.com/leanprover/lean4/blob/293d5d0c0c3f3dded4688b3ccd6a33939ac5102b/src/Lean/Widget/InteractiveDiagnostic.lean
[template]: https://github.com/leanprover/verso-templates/tree/76c9edf5a70f14d272af0f0f354ec833ac22c350/package-docs
[ca1416]: https://learn.microsoft.com/en-us/dotnet/fundamentals/code-analysis/quality-rules/ca1416

The CATALOG-01 implementation and schema migration are documented in
[Rule registry and diagnostics](rule-registry.md). Its scoped `completed` observations
are distinct from the [proof-bearing policy acceptance evidence](policy-acceptance.md).
