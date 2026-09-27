# Ecosystem research and Lean-native design

DESIGN-01 (#20), researched 2026-09-15 against Regula
`79851f567ac8c1000575b707630e7ea593bfccb0`. This is an implementation-ready design,
not a claim that the remaining engine, editor adapters or public website have shipped.
The [architecture](linter-architecture.md) records package boundaries;
[developer experience](developer-experience.md) specifies the resulting interactions.
The [standard](https://rbeauchamp.github.io/regula/dev/standard/) remains the normative authority.

## Recommendation

Build a **Lean package that participates in Lean's existing checking experience**:
command/module hooks for timely local findings, semantic environment inspection for
completed declarations, and a Lake lint driver for the declared project scope. Use the
existing language server, infoview and build system. Keep the actual policy functions
shared across these adapters. A separate process is appropriate for isolated full checks;
a second parser, type checker or language server is not selected.

This conclusion follows from the ecosystem evidence below, not from a requirement to
imitate any one product. Microsoft CA1416, Ruff and Pyrefly were illustrative examples.
The comparison also includes Clippy, ESLint, HLint/Haskell Language Server, and Lean's own
core, Batteries and Mathlib facilities. Existing decisions were reassessed: the registry,
pure policy boundary and Verso remain useful; diagnostics, command semantics, configuration
explanation, rule discovery and fix policy receive more precise requirements.

## Method and evidence strength

The sample covers complementary design questions: compiler-integrated semantic analysis
(Lean, Clippy, Roslyn), extensible rule infrastructure (ESLint), cohesive rule discovery
and fixes (Ruff), editor/project scope and incremental type analysis (Pyrefly), and
functional-language hints alongside compiler feedback (HLint/HLS). It is representative,
not an exhaustive ranking of every popular tool. No star/download count selects a feature.

Sources are primary documentation and inspected implementation/configuration snapshots.
Immutable references below identify source-dependent claims. Rolling documentation was
read on the research date; it is not asserted to match every released binary. Captured
upstream development revisions are research evidence, not new Regula dependencies.

- **Source evidence:** exact APIs, configured integration and documented behavior.
- **Observed:** the small pinned Lean API compilation and Lake help inspection in §Verification.
- **Design inference:** fit, tradeoffs and the decisions below. They are not universal UX theorems.
- **Unresolved:** actual end-user usability, client interaction and performance of adapters
  that do not yet exist. No user interviews, production deployment or cross-tool benchmark
  was performed. No maintainer was contacted.

Evidence of established use is specific: Mathlib's pinned build configuration selects
linters and its CI invokes linting; HLS integrates HLint; Clippy documents the Cargo workflow;
Microsoft documents SDK/IDE analyzer integration. PyTorch's own team reports adopting
Pyrefly, while Pyrefly's maintainers report Instagram use. Ruff documents projects using it.
These establish concrete use/integration accounts, not comparative defect rates or proof
that every design choice is good. Pyrefly's shorter public history is not equated with the
maturity of every older tool. [Mathlib build][mathlib-lake], [Mathlib CI][mathlib-ci],
[HLS features][hls], [Clippy usage][clippy-use], [Roslyn][roslyn],
[PyTorch adoption][pytorch], [Pyrefly release account][pyrefly-use], [Ruff overview][ruff-use].

## What Lean developers already use

### Linters exist, alongside other checking tools

At Lean 4.33.1, command and module linter hooks are supported, as is a core environment
linter framework. Batteries has its own environment-linter machinery and driver; Mathlib
configures that driver and imports default syntax linters early. These are distinct
facilities with different admission/omission behavior, not interchangeable spellings for
one universal checker. The older community glossary is useful orientation but its
Batteries-only environment-linter description does not exhaust this newer core pin.
[Core hooks][command], [core environment linters][env], [Batteries][batteries],
[Mathlib configuration][mathlib-lake], [Mathlib imports][mathlib-init], [glossary][glossary].

The pinned Mathlib configuration supplies weak linter options to builds and selects
`batteries/runLinter` with `Mathlib` as its driver argument. Its CI deliberately also obtains
best-effort lint feedback after a failed build. That is useful feedback, not evidence that
a failed build was accepted. Regula must preserve the distinction rather than reuse
a best-effort report as a complete result. [Build configuration][mathlib-lake], [CI][mathlib-ci].

Experienced Lean users also interact with expected types, tactic goals, elaborator errors,
hover information, declaration navigation and proof suggestions. The official VS Code
manual places interactive diagnostics in the infoview and explains that unprocessed source
has no available elaboration information yet. Regula should contribute messages there,
with authentic ranges and scope, rather than demand a separate dashboard before users can
understand a problem. This is documented workflow evidence, not a survey of all Lean users.
[VS Code manual][vscode].

Std is part of the same pinned Lean distribution: its root exposes data structures,
monadic/program-verification facilities, tactics and other standard functionality. Reuse
its suitable collection abstractions and laws for the pure policy domain; do not add a
second collection framework because another linter uses one. The inspected native lint
extension points live under `Lean`, while Batteries/Mathlib add library-specific checks.
This is a statement about the inspected facilities, not a claim that no Std code performs
checking. [Pinned Std root][std], [Std tree maps][std-map].

### Two important working contexts

| Context | Existing workflow and useful Regula contribution | Boundary |
| --- | --- | --- |
| Theorem/library development | Edit a statement/proof, inspect goals and types, use existing tactics and library lemmas, inspect axiom dependencies, build and undergo library review. Add precise policy findings beside this evidence. | An unfinished proof is normal during editing. Completed detection of its hole is a violation; unfinished collection is incomplete. Final positive acceptance excludes holes. A compiled proof does not establish that its statement captures the intended mathematics. |
| Functional application development | Use Lean types and compilation, Lake executable targets, ordinary execution and explicit specifications/proofs where promised. Add registered-contract and execution-boundary explanations without forcing a Mathlib import. | Runtime effects and imported/native code have their documented trust boundaries. Successful evaluation is not a universal correctness argument. |

Mathlib's contribution guide explicitly combines editor/build work, CI and maintainer review.
Functional Programming in Lean demonstrates validation whose successful results carry
constraints in their types. These support complementary mechanisms, not replacing all
reasoning with lint rules. [Contribution workflow][contribute], [typed validation][fp].

There is no evidence here that Lean generally avoids linters. The narrower inference is
that some errors are already excluded by elaboration/types or discharged by proofs, while
other checks require an environment or whole-project account. Research did not establish
usage prevalence across industrial Lean application teams. #10 must report that limit and
qualify both a Core-only application and a Mathlib-using library experience; it must not
advertise broad user validation from these examples alone.

### Choose the stage from the information required

| Required information | Implementation choice | What it cannot establish alone |
| --- | --- | --- |
| Surface syntax / command source | Lean syntax and command hook; inspect elaboration output when meaning matters. | The meaning of overloaded notation, implicit arguments, inferred instances or macro-generated declarations from text alone. |
| Actual declaration/type/dependencies | Shared semantic collector over Lean's environment, structural names, ranges, axiom and contract data. | Complete current-module coverage from an imported-module-only traversal, or missing intended specifications. |
| Completed module metadata | Module hook / completed environment and module documentation. | Whole-project acceptance while other modules are pending. |
| Exact project scope and fresh admission | Lake-derived census, completed producer jobs, existing admission and pure policy decision. | Filesystem/compiler authenticity or natural-language adequacy beyond the stated trusted boundary. |
| A relation representable in an interface | Prefer existing types, law-bearing structures and explicit proof obligations. | Correctness of a different implementation or externally executed code from a theorem about a model. |

Dependent types, typeclass synthesis, macros and generated constants make semantic reuse
particularly valuable. Proof irrelevance does not make axiom policies irrelevant; a shorter
proof or a more convenient tactic is not automatically a stronger foundation. A change to
a type can change the claim being proved. Those are reasons to avoid generic “simplify/fix
all” behavior. The exact foundation/role/execution predicates stay in the existing
[coverage](rule-coverage.md) and [policy contracts](policy-acceptance.md); this research adds
no new normative rule, theorem or relaxation.

## Comparative decision matrix

“Adopt” means adopt the principle; actual integration still uses Lean facilities.

| System / mechanism examined | Useful lesson and decision | Lean-specific limit / rejected transfer |
| --- | --- | --- |
| Lean core, Batteries, Mathlib | **Adopt** native messages, semantic inspection, module-aware work and Lake dispatch. Maintain a predicate-by-predicate upstream reuse account. | Default scans, `nolint` and generated/private-declaration filters do not establish Regula's required coverage. Reuse matching tests, not their entire selection policy. [Core][env], [Batteries][batteries] |
| Ruff | **Adopt** a searchable code/name/message catalog, explicit availability and clear fix metadata. **Adapt** visible configuration provenance. | Prefix selection, nearest-file configuration and suppression are useful choices in Ruff, not Regula conformance authority. Do not automatically enable future upstream rules. [Rules][ruff-rules], [configuration][ruff-config] |
| Pyrefly | **Adopt** clear local/workspace scope, useful related evidence and consistent interpretation across editor/CLI. Reuse Lean's existing snapshot machinery. | Its inspected architecture chooses module-centric computation rather than a universal fine-grained query model. Do not copy a new engine or infer a Lean latency promise from Python performance reports. [IDE][pyrefly-ide], [architecture][pyrefly-arch] |
| ESLint | **Adopt** metadata/message IDs, documentation links, validated options and separation of suggestions from fixes. **Adapt** an inspectable effective configuration. | A runtime plugin marketplace, alternate parser and inherited JavaScript configuration are unnecessary for the closed initial Lean registry. [Rule API][eslint], [config inspection][eslint-config] |
| Clippy | **Adopt** placing a check at the compiler stage with the information it needs and invoking it through the ecosystem's build tool. | Rust AST/HIR passes do not map one-to-one onto Lean elaboration. Opinionated/pedantic lints and `allow` are not mandatory technical Lean requirements. [Passes][clippy], [usage][clippy-use] |
| Roslyn / CA1416 | **Adopt** source diagnostics connected to explanations and appropriate actions, with editor/build scope made visible. | CA1416 illustrates a rule page. Neither its visual layout nor .NET severity/suppression semantics dictate this product. [Analyzers][roslyn], [example page][ca1416] |
| HLint + HLS | **Adopt** hints coexisting with compiler diagnostics, hovers and navigation. Preserve manual judgment for semantic edits. | HLint documents type/scope and semantics limitations, including `seq`/eta reduction. A plausible functional rewrite is not evidence that a Lean theorem statement, elaborated program or effect behavior is preserved. [HLint][hlint], [HLS][hls] |

### Documented comparative journeys

These are reconstructions from primary examples and documented commands, not tools run
in a usability experiment. The correction/recheck columns describe the documented workflow
and our concrete application of it; no measured result or invented terminal transcript is supplied.

| Trigger and tool | Diagnostic → explanation → correction → recheck | Decision for Lean |
| --- | --- | --- |
| Ruff: unused NumPy import in its F401 example | `ruff check` reports F401; the page explains unused imports, re-exports and fix limits. Remove the genuinely unused import, then rerun the same check. An `__init__.py` export requires different reasoning. [Example and exceptions][ruff-f401] | Link the exact rule and context-specific repair; availability of a fix is not a blanket safety promise. |
| Pyrefly: integer assigned to a string-annotated variable | With project configuration enabling `bad-assignment`, the error-kinds guide identifies the mismatch. Inspect expected/actual types; if the string contract is intended, supply a string value, then rerun `pyrefly check` or let the editor recheck. Changing the annotation is a different contract decision. [Error example][pyrefly-errors], [entry point][pyrefly-install] | Surface expected evidence and the actual mismatch; never “fix” a Lean proof by silently changing its proposition. |
| ESLint: expected rule is apparently absent | Run `--debug` to locate configuration and `--print-config file.js` to see effective settings; correct the intended configuration and rerun the file check. [Configuration diagnosis][eslint-config] | Provide read-only effective configuration and origins so users can explain behavior without trial-and-error overrides. |
| CA1416: call to a platform-specific API | The diagnostic links to platform compatibility guidance. The page demonstrates platform guards or appropriately annotated calling code; choose the remedy that matches the application's actual contract, then rebuild with analysis enabled. [Guarded-call examples][ca1416] | Explain the condition under which a call is justified; do not transplant platform annotations or suppression into Lean. |
| HLint/HLS: separate `concat` and `map` | HLint's example supplies a source location, the original expression and a suggested `concatMap` replacement. Review the hint and caveats, edit, rerun HLint and compile; HLS presents hints alongside compiler diagnostics. [Documented hint][hlint], [editor integration][hls] | Keep explanation, navigation and compiler feedback together; successful hint removal is not a semantic proof. |

## Reuse and specialization decisions

Prefer, in order: an existing type/proof or semantic primitive that establishes the needed
property; a supported reusable API/component; an adapted existing implementation with
explicitly discharged assumptions; and finally a small new component for the remaining gap.
A similar name, public source repository or ability to import a module is not sufficient
evidence that its internals are intended as a supported extension surface. Read the API,
callers, scope/omission policy and version contract before selecting reuse.

| Candidate | Reuse decision and intended boundary | Why custom work remains / owner |
| --- | --- | --- |
| Lean command/module hooks, environment queries, FileMap, native messages | Reusable extension facilities; preserve required context, snapshot and cancellation behavior. | Adapter from exact Regula observations to existing messages; no new parser/typechecker/server. #13/#14 |
| Init/Std collections, structural Lean names, existing law-bearing interfaces | Reuse definitions and applicable laws. Match duplicate/order/key semantics before selecting a collection; do not infer canonicality from a container name. | Pure policy retains its own domain distinctions and proofs of actual acceptance predicates. #5/#6 |
| Batteries/Mathlib linter predicates | Reuse a test only after its exact selector, assumptions, dependencies and result meaning match; these are often specialized to library conventions. | Their default/private/generated/omission policies are not Regula's census. Keep mandatory scope and missing-evidence checks outside reused selection. #13 |
| Existing Regula registry, codecs, collector primitives and admission | Preserve their established responsibilities and qualification. Move neutral definitions to a safe shared dependency where needed, retaining compatibility re-exports. | Fix the public-import dependency boundary described in the companion guide; do not duplicate codecs or weaken contamination checks. #5/#13/#14 |
| Existing Lean server and infoview, Verso generator/renderer | Reuse supported presentation and project facilities; keep the proven separate documentation pin. | External-help fallback, concise human renderer and generated rule index are small product-specific pieces. #14/#15 |
| Ruff/Pyrefly/Clippy/Roslyn analysis engines | Specialized for their source languages and compiler models; use evidenced design ideas. | Importing or porting their engines would duplicate Lean semantics. No cross-language engine dependency selected. |
| ESLint rule API and HLint hints | Useful component-design examples; public extension contracts are distinct from private built-in rule internals. | Lean-native adapters and rules use Lean's own extension points. No wholesale copy or assumed rewrite equivalence. |

For each selected upstream test in #13, record the exact definition/revision, intended
extension status, input domain, omission behavior, dependencies, equivalence to the required
predicate and adapter qualification. Reuse does not require enabling unrelated rules or
weakening strict guarantees. Where a gap remains, name the smallest missing contract rather
than rebuilding the surrounding framework.

## Architecture decisions and alternatives

| Decision | Selected design and rationale | Alternative and cost | Owner |
| --- | --- | --- | --- |
| D1 Semantic host | Lean-native package hooks and Lake driver, shared with the existing checker. Leans on the ecosystem above. | Standalone parser/server duplicates semantics and user setup; rejected for this delivery. | #13/#14 |
| D2 Pure core and collection | Preserve separate `RegulaPolicy`, one typed registry, immutable claim/snapshot keys and complete required-job assembly. Reuse current collectors; add an actual current-document bridge. | A UI-specific policy evaluator or serializable “accepted=true” creates conflicting authorities; rejected. | #5–#7/#13 |
| D3 Feedback scope | Snapshot-local findings are useful immediately; completed project checks have their own result. Mark pending/incomplete evidence and discard stale findings. | Run a full build after each command: unnecessary repeated work and poor integration; rejected. | #13/#14 |
| D4 Rule scope | Preserve all twenty-two selected predicates and nine residual accounts. Mandatory project requirements remain mandatory. Keep upstream advisory linters identifiable as upstream. | Enable every ecosystem lint or invent a style tier to resemble another tool; rejected. | #13/#10 |
| D5 Configuration | One explicit project manifest selected by the existing project/manifest arguments; expose effective configuration and origin. Lean-local options govern local feedback only. | Automatic nearest-file inheritance or silent rule/profile weakening creates ambiguous claims; rejected. | #5/#14 |
| D6 Presentation | Concise problem/cause/action first; expandable evidence; native names and related locations; stable help fallback and deterministic CLI order. Preserve transport identity and all observations. | Dense serialized internals as the default infoview experience; revise the current prototype renderer in #14. | #14/#15 |
| D7 Actions | Ship navigation/explanation and human-authored remediation first. Initial Regula release has no automatic source-rewriting fix or fix-all. | General rewrite engine with asserted “safe fixes” lacks a justified semantic contract; deferred until a specific transformation is justified. | #14/#15 |
| D8 Website | Keep pinned Verso and checked-source generation; add generated searchable/filterable rule index and purpose-led pages. Server-rendered links work without search JavaScript. | Rebuild in a familiar web stack only to match another site's styling: no evidenced benefit over the proven prototype. | #15 |
| D9 Scheduling/cache | Use Lean snapshots and share work within a fixed environment; rerun policy for changed configuration and never cache an accepted verdict. | Cross-environment certificate cache or custom incremental engine needs linkage proofs and measured benefit not established here. | #13/#7 |
| D10 Adoption | Native import for local feedback plus explicit Lake driver/build setup for project enforcement. Publish exact supported commands, current scope and toolchain pin. | Treat installing an editor extension or `lake check-lint` success as completed strict analysis; rejected. | #14/#10 |

D5/D6/D8 are new concrete requirements; D1/D2/D4/D9 retain sound prior decisions with broader
justification. D7 settles the initial fix policy. D3/D10 sharpen pending-work and invocation
contracts. Existing code remains reusable; no registry IDs, semantic predicates, proof profiles
or source schema are changed in this research delivery.

### Recurring costs

Each supported Lean upgrade requires API/import-boundary requalification and regeneration
of affected evidence; editor upgrades need the focused message/link interaction checks.
Maintain the separate Verso dependency lock and checked-example toolchain deliberately.
Registry, codec/schema, examples and explanations must evolve together, with compatible
migration or explicit versioning. Retaining old help routes incurs ongoing artifact/link
maintenance. These costs favor a small adapter over a new server, a closed initial rule
set over a plugin platform, and reuse of existing definitions over parallel copies. They
do not justify freezing an unsuitable API indefinitely; pin changes belong in reviewed
compatibility work.

### Proofs and runtime are different responsibilities

The pure policy work proves properties of the executing validators over admitted observations.
Metaprogramming extracts observations and emits messages; being written in Lean does not prove
that extraction correct. Preserve source/admission/role qualification at that boundary. A
future code action must state exactly what it preserves (types, proposition, axioms, runtime
relation, effects, comments as applicable). Re-elaboration is necessary evidence for a Lean
edit, but successful elaboration alone does not show the intended claim stayed unchanged.
Ruff's safety distinction and ESLint's separate suggestions are useful UX precedents;
HLint supplies a concrete warning against treating all functional simplifications as semantic
identities. [Ruff fixes][ruff-linter], [ESLint suggestions][eslint], [HLint caveats][hlint].

## Verification and remaining decisions

A bounded interface check on Lean 4.33.1 compiled the ten `#check` queries for
`Command.Linter`, `ModuleLinter`, `addLinter`, `addModuleLinter`, core `EnvLinter`,
`collectAxioms`, `findDeclarationRangesCore?`, `findDocString?`, `getModuleDoc?` and
`Meta.isDefEq`. Lake's pinned help and `CLI.Main`/`CLI.Actions` were inspected together.
This establishes available signatures and documented/source dispatch, not callback adequacy
or end-user usability. The check used a disposable file under `tmp/`; no new theorem is claimed.
[Command implementation][command], [Lake dispatch][lake-main], [driver actions][lake-actions].

PR #19's unchanged prototype is prior bounded evidence for actual native named diagnostics,
Lake dependency dispatch, exact-source examples and Verso rendering. It did not verify live
VS Code interaction. No repeated prototype or timing campaign is necessary merely to choose
this design. The production journeys below remain acceptance work for their named owners.

Before empirical work, use these smallest informative evaluations:

- **#14 client interaction:** pinned supported VS Code extension; three journeys in the companion
  guide, plus Unicode/CRLF, stale/cancelled processing, disabled widgets and a missing help
  version. One disposable adopter at a time, 30 minutes per focused client pass. Success means
  correct source/action/scope and no stale success. If incomplete, report that result rather
  than declaring the budget a waiver. Actual user preference remains unmeasured.
- **#13 latency:** first derive bounded work from command/environment deltas and reuse existing
  Lean scheduling. Only if responsiveness is uncertain, measure edit-to-current-diagnostic
  on one Core-only application and one Mathlib-using library, with pins and machine recorded;
  separate dependency setup, cold/warm work and repeated edits. Limit the diagnostic campaign
  to 15 minutes, report distribution and cancellations, and use its results to set an honest
  supported-workload target. There is no numerical latency guarantee yet.
- **#15 site usability:** check keyboard traversal, readable narrow layout, text search, stable
  ID lookup, every supported filter and no-JS fallback on the generated production artifact.
  A 20-minute focused interaction pass is separate from build/link checks. Completion needs
  the actual evidence; an attractive mockup alone is insufficient.

These are product diagnostic budgets, not partitions of the unchanged 420-second ordinary
acceptance command. No new external tooling installation, upstream submission, release or
hosting change is part of this research delivery.

## Source ledger and credit

Historical research snapshot: Lean **4.33.1**, `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`; Batteries:
`4488d40d070b9700d4d5a6aa342f0d40c31b2a2d`. Documentation then used a separate
Lean 4.33.0 / Verso `3bdedf29bada13d8103e6c979001c51dcee210c8` pin.
The inspected VS Code source reports extension version 0.0.239; this is a research snapshot,
not an assertion that the user's installed extension matches it.

Immutable comparison snapshots (links target the inspected files, not release endorsements):
Ruff [linter][ruff-pin] and [configuration][ruff-config-pin]; Pyrefly [architecture][pyrefly-arch];
ESLint [rule API][eslint-pin]; Clippy [passes][clippy-pin]; HLint [README][hlint];
HLS [features][hls-pin]; Lean VS Code [manual][vscode]. Rolling web documentation is linked
at the claim it supports. When sources disagree across dates, the pinned Lean source governs
supported implementation; retain the discrepancy rather than silently combine incompatible APIs.

Credit each project and its contributors for the identified ideas. Lean FRO, Lean, Batteries,
Mathlib, Astral, the Pyrefly team, ESLint, Rust/Clippy, Microsoft, Neil Mitchell/HLint and HLS
supply distinct precedents. Con-leche's Joachim Breitner and contributors (Lean FRO) remain
credited for canonical and complete indexed representations via [PropWhen][propwhen] and
[Installed][installed]. No upstream code or proof is copied by this design; no endorsement
or proof of Regula is implied. Con-ron remains excluded.

[command]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Elab/Command.lean
[env]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Linter/EnvLinter/Basic.lean
[lake-main]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/lake/Lake/CLI/Main.lean
[lake-actions]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/lake/Lake/CLI/Actions.lean
[mathlib-lake]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/lakefile.lean
[mathlib-ci]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/.github/workflows/build_template.yml
[mathlib-init]: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Init.lean
[batteries]: https://github.com/leanprover-community/batteries/blob/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d/Batteries/Tactic/Lint/Basic.lean
[glossary]: https://leanprover-community.github.io/glossary.html#lint
[contribute]: https://leanprover-community.github.io/contribute/how-to-contribute.html
[fp]: https://lean-lang.org/functional_programming_in_lean/Functors___-Applicative-Functors___-and-Monads/Applicative-Functors/
[vscode]: https://github.com/leanprover/vscode-lean4/blob/4717483a63f18bde1e4a2dfc7938a57b8a1cd942/vscode-lean4/manual/manual.md
[ruff-rules]: https://docs.astral.sh/ruff/rules/
[ruff-config]: https://docs.astral.sh/ruff/configuration/
[ruff-linter]: https://docs.astral.sh/ruff/linter/
[ruff-use]: https://docs.astral.sh/ruff/
[pyrefly-ide]: https://pyrefly.org/en/docs/IDE/
[pyrefly-arch]: https://github.com/facebook/pyrefly/blob/3aa0829a5f6816341613a32a0640f01a817ecdef/ARCHITECTURE.md
[pyrefly-use]: https://pyrefly.org/blog/v1.0/
[pytorch]: https://pytorch.org/blog/pyrefly-now-type-checks-pytorch/
[eslint]: https://eslint.org/docs/latest/extend/custom-rules
[eslint-config]: https://eslint.org/docs/latest/use/configure/debug
[clippy]: https://doc.rust-lang.org/clippy/development/lint_passes.html
[clippy-use]: https://doc.rust-lang.org/clippy/usage.html
[roslyn]: https://learn.microsoft.com/en-us/visualstudio/code-quality/roslyn-analyzers-overview?view=visualstudio
[ca1416]: https://learn.microsoft.com/en-us/dotnet/fundamentals/code-analysis/quality-rules/ca1416
[hlint]: https://github.com/ndmitchell/hlint/blob/c2509891034d99c86b658c1b1a121ed14d7f2434/README.md
[hls]: https://haskell-language-server.readthedocs.io/en/latest/features.html
[ruff-pin]: https://github.com/astral-sh/ruff/blob/feecd77879459f5285ac095542b667e86b3451ee/docs/linter.md
[ruff-config-pin]: https://github.com/astral-sh/ruff/blob/feecd77879459f5285ac095542b667e86b3451ee/docs/configuration.md
[eslint-pin]: https://github.com/eslint/eslint/blob/24310e3a0e22b3c086ca402f88448676f2e1cfcd/docs/src/extend/custom-rules.md
[clippy-pin]: https://github.com/rust-lang/rust-clippy/blob/47e8223f80ba7c748581b48c012252a45a9f512b/book/src/development/lint_passes.md
[hls-pin]: https://github.com/haskell/haskell-language-server/blob/01a25d4fd847a5d5cb7e9be7b218883475d7cbbf/docs/features.md
[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean

[std]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Std.lean
[std-map]: https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Std/Data/TreeMap.lean
[ruff-f401]: https://docs.astral.sh/ruff/rules/unused-import/
[pyrefly-errors]: https://pyrefly.org/en/docs/error-kinds/#bad-assignment
[pyrefly-install]: https://pyrefly.org/en/docs/installation/
