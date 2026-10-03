# Design influences and attribution scope

Regula is a Lean-native linter and rule-reference website. This is its attribution account:
the code it adapts, the interfaces it depends on and the designs that influenced it.

## What con-leche contributes

| Relationship | Actual scope | Treatment |
| --- | --- | --- |
| Design inspiration | `PropWhen` illustrates an invariant-bearing canonical representation with laws at its API boundary. `InstalledEnv`/`FullyChecked` illustrates acceptance bound to a specific installed input and all required record checks. The scanner equivalence proof (`Frontend/Scan/Equiv.lean`) illustrates proving a fast executed form equal to its reference definition, the pattern of `ruleForMember_eq` and the editor-policy theorems (`editor_request_sound`, `editor_decision_rule`). | Keep precise citations in registry/policy design documentation and relevant source attribution. |
| Current code or proof dependency | Root and website package manifests contain no con-leche dependency; the linter does not import its modules or invoke its checker. No con-leche code is copied. | Do not describe Regula as built on con-leche or claim its correctness theorem applies here. |
| Rule detection and developer experience | The actual semantic host is Lean; native hooks, Lake, infoview, Std/library facilities and the cross-language UX references have their own roles. | Credit those facilities and examples where used. Con-leche does not supply the linter rules, editor adapter or website UX. |
| Optional external checking | [#8](https://github.com/rbeauchamp/regula/issues/8) researched export/toolchain fidelity and ended in a no-go; [#9](https://github.com/rbeauchamp/regula/issues/9) is closed as not planned, and its body records the decision and what would justify revisiting it. No adapter exists, and con-leche was never run on a Regula artifact. | Do not describe any con-leche run as Regula evidence. |

The concrete precedents are [PropWhen][propwhen], [Installed][installed] and [scanner
equivalence][equiv], pinned at `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0`; con-leche's
[README][conleche-readme] gives its Lean FRO context. Their universe-zero representation and
checker-specific environment are specialized implementations, not generic linter components
to import. Regula's existing closed `RuleId`/indexed descriptors and [policy
assembly](proofs-and-boundaries.md#the-acceptance-boundary) apply related ideas to different predicates. Ordinary
dependent types, canonical forms and complete indexing are broader techniques; con-leche is a documented example,
not their origin or an exclusive source. Prefer matching Core/Std/Lean definitions and laws
before writing a new implementation.

The [acceptance boundary](proofs-and-boundaries.md#the-acceptance-boundary) owns the implemented assembly and
its delivery evidence. Registry laws concern Regula's own definitions. Neither
inspiration nor those laws establish extraction fidelity, whole-checker correctness or native runtime behavior. No source copy or imported con-leche
proof was found in the inspected linter surfaces.

## Lean and Lake interfaces used by adoption

The adoption adapters are built on interfaces by the Lean 4 and Lake authors (Lean FRO and
contributors), used through each checker revision's pinned toolchain as dependencies; the
stable reference is `v4.34.0`. Except for the adapted parser below,
no code is copied.
Lake's `lintDriver` package field and `lake lint` dispatch (`Lake.CLI.Main`, `Package.lint` in
`Lake.CLI.Actions`) run `lint`. Lean's `errorDescriptionWidget` in `Lean.Log`, the
builtin widget behind named errors, renders the editor's **View explanation** link with Regula's
registry URL. The VS Code Lean 4 extension and infoview (leanprover/vscode-lean4) host
these messages. These are dependencies, not design influences on Regula's policy.
The `regula` package that projects require imports only Lean's core libraries and requires no
other package. The repository's Mathlib-dependent `audit/` package (the standard's Mathlib
examples) and the website depend on Mathlib and, through it, Batteries (both Apache 2.0, pinned
dependencies).

## Adapted code and licenses

| Code | Origin and license | Treatment |
| --- | --- | --- |
| Container recursion of the strict JSON parser in [`PolicyCodec.lean`](../../lean/Regula/Checker/PolicyCodec.lean) | Lean 4's [`src/Lean/Data/Json/Parser.lean`](https://github.com/leanprover/lean4/blob/v4.34.0/src/Lean/Data/Json/Parser.lean) (notice as at `v4.34.0`), Copyright (c) 2019 Gabriel Ebner, authors Gabriel Ebner and Marc Huisinga, Apache 2.0 | Modified to reject duplicate keys. The upstream notice is retained in the source, the [Apache 2.0 text](../../LICENSES/Apache-2.0.txt) is in the repository, and the site's credits page names it. |

No other third-party code is copied or adapted in the linter, the site builder or the Verso
extension. The rest of Regula is MIT licensed ([LICENSE](../../LICENSE)).

## Other linters

Regula's architecture, one Lean package working inside Lean's own checking experience, was
chosen by comparison with other language tools, each credited for the idea it illustrates:
compiler-integrated semantic analysis (Rust's [Clippy][clippy] and Microsoft's
[Roslyn analyzers][roslyn]), extensible rule infrastructure ([ESLint][eslint]), cohesive rule
discovery and fixes (Astral's [Ruff][ruff]), editor and project scope with incremental analysis
(the [Pyrefly][pyrefly] team), and hints beside compiler feedback (Neil Mitchell's
[HLint][hlint] and the [Haskell Language Server][hls]). None of these examples prescribes an exact
UX or supplies Lean policy semantics or suppression permission. Lean's command, module and
environment linters, Batteries' linter driver and Mathlib's linter configuration are the Lean
facilities it builds beside. No code of these projects is copied.

## Website

The rule reference is rendered by Verso (Lean FRO and contributors, Apache 2.0) as a
pinned dependency ([license](https://github.com/leanprover/verso/blob/cad4b633e75ea769b851f12f9ca3b4f0dfcc625f/LICENSE)); the search and
table-of-contents scripts and stylesheets are Verso's, and the third-party components it bundles
(elasticlunr, fuzzysort, the W3C APG combobox) are listed with their licenses on the
generated credits page, together with the marked library that pages load from the jsDelivr CDN. The documentation/example toolchain separation follows
David Thrane Christiansen's package-docs template; no template text is copied. Microsoft's
CA1416 rule page is one illustrative reference for the page structure; no .NET content is used
and no affiliation with or endorsement by Microsoft is implied. The site's own theme layer
(`RegulaCore.SiteTheme` and the theme script in `website/RegulaSite.lean`) follows patterns
observed on other linters' references: ESLint's explicit Light, System and Dark buttons with
`aria-pressed`, Ruff's site-scoped theme storage key and its single rule table with select filters,
and Biome's and ESLint's rejected/accepted example labels. Its theme icons are drawn in the common
24-pixel stroke style of open icon sets such as Lucide; no stylesheet, script or icon file of
those projects is copied. Crediting any project here
implies no endorsement of Regula by it.
The explanations and site code are original. The site documents the registry, whose canonical
design credits con-leche above; con-leche did not design the site.

## Keep attribution proportionate

Credit actual copied/adapted code with its applicable license/notices. Cite identifiable design
influences at the component/design boundary, distinguishing inspiration from dependencies and
proof reuse. Do not require every unrelated issue, code module, rule page, CI change or PR to
mention con-leche. A shared metadata credit may link to this account; it is not a claim that
con-leche authored every rule or detector. Preserve meaningful existing attribution without
repeating it as product branding.

[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean
[equiv]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Frontend/Scan/Equiv.lean
[conleche-readme]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/README.md
[clippy]: https://github.com/rust-lang/rust-clippy/blob/47e8223f80ba7c748581b48c012252a45a9f512b/book/src/development/lint_passes.md
[roslyn]: https://learn.microsoft.com/en-us/visualstudio/code-quality/roslyn-analyzers-overview?view=visualstudio
[eslint]: https://github.com/eslint/eslint/blob/24310e3a0e22b3c086ca402f88448676f2e1cfcd/docs/src/extend/custom-rules.md
[ruff]: https://github.com/astral-sh/ruff/blob/feecd77879459f5285ac095542b667e86b3451ee/docs/linter.md
[pyrefly]: https://github.com/facebook/pyrefly/blob/3aa0829a5f6816341613a32a0640f01a817ecdef/ARCHITECTURE.md
[hlint]: https://github.com/ndmitchell/hlint/blob/c2509891034d99c86b658c1b1a121ed14d7f2434/README.md
[hls]: https://github.com/haskell/haskell-language-server/blob/01a25d4fd847a5d5cb7e9be7b218883475d7cbbf/docs/features.md
