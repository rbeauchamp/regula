# Design influences and attribution scope

Regula is a Lean-native linter and rule-reference website. This account was last
re-checked for issue #10 against `a52bf1f0e2c7854c45ab6694b35b697b5e900fc8` on 2026-09-24. The
[ecosystem study](ecosystem-design.md) explains the broader selection of tools and APIs.

## What con-leche contributes

| Relationship | Actual scope | Treatment |
| --- | --- | --- |
| Design inspiration | `PropWhen` illustrates an invariant-bearing canonical representation with laws at its API boundary. `InstalledEnv`/`FullyChecked` illustrates acceptance bound to a specific installed input and all required record checks. The scanner equivalence proof (`Frontend/Scan/Equiv.lean`) illustrates proving a fast executed form equal to its reference definition, the pattern of `ruleForMember_eq` and the editor-policy theorems (`editor_request_sound`, `editor_decision_rule`). | Keep precise citations in registry/policy design documentation and relevant source attribution. |
| Current code or proof dependency | Root and website package manifests contain no con-leche dependency; the linter does not import its modules or invoke its checker. Existing registry attribution explicitly marks copied code false. | Do not describe Regula as built on con-leche or claim its correctness theorem applies here. |
| Rule detection and developer experience | The actual semantic host is Lean; native hooks, Lake, infoview, Std/library facilities and the cross-language UX references have their own roles. | Credit those facilities and examples where used. Con-leche does not supply the linter rules, editor adapter or website UX. |
| Optional external checking | #8 researched export/toolchain fidelity and ended in a no-go ([decision record](con-leche-research.md), pinned at `ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`); #9 is closed as not planned. No adapter exists, and neither issue was a core linter prerequisite. | Keep the `con-leche` topic label on both issues. Do not describe any con-leche run as Regula evidence. The record lists what would justify revisiting. |

The concrete precedents are [PropWhen][propwhen], [Installed][installed] and [scanner
equivalence][equiv], pinned at `c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0`; con-leche's
[README][conleche-readme] gives its Lean FRO context. Their universe-zero representation and
checker-specific environment are specialized implementations, not generic linter components
to import. Regula's existing closed `RuleId`/indexed descriptors and [policy
assembly](policy-acceptance.md) apply related ideas to different predicates. Ordinary
dependent types, canonical forms and complete indexing are broader techniques; con-leche is a documented example,
not their origin or an exclusive source. Prefer matching Core/Std/Lean definitions and laws
before writing a new implementation.

The [policy acceptance guide](policy-acceptance.md) owns the implemented assembly and
its delivery evidence. Registry laws concern Regula's own definitions. Neither
inspiration nor those laws establish extraction fidelity, whole-checker correctness or native runtime behavior. No source copy or imported con-leche
proof was found in the inspected linter surfaces.

## Lean and Lake interfaces used by adoption

The adoption adapters are built on interfaces by the Lean 4 and Lake authors (Lean FRO and
contributors), used through the pinned `v4.34.0` toolchain as dependencies. Except for the adapted parser below,
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

Core project issues use linter/policy terminology and do not carry the `con-leche` topic label.
Policy issues #4–#7 use POLICY-01–04; older CL-01–04 references identify the same issue numbers.
The label remains appropriate for actual con-leche research/adapter work and its historical archive.

[#3](https://github.com/rbeauchamp/regula/issues/3) preserves the original con-leche/con-ron
research. Keep it linked as historical background, outside the linter project's work-item list.
Its original report is not edited retroactively or treated as the controlling product plan.
Con-ron adoption remains outside scope. Project 8 and the current issue contracts govern delivery.

[propwhen]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean
[installed]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean
[equiv]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Frontend/Scan/Equiv.lean
[conleche-readme]: https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/README.md
