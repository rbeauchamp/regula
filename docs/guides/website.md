# Rule-reference website

The rule reference at <https://rbeauchamp.github.io/regula/> explains every diagnostic the
linter can emit. Each Regula diagnostic ends with its rule's page in the edition of the installed
Regula version (the registry's `helpUrl`), and the editor's **View explanation** link opens the
same page. This guide covers where the site's content comes from, what its build establishes, how
it is published and versioned, and how to change a rule. It is repository practice, not part of
the normative standard.

## Sources and ownership

Nothing on a rule page is a hand-maintained copy of the linter. Each part has one owner:

| Content | Owner | How it reaches the page |
| --- | --- | --- |
| Rule identity, title, category, scope, subreason, modes, lifecycle, message form, clauses, route, help URL, and the agent-facing requirement, rationale, remedy (what to do), rewrites (how to fix it) and example correction that every finding and `lake exe regula` also print | [`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean) (`descriptor`, closed `RuleId`) | Projected by the page constructors; the index iterates `RuleId.all`. |
| Explanation sections (problem, trigger, further rationale, proof shape, established and not established, configuration, limitations, open obligations, checklist rows, sources, proved linkage) | [`RegulaCore.Guide`](../../lean/RegulaCore/Guide.lean) (`guide`, one exhaustive definition over `RuleId`) | Rendered in a fixed section order. A new rule without an explanation does not compile. |
| Violating and corrected inputs, findings, statuses | [`examples/rules/<ID>/`](../../examples/rules/) and [`corpus.json`](../../examples/rules/corpus.json), run by the rule-example campaign | The builder reads the campaign's exports for the same commit and renders the recorded bytes and findings. |
| What every rule shares: strict impact, local options, where rules run, the message form, open obligations, trusted mechanisms and example kinds | [`RegulaCore.SiteDocs`](../../lean/RegulaCore/SiteDocs.lean) `enforcementPage`; each obligation's text is `Residual.description` and each mechanism's `Trusted.detail` in [`RegulaCore.Account`](../../lean/RegulaCore/Account.lean) | Stated once on the *How rules are enforced* page, which every rule page links; each obligation is defined there under the element id of its identifier, which rule pages and the coverage page link (`residualRoute`). |
| Checklist coverage: every module 8 row with the rules that list it and the review obligations it carries | `coveragePage`, from `Regula.checklistRows` ([`RegulaCore.Standard`](../../lean/RegulaCore/Standard.lean)), each rule's `checklist` and each obligation's `Residual.rows` | `rulesOfRow` and `residualsOfRow` invert them (`mem_rulesOfRow`, `mem_residualsOfRow`), so the page cannot disagree with the rule pages or the obligations ([architecture](architecture.md#coverage-of-the-standard)). |
| Page construction, escaping, filters, diffs, banners, link checking | [`RegulaCore.Site`](../../lean/RegulaCore/Site.lean), [`SitePage`](../../lean/RegulaCore/SitePage.lean), [`SiteDocs`](../../lean/RegulaCore/SiteDocs.lean) (claimed, proved) | Pure functions the builder executes. |
| Releases, editions, help links and the route policy | [`RegulaCore.Edition`](../../lean/RegulaCore/Edition.lean) (claimed, proved) | `installed`, `releases`, `published`, `helpUrl` and `sitePath`. |
| Evidence admission, generation, rendering, release copies, assembly, artifact check | [`Regula.Site`](../../lean/Regula/Site/) (`lake exe site`, operational) | Writes `website/Generated/`, runs Verso, writes `_site/`. |
| The standard: normative text, checked Lean examples, section and checklist-row anchors | [`website/RegulaStandard.lean`](../../website/RegulaStandard.lean) and [`website/RegulaStandard/`](../../website/RegulaStandard/) (Verso, the only source), with the code blocks of [`RegulaExample`](../../website/RegulaExample.lean) | Included by the generated home page under `standard/`. Each `lean` block is elaborated where it is written, in a fresh [`regula-example`](../../website/RegulaExampleMain.lean) process with exactly its own imports. |
| Colours and stylesheet | [`RegulaCore.SiteTheme`](../../lean/RegulaCore/SiteTheme.lean) (claimed; contrast proved) | Written by the builder as `website/Generated/regula.css`, copied to each edition's root and linked from every page. |
| Rendering and theme script | [`website/`](../../website/): pinned Verso package (search feature only), `RegulaSite` extension (raw-HTML block and theme script) | `website/Generated/` is generated and ignored by Git. |
| Publication | [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) and [`Regula.Site.Deployment`](../../lean/Regula/Site/Deployment.lean) | `site`, `deploy` and `verify-deployment` jobs. |

The site publishes the standard under `standard/` of every edition, next to the rule pages. A
rule page links each registry clause ([`RegulaCore.Standard`](../../lean/RegulaCore/Standard.lean)
`Clause`) to its section anchor and each checklist row to its anchor on module 8, in the same
edition; rule pages do not restate the standard's normative text. The documentation
acceptance step renders the standard alone and requires each cited section in the elaborated
standard with its tag and exact heading in its chapter (`website/StandardMain.lean`), each cited
section's anchor on its chapter page and each linked row's anchor on module 8
(`Regula.Site.standardAnchors`), each page and anchor the `docs/` Markdown links in the
development standard (`Regula.Site.documentAnchors`), and the rendered checklist's rows to be
exactly `Regula.checklistRows`, in order (`Regula.Site.rowsMismatch`; a row is the `id` of an
element of class `Regula.checklistRowClass`). Every row a rule lists is one of them
(`guide_checklist_listed`). It also requires each cited section's source to be a module of the
library. Which rows a rule lists is reviewed with the rule; the artifact's
link check requires every anchor in the rendered site. The generator refuses a cited repository
path that does not exist.

## What the build establishes

`./scripts/verify.sh site` (below) proceeds only if all of the following hold; otherwise it
fails and removes `_site/`:

- **Evidence identity.** Both corpus shard exports are `COMPLETED`, are admitted again by the
  proved `ruleExampleQualification` executable, select every registered rule exactly once
  between them, record exactly the current bytes of the checker, corpus and configuration
  sources (`RuleExamples.sourcePaths`), and carry this commit (with the uncommitted-changes suffix
  only for a labelled local preview), toolchain and linter version.
  Each rule has one violating and one corrected record; the corrected run is a completed positive.
- **Totality and uniqueness.** Pages are generated by iterating `RuleId.all`.
  `pageFiles_nodup` and `mem_pageFiles` prove every rule has exactly one page route per edition
  and no two rules share one; `ruleModules_nodup` does the same for the generated Verso modules.
  The artifact check requires exactly the registry's rule directories in `dev/`, no more.
- **Diagnostic links.** `helpUrl_pagePath` proves the linter's emitted `helpUrl id` is the page
  of `id` in the installed build's edition; `helpUrl_release` and `helpUrl_unreleased` fix that
  edition, and `helpUrl_dev_iff` proves the link names `dev/` exactly when the build is
  unreleased. `installed_published` proves that edition is published, and the artifact check
  requires its page for every rule, so every emitted help link names a page of the artifact.
- **Page structure.** `ruleSections_sublist` and `required_mem_ruleSections` prove every rule
  page has every required section and only sections of the fixed order, the checked example
  first; the proof-shape and configuration sections appear when the rule has them.
  `guide_wellFormed` (kernel-checked over all rules) proves every required field is a nonempty
  string or list. Whether the content is adequate is review. The check also finds every
  required heading in the rendered page.
- **Exact examples.** Displayed example text is the recorded bytes, escaped by `escape`
  (`escape_safe`: no markup character or backtick survives) and inserted only through
  `htmlBlock` (`htmlBlock_ok`). Each diff is admitted only when it reproduces both line lists
  (`admitDiff`); a change of only the final line terminator is stated in words. The check
  requires the escaped text of every displayed fixture and finding detail in the rendered page. A
  file is attributed to a fixture only when its bytes are identical. Optional SubVerso
  highlighting may replace this presentation only with exact source/output correspondence.
- **The standard.** Every build removes the standard's earlier build outputs and elaborates it
  again, because Lake does not trace the root-package modules its examples import. Each `lean`
  block must elaborate as its kind requires (no error or warning, or an error matching its
  pattern and no warning) in a fresh process whose environment is exactly the block's own
  imports, with automatic implicits off and `linter.missingDocs` on, and
  rendering resolves every cross-reference and checklist-row anchor. Every line of every code
  block is at most 100 characters, the Lean community's limit, or the build fails; the
  stylesheet wraps a line that does not fit the column instead of scrolling sideways. An
  expected rejection is shown under the rule pages' verdict, *Rejected by Lean, as intended*,
  with the error message that matched its pattern as the evidence. Classifying the same
  blocks' declarations and axioms is the documentation step of acceptance, not the site build.
- **Links and base path.** Every `href` and `src` attribute the tokenizer finds in each
  HTML file of the artifact is resolved against its page and `<base href>`, following RFC 3986
  for schemes; `linkErrors_nil_iff` proves an empty result means each of those links reaches an
  existing artifact file (and fragment) under `/regula/`. CSS and JavaScript files,
  `srcset` and `meta refresh` targets are not scanned. External links are not fetched.
- **Registry validation.** The registry's own `axiomGate --validate-site` accepts the page
  inventory, the pages whose example content the check verified, and every rule ID the
  examples emitted.
- **Routes and editions.** Every artifact path is a root file or lies in a published edition
  (`sitePath`, `sitePath_iff`): `dev/` and `v/<version>/` for each of `Regula.releases`, nothing
  else. `dev/` is the rendered edition, byte for byte. Each release edition is its copy
  ([versions](#versions-and-routes)) with the latest-release banner on every HTML page when a
  later release exists. The artifact contains no hidden files (the Pages upload drops them);
  `build.json` records the commit, toolchain, linter version, Verso revision, per-rule evidence,
  the published editions, how each release edition was obtained (its asset or rendered from
  source) and whether the build's commit is the one the installed release's tag names.
- **Size.** The artifact is at most `artifactBudget` (900 MB) of file bytes, below GitHub Pages'
  1 GB limit on a published site. Each release adds one edition of a few megabytes.

These are statements about the builder's own output. The HTML tokenizer (`scanTags`) is a
small scanner of that output: the link theorem covers the links it extracts, not every link a
browser could follow. Verso, the browser, GitHub Pages and the network are trusted or observed.
Semantic accuracy of the explanations is review (R-DOC, R-INTENT), and a corpus pass is scoped
detector qualification, not a proof that the detectors are correct for all inputs.

## Build and preview locally

After provisioning the shared Mathlib and the pinned Verso package once:

```sh
./scripts/provision.sh                                # root setup (shared, read-only Mathlib)
(cd website && lake build verso/VersoManual)         # Verso setup
./scripts/verify.sh diagnostics rule-examples 1/2    # corpus shard 1
./scripts/verify.sh diagnostics rule-examples 2/2    # corpus shard 2
./scripts/verify.sh site                             # build and check _site/
```

The website package requires the root `regula` package and the Mathlib-dependent `audit/`
package by relative path, because the standard's examples import modules of both and Mathlib.
Like `audit/`, it names the root `.lake/packages` as its packages directory (`packagesDir`), so
one Mathlib checkout and its artifacts serve every workspace; its Git pins must equal those of
the packages it requires by path (the documentation check refuses a difference). The website
package and the checker and examples use the same supported Lean release. Verso setup is
also required before `./scripts/verify.sh docs`, which builds the standard.

Any change to a module source, the corpus or the Lake configuration makes earlier shard
exports stale; the site build refuses them, so rerun both shards. The checker embeds its commit
when `lean/Regula/Checker/Producer.lean` is compiled, and Lake reuses that build after a new
commit; the site build then refuses the evidence as another commit's. Delete
`.lake/build/lib/lean/Regula/Checker/Producer.*` before rerunning the shards. CI builds fresh. A
worktree with uncommitted changes produces a labelled local preview. Every build requests the
release asset of every release, and a build whose `installed` is a release also reads its tag
with `git ls-remote` ([versions](#versions-and-routes)), so a build needs network access once a
release exists. The artifact expects to be served at `/regula/`; any static file
server works if `_site/` is mounted at that path (for example a directory containing only a
`regula` link to `_site`).

## Publication

CI runs on every pull request and on `main`:

1. `verify`: the two [acceptance](contributing.md#develop-and-verify) steps. It also names the
   release the commit installs (`Regula.installed`), if any.
2. `rule-examples` (two shards): the corpus campaign; each uploads its export. The diagnostics
   workflow also runs both shards nightly on `main`.
3. `tag` (`main` only, and only for a commit whose `Regula.installed` is a release, after
   `verify` and `rule-examples`): until the release is published, creates tag `v<version>` at
   this commit or moves it here if the commit is still the head of `main`, and keeps a tag that
   already names it; once the release is published, refuses any other commit
   ([release](contributing.md#release)).
4. `site` (after `rule-examples` and after `tag` passed or was skipped): builds the site tooling,
   then `./scripts/verify.sh site` over this run's exports, and uploads the checked `_site/` as
   `site-<commit>` (preview) and, from a clean build of a release whose commit its tag names,
   that release's edition as `site-release-<commit>`. On `main` only, `Deployment gate` refuses
   an artifact built from uncommitted changes, from another commit than `GITHUB_SHA`, or with a
   release edition rendered from source by a build whose commit that release's tag does not name
   (the build's recorded value of `Regula.publishable`), and the checked `_site/` is then
   uploaded as the Pages artifact. Pull requests never publish.
5. `deploy` (`main` only, after `verify` and `site`): a dependency-free step asks the GitHub API
   (default token, `contents: read`) whether this commit is still the head of `main` and refuses
   otherwise; then `actions/deploy-pages` publishes exactly the validated artifact to the
   `github-pages` environment (which allows `main` only). Only this job has `pages: write` and
   `id-token: write`; it runs no checkout, provisioning or project code, so nothing it could
   fetch and execute can use its OIDC token.
6. `verify-deployment`: `Deployment verify` fetches the live `build.json` with a per-attempt
   query string until it equals the artifact's bytes, then requires the home page of every
   edition, every development rule page and every release edition's `build.json` to be served
   with the artifact's exact bytes, and an unpublished route to return the artifact's `404.html`
   with HTTP 404. It compares only those files.
7. `release` (only after `tag` passed and `verify-deployment` observed the release's pages live):
   publishes the GitHub release with the `site-release-<commit>` edition as its asset, then opens
   the reset pull request ([release](contributing.md#release)).

Each run on `main` cancels older runs of `main`, the deploy job refuses to publish a revision
that is no longer the head of `main` (for example a manual re-run of an older run, which
re-checks because the check is part of that job), and deployments are serialized in the
`github-pages` concurrency group. The `site` job and the corpus shards are not yet required
status checks (only `verify` is); until the operator adds them, a change that breaks the site can
merge and `main` stops deploying until it is fixed. The site can lag `main` while checks run or
after they fail; each page states its commit. Repository Pages settings use **GitHub Actions**
as the source. There is no custom domain or paid hosting. Actions are pinned by commit SHA.

## Versions and routes

| Route | Meaning |
| --- | --- |
| `/regula/dev/` | The development version: every deployment rebuilds it from `main`. An unreleased build's help links. |
| `/regula/v/<version>/` | The permanent copy of a release, made when it is released. A released build's help links. |
| any other path | The not-available page (HTTP 404). It never redirects to other rules. |

`Regula.installed` is the version of a build: a release, or unreleased; `Regula.releases` lists
every release, oldest first (`releases_ascending`), and a released build is one of them
(`installed_listed`). Every deployment publishes `dev/` and the edition of every release
(`published`). The pages of a release's edition are the site its release build rendered; once a
later release exists, the build inserts a banner at the top of each HTML page's content, directly
after Verso's content column tag (`bannerAnchor`, `insertBanner_ok`). The banner names the latest
release (`bannerRelease_eq_some`, `latest_greatest`) and links the same page in its edition, or
that edition's home page when it has no such page (`bannerTarget_mem`). The development edition
carries no banner.

A release's copy is its GitHub release asset `regula-site-<version>.tar.gz`, attached to the
release tagged `v<version>`: a gzip-compressed tar archive of that release's edition, paths
relative to the edition root. Every build requests the asset of each release (HTTP 404 means
absent; any other failure refuses) and, when it exists, takes that release's edition from it and
never renders it again (`Regula.releaseSource`, `releaseSource_asset_iff`). It refuses an
unreadable archive, a symbolic link, a copy without a home page, and a copy whose `build.json`
does not record a clean build of that release for this site. A build renders a release's edition
from source only while no asset exists, only as a build of that release, and only while its tag
`v<version>` is absent or names the build's commit (`releaseSource_render_iff`); any other build
refuses a release without an asset, so a release edition cannot silently drop out of a deployment
or be replaced. A build whose `installed` is a release refuses once that tag names another commit
(`labelAdmitted_release_iff`); the tag is read with `git ls-remote` because CI checkouts have no
tags. Publication needs the tagged build: the build records in `build.json` whether its artifact is
`publishable` (no release edition rendered from source unless its commit is the one the tag
names), `Deployment gate` refuses an artifact that is not, and only such a clean build writes the
release asset. That the asset stays the one attached at release rests on GitHub: immutable
releases, a repository setting that is on, forbid changing a published release's tag or assets.

A release takes these steps, in order ([release procedure](contributing.md#release)):

1. The Release workflow opens the release pull request, whose commit sets `Regula.installed` to
   the release, appends it to `Regula.releases`
   ([`RegulaCore.Edition`](../../lean/RegulaCore/Edition.lean)) and stamps every rule still
   marked unreleased as introduced by it. Before the tag exists, its site
   build renders the release's edition as a preview, which pull requests never publish.
2. When it merges, CI on `main` gives the head of `main`, which carries the release label, the
   tag `v<version>` once acceptance and the rule-example shards pass. That commit's site build then renders the
   release's edition, so it is publishable, and writes
   `tmp/site-release/regula-site-<version>.tar.gz`, kept as the `site-release-<commit>` artifact
   of that run. The deployment publishes `/v/<version>/`, with `dev/` carrying the release's
   label at that commit. Other pull requests still merge meanwhile and carry the label too; until
   the release is published, the tag follows the head of `main`, and a build of another labelled
   commit is refused only while the tag names a different one.
3. Once `verify-deployment` observes those pages live, CI attaches that file, from the commit the
   tag names, to the GitHub release `v<version>` as its permanent asset and publishes the release.
   The tag then never changes.
4. CI then opens the reset pull request, which sets `Regula.installed` back to `.unreleased` and
   restores the development label of `dev/`. Its site build and every later one take the
   release's edition from the asset. Until it merges, CI on `main` refuses every other commit
   that still carries the release label, because the tag names another commit.

Rule IDs are never reused for a changed rule. A retired rule keeps a page (its lifecycle chip
says so).

## Budgets

`./scripts/verify.sh site` runs under the deadline of every `verify.sh` mode
([contributor guide](contributing.md#develop-and-verify)); it is not part of acceptance.
In CI the site tooling is built in the preceding step (20-minute step limit) and Verso is
provisioned from cache by the shared provisioning action (within the job's 45-minute limit on
a miss). Pinned dependencies are cached by toolchain and lock digest; no accepted verdict is
cached. Link checking grows with the number of release editions. Observed timings are
observations, not guarantees.

## Changing a rule

A rule change touches its semantics, metadata, examples and explanation together, in one PR:

1. Registry: `descriptor` in `RegulaCore/Rule.lean`, including its requirement, rationale,
   remedy, rewrites and example pair; a new rule states `lifecycle := .active "unreleased"`,
   which the next release stamps. Never change an ID's meaning; add an ID and retire the
   old one. Regenerate the dogfooded skill with
   `lake exe regula skill > .agents/skills/regula/SKILL.md`; acceptance refuses a stale one.
2. Explanation: the rule's case of `guide` in `RegulaCore/Guide.lean`. Keep every statement no
   stronger than the detector and the standard; `@repo/PATH` links name repository files. State
   only what is specific to the rule; what every rule shares belongs on the enforcement page.
3. Examples: `examples/rules/<ID>/` and its `corpus.json` entry ([rule examples](architecture.md#rule-examples)).
4. Run both shards and `./scripts/verify.sh site`; open the affected pages in a browser at a
   narrow and a wide width.

Review reads the elaborated rule predicate, the explanation and the example together: the
explanation must describe exactly what the detector rejects and what a pass establishes, and
the correction must preserve the violating example's intended proposition or behavior. See the
review toolkit's [rule and site changes](../../.agents/skills/pr-review-toolkit/references/review-workflow.md#rule-and-site-changes).

## Accessibility and interface

Every explanation, link and the full rule catalogue work without JavaScript. The index's
category and reported-in (evidence mode) filters are native selects driven by generated CSS;
**Reset** is a form reset. The no-match notice is emitted for exactly the filter combinations
that list no rule (`mem_emptySelections`); that the generated CSS rules and row classes implement
`Selection.admits` holds by construction of the generator and was observed for several
combinations, not proved. The index shows one "Project" label for the incremental and fresh
project modes; `projectModes_coincide` proves that no registered rule has only one of them, and
the filter keeps the exact modes. On narrow screens index rows become cards; other wide tables
scroll inside a keyboard-focusable region.

Every colour is a token of [`RegulaCore.SiteTheme`](../../lean/RegulaCore/SiteTheme.lean) with
exactly one light and one dark value, emitted once with CSS `light-dark()`. In both themes,
`ink_on_paper` proves that every text token has at least 7:1 (body text and headings) or 4.5:1
(all other text) against every background token, and `control_on_paper` that the control
boundary has 3:1 (WCAG 1.4.11). The proofs are exact integer computations of the WCAG 2.x
relative-luminance formula (`channel_bracket` brackets every 8-bit channel), so a token change
that breaks a pair fails the build; reading them as real-valued ratios rests on one argued step
(`p ^ 5 ≤ x ^ 12` exactly when `p ≤ x ^ (12 / 5)` for nonnegative reals). The layer outside the
token block is checked by evaluation to write no hexadecimal or functional colour literal; that it
draws text and backgrounds only from the tokens, and overrides every colour of Verso's own
stylesheets the pages show, is review. Status is always carried by a word or a `+`/`-`/✗/✓
marker as well as colour. There are no web fonts and no third-party requests besides Verso's CDN
script.

The theme control (Light, Dark, System; System by default) is three buttons with
`aria-pressed`, in the header and, on narrow screens, at the foot of the table-of-contents
drawer. Its script is inlined in every page's `<head>`, so a stored choice applies before the
first paint. The choice is kept in the browser's `localStorage` under `regula-theme`, covers
every edition, and follows other open tabs; System stores nothing and follows the operating
system, including live changes. Without JavaScript there is no control and the pages follow the
operating system. The script also makes `/` focus the search box and patches defects of Verso's
page template until they are fixed upstream: it sets `lang="en"`, removes the viewport's zoom
lock, names the table-of-contents toggles and gives the search box the `combobox` role that its
`aria-expanded` state requires. Search and the collapsible table of contents are Verso's bundled
JavaScript; only Verso's search feature is enabled, so the site ships no KaTeX.
`prefers-reduced-motion` turns transitions off.

Lighthouse's accessibility category (Chrome headless, 2026-09-26, a local preview of the theme
change) scored 1.0 for the rule index and RG1002 in both themes at 1280 pixels, and for RG1002
on a 390-pixel phone viewport. These are bounded observations, not proofs of usability. The site
sets no cookies and has no accounts or analytics.

## Credits and licenses

The credits page is generated from `creditsPage` in
[`RegulaCore.SiteDocs`](../../lean/RegulaCore/SiteDocs.lean); that definition owns the page's
text. The attribution and license account it summarizes is
[design influences](design-influences.md).
