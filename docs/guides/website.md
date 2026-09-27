# Rule-reference website

The rule reference at <https://rbeauchamp.github.io/regula/> explains every diagnostic the
linter can emit. Each Regula diagnostic ends with its rule's development URL
`https://rbeauchamp.github.io/regula/dev/rules/<ID>/` (the registry's `helpUrl`), and the
editor's **View explanation** link opens the same page. This guide covers where the site's
content comes from, what its build establishes, how it is published, and how to change a rule.
It is repository practice, not part of the normative standard.

## Sources and ownership

Nothing on a rule page is a hand-maintained copy of the linter. Each part has one owner:

| Content | Owner | How it reaches the page |
| --- | --- | --- |
| Rule identity, title, category, scope, subreason, modes, availability, lifecycle, message form, clauses, route, help URL, and the agent-facing requirement, rationale, remedy (what to do), rewrites (how to fix it) and example correction that every finding and `lake exe regula` also print | [`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean) (`descriptor`, closed `RuleId`) | Projected by the page constructors; the index iterates `RuleId.all`. |
| Explanation sections (problem, trigger, further rationale, proof shape, established and not established, configuration, limitations, residual obligations, checklist rows, sources, proved linkage) | [`RegulaCore.Guide`](../../lean/RegulaCore/Guide.lean) (`guide`, one exhaustive definition over `RuleId`) | Rendered in a fixed section order. A new rule without an explanation does not compile. |
| Violating and corrected inputs, findings, statuses | [`examples/rules/<ID>/`](../../examples/rules/) and [`corpus.json`](../../examples/rules/corpus.json), run by the rule-example campaign | The builder reads the campaign's exports for the same commit and renders the recorded bytes and findings. |
| Open review obligations and trusted mechanisms | Each rule's `residuals` in `Guide` (the obligations [rule-coverage.md](rule-coverage.md) associates with it), typed as the checker's `Residual`; `Residual.all` and `Trusted` from [`RegulaCore.Account`](../../lean/RegulaCore/Account.lean) | Every page also states that each accepted result lists all residual obligations as open. The per-rule selection is reviewed, not derived. |
| Page construction, escaping, filters, diffs, link checking | [`RegulaCore.Site`](../../lean/RegulaCore/Site.lean), [`SitePage`](../../lean/RegulaCore/SitePage.lean), [`SiteDocs`](../../lean/RegulaCore/SiteDocs.lean) (claimed, proved) | Pure functions the builder executes. |
| Evidence admission, generation, rendering, assembly, artifact check | [`Regula.Site`](../../lean/Regula/Site/) (`lake exe site`, operational) | Writes `website/Generated/`, runs Verso, writes `_site/`. |
| The standard: normative text, checked Lean examples, section and checklist-row anchors | [`website/RegulaStandard.lean`](../../website/RegulaStandard.lean) and [`website/RegulaStandard/`](../../website/RegulaStandard/) (Verso, the only source), with the code blocks of [`RegulaExample`](../../website/RegulaExample.lean) | Included by the generated home page under `standard/`. Each `lean` block is elaborated where it is written, in a fresh [`regula-example`](../../website/RegulaExampleMain.lean) process with exactly its own imports. |
| Colours and stylesheet | [`RegulaCore.SiteTheme`](../../lean/RegulaCore/SiteTheme.lean) (claimed; contrast proved) | Written by the builder as `website/Generated/regula.css`, copied to each edition's root and linked from every page. |
| Rendering and theme script | [`website/`](../../website/): pinned Verso package (search feature only), `RegulaSite` extension (raw-HTML block and theme script) | `website/Generated/` is generated and ignored by Git. |
| Published revision snapshots | The append-only `site-archive-regula` branch (`rev/<commit>/` directories only), read by [`Regula.Site.Deployment`](../../lean/Regula/Site/Deployment.lean) | Copied verbatim into every artifact. |
| Publication | [`.github/workflows/ci.yml`](../../.github/workflows/ci.yml) | `site`, `deploy-gate`, `archive`, `deploy` and `verify-deployment` jobs. |

The site publishes the standard under `standard/` of every edition, next to the rule pages. A
rule page links each registry clause ([`RegulaCore.Standard`](../../lean/RegulaCore/Standard.lean)
`Clause`) to its section anchor and each checklist row to its anchor on module 9, in the same
edition; rule pages do not restate the standard's normative text. The documentation
acceptance step renders the standard alone and requires each cited section in the elaborated
standard with its tag and exact heading in its chapter (`website/StandardMain.lean`), each cited
section's anchor on its chapter page and each linked row's anchor on module 9
(`Regula.Site.standardAnchors`), each page and anchor the `docs/` Markdown links in the
development standard (`Regula.Site.documentAnchors`), and the
[coverage map](rule-coverage.md#complete-chapter-9-row-map)'s links into module 9 to be exactly
its rendered rows, in order, each labelled with its row (`Regula.Site.rowMapMismatch`; a row is
the `id` of an element of class `Regula.checklistRowClass`); the artifact's link check requires
every anchor in the rendered site. The generator refuses a cited repository path that does not
exist.

## What the build establishes

`./scripts/verify.sh site` (below) proceeds only if all of the following hold; otherwise it
fails and removes `_site/`:

- **Evidence identity.** Both corpus shard exports are `COMPLETED`, are admitted again by the
  proved `ruleExampleQualification` executable, select every registered rule exactly once
  between them, record exactly the current bytes of the checker, corpus and configuration
  sources (`RuleExamples.sourcePaths`), and carry this commit (with the uncommitted-changes suffix only for a labelled local preview),
  toolchain and linter version.
  Each rule has one violating and one corrected record; the corrected run is a completed positive.
- **Totality and uniqueness.** Pages are generated by iterating `RuleId.all`.
  `pageFiles_nodup` and `mem_pageFiles` prove every rule has exactly one page route per edition
  and no two rules share one; `ruleModules_nodup` does the same for the generated Verso modules.
  The artifact check requires exactly the registry's rule directories, no more.
- **Diagnostic links.** `Regula.Site.Build.helpUrl_dev` proves the linter's emitted
  `helpUrl id` is the site's development route of `id` (kernel-checked when `lake exe site` is
  built; it lives in the excluded operational library), and the artifact check requires that
  page to exist for every rule, so every emitted help link names a page of the artifact.
- **Page structure.** `ruleSections_headings` proves every rule page has the nine required
  sections in order, the checked example first; `guide_wellFormed` (kernel-checked over all rules) proves every required
  field is a nonempty string or list. Whether the content is adequate is review. The check also finds every heading in the rendered page.
- **Exact examples.** Displayed example text is the recorded bytes, escaped by `escape`
  (`escape_safe`: no markup character or backtick survives) and inserted only through
  `htmlBlock` (`htmlBlock_ok`). Each diff is admitted only when it reproduces both line lists (`admitDiff`); a change of only
  the final line terminator is stated in words. The check requires the escaped text of every displayed fixture and finding
  detail in the rendered page. A file is attributed to a fixture only when its bytes are identical.
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
  HTML file of the artifact, archived snapshots included, is resolved against its page and `<base href>`, following RFC 3986 for
  schemes; `linkErrors_nil_iff` proves an empty result means each of those links reaches an
  existing artifact file (and fragment) under `/regula/`. CSS and JavaScript files,
  `srcset` and `meta refresh` targets are not scanned. External links are not fetched.
- **Registry validation.** The registry's own `axiomGate --validate-site` accepts the page
  inventory, the pages whose example content the check verified, each rule's advertised
  availability from its descriptor, and every rule ID the examples emitted.
- **Editions and identity.** `dev/` and the current `rev/<commit>/` are byte-identical apart from
  the snapshot's `build.json` (unless that commit is already archived, when the archived copy is
  kept), and the artifact contains no hidden files (the Pages upload drops
  them); `build.json` records the commit, toolchain, linter version, Verso revision, per-rule
  evidence and the archived snapshots it retains, and each snapshot's own `build.json` records
  the build that produced it.
- **Retained snapshots.** The `rev/` children are exactly `artifactRevisions` of the fetched
  archive and the current clean build (`mem_artifactRevisions`), and every archived snapshot is
  byte-identical to the archive. Each archived snapshot is a set of regular files whose
  `build.json` names its own commit as a clean build. The link check covers the whole tree,
  so a link from an old snapshot to a page that no longer exists fails the build.
- **Size.** The artifact is at most `artifactBudget` (900 MB) of file bytes, below GitHub Pages'
  1 GB limit on a published site.

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
the packages it requires by path (the documentation check refuses a difference). Verso setup is also required before `./scripts/verify.sh docs`, which builds
the standard.

Any change to a module source, the corpus or the Lake configuration makes earlier shard
exports stale; the site build refuses them, so rerun both shards. The checker embeds its commit when
`lean/Regula/Checker/Producer.lean` is compiled, and Lake reuses that build after a new commit;
the site build then refuses the evidence as another commit's. Delete
`.lake/build/lib/lean/Regula/Checker/Producer.*` before rerunning the shards. CI builds fresh. A worktree with uncommitted
changes produces a labelled local preview without its own `rev/` snapshot. Every build reads the
site archive from `https://github.com/rbeauchamp/regula`, so it needs network access and
includes every published snapshot. The artifact expects to be
served at `/regula/`; any static file server works if `_site/` is mounted at that path
(for example a directory containing only a `regula` link to `_site`).

## Publication

CI runs on every pull request and on `main`:

1. `verify`: the two [acceptance](contributing.md#develop-and-verify) steps.
2. `rule-examples` (two shards): the corpus campaign; each uploads its export. The diagnostics
   workflow also runs both shards nightly on `main`.
3. `site`: builds the site tooling, then `./scripts/verify.sh site` over this run's exports and
   the current site archive, and uploads the checked `_site/` as `site-<commit>` (preview) and,
   on `main`, as the Pages artifact. Pull requests never publish.
4. `deploy-gate` (`main` only, after `verify` and `site`, unprivileged):
   [`Regula.Site.Deployment`](../../lean/Regula/Site/Deployment.lean) `gate` refuses an artifact
   built from uncommitted changes or from another commit, and a commit that is no longer the
   head of `main` (`git ls-remote`). It fetches the archive again and refuses unless the
   artifact's `rev/` snapshots are exactly the archived ones, byte for byte, plus this commit's,
   which must not be archived yet. It then writes the next archive commit (the archive head plus
   this commit's snapshot; an orphan commit for the first snapshot) as a Git bundle and reports
   the parent and the new commit as job outputs.
5. `archive` (`contents: write`): applies the bundle to the fetched archive head and pushes
   `site-archive-regula` without force. It runs no provisioning or project code, only checkout,
   artifact download and `git`.
6. `deploy`: dependency-free steps ask the GitHub API (default token, `contents: read`)
   whether `site-archive-regula` is the commit the gate wrote and whether this commit is still the head
   of `main`, and refuse otherwise; then `actions/deploy-pages` publishes exactly the validated
   artifact to the `github-pages` environment (which allows `main` only). Only this job has
   `pages: write` and `id-token: write`; only `archive` can write repository contents; the
   others have `contents: read`.
7. `verify-deployment`: `Deployment verify` fetches the live `build.json` with a per-attempt
   query string until it equals the artifact's bytes, then requires every rule page of every
   edition and the `build.json` of every revision snapshot to be served with the artifact's
   exact bytes, and an unpublished route to return the artifact's `404.html` with HTTP 404. It
   compares only those files.

Each run on `main` cancels older runs of `main`, the gate refuses to publish a revision that is
no longer the head of `main` (for example a manual re-run of an older run), and deployments are
serialized in the `github-pages` concurrency group. A push that lands between an older run's
gate and its deployment cancels that run, and its own run deploys afterwards; the remaining
window is GitHub's cancellation latency. Because the deploy job repeats the archive and
head-of-`main` checks itself, re-running only that job re-checks them. A commit whose snapshot
is already archived is refused by the gate (its snapshot is published by the next push to
`main`); so re-running all jobs of a run whose `archive` job succeeded fails at the gate, while
re-running only its failed jobs reuses the gate's result.

The deploy and archive jobs run no toolchain provisioning or project code. Anything those steps
fetch and execute (the Elan installer, Lake, the Mathlib cache tool, the checker) could request
the deploy job's OIDC token and deploy arbitrary content, or use the archive job's write token,
so the Lean gate runs in the unprivileged `deploy-gate` job. The deploy job keeps only the
runner's `gh` client and the pinned `deploy-pages` action; the archive job keeps checkout,
artifact download and `git`, and can only fast-forward `site-archive-regula`. Re-running an older run
while a newer one is in progress cancels the newer run and then refuses the older revision, so
nothing is published and the site stays on its previous deployment until the next push to
`main`. The `site` job and the corpus shards are not yet required status checks (only `verify`
is); until the operator adds them, a change that breaks the site can merge and `main` stops
deploying until it is fixed. The site can lag `main` while checks run or after they fail; each
page states its commit. Repository Pages settings use **GitHub Actions** as the source. There
is no custom domain, paid hosting or release; publishing the site is not a software release.
Actions are pinned by commit SHA.

## Retention

Each deployment replaces the whole Pages site, so published `rev/<commit>/` snapshots are kept
in the `site-archive-regula` branch and copied into every later artifact. Snapshots are archived
only for the base path they were built for. Invariant: **a snapshot published under `/regula/`
is never dropped by a later deployment.** The argument:

1. The archive is append-only: its only writer, the `archive` job, pushes without force, so a
   push that is not a fast-forward of the current head fails.
2. A snapshot is archived before it is deployed: `deploy` needs `archive`.
3. A deployed artifact contains exactly the archive at deploy time: the gate checks that the
   artifact's snapshots are the archived ones, byte for byte, plus its own, the archive commit
   the job pushed consists of those snapshots, and the deploy job checks that the archive head
   is still that commit immediately before deploying. `mem_artifactRevisions` and
   `archived_subset_artifactRevisions` state the builder's side exactly; `artifactRevisions_mono`
   states that a larger archive never yields a smaller artifact.
4. Deployments are serialized, so every earlier deployment finished, and archived its
   snapshots, before a later one checks the archive head.

Hence every snapshot an earlier deployment published under `/regula/` is in the archive when a
later deployment checks it, and so in that deployment. A failed deploy after a successful
`archive` leaves an archived, validated snapshot that is not yet published; the next deployment
publishes it. The residual window is the time between the deploy job's archive check and
`deploy-pages` completing; within it only another run's `archive` job could write, and that
run's own deployment waits for this one and then contains every snapshot. Rules 1 and 4 rest on
GitHub (the workflow's non-force push and the concurrency group); a repository rule forbidding
force pushes and deletion of `site-archive-regula` would enforce rule 1 against every writer and
is an operator setting that is not yet configured. An unreachable archive fails the build and
the gate; an absent branch is the empty archive.

The archive grows linearly with deployments to `main`: one snapshot is about 125 files and
about 1.9 MB (measured on a local build of the current site, not a measurement of the archive), so
GitHub Pages' 1 GB limit on a published site would be reached after roughly 500 deployments.
The build refuses an artifact above `artifactBudget` (900 MB of file bytes); reaching it stops
deployment rather than dropping snapshots. Link checking, byte comparison and deployment
verification also grow linearly; the site build's 420-second deadline may be reached before the
size budget, which likewise fails rather than drops a snapshot. Pruning snapshots would change
the documented meaning of their routes and needs a separate decision.

## Routes and versions

| Route | Meaning |
| --- | --- |
| `/regula/dev/rules/<ID>/` | Latest successfully deployed `main`; the linter's help links. |
| `/regula/rev/<commit>/rules/<ID>/` | Snapshot of a published commit, kept byte for byte by every later deployment (see [retention](#retention)). |
| `/regula/v/<version>/rules/<ID>/` | Reserved for released packages. None exist. |
| any other path | The not-available page (HTTP 404): it names the GitHub source of every revision and never redirects to the latest rules. |

Rule IDs are never reused for a changed rule. A retired rule keeps a page (its `Lifecycle` says
so). Publishing released-version pages requires a release, which is separately authorized; their
pages would need the same kind of retention as revision snapshots.

## Budgets

`./scripts/verify.sh site` runs under the deadline of every `verify.sh` mode
([contributor guide](contributing.md#develop-and-verify)); it is not part of acceptance.
In CI the site tooling is built in the preceding step (20-minute step limit) and Verso is
provisioned from cache by the shared provisioning action (within the job's 45-minute limit on
a miss). The site build's work grows with the
number of archived snapshots ([retention](#retention)). Observed timings are observations, not
guarantees.

## Changing a rule

A rule change touches its semantics, metadata, examples and explanation together, in one PR:

1. Registry: `descriptor` in `RegulaCore/Rule.lean`, including its requirement, rationale,
   remedy, rewrites and example pair. Never change an ID's meaning; add an ID and retire the
   old one. Regenerate the dogfooded skill with
   `lake exe regula skill > .agents/skills/regula/SKILL.md`; acceptance refuses a stale one.
2. Explanation: the rule's case of `guide` in `RegulaCore/Guide.lean`. Keep every statement no
   stronger than the detector and the standard; `@repo/PATH` links name repository files.
3. Examples: `examples/rules/<ID>/` and its `corpus.json` entry ([rule examples](rule-examples.md)).
4. Run both shards and `./scripts/verify.sh site`; open the affected pages in a browser at a
   narrow and a wide width.

Review reads the elaborated rule predicate, the explanation and the example together: the
explanation must describe exactly what the detector rejects and what a pass establishes, and
the correction must preserve the violating example's intended proposition or behavior. See the
review toolkit's [rule and site changes](../../.agents/skills/pr-review-toolkit/references/review-workflow.md#rule-and-site-changes).

## Accessibility and interface

Every explanation, link and the full rule catalogue work without JavaScript. The index's
category, reported-in (evidence mode) and availability filters are native selects driven by
generated CSS; **Reset** is a form reset. The no-match notice is emitted for exactly the filter
combinations that list no rule (`mem_emptySelections`); that the generated CSS rules and row
classes implement `Selection.admits` holds by construction of the generator and was observed
for several combinations, not proved. The index shows one "Project" label for the incremental and fresh project modes;
`projectModes_coincide` proves that no registered rule has only one of them, and the filter keeps
the exact modes. On narrow screens index rows become cards; other wide tables scroll inside a
keyboard-focusable region.

The theme described below covers `dev/` and every snapshot built with it. Snapshots archived
before it stay byte-identical to the archive (see [retention](#retention)), so they have no theme
control and still ship the KaTeX files that Verso bundled then.

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
every themed edition, and follows other open tabs; System stores nothing and follows the
operating system, including live changes. Without JavaScript there is no control and the pages
follow the operating system. The script also makes `/` focus the search box and patches
defects of Verso's page template until they are fixed upstream: it sets `lang="en"`, removes the
viewport's zoom lock, names the table-of-contents toggles and gives the search box the
`combobox` role that its `aria-expanded` state requires. Search and the collapsible table of
contents are Verso's bundled JavaScript; only Verso's search feature is enabled, so themed editions
ship no KaTeX. `prefers-reduced-motion` turns transitions off.

Lighthouse's accessibility category (Chrome headless, 2026-09-26, a local preview of the theme
change) scored 1.0 for the rule index and RG1002 in both themes at 1280 pixels, and for RG1002
on a 390-pixel phone viewport. These are bounded observations, not proofs of usability. The site
sets no cookies and has no accounts or analytics.

## Credits and licenses

The credits page is generated from `creditsPage` in
[`RegulaCore.SiteDocs`](../../lean/RegulaCore/SiteDocs.lean); that definition owns the page's
text. The attribution and license account it summarizes is
[design influences](design-influences.md).
