# Work on this repository

This guide describes this repository's layout and development commands. The
[standard](https://rbeauchamp.github.io/regula/dev/standard/) defines conformance; these instructions do not
prescribe a directory layout for other Lean projects. Read the current
[repository instructions](../../AGENTS.md) before changing the project.

## Find the relevant artifact

- **Rules and teaching:** [standard chapters](https://rbeauchamp.github.io/regula/dev/standard/);
  their only source is the Verso library in [`website/RegulaStandard/`](../../website/RegulaStandard/).
- **Contracts, examples, and checker internals:** [Lean module map](../../lean/README.md).
- **Standalone consumers:** [example projects](../../examples/README.md).

The root `lakefile.lean` sets the package source directory to `lean/`. Module
names and imports remain independent of that physical prefix: for example,
`lean/AuditApp/Limiter.lean` is still `AuditApp.Limiter`. That root `regula` package, the one
adopters require, requires nothing beyond the Lean toolchain. Everything that imports Mathlib is
the `regula_audit` package in [`audit/`](../../audit/lakefile.lean) (`audit/Audit/Research.lean`
is `Audit.Research`), which requires the root package by relative path and Mathlib, as a Mathlib
adopter would, and names the root `.lake/packages` as its packages directory. Run Lake commands
from the repository root, and the `audit/` package's in `audit/` (or with `lake -d audit`).
Lake's elaborated library and executable inventory owns source discovery; directory names alone
do not establish audit ownership.

## Develop and verify

Provision [elan](https://github.com/leanprover/elan), the pinned toolchain,
the shared Mathlib (`./scripts/provision.sh`), the website package's pinned Verso
(`(cd website && lake build verso/VersoManual)`), GNU coreutils timeout, and ShellCheck
before verification. On macOS, `brew install coreutils shellcheck` supplies the
last two tools. Verification runs offline against those pinned dependencies.

```sh
./scripts/provision.sh              # first, in a fresh copy: link the shared, read-only Mathlib
lake build                         # incremental development check (the regula package)
lake -d audit build                # the Mathlib-dependent package
./scripts/verify.sh                 # ordinary acceptance (project surfaces)
./scripts/verify.sh docs            # audit/ package, documentation examples and the Verso standard, linked to that acceptance
./scripts/verify.sh diagnostics fixtures # focused diagnostic qualification
```

Ordinary acceptance builds its checker executables, type-checks the diagnostic
modules and audits the root package's claimed Lean surfaces from fresh output. It also runs the
registry and native qualification controls (`qualify combined`, which runs those of
`qualify registry` and then `qualify native`). It refuses a root
lock manifest that records any dependency. It records the content
identity of the inputs it accepted in `tmp/acceptance-link.json`. `./scripts/verify.sh docs`
then audits the `audit/` package's claimed surface from fresh output, checks every Lean example
under `docs/` and in the Verso standard (each elaborated in the Verso package's workspace, which
requires both packages), builds and renders the standard fresh, and refuses unless its own freshly captured inputs have the same identity. `DOC-*` rows need both commands. The
declaration gate performs Lake-semantic discovery and a clean, warning-free build before
inspection, so a redundant preliminary clean build is unnecessary; `lake build` remains the
development command. Each command has its own hard seven-minute
limit; a timeout is an incomplete run, not acceptance. Provisioning happens before
that limit, under its own 30-minute limit. CI runs both commands, in that order in one job, after restoring or
provisioning pinned dependency caches.

The applicable command evidence is required but does not complete the standard's checklist:
theorem, type and prose rows still require semantic review. A conformance record for this
repository states the Lean version, the exact dependency source state (including Mathlib when
present), the claimed Lake modules, declaration coverage and exact axiom results, execution
boundaries, the applicable fence and checker-qualification results, and any failures or missing
evidence. A required check that was skipped leaves its affected row or optional claim
`INCOMPLETE`; it cannot support conformance. No CI, publication, merge, actual VS Code
interaction, or full repository semantic conformance is implied by local acceptance or scoped
integration results.

### Share one Mathlib across local copies

Locally, every copy uses one unpacked Mathlib per pinned revision and toolchain instead of
its own. The pin is the `mathlib` entry of `audit/lake-manifest.json`; the root package pins
nothing. [`lean/RegulaProvision.lean`](../../lean/RegulaProvision.lean) unpacks Mathlib's
archive cache (`~/.cache/mathlib`) once into
`~/.cache/mathlib-packages/<mathlib-rev>-lean-<toolchain-commit>/` (under
`$XDG_CACHE_HOME` instead of `~/.cache` when that is set), compiles every
module's native object there (executables that import Mathlib link them), makes it
read-only, and links the copy's `.lake/packages/mathlib` to it. The rest of Mathlib's closure
(Batteries, Aesop, ...) becomes writable copy-on-write clones, since executables compile
native objects into them. The `audit/` and `website/` packages name that root `.lake/packages`
as their packages directory; the example adopters under `examples/` require only `regula` and
need no packages directory. Run `./scripts/provision.sh` in a fresh copy before the first `lake build`,
which would otherwise clone and build a per-copy Mathlib; `./scripts/verify.sh` runs it
before its deadline. The first run for a new
pin takes about four minutes and needs the network; later copies take a few seconds and no
Mathlib space. The receipt `regula-provisioned.json` in the shared directory records its
revisions. A clean per-copy Mathlib checkout is replaced by the link; one with local
changes, stashes or commits that no remote-tracking branch holds is refused.

Each shared directory's registry `<dir>.copies.json` beside it records the copies provisioned
to link it; a copy is registered before it links. Every provisioning run removes the shared
directories of other pins and toolchains that no registered copy still links, and drops the
registrations of copies that are gone or link elsewhere. Only a directory whose receipt names
it is removed; a removal a killed run began is finished by the next run. A copy left with a
dangling link is relinked by its next provisioning, which recreates the directory. One lock,
`~/.cache/mathlib-packages/regula-provision.lock`, orders creation, registration and removal,
so copies wait while another copy creates a new pin.

- Do not run Mathlib's `cache get` locally (`lake -d audit exe cache get`): it unpacks a full
  Mathlib into the copy, and with the link in place it fails on the read-only directory. A Lake write into the shared
  Mathlib fails the same way, which is how an unintended rebuild shows up.
- Write probes that need Mathlib as single files under `tmp/` and check them with
  `lake -d audit env lean tmp/Probe.lean`; a separate Lake project there would fetch its own
  Mathlib. A probe that needs only the checker uses `lake env lean tmp/Probe.lean`.
- Scratch directories live in `tmp/.regula-scratch/`, each beside an ownership marker
  `<name>.owner`. Those of killed runs (for example at the seven-minute limit) are reclaimed
  by the next run that creates one while no other run in the copy holds scratch; only marked
  directories there are removed. Scratch outside `tmp/.regula-scratch/` is never reclaimed;
  remove it by hand.
- GitHub Actions keeps `lake -d audit exe cache get` and its dependency cache; provisioning does
  nothing there. A shared directory is never modified, only removed whole.

[AGENTS.md](../../AGENTS.md#changes-and-verification) owns verification and merge policy.
The [CI workflow](../../.github/workflows/ci.yml) defines runner and cache configuration.
Reuse evidence when its relevant inputs and claims remain unchanged; instruction-only
changes need scoped review rather than another Lean run.

### Choose focused diagnostics

Use `./scripts/verify.sh diagnostics PARTITION` when changes affect the corresponding
checker behavior:

| Partition | Focus |
| --- | --- |
| `fixtures` | Positive controls and intentionally invalid Lean declarations. |
| `structural` | Surface discovery, ownership, contamination, and required application contracts. |
| `cli` | Command-line behavior and diagnostics. |
| `environments` | Isolated environments, documentation scanning, and external adopters. |
| `build-policy` | Enforcement through the example's ordinary Lake build. |
| `lint-driver` | `lake lint` dispatch and exit classes in both shipped adopters. |
| `producers` | [Project producer and documentation qualification](proofs-and-boundaries.md#producers). |
| `history` | [Source-bound replacement history qualification](proofs-and-boundaries.md#producers). |
| `self-lint` | This repository's own `lake lint` through the `regula/lint` driver, in the root and `audit/` packages ([repository conformance](#repository-conformance)). |
| `self-audit` | Operational self-audit of the excluded `Regula` library ([repository conformance](#repository-conformance)). |
| `rule-examples`, `rule-examples 1/2`, `rule-examples 2/2` | [Source-owned corpus and diagnostic demonstrations](architecture.md#rule-examples); a shard runs half of the rules. |

The `environments` clean-checkout `freshChecker` control claims two import-free modules
written into a copy with no build directory. It establishes that `freshChecker` builds its
claimed targets itself, checks each maximal root, and reports accepted coverage of exactly
those modules. The control does not run `leanchecker --fresh` over this repository's claimed
graph. That replay rechecks Init, Lean and Mathlib once per root, and took more than 360 s.
It is the optional serialized-graph claim (§7.9), which ordinary acceptance does not include
and this repository does not make. `./scripts/verify.sh serialized-graph` remains its
command. Ordinary acceptance's isolated clean build still covers the real claimed surface.

Omitting `PARTITION` requests the `checkerSelftest` campaign; the `producers`, `history` and
`rule-examples` campaigns remain separate explicit selections. Each invocation uses the
same deadline; choose affected checks rather than treating every campaign as a routine
prerequisite. Checker changes need focused verification of the affected capabilities and public
invocation paths (standard
[§7.8](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#78-qualify-checker-implementations-with-independent-mutations));
the complete `checkerSelftest --build-bound` campaign is for broad qualification, not a per-change
gate. A selected diagnostic that fails remains a defect, and an unrun campaign is never reported
as passed. Run `./scripts/verify.sh serialized-graph` (`lake exe freshChecker --verbose`) only for
the separate serialized-graph claim: that claim needs fresh checker-state evidence for the exact
claimed graph, so run the driver when that graph, claim or driver changes, and reuse equivalent
coverage already obtained for the same inputs rather than repeating the same roots in a raw
invocation. Diagnostics do not replace a failed acceptance run.

The [diagnostics workflow](../../.github/workflows/diagnostics.yml) runs `producers`,
`history` and `lint-driver` as parallel jobs, each with its own hard 420-second limit, when the
checker, rules, rule examples, the adopter fixtures in `examples/lake-lint-toml` and
`examples/build-lint`, Lake configuration or manifests change, on every push to `main`, and
nightly; it also runs both `rule-examples` shards nightly. [CI](../../.github/workflows/ci.yml)
runs both shards on every pull request and push to `main`, where they feed
`./scripts/verify.sh site` ([website guide](website.md)). These campaigns are
capability-triggered diagnostics (standard §7.8), not a partition of ordinary acceptance.
The [dogfood workflow](../../.github/workflows/dogfood.yml) runs `self-lint` and `self-audit`
as parallel jobs under the same limit when Lean sources, Lake configuration or manifests
change, on every push to `main`, and nightly. They are not part of acceptance.

## Implementation and qualification layout

Project-owned implementation is Lean 4; `scripts/verify.sh` is the minimal acceptance
shell boundary. Additional shell scripts require explicit approval under `AGENTS.md`. Direct
commands in CI and developer setup examples are invocation recipes, not a second implementation
language for qualification logic.
[Proofs and boundaries](proofs-and-boundaries.md) gives the proof/IO split and why the
integration controls are still necessary. Configuration and external toolchains are
not claimed as formally verified Lean implementations.

## Repository conformance

This repository applies the standard to its own code and qualifies the checkers it publishes.
Its claimed surfaces are those of the root [`foundation_manifest.json`](../../foundation_manifest.json)
(`RegulaPolicy`, `RegulaCore`, `RegulaQualification`, `RegulaVerification`, `RegulaProvision` and
`AuditApp` with its standalone `Main`) and the `Audit` library of
[`audit/foundation_manifest.json`](../../audit/foundation_manifest.json). Ordinary acceptance
audits both freshly, with every target built under the options of
[Follow the Lean community's conventions](#follow-the-lean-communitys-conventions).

- `Audit` uses an all-submodules glob, so Lake's elaborated inventory owns its module set. It is
  the claimed surface of the Mathlib-dependent `audit/` package, which requires the checker by
  relative path exactly as a Mathlib adopter does and is audited against its own surface
  manifest, so the checker package requires no Mathlib. `audit/Audit/` is one positive surface
  holding mathematical models, proofs and executable examples, not the checker, and contains no
  project axioms, holes, compiler-trusting proofs, authored partial or unsafe declarations,
  runtime replacements or external declarations; generated partial helpers for safe recursion are
  separately authenticated under standard
  [§7.4](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#74-inventory-every-owned-declaration).
- `AuditApp` and its claimed `auditApp` executable apply the complete-program contracts of
  standard [§3.7](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#37-a-compositional-method-for-complete-program-contracts)
  to their actual definitions: `RequiredContracts` states the required propositions and
  `required_contracts` supplies their proofs; `executeChecked` requires that evidence, admits
  capacity and runs the strict state/error script. Its success, first-refusal and append theorems
  describe the retained successful prefix; the intrinsic `Limiter` bound supplies the state
  invariant. `checked_executable` registers the exact admission/runner relation through
  `ExecutableContract`, reusing `executeChecked_exact`, and `Main` invokes its `run` with
  `required_contracts`. The total `run` and `execute` remain available, so review inspects the
  actual caller. In `report` mode, the `IO` shell and reached native mechanisms are reported as
  execution boundaries; these pure contracts do not prove terminal effects or compiler/runtime
  correctness. `AuditApp` registers its
  material claims with `@[regula_material]`, so acceptance checks their docstrings and Intent
  sections.
- `lean/Fixtures/` holds isolated positive controls and independent mutations, imported by no
  positive surface. The checker executables are discovered as root-package `lean_exe` targets and
  recorded in `excluded-executables`: they are operational tooling whose root modules belong to
  the excluded `Regula` library, qualified by the diagnostic campaigns rather than claimed.
- Every Lean block of the Verso standard and every `lean` fence of the Markdown below `docs/`
  (the guides, which scanning does not make normative) is checked verbatim, before environment
  inspection, by `./scripts/verify.sh docs`.
- Checker changes receive focused qualification for affected capabilities under standard §7.8;
  unchanged capability evidence is reused. When this repository claims separate serialized-graph
  checking, it runs a fresh `leanchecker` pass over every declared root needed for complete module
  coverage.

Two diagnostics apply Regula to the rest of its own code base; neither is part of acceptance.
`./scripts/verify.sh diagnostics self-lint` runs `lake lint` through the `regula/lint` driver in
the root package and then in `audit/`, exactly as an adopter does. Both packages set
`lintDriver := "regula/lint"`, so it runs over each package's `foundation_manifest.json` in
incremental mode and checks the same claimed surfaces as acceptance, through the driver's
dispatch and exit classes. `./scripts/verify.sh
diagnostics self-audit` checks the excluded operational `Regula` library: `lake build Regula`
builds every module warning-free (RG2003, because the package sets `warningAsError`), then
`qualify self-audit` inspects each module of the library as Lake discovers it, each in its own
worker (several roots define `main`, so the modules cannot share one environment). For each
module it kernel-replays every owned declaration that is not `unsafe` or `partial` (RG2005,
`Admission.validate`), decides every declaration record from the live linter's collector
(`Regula.Collect.declaration`) with the proved `RegulaPolicy.checked_operationalFailure`
(RG1001–RG1005, RG1007), and checks module and material-claim docs with the linter's predicates
(RG5001–RG5003). Operational code is held to Standard-Logical with two facts reported, not
failed: authored `unsafe`/`partial` declarations (RG1006), and, in a definition whose type is not
a proposition, the pinned toolchain's Lake axioms (those a `Lake` module in the toolchain's own
library directory declares). `operationalFailure_none_iff` states the exact success relation,
`operationalFailure_ne_escapeHatch` that an escape hatch never fails a declaration,
`operationalFailure_prop` that a proof gets exactly the conforming decision, and
`operationalFailure_eq_conforming` that the decision is the conforming one on every declaration
without a reported fact. The self-audit claims no proof surface and no execution result, and
applies the linter's collector and decisions to completed modules rather than attaching its
editor hooks. Lean's import and kernel replay, the collector's observations, toolchain artifact
paths, the worker processes and their JSON transport are trusted.

The repository's own checklist rows, which apply to this repository only:

| ID | Required result | Normative source | Required Lean-specific verification |
| --- | --- | --- | --- |
| DOGFOOD-01 | The repository's own claimed Lean surfaces — the `Audit` library of mathematical models, proofs, and executable examples (in the Mathlib-dependent package in `audit/`), the `AuditApp` complete application with its standalone `Main` executable root, and the pure libraries `RegulaPolicy`, `RegulaCore`, `RegulaQualification`, `RegulaVerification` and `RegulaProvision` — satisfy every applicable row of the standard's checklist. | [Repository conformance](#repository-conformance) | Audit each claimed Lake surface as an ordinary claimed surface with no special exemptions; the application's admission, update, and composition contracts are proved about the same computable definitions its executable runs, and its `IO` boundary is reported, never silently excluded. |
| DOGFOOD-02 | Intentionally invalid fixtures are isolated from the positive elaborated environment. | [§7.2](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#72-define-surfaces-through-lake-semantics), [Repository conformance](#repository-conformance) | Reconcile exact imported project modules. Qualification includes a contamination mutation. |
| DOGFOOD-03 | Normative prose, representative Lean fixtures, checker diagnostics, and status text make no stronger claim than the same verified property. | [§1.6](https://rbeauchamp.github.io/regula/dev/standard/1-core-principles/#16-claim-boundaries-and-automated-checking), [Repository conformance](#repository-conformance) | Compare advertised capabilities with the checked implementation and applicable qualification evidence. Diagnostic qualification does not prove the checker is universally correct. |
| DOGFOOD-04 | Examples and fixtures reuse or extend matching Lean/Mathlib mathematical definitions. Custom mathematical definitions state their meaning and why existing definitions do not fit; proofs follow the economy guidance in §3.2.5. | [§1.4](https://rbeauchamp.github.io/regula/dev/standard/1-core-principles/#14-principled-mathematical-modeling), [§3.2.5](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#325-proof-economy-four-cost-domains-and-one-trust-question) | Compare custom mathematical structures, classes, and aliases with the pinned libraries and inspect required justifications. Review proof reuse where it simplifies the argument. A domain definition or teaching proof does not need a claim that no library theorem exists. |
| DOGFOOD-05 | The complete application enforces its explicit required propositions: omitting executable classification, removing or weakening required evidence while its proposition remains, or weakening admission fails the gate. Semantic review rejects a narrowed requirement set or bypassed application linkage. | [§7.8](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#78-qualify-checker-implementations-with-independent-mutations), [Repository conformance](#repository-conformance) | Inspect `RequiredContracts`, its evidence, and `Main`'s call through `checked_executable.run` to `executeChecked` for adequacy and completeness. The diagnostic campaign includes `app-omitted-exe`, `app-unproved-update`, `app-trivial-update`, `app-weakened-update`, `app-missing-contract-field`, and `app-weakened-admission`, each with its intended diagnostic and a fresh restored control. |

A repository conformance claim records what [Develop and verify](#develop-and-verify) lists and
follows the standard's [result rule](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/#result-rule), stating which rows it
covers; a scoped review does not establish full conformance.

## Follow the Lean community's conventions

Regula's own code follows the community conventions that
[standard §6.7](https://rbeauchamp.github.io/regula/dev/standard/6-code-organization/#67-community-conventions-and-linters)
requires of claimed code:

- **Style and naming.** Regula's libraries build on Lean core (only the `audit/` package's
  `Audit` imports Mathlib), so they follow Lean core's
  [style guide](https://github.com/leanprover/lean4/blob/master/doc/std/style.md), for example
  `fun x =>` rather than Mathlib's preferred `fun x ↦`, and the shared case rules of the
  [naming conventions](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md):
  proofs, including `ExecutableContract` registrations, in `snake_case`; propositions and
  types in `UpperCamelCase`; other terms in `lowerCamelCase`.
- **Options and linters.** Every library and executable builds with `autoImplicit` and
  `relaxedAutoImplicit` off and `linter.missingDocs` on (the package `leanOptions`; only the
  `Fixtures` controls turn the linter off); `Audit` also enables Mathlib's standard linter set
  with the §6.7 exclusions (`mathlibLinters` in `audit/lakefile.lean`). RG2006 checks these options on the claimed targets. Declare universes and
  implicit binders explicitly, and give every public declaration, constructor and field a
  docstring that states what it is or guarantees, no more than its definition and proofs
  establish (standard §5.1).
- **Module docstrings.** Each module starts, directly after its imports and before any
  `public section`, with a `/-! # Title … -/` docstring (RG5001 checks the position).
- **Evaluation is observation.** Prefer a kernel-checked `example … := by decide` to a
  `#guard`; where kernel reduction is infeasible, keep the `#guard` with a comment saying it is
  a compiled-evaluation observation.
- **Commit messages.** Use the community's
  [commit convention](https://leanprover-community.github.io/contribute/commit.html):
  `<type>(<scope>): <subject>`, with type `feat`, `fix`, `doc`, `style`, `refactor`, `test`,
  `chore`, `perf` or `ci` (`doc`, not `docs`), the scope a library, module or directory
  (for example `RegulaCore`, `website`, `lean/Regula/Checker`), and a lowercase imperative
  subject without a final period.

## Change prose and code together

Keep a teaching example beside the prose when it helps readers. Every Lean fence
under `docs/`, including this guides directory, and every `lean` block of the Verso standard
follows the [checked example convention](https://rbeauchamp.github.io/regula/dev/standard/introduction/#lean-example-convention).
Link to the actual Lean module for larger definitions and proofs; do not copy an
implementation merely to mirror the chapter structure.

For review, use the repository-local
[review toolkit](../../.agents/skills/pr-review-toolkit/SKILL.md) and the applicable
[compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/), with the repository rows above. Scope verification to
the affected claims, retain required checks, and distinguish historical results
from evidence for the current revision.

## Change an acceptance boundary

Use the [acceptance boundary](proofs-and-boundaries.md#the-acceptance-boundary) when changing a driver.
Freeze the request and independently discovered census before result collection;
reuse `ResultState.collect`, `finalize` and `AcceptedRun` instead of another transition
or success Boolean. Require accepted evidence in success renderers. Worker packets
carry raw observations and strict request identity; serialized `acceptance` fields
are never proof inputs. Keep file, fresh/incremental project, documentation, optional
graph and classification-only meanings separate.

Trace the actual theorem-to-execution path and preserve all source/admission guards.
An axiom census or theorem-statement reference alone does not establish semantic linkage.
Collection proofs establish universal finite-data guarantees; public positive/refusal/
restored controls qualify the IO boundary. Record commands, exact relevant input identity,
failed attempts and pending gates in the issue or its PR rather than inferring coverage
from a few mutations or a worker exit.

## Linter and website development

Follow the [architecture](architecture.md). A rule change updates its descriptor, actual detector, source fixtures, expected typed diagnostics and explanatory page together. Regula is agent-first: the descriptor's requirement, rationale, remedy, rewrites and checked example pair are required fields, because every finding, `lake exe regula` and the agent briefing print them; regenerate the dogfooded [skill](../../.agents/skills/regula/SKILL.md) with `lake exe regula skill > .agents/skills/regula/SKILL.md`, which acceptance checks. Follow the [attribution scope](design-influences.md): preserve actual code/license notices and cite relevant component-level design influences; examples such as CA1416, Ruff and Pyrefly are not exclusive design mandates. Never replace semantic review with docstring presence or generated-page counts.

The [website guide](website.md) specifies the pinned Verso setup, `./scripts/verify.sh site` (after both rule-example shards), publication and the rule-change workflow. The site build complements, and never partitions, [acceptance](#develop-and-verify). Review workflow must inspect rule IDs, exact scopes/modes, source ranges, versioned help routes and generated-source agreement where affected; no extra mandatory benchmark campaign is introduced.

The acceptance transport groups are maintained, capability-triggered diagnostics. Run
all affected groups when worker dispatch, codecs, joins, request reconstruction or
terminal output ownership changes. Their positive/refusal/restoration observations
qualify those IO boundaries; `collect_success_iff` and `finalize_iff` already quantify
universally over supplied finite observations. A changed worker protocol requires
public-entrypoint controls for omitted, duplicate and substituted keys, wrong modes and
snapshots, worker crash and malformed versions; changed library or overlay coverage requires a
fresh imported-client control and exact Lake inventory checks. Do not add the multi-minute
groups to every ordinary acceptance run. Existing CI builds transitively check all proof and
adapter modules; the required CI diagnostics and budgets are described above.
After fixes, reuse a diagnostic only with an explicit unchanged-relevant-input argument.

## Release

A release is one action: run the **Release** workflow on `main` (**Actions → Release → Run
workflow**, or `gh workflow run release.yml --ref main`). Its version is the Lean release in
[`lean-toolchain`](../../lean-toolchain), the Lean ecosystem's tag convention (Batteries, Aesop,
Plausible, import-graph and doc-gen4 tag `v4.34.0` for Lean 4.34.0; ProofWidgets instead numbers
its own versions, such as `v0.0.114`). There is therefore one release per
supported toolchain: move to the next Lean release before the next Regula release. The workflow
([`release.yml`](../../.github/workflows/release.yml)) runs the steps of
[`lean/Regula/Release.lean`](../../lean/Regula/Release.lean) and the checks of `ci.yml`:

1. **prepare** creates the release commit, a child of the `main` commit the workflow runs on
   that sets `Regula.installed` to the release and appends it to `Regula.releases`
   ([`RegulaCore.Edition`](../../lean/RegulaCore/Edition.lean)). GitHub creates and signs it,
   and the step refuses unless GitHub verified the signature; it then tags the commit
   `v<version>`. `main` itself never carries the release label.
2. **checks** runs `ci.yml` on the tagged commit: both acceptance steps, both rule-example shards
   and the site build, which renders the release's edition because the tag names its commit
   ([versions](website.md#versions-and-routes)). This run publishes nothing.
3. **publish** creates the GitHub release with its notes (how to require, set up and update,
   then GitHub's generated list of changes) and the edition as the asset
   `regula-site-<version>.tar.gz`, published only once the asset is attached. Immutable releases,
   a repository setting that is on, then freeze the tag and the asset.
4. **record** opens the pull request `release: record Regula v<version>`, which appends the
   release to `Regula.releases` on `main`, and starts its checks. Merging it is the release's
   one review step; every later deployment then serves `/v/<version>/` from the asset.

A failed run is re-run from the start: **prepare** resumes from an existing tag, or skips to
**record** once the release is published; **publish** replaces an unpublished draft; **record**
updates its branch to the current `main`. To start again from a newer `main` before the release
is published, delete the tag first. **record** opens its pull request only when the repository
setting *Allow GitHub Actions to create and approve pull requests* is on; otherwise it fails
after pushing the branch and dispatching its checks, and prints the link that opens the pull
request.

Adopters update by changing the tag and `lean-toolchain`, then running `lake update regula` and
`lake exe regula init` ([adoption guide](adoption.md#update-regula)).

### Reservoir

[Reservoir](https://reservoir.lean-lang.org), the Lean package index, lists a public, non-fork
GitHub repository with a root `lake-manifest.json` and an OSI-approved license that GitHub
recognizes once the repository has at least two stars, or when Reservoir's maintainers register
it. It reads the package's versions from its `v`-prefixed tags and its description, keywords,
homepage and license from the package configuration (`lake reservoir-config` prints them), and
refreshes about daily.
