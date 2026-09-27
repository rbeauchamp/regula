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
modules and audits the root package's claimed Lean surfaces from fresh output. It refuses a root
lock manifest that records any dependency. It records the content
identity of the inputs it accepted in `tmp/acceptance-link.json`. `./scripts/verify.sh docs`
then audits the `audit/` package's claimed surface from fresh output, checks every Lean example
under `docs/` and in the Verso standard (each elaborated in the Verso package's workspace, which
requires both packages), builds and renders the standard fresh, and refuses unless its own freshly captured inputs have the same identity. Each command has its own hard seven-minute
limit; a timeout is an incomplete run, not acceptance. Provisioning happens before
that limit, under its own 30-minute limit. CI runs both commands, in that order in one job, after restoring or
provisioning pinned dependency caches.

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

- Do not run `lake exe cache get` locally: it unpacks a full Mathlib into the copy, and
  with the link in place it fails on the read-only directory. A Lake write into the shared
  Mathlib fails the same way, which is how an unintended rebuild shows up.
- Write probes that need Mathlib as single files under `tmp/` and check them with
  `lake -d audit env lean tmp/Probe.lean`; a separate Lake project there would fetch its own
  Mathlib. A probe that needs only the checker uses `lake env lean tmp/Probe.lean`.
- Scratch directories live in `tmp/.regula-scratch/`, each beside an ownership marker
  `<name>.owner`. Those of killed runs (for example at the seven-minute limit) are reclaimed
  by the next run that creates one while no other run in the copy holds scratch; only marked
  directories there are removed. Scratch left directly under `tmp/` by earlier versions is
  never reclaimed; remove it by hand.
- GitHub Actions keeps `lake exe cache get` and its dependency cache; provisioning does
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
| `producers` | [Project producer and documentation qualification](engine-producers.md). |
| `history` | [Source-bound replacement history qualification](engine-producers.md). |
| `self-lint` | This repository's own `lake lint` through the `regula/lint` driver, in the root and `audit/` packages ([dogfooding](lean-qualification.md#dogfooding-regula-on-itself)). |
| `self-audit` | Operational self-audit of the excluded `Regula` library ([dogfooding](lean-qualification.md#dogfooding-regula-on-itself)). |
| `rule-examples`, `rule-examples 1/2`, `rule-examples 2/2` | [Source-owned corpus and diagnostic demonstrations](rule-examples.md); a shard runs half of the rules. |

The `environments` clean-checkout `freshChecker` control claims two import-free modules
written into a copy with no build directory. It establishes that `freshChecker` builds its
claimed targets itself, checks each maximal root, and reports accepted coverage of exactly
those modules. The control does not run `leanchecker --fresh` over this repository's claimed
graph. That replay rechecks Init, Lean and Mathlib once per root, and took more than 360 s.
It is the optional serialized-graph claim (§8.9), which ordinary acceptance does not include
and this repository does not make. `./scripts/verify.sh serialized-graph` remains its
command. Ordinary acceptance's isolated clean build still covers the real claimed surface.

Omitting `PARTITION` requests the `checkerSelftest` campaign; the `producers`, `history` and
`rule-examples` campaigns remain separate explicit selections. Each invocation uses the
same deadline; choose affected checks rather than treating every campaign as a routine
prerequisite. Run `./scripts/verify.sh serialized-graph` only for the separate serialized-graph
claim. See the [verification sequence](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#repository-verification-sequence)
for evidence requirements. Diagnostics do not replace a failed acceptance run.

The [diagnostics workflow](../../.github/workflows/diagnostics.yml) runs `producers` and
`history` as parallel jobs, each with its own hard 420-second limit, when the checker, rules,
rule examples, Lake configuration or manifests change, on every push to `main`, and nightly;
it also runs both `rule-examples` shards nightly. [CI](../../.github/workflows/ci.yml) runs both
shards on every pull request and push to `main`, where they feed `./scripts/verify.sh site`
([website guide](website.md)).
The [lint-driver workflow](../../.github/workflows/lint-driver.yml) runs `lint-driver`
under the same limit when the `lake lint` driver or anything it imports changes, or the
adopter fixtures in `examples/lake-lint-toml` and `examples/build-lint` change, on every push
to `main`, and nightly. These campaigns are capability-triggered diagnostics (standard
§8.8), not a partition of ordinary acceptance.
The [dogfood workflow](../../.github/workflows/dogfood.yml) runs `self-lint` and `self-audit`
as parallel jobs under the same limit, and the opt-in
[intent screen](intent-screening.md#dogfood-screen) as a third job, when Lean sources, Lake
configuration, manifests or the screen configuration change, on every push to `main`, and
nightly. They are not part of acceptance.


## Implementation and qualification layout

Project-owned implementation is Lean 4; `scripts/verify.sh` is the minimal acceptance
shell boundary. Additional shell scripts require explicit approval under `AGENTS.md`.
See [Lean qualification](lean-qualification.md) for the proof/IO split and why these
integration controls are still necessary. Configuration and external toolchains are
not claimed as formally verified Lean implementations.

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
[compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/). Scope verification to
the affected claims, retain required checks, and distinguish historical results
from evidence for the current revision.

## Change an acceptance boundary

Use the [success-owner and API map](policy-acceptance.md) when changing a driver.
Freeze the request and independently discovered census before result collection;
reuse `ResultState.collect`, `finalize` and `AcceptedRun` instead of another transition
or success Boolean. Require accepted evidence in success renderers. Worker packets
carry raw observations and strict request identity; serialized `acceptance` fields
are never proof inputs. Keep file, fresh/incremental project, documentation, optional
graph and classification-only meanings separate. Con-leche's complete indexed assembly
is credited at this boundary; its proofs are not imported.

Trace the actual theorem-to-execution path and preserve all source/admission guards.
An axiom census or theorem-statement reference alone does not establish semantic linkage.
Collection proofs establish universal finite-data guarantees; public positive/refusal/
restored controls qualify the IO boundary. Record commands, exact relevant input identity,
failed attempts and pending gates in the issue or its PR rather than inferring coverage
from a few mutations or a worker exit.

## Linter and website development

Follow the [architecture](linter-architecture.md), [comparative design decisions](ecosystem-design.md), [developer experience](developer-experience.md) and [coverage map](rule-coverage.md). A rule change updates its descriptor, actual detector, source fixtures, expected typed diagnostics and explanatory page together. Regula is agent-first: the descriptor's requirement, rationale, remedy, rewrites and checked example pair are required fields, because every finding, `lake exe regula` and the agent briefing print them; regenerate the dogfooded [skill](../../.agents/skills/regula/SKILL.md) with `lake exe regula skill > .agents/skills/regula/SKILL.md`, which acceptance checks. Follow the [attribution scope](design-influences.md): preserve actual code/license notices and cite relevant component-level design influences; examples such as CA1416, Ruff and Pyrefly are not exclusive design mandates. Never replace semantic review with docstring presence or generated-page counts.

The [website guide](website.md) specifies the pinned Verso setup, `./scripts/verify.sh site` (after both rule-example shards), publication and the rule-change workflow. The site build complements, and never partitions, the unchanged 420-second acceptance commands. Review workflow must inspect rule IDs, exact scopes/modes, source ranges, versioned help routes and generated-source agreement where affected; no extra mandatory benchmark campaign is introduced.

The acceptance transport groups are maintained, capability-triggered diagnostics. Run
all affected groups when worker dispatch, codecs, joins, request reconstruction or
terminal output ownership changes. Their positive/refusal/restoration observations
qualify those IO boundaries; `collect_success_iff` and `finalize_iff` already quantify
universally over supplied finite observations. Do not add the multi-minute groups to
every ordinary acceptance run. Existing CI builds transitively check all proof and
adapter modules; the required CI diagnostics and budgets are described above.
After fixes, reuse a diagnostic only with an explicit unchanged-relevant-input argument.
