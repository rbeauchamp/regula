# Work on this repository

This guide describes this repository's layout and development commands. The
[standard](../standard/README.md) defines conformance; these instructions do not
prescribe a directory layout for other Lean projects. Read the current
[repository instructions](../../AGENTS.md) before changing the project.

## Find the relevant artifact

- **Rules and teaching:** [standard chapters](../standard/README.md).
- **Contracts, examples, and checker internals:** [Lean module map](../../lean/README.md).
- **Standalone consumers:** [example projects](../../examples/README.md).

The root `lakefile.lean` sets the package source directory to `lean/`. Module
names and imports remain independent of that physical prefix: for example,
`lean/Audit/Research.lean` is still `Audit.Research`. Run Lake commands from the
repository root. Lake's elaborated library and executable inventory owns source
discovery; directory names alone do not establish audit ownership.

## Develop and verify

Provision [elan](https://github.com/leanprover/elan), the pinned toolchain,
Mathlib artifacts (`lake exe cache get`), GNU coreutils timeout, and ShellCheck
before verification. On macOS, `brew install coreutils shellcheck` supplies the
last two tools. Verification runs offline against those pinned dependencies.

```sh
lake build                         # incremental development check
./scripts/verify.sh                 # ordinary acceptance (project surfaces)
./scripts/verify.sh docs            # documentation fences, linked to that acceptance
./scripts/verify.sh diagnostics fixtures # focused diagnostic qualification
```

Ordinary acceptance builds its checker executables, type-checks the diagnostic
modules and audits the claimed Lean surfaces from fresh output. It records the content
identity of the inputs it accepted in `tmp/acceptance-link.json`. `./scripts/verify.sh docs`
then checks every Lean example under `docs/` and refuses unless its own freshly
captured inputs have the same identity. Each command has its own hard seven-minute
limit; a timeout is an incomplete run, not acceptance. Provisioning happens before
that limit. CI runs both commands, in that order in one job, after restoring or
provisioning pinned dependency caches.

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
| `self-lint` | This repository's own `lake lint` through the `regula/lint` driver ([dogfooding](lean-qualification.md#dogfooding-regula-on-itself)). |
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
claim. See the [verification sequence](../standard/9-compliance-audit.md#repository-verification-sequence)
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

## Change prose and code together

Keep a teaching example beside the prose when it helps readers. Every Lean fence
under `docs/`, including this guides directory, follows the
[checked fence convention](../standard/README.md#lean-example-convention).
Link to the actual Lean module for larger definitions and proofs; do not copy an
implementation merely to mirror the chapter structure.

For review, use the repository-local
[review toolkit](../../.agents/skills/pr-review-toolkit/SKILL.md) and the applicable
[compliance checklist](../standard/9-compliance-audit.md). Scope verification to
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
