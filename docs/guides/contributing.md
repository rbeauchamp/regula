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
- **Planned work:** the [roadmap](https://github.com/users/rbeauchamp/projects/8); each item needs a design pass before implementation.

The root `lakefile.lean` sets the package source directory to `lean/`. Module
names and imports remain independent of that physical prefix: for example,
`lean/AuditApp/Limiter.lean` is still `AuditApp.Limiter`. That root `regula` package, the one
adopters require, requires nothing beyond the Lean toolchain. The standard's example library is
the `regula_audit` package in [`audit/`](../../audit/lakefile.lean) (`audit/Audit/Research.lean`
is `Audit.Research`), which requires the root package by relative path, as an adopter would, and
nothing else. Everything that imports Mathlib is the `regula_mathlib` package in
[`integration/mathlib/`](../../integration/mathlib/lakefile.lean), which only the
[Mathlib integration check](#mathlib-integration-check) builds. The `regula_markdown` package
in [`markdown/`](../../markdown/lakefile.toml) has the md4c reader and the executable of the
[checks of Markdown documents](#markdown-documents). It requires the root package and MD4Lean
only. Run Lake commands
from the repository root, and the `audit/` package's in `audit/` (or with `lake -d audit`).
Lake's elaborated library and executable inventory owns source discovery; directory names alone
do not establish audit ownership.

## Develop and verify

Provision [elan](https://github.com/leanprover/elan), the pinned toolchain
and the website package's pinned Verso
(`lean --run lean/RegulaProvision.lean verso`). Every copy also needs GNU coreutils timeout and ShellCheck
before verification. On macOS, `brew install coreutils shellcheck` supplies the
last two tools. Verification runs offline against those pinned dependencies. None of the
commands below downloads, caches, imports or builds Mathlib; the
[Mathlib integration check](#mathlib-integration-check) is a separate command with its own setup.

```sh
lake build                         # incremental development check (the regula package)
lake -d audit build                # the standard's example library
./scripts/verify.sh                 # ordinary acceptance (project surfaces)
./scripts/verify.sh docs            # checks of tracked Markdown documents, audit/ package, documentation examples and the Verso standard, linked to that acceptance
./scripts/verify.sh diagnostics fixtures # focused diagnostic qualification
```

Ordinary acceptance builds its checker executables, type-checks the diagnostic
modules and audits the root package's claimed Lean surfaces from fresh output. It also runs the
registry and native qualification controls (`qualify combined`, which runs those of
`qualify registry` and then those of `qualify native` beside `qualify unique-constants`).
It refuses a root lock manifest that records any dependency. It records the content
identity of the inputs it accepted in `tmp/acceptance-link.json`. `./scripts/verify.sh docs`
then refuses a rule ID in the prose of a tracked Markdown document that is not a link to its rule page ([rule IDs in documentation](#rule-ids-in-documentation)), refuses a link of the root `README.md` to the rule-reference site that is not a stable address ([links of the root README](#links-of-the-root-readme)), refuses a root `README.md` or adoption guide that does not open with the summary of Regula ([opening of the root README](#opening-of-the-root-readme)), refuses a root `README.md` if its example does not show its module and what Lean and `axiomGate --file` give for it ([example of the root README](#the-example-of-the-root-readme)), audits the `audit/` package's claimed surface from fresh output, checks every Lean example
under `docs/` and in the Verso standard (each elaborated in the Verso package's workspace, which
requires both packages), builds the standard in its own copy and renders it, refuses such a rule ID in the prose of the rendered standard, and refuses unless its own freshly captured inputs have the same identity. That command also operates the controls of the [checks of the prose](#the-prose-of-markdown-documents) and of the [check of the vocabulary](#the-vocabulary-of-the-project), and then does those checks. `DOC-*` rows need both commands. Each
acceptance step performs Lake-semantic discovery and a clean, warning-free build before
inspection, so a redundant preliminary clean build is unnecessary; `lake build` remains the
development command. Each command has its own hard seven-minute
limit; a timeout is an incomplete run, not acceptance. `./scripts/provision.sh` runs before
that limit, under its own 30-minute limit; it validates the released compiler and acquires no dependencies. CI runs both commands, in that order in one job, after restoring or
provisioning the pinned Verso artifacts.

Ordinary acceptance puts the accepted record at `tmp/acceptance-link.json` only after each of
its commands ended with exit status 0. Its driver first makes one copy of the checkout in
`.lake/regula-scratch/`. The build, the registry checks and the qualification controls operate
in that copy. The gate that the copy built audits the build output of the copy. Thus the step
builds the claimed libraries one time.

In the copy, the driver first builds the claimed targets and the gate. Then the gate runs beside
the other three commands, which run at low priority.

`qualify unique-constants` refuses a constant that two modules of one claimed environment
declare, if one of them is a module of the root package. Lean makes an equation lemma in the first
module that unfolds its definition. If two modules that do not import each other each make it, the
audit replays a module again in each environment that loads the two.

If the step passed and the checkout has no build output, the driver moves the build output of
the copy to `.lake/build` of the checkout. After a step that failed, a checkout with no build
output stays without it. If the checkout has build output, the driver does not change it.
The driver removes the copy at the end of the step. A killed step leaves its copy. The next
first step or the next run of the checker removes it.

After it moves the build output, the driver adds digests to the accepted record. These are the
SHA-256 of each file of the copy and of that build output. The fence audit of
`./scripts/verify.sh docs` then puts part of that build output in its own copy. That part is the
files of the modules that its claimed build compiles. It does this only if each digest is equal to the digest of
the file that it reads.

If a digest is not there or is different, the fence audit builds the claimed libraries in a
copy with no build output. Thus the libraries that the fences read were compiled from equal files.
The first step compiled them in a copy with no earlier build output, or this run compiled them. The
output of the fence audit tells if it placed the first step's build. It does not tell which build
compiled each library.

The fence audit checks the record first, before it builds. Thus without an accepted record it
refuses immediately and builds nothing.

Two ordinary attempts at the same time in one checkout are not a supported use.

Each line that starts with `verification:` is
a progress line of the driver of `./scripts/verify.sh`. Such a line gives the start of a command,
the end of a command, or a different event of the driver
([proofs and boundaries](proofs-and-boundaries.md#the-acceptance-boundary)).

The applicable command evidence is required but does not complete the standard's checklist:
theorem, type and prose rows still require semantic review. A conformance record for this
repository states the Lean version, the exact dependency source state (including Mathlib when
present), the claimed Lake modules, declaration coverage and exact axiom results, execution
boundaries, the applicable fence and checker-qualification results, and any failures or missing
evidence. A required check that was skipped leaves its affected row or optional claim
`INCOMPLETE`; it cannot support conformance. No CI, publication, merge, actual VS Code
interaction, or full repository semantic conformance is implied by local acceptance or scoped
integration results.

### Mathlib integration check

The `regula` package, the standard's examples and the site use no Mathlib, but Regula supports
projects that do. The `regula_mathlib` package in
[`integration/mathlib/`](../../integration/mathlib/lakefile.lean) is a Mathlib adopter of the
checker, required by relative path exactly as a Mathlib project would, and its `MathlibAudit`
library is the claimed surface on which that support is checked:

| Mathlib-specific behaviour | Where it is exercised |
| --- | --- |
| A surface that imports Mathlib must enable Mathlib's standard linter set with the §6.7 exclusions ([RG2006]) | `mathlibLinters` in the package's `lakefile.lean`, on the `MathlibAudit` target |
| Warning-free elaboration under that linter set ([RG2003]) | Every `MathlibAudit` module |
| Exact foundation labels through Mathlib dependencies, including `Classical.choice` reached through `ℝ` | `MathlibAudit.DocPrelude`, `MathlibAudit.DocClaims`, `MathlibAudit.Models` |
| Mathlib syntax, tactics and canonical structures in claimed declarations (`Type*`, `ring`, `norm_num`, `LinearOrder.lift'`, `unitInterval`, `IsOrderedAddMonoid`, `MetricSpace`) | `MathlibAudit.Refinement`, `MathlibAudit.Economy`, `MathlibAudit.DocClaims`, `MathlibAudit.Models` |
| Material-claim registration and its docstring rules on a Mathlib surface ([RG5002], [RG5003]) | `MathlibAudit.Refinement` |
| Statements about Mathlib's own definitions (`Nat.Perfect`, `Relation.ReflTransGen`, `Even`) | `MathlibAudit.Research`, `MathlibAudit.Refinement`, `MathlibAudit.Basic` |
| `lake lint` through the `regula/lint` driver in a Mathlib project | The package's `lintDriver` |

These modules are the Mathlib forms of lessons whose Lean/Std forms the standard displays. The
standard links five of them where it teaches the lesson: `MathlibAudit.Models`,
`MathlibAudit.DocClaims`, `MathlibAudit.Economy`, `MathlibAudit.Refinement` and
`MathlibAudit.Research`. It has no link to `MathlibAudit.Basic` (small positive controls) or
`MathlibAudit.DocPrelude` (the real-valued glossary types that `MathlibAudit.DocClaims` imports).
Run the check with its own setup:

```sh
lean --run lean/RegulaProvision.lean mathlib   # setup: the shared, read-only Mathlib (network on first use)
./scripts/verify.sh mathlib                    # the check, under its own seven-minute limit
```

`./scripts/verify.sh mathlib` first refuses a copy the check does not apply to, or whose Mathlib is
not provisioned (`lean --run lean/RegulaProvision.lean mathlib-applies --require`), then runs
`lake exe axiomGate` in the package, the fresh acceptance of its
claimed surface against its own `foundation_manifest.json`, and then `lake lint` there. It is never
part of acceptance and no acceptance step, diagnostic or site build depends on it. In CI the
`mathlib integration` job of [`ci.yml`](../../.github/workflows/ci.yml) runs it on every pull
request and on `main`; it is the only job that restores or provisions Mathlib.

Its result is about the Lean toolchain in `integration/mathlib/lean-toolchain` and the Mathlib
revision pinned in `integration/mathlib/lake-manifest.json`, and about nothing else. The proved decision
`RegulaProvision.mathlibApplies` (`mathlibApplies_iff`) accepts exactly when the root and
integration toolchain selectors are equal. A mismatch fails setup and the integration job;
CI always schedules that job on ordinary pull requests and `main`.

### Share one Mathlib across local copies

Every local copy uses one unpacked Mathlib per pinned revision and exact released compiler instead of
its own. The pin is the `mathlib` entry of `integration/mathlib/lake-manifest.json`; the root,
`audit/` and `website/` packages pin no Mathlib.
[`lean/RegulaProvision.lean`](../../lean/RegulaProvision.lean), run with the `mathlib` argument, unpacks Mathlib's
archive cache (`~/.cache/mathlib`) once into
`~/.cache/mathlib-packages/<mathlib-rev>-lean-<toolchain-commit>/` (under
`$XDG_CACHE_HOME` instead of `~/.cache` when that is set), compiles every
module's native object there (executables that import Mathlib link them), makes it
read-only, and links the copy's `integration/mathlib/.lake/packages/mathlib` to it. The rest of Mathlib's closure
(Batteries, Aesop, ...) becomes writable copy-on-write clones, since executables compile
native objects into them. The integration package keeps its own packages directory, so its pins
are independent of the website's; the example adopters under `examples/` require only `regula` and
need no packages directory. Run `lean --run lean/RegulaProvision.lean mathlib` in a copy before the first Lake command in
`integration/mathlib/`, which would otherwise clone and build a per-copy Mathlib. `./scripts/provision.sh`,
which `./scripts/verify.sh` runs before its deadline, acquires no Mathlib. The first run for a new pin needs the network; later copies reuse the
sealed artifacts. The receipt `regula-provisioned.json` in the shared directory records its
revisions, compiler and artifact mode. A clean per-copy Mathlib checkout is replaced by the link; one with local
changes, stashes or commits that no remote-tracking branch holds is refused. Before acquiring a
shared store or changing registrations and packages, provisioning requires each existing package
link to identify a stable store with an admissible receipt. Source-origin, unknown and dangling
links are preserved and refused; their disposition remains manual.

Each shared directory's registry `<dir>.copies.json` beside it records the copies provisioned
to link it; a copy is registered before it links. Every provisioning run removes the shared
directories of other stable pins and toolchains that no
registered copy still links, and drops the
registrations of copies that are gone or link elsewhere. Only a directory whose receipt names
it with a decodable stable receipt is removed; this retention step leaves staging directories,
source stores and anything else there as they are. Before creating a missing stable store,
provisioning separately removes abandoned staging directories with that store's exact stable-key
prefix. A stable-store removal a killed run began is
finished by the next run. A copy left with a dangling link requires manual disposition before
provisioning can continue. One lock,
`~/.cache/mathlib-packages/regula-provision.lock`, orders creation, registration and removal,
so copies wait while another copy creates a new pin.

A copy provisioned before the Mathlib integration package existed linked Mathlib at the root
`.lake/packages/mathlib`, which no package uses any more. Its next
`lean --run lean/RegulaProvision.lean mathlib` removes that link when it is a symbolic link that
a shared directory's registry records and that still resolves to that directory's Mathlib
(`RegulaProvision.retires`, `retires_iff`), and drops its registration, so the link no longer keeps
a shared directory. Nothing else is removed from the copy: a real directory there, an
unregistered link and a dangling one stay as they are. A copy that will not provision Mathlib
again keeps the link, and the shared directory it names, until the link is removed by hand
(`rm .lake/packages/mathlib` removes only the link). The same earlier provisioning left writable
clones of the rest of Mathlib's closure in the root `.lake/packages`: `batteries`, `aesop`, `Qq`,
`proofwidgets`, `importGraph` and `LeanSearchClient`. No manifest names them there now and
provisioning never deletes them; after checking that they hold no work of yours, remove them once
by hand:

```sh
rm -rf .lake/packages/{batteries,aesop,Qq,proofwidgets,importGraph,LeanSearchClient}
```

- Do not run Mathlib's `cache get` locally (`lake exe cache get` in `integration/mathlib/`): it unpacks a full
  Mathlib into the copy, and with the link in place it fails on the read-only directory. A Lake write into the shared
  Mathlib fails the same way, which is how an unintended rebuild shows up.
- Write probes that need Mathlib as single files under `tmp/` and check them with
  `lake -d integration/mathlib env lean tmp/Probe.lean`; a separate Lake project there would fetch its own
  Mathlib. A probe that needs only the checker uses `lake env lean tmp/Probe.lean`.
- Scratch directories live in `.lake/regula-scratch/`, each beside an ownership marker
  `<name>.owner`. Those of killed runs (for example at the seven-minute limit) are reclaimed
  by the next run that creates one while no other run in the copy holds scratch; only marked
  directories there are removed. Scratch outside `.lake/regula-scratch/` is never reclaimed;
  remove it by hand.
- GitHub Actions fetches Mathlib's published artifacts into the integration job's writable `integration/mathlib/.lake/packages`, where later builds compile the native objects they link. Only a local read-only shared directory needs those objects built in advance. CI cache keys include the platform, exact released compiler identity and pinned manifests. A shared directory is never modified, only removed whole.

Existing stable shared-store receipts and keys remain compatible. A receipt whose origin is `source` fails decoding; its store is neither reused nor pruned. Removed source-mode and snapshot configuration files are refused during setup. Provisioning does not migrate or delete source stores.

Run `lean --run lean/RegulaProvision.lean verso` to provision the pinned Verso. The default provisioning command validates the released compiler and acquires no dependencies. Verification invokes commands directly with their declared arguments and working directories. The existing setup and acceptance deadlines still apply. Git, package build hooks, compiler binaries, cache storage, process execution and filesystem operations remain trusted boundaries.

[AGENTS.md](../../AGENTS.md#changes-and-verification) owns verification and merge policy.
The [CI workflow](../../.github/workflows/ci.yml) defines runner and cache configuration.
Reuse evidence when its relevant inputs and claims remain unchanged; instruction-only
changes need scoped review rather than another Lean run.

### Choose focused diagnostics

Use `./scripts/verify.sh diagnostics PARTITION` when changes affect the corresponding
checker behavior:

| Partition | Focus |
| --- | --- |
| `fixtures`, `fixtures 1/5` to `fixtures 5/5` | Positive controls and intentionally invalid Lean declarations, then the Markdown scanner controls and the in-process fence corpus. A shard checks one fixture in five, by its position in module-name order, not the file order of `fixtures.json`. The last shard also runs the scanner controls and the fence corpus. |
| `structural`, `structural 1/5` to `structural 5/5` | Surface discovery, ownership, contamination, required application contracts, decision contracts that one surface counts for a different surface, and admission reuse between environments; a shard runs part of the controls. The shards together run all of them but the self-hosted identity. Shards 1/5 and 5/5 write its two digests, `tmp/self-hosted-digest/positive.sha256` and `restored.sha256`. Only the CI `diagnostics` gate compares them, so a local claim rests on the unsharded `structural` run or a comparison of the two files. |
| `execution`, `execution 1/4` to `execution 4/4` | Execution evidence: each compiler-path mutation and correspondence control with its positive and fresh restoration; a shard runs part of the controls, and the shards together run all of them. |
| `cli`, `cli 1/6` to `cli 6/6` | Command-line behavior and diagnostics: each fixture through a real `axiomGate --file` run, then the source-attribution controls. A shard checks one fixture in six, by its position in module-name order. The last shard also runs the source-attribution controls. |
| `environments`, `environments 1/6` to `environments 6/6` | Isolated environments, documentation scanning, and external adopters. Shard 1/6 runs the public fence corpus. Shard 2/6 runs the `lakefile.toml` adopter, and 3/6 runs the `lakefile.lean` and relative-path adopters. Shard 4/6 runs the clean-checkout documentation fences and `freshChecker`. Shard 5/6 runs the clean-checkout `--file` control, and 6/6 runs the public surface. |
| `build-policy`, `build-policy 1/3` to `build-policy 3/3` | Enforcement through the example's ordinary Lake build. A shard runs one mutation case in three. The last shard also runs the disabled-policy control. |
| `lint-driver`, `lint-driver 1/5` to `lint-driver 5/5` | `lake lint` dispatch and exit classes in both shipped adopters, and the cold compiler guard of `lakefile.lean`: refusal of an inherited `LEAN_SYSROOT` child that fails and of one that succeeds without reporting the running compiler's identity, then a restored load. In a plain workspace the driver keeps the audit-build marker without `REGULA_ORDINARY_LAKEFILES=1`, and with it omits the marker, reports it and reuses the ordinary build. Under the assertion, an import of `Regula.Linter` keeps the marker, and the driver reports the reason. Decision probes of the guard load a changed adopter in the process and check its decision and reason without an audit. A custom target, a library in `needs`, a facet of Lake declared again and a library field outside the list keep the marker. So do a different `nativeFacets`, a lakefile declaration, a theorem that equates two functions, a TOML filter other than `"*"` and an import of `Regula.Linter`. An input file in `needs` and the filter `"*"` keep the plain shape. Lake's artifact cache is on in a private directory, and a claimed module warns. Then two identical `--fresh` runs and an incremental audit of the module that Lake restored from the cache each report [RG2003]. The same holds when only a path dependency turns the cache on in its own configuration, and its module warns. It also holds when the claimed library builds no module by default, and the module was elaborated or restored by an ordinary build. The claimed library can also have the name `foo/bar`, and Lake target syntax reads its spelling `«foo/bar»` as a library of a dependency. Then an incremental audit also reports it. Without the warning, a fresh run is accepted. An adopter's path dependency is replayed in its Git work tree, also with `--fresh`, and trusted and named in a work tree of its own. An adopter in the checker's own work tree owns `regula` and imports `Regula.Linter`. Its fresh audit owns no `Regula` or `RegulaPolicy` module of `regula` and accepts the adopter. On a project from `lake new` in each format, `regula init` writes the glob of its library, and a second run writes nothing. In the `lakefile.toml` project, `lake lint` then reports the missing docstrings, and it accepts the project when they are written. A shard runs part of the control groups, and the five shards together run all of them. |
| `producers` | [Project producer and documentation qualification](proofs-and-boundaries.md#producers). |
| `history` | [Source-bound replacement history qualification](proofs-and-boundaries.md#producers). |
| `self-lint` | This repository's own `REGULA_ORDINARY_LAKEFILES=1 lake lint` through the `regula/lint` driver, in the root and `audit/` packages ([repository conformance](#repository-conformance)). |
| `self-lint-default` | The root package's `lake lint` without `REGULA_ORDINARY_LAKEFILES`, so with the audit-build marker that an adopter gets by default ([repository conformance](#repository-conformance)). |
| `self-audit`, `self-audit 1/4` to `self-audit 4/4` | Operational self-audit of the excluded `Regula` library, and the check for one-sided `Json` comparisons in each library except `Fixtures` ([repository conformance](#repository-conformance)). A shard audits a quarter of the modules, and the four shards together audit all of them. |
| `rule-examples`, `rule-examples 1/3` to `rule-examples 3/3` | [Source-owned corpus and diagnostic demonstrations](architecture.md#rule-examples); a shard runs a third of the rules. |
| `input-inventory` | Root additions and Markdown edits or removals during the prerequisite build of the checker, an actual new-module build and restored fresh controls (`qualify input-inventory`). |
| `environment-census` | This repository's claimed environments and their mutations (`qualify environments`). |
| `snapshot-history` | Fresh, incremental and build-lint history refusal and restoration over the dependency snapshot (`qualify acceptance-snapshots history`). |
| `acceptance-controls` | Fence-compilation packet mutations with positive restoration, and the `dependencies` and `git-status` snapshot groups. Also timeout-selection and spawn failures, and the preparation of a shared producer slot. The commands are `qualify acceptance fences`, `acceptance-snapshots dependencies` and `git-status`, `receipt-boundaries` and `prep-measure`. |
| `documentation-controls` | The two documentation commands keep their pre-build dependency observations. An initial configuration IO failure goes through the project and file result protocols. The commands are `qualify documentation-dependencies` and `configuration-capture`. |
| `focused-controls` | The self-test's focused native-adopter, combined-snapshot and policy-transport controls (`checkerSelftest --native-adopter-only`, `--combined-snapshot-only`, `--policy-transport-only`). |
| `policy-domain` | The self-test's focused policy-domain controls, the policy transport and the public paths (`checkerSelftest --policy-domain-only`). |

The `environments` clean-checkout `freshChecker` control claims two import-free modules
written into a copy with no build directory. It establishes that `freshChecker` builds its
claimed targets itself, checks each maximal root, and reports accepted coverage of exactly
those modules. The control does not run `leanchecker --fresh` over this repository's claimed
graph. That replay rechecks Init and Lean once per root; with the earlier Mathlib examples in the
claimed graph it took more than 360 s.
It is the optional serialized-graph claim (§7.9), which ordinary acceptance does not include
and this repository does not make. `./scripts/verify.sh serialized-graph` remains its
command. Ordinary acceptance's isolated clean build still covers the real claimed surface.

The copy of that control also has a `leanchecker` program in the binary directory of its root
package. This program is a link to the toolchain's `lean`, and `lake env` puts that directory first
on `PATH`. The control first runs it as a `leanchecker` of each root and requires each run to fail.
It accepts a run only if the check of each root passed, thus an accepted run did not start that
program.

`freshChecker` starts `lake` and `leanchecker` by their paths in the installation directory of the
toolchain (`Regula.Toolchain.program`). The `lean` of that directory must give the version and the
commit of the supported compiler.

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

The [diagnostics workflow](../../.github/workflows/diagnostics.yml) runs on every pull request,
every push to `main`, nightly and on dispatch. Its first job, `applies`
(`lean --run lean/Regula/DiagnosticsGate.lean applies`), provisions the pinned release and
decides which jobs apply. It runs the
invocations that `Regula.DiagnosticsGate.campaigns` lists, and `applies` writes them for the matrix
of the `campaign` job. These are `producers`, `history`, the shards of the structural, execution and
lint-driver partitions of the self-test, and four groups of qualification controls. The other
partitions and groups are too long for a job, and the table of
[campaigns no workflow runs](#campaigns-no-workflow-runs) names them. They run as parallel jobs, each with its own hard 420-second limit, on a pull
request exactly when it changes one of the paths `Regula.DiagnosticsGate.inputs` lists (the checker, rules, rule examples, the
adopter fixtures in `examples/lake-lint-toml` and `examples/build-lint`, the application and
fixture sources the structural and execution controls mutate, Lake configuration, manifests, or
the compiler and dependency setup: the provisioning program and its decision contracts, the
provisioning action, the verification scripts and the configuration they read before a campaign),
and on every other run; it also runs the three `rule-examples` shards nightly. Its last job,
`diagnostics`, is a required check of the ruleset of `main`. It reports on every pull request and
passes exactly when `applies` succeeded and each partition job passed and applies, or was
skipped and does not apply, so a pull request merges only once every one of these jobs that
applies to it has passed on its head commit, and a failed, cancelled or timed-out one refuses the
merge. A pull request that changes none of the listed paths, such as one that changes only
documentation, passes it without running a campaign
([proofs and boundaries](proofs-and-boundaries.md#the-diagnostics-gate)).
[CI](../../.github/workflows/ci.yml) runs the three shards on every pull request and push to `main`,
where they feed `./scripts/verify.sh site` ([website guide](website.md)). These campaigns are
capability-triggered diagnostics (standard §7.8), not a partition of ordinary acceptance.
The [dogfood workflow](../../.github/workflows/dogfood.yml) runs `self-lint` and the four shards of
`self-audit` as parallel jobs under the same limit when Lean sources, Lake configuration, manifests or
that compiler and dependency setup change, on every push to `main`, and nightly. They are not part of acceptance.
None of these jobs is a required check of the ruleset of `main`. The workflow runs on a pull request only when those paths change. A required check from it does not report on a different pull request, so that pull request cannot merge.
It runs `self-lint-default` only nightly and on dispatch, as one more job under the same limit. It is not a check of a pull request or of a push.

When the campaigns apply, the `diagnostics` job also compares two digests. The shard
`structural 1/5` uploads the SHA-256 digest of the fresh input that the self-hosted positive's
fresh gate accepted. The shard `structural 5/5` uploads that of its restored self-hosted copy.
The gate refuses unless the two are present, well-formed and equal.

### Campaigns no workflow runs

The inventory `Regula.Campaigns` lists each invocation of `./scripts/verify.sh`, each form of a
`qualify` selection and each campaign of `checkerSelftest`. Each one runs in a workflow job, or
the table below gives the reason that no job runs it. The inventory also states which jobs run
which invocations. The kernel checks its theorem `covered_all` when the module builds. A campaign
that runs has no reason. Each other campaign has a reason, and the campaigns that the reason
names run.

Two modules tie the inventory to the programs with theorems. `Regula.Campaigns.Verification`
relates it to the modes and commands of the verification driver. `Regula.Campaigns.Diagnostics`
relates it to the matrix of the diagnostics workflow. The first acceptance step builds the two
modules.

`Regula.RegistryChecks` requires this table without a change. It also reads the `verify.sh` steps
of each job from its workflow file, with each matrix value in place. It requires them to be the
invocations that the inventory gives.

Two statements are readings, not theorems. The first is that GitHub runs a job's steps when its
triggers and `if:` say. The second is that the campaigns a reason names have the controls of the
campaign that does not run. For a reason that names part of them, its text names the rest.

| Campaign | Why no workflow job runs it |
| --- | --- |
| `./scripts/verify.sh serialized-graph` | The optional serialized-graph claim (§7.9), which this repository does not make. |
| `./scripts/verify.sh diagnostics` | The shards of the structural, execution and lint-driver partitions run. The shards of the fixtures, cli, environments and build-policy partitions are too long for a job. The structural shards do not compare the self-hosted fresh inputs. Shards 1/5 and 5/5 write their digests, and the `diagnostics` gate compares them. |
| `./scripts/verify.sh diagnostics fixtures` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics structural` | Its 5 shards run. Together they run each of its controls one time, but for the comparison of the self-hosted fresh inputs. Shards 1/5 and 5/5 write the digests of those inputs, and the `diagnostics` gate compares them. |
| `./scripts/verify.sh diagnostics execution` | Its 4 shards run. Together they run each of its controls one time. |
| `./scripts/verify.sh diagnostics cli` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics build-policy` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics lint-driver` | Its 5 shards run. Together they run each of its controls one time. |
| `./scripts/verify.sh diagnostics self-audit` | Its 4 shards run. Together they audit each module one time. |
| `./scripts/verify.sh diagnostics rule-examples` | Its 3 shards run. Together they run the records of each rule one time. |
| `./scripts/verify.sh diagnostics fixtures 1/5` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics fixtures 2/5` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics fixtures 3/5` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics fixtures 4/5` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics fixtures 5/5` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics cli 1/6` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics cli 2/6` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics cli 3/6` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics cli 4/6` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics cli 5/6` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics cli 6/6` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments 1/6` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments 2/6` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments 3/6` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments 4/6` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments 5/6` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environments 6/6` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics build-policy 1/3` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics build-policy 2/3` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics build-policy 3/3` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `./scripts/verify.sh diagnostics environment-census` | Too long for a job. Its check took 172 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `./scripts/verify.sh diagnostics snapshot-history` | Too long for a job. Its check took 104 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `./scripts/verify.sh diagnostics policy-domain` | Too long for a job. Its check took 158 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify registry` | Its controls run in `lake exe qualify combined`: `combined` runs `registry` first. |
| `lake exe qualify native` | Its controls run in `lake exe qualify combined`: `combined` runs `native` second. |
| `lake exe qualify unique-constants` | Its controls run in `lake exe qualify combined`: `combined` runs `unique-constants` beside `native`. |
| `lake exe qualify native-launcher` | Too long for a job. Its check took 92 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify rule-examples --evidence PATH` | Its controls run in `lake exe qualify rule-examples --evidence PATH --shard K/N`: the shards together run the whole corpus. |
| `lake exe qualify rule-examples --evidence PATH --rules RULE ...` | Its controls run in `lake exe qualify rule-examples --evidence PATH --shard K/N`: each rule's records are in one shard. |
| `lake exe qualify producers --evidence PATH` | Its controls run in `lake exe qualify producers`: the same campaign, which also writes its evidence. |
| `lake exe qualify producers-combined` | `producers` and `history` run, each in a job of its own. |
| `lake exe qualify self-audit` | Its controls run in `lake exe qualify self-audit --shard K/4`: the four shards together audit all modules. |
| `lake exe qualify self-audit-module MODULE SOURCE` | An internal entry point that `lake exe qualify self-audit --shard K/4` starts. |
| `lake exe qualify self-audit-json-module MODULE` | An internal entry point that `lake exe qualify self-audit --shard K/4` starts. |
| `lake exe qualify environments --evidence PATH` | Too long for a job. Its check took 172 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify acceptance-snapshots history` | Too long for a job. Its check took 104 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify acceptance-snapshots all` | Its groups `dependencies` and `git-status` run. Its group `history` is too long for a job. |
| `lake exe qualify closure-evidence` | Too long for a job. Its check took 105 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify fence-evidence` | Too long for a job. Its check took 140 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify frozen-exits` | Too long for a job. Its check took 240 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify documentation-source` | Too long for a job. Its check took 182 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe qualify documentation-source --source-read-only` | Too long for a job. Its check took 202 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe checkerSelftest --forced-collector-only` | Too long for a job. Its check took 336 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe checkerSelftest --policy-domain-only` | Too long for a job. Its check took 158 s, and a check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide it into shards. |
| `lake exe checkerSelftest --fences-only` | The focused controls include the combined snapshot. The in-process and public fence corpora are controls of the fixtures and environments partitions. The shards of those partitions are too long for a job. |
| `lake exe checkerSelftest --build-lint-only` | Its controls are those of the build-policy partition. The shards of that partition are too long for a job. |
| `lake exe checkerSelftest --compiler-paths-only` | The execution shards run its compiler-path mutations. |
| `lake exe checkerSelftest --transcript-worker MODULE SOURCE REJECT OUT` | An internal entry point that the fixtures shards start, which are too long for a job. |
| `lake exe checkerSelftest --jobs 4` | The shards of the structural and execution partitions run. It also runs the controls of the fixtures and cli partitions, and their shards are too long for a job. The structural shards do not compare the self-hosted fresh inputs. Shards 1/5 and 5/5 write their digests, and the `diagnostics` gate compares them. |
| `lake exe checkerSelftest --structural-only --jobs 4` | The shards of the structural and execution partitions run. The structural shards do not compare the self-hosted fresh inputs. Shards 1/5 and 5/5 write their digests, and the `diagnostics` gate compares them. |
| `lake exe checkerSelftest --build-bound --jobs 4` | The shards of the structural, execution and lint-driver partitions run. The shards of the fixtures, cli, environments and build-policy partitions are too long for a job. The structural shards do not compare the self-hosted fresh inputs. Shards 1/5 and 5/5 write their digests, and the `diagnostics` gate compares them. |
| `lake exe checkerSelftest --build-bound --partition fixtures --jobs 4` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition structural --jobs 4` | Its 5 shards run. Together they run each of its controls one time, but for the comparison of the self-hosted fresh inputs. Shards 1/5 and 5/5 write the digests of those inputs, and the `diagnostics` gate compares them. |
| `lake exe checkerSelftest --build-bound --partition execution --jobs 4` | Its 4 shards run. Together they run each of its controls one time. |
| `lake exe checkerSelftest --build-bound --partition cli --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition build-policy --jobs 4` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition lint-driver --jobs 4` | Its 5 shards run. Together they run each of its controls one time. |
| `lake exe checkerSelftest --build-bound --partition fixtures --shard 1/5 --jobs 4` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition fixtures --shard 2/5 --jobs 4` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition fixtures --shard 3/5 --jobs 4` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition fixtures --shard 4/5 --jobs 4` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition fixtures --shard 5/5 --jobs 4` | The shards of the `fixtures` partition are too long for a job. Its slowest shard's check took 172 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition cli --shard 1/6 --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition cli --shard 2/6 --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition cli --shard 3/6 --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition cli --shard 4/6 --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition cli --shard 5/6 --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition cli --shard 6/6 --jobs 4` | The shards of the `cli` partition are too long for a job. Its slowest shard's check took 196 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --shard 1/6 --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --shard 2/6 --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --shard 3/6 --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --shard 4/6 --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --shard 5/6 --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition environments --shard 6/6 --jobs 4` | The shards of the `environments` partition are too long for a job. Its first shard's check was still running after 203 s in CI, when the 420-second deadline ended the job. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition build-policy --shard 1/3 --jobs 4` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition build-policy --shard 2/3 --jobs 4` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |
| `lake exe checkerSelftest --build-bound --partition build-policy --shard 3/3 --jobs 4` | The shards of the `build-policy` partition are too long for a job. Its slowest shard's check took 137 s in CI. A check of more than 85 s does not leave a quarter of the 420-second deadline. [Issue 391](https://github.com/rbeauchamp/regula/issues/391) is the work to divide them into shards that fit. |

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
Its claimed surfaces are classified by the root [`foundation_manifest.json`](../../foundation_manifest.json)
and [`audit/foundation_manifest.json`](../../audit/foundation_manifest.json); the Mathlib
integration package has its own
[`foundation_manifest.json`](../../integration/mathlib/foundation_manifest.json), which only the
[Mathlib integration check](#mathlib-integration-check) audits. Acceptance
audits the first two freshly, with every target built under the options of
[Follow the Lean community's conventions](#follow-the-lean-communitys-conventions).

- `Audit` uses an all-submodules glob, so Lake's elaborated inventory owns its module set. It is
  the claimed surface of the `audit/` package, which imports only Lean's core libraries, requires
  the checker by relative path as an adopter can and is audited against its own surface manifest.
  The checker is in the same Git work tree, so that audit replays and checks each of its modules
  that the `Audit` modules import. Its `Regula` and `RegulaPolicy` modules are the checker's own
  code, and that audit does not own them. `audit/Audit/` is one positive surface
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

Three diagnostics apply Regula to the rest of its own code base; none is part of acceptance.
`./scripts/verify.sh diagnostics self-lint` runs `REGULA_ORDINARY_LAKEFILES=1 lake lint` through the
`regula/lint` driver in the root package and then in `audit/`, as the owner of the two packages. Both packages set
`lintDriver := "regula/lint"`, so it runs over each package's `foundation_manifest.json` in
incremental mode and checks the same claimed surfaces as acceptance, through the driver's
dispatch and exit classes. `./scripts/verify.sh diagnostics self-lint-default` runs the root
package's `lake lint` without `REGULA_ORDINARY_LAKEFILES`, so with the audit-build marker that an
adopter gets by default. It leaves out the `audit/` package, which runs the same driver code.
Its default path only adds the rebuild that made the old step exceed its limit. `./scripts/verify.sh
diagnostics self-audit` checks the excluded operational `Regula` library: `lake build Regula`
builds every module warning-free ([RG2003], because the package sets `warningAsError`), then
`qualify self-audit` inspects each module of the library as Lake discovers it, each in its own
worker (several roots define `main`, so the modules cannot share one environment). For each
module it kernel-replays every owned declaration that is not `unsafe` or `partial` and calculates
the axioms of each declaration in that kernel ([RG2005], `Admission.validate`), decides every
declaration record from the live linter's collector
(`Regula.Collect.declaration`) with the proved `RegulaPolicy.checked_operationalFailure`
([RG1001]–[RG1005], [RG1007], [RG1009]) and, where that passes, `RegulaPolicy.checked_decisionFailure`
([RG1008]) against the decision contracts of the same module, and checks module and
material-claim docs with the linter's predicates ([RG5001]–[RG5003]). Operational code is held to Standard-Logical with three facts reported, not
failed: authored `unsafe`/`partial` declarations ([RG1006]), the axioms that Lean's `collectAxioms`
omits for a declaration, and, in a definition whose type is not
a proposition, the pinned toolchain's Lake axioms (those a `Lake` module in the toolchain's own
library directory declares). `operationalFailure_none_iff` states the exact success relation,
`operationalFailure_ne_escapeHatch` that an escape hatch never fails a declaration,
`operationalFailure_prop` that a proof gets exactly the conforming decision, and
`operationalFailure_eq_conforming` that the decision is the conforming one on every declaration
without a reported fact. The self-audit claims no proof surface and no execution result, and
applies the linter's collector and decisions to completed modules rather than attaching its
editor hooks. Lean's import and kernel replay, the collector's observations, toolchain artifact
paths, the worker processes and their JSON transport are trusted.

The self-audit also refuses a one-sided comparison of `Json` values, the defect of
[#269](https://github.com/rbeauchamp/regula/issues/269). It inspects each module of each library
except `Fixtures`, and each executable root that no library contains. Lake builds them first, and a
worker imports each module alone, with its private declarations. It refuses a declaration if its
type or value names the instance `Lean.Json.instBEq`. It also refuses one that compares texts of
`Json.compress`, directly or through `let` bindings. The module `RegulaCore.JsonAgreement` is
exempt, and so is each entry of `SelfAudit.jsonComparisonAllowlist`, which states its reason.

Each use of that instance names it, so the check finds each such use in the inspected modules. It
does not find texts that a named helper or a function argument renders before a comparison. It also
misses a comparison through an instance that Lean or a dependency declares for a type with a `Json`
field.

The self-audit refuses an allowlist entry if its declaration compares no `Json` values, so each
entry is a control of the check. Three fixed controls run too. A declaration named under
`Regula.JsonAgreement` in a different module is found, and so are `compress` texts compared through
`let` bindings. A `compress` that no comparison reads is not found.

`./scripts/verify.sh diagnostics self-audit 1/4` to `4/4` each run one shard of the self-audit.
The campaign sorts each list of modules that it inspects by name, and it deals the list to the
four shards in turn. Thus each shard audits a quarter of each list. The theorem
`SelfAudit.selected_cover` states that the four selections together are a rearrangement of the
list that the single run audits. The dogfood workflow runs the four shards, and the local command
`diagnostics self-audit` runs all of them in one invocation.

Before its `lake lint` in the root package, `diagnostics self-lint` builds the `lint` driver, its
worker `axiomGate` and the claimed targets in one `lake build`. Lake's lint dispatch, the driver
and the audit otherwise build them in sequence. Each of these builds still runs, and it
builds what is not built.

The repository's own checklist rows, which apply to this repository only:

| ID | Required result | Normative source | Required Lean-specific verification |
| --- | --- | --- | --- |
| DOGFOOD-01 | The repository's own claimed Lean surfaces, classified by the manifests in [Repository conformance](#repository-conformance), satisfy every applicable row of the standard's checklist. | [Repository conformance](#repository-conformance) | Audit each claimed Lake surface as an ordinary claimed surface with no special exemptions; the application's admission, update, and composition contracts are proved about the same computable definitions its executable runs, and its `IO` boundary is reported, never silently excluded. |
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

- **Style and naming.** Regula's libraries build on Lean core (only the Mathlib integration
  package's `MathlibAudit` imports Mathlib), so they follow Lean core's
  [style guide](https://github.com/leanprover/lean4/blob/master/doc/std/style.md), for example
  `fun x =>` rather than Mathlib's preferred `fun x ↦`, and the shared case rules of the
  [naming conventions](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md):
  proofs, including `ExecutableContract` registrations, in `snake_case`; propositions and
  types in `UpperCamelCase`; other terms in `lowerCamelCase`.
- **Options and linters.** Every library and executable builds with `autoImplicit` and
  `relaxedAutoImplicit` off and `linter.missingDocs` on (the package `leanOptions`; only the
  `Fixtures` controls turn the linter off); `MathlibAudit` also enables Mathlib's standard linter set
  with the §6.7 exclusions (`mathlibLinters` in `integration/mathlib/lakefile.lean`). [RG2006] checks these options on the claimed targets. Declare universes and
  implicit binders explicitly, and give every public declaration, constructor and field a
  docstring that states what it is or guarantees, no more than its definition and proofs
  establish (standard §5.1).
- **Module docstrings.** Each module starts, directly after its imports and before any
  `public section`, with a `/-! # Title … -/` docstring ([RG5001] checks the position).
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

For a new or changed Markdown document, obey the [writing rules](writing.md). The documentation
step does the [checks of the prose](#the-prose-of-markdown-documents) and the
[check of the vocabulary](#the-vocabulary-of-the-project).

For review, use the repository-local
[review toolkit](../../.agents/skills/pr-review-toolkit/SKILL.md) and the applicable
[compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/), with the repository rows above. Scope verification to
the affected claims, retain required checks, and distinguish historical results
from evidence for the current revision.

### Rule IDs in documentation

The [adoption guide](adoption.md#cite-a-rule) states the convention. `Regula.Prose`
([`RegulaCore/Prose.lean`](../../lean/RegulaCore/Prose.lean)) defines it for rendered pages and
checks it there: a rule ID is `RG` and four digits with no ASCII letter or digit directly before or
after, and each one in prose must be a registered rule inside a link to that rule's page
(`bareMentions_nil_iff`). `Regula.Markdown`
([`RegulaCore/Markdown.lean`](../../lean/RegulaCore/Markdown.lean)) decides the same for a
Markdown document, from a CommonMark parser's reading of it
([Markdown documents](#markdown-documents)).

| Document | The link |
| --- | --- |
| Each Markdown document that the repository tracks, but not the root `README.md` | The development page, `https://rbeauchamp.github.io/regula/dev/rules/<ID>/` (`Edition.url`, which a finding's rule link also uses), optionally with a fragment. Write `[RG2003]` and define `[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/` once at the end of the document, after a blank line; an inline link is accepted too. The agent skill, `.agents/skills/regula/SKILL.md`, is generated with every rule ID it names already such a link (`Regula.Guidance.citation`); regenerate it with `lake exe regula skill` and never edit it. |
| The root `README.md` | The stable address `https://rbeauchamp.github.io/regula/rules/<ID>/` with no fragment, for a rule that is in a release (`Regula.Markdown.target`, `released_iff`). The check accepts this address only in a document of the list `Regula.Markdown.stableDocuments`, and that list has only this file. The site build examines the addresses of the documents of the same list ([links of the root README](#links-of-the-root-readme)). |
| A rendered page of the standard or of the rule-reference site | The rule's page in the same edition: its route `rules/<ID>/` (`RuleId.route`) relative to the edition root. In the standard write `{rule}[RG2003]`, which refuses an unregistered ID; generated pages link the IDs of registry and explanation prose themselves (`Prose.linkVerso`, `ruleLink`), and generator text names a rule with `Prose.relativeCitation`. |

In a rendered page, prose is the text outside the `code`, `pre`, `script` and `style` elements and
comments. Pasted tool output is a `pre` element, and a Lean identifier is written as code. A rule
table that is an index of rule pages names each rule as a link to its page, so its IDs are already
linked. A heading is prose, so a rule ID in one is a link. The one rule ID that is not written as
a link is a rule page's own, in that page's `title` and `h1`, because a page cannot usefully link
to itself (`Prose.ownPage`); any other rule's ID there, and any rule ID in the `title` or `h1` of
another page, is refused. `./scripts/verify.sh docs` checks the standard rendered alone
(`docFenceAudit --verso`), and `./scripts/verify.sh site` checks every page of the
development edition; each failure names the file, the line and the ID. The scanner is small and
strict, not an HTML parser: a page with a `code`, `pre`, `title` or `h1` element, a comment or a
script that is never closed is refused, since the text after it could not be read as prose. The
release editions already published are frozen copies and are not rewritten.

#### Markdown documents

`./scripts/verify.sh docs` checks every Markdown document Git tracks: each file `git ls-files`
lists with the extension `md` or `markdown`, read from the working tree
(`lake exe regula-markdown ..` in `markdown/`). This check reads no Markdown syntax of its own.
md4c, a CommonMark parser that the `markdown/` package requires as MD4Lean, parses each document
in its GitHub dialect (tables, strikethrough, task lists and autolinks), and
[`markdown/RegulaMarkdown.lean`](../../markdown/RegulaMarkdown.lean) translates its parse into
pieces (prose, code, the edges of links, refusals, and the boundaries between runs and lines)
for `Regula.Markdown`, which decides on the pieces (`documentErrors_nil_iff`). The theorem is
about the pieces it is given; the translation has no theorem. Hand-written readers of
Markdown remain elsewhere in the repository and are no part of this check: the fence scanner of
the documentation audit (`Regula.Checker.FenceScan`, which finds the `lean` fences and their
markers), `Regula.Prose.scanGenerated`, which finds the code spans and links of generated
prose, and `RegulaPolicy.Intent`, which finds the heading lines of a docstring.

- Prose is every text md4c reports outside code spans and code blocks: paragraphs, headings,
  list items, block quotes, table cells, emphasis, link text and image descriptions. A rule ID
  there must be a registered rule inside one link to a page of that rule. That page is its
  development page. In the root `README.md` only, that page can also be the stable address of
  the rule, if the rule is in a release. The link is written
  inline or as a reference to a link reference definition. A reference without a definition is
  prose.
- A rule ID is read in the rendered text of a line, across the edges of links and code spans.
  One that such an edge divides, as in `RG[2003](…)`, is refused; one that is wholly code is not
  a mention. md4c itself decodes each character reference, in text and in a link's destination.
- An image's description is read as md4c renders it, as text alone: a link or a code span
  inside it is description text, and only a link around the image links it.
- No HTML is read. A raw HTML block is refused, a comment too, and so is a document with inline
  raw HTML such as `<kbd>`; write it in Markdown. The one raw HTML that is read is a block that
  is exactly a fence marker of the documentation audit, `<!-- lean-trusted-compiler -->` or
  `<!-- lean-fail: PATTERN -->` with no `>` in the pattern: it is one comment and renders as
  nothing (`auditMarker`).
- A document with a table that has no body row, or with a NUL character, is refused: MD4Lean
  cannot represent either.
- A refusal names the file, the line and the ID or the construct. The exception is a document
  whose reading cannot be used (inline raw HTML, a table with no body row, a NUL character, or
  md4c failing): it is refused as a whole, by file and reason with no line, and its rule IDs
  are reported only once it is read. md4c reports text, not
  positions, so the line is derived: the reported text is placed on the source lines in order,
  and every such placement lies between the first and the last (`leftmost_le`, `le_rightmost`).
  Where they differ, because the same text also stands on a line md4c does not report (a link
  reference definition, usually), the refusal names both, as in `README.md:88-162`.

#### Links of the root README

Each link of the root `README.md` to the rule-reference site is a stable address. A stable
address names no edition. Thus the link opens the latest release, and a release changes no link
of that file. A stable address is one of these:

- The site root, `https://rbeauchamp.github.io/regula/`.
- An address below `https://rbeauchamp.github.io/regula/rules/` or
  `https://rbeauchamp.github.io/regula/standard/`, with no fragment.

`./scripts/verify.sh docs` does this check on md4c's reading of the file
(`Regula.Markdown.siteLinkErrors`, `siteLinkErrors_nil_iff`). It reads a link destination as an
address of the site if the text `rbeauchamp.github.io/regula` is in it. The theorem
`Stable.not_edition` shows that a stable address is not an address of `dev/` or of
`v/<version>/`, for each version. The check does not read an image, and it does not read a link
reference definition that no link uses.

`./scripts/verify.sh site` then reads the text of that file (`Regula.Site.siteAnchors`). It finds
an address of the site only where the text `https://rbeauchamp.github.io/regula/` is in the file.
The route is the text after it, up to the first character that is not a letter, a digit, `-`,
`_`, `/` or `#`.

The command refuses an address that is not a file of the artifact (`missingAnchors`). Thus it
refuses a stable address that has no page in the latest release.

The root `README.md` cannot link a rule that is in no release, because that rule has no stable
address. It also cannot give the ID of that rule in prose. Write the ID as code, or add the rule
to that file after its release.

The other tracked documents link the development edition. This check does not read their links
to the site. The check of rule IDs refuses the stable address of a rule in such a document.
The site build examines only the addresses of the root `README.md`. The list
`Regula.Markdown.stableDocuments` gives the documents to the two checks.

The check trusts, and does not verify:

- md4c's conformance to CommonMark and to the GitHub extensions it implements, and its
  rendering of a character reference, which is how one is decoded.
- MD4Lean's wrapper, for the documents the check reads. At the pinned revision its parse of
  inline raw HTML is not a value of its own type (reading it crashed when tried), which is why
  the check never asks for it.
- That md4c's HTML renderer and MD4Lean's parse see the same reading of the same text and flags.
  The treatment of inline raw HTML rests on this: a document is read only when md4c renders it
  to the same HTML with inline raw HTML enabled and with it taken as text, and the parse taken
  with it as text then describes the rendering GitHub's dialect gives.
- That md4c reads a document as GitHub's renderer does (cmark-gfm and GitHub's later passes).
- The translation of MD4Lean's document into the pieces the proved check decides on (`read`
  and every definition it calls in `markdown/RegulaMarkdown.lean`: `block`, `inline`, `flat`,
  `link` and the rest). It is project-owned Lean with no theorem: it decides which
  piece each element md4c reports becomes, and only the evaluated controls of that module
  observe it.

Where md4c and GitHub are known to differ in a way that bears on the check, the check refuses
what md4c's parse shows of the difference. The rest is not seen:

| Difference between md4c and GitHub | What the check does |
| --- | --- |
| GitHub renders footnotes; md4c has none. md4c reads a footnote whose body is a link destination, with or without a title and whatever lines continue it, as a link reference definition, which is not prose. | Such a footnote's reference becomes a link whose text starts with `^`, or with a `!` before it an image whose description does, and that link or image is refused, inside an image's description too. So is a link or an image written with its destination whose text or description starts with `^`, since MD4Lean does not tell it from a reference. Not seen: such a footnote referenced only in the second brackets of a full reference, and the indented lines that continue a footnote, which md4c reads as a code block. Every other footnote is paragraph text for md4c and is checked as such, which the next row limits. |
| GitHub starts a new block at each footnote definition (`[^n]:`), also on the line after paragraph text or after another definition; md4c reads those lines on as one paragraph. | Not seen: a code span or a link's text that md4c reads from one such line into the next is kept whole, where GitHub reads each definition by itself. A rule ID inside it is code or linked for md4c and prose on GitHub. |
| GitHub reads a table only when its header row has as many cells as its delimiter row; md4c takes the column count from the delimiter row and drops the cells beyond it. | Not seen: where the counts differ, GitHub shows the lines as a paragraph, and md4c's parse has no trace of a cell it dropped. |
| GitHub starts a table at a header row that is the last line of a paragraph; md4c only at one that is the first line of its paragraph, and otherwise reads the header row, the delimiter row and the rows after them on as that paragraph. | Not seen: md4c's parse has no table there, so the refusal of the next row does not apply, and a code span or a link's text that holds a pipe character or runs from one row into the next is kept whole, where GitHub ends the cell. A rule ID inside it is code or linked for md4c and prose on GitHub. Leave a blank line before a table. |
| GitHub finds the cells of a table row first and ends a cell at a pipe character that is not escaped, also one inside a code span, a link's text or an image's description; md4c reads those first and keeps them whole. A link GitHub cuts that way leaves its text as prose. An escaped pipe character there ends no cell for either, but md4c keeps its backslash in a code span, where GitHub removes it. | A pipe character inside a code span, a link's text or an image's description in a table cell is refused, an escaped one too: md4c reports a link's text and an image's description without the backslash, and the check reads no escapes, so it does not tell an escaped pipe character from another. An escaped pipe character in a cell's own text is text for both and is read. |
| The two find the end of a bare URL by their own rules. | A rule ID in an autolink is refused, in a bare URL and in `<URL>` alike, since MD4Lean does not tell them apart. Write the link in brackets. |
| md4c reads an autolink inside a link's text as a link of its own. GitHub makes no link of a bare URL there, and it renders `<URL>` there as a link inside a link, which a browser ends at the inner one, so the text after it is outside every link. | A link inside a link's text is refused, for a bare URL and for `<URL>` alike, since MD4Lean does not tell them apart. For the bare URL that refuses what GitHub shows as one link. Write the URL outside the link's text. |
| GitHub renders math written as `$…$`, as `$$…$$`, as a code span between two dollar signs, and as a fenced code block with the info string `math`. md4c reads the first two as text here, and the other two as a code span and a code block. | A rule ID in `$…$` or `$$…$$` is refused as prose. Not seen: one in the code span or the fenced block is code for md4c and is accepted, where GitHub renders it as math. |
| GitHub shows YAML front matter, the lines between two `---` lines at the start of a document, as a table of its raw values; md4c has no front matter and reads those lines as Markdown, a thematic break and then a heading. | Not seen: md4c's parse has no trace of front matter, so its text is checked as prose. A bare rule ID there is refused; one written as a code span or a link is code or linked for md4c and plain text on GitHub, backticks or brackets included. The skill files under `.agents/skills/` have front matter. |

Link destinations and titles, code block info strings, and link reference definitions are not
prose and are not checked.

#### Opening of the root README

The summary of Regula is one definition, `Regula.Site.summary` in [`lean/RegulaCore/Summary.lean`](../../lean/RegulaCore/Summary.lean). The home page of the site shows it, and its link previews show its plain text.

`./scripts/verify.sh docs` reads the top-level blocks of the root `README.md` and of the adoption guide, as md4c gives them. It refuses a document unless its first block is a heading of level 1. Its second block must be the paragraph that md4c reads for the summary alone (`Regula.Markdown.summaryErrors`, `summaryErrors_nil_iff`). Thus the second block is the summary on one line, and a block of a different kind before it is refused.

The same step runs `lake reservoir-config` in the repository root. It refuses a `description` of `lakefile.lean`, as Lake reads it, that is not the summary without its backticks.

#### The example of the root README

The root `README.md` shows the module [`markdown/Readme/Shortcut.lean`](../../markdown/Readme/Shortcut.lean) and the findings of `axiomGate --file` for it. No Lake library contains that file, thus no target of the repository builds it.

`./scripts/verify.sh docs` makes a new Lake project in a temporary directory. The project has the `lean-toolchain` of the repository, and it requires the root package by its path. In that project, the step runs `lean --json` and `lake exe axiomGate --file` on the module. It refuses the `README.md` unless these conditions are true (`Regula.Markdown.demonstrationErrors`, `demonstrationErrors_nil_iff`):

- Its one `lean` code block is the text of the module, byte for byte.
- Lean gives only the warning that the `README.md` states for the module (`demonstrationMessages`).
- `axiomGate --file` exits with 1.
- The output of `axiomGate --file` fits the one `text` code block. A line that is `…` alone stands for any sequence of lines, also for no line. A `…` in a different line stands for any text in that line. Each other character must be equal (`lineFits_plain`).

The step also examines three changed copies of its input. They have a changed `lean` block, a warning of Lean that the `README.md` does not state and a changed finding line. It refuses unless the check refuses each copy, and it shows the refusal of each copy.

### The vocabulary of the project

The same executable does a check of [`CONTEXT.md`](../../CONTEXT.md), the vocabulary of the
project. This check is check C9 of the [writing rules](writing.md), and the writing rules give
its definition.

The decisions are in [`RegulaCore/Vocabulary.lean`](../../lean/RegulaCore/Vocabulary.lean). Each
decision has a decision contract and the attribute `regula_decision`. The definitions of a word
and of a sentence are in
[`RegulaCore/ControlledText.lean`](../../lean/RegulaCore/ControlledText.lean). The function
`vocabularyOf` in [`markdown/MarkdownMain.lean`](../../markdown/MarkdownMain.lean) uses these
decisions.

The executable also does not accept the file in each of these conditions, and it has no decision
contract for them:

- The file has the line `Shared vocabulary:`, and the command does not have the option
  `--shared`.
- Git does not track the file.
- Git gives no list of tracked files for the repository, or for the directory of the file of the
  option `--shared`.

The controls of the check are the files of
[`lean/Fixtures/ControlledProse/`](../../lean/Fixtures/ControlledProse/) with a name that starts
with `C9`. The documentation step operates the controls of that directory first:
`lake exe regula-markdown --controls ../lean/Fixtures/ControlledProse` in `markdown/`. The check
accepts two controls of C9 and does not accept the others. For a control that it does not
accept, each message must start with the file, the line and the check of the control. A control
has the extension `text`. Thus the check of the tracked Markdown documents does not read the
controls.

This check is not a rule of the checker and not a requirement of the standard. It has no rule
ID.

### The prose of Markdown documents

The same executable does the checks C1 to C8 of the [writing rules](writing.md) on each tracked
Markdown document. The baseline [`prose-baseline.json`](../../prose-baseline.json) gives the
findings of each document that does not obey the writing rules at this time. Check B1 compares
each document with its entry, and it does not accept an entry with no tracked Markdown document.
Check B2 compares the baseline with the baseline of the base revision. If the base revision has
no baseline, B2 compares the baseline with the Markdown documents of the base revision.

The decisions are in
[`RegulaCore/ControlledProse.lean`](../../lean/RegulaCore/ControlledProse.lean) and
[`RegulaCore/ProseBaseline.lean`](../../lean/RegulaCore/ProseBaseline.lean). Each decision has a
decision contract and the attribute `regula_decision`.

The start of the check gives the base revision of check B2. The
[writing rules](writing.md#the-baseline) give the base revision for each start. The workflow
gives the start to the documentation step in the variable `REGULA_PROSE_START`. The `verify`
job of CI gets the full history of the repository. If Git does not give the base revision,
check B2 does not accept the baseline.

The controls of the base revision are repositories that the executable makes with Git in a
temporary directory. Each control gives the variable in a form that a start gives, or no
variable for the run of a developer. No control has the values that GitHub gives for an event.

A control that expects a refusal does not pass if the check uses a base that accepts. A control
that expects no refusal does not pass if the check uses a base that refuses. The comment of each
control gives the bases that the control tells apart from the correct base. No control that
expects no refusal tells the correct base apart from the examined commit.

The controls of an entry with no document are commits of one of these repositories. Three
commits remove a document and keep its entry: an entry of numbers, a `generated` entry and a
`frozen` entry. One commit has an entry for a file that Git does not track. One commit has an
entry for a tracked file that is not a Markdown document. Check B1 must give a refusal for each
of these commits, at the line of the entry.

One more control is a repository with a baseline that Git does not track. The option
`--write-baseline` must keep the `frozen` entry and the `generated` entry of a document. It
must write no entry that has no document.

The controls of these checks are in the same directory as the controls of the vocabulary. A
control of C1 to C8 is a document with the extension `text`. A control of B1 or B2 is a baseline
with the extension `json`. Thus the checks of the tracked Markdown documents do not read the
controls. For a control that a check does not accept, each message must start with the file,
the line and the check of the control.

These checks are not rules of the checker and not requirements of the standard. They have no
rule ID.

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

The [website guide](website.md) specifies the pinned Verso setup, `./scripts/verify.sh site` (after the three rule-example shards), publication and the rule-change workflow. The site build complements, and never partitions, [acceptance](#develop-and-verify). Review workflow must inspect rule IDs, exact scopes/modes, source ranges, versioned help routes and generated-source agreement where affected; no extra mandatory benchmark campaign is introduced.

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

## Pull request titles

Pull requests merge by squash, so a pull request's title becomes the subject of its one commit on
`main` and its description that commit's body. The title is a
[Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) header,
`type(scope)!: summary`: a type in lower case, an optional scope, `!` for a breaking change, then
`: ` and a summary. The required `title` check ([`title.yml`](../../.github/workflows/title.yml),
`lean --run lean/Regula/Release.lean title`) refuses any other title, and runs again when the
title is edited. The type decides what the commit calls for in the next release:

| Type | Use it for | Release |
| --- | --- | --- |
| `feat` | a new rule, a tightened rule (one that refuses what it accepted before), or a new feature | minor |
| `fix` | a bug fix: more accurate findings, messages, CLI or report behaviour | patch |
| `perf` | a performance improvement | patch |
| `build` | the build or dependencies, including a move to another Lean toolchain | none; a toolchain move makes the release minor |
| `docs`, `refactor`, `test`, `ci`, `chore`, `revert` | documentation, restructuring, checks, CI, maintenance, reverts | none |

A breaking change, `type!:` or a `BREAKING CHANGE: <what breaks>` line in the description, calls
for a major release, or a minor one before 1.0. A tightened rule is a `feat`, not a breaking
change: before 1.0 both make a minor release. The Release workflow's own pull request is a
`chore(release)`.

## Release

A release is one action: run the **Release** workflow on `main` (**Actions → Release → Run
workflow**, or `gh workflow run release.yml --ref main`), then open and merge the pull request it
prepares. Every step is a command of [`lean/Regula/Release.lean`](../../lean/Regula/Release.lean).

Regula numbers its own releases by [Semantic Versioning](https://semver.org), in the `version`
of [`lakefile.lean`](../../lakefile.lean) (whose Lake documentation reserves patch increments for
bug fixes), and tags each release `v<version>`. A release supports exactly one Lean toolchain,
the [`lean-toolchain`](../../lean-toolchain) of its release commit, and `Regula.releases`
([`RegulaCore.Edition`](../../lean/RegulaCore/Edition.lean)) records it with the release. A
**patch** release carries fixes on the same toolchain, with no new or tightened rule; a **minor**
release carries new or tightened rules, new features or a move to another Lean toolchain; the
**major** version stays `0` until the maintainer declares 1.0 (the workflow's `bump` input set to
`major`). So a fix reaches adopters on their toolchain whenever `main` has one, without waiting for
the next Lean release.

The version is derived, not chosen: from the [types](#pull-request-titles) of the commits of
`main` since the previous release, the greatest bump any of them calls for, and at least minor
when `lean-toolchain` differs from the previous release's. When the commits call for none and
the toolchain is unchanged, there is nothing to release. The workflow's `bump` input (`derived`,
`patch`, `minor` or `major`) may raise that bump and never lowers it; it is also how a release
goes out when the commits call for none, or when a commit's subject is not a Conventional
Commits header, which leaves the derivation undecided: the release's bump is then the greater of
the requested one and the one the other commits and the toolchain call for.
`Regula.Release.nextVersion` is that decision, and the kernel checks its theorems each time a
step runs. The derivation over the commits alone
(`derive`) calls for no release exactly when every commit's type calls for none
(`derive_eq_none_bump`) and is undecided exactly when a subject is not a header
(`derive_eq_none`). The release's bump from its predecessor is at least each header's, whatever
was requested (`nextVersion_ge`), never below the requested bump (`nextBump_ge_requested`), and
at least minor for a toolchain move (`nextBump_moved`); the derived version follows its
predecessor (`nextVersion_follows`, `follows`): it is later than its predecessor, a patch
release keeps its predecessor's toolchain, and a new line resets the lower components. **open**
also refuses it unless it is later than every listed release before it, a pending release it
replaces excepted (`admits`, `admits_iff`). `introduced_startsLine`
([`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean)) refuses a patch release that introduces a
rule, and `releases_ascending` and `releases_follow` check the listed releases themselves. The
job summary of **open** lists each commit's bump.

The Lean ecosystem is split on release numbering. Batteries, Aesop, Plausible, import-graph and
doc-gen4 tag the toolchain they support (`v4.34.0` for Lean 4.34.0), which allows one release per
toolchain; ProofWidgets numbers its own versions (such as `v0.0.114`), as Regula now does, and
the compatibility table in the [adoption guide](adoption.md#1-require-regula) maps each release to
its toolchain. Two alternatives were rejected. A tag `v4.34.1` for a fix on Lean 4.34.0 reads, by
that convention, as a release for Lean 4.34.1, and collides with a real Lean point release. A tag
`v4.34.0-1` sorts before `v4.34.0` in Lake's order, which ranks a version with a `-` suffix below
the version without it.

The first release, `v4.34.0`, predates this numbering: it was tagged with its Lean release, and it
stays as published, immutable. Its semantic version is `0.1.0`, which orders it before every later
release, so the first own-numbered release is `0.2.0`; its lifecycle stamps
(`.release ⟨4, 34, 0⟩`) and its rule reference `/v/4.34.0/` keep its tag's number. Its
`lakefile.lean` declares no version, which Lake reads as `0.0.0`, so Lake and Reservoir rank it
below every later release too ([Reservoir](#reservoir)). `main`'s `lakefile.lean` declares the
latest release's version (`0.0.0` until `0.2.0`), and a step of the required `verify` check,
before acceptance (`lean --run lean/Regula/Release.lean agree`), refuses a version Lake reads
that is not the latest listed release's, and an adoption-guide compatibility table that is not
the one `Regula.releases` gives.

The same step reads each `require` of Regula in the tracked Markdown documents: the line
`rev = "<tag>"` after the line `git = "<url>"`, or the text `"<url>" @ "<tag>"`. In these forms,
`<url>` is `https://github.com/rbeauchamp/regula`, and the step reads only the lines that contain
it in quotation marks. It refuses a `require` that names a release other than the latest listed
release. It also refuses a different use of that address in quotation marks. The root `README.md`
and the adoption guide must each have a `require` of each form, or the step refuses. The release
pull request sets each `require` to its release, and reads its edit back.

The same step reads each mention of a release in the root `README.md`. The text ``Regula `v<version>` `` is a mention of a release of Regula, and the text `leanprover/lean4:<release>` is a mention of a Lean toolchain. The step refuses a mention that does not name the latest listed release or the toolchain of that release. It also refuses a `README.md` without a mention of each kind, and a mention without its version or its closing backtick. The release pull request sets each mention to its release or to the toolchain of the release, and reads its edit back. The theorems `mentionsAgree_iff` and `unmentioned_eq_nil_iff` state the two decisions.

`main` never carries a release label: `Regula.installed`
([`RegulaCore.Edition`](../../lean/RegulaCore/Edition.lean)) is `.unreleased` on every commit of
`main` and of a pull request, which the first step of the required `verify` check enforces
(`lean --run lean/Regula/Release.lean unreleased`). The only build labelled a release is the
release commit that CI creates beside `main`, and the site build refuses a release label once
the release's tag names another commit (`labelAdmitted_release_iff`). Nothing public exists
until the release commit has passed the same checks as `main`:

1. **open** ([`release.yml`](../../.github/workflows/release.yml)) derives the version and
   creates the commit of the release pull request, a child of the `main` commit the workflow runs
   on that appends the release with its toolchain to `Regula.releases`, sets `lakefile.lean`'s
   `version` to it, adds its row to the adoption guide's compatibility table, sets each
   `require` of Regula in the tracked Markdown documents and each mention of a release in
   `README.md` to it or to its toolchain, and stamps it into
   rule lifecycle positions still `.unreleased`
   ([`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean)): each `.unreleased` on a line that
   starts `lifecycle :=`. `.unreleased` is the placeholder for both positions: a new rule states
   `lifecycle := .active .unreleased`, and a rule retired since the last release states
   `lifecycle := .retired (.release ⟨X, Y, Z⟩) .unreleased replacement` on one line. The stamp is
   a convenience that reads text; the guarantee is the kernel's check of
   `release_attributes_rules` on the release commit (step 2). `Regula.installed` stays
   `.unreleased`. It refuses unless the releases GitHub reports published (its releases that are
   not drafts) are exactly the releases it keeps listed before the one it lists
   (`Regula.Release.publishedExactly`), and checks that again just before it creates the branch,
   so it never
   lists a release in place of one published by then. GitHub creates and signs the commit, and
   the step refuses unless GitHub verified
   the signature. It creates the branch `release/v<version>-<commit>`, named after that commit
   (`Regula.Release.pullBranch`), and writes to its job summary the
   link that opens the pull request `chore(release): Regula v<version> for Lean <toolchain>`,
   title and description filled in. A maintainer opens the pull request from that link, which
   starts its checks, and merging it through normal review is the decision to release. While it
   observes a release pull request for that version open, it
   [refuses and creates no branch](#rebuilding-the-release-pull-request)
   (`Regula.Release.branchAction`); a run that creates a branch creates one of its own and moves
   none. Every
   check of this pull request passes before it merges. Until the release is published, its
   `site` check, like the site build of every unreleased commit that lists the release, builds
   and checks the artifact with a preview of the release's edition, rendered from that commit
   without a release label ([versions](website.md#versions-and-routes)): the release's own
   edition exists only once CI builds it from the release commit, and an artifact with a preview
   is never deployed. The required checks are `verify`, `title`, `diagnostics`,
   `diagnostics rule-examples 1/3`, `diagnostics rule-examples 2/3`, `diagnostics rule-examples 3/3`,
   `site`, `mathlib integration`
   and code scanning's `CodeQL` and `Analyze (actions)`.
2. **candidate** (`ci.yml`, the `candidate` job on `main`): once acceptance and the three rule-example
   shards pass on a commit of `main` that lists a release not yet published, it refuses unless
   the releases GitHub reports published are exactly the releases listed before it
   (`publishedExactly`): its listed predecessor is then the latest published release
   (`publishedExactly_latest`), and a release whose listed predecessor is not is refused
   (`publishedExactly_refuses`), so every published release stays listed, in order. It derives
   the bump again, over the commits of `main` since the release listed before it up to that
   commit, which
   are the commits the release contains, and refuses unless the release's bump from that
   predecessor is at least the bump those commits and `lean-toolchain` call for
   (`Regula.Release.covers`, which `covers_iff` characterizes exactly; the release **open**
   derived passes on the commits it derived from, `nextVersion_covers`). So a pull request that
   merged after **open** derived the version and calls for more, such as a `feat` after a patch
   release was derived, stops the release; the refusal lists each commit's bump. Otherwise it
   creates the release commit, a signed child of that commit that is not on `main` and whose
   only change sets `Regula.installed` to the release, and points the branch
   `release/v<version>-candidate` at it.
   The next jobs run on it, with its release label, the checks of `main`: `release-verify` both
   acceptance steps, and `release-site` the three rule-example shards and the site build, which
   renders the release's edition and writes it as `regula-site-<version>.tar.gz`
   ([versions](website.md#versions-and-routes)). They check out the commit of `main` itself, not
   the release commit: their **adopt** step derives the release commit's content there with
   `main`'s own code, requires that it is the release commit's tree and that the commit of
   `main` is the release commit's only parent, and only then adopts the release commit's name,
   writing no file from it. `Regula.Release.adopt` states why the checked content, and every
   identity the checks record, is then exactly the release commit's.
   `release_attributes_rules` is the gate: when `Regula.installed` is a release, no lifecycle
   position of any rule is `.unreleased`, so a release commit that misses one, however it is
   written, fails to build.
3. **publish** (`ci.yml`, the `publish` job), only once all of those checks pass and both
   adopted the release commit, creates the
   GitHub release with its notes (how to require, set up and update, then GitHub's generated list
   of changes since the tag of the release listed before it) and that edition as its asset,
   published only once the asset is attached.
   Publishing creates the tag `v<version>` at the release commit; no step writes the tag
   otherwise, so a failed check leaves no tag and no release. Immutable releases, a repository
   setting that is on, then freeze the tag and the asset. The site build of `main` runs after it
   and takes the release's edition from the asset, and `deploy` publishes `/dev/` and
   `/v/<version>/`.

Each job keeps the budget of the job on `main` it repeats: `candidate` and `publish` 30 minutes
each; `release-verify` 45 minutes, like `verify`, with each `verify.sh` step under its own
420-second deadline; and `release-site` 105 minutes, which is 30 + 30 + 45, the budgets of the two
`rule-examples` shards and the `site` job it repeats one after another, each `verify.sh` step
again under its own deadline.

Nothing follows the release: `main` stays unreleased, so there is no reset to merge. Adopters
require the tag, and Lake fetches a dependency's tags with the repository, so a tag whose commit
is not on `main` resolves like any other.

Other pull requests still merge during a release. The release is cut from whichever head of
`main` that lists it first completes the whole chain: until the release is published, each run
of **candidate** on the head of `main` creates a fresh release commit on it, so a run that a
later merge cancelled needs no repair, and a re-run of CI on `main` finishes the release. Once
the release is published, nothing changes. The decision of **candidate** and **publish** is
`Regula.Release.tagAction`, whose theorems the kernel checks each time a step runs
(`tagAction_converges`, `tagAction_published` and the exact cases of each action). If a pull
request that calls for a greater bump than the release's merges to `main` before the release is
published, **candidate** refuses the release; if one that adds or retires a rule does, its
`.unreleased` lifecycle position makes the release commit fail `release_attributes_rules` in
`release-verify` and `release-site`. Either way nothing is published: run the Release workflow
on `main` again as a new run, whose **open** derives the version the commits then call for and
stamps that rule too. While the listed release is unpublished, that run lists that version in
its place (a `feat` turns a pending patch release into a minor one) and restamps its lifecycle
positions, in a new pull request. While the release pull request is still open, the run refuses
when the version is unchanged, until that pull request is
[closed](#rebuilding-the-release-pull-request), and otherwise creates the branch of the new
version and leaves the open pull request as it is: close it, since it is stale. If it merges
instead, the same checks apply to it: **candidate** refuses a release that does not cover the
commits it contains, and a rule it left unstamped fails `release_attributes_rules`. A pull
request that **open** prepared
to list a release in place of a pending one is
refused by **candidate** if the pending release was published before it merged: list the
published release again, before the new one, with its stamps. A re-run of the Release workflow
reuses its original commit, so it stamps nothing new.

Each step resumes when its job is re-run: **open** creates a fresh commit and branch on the
commit its run started from, while it observes no release pull request for its version open;
**candidate** creates a fresh release commit and refuses published releases other
than those listed before the release, a release that does not cover the commits it contains and
a `lean-toolchain` other than the toolchain the release records; and **publish** replaces an
unpublished draft and skips a published release. While the release is unpublished,
**candidate** and **publish** refuse a stale run whose commit is no longer the head of `main`
and a tag that names another commit. **open** refuses a derivation that releases nothing, a
patch release that introduces a rule (a new rule, or one a pending release it replaces
introduced), published releases other than those it keeps listed (an earlier listed release not
yet published, or a published release not listed), a `main` that already lists the release
with nothing left to change, and a release pull request for its version that it observes open.

Who opens the pull request, and when its checks start: a maintainer opens it from the link in the
job summary of **open**, and opening it starts its checks. No workflow creates a pull request,
because the repository does not let GitHub Actions create one.

Adopters update by changing the tag, and `lean-toolchain` when the release supports another
toolchain, then running `lake update regula` and `lake exe regula init`
([adoption guide](adoption.md#update-regula)).

### Rebuilding the release pull request

To rebuild the release pull request, on the same commit of `main` by a re-run or on its head by
a new run:

1. Close the release pull request.
2. Run the Release workflow.
3. Open a fresh pull request from the link in that run's job summary, which starts its checks, as
   on a first run.

**open** keeps two guarantees, of different strength.

The refusal holds for what **open** observed. Just before it writes the branch, it lists the
pull requests GitHub reports open. While one of them is from a branch `release/v<version>-…` of
this repository, for the version it derived, it writes the refusal to its job summary, which
says to close that pull request first and then run the workflow again, writes no reference and
fails. `Regula.Release.releasePulls` selects those pull requests: exactly the ones whose head is
a branch `pullBranch` names for that version (`mem_releasePulls`, `isPullHead_iff`), so every
branch **open** creates for it is among them. `branchAction` is the decision over them: it
creates the branch exactly when there is none (`branchAction_create_iff`) and otherwise refuses,
naming the first (`branchAction_refuse_iff`). `branchStep`, the program the step runs on what it
observed, is then exactly the refusal that names one of them (`branchStep_open`); with none it
is the creation (`branchStep_unopened`). The observation is GitHub's, and GitHub offers no
creation conditional on it, so the refusal does not exclude a release pull request opened
between the observation and the creation: two release pull requests for the version are then
open, and the earlier build's is to be closed.

That no run moves a branch that exists holds by construction, whatever was observed and
whenever a pull request was opened. A run that does not refuse creates the branch
`release/v<version>-<commit>`, named after the commit it names (`Regula.Release.pullBranch`),
with GitHub's request that creates a reference, which GitHub refuses when a reference of that
name exists. That request is the step's only write of a branch (`createUnopened`,
`createBranch`): the step has no request that updates one. Two builds of a release have the same
branch only when they are the same commit (`pullBranch_inj`), and then the request is refused.
That GitHub refuses to create a reference that exists is GitHub's behaviour: trusted, not
proved.

The repository deletes the branch of a pull request that merges (a setting that is on). A
branch whose pull request is never opened, or is closed without merging, stays until a
maintainer deletes it.

The reason is the rules of `main`, which set `require_extra_approval_for_unattributed_changes`:
a push by the workflow to the branch of an open pull request left that pull request blocked
pending an approving review, although every required check had passed on its new head, and the
`pull_request` runs that push started waited for approval
([#234](https://github.com/rbeauchamp/regula/issues/234)). A pull request opened after its
branch was written, as on a first run, was not blocked, and its checks started when it was
opened. The `open` job has `contents: write`, and `pull-requests: read` for the listing; it has
no `actions` permission.

### Reservoir

[Reservoir](https://reservoir.lean-lang.org), the Lean package index, lists a public, non-fork
GitHub repository with a root `lake-manifest.json` and an OSI-approved license that GitHub
recognizes once the repository has at least two stars, or when Reservoir's maintainers register
it. It reads the package's description, keywords, homepage and license from the package
configuration (`lake reservoir-config` prints them), and refreshes about daily.

Reservoir takes a package's version tags from the `versionTags` of `lake reservoir-config` on the
default branch (by default every tag that starts with `v` and a digit), checks out each, and
indexes it with the `version` that tag's own `lake reservoir-config` reports, `0.0.0` when its
lakefile declares none; it orders the versions by that version (lexicographic in major, minor
and patch), then by commit date, newest first, and shows a `0.0.0` version as belonging to no
version track. Lake, resolving a `require` by version range from Reservoir, takes the first
version in that order that the range matches.

So Reservoir indexes `v4.34.0`, whose lakefile declares no version, as `0.0.0`, below every
own-numbered release, and no `versionTags` pattern is needed to exclude it: the tag is
immutable, every later release declares its version (`agree`), and `Regula.Release.admits_lake`
proves that Lake's order of the declared versions puts every admitted release above every listed
one. That Reservoir behaves so is an observation of its source at
[`a5774ea`](https://github.com/leanprover/reservoir/tree/a5774ea3b51fef4a496f35c791cfa660c914454f/scripts)
(`testbed-analyze.py`, `testbed-save.py`, `utils/manifest.py`) and of Lake 4.34.0's
(`Lake/CLI/Main.lean`, `Lake/Load/Materialize.lean`), not a guarantee.
Git requires such as `rev = "v0.2.0"` name the tag directly and involve no version order.

[RG1001]: https://rbeauchamp.github.io/regula/dev/rules/RG1001/
[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
[RG1006]: https://rbeauchamp.github.io/regula/dev/rules/RG1006/
[RG1007]: https://rbeauchamp.github.io/regula/dev/rules/RG1007/
[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG1009]: https://rbeauchamp.github.io/regula/dev/rules/RG1009/
[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/
[RG2005]: https://rbeauchamp.github.io/regula/dev/rules/RG2005/
[RG2006]: https://rbeauchamp.github.io/regula/dev/rules/RG2006/
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
