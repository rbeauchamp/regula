# Development toolchains

Regula keeps one exact compiler version and source commit per checker revision. The stable
default on `main` remains Lean 4.34.0. This adaptation selects source commit
`6751f97b0c3dbefec2aaf1ce9e07b877101c5662`. A version such as `4.36.0-pre` identifies many compiler builds;
it is insufficient to select compatible checker code. `RegulaPolicy.Compiler` is the shared
identity used by the cold Lake guard, compiled probe, inventory admission, and plan admission.

**Status.** The reusable workflow and portable compatibility changes for
[#191](https://github.com/rbeauchamp/regula/issues/191) are implemented. These include the
capability-aware compiler-trust policy ([#192](https://github.com/rbeauchamp/regula/issues/192)),
constructor-index authentication ([#193](https://github.com/rbeauchamp/regula/issues/193)),
documentation fixture repair ([#195](https://github.com/rbeauchamp/regula/issues/195)) and
source dependency provisioning ([#201](https://github.com/rbeauchamp/regula/issues/201)).
A compatibility revision is ready for use only after its source adaptations and candidate
promotion have been reviewed, complete ordinary and documentation acceptance and applicable
qualification have passed, and all required checks are green at that exact checker commit.
Select the compiler and checker revision together. A qualification receipt or candidate
marker alone does not establish support.

## Prepare an isolated candidate

Start in a clean, committed Regula checkout. Install the desired release candidate or nightly
with Elan first. A compiler's identity is the version and commit it reports about itself, and
Lean records the Git commit of its source tree with no marker for uncommitted changes.
Build a local compiler from a clean, committed Lean tree: two builds of one commit with
different uncommitted edits report the same identity, and nothing here tells them apart.
Register the build's complete toolchain directory:

```sh
elan toolchain link lean-issue /absolute/path/to/lean4/build/release/stage1
lake exe toolchain prepare lean-issue /absolute/path/to/new-regula-candidate
```

For an installed release candidate, substitute its name exactly as `elan toolchain list` prints
it, for example `leanprover/lean4:v4.35.0-rc3`. The command probes the selected compiler for its
version and full commit and legacy compiler-trust capability, creates a detached Git worktree from the
current commit, changes only the compiler declaration, capability, candidate marker and
`lean-toolchain`, and commits the candidate.
It refuses a selector unless `elan toolchain list` prints exactly that name; it resolves no channel
such as `stable` and completes no shorter spelling, so it never installs a toolchain, changes
the caller's branch, or overrides the stable guard. The new worktree is retained for inspection,
source adaptation, and ordinary Git worktree management.

The capability probe executes the same isolated Core observer used by the checker. It accepts
only the complete legacy axiom family with the expected types and origins, or all three names
absent. Each report carries the observation, and admission requires agreement with the compiled
policy. On a compiler that removed the family, recreating a retired name in project or dependency
code cannot give it compiler trust. The qualification receipt retains the observed capability
alongside the exact version and commit.

The [RG5002] qualification fixture has no whitespace between its final documentation character
and the closing delimiter. Lean's newer Markdown parser stores that whitespace as source
information instead of documentation text; the older parser retained it in the string. This
fixture therefore gives both parsers the same complete documentation value, which the producer
oracle still compares exactly. The theorem and Fixed/Violation/restored Fixed controls are
unchanged ([#195](https://github.com/rbeauchamp/regula/issues/195)).

If the candidate needs source changes, make them in a feature branch, review and commit them,
and run `prepare` from that clean revision into a new directory. Keep changes that work on
stable Lean on the main development branch; keep incompatible adaptations on a compatibility
revision. Preparation does not declare that either revision supports the new compiler.

### Build dependencies with the selected compiler

Full repository acceptance also needs coherent Mathlib, Verso and transitive pins in the
`audit/` and `website/` packages. All five `lean-toolchain` files must name the selected
compiler: the root, `audit/`, `website/`, `examples/build-lint/` and
`examples/lake-lint-toml/`. Upstream artifacts are usable only when their compiler matches. For a development
commit without matching artifacts, set `dependency-build-mode` to `source` in the adaptation
and run `./scripts/provision.sh`, then `lean --run lean/RegulaProvision.lean verso`.
An interrupted source setup retains its staging directory. A later invocation resumes only
when its compiler/mode/policy key, pre-build artifact-policy marker, Lake configuration,
manifest, toolchain selector and generated import module match exactly, and its existing
package checkouts retain their pinned origins and commits, without working-tree edits, stashes
or additional local branch work. A matching stage that fails those package checks, such as one
an interrupted clone left without a checked-out revision, is reported and left untouched; another
admissible stage is resumed, or else a new one is created. Unknown stages and local changes are
preserved. It still completes the requested transitive dependency build before publishing the
read-only store. A setup timeout remains a failed invocation. Finish setup before running
acceptance; this does not divide either acceptance step or change its deadline.
The source plan disables Lake and Mathlib cache downloads; shared receipts and CI keys
distinguish its artifacts by compiler commit and mode. See
[dependency provisioning](contributing.md#share-one-mathlib-across-local-copies) for the
entry points and trusted effects. Pin selection and a successful setup do not establish
checker qualification or repository acceptance.

### Reproduce a source compiler in CI

An adaptation using a local Elan alias also commits `.github/compiler-source.json`:

```json
{
  "owner": "rbeauchamp",
  "repository": "lean4",
  "revision": "6751f97b0c3dbefec2aaf1ce9e07b877101c5662",
  "selector": "regula-lean4-6751f97",
  "bootstrap": "leanprover/lean4-nightly:nightly-2026-10-01",
  "bootstrapRevision": "77f336f7ae6a60419d3882e0d5ca7ac3a2155528"
}
```

The alias must match `lean-toolchain` and the artifact mode must be `source`.
`lean/RegulaCompiler.lean` checks the specification, obtains the exact source commit,
installs the bootstrap unless Elan already lists it, checks the bootstrap's CLI and library identity, configures Lean's release preset with
that preceding stage, and runs the documented `make -j… -C build/release` command.
It checks both identities of the resulting compiler before linking the alias. An existing
alias is reused only when both reports match; a mismatch is refused. Source and build
directories remain under `~/.cache/regula-compilers` for inspection or resumption.
Before a fresh Linux CI build, the Lean installer installs the compiler toolset and
development packages for GMP, LibUV and OpenSSL through Apt. CMake enforces the source
revision's library requirements. Other environments must provide those prerequisites.
The proved package-installation predicate requires both `GITHUB_ACTIONS=true` and
`RUNNER_OS=Linux`; these environment observations and Apt's effects remain trusted.

CI first runs the reusable compiler preparation job, then restores that compiler in the
existing check jobs. Its cache key includes the specification, selector and installer
source. The required `verify` and `title` checks, the rule-example shards and the dogfood jobs
follow that job only for its cache and start whatever its result, so a failed or cancelled
preparation cannot leave them skipped, which GitHub reports as success: after a failed
preparation each runs its own provisioning and checks, and on a cancelled run its steps do not
pass, so it reports cancelled. In the diagnostics workflow `applies` runs only once preparation
succeeded, so a failed or cancelled preparation fails the required `diagnostics` gate. The shell
bootstrap installs fixed Lean 4.34.0 to run this Lean installer even when the repository's
compiler is not installed yet. With no source specification, the installer asks Elan for the
committed official release or dated nightly unless Elan already lists it, and then runs that
compiler.
Compiler preparation does not establish checker support. The existing acceptance and
diagnostic commands keep their deadlines, and their results must still pass at the
reviewed revision. Compiler self-reports, the build tools, cache storage and filesystem
effects remain trusted; the identity predicate proves agreement of supplied values.

## Qualify that exact revision

From the original Regula checkout:

```sh
lake exe toolchain qualify /absolute/path/to/new-regula-candidate
```

This runs an ordinary-invocation refusal control and existing core checker campaigns: build,
fixture policy, producer boundaries, history, structural checks, execution checks, lint
dispatch, and the operational self-audit. Each command has its own external 420-second limit. These are separate
diagnostics, not partitions of repository acceptance. The immutable candidate commit and
compiler identity are checked before and after commands. Logs and `qualification.json` are in
the candidate's `.lake/regula-toolchain/` directory. A prior receipt is invalidated before any
probe or process begins. Build failure stops dependent campaigns; other failures remain in
the receipt. A failure, timeout, missing command, or changed input prevents completion.

The receipt has `grantsSupport: false`, including when all its campaigns complete. On a
candidate, an ordinary invocation of `axiomGate` (so also the audit `lake lint` runs),
`docFenceAudit` or `freshChecker` refuses. The other executables do not call that guard
themselves, among them `regula` (`doctor`, `init` and the offline guidance commands),
`ruleExamples`, `toolchain`, `qualify` and `checkerSelftest`: whatever they print on a
candidate is unqualified. The driver selects the explicit diagnostic purpose
(`REGULA_COMPILER_QUALIFICATION=1`) for every campaign except `candidate-refusal`, which it runs
with that variable cleared to observe the ordinary refusal; this does not enable supported PASS
results, and a diagnostic run that accepts its controls still exits 0, so an exit status alone
never distinguishes a diagnostic observation from a supported result. Candidate result files
have an outer `status: unsupported`, `purpose: compiler-qualification`, and
`grantsSupport: false`, with the detector result under
`observation`. Their text labels accepted controls as diagnostic observations. Only diagnostic
readers in that candidate invocation unpack the observation; ordinary readers refuse it.
These results cannot establish that an unrelated Lean fix conforms. Mathlib, the Verso standard,
website examples, editor interactions, serialized graphs, and additional adopter paths need
their own applicable qualification before a revision claims those capabilities.

Review the actual source adaptations and affected standard checklist rows before promoting a
compatibility revision and changing its compiled candidate marker to false. That is a reviewed
source change, not a receipt import or runtime override. Run complete repository acceptance and required CI under the declared
dependency pins for a release. Do not point a stable release at a newer compiler merely because
these core campaigns succeeded. When a compiler or checker changes, reuse evidence only for
claims whose relevant source, dependencies, compiler identity, and invocation path are unchanged.

## Use it for a Lean fix

Select a reviewed and qualified Regula compatibility revision whose declared identity matches
the compiler used to elaborate the fix. A fix normally targets Lean's current development
branch; an issue should still name the released compiler on which the defect was observed.
These may need different Regula revisions and evidence. Record both identities rather than
substituting one.

Require the selected checker revision in the audit project and run the normal `regula doctor`
and `lake lint` workflow. The audit needs its own claimed surfaces and implementation-linked
contracts. In particular, a theorem about a separately written Lake model does not verify the
Lake implementation. Checker qualification establishes only its exercised detector behavior.

## Initial compatibility observations

The workflow was exercised while implementing [#191](https://github.com/rbeauchamp/regula/issues/191)
against Lean 4.35.0-rc3 (`470d5ce1400764999581fd26d5d72b00d990b0f4`) and the local Lean development
build at `6751f97b0c3dbefec2aaf1ce9e07b877101c5662`. The release-candidate receipt covers checker
candidate `3fc295bc179835ad19505fcde016b7b0888b4a3c`, prepared from
`09f030381119fc57e217863b58748feb158ba1fa`. The development receipt covers checker candidate
`d0e9e3c650de78dc420d2b558a8a10a05824c2e7`, prepared from
`16fba8111c4861bd6483b04c0367b835a1b1eb68`. Both built Regula and remained **unqualified**;
their ordinary audit commands refused. The candidate commits and their receipts and logs are
local to the machine that ran them and are not published. The receipts predate later changes
on this branch: the #192, #193 and #195 repairs, the shared documentation labels,
compiler-specific LRAT generation, the cold
guard's binding to the running compiler, the identity probe, and `doctor`'s check of the
project's pin. No receipt exercised those paths, so these historical observations establish
neither support for this revision nor an extension to the supported stable release.

| Campaign | Lean 4.35.0-rc3, candidate `3fc295b` | Lean `6751f97`, candidate `d0e9e3c` |
| --- | --- | --- |
| `build` | met | met |
| `candidate-refusal` | met | met |
| `fixtures` | not met: removed legacy compiler axiom, obsolete LRAT bytes ([#192](https://github.com/rbeauchamp/regula/issues/192)) | not met: the same legacy axiom and LRAT controls, and controls over `ctorIdx._impl` ([#193](https://github.com/rbeauchamp/regula/issues/193)) |
| `producers` | met | not met: `uncaught exception: declaration documentation` after the [RG5001] controls passed; cause unknown ([#195](https://github.com/rbeauchamp/regula/issues/195)) |
| `history` | met | met |
| `structural` | met | not met: fresh gates refused over `ctorIdx._impl` (#193) |
| `execution` | met | not met: correspondence controls refused over `ctorIdx._impl`, and `replacement-cycle` stops in compilation (#193) |
| `lint-driver` | met | met |
| `self-audit` | met | met |

Each cell is the receipt's `observationMet` for that campaign, with the cause its log shows.
These are historical results for those two candidate commits, not for this revision.

The portable changes preserve Lake's path-dependency `copy` flag during relocation, inspect
loaded dependency locations, avoid the newly reserved binder name `given`, and use generated
structural equality where Lean no longer offers its former safe generic pointer shortcut.
Whichever instance a compiler elaborates decides the same proposition, as every `Decidable`
instance of it does; `snapshotDecidableEq_eq` and `claimCandidateDecidableEq_eq` state only
that, and say nothing about which implementation was compiled or what it costs. `regula
doctor` asks Elan for the compiler the project's own `lean-toolchain` selects and compares the
version and commit that compiler reports with the supported identity, so two installed names of one
compiler agree and an override cannot hide a project pinned to another. LRAT qualification
setup now generates separate direct and grind certificates with the selected compiler before
checking them.

Those failures motivated the portable changes now present in this revision. The capability
policy preserves refusal of dependency spoofs when the legacy builtin names are absent; a
native-proof control does not replace the retired direct-axiom control. Constructor-index
helpers are authenticated against Lean's generator under their own declaration policy, while
their unsafe and runtime-replacement execution boundaries remain visible. The
`replacement-cycle` control now reaches the detector through compiler-compatible construction.
The [RG5002] failure is attributed to the changed documentation parser behavior described above
by reading the producer's exact documentation check, not by a rerun.
The original failures remain historical evidence; compatibility use requires qualification
of these repairs at the selected checker revision.

## Guarantees and trusted boundaries

### Compiler-source account for Lean `6751f97`

At compiler commit `6751f97b0c3dbefec2aaf1ce9e07b877101c5662`,
`ToLCNF.constantReplacer` performs at most one `CSimp.replaceConstant?` lookup per call, and
conversion revisits the resulting expression. This adaptation's standard §7.6 records that
source compiler path; the stable 4.34.0 revision records its own two-stage path. The standard
remains normative. The accepted constant-equality shape and positional universe substitution
are unchanged.

Regula's `simplificationCandidates` recognizes every declaration of that equality shape,
and `executionWalk` enqueues every recognized target before continuing the traversal.
For a completed closure with no unresolved path, induction on chain length therefore
includes every finite chain of those candidate edges, independently of how often the
compiler performs a lookup. This is an argument from the selected compiler and checker
sources, not a machine-checked compiler-completeness theorem. It does not establish that
the compiler chose any particular candidate. A candidate classified as checked still
requires independently kernel-checked correspondence over the complete dependent domain
and universal level parameters. Report mode may retain a reported trusted replacement;
checked mode keeps its stricter requirement. Retained IR, source histories and reached
execution boundaries remain separate obligations.

### Proved decisions and external effects

`Compiler.accepts_iff` connects the executed identity guard to the admission predicate;
`refuses_other_commit` rejects every other commit even with the same version, and
`transcript_plan_compiler` binds admitted transcripts to the plan's identity. The actual
`parseIdentity` and `complete` functions have contracts proving valid parsed identities and
complete, ordered campaign observations meeting each required exit and output.
`Regula.Setup.toolchainIssues_eq_nil_iff` proves that `doctor`'s decision reports no toolchain
issue exactly when the project's pin resolved to a compiler whose reported identity
`Compiler.Supports`; a pin that resolves to no installed compiler is an issue.
`installedName?_spec` proves that the name `selectedLean` gives `elan run`, the path `prepare`,
`qualify` and `doctor` use, is among the names parsed from `elan toolchain list` and equals
the selector, run without Elan's `--install`. These are
kernel-checked statements about supplied values. They do not authenticate compiler binaries
or Git commits, prove subprocess behavior, establish detector completeness, or prevent a
filesystem change-and-restore race.

The supplied identity is a self-report: `Lean.versionString` and `Lean.githash`. It names the
Git commit of the tree a compiler was built from, not the bytes of its executable and not
uncommitted source edits, so every statement here assumes a compiler built from a clean,
committed tree. Nothing checks that hypothesis, and no correspondence between an executable
and its source is claimed.

The cold guard in `lakefile.lean` runs the `lean` that `LEAN_SYSROOT` or `PATH` selects on the
policy source. It passes only when that child accepts its own identity and prints the version
and commit of the Lean elaborating the lakefile; a child that fails, cannot be run, or reports
another identity is refused. Lake reuses an elaborated configuration, so the guard runs when
the configuration is elaborated, and the compiled guards remain in force otherwise. The
retained `lint-driver` control gives the guard, through an inherited `LEAN_SYSROOT`, two
children that are not the running compiler: one that fails on the policy source, and one that
exits successfully without printing the running compiler's identity. Each is refused on its
own branch, the second by the identity comparison, and the same package then loads again.
Neither child is a compiler; a compiler of another identity as the child, or as the Lean
running Lake, has no retained control.

Compiler self-reports, Elan's listing and resolution, Git, native compilation, JSON serialization, process
exit observations, filesystem reads, and GNU timeout remain trusted operational mechanisms.

[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
