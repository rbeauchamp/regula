# Development toolchains

Regula keeps one exact compiler version and source commit per checker revision. The stable
default remains Lean 4.34.0. A version such as `4.36.0-pre` identifies many compiler builds;
it is insufficient to select compatible checker code. `RegulaPolicy.Compiler` is the shared
identity used by the cold Lake guard, compiled probe, inventory admission, and plan admission.

**Status.** This is the first, partial delivery of
[#191](https://github.com/rbeauchamp/regula/issues/191): the identity policy, the preparation
and qualification workflow, and the refusals are in place, but no checker revision is
qualified for a compiler newer than Lean 4.34.0. Until the work tracked by
[#192](https://github.com/rbeauchamp/regula/issues/192),
[#193](https://github.com/rbeauchamp/regula/issues/193) and
[#195](https://github.com/rbeauchamp/regula/issues/195) is reviewed and a compatibility
revision is promoted, code elaborated with a newer compiler cannot receive a supported result.

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

For an installed release candidate, substitute its full selector, for example
`leanprover/lean4:v4.35.0-rc3`. The command probes the selected compiler for its version and
full commit, creates a detached Git worktree from the current commit, changes only the
compiler declaration, its candidate marker and `lean-toolchain`, and commits the candidate.
It refuses a selector that names no toolchain `elan toolchain list` prints, a release channel
such as `stable` included, so it
never installs a toolchain, changes the caller's branch, or overrides the stable guard. The
new worktree is retained for inspection, source adaptation, and ordinary Git worktree
management.

If the candidate needs source changes, make them in a feature branch, review and commit them,
and run `prepare` from that clean revision into a new directory. Keep changes that work on
stable Lean on the main development branch; keep incompatible adaptations on a compatibility
revision. Preparation does not declare that either revision supports the new compiler.

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
(`REGULA_COMPILER_QUALIFICATION=1`) for its children; this does not enable supported PASS
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

Select a reviewed Regula compatibility revision whose declared identity matches the compiler
used to elaborate the fix. None exists yet for a compiler newer than Lean 4.34.0 (see the
status above). A fix normally targets Lean's current development branch; an issue
should still name the released compiler on which the defect was observed. These may need
different Regula revisions and evidence. Record both identities rather than substituting one.

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
on this branch: the shared documentation labels, compiler-specific LRAT generation, the cold
guard's binding to the running compiler, the identity probe, and `doctor`'s check of the
project's pin. No receipt exercised those paths, so the final source remains unqualified on
both newer compilers and these observations add neither to the supported stable release.

| Campaign | Lean 4.35.0-rc3, candidate `3fc295b` | Lean `6751f97`, candidate `d0e9e3c` |
| --- | --- | --- |
| `build` | met | met |
| `candidate-refusal` | met | met |
| `fixtures` | not met: removed legacy compiler axiom, obsolete LRAT bytes ([#192](https://github.com/rbeauchamp/regula/issues/192)) | not met: the same legacy axiom and LRAT controls, and controls over `ctorIdx._impl` ([#193](https://github.com/rbeauchamp/regula/issues/193)) |
| `producers` | met | not met: `uncaught exception: declaration documentation` after the RG5001 controls passed; cause unknown ([#195](https://github.com/rbeauchamp/regula/issues/195)) |
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
version and commit that compiler reports with the supported identity, so two selectors of one
compiler agree and an override cannot hide a project pinned to another. LRAT qualification
setup now generates separate direct and grind certificates with the selected compiler before
checking them.

The release candidate's initial campaign completed build, ordinary refusal, producer, history,
structural, execution, lint-driver and operational self-audit controls. Its fixture campaign
failed on the removed legacy compiler axiom and obsolete LRAT certificate bytes. The legacy
fixture and the compiler-trust policy need the capability-aware port tracked by
[#192](https://github.com/rbeauchamp/regula/issues/192), including refusal of dependency spoofs
when those builtin names no longer exist. A native-proof control is not a replacement for
that retired direct-axiom control.

The development compiler also generates unsafe `ctorIdx._impl` declarations outside the
standard's current recursion-helper exception. They cause genuine positive controls to be
refused. [#193](https://github.com/rbeauchamp/regula/issues/193) tracks separate authentication
against Lean's generator, its precise policy and execution boundaries, and the
`replacement-cycle` control that stops in compilation. Its producer campaign stopped with
`uncaught exception: declaration documentation` after the RG5001 controls passed. The RG5002
fixtures that follow declare no inductive type, so that failure is not attributed to the
constructor-index helpers; its cause is unknown and
[#195](https://github.com/rbeauchamp/regula/issues/195) tracks it separately. Preserve these
failures until the required ports and review are complete; compiling the checker or
completing a subset of diagnostics does not qualify it.

## Guarantees and trusted boundaries

`Compiler.accepts_iff` connects the executed identity guard to the admission predicate;
`refuses_other_commit` rejects every other commit even with the same version, and
`transcript_plan_compiler` binds admitted transcripts to the plan's identity. The actual
`parseIdentity` and `complete` functions have contracts proving valid parsed identities and
complete, ordered campaign observations meeting each required exit and output.
`Regula.Setup.toolchainIssues_eq_nil_iff` proves that `doctor`'s decision reports no toolchain
issue exactly when the project's pin resolved to a compiler whose reported identity
`Compiler.Supports`; a pin that resolves to no installed compiler is an issue.
`installedName?_spec` proves that `prepare`, `qualify` and `doctor` give `elan run` only a
name among those `elan toolchain list` printed, spelled as the selector or as its release
name; Elan would install any other known release. These are
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

Compiler self-reports, Elan's listing, naming and resolution, Git, native compilation, JSON serialization, process
exit observations, filesystem reads, and GNU timeout remain trusted operational mechanisms.
