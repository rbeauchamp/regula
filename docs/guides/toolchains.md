# Development toolchains

Regula keeps one exact compiler version and source commit per checker revision. The stable
default remains Lean 4.34.0. A version such as `4.36.0-pre` identifies many compiler builds;
it is insufficient to select compatible checker code. `RegulaPolicy.Compiler` is the shared
identity used by the cold Lake guard, compiled probe, inventory admission, and plan admission.

## Prepare an isolated candidate

Start in a clean, committed Regula checkout. Install the desired release candidate or nightly
with Elan first. For a local Lean build, register its complete toolchain directory:

```sh
elan toolchain link lean-issue /absolute/path/to/lean4/build/release/stage1
lake exe toolchain prepare lean-issue /absolute/path/to/new-regula-candidate
```

For an installed release candidate, substitute its full selector, for example
`leanprover/lean4:v4.35.0-rc3`. The command probes the selected compiler for its version and
full commit, creates a detached Git worktree from the current commit, changes only the
compiler declaration, its candidate marker and `lean-toolchain`, and commits the candidate. It never installs a
toolchain, changes the caller's branch, or overrides the stable guard. The new worktree is
retained for inspection, source adaptation, and ordinary Git worktree management.

If the candidate needs source changes, make them in a feature branch, review and commit them,
and run `prepare` from that clean revision into a new directory. Keep changes that work on
stable Lean on the main development branch; keep incompatible adaptations on a compatibility
revision. Preparation does not declare that either revision supports the new compiler.

## Qualify that exact revision

From the original Regula checkout:

```sh
lake exe toolchain qualify /absolute/path/to/new-regula-candidate
```

This runs an ordinary-invocation refusal control and existing core checker campaigns: build, fixture policy,
producer boundaries, history, structural checks, execution checks, lint dispatch, and the
operational self-audit. Each command has its own external 420-second limit. These are separate
diagnostics, not partitions of repository acceptance. The immutable candidate commit and
compiler identity are checked before and after commands. Logs and `qualification.json` are in
the candidate's `.lake/regula-toolchain/` directory. A prior receipt is invalidated before any
probe or process begins. Build failure stops dependent campaigns; other failures remain in
the receipt. A failure, timeout, missing command, or changed input prevents completion.

The receipt has `grantsSupport: false`, including when all its campaigns complete. Ordinary
candidate audit commands refuse. The driver selects the explicit diagnostic purpose
(`REGULA_COMPILER_QUALIFICATION=1`) for its children; this does not enable supported PASS
results. Candidate result files have an outer `status: unsupported`, `purpose:
compiler-qualification`, and `grantsSupport: false`, with the detector result under
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
used to elaborate the fix. A fix normally targets Lean's current development branch; an issue
should still name the released compiler on which the defect was observed. These may need
different Regula revisions and evidence. Record both identities rather than substituting one.

Require the selected checker revision in the audit project and run the normal `regula doctor`
and `lake lint` workflow. The audit needs its own claimed surfaces and implementation-linked
contracts. In particular, a theorem about a separately written Lake model does not verify the
Lake implementation. Checker qualification establishes only its exercised detector behavior.

## Guarantees and trusted boundaries

`Compiler.accepts_iff` connects the executed identity guard to the admission predicate;
`refuses_other_commit` rejects every other commit even with the same version, and
`transcript_plan_compiler` binds admitted transcripts to the plan's identity. The actual
`parseIdentity` and `complete` functions have contracts proving valid parsed identities and
complete, ordered campaign observations meeting each required exit and output. These are kernel-checked statements about
supplied values. They do not authenticate compiler binaries or Git commits, prove subprocess
behavior, establish detector completeness, or prevent a filesystem change-and-restore race.
Compiler self-reports, Elan resolution, Git, native compilation, JSON serialization, process
exit observations, filesystem reads, and GNU timeout remain trusted operational mechanisms.
