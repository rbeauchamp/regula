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
full commit and legacy compiler-trust capability, creates a detached Git worktree from the current commit, changes only the
compiler declaration, capability, candidate marker and `lean-toolchain`, and commits the candidate. It never installs a
toolchain, changes the caller's branch, or overrides the stable guard. The new worktree is
retained for inspection, source adaptation, and ordinary Git worktree management.

The capability probe executes the same isolated Core observer used by the checker. It accepts
only the complete legacy axiom family with the expected types and origins, or all three names
absent. Each report carries the observation, and admission requires agreement with the compiled
policy. On a compiler that removed the family, recreating a retired name in project or dependency
code cannot give it compiler trust. The qualification receipt retains the observed capability
alongside the exact version and commit.

The RG5002 qualification fixture has no whitespace between its final documentation character
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
`audit/` and `website/` packages, with all three `lean-toolchain` files naming the selected
compiler. Upstream artifacts are usable only when their compiler matches. For a development
commit without matching artifacts, set `dependency-build-mode` to `source` in the adaptation
and run `./scripts/provision.sh`, then `lean --run lean/RegulaProvision.lean verso`.
An interrupted source setup retains its staging directory. A later invocation resumes only
when its compiler/mode/policy key, pre-build artifact-policy marker, Lake configuration,
manifest and toolchain selector match exactly. Existing package checkouts must retain their
pinned origins and commits, without working-tree edits, stashes or additional local branch
work. Unknown stages and local changes are preserved. It still runs the complete dependency
build before publishing the read-only store. A setup
timeout remains a failed invocation. Finish setup before running acceptance; this does not
divide either acceptance step or change its deadline.
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
checks the bootstrap's CLI and library identity, configures Lean's release preset with
that preceding stage, and runs the documented `make -j… -C build/release` command.
It checks both identities of the resulting compiler before linking the alias. An existing
alias is reused only when both reports match; a mismatch is refused. Source and build
directories remain under `~/.cache/regula-compilers` for inspection or resumption.

CI first runs the reusable compiler preparation job, then restores that compiler in the
existing check jobs. Its cache key includes the specification, selector and installer
source. The shell bootstrap installs fixed Lean 4.34.0 to run this Lean installer even
when the repository's compiler is not installed yet. With no source specification, the
installer asks Elan for the committed official release or dated nightly.
Compiler preparation does not establish checker support. The existing acceptance and
diagnostic commands keep their deadlines, and their results must still pass at the
reviewed revision. Compiler self-reports, the build tools, cache storage and filesystem
effects remain trusted; the identity predicate proves agreement of supplied values.

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

## Initial compatibility observations

The workflow was exercised while implementing [#191](https://github.com/rbeauchamp/regula/issues/191)
against Lean 4.35.0-rc3 (`470d5ce1400764999581fd26d5d72b00d990b0f4`) and the local Lean development
build at `6751f97b0c3dbefec2aaf1ce9e07b877101c5662`. The release-candidate receipt covers checker
candidate `3fc295bc179835ad19505fcde016b7b0888b4a3c`, prepared from
`09f030381119fc57e217863b58748feb158ba1fa`. The development receipt covers checker candidate
`d0e9e3c650de78dc420d2b558a8a10a05824c2e7`, prepared from
`16fba8111c4861bd6483b04c0367b835a1b1eb68`. Both built Regula and remained **unqualified**;
their ordinary audit commands refused. These receipts predate the final documentation-label
and LRAT changes described below. The final source remains unqualified on both newer compilers;
these observations do not add either compiler to the supported stable release.

The portable changes preserve Lake's path-dependency `copy` flag during relocation, inspect
loaded dependency locations, avoid the newly reserved binder name `given`, compare actual
compiler identities in `doctor`, and use generated structural equality where Lean no longer
offers its former safe generic pointer shortcut. The two equality instances have pointwise
contracts proving that they decide the same equality. LRAT qualification setup now generates
separate direct and grind certificates with the selected compiler before checking them.

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
against Lean's generator, its precise policy and execution boundaries, and the remaining
development-compiler controls. Preserve these failures until the required port and review
are complete; compiling the checker or completing a subset of diagnostics does not qualify it.

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
