# Proofs and boundaries

This guide tells what the implementation of Regula proves, what it observes and what it trusts. The [architecture](architecture.md) gives the structure. The [specification of the smaller Regula](../../specification/README.md) gives the closed input and the rules.

The guide keeps three kinds of evidence apart:

- **Proved:** a kernel-checked theorem about the definition that the checker executes. Its quantifiers range over supplied Lean values, not over external executions.
- **Observed:** a run of a program on the pinned toolchain. It is an observation, not evidence for a universal claim.
- **Trusted:** the supported Lean compiler and process, Lake, the filesystem, Git, GNU timeout and the imported libraries.

No proof of this guide verifies the Lean compiler, Lake, the filesystem or the intended specification of a user.

The root [foundation manifest](../../foundation_manifest.json) has the foundation claims of the libraries. The checker reports each declaration of a claimed module that depends on an axiom outside its profile. The build of the excluded `Regula` library has warnings as errors, so the kernel checks its theorems, and `warningAsError` also refuses `sorry`.

## The checker of a finished build

`lake lint` runs the checker of Regula, the `lint` executable (`Regula.LintMain`). The checker has three effects. It loads the finished build, it prints its findings, and it sets its exit code. The checker writes no file and removes no file. It starts itself again once, in an environment that isolates Git (`Regula.GitIsolation`). The load of the workspace by Lake can start processes, as `lake build` can.

The checker does not build the project. Build the claimed targets with `lake build --wfail` first. A module without its compiled files makes the run INCOMPLETE.

The checker reads one closed input (`Regula.Closed.Input` in `Regula.Input`). The loader `Regula.Load` fills each part of it through the interface of its owner:

| Part | Interface |
| --- | --- |
| The targets of the root package, with their modules, options and extra Lean arguments | The load of the workspace by Lake |
| The claim | `foundation_manifest.json`, read by `Regula.Checker.Manifest.parse` |
| The imports of each module of the root package that Lake builds, and its extensions with entries | `Lean.readModuleDataParts` |
| The constants of each environment that the checker loads | `Lean.importModules` with `loadExts := false` |
| The compiled code of each constant, and its departures from the kernel value | `Lean.IR.findEnvDecl`, and the module entries of `implemented_by` and `csimp` |

The input has no source text, message, info tree, option set in source, build log or list of files. A rule does not decide what it cannot read in this input.

### Refusal

The checker refuses an input that does not have the closed form. The verdict is then INCOMPLETE ([RG2001]), not a pass. These are the conditions of the closed form:

- Lake loads the workspace, and the claim parses. The claim claims no target as `compiler-trusting`.
- Each module of a target has its `.olean` files in the build of the root package, and Lean reads them. A read error is a refusal, not an absent file.
- Lean loads each environment.
- For an implicit workspace, the current directory is the workspace that Lake dispatched (`Regula.Load.dispatchedFrom_iff`).
- In each environment, each name is the name of one constant. Each constant that a constant mentions is loaded.
- Each module of each target is loaded in one of the environments.
- The claim claims at least one target.

The functions `Regula.Closed.Input.refusal?` and `Regula.Closed.Bundle.refusal?` decide the last three conditions.

### Environments

One environment cannot hold two modules that declare one name, for example the `main` of two programs. Thus the checker loads the root of each executable in an environment of its own. It puts the other modules of the libraries in as few environments as hold them.

The checker loads the environments one after the other. Before it loads the next environment, it copies the input out of the data of the last one. Then it frees that data (`Environment.freeRegions`). Thus the memory of a run is that of one environment.

### Trusted interfaces

The loader reads each part through the interface of its owner. These statements are trusted, not proved:

- The load of the workspace by Lake gives the targets, their modules and the options that Lake builds with.
- `LEAN_SYSROOT` names the toolchain that Lake runs. `lake lint` and `lake exe` set it.
- Lake supplies the search path that `Regula.Load.dispatchedFrom_iff` describes. Distinct packages do not share a library directory, and no package uses Lake's library directory.
- Lean finds the library of the toolchain only below the `lib/lean` directory of the pinned toolchain ([RG1003]).
- Lean refuses an `.olean` file that a different version of Lean wrote ([RG2001]).
- `Lean.importModules` with `loadExts := false` loads exactly the constants of the `.olean` files. It sets the module entries of each extension, and it builds no state of an extension.
- The executable runs the code that the build records ([RG3001], [RG3002]).

### The rules

Each kept rule is a function from the closed input to the subjects that it reports (`Regula.Rules`). The [specification](../../specification/README.md) states the violation predicate of each rule. Leaf #487 proves that each function reports a subject exactly when the subject violates its rule. Until then, no theorem relates a function to its predicate.

Lean's own tools decide two rules. [RG2003] is `lake build --wfail`, and [RG2005] is `lake check`. The gate of this repository builds with warnings as errors. Leaf #482 adds `lake check` to the gate.

The option allowlist of [RG2006] is the set of options that the previous checker accepted, until leaf #484 sets its members.

## The acceptance boundary

The acceptance of this repository has two steps, `./scripts/verify.sh` and `./scripts/verify.sh docs`. Each step has a deadline of 420 seconds.

The first step makes a copy of the checkout. In the copy, it builds each claimed target, the checker and the acceptance tools, with warnings as errors. Then it runs the registry checks and builds the specification package. Last, it runs the checker (`lake lint`) on the build of the copy. If all commands pass, it records the SHA-256 of each file of the copy.

The second step refuses to start unless the files of a new copy have the recorded digests. It does the same check again after its last command. It checks the Markdown documents, builds the `audit/` package and runs the checker on it, and builds, renders and checks the Verso standard.

These statements are trusted, not proved: `shasum` and the filesystem report the contents of the files, and no other process writes the record.

## Project setup and releases

**Proved** (`RegulaCore.Setup`, over the observation `regula init` and `regula doctor` read):
`plan_idempotent`, applying `init`'s plan leaves an empty plan, so a second run writes nothing;
`plan_eq_nil_iff`, the plan is empty exactly when every setup issue is one `init` does not fix;
`issues_run`, the plan removes exactly the fixable issues and adds none. The option check covers
exactly the claimed targets (the root targets the manifest does not exclude, and none while an
existing manifest fails [RG2002]), as [RG2006] does: `run_sets`, every required option a claimed
target built without is then set to its required value as `RegulaPolicy.Community.sets` reads
it, which meets [RG2006]'s requirement on that option (`meets_of_sets`); `resolved_run`, every
claimed target then has a value for every required option or a `-D` candidate of its own extra
`lean` arguments names it; `added_unargued`, no option the plan adds to the package or to a
claimed target's own configuration names an option that a `-D` candidate of that target sets
(the candidates of `RegulaPolicy.Community.argumentSettings`, [RG2006]'s own reading, which
includes every `-D` that `lean` reads only under the command-line assumption stated in
`RegulaPolicy.Community`); `argued_run`, the plan leaves unchanged the required options that
claimed targets set only with such a `-D`, which `doctor` reports once as a setup issue `init`
does not fix, and `arguedBy_run` those of each claimed target; `run_options_unclaimed`, when a
root target is excluded the package's options are unchanged, the options going into each claimed
target's own configuration (`run_plan_targets`), so none reaches an excluded target, and an option
some claimed target's `-D` sets likewise goes only into the configuration of each target that
builds without it; and `run_options_prefix` and `withAdded_prefix`, the options and extra `lean`
arguments the package and each claimed target already give are kept. An edit adds a missing
piece and has no form that replaces a lint driver, an option value or a library's `globs`.
`init` writes a glob in one case only, `Observation.globCase`, and `plan_globs_mem` proves it.
The package has one `lean_lib` with one root, declared at the top level with no `globs`. It is a
`[[lean_lib]]` table, or a `lean_lib` declaration with a `where` block or no fields, not an inline
table. `doctor`
reports a module of the claimed modules' import closure below that root, which neither the library
nor an executable root includes. Each module that the glob adds is in that closure, the claimed
roots included, with the same canonical source file. The glob also adds each module that `doctor`
reports.
`globCase_run` proves that after the plan no glob is left to write. `uncovered_run` proves that
only the entries of that library leave the issues. The glob is the one that `doctor` asks for,
and one definition, `Lakefile.globsSetting`, gives that glob to the two. The starter manifest is
planned exactly when there is no manifest and the package has a `lean_lib` for it to claim
(`plan_manifest_mem`); a package with none has a setup issue `init` does not fix.

**Checked when it runs:** `init` observes the project again after writing and restores every
file it wrote unless the new plan is empty, no library that the plan gave a glob leaves out a
module that `doctor` reports (`uncovered_run`'s executable counterpart), and each claimed target
of both observations, matched by kind and name, sets the same required options only with a `-D`
as before (`arguedBy_run`'s
executable counterpart, which catches an added option that reaches such a target; a target the
new observation does not claim, as while a starter manifest fails [RG2002], is not compared), and it
writes the starter manifest only after `Manifest.parse` reads the text back as exactly that
manifest. That the lakefile edits realize the model's `apply` is not a theorem. The command
checks only these consequences when it runs. That `allClaimed` holds only when the observed
targets are every root `lean_lib` and `lean_exe` is how `observe` builds the observation. The
extra `lean` arguments that it reads are those that Lake gives each target (`weakLeanArgs` and
`leanArgs`). When the project has a manifest, `doctor` also prints the [RG2002] and [RG2006] findings of the
checker. `Regula.Cli.Setup.projectInput` gives their input with no build: the targets that Lake
loads and the claim, read as the checker reads them (`Regula.Load.targets`, `Regula.Load.claim`).
Over this input, `doctor` runs the decision of the checker,
`Regula.Closed.Input.configurationFindings`, with the option allowlist of the checker
(`Regula.Shell.allowed`). It prints each finding in the form of the checker, one line for each.
The required options of a setup issue include the options of Mathlib when the workspace contains
Mathlib. `init` writes them under `weak.`, so a target that imports no Mathlib ignores them. By
`conforming_of_mathlib`, a target that has the options of Mathlib also has the options without
Mathlib. A module below a library root that no library includes can be a failing setup issue. It
is one only when a claimed module (of a library or executable the manifest does not exclude)
reaches it by import through the package's modules. `lake lint` reports such a module under
[RG2004]. Any other
such module is a `note` that does not count toward `doctor`'s exit status. That reachability is
read from import headers, not from a build, and Lake's own lookup `Workspace.findModule?` gives
the file of each import.
`doctor` and `init` refuse a project in which Lake resolves a module of that closure to a source file that does not exist.
The module can be a claimed module or a module that a module of the closure imports.
A build of that module fails when it reads the file (`Module.recFetchInput`).
The message names the module that imports it, or it names the module as a claimed module.
For the glob case, Lake's own glob gives the modules that the glob adds.
`soleDeclared` finds the place of the glob with the walk of the lakefile that writes it. A library
written as an inline table has no such place. Each such
finding states how many modules the library leaves out and names at most
`shownModules` of them, wrapped (`moduleLines`, which prints `moduleSummary`'s names grouped by
`wrapFrom`): `moduleSummary_complete` proves those names are a prefix of the modules and the
count is exactly the rest, and `wrapFrom_flatten` that grouping keeps each name, in order; that
the finding text is `moduleLines` is by definition, and the line width is layout. The starter
manifest lists each `lean_exe` with the first library containing its root module, and it gives
each target the same claim. Thus each executable has the claim of each library that contains its
root ([RG2002]). This follows from its definition, not from a theorem. The agent-guidance file is
found operationally:
from the Lake root up to the nearest directory holding a `.git` entry (Git itself is not run),
the nearest `AGENTS.md` with the section, else the nearest that exists, else the repository
root's; the skill files are read and written at that repository root (the Lake root outside a Git
repository).

Regula's `lakefile.lean` executes the core-only source `RegulaPolicy.Compiler` when its
configuration is elaborated, in a child `lean` that `LEAN_SYSROOT` or `PATH` selects. The
source guard compares that child's version and full commit with the revision's declared
identity and then prints them; the lakefile passes only when the child succeeds and the
printed pair is the `Lean.versionString` and `Lean.githash` of the Lean elaborating the
lakefile, so a child that is another compiler, fails or cannot be run is refused, with the
adopter's remedy. That comparison is an elaboration-time check, not a theorem. The compiled
probe, inventory admission, and plan admission use the same declared pair.
`Compiler.accepts_iff` proves the executed Boolean matches the predicate;
`transcript_plan_compiler` proves admitted transcripts and a valid plan agree on both fields.
Compiler self-reports and locating and launching the compiler are trusted IO, and a
self-report names the Git commit of a build's source tree, not uncommitted source edits or the
executable's bytes. Lake may reuse an elaborated configuration; `lake update` elaborates it
again. The compiled admission guards remain in force when a configuration is cached.

`doctor` reads the project's own `lean-toolchain`, resolves it to a toolchain
`elan toolchain list` names, and reads the version and commit that compiler reports,
independently of the compiler running `regula`. Only a listed name is run, without Elan's
`--install`, and no channel is resolved: `Regula.Toolchain.installedName?_spec` proves that the
name is one of those supplied as listed and equals the selector.
`Regula.Setup.toolchainIssues_eq_nil_iff` proves that the
decision reports no toolchain issue exactly when that resolved identity
`RegulaPolicy.Compiler.Supports`, under any selector; an unresolved selector or a failed probe
is an issue `init` does not fix. Elan's listing, that it runs a listed toolchain without
installing, and the report are trusted.

Only the exact [supported toolchain](toolchains.md) is admitted. There is no runtime
qualification switch or candidate publication mode.

**Trusted:** Lake's loader, its TOML grammar, Lean's import-header parser and Lean's frontend,
which elaborates a `lakefile.lean` as Lake does to locate the `package`, `lean_lib` and
`lean_exe` declarations, and the filesystem. Runs of `init` and `doctor` on scratch projects in
both formats (fresh, template, inline-table, structure-instance, bare-`package` and
computed-`leanOptions` shapes, another driver, a contradicting option, a stale skill, a library
without globs, left-out modules that a claimed module does and does not import, a library the
manifest excludes, with options written into bare and configured claimed targets, a package
with no `lean_lib`, a package-level `-D` setting Mathlib's options as in the first adopter, a
`-D` in one library's own `moreLeanArgs` in both formats, and a Lake project in a subdirectory of
a Git repository with and without a root `AGENTS.md`) are bounded observations, as are the
historical version-string guard's refusal of Lean 4.33.0 and 4.34.1 through the `lake` command
line and when a checker executable loaded the workspace. Those historical observations do not
qualify the new exact-identity guard. The controls of the previous checker, which ran `init`
and the guard on scratch projects, are removed, so no retained control observes them.

**Releases** ([procedure](contributing.md#release)): **Proved** in `lean/Regula/Release.lean`,
and checked by the kernel each time a step elaborates it: `tagAction`, the decision of the
candidate and publish steps, proceeds exactly for the head of `main` of an unpublished release
whose tag is absent or names the release commit (`tagAction_release_iff`), so publication, which
creates the tag, never leaves it naming another commit; it changes nothing once the release is
published (`tagAction_published`, `tagAction_skip_iff`), always proceeds on the head of `main` of
an unpublished release that no tag names elsewhere (`tagAction_converges`), and
`tagAction_refuse_iff` gives the remaining case. The derivation over the Conventional Commits
headers of the commits of `main` since the previous release (`parseCommit`) alone, `derive`, is
at least each commit's bump (`derive_ge`), calls for no release exactly when every commit's type
calls for none (`derive_eq_none_bump`), and is undecided exactly when a subject is not a header
(`derive_eq_none`). `nextVersion`, the version the open step derives from those headers,
`lean-toolchain` and the workflow's requested bump, bumps from its predecessor at least as much
as each header calls for, whatever was requested and also when the derivation is undecided
(`nextVersion_ge`); its bump is never less than the headers' greatest bump or the requested bump
(`nextBump_ge_called`, `nextBump_ge_requested`) and at least minor for a toolchain move
(`nextBump_moved`), so a toolchain move or a request releases even when every commit's type calls
for none, and an undecided derivation yields a version only for a requested bump
(`nextBump_undecided`). The version it yields follows its predecessor (`nextVersion_follows`):
later, on its toolchain for a patch release, with the lower components reset on a new line.
`covers`, which the candidate step checks on the commits of `main` since the release listed
before the one it releases up to the commit it releases, holds exactly when that release's bump
from its predecessor (`Version.bumpTo`) is at least each such header's bump, and at least minor
for a toolchain move (`covers_iff`); it holds for the release the open step derived from the same
commits (`nextVersion_covers`, with `Version.bumpTo_bump`). `publishedExactly`, which the
candidate step checks before it creates a release commit and the open step when it starts and
again just before it creates the branch, holds exactly when every release listed before the one
the step
handles is published and every published release is one of them (`publishedExactly_iff`); when
it holds, that release's listed predecessor is the latest published release
(`publishedExactly_latest`), and a release whose listed predecessor is unpublished, or is earlier
than a published release, is refused (`publishedExactly_refuses`), both given the releases before
it listed in ascending order, which `releases_ascending` checks. So once a release is published,
no release listed in its place is released. `pullBranch`, the name of the branch the open step
creates for the release pull request, is the same for two builds of a release only when they are
the same commit (`pullBranch_inj`), so builds with different commits never share one.
`releasePulls` selects, from the pull requests GitHub reports open, exactly those whose head is
a branch `pullBranch` names for the release's version in the repository (`mem_releasePulls`,
`isPullHead_iff`). `branchAction`, the decision of the open step over them, creates the branch
exactly when there is none (`branchAction_create_iff`) and otherwise refuses, naming the first
(`branchAction_refuse_iff`). `branchStep`, the program the step runs on that observation, is,
while one is open, exactly the refusal `refuseOpen` that names one of them, whatever the commit
(`branchStep_open`), and with none it is the creation (`branchStep_unopened`). These hold for
what the step observed just before it writes: a release pull request opened after the
observation is not excluded. That `refuseOpen` writes no reference is read from its definition,
which writes the job summary and fails; it is not a theorem. Separately, that the open step
never moves a branch that exists, and so never changes the branch of a pull request that is
open, whatever it observed, is by construction and not a theorem: its only write of a branch is
`createBranch`, GitHub's request that creates a reference, and that GitHub refuses that request
when the reference exists is trusted. `admits`,
which the open step also
checks, characterizes a new release exactly (`admits_iff`); an admitted release's tag is new
(`admits_new`), and once the legacy release `v4.34.0` is listed, Lake's order of the versions
the releases' lakefiles declare puts an admitted release above every listed one
(`admits_lake`, `Version.lakeLt_declared`). A release that follows its predecessor has patch `0`
exactly when it starts a new line (`follows_patch_iff`), and a release on another toolchain
starts one (`follows_toolchain`). **Proved** in `RegulaCore.Edition`: a build
labelled a release is admitted exactly while its tag is absent or names its commit
(`labelAdmitted_release_iff`), an unreleased build previews a release's edition exactly while
that release is the latest listed and has neither asset nor tag (`releaseSource_preview_iff`),
an artifact is deployable exactly when every release edition in it is its release asset
(`publishable_iff`), and a release that follows its predecessor has
patch `0` exactly when it starts a new line (`follows_startsLine_iff`). The rest of
`Release.lean` is operational: the text reading of a Conventional Commits header (`parseHeader`)
and of the edited files, its check that a commit of `main` or of a pull request is unreleased,
`agree`, and `adopt`, which checks, with `git` trusted, that the release commit is the content CI
derived from `main`'s commit before CI records it as that commit. Its edits of
`RegulaCore/Edition.lean`, `lakefile.lean`, the adoption guide's compatibility table, each
`require` of Regula in the tracked Markdown documents and each mention of a release in the root
`README.md` are read back before use; its stamps of
`RegulaCore/Rule.lean` are a convenience that reads text. `agree`,
a step of `verify` before acceptance, refuses a `lakefile.lean` version, as Lake reads it
(`lake reservoir-config`), other than the latest listed release's, a compatibility table
other than the one `Regula.releases` gives, and a `require` of Regula in a tracked Markdown
document that names a different release than the latest listed one, as the text reading
`setPins` reads it (`pinsAgree_iff`). That reading finds a `require` only on a line with the
repository's address in quotation marks, exactly as `gitUrl` writes it. Thus `agree` also refuses
unless the root `README.md` and the adoption guide each have a `require` of each form
(`unpinned_eq_nil_iff`). `agree` also reads each mention of a release in the root `README.md` with the text reading `setMentions`. It refuses a mention that names a different release than the latest listed one or its toolchain (`mentionsAgree_iff`). It also refuses a `README.md` without a mention of each kind (`unmentioned_eq_nil_iff`). The kernel checks the edited modules' theorems when
the local gate on the release pull request and CI's checks of the release commit build them:
`releases_ascending`, `releases_follow`, `installed_listed`, `release_attributes_rules` (when
`installed` is a release, no lifecycle position of any rule is `.unreleased`; on the release
commit this is the gate before anything is published), `lifecycle_listed` (every release a rule's
lifecycle names is in `versions`) and `introduced_startsLine` (the release that introduces a rule
has patch `0`, so it is not a patch release). What the steps observe (whether the release is
published, the versions of the published releases, read from the tags of the releases GitHub
lists that are not drafts, the head of `main`, the tag, the commits since the previous release,
the pull requests open and their heads, observed just before the open step writes its branch and
not again afterwards, a pull request's title), GitHub's signature verification, that GitHub
refuses to create a
reference that exists, that publishing a release
creates its tag at the given commit, tags, immutable releases, pull requests, squash merges
taking the pull request's title and description, workflow ordering, and that Lake and Reservoir
read and order versions as their source shows ([Reservoir](contributing.md#reservoir)) are
trusted.

## External systems

Regula's code reads and changes systems that no Lean proof can examine. These external systems are
the file system, processes, the process environment, Lake, Lean, the file locks of the operating
system and Git. `RegulaPolicy.External.System` gives them. A contract gives what Regula's code
uses of an operation of such a system. A theorem about code that uses the operation has the
contract as a hypothesis. At this time, only the
file system has contracts.

### Assumptions, checked operations and observers

The module of an external system gives its operations as the structure `Ops` and a model of the
system as the structure `Model`. A model gives each operation as an action on a state. An
assumption is a predicate over a model. Each assumption of the file system is the contract of one
operation, as a `Std.Do` triple. The attribute `@[regula_assumption]` of `Regula.Assumption`
gives the system and the sources of the assumption. An assumption is not an `axiom`: each theorem
that uses it has it as a hypothesis.

A checked operation runs an operation and then examines the result. It fails when the
postcondition of the operation is not true for that result. The attribute `@[regula_checked]`
gives the theorem that proves its postcondition. That theorem uses the contracts of the operations
that examine the result, not the contract of the operation that the checked operation runs.

An observer is the code that operates the real system for a Regula program. Code that Regula
writes over the operations of a model gets the real system only through an observer. The
attribute `@[regula_observer]` marks it.

Each attribute is checked where it is written. An assumption must be a definition or an inductive
type, and its type must end in `Prop`. The check reduces the type, thus it also accepts a different
name of `Prop`. The contract of a checked operation must be a theorem, and its statement must use
the checked operation. A role is given only in the module that declares the constant, and only one
time. Thus no import can give a second role to a constant.

### From a model to the real system

A theorem about a model is not a theorem about the code that runs. In Lean, an action of `IO` gets
a world, `IO.RealWorld`, and gives its result and a new world. No proof can examine a world. The
definition `Corresponds ops M view` connects the operations `ops` in `IO` to the model `M`. The
function `view` gives a state of the model for each world.

`Corresponds` states that each operation of `ops` gives the result of the operation of the model,
from the state that `view` gives. The world after the operation gives the state after the
operation of the model. This is a relation between two runs, not a property of the file system.
Thus it is not an assumption. The theorem `corresponds_ofIO` proves it for each `ops`, when the
states of the model are the worlds (`Model.ofIO`).

The theorems for the observer use that model. Thus they use only the five assumptions of the file
system at that model. Each assumption is a statement about each run from each world.

In `IO`, the world at the end of an operation is the world at the start of the next operation.
Thus a change by a different process while the code runs is a part of the run of one operation. A
read changes nothing, thus a change during a read makes an assumption false. A removal keeps the
entry at each path in its frame. Thus a change during a removal, at an entry that the frame keeps,
makes an assumption false.

A change in the removed tree can also make `RemovesTree` false, as "The file system" shows. Thus
the assumptions are about runs in which no different process writes to the file system. The
theorems that use a false assumption give no result.

### The sources of an assumption

A source is a file of the Lean 4 repository at a release tag, with its lines. It can also be a
document about a system, or the reason that Regula trusts the assumption when no source states
it. A `lean` source must be at the release of the Lean that elaborates its module
(`RegulaPolicy.External.Source.stale`). After an upgrade of the toolchain, each module with a
source at the earlier release does not elaborate. The writer must read the source again at the
new release, and then change the release of the source.

Only a `lean` source has a release that the module checks. Thus the attribute refuses a document
about Lean or Lake, and a document in the Lean 4 repository or in the documentation of Lean
(`RegulaPolicy.External.Source.unpinned`). It finds such a document by the text
`leanprover/lean4`, `lean-lang.org` or `leanprover.github.io` in its reference. It does not find a
reference that names such a place with a different text.

No retained control shows these refusals, or the refusals of a role for an imported constant, of
an assumption that is not a predicate and of a contract with a statement that does not use its
checked operation. The controls of the previous checker are removed.

### The file system

`RegulaCore.Filesystem` gives the model of the file system and its assumptions.
`Regula.Filesystem.observer` is its observer for the programs of the package.
`RegulaCore.Removal` gives the last three checked operations of the table. Each `lean` source
below is a file of the Lean 4 repository at `v4.35.0`, below `src`.

| Declaration | Status | Contract | Sources |
| --- | --- | --- | --- |
| `ReadsEntry` | trusted | `symlinkMetadata` gives the type of the entry at a path and changes nothing. It fails with `noFileOrDirectory` only when no entry is at the path. | [`Init/System/IO.lean#L1151-L1156`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1151-L1156), [`runtime/io.cpp#L1160-L1179`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1160-L1179), [`runtime/io.cpp#L276-L279`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L276-L279), POSIX.1-2024 `lstat()` |
| `ReadsReal` | trusted | `realPath` gives the real path of a path and changes nothing. It fails only when there is no real path. | [`Init/System/IO.lean#L873-L879`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L873-L879), [`runtime/io.cpp#L1054-L1066`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1054-L1066), POSIX.1-2024 `realpath()`, Apple Libc-1752.120.2 `stdlib/FreeBSD/realpath.c#L216-L243` and `#L348-L358` |
| `RemovesTree` | trusted | `removeDirAll` of a directory at its real path keeps the entry at each path in its frame (`Model.Unchanged`), when it succeeds and when it fails. | [`Init/System/IO.lean#L1330-L1342`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1330-L1342), [`runtime/io.cpp#L1160-L1179`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1160-L1179), [`runtime/io.cpp#L1197-L1207`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1197-L1207), [`runtime/io.cpp#L1351-L1364`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1351-L1364), POSIX.1-2024 `lstat()`, `unlink()` and `rmdir()`, POSIX.1-2024 `<sys/stat.h>` |
| `RemovesEntry` | trusted | `removeFile` of a path keeps the entry at each path in its frame (`Model.Unchanged`), when it succeeds and when it fails. The path is at its real path, or it is a symbolic link in a directory at its real path (`Model.InOwnDirectory`). | [`Init/System/IO.lean#L881-L886`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L881-L886), [`runtime/io.cpp#L1351-L1364`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1351-L1364), POSIX.1-2024 `unlink()`, POSIX.1-2024 `<sys/stat.h>` |
| `Renames` | trusted | `rename` keeps the entry at each path in the frame of its two paths (`Model.Kept`), when it succeeds and when it fails. The source is at its real path, and the destination has a parent at its real path. | [`Init/System/IO.lean#L903-L909`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L903-L909), [`runtime/io.cpp#L1209-L1238`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1209-L1238), POSIX.1-2024 `rename()`, POSIX.1-2024 `<sys/stat.h>` |
| `removeDirectory` | checked | After a removal that succeeds, no entry is at the path: `removeDirectory_gone`, which uses only `ReadsEntry`. | [`Init/System/IO.lean#L1330-L1342`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1330-L1342) |
| `removeEntry` | checked | After a removal that succeeds, no entry is at the path: `removeEntry_gone`, which uses only `ReadsEntry`. | [`Init/System/IO.lean#L881-L886`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L881-L886) |
| `removeOwnWith` | checked | After a removal that succeeds, no entry is at the path: `removeOwnWith_gone`, which uses only `ReadsEntry`. | [`Init/System/IO.lean#L1330-L1342`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1330-L1342), [`Init/System/IO.lean#L881-L886`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L881-L886) |
| `removeFoundWith` | checked | After a removal that succeeds, no entry is at the path: `removeFoundWith_gone`, which uses only `ReadsEntry`. | [`Init/System/IO.lean#L1330-L1342`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1330-L1342), [`Init/System/IO.lean#L881-L886`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L881-L886) |
| `replaceWith` | checked | After a move that succeeds, nothing is at the source and a file is at the destination: `replaceWith_moved`, which uses only `ReadsEntry`. | [`Init/System/IO.lean#L903-L909`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L903-L909) |

The theorems `removeDirectory_spec` and `removeEntry_spec` are about the removal of a directory, a
file or a link at its own place, in a model. After a removal that succeeds, no entry is at the
path. A removal keeps the entry at each path in its frame, when it succeeds and when it fails. Their
hypotheses are the assumptions that they use. The theorems `removeDirectory_io` and
`removeEntry_io` give the same result for the code in `IO`, with `Corresponds` as one more
hypothesis. `Regula.Filesystem` gives them for the observer at the model of the worlds, where
`corresponds_ofIO` proves `Corresponds`.

`Model.Unchanged` gives the frame of a removal. It is each path with a file name, if its parent is
its own real path before the removal. The path is not the removed path, and the chain of its
parents does not reach the removed path (`Within`). Before the removal, also no entry is at the
path, or the path names a file that is not an entry of the removed tree. For each such path, the
entry after the removal has the same type as before, or no entry is at the path before and after.

`Model.Below` gives the removed tree. The removed path is in its tree. A name in a directory of
the tree, other than `.` and `..`, is also in the tree. A symbolic link is not a directory, thus
the tree does not go into a symbolic link.

The tree includes the entries that `removeDirAll` of Lean 4.35.0 visits when no different process
writes
([`Init/System/IO.lean#L1335-L1342`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1335-L1342)).
It also has a name with no entry in a directory of the tree. It also has a different spelling of
an entry, for example a different case on a volume that ignores case. These names add no file to
the files of the tree. The first names no file, and the second names the file of the entry.

`Model.ident` gives the file that a path names. It is the device and the number of the file, the
values `st_dev` and `st_ino` of `lstat(2)`. POSIX.1-2024 `<sys/stat.h>` states that these two
values identify a file in the system. A second name of a file has the same identity. Examples are a
different case of a name on a volume that ignores case, an APFS firmlink, a bind mount and a hard
link. Thus the frame does not include a second name of an entry of the removed tree.

The `IO.FS.Metadata` of Lean 4.35.0 has no device and no file number
([`Init/System/IO.lean#L1115-L1129`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1115-L1129)).
Thus no observer reads `Model.ident`, and no decision uses it. It only identifies the files that
the frame is about.

The frame also does not include a path if the real path of its parent is not that parent. Such a
path can go through the removed path, for example through a symbolic link or with `..`. The target
of a symbolic link in the tree is not an entry of the tree through that link. Thus the entry of
the target is in the frame, if the tree does not have it with a different name. Thus in a run with
no different process that writes, the removal keeps the entry of the target. A path with no entry
is in the frame, thus no entry appears outside the removed path.

`removeDirAll` of Lean 4.35.0 resolves each path of the tree again at each call. During the
removal, a different process can replace a directory of the tree with a symbolic link. It can also
change what a path of the tree resolves to in a different way, for example with a rename. Then the
walk can go out of the tree and remove entries outside it. This is the race of CVE-2022-21658. In
such a run, `RemovesTree` is false.

Some volumes ignore case or Unicode normalization. On such a volume, the `realpath(3)` of Darwin
gives the name that the volume keeps for each component. Apple Libc-1752.120.2
`stdlib/FreeBSD/realpath.c#L216-L243` and `#L348-L358` show this. This was observed one time on
macOS 27.0.1 with APFS: `realpath dir/FILE` printed `.../Dir/file`. Thus `atOwnPlace` gives
`false` for a different case of such a name. `ReadsReal` gives this source.

The assumptions are for a POSIX system. On Windows, `symlinkMetadata` of Lean 4.35.0 follows a
symbolic link. Also, `realPath` gives the path that it got when it cannot find the real path
([`runtime/io.cpp#L1032-L1033`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1032-L1033)).
Thus the observer refuses these two reads and each removal of a directory on Windows.

### Assumptions of directory enumeration

Lean `v4.35.0` reads a directory with `readdir` until it gives null, and then it returns the names that it has read ([`runtime/io.cpp#L1076-L1098`](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/io.cpp#L1076-L1098)). A failed read also gives null, so `System.FilePath.readDir` can return fewer names and no error. Regula lists each directory through an admitted `ls` program instead, which `Construction.locate` selects. An admitted `ls` examines `errno` after each `readdir`, and it exits with a nonzero code after a failed read. `Construction.Enumerator.names` refuses unless the program exits with code 0 and writes no error text.

A copy, the capture of a directory and a Git copy each locate the program one time and list each directory through it.

The names of a listing decode exactly. `decodeListing_zero` states that the names that `ls --zero` writes decode to the stored names. `decodeListing_gnu` states the same for the escaped names of GNU `ls` 8.32. These theorems are about encoders written from the source of each program, not about the programs. `Enumerator.names` also refuses a name that is not UTF-8, a name with `/` or NUL, and the names `.` and `..`.

`Construction.ReadsNames` is the hypothesis of the copy theorems about the names of a directory. It names these programs and sources:

| Program | Options | Sources |
| --- | --- | --- |
| GNU coreutils `ls` 9.0 to 9.12 | `-A -U --zero` | `src/ls.c`: `print_dir`, `file_failure` and the `ZERO_OPTION` case, at [`v9.0`](https://github.com/coreutils/coreutils/blob/v9.0/src/ls.c#L3008-L3068) and [`v9.12`](https://github.com/coreutils/coreutils/blob/v9.12/src/ls.c#L3024-L3077) |
| GNU coreutils `ls` 8.32 | `-1 -A -U --quoting-style=escape --show-control-chars --color=never --indicator-style=none` | [`src/ls.c`](https://github.com/coreutils/coreutils/blob/v8.32/src/ls.c#L2966-L3036) lines 2318-2319, 2847-2867 and 2966-3036, and gnulib `lib/quotearg.c` at `d279bc6d` |

Regula admits a program only when its completeness and its report of a failed read rest on the source of the program itself. That source must be the source of the release that the first line of `ls --version` names exactly, as `gnuRelease?_sound` states. Regula refuses a later release with the reason, until a later Regula release reads it. Regula does not admit the `ls` of macOS, which reads directories through the `fts` functions of the system C library. Nothing that it reports names the release of that library. The [adoption guide](adoption.md#a-program-that-lists-directories) tells an adopter which program to install.

Assumes: The program that Regula finds is the release that it identifies as. GNU `ls` gives its release in the first line of `ls --version`.

Assumes: The kernel and the file system report each failed read of a directory to `readdir`, with an error other than `ENOENT`. POSIX.1-2024 `readdir()` sets `errno` on an error and keeps it unchanged at the end of a directory. Linux v6.8 ext4 reports a failed read of a block. It skips a block that fails its checksum and writes only a message to the kernel log.

Regula trusts the exclusion of `ENOENT` because some releases of GNU `ls` do not report it. GNU `ls` 9.12 takes `ENOENT` as the end of a directory. GNU `ls` 9.6 to 9.11 do the same without glibc 2.3 or later. GNU `ls` 9.5 clears `ENOENT` after each `readdir`, at [`src/ls.c#L3064-L3066`](https://github.com/coreutils/coreutils/blob/v9.5/src/ls.c#L3064-L3066). Also, glibc 2.39 takes `ENOENT` as the end of a removed directory, at `sysdeps/unix/sysv/linux/readdir.c` lines 39-48. A removed directory has no names to miss.

No retained control runs this code with a stand-in `ls` or with a failed read: the controls of the previous checker are removed.

Lean and Lake read directories in two more places. `IO.FS.removeDirAll` lists a directory with `readDir` before it removes the directory ([`Init/System/IO.lean#L1335-L1342`](https://github.com/leanprover/lean4/blob/v4.35.0/src/Init/System/IO.lean#L1335-L1342)). After a failed read, entries remain, so its last `removeDir` fails and the removal stops with an error.

Lake finds the modules of a glob with Lean's `forEachModuleInDir`, which uses `readDir`. Lake also reads the files of an `inputDir` target with `walkDir`. A failed read there gives Lake fewer modules or files without an error, and Regula trusts these reads of Lake.

### What the contracts do not establish

The checker does not report the assumptions or the checked operations of a declaration. The
contracts of the external systems do not establish these properties:

- That the real system satisfies the assumptions. Regula trusts each one, with its sources.
- That no different process changes the file system while the code runs. Such a process can make
  an assumption false, as "From a model to the real system" shows. For example, a process can
  replace a directory of a removed tree with a symbolic link during the removal. This race of
  CVE-2022-21658 makes `RemovesTree` false. Regula does not examine the other processes.
- That two names of one file give the same device. Two mounts of one network or FUSE file system
  can give two devices for one file. There `RemovesTree` and `RemovesEntry` are false.
- That the file numbers of a file system are stable. On a file system with file numbers that
  change, `RemovesTree` and `RemovesEntry` can be false.
- That a second name of an entry of a removed tree stays, for example a second hard link. The
  frame does not include such a name.
- That an entry outside a removed path is the same file, with the same contents, after the
  removal. The frame compares only the type of each entry.
- That each call of an operation of an external system is in an observer. Regula's code also calls
  these operations in other places.

## Operational assumptions

The supported compiler, the filesystem, the process runtime and GNU timeout are trusted. Each acceptance step runs under one GNU timeout that owns the whole group of processes. OS scheduling and signal delivery are trusted, not a real-time theorem.

Before provisioning and before any build, `scripts/verify.sh` has `RegulaVerification` invalidate the accepted link of the selected step (the private `--begin-attempt` flag). It also removes an earlier site artifact. Thus a failed setup or build cannot leave either in place. The copy of the first step is in `.lake/regula-scratch/` of the project, and the driver removes it on each return. A killed run leaves its copy, and the next driver removes it when no live process holds the lock of that directory.

Helpers invoke external programs with arrays of arguments, not with generated shell programs. [`AGENTS.md`](../../AGENTS.md) records the narrow shell exceptions of the operator.

[RG1001]: https://rbeauchamp.github.io/regula/dev/rules/RG1001/
[RG1002]: https://rbeauchamp.github.io/regula/dev/rules/RG1002/
[RG1003]: https://rbeauchamp.github.io/regula/dev/rules/RG1003/
[RG1004]: https://rbeauchamp.github.io/regula/dev/rules/RG1004/
[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
[RG1006]: https://rbeauchamp.github.io/regula/dev/rules/RG1006/
[RG1007]: https://rbeauchamp.github.io/regula/dev/rules/RG1007/
[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG1009]: https://rbeauchamp.github.io/regula/dev/rules/RG1009/
[RG2001]: https://rbeauchamp.github.io/regula/dev/rules/RG2001/
[RG2002]: https://rbeauchamp.github.io/regula/dev/rules/RG2002/
[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/
[RG2004]: https://rbeauchamp.github.io/regula/dev/rules/RG2004/
[RG2005]: https://rbeauchamp.github.io/regula/dev/rules/RG2005/
[RG2006]: https://rbeauchamp.github.io/regula/dev/rules/RG2006/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
