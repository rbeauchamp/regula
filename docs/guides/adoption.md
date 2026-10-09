# Adopt Regula

Regula checks the mechanical requirements of the
[standard](https://rbeauchamp.github.io/regula/dev/standard/) in your own Lean project: `lake lint`
rejects holes, project axioms, compiler-trusting proofs and axioms beyond the foundation you
claim, and names every compiled boundary your executables reach. Conformance additionally needs
the semantic review of the [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/),
which a passing run does not replace ([semantic review](#complete-semantic-review)).

The first four steps take a project from `require` to its first `lake lint`. They use your own
layout, module names and lakefile format; nothing named `Audit`, `Fixtures` or `tmp` from this
repository is required. The normative definitions behind them are in
[standard §7.10](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#710-adopting-the-checker-in-another-project).

## 1. Require Regula

Regula is a Lake package named `regula`, like any other Lean tool. It numbers its own releases
by [Semantic Versioning](https://semver.org) and tags each `v<version>`; each release supports
exactly one Lean toolchain. Patch releases (`0.2.1` after `0.2.0`) carry fixes on the same
toolchain; a new rule, a tightened rule or a move to another toolchain makes a minor release. The
first release, `v4.34.0`, predates this numbering and is tagged with the Lean release it
supports. This table lists every release, newest first, with its one toolchain:

| Regula tag | Lean toolchain | Rule reference |
| --- | --- | --- |
| `v0.10.0` | `leanprover/lean4:v4.34.1` | [v/0.10.0/](https://rbeauchamp.github.io/regula/v/0.10.0/) |
| `v0.9.0` | `leanprover/lean4:v4.34.1` | [v/0.9.0/](https://rbeauchamp.github.io/regula/v/0.9.0/) |
| `v0.8.0` | `leanprover/lean4:v4.34.0` | [v/0.8.0/](https://rbeauchamp.github.io/regula/v/0.8.0/) |
| `v0.7.0` | `leanprover/lean4:v4.34.0` | [v/0.7.0/](https://rbeauchamp.github.io/regula/v/0.7.0/) |
| `v0.6.0` | `leanprover/lean4:v4.34.0` | [v/0.6.0/](https://rbeauchamp.github.io/regula/v/0.6.0/) |
| `v0.5.0` | `leanprover/lean4:v4.34.0` | [v/0.5.0/](https://rbeauchamp.github.io/regula/v/0.5.0/) |
| `v0.4.3` | `leanprover/lean4:v4.34.0` | [v/0.4.3/](https://rbeauchamp.github.io/regula/v/0.4.3/) |
| `v0.4.2` | `leanprover/lean4:v4.34.0` | [v/0.4.2/](https://rbeauchamp.github.io/regula/v/0.4.2/) |
| `v0.4.1` | `leanprover/lean4:v4.34.0` | [v/0.4.1/](https://rbeauchamp.github.io/regula/v/0.4.1/) |
| `v0.4.0` | `leanprover/lean4:v4.34.0` | [v/0.4.0/](https://rbeauchamp.github.io/regula/v/0.4.0/) |
| `v0.3.1` | `leanprover/lean4:v4.34.0` | [v/0.3.1/](https://rbeauchamp.github.io/regula/v/0.3.1/) |
| `v0.3.0` | `leanprover/lean4:v4.34.0` | [v/0.3.0/](https://rbeauchamp.github.io/regula/v/0.3.0/) |
| `v0.2.0` | `leanprover/lean4:v4.34.0` | [v/0.2.0/](https://rbeauchamp.github.io/regula/v/0.2.0/) |
| `v4.34.0` | `leanprover/lean4:v4.34.0` | [v/4.34.0/](https://rbeauchamp.github.io/regula/v/4.34.0/) |

The release steps generate the table from the release data, and CI refuses a table that
disagrees with it; a row is added when a release's pull request merges, shortly before CI
publishes the release. The [releases page](https://github.com/rbeauchamp/regula/releases)
has each release's notes. Choose the newest release for your `lean-toolchain`, set your
`lean-toolchain` to its toolchain if you move, then require its tag (below, `v4.34.0`).

`lakefile.toml`:

```toml
[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "v4.34.0"
```

`lakefile.lean`:

```text
require regula from git
  "https://github.com/rbeauchamp/regula" @ "v4.34.0"
```

Then fetch it:

```sh
lake update regula
```

Requiring `regula` adds exactly one package to your `lake-manifest.json`: `regula` itself. It
requires nothing beyond the Lean toolchain (no Mathlib, no Batteries) and imports only Lean's
core libraries, so it never pins a package your project also uses, and a project with Mathlib
keeps the Mathlib revision it pins.

### When your Lean release has no Regula release

Each Regula release supports exactly one Lean release, the one in its `lean-toolchain`; a Lean
patch release such as `v4.34.1` is another release. Lake loads Regula with the Lean your project
runs. Regula `v0.2.0` through `v0.5.0` stop in Regula's `lakefile.lean` before anything compiles
when that Lean's version differs, naming both releases; they compare only the version, not the
compiler's commit, and the earlier `v4.34.0` tag has no such guard:

```text
error: …/regula/lakefile.lean:…: this Regula release supports only Lean leanprover/lean4:v4.34.0, but Lake is running Lean 4.33.0. …
```

This source revision guards the exact compiler instead: it declares one exact compiler version and
commit in [`RegulaPolicy.Compiler`](../../lean/RegulaPolicy/Compiler.lean).
A fresh configuration invokes that identity guard before building the checker; inventory, plan,
and probe admission retain it. Elan aliases may differ when they resolve to the same compiler. A
mismatch stops Regula's `lakefile.lean` with `Regula's compiler guard stopped`, naming the Lean
running Lake and the selected executable. The policy's `refusal` supplies the expected and
observed version and full commit, the migration remedy, and a link to the
[supported-toolchain policy](toolchains.md).

A Lean too old to compile the policy prints its own errors in place of that refusal. The
guard runs the `lean` that `LEAN_SYSROOT` or `PATH` selects and requires it to be the Lean
running Lake. When another toolchain's variables are inherited, a `lean` the policy refuses
stops with that diagnostic, whichever Lean runs Lake, and a `lean` the policy accepts while
Lake runs another Lean stops with `… is not the Lean running Lake …` instead. Running Lake
without those variables is the remedy in both cases.
`lake exe regula doctor` reports the same mismatch for the compiler your own `lean-toolchain`
selects, whichever compiler an override runs. For a Lean too old to run its identity probe, it
instead reports that the pin selects no installed compiler that reports its identity, with the
probe's error.

Move your project to the supported Lean release first: set `lean-toolchain`, move Mathlib (if you
use it) to a revision for that release the usual way, and run `lake update`. Otherwise require a
Regula release that supports your Lean from the [compatibility table](#1-require-regula), if there
is one. When no other dependency pins a
toolchain, `lake update` itself moves an older `lean-toolchain` to Regula's release and restarts.
When Mathlib pins another one, `lake update` prints `toolchain not updated; multiple toolchain
candidates` and keeps yours, so the stop above follows.

This revision supports only the exact pinned release. Other compiler identities require a
future deliberate port; see the [supported toolchain](toolchains.md).

## 2. Run `lake exe regula init`

```sh
lake exe regula init            # or: lake exe regula init --skill
```

`init` reads your project through Lake, then writes only what is missing:

| Piece | What `init` writes when it is missing |
| --- | --- |
| Lint driver | `lintDriver = "regula/lint"` (`lakefile.toml`, top level) or `lintDriver := "regula/lint"` (`lakefile.lean`, in the `package` declaration), so `lake lint` runs Regula. |
| Options | The `leanOptions` the rules require for every claimed target, each only where neither the package nor the target gives it a value and no `-D` in the target's `weakLeanArgs` or `moreLeanArgs` (its own or the package's) sets it: in the package's configuration when every root target is claimed (as the starter manifest claims them all) and no claimed target's `-D` sets the option, and otherwise in each claimed target's own `[[lean_lib]]`/`[[lean_exe]]` table or `lean_lib`/`lean_exe` declaration, so no option reaches a target the manifest excludes or a target whose `-D` sets it; while an existing manifest does not load or classify every root target, none, until `doctor`'s [RG2002] finding is fixed. They are `autoImplicit` and `relaxedAutoImplicit` false and `linter.missingDocs` true, and, when your workspace contains Mathlib, Mathlib's standard linter set with its three exclusions ([community linters](#community-conventions-and-linters)). |
| Manifest | A starter `foundation_manifest.json` that claims every `lean_lib` as `standard-logical` with `report` execution and lists every `lean_exe` with the first library that contains its root module, or with the first library when none does ([step 3](#3-review-the-claimed-surface)). A manifest claims each surface per library, a `lean_exe` belonging to a library's surface, so a package with no `lean_lib` (such as Lake's `exe` template) gets none: `init` writes the other pieces and `doctor` asks you to add a library, after which `init` writes the starter. |
| Agent guidance | A short `## Lean standard: Regula` section in your repository's `AGENTS.md`, or with `--skill` the briefing as `.agents/skills/regula/SKILL.md` at the repository root: the root of the Git repository that contains the Lake project (the nearest directory holding `.git`), or the Lake project outside a Git repository. `init` looks for `AGENTS.md` from the Lake project's directory up to the repository root and adds the section to the nearest one, so a Lake project in a subdirectory such as `lean/` without its own `AGENTS.md` uses the repository's root one; there the section ends by naming the directory its `lake` commands run in. When there is none, it creates `AGENTS.md` at the repository root and says so. `doctor` and `init` print each path relative to the Lake project, such as `../AGENTS.md` or `../.agents/skills/regula/SKILL.md`. A section already in a nearer `AGENTS.md` counts; if an earlier `init` created `lean/AGENTS.md` with only the section, or `lean/.agents/skills/regula/SKILL.md`, delete that file and run `init` again. In a repository with several Lake projects, the first to run `init` adds the section; name the other projects' directories in it by hand. `init` also rewrites `.claude/skills/regula/SKILL.md` at the repository root, where Claude Code discovers project skills, whenever that file exists and differs from the installed briefing, but never creates it (copy the `.agents` file there for Claude Code). Both files are generated and owned by `init`: re-running it replaces local edits and prints each file it replaced. |

It never changes a value you set: a lint driver of your own, an option with another value and an
existing manifest stay as they are, and `lake exe regula doctor` reports each with its fix. A
required option that a `-D` extra `lean` argument of a target sets counts as set for that target:
`init` adds it to no configuration that reaches the target (`Regula.Setup.added_unargued`, over the
modelled setup and reading every `-D` candidate as [RG2006] does, and checked again after writing,
target by target, as `Regula.Setup.arguedBy_run` states), and `doctor` reports once that [RG2006]
requires those options in `leanOptions`, naming the entries to write there. It edits the lakefile
in place, in its own format, then reads the project again and restores every file it wrote unless
nothing is left to write. A second run therefore writes nothing:
`Regula.Setup.plan_idempotent` proves that the plan of the result is empty over the modelled
setup, and that runtime check confirms the files as written match it. `init` ends by running
`doctor`.

`lake exe regula doctor` changes nothing. It prints each missing or wrong piece in the linter's
finding form, with the exact fix: setup findings for the lint driver, options, manifest, agent
guidance, the compiler your `lean-toolchain` selects (resolved only to a toolchain Elan lists as
installed under exactly that name, so use the fully qualified selector from the supported
revision's [`lean-toolchain`](../../lean-toolchain), as `elan toolchain list` prints it, rather than
a shorter spelling or a channel such as `stable`; `doctor` resolves no channel and installs
nothing) and any module below a library root that no library includes but a claimed module imports
(which `lake lint` rejects), and,
once a manifest exists, the linter's own manifest validation ([RG2002]) and option decision ([RG2006])
for every claimed target, one [RG2006]
finding naming every target with the same claim and failures, where `lake lint` prints one per
target. It exits 0
when the setup is complete and 1 otherwise, and lists what `init` would write. A module left out
of every library that no claimed module imports is only a `note`, which does not affect the exit
status: include it to audit it, or leave it out deliberately.

### Agent guidance

Regula is designed first for coding agents, which may not know this standard from their training
data. Every rule is one typed registry definition stating what it requires, why, how to comply
(with the common compliant rewrites) and a checked example pair; findings, the offline commands
below, the JSON report and the rule-reference site are all generated from it. The `AGENTS.md`
section tells an agent to run the briefing before it writes Lean; it names no version, so it
stays current. The skill file holds the briefing itself; `init` refreshes it after an update.

```sh
lake exe regula agent-guide      # compact briefing of every rule, ordered for writing code
lake exe regula skill            # the same briefing as an Agent Skills SKILL.md
lake exe regula explain RG1001   # one rule in full: requirement, rationale, remedy, examples
lake exe regula rules            # the index of every rule
```

Each prints Markdown generated from the installed package's registry, so it needs no network and
matches your pinned release. This repository dogfoods the skill in
[`.agents/skills/regula/SKILL.md`](../../.agents/skills/regula/SKILL.md).

### Cite a rule

Wherever an issue, a comment, a pull request or a document mentions a rule ID in prose, the ID is
a link to that rule's page for the Regula version the text is about, the
[rule link](#read-a-finding) a finding prints:
`[RG3002](https://rbeauchamp.github.io/regula/v/<version>/rules/RG3002/)` for a release, with
`dev` in place of `v/<version>` only for unreleased `main`. A document uses one form throughout,
never a mixture of bare and linked IDs. IDs in code blocks and code spans, in pasted tool output,
in a rule table that is itself the index of rule pages, and in Lean identifiers stay as they are.
The briefing tells an agent the same, with the link for your installed build.

Regula's own documentation follows this. Each Markdown document tracked on `main`, other than
the root `README.md`, links to the development pages, as [RG3002] does here. The generated agent
skill is one of these documents. Each page of the rule-reference site links in its own edition.
There, only the title and the top heading of a rule page name its rule without a link.

The root `README.md` links the stable address of each rule,
`https://rbeauchamp.github.io/regula/rules/<ID>/`. That address names no edition and opens the
page of the latest release ([links of the root README](contributing.md#links-of-the-root-readme)).

The documentation step of acceptance reads the prose of each tracked Markdown document and of
the rendered standard, headings included. In a Markdown document, it refuses a rule ID that is
not a link the check accepts for that document. In the rendered standard, it refuses a rule ID
that is not a link to the page of that rule in the same edition. The site check refuses such an
ID in a page of the site
([how to write one, and what the checks rely on](contributing.md#rule-ids-in-documentation)).

## 3. Review the claimed surface

Conformance is claimed per Lake library or executable, and the checker discovers modules through
Lake's elaborated inventory, not through your umbrella import or a file list
([standard §7.2](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#72-define-surfaces-through-lake-semantics)).
Give every claimed library a glob that covers its modules, so a module your umbrella does not
import is still inspected; `lake new` writes none, and `doctor` names each module a library leaves
out:

- `lakefile.lean`: ``globs := #[.andSubmodules `Widget]``
- `lakefile.toml`: `globs = ["Widget", "Widget.+"]` (`"Widget.+"` alone omits `Widget` itself)

When a library leaves out many modules, `doctor` states how many, names the first few and gives
the glob that includes them all.

`foundation_manifest.json` classifies every root `lean_lib` and `lean_exe`, claimed or excluded
with a rationale. Review the starter: strengthen each `claim` where the library allows, write
the real rationale, and exclude what you do not claim.

Name a library or an executable by its Lake target name, the `name` of its `lean_lib` or
`lean_exe` that `lake build` takes (and `lake exe`, for an executable), such as `widget-tool`.
A name that is not a Lean identifier has a second spelling, `«widget-tool»`, which is how Lean
prints it: `init` writes that spelling and reports show it. Both name the same target, so a
manifest that names both has a duplicate. A library or executable entry, claimed or excluded, that names no root
target of its kind is refused ([RG2002]): the finding quotes the entry as you wrote it and lists
the root libraries, or the root executables, by Lake target name.

An executable's root may live inside a library's namespace, such as ``root := `Widget.Cli` `` under
the ``.andSubmodules `Widget`` glob, so no glob needs to leave executable roots out. List such an
executable in the `executables` of that library's surface: its root keeps the library's claim
and is inspected once, in the executable's own environment with its import closure, while the
library's other modules stay in the library's environment. [RG2002] rejects the other
combinations: a claimed executable whose root is in an excluded library or in another surface's
library, and an excluded executable whose root is in a claimed library. An excluded executable
may keep its root in an excluded library. A claimed library still needs one module that is not
such a root, such as its umbrella module, for its own environment.

```json
{
  "schema-version": 2,
  "surfaces": [
    { "library": "Widget", "executables": ["widget_tool"], "claim": "choice-free",
      "execution": "report", "rationale": "..." }
  ],
  "excluded-libraries": [],
  "excluded-executables": []
}
```

`claim` is the strongest foundation any declaration on the surface may use
([standard §4.5](https://rbeauchamp.github.io/regula/dev/standard/4-mathematical-foundations/#45-foundation-strength-kernel-only-choice-free-standard-logical)):

| Profile | Permitted transitive axioms |
| --- | --- |
| `kernel-only` | none |
| `choice-free` | `propext`, `Quot.sound` |
| `standard-logical` | `propext`, `Quot.sound`, `Classical.choice` |

Every declaration is labelled from its own exact transitive axiom set and must fit the claim;
neither an `IO` type nor recursion determines it. Compiler-trusting axioms (from `native_decide`,
`decide +native` or `bv_decide`) fit no profile and are reported separately.

Regula calculates this set from the declarations that Lean's kernel replayed. The set can be larger
than the set that `#print axioms` shows. For an imported declaration, `#print axioms` reads the
axiom table that Lean wrote for its module, and that table can omit axioms. For example, Lean
4.34.1 writes no axiom for `Float`, but the constructor of `Float` reaches `propext` and
`Quot.sound`. The audit reports each declaration for which the table omits an axiom, and it does
not fail it for that.

`execution` states what you claim about compiled code
([standard §7.6](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#76-classify-lean-computation-mechanisms-exactly)):

| Mode | Meaning |
| --- | --- |
| `report` (default) | Every execution boundary reached from an owned executable root is reported with its kind and correspondence state; trusted boundaries are recorded, not failed. |
| `checked` | Additionally fails on any trusted boundary your project or a dependency owns: an unproved `implemented_by` replacement, a `csimp` equality whose proof is not admitted, an `extern`, unsafe or partial code, or a compiler-trusting proof. A constant and the `partial` implementation Lean runs for it (a constant of `partial` definition safety) are one finding and one counted boundary, not two: a recursor that Mathlib's `compile_inductive%` compiled, or a dependency's `partial def`, is reported once per root, in a finding that also names that implementation (`…, with its implementation …`), the recursor's generated one or the `partial def`'s `_unsafe_rec` helper. A `partial def` that an `implemented_by` replacement or a `csimp` equality names as its target is not such an implementation: it keeps its own finding, which names its helper, and its own count, beside the replacement's or equality's. A later record of one trusted boundary in a root (the same constant, kind, replacement and toolchain origin, as two constants of one `csimp` equality's type give) is reported and counted with the first. The Lean toolchain's own replacements, externs, and unsafe and partial code (in `Init`, `Std` and `Lean`, checked by where Lean loaded the module from, not by its name) are its trusted base: they pass, and the default output gives only their count; `--verbose` and `--json-out` list each once for the whole audit, with the environments and roots that reach it. The account covers the code your roots reference; code a program loads or evaluates by name at runtime (for example with `Lean.Environment.evalConst` or a spawned process) is outside it. |

In both modes an unresolved path blocks the execution claim. Native arithmetic, the Lean runtime
and the toolchain's own library code remain trusted in every mode; the checker verifies Lean
source, not the compiler or the machine.

## 4. Run `lake lint`

From the project root:

```sh
lake lint                                  # incremental elaboration + current policy
lake lint -- --fresh                       # isolated copy built from empty output
lake lint -- --json-out tmp/regula.json    # also write the JSON report
lake lint -- --explain-config              # read-only: manifest, scope, profiles, stages
```

The driver builds every manifested library and executable by its explicit Lake target, with
warnings as failures, and inspects the completed environments: each library in one, and each
claimed executable's root in one of its own, since every root defines `main` (a root inside
its library is inspected there, not in the library's environment). An environment waits for the
claimed libraries it imports and reuses their kernel check of the modules it loads from them,
when those load from byte-identical `.olean` files (including `.olean.private` parts) in both,
instead of repeating it; libraries that do not import one another are inspected side by side.
So each claimed library module is kernel-checked once per audit, in its own library's
environment (or, where claimed libraries import one another, in the first environment that
loads it), and again only where the conditions for reuse cannot be established
([admission reuse](proofs-and-boundaries.md#producers) lists them and the modules they leave
replayed in each environment). It re-evaluates current policy even when every module is cached.
Run it from the project root without `-d`: it refuses a working directory that is not the
workspace that dispatched it. Its exit status separates the outcome:

| Exit | Outcome |
| --- | --- |
| 0 | `ACCEPTED`: the audit constructed its accepted result for the selected mode. |
| 1 | `VIOLATION`: completed policy rejections, for example [RG1001]–[RG1009], [RG3002], or [RG2004] for a claimed import of a module outside every library. |
| 2 | `INVALID CONFIGURATION`: only [RG2002] manifest/scope rejections, an invalid driver argument, a working directory that is not the dispatching workspace, or `--help`/`--explain-config`, which run no audit. |
| 3 | `INCOMPLETE`: an incomplete finding, for example [RG2001], [RG2003], [RG2005] or [RG3001], a failed audit-worker build, a failed audit worker ([RG2001], whose detail carries the worker's error), a working directory outside any Lean project or whose workspace fails to load, or an error that escaped the audit. It takes precedence over violations reported in the same run. |

The success line names its coverage: an incremental run is "incremental project acceptance over
existing build state, not a fresh-source audit"; only `--fresh` is fresh whole-project
acceptance. An audit that records a result without accepting it prints its findings, then one
summary line that counts them by impact, for example
`FAIL: 1 violation(s), 25 incomplete finding(s)`, and the driver prints the outcome line
`regula lint: INCOMPLETE (exit 3)`. The report's `status`, the summary counts and the exit code
are all derived from that one recorded result (`Regula.Checker.Lint.Observation`), which holds the
rule and `impact` of each reported diagnostic: each count is the number of findings of that
impact (`tally_eq`), an incomplete finding makes the run `INCOMPLETE` whatever violations it also
counts (`Observation.exitCode_incomplete`), and `VIOLATION` requires a violation and no incomplete
finding (`Observation.exitCode_violation`). A run that fails before recording a result, such as a
failed audit-worker build or an invalid argument, prints its error and the outcome line only.

While the claimed targets build, the driver shows Lake's own progress line for each job that
does work (`✔ [3/10] Built Widget (1.2s)`), including a cached module whose warnings Lake
replays; an up-to-date module without warnings prints nothing. `--verbose` adds every classified
declaration, each execution root with a boundary the toolchain does not own or an unresolved path,
every entry of the toolchain trusted base, and the checker's timing spans (`verification phase …`,
`diagnostic span: …`), which default output omits.

Regula keeps its working files in `.lake/regula-scratch/` of the project: the isolated copy of a
`--fresh` run and the copies of Lean sources it compiles. It removes each directory there when
the run that made it returns. A run that is killed leaves its directory, with those `.lean`
copies, until the next Regula run in the project removes it. `.lake/` is Lake's own output
directory, so a tool that walks your sources and skips it never sees these files.

**A first run usually stops at build warnings.** Rules are inspected only after a build without
warnings ([RG2003]), so a warning, such as a missing docstring, makes the run `INCOMPLETE` (exit 3)
with the compiler's message before any foundation rule is checked. The same holds for your first
`sorry`: Lean warns `declaration uses 'sorry'`, so it is reported as [RG2003], not [RG1002]; silencing
the warning does not help, because the hole is then reported as [RG1002].

Lake's artifact cache does not change what a run checks. The audit's builds do not read or
write that cache, whatever `enableArtifactCache` or `LAKE_ARTIFACT_CACHE` says. Lake keeps no
compiler messages for a module that it restores from the cache. Thus the audit elaborates again
each claimed module that Lake restored from the cache.

For CI, provision the toolchain and dependencies, then run the driver as its own step so its
exit status fails the job; use `--fresh` where the claim is fresh-source conformance, since
incremental evidence trusts the build traces that Lake recorded in the project:

```yaml
- name: Regula
  run: lake lint -- --json-out tmp/regula.json
```

Lake details that affect what ran:

- Arguments for the driver follow `--`; Lake prepends `lintDriverArgs`. Positional module
  arguments before `--` affect only Lake's builtin linters.
- `lake lint --builtin-only` skips the driver and is **not** Regula enforcement: it exits 0 with
  a Regula violation present. `lake lint --builtin-lint` runs the builtin linters and then the
  driver, and a failing driver determines the exit code; builtin linting needs module arguments
  (for example `lake lint --builtin-lint Widget`) when the default target is not a library, such
  as the build-lint `policy` target. `lake check-lint` only reports whether a lint command is
  configured.
- Lake has one `lintDriver` per package. A project that keeps another driver (for example
  `batteries/runLinter`) runs Regula as its own step with `lake exe lint`; see
  [community linters](#community-conventions-and-linters).
- A `lakefile.lean` project can also enforce during plain `lake build` with the
  [build-lint example](../../examples/build-lint/)'s sole-default `policy` target
  ([standard §7.11](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#711-opt-in-enforcing-build-linter));
  `lakefile.toml` has no custom targets. Direct `lean`, editor elaboration and an explicit
  build of another target never run the strict gate.
- `lake exe axiomGate` runs the same audit body directly: fresh by default, over the incremental
  build with `--incremental`, and as the build-lint `policy` target runs it with `--build-lint`
  (`lake exe axiomGate -- --help` lists every option);
  `lake exe axiomGate --file F.lean --claim standard-logical` audits one file, which is never
  project coverage. Every `axiomGate` audit uses `lake lint`'s exit codes: 0 accepted (or, for
  `--file` without a conforming claim, classified), 1 violation, 2 invalid configuration or
  invocation, 3 incomplete. An audit that recorded a result exits with that result's code, and 3
  when it recorded none, failed after recording a success (`Regula.Checker.Lint.gateExitCode`) or
  stopped on an error; `lake lint` reports the code its own audit returned
  (`Regula.Checker.Lint.classify_gateExitCode`). That audit builds with the driver's audit-build
  marker, so a standalone `axiomGate` run can differ: there a live Regula finding stops the
  warning-free build check as incomplete (3). `--file` prints only the declarations with a
  finding; `--verbose` lists every classified declaration. `lake exe docFenceAudit` checks Lean
  examples you keep in Markdown under `docs/` with the [fence protocol](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#77-check-lean-documentation-verbatim).

## Update Regula

To move to a new release, change the tag, and your `lean-toolchain` when the release supports
another toolchain (the [compatibility table](#1-require-regula) lists each), then:

```sh
lake update regula
lake exe regula init
lake lint
```

`lake update regula` updates only `regula`. Running `init` again rewrites a skill file that
differs from the new release's briefing and adds any option the new release requires; it changes
nothing else. A project that also uses Mathlib moves Mathlib to the same Lean release the usual
way. Each finding's rule link, and the link the refreshed briefing gives for citing a rule, then
targets the new release's pages.

Regula v0.3.0 and earlier kept those working files in `tmp/.regula-scratch/` instead. A later
release neither writes nor removes anything there, so delete `tmp/.regula-scratch/` once after
upgrading.

## Read a finding

Every finding carries what it needs to be fixed, in the terminal, the editor and the JSON report:

```text
RG1001 [violation; freshFile; claim=kernel-only; Widget/Basic.lean:2:6]: reflexive: …
  fix: Turn the assumption into a hypothesis (…) of the results that need it, or replace the axiom with a proof.
  rule: https://rbeauchamp.github.io/regula/dev/rules/RG1001/ (offline: lake exe regula explain RG1001)
  requirement: A claimed module declares no logical `axiom`: …
  why: An axiom extends Lean's logic for everything that imports it. …
  common rewrites:
  - If the statement is provable, prove it: replace `axiom name : P` by `theorem name : P := proof`.
  …
  compliant example (examples/rules/RG1001/Fixed.lean):
    /-! # Reflexivity

    Reflexivity for every natural number. -/
    theorem reflexive (n : Nat) : n = n := rfl
RG1001 [violation; freshFile; claim=kernel-only; Widget/Basic.lean:3:6]: symmetric: …
  fix: Turn the assumption into a hypothesis (…) (full guidance: first RG1001 finding above)
```

The first line states what is wrong and where (`FILE:LINE:COLUMN` in Lean's own coordinates). The
first finding of each rule in a run adds its requirement, rationale, rewrites and checked
compliant example; later findings of that rule point back to it. The rule link opens the rule's
page in the [rule reference](https://rbeauchamp.github.io/regula/dev/rules/) of your installed
release (`…/regula/v/<version>/rules/<ID>/`; an unreleased build links the development pages
under `/dev/`), where the [rule index](https://rbeauchamp.github.io/regula/dev/rules/) shows each
rule's scope, reason and a violating and corrected example produced by the real checker.

Lean also generates declarations from the ones you write. In a project or file audit, a
declaration-policy finding about one of them, such as [RG1005], is reported
at the declaration Lean generated it from, following the chain to its end, and, unless Lean
recorded a range of its own for it, as for a constructor or a field, located at that
declaration's range, when it belongs to one of the families the [RG1005] guidance names (`lake exe
regula explain RG1005`), from the same list the checker runs:

> `lake lint` groups a declaration Lean generated under the one it came from if it is a constructor; projection; recursor such as `casesOn`; equation lemma; reserved name such as `f.induct`; matcher; fixpoint helper; structural helper; auxiliary declaration such as `f._proof_1`; constructor lemma; type construction; field default; recursion helper `f._unsafe_rec`. Other declarations keep their own location. Fix the one reported or a definition it uses that adds the axiom.

Each family is named by an example, not by every member; the
[enumeration of the declarations Lean v4.34.0 generates](proofs-and-boundaries.md#generated-declaration-families)
lists them all, with the family that covers each or why it keeps its own location. So
`Channel.mk.injEq`, generated from the constructor `Channel.mk`, is reported at the structure
`Channel`. The [RG1005] findings under one declaration at one location print as one block, which
lists each declaration's axioms and says where to fix them; a generated declaration with a range
of its own, such as a constructor or a field, prints as its own block under the same declaration.
The closing `FAIL` summary counts the attributed ones in one line; the JSON report keeps one
diagnostic per declaration:

```text
RG1005 [violation; freshProject; claim=kernel-only; Widget/Basic.lean:4:4]: countdown: it and 3 declarations Lean generated from it exceed the claim
  - countdown: countdown (def) type=Nat → Nat axioms=["propext", "Quot.sound"] -> choice-free
  - countdown._proof_1: countdown._proof_1 (theorem) [Prop] roles=["internal"] type=… axioms=["propext", "Quot.sound"] -> choice-free
  - countdown.eq_1: countdown.eq_1 (theorem) [Prop] type=… axioms=["propext", "Quot.sound"] -> choice-free
  - countdown.eq_def: countdown.eq_def (theorem) [Prop] type=… axioms=["propext", "Quot.sound"] -> choice-free
  attributed: 3 declarations of these are generated by Lean from countdown and reported under it; change countdown or a definition it uses that introduces the axiom
  fix: Prove the same statement with fewer axioms, or deliberately raise the surface's claim …
```

Which family a declaration belongs to, and what it was generated from, is read from what Lean's
environment records about it, never from its name alone; the
[enumeration](proofs-and-boundaries.md#generated-declaration-families) names the fact read for
each family. A recursion helper `f._unsafe_rec` is related by Regula's own observation that
Lean's recursion compiler regenerates it from `f`. A declaration you write keeps its own
location, because Lean records its source range, and it is not grouped under another declaration
by its name: a `Word.ofNat` you write for a structure, or a theorem you name `f._proof_8`, is
reported on its own. A declaration a metaprogram adds without a range is reported on its own
unless a family's environment fact holds of it, as it can when it is named like a generated
declaration. An elaborator Lean names `«_aux_…»` inside a namespace is reported on its own, and so
is a derived instance, or an enumeration's `ofNat` from deriving `DecidableEq`: Lean records no
relation between it and the type.

## Machine-readable report

`lake lint -- --json-out PATH` writes one JSON document, result schema 12, whatever the outcome;
the path is first written as an incomplete result, so a stale report is never mistaken for this
run's. Its main members:

| Member | Meaning |
| --- | --- |
| `schemaVersion` | `12`. Also `producerVersion`, `toolchain` and `sourceRevision` of the Regula build. |
| `status` | `completed` (accepted), `rejected` (a violation was established and no finding is incomplete), `incomplete` (evidence was missing) or `classified` (a file inspection with no conforming claim). For an audit that recorded its result and then finished, it and the diagnostics determine the exit code. |
| `stages`, `stagesCompleted`, `stagesNotRun`, `complete` | The run's required stages and which completed, including the stages that finished before the run stopped. `complete` is `false` when the run stopped early, so fixing the reported findings can reveal more. |
| `diagnostics` | Every finding in printed order, one per declaration even where the text groups them, with `id`, `impact`, `severity`, `mode`, `claim`, `location` (for source, its `uri`, byte and LSP ranges and its `sourceText`, an index into `sourceTexts`; for a module, its `name`), `arguments`, `text`, `remedy` and `helpUrl`. `arguments.declaration` (or `root` for an execution finding) is the name as Lean prints it, such as `"Widget.countdown.eq_1"`. For a declaration-policy finding of a project or file audit or of a rule example ([RG1005] and the other rules decided per audited declaration), `arguments.sourceDeclaration` names the declaration Lean generated the declaration from, at the end of that chain, or is `null` for a declaration Lean did not generate from another; for a generated declaration, `location` is its own range when Lean recorded one, and otherwise that source declaration's range when Lean recorded one, with `related` naming the declaration's own module. Other declaration findings carry no attribution: a documentation example's, a material-documentation one ([RG5002], [RG5003]) and the editor linter's record `null` and the declaration's own location. A declaration whose recorded selection range leaves its recorded range, as Lean records for the definitions of a `macro_rules` command over several syntax kinds, is located at its range, which is then its selection range too. |
| `rules` | Once per fired rule: `requirement`, `rationale`, `remedy`, `rewrites`, `compliantExample`, `correction`, `helpUrl` and the offline `explain` command. |
| `sourceTexts` | Every distinct source text of the document, once each. A `sourceText` member, wherever it occurs, is the index of its text in this array. |

The document holds each source file's text once, however many findings are in the file. A source
location is its `uri`, its ranges and a `sourceText` index, and its byte ranges are offsets into
`sourceTexts[sourceText]` (other members omitted here):

```json
{
  "sourceTexts": ["theorem reflexive : 1 = 1 := by\n  sorry\n"],
  "diagnostics": [
    { "id": "RG1002",
      "location": { "kind": "source", "uri": "/work/widget/Widget/Basic.lean", "sourceText": 0,
        "range": { "startByte": 0, "endByte": 39 },
        "selectionRange": { "startByte": 8, "endByte": 17 } } }
  ]
}
```

The same member carries the text wherever else the document records a source: in
`sourceAccount`, in `scope` (its `sources`, each surface's `frontendTranscripts` and its report's
`sourceBindings` and `histories`) and in the snapshots of `acceptance`. Earlier schemas repeated
the text in each of those members and in every source location (as `source`, `content`,
`sourceContent`, `before` and `after`). Project configuration files stay inline, in `request`,
`effective` and `scope.configuration`.

`scope` holds the audit's account. Each environment report in it (`scope.surfaces[*].report`,
each `executables[*].report`, and `scope.report` for a file audit) lists its `declarations`, each
with `prettyType`, its type as Lean prints it, and its `execution`, the account of what each
executable root reaches. A declaration also has `type`, the `repr` of its kernel type
expression, only when the audit is run with `axiomGate`'s `--kernel-types` option (`lake exe
axiomGate -- --json-out PATH --kernel-types`), which `lake lint` does not take; earlier schemas
always wrote it. `execution` stores what the environment's roots reach once, and each root as a
short entry:

```json
{ "names": ["Nat.add", "Widget.double", "Widget.twice"],
  "modules": ["Init.Prelude", "Widget.Basic"], "nameModules": [0, 1, 1],
  "compilerEdges": [[1, 0], [2, 1]], "logicalEdges": [[1, 0], [2, 1]],
  "candidateEdges": [], "historyEdges": [], "currentReplacementEdges": [],
  "activeSimplificationEdges": [], "helperEdges": [],
  "boundaries": [
    { "node": 0, "name": "Nat.add", "module": "Init.Prelude", "boundary": "native-runtime",
      "correspondence": "trusted", "owned": false, "replacement": null, "evidence": null,
      "toolchainOrigin": { "module": "Init.Prelude", "actual": "…", "expected": "…" } } ],
  "unavailableCode": [],
  "roots": [
    { "name": 1, "module": "Widget.Basic", "unresolved": [], "requiresCode": true },
    { "name": 2, "module": "Widget.Basic", "unresolved": [], "requiresCode": true } ] }
```

A number in an edge, in `node`, in `unavailableCode` or as a root's `name` is an index into
`names`; `nameModules[i]` is the index in `modules` of the module of `names[i]`, or `null`. A
root's account follows from its entry:

- its reached names are those the walk from the root visits: start with the root; take the name
  queued last, and if it was not yet visited, visit it and queue the targets of its
  `compilerEdges`, `candidateEdges`, `historyEdges`, `currentReplacementEdges`, `logicalEdges`
  and `helperEdges`, in that order and each in listed order;
- its edges in each channel are the listed edges that leave a reached name;
- its boundaries are the `boundaries` records of its reached names, in visit order, and a
  boundary's compiled callers are the reached names with a compiler edge to its name;
- its required code is the targets of its compiler edges, and the root itself when
  `requiresCode` is `true`; its unavailable code is the required code listed in
  `unavailableCode`;
- `unresolved` lists the paths the analysis could not resolve for this root.

An environment without executable roots has the same object, with every list empty. A root
entry may instead hold its whole account as `explicit`; Regula writes that only for an account
the derivation above does not reproduce. A reader that accepts everything Regula's own reader
does also takes an object with a `verbatim` member as that member's value, the accounts in full,
and any other `execution` value that is not an object with `roots` as it is; Regula writes those
only when its reader would not return the accounts from the shared form. Earlier schemas wrote
`execution` as an array with every root's account in full (`name`, `module`, `boundaries`,
`unresolved`, `compilerEdges` and a `closure` of `nodes`, `visits` and the edge lists), so a
name, edge or boundary several roots reach was written once for each.

The other members named `execution` are a surface's or a file audit's execution claim and the
request's execution mode: strings or `null`, written unchanged. The acceptance account's
per-environment counts, which earlier schemas also named `execution`, are
`acceptance.account.executionSummary`. Its `boundaries`, `checked` and `trusted` count the
boundaries reported on their own, as the text does: a `partial` implementation (a constant of
`partial` definition safety, such as a `partial def`'s `_unsafe_rec` helper) is counted with the
trusted boundary that names it as the code run in its place where neither is the toolchain's,
and a later record of one trusted boundary of a root with the first, while a root's account
above keeps every boundary record.

Every Lean name in the document, in `diagnostics`, `scope` and `acceptance` alike, is written one
way: as the text Lean prints for it (`Name.toString`, which escapes a component with `«»` where it
can). Only where Lean's own parser (`String.toName`) would not read that text back as the same
name, for example for a component containing `»`, is the name written instead as its structural
components: an array, innermost first, of `["str", s]` and `["num", n]`. A string is therefore
always the printed name, and earlier schemas' arrays remain only for such names.

The exit status is the stable pass/fail contract; `status` and `complete` say why. Treat the
report as observations, never as a Lean proof: its consistency checks catch writer regressions,
not a report edited by hand.

## Receive diagnostics while editing

Import `Regula.Linter` from a module your project already imports widely (the
[TOML example](../../examples/lake-lint-toml/) imports it in `Gadget/Double.lean`). The
supported editor is VS Code with the Lean 4 extension. Completed commands and modules then show
warnings with codes `Regula.RG1001`–`RG1007`, `RG1009`, `RG2002` and `RG2005` at the declaration, plus
`RG5001`–`RG5003` once the module elaborates without errors, each with its fix, rule link and
offline `explain` command; the infoview adds a **View explanation** link. `RG2005` means a
finding needs evidence only `lake lint` collects.

Execution closure ([RG3001]/[RG3002]), coverage ([RG2004]), build and warning checks ([RG2003]) and fresh
admission run only in `lake lint`, the build-lint `policy` target or `axiomGate`. A clean editor
buffer means no current local findings, not a project result, and `set_option linter.regula
false` changes only local feedback. `lake lint` turns the local linter off for its own build
and reports the same rules itself, as `VIOLATION`.

## Community conventions and linters

Regula's rules are Lean correctness rules.
[Standard §6.7](https://rbeauchamp.github.io/regula/dev/standard/6-code-organization/#67-community-conventions-and-linters)
also requires the Lean community's baseline for style, naming and documentation form, as the
community's own linters enforce it: Mathlib's [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[documentation](https://leanprover-community.github.io/contribute/doc.html) guides for code that
depends on Mathlib, and Lean's
[standard library style guide](https://github.com/leanprover/lean4/blob/master/doc/std/style.md)
and [naming conventions](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md) for
core-only code.

- **Required options.** Every claimed library and executable enables `linter.missingDocs`, turns
  off automatic implicits
  ([standard §7.1](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#71-declare-the-elaboration-environment))
  and, in a project that depends on Mathlib, enables the syntax linters Mathlib builds with,
  except the three that enforce policies of the Mathlib repository itself. `init` writes these
  (into each claimed target's own configuration instead when the manifest excludes a root target
  or another claimed target's `-D` sets the option, and none that a `-D` of the target sets):

  ```toml
  [leanOptions]
  linter.missingDocs = true
  autoImplicit = false
  relaxedAutoImplicit = false
  # With Mathlib: its standard set, without its Mathlib-repository linters.
  weak.linter.mathlibStandardSet = true
  weak.linter.style.header = false
  weak.linter.hashCommand = false
  weak.linter.style.longFile = 0
  ```

  The last four lines apply only with Mathlib. The excluded linters enforce Mathlib's
  contribution header, its ban on `#` commands such as a passing `#guard`, and its file-length
  limit; turning off the header linter also turns off its checks that the module docstring comes
  first and that no import repeats, which [RG5001] checks instead (standard §5.3 and §6.4).
  In `lakefile.lean` the same options are
  ``leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`weak.linter.style.header, false⟩, ⟨`weak.linter.hashCommand, false⟩, ⟨`weak.linter.style.longFile, .ofNat 0⟩]``.
  The linters report through build warnings, so `lake lint` reports each as [RG2003] (`INCOMPLETE`,
  exit 3). [RG2006] checks every option above in Lake's resolved configuration of each claimed
  target, and rejects a target-wide `false` for any other linter and any `-D` in `moreLeanArgs`
  or `weakLeanArgs` that overrides them (`VIOLATION`, exit 1); it does not read `set_option` in
  source, which review checks. Where the community's guidance accepts an exception, disable that
  linter for the one declaration (`set_option linter.style.longLine false in`) with a comment
  giving the reason. Never disable Lean's default warnings, such as `linter.unusedVariables` or
  `warn.sorry`.

  To keep Mathlib's header linter on, replace `weak.linter.style.header = false` with `true` and
  give the license line it expects in `weak.linter.style.header.license`, a `String` that defaults
  to Mathlib's Apache 2.0 statement at the pinned Mathlib. [RG2006] accepts the header linter only
  with that option set to a nonempty string in `leanOptions`, and the linter then also checks the
  copyright and authors lines of every module that the library root imports. A TOML key cannot
  both hold a value and have sub-keys, so Lake rejects `weak.linter.style.header.license` beside
  `weak.linter.style.header` in a `[leanOptions]` table; in `lakefile.toml` write `leanOptions` as
  an array of `{name, value}` entries instead, a top-level key before any table:

  ```toml
  leanOptions = [
    {name = "linter.missingDocs", value = true},
    {name = "autoImplicit", value = false},
    {name = "relaxedAutoImplicit", value = false},
    {name = "weak.linter.mathlibStandardSet", value = true},
    {name = "weak.linter.style.header", value = true},
    {name = "weak.linter.style.header.license", value = "Released under the MIT license as described in the repository LICENSE."},
    {name = "weak.linter.hashCommand", value = false},
    {name = "weak.linter.style.longFile", value = 0},
  ]
  ```

  In `lakefile.lean` add both to the same `leanOptions`:
  ``⟨`weak.linter.style.header, true⟩, ⟨`weak.linter.style.header.license, "Released under the MIT license as described in the repository LICENSE."⟩``.
  A `-D` extra `lean` argument does not configure the license line for [RG2006].
- **Batteries' environment linters** (`docBlame`, `simpNF`, `unusedArguments` and others) are
  recommended. They report through their own command and lint the built modules, so run
  `lake build` first. Keep one lint driver and run the other as its own command:

  ```sh
  # lintDriver = "regula/lint"
  lake lint && lake build && lake exe runLinter
  # lintDriver = "batteries/runLinter"
  lake build && lake lint && lake exe lint
  ```

  Each command's exit status covers only its own checks, so CI requires both.

A community linter's pass establishes only what that linter checks, and a Regula pass says
nothing about style no enabled linter checks. This configuration was observed on small Mathlib and
Batteries adopters in the `lakefile.toml` spelling; these are bounded observations, not proofs.

## Complete semantic review

A green `lake lint` establishes hole-freedom, exact axiom sets, module coverage and boundary
classification. It does not establish that your theorems say what your prose says, that your
contracts are complete, or that your types encode the invariant you advertise. Those are the
semantic-review rows of [standard module 8](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/),
including `SCOPE-*`, `TYPE-*`, `THEOREM-*`, `COMP-01`, `COMP-04`, `DOC-01` and `DOC-02`.
Conformance is the whole checklist with one terminal result (`PASS`, `FAIL` or `INCOMPLETE`),
not the linter alone.

For a function that acts as a checker (a parser, validator or admission function), you can state
which direction you proved in the registration itself. `Regula.Contract` provides
`Regula.Decides accepts spec` for both directions and `Regula.DecidesSoundly` or
`Regula.DecidesCompletely` for a deliberate one-way guarantee, each with a witness that the
function accepts or refuses some input, so a function that refuses everything cannot be
registered as sound. Register `theorem c : Regula.ExecutableContract check (Regula.Decides (· =
true) Spec)`, with `fun g => Regula.Decides accepts Spec (Function.uncurry g)` for a function of
two arguments, and state `Spec` without `check`. The accepted account then reports the kind
and, for a one-way kind, the direction it leaves open.

[RG1009] refuses the registration when `Spec` and `check` reach one function with a result of
`Bool` or `BEq`. The acceptance predicate counts as `check` does, and the search reads at any
depth. State that condition as a proposition in `Spec`, and let `check` decide it. The rule
compares names. A copy of a test under a second name passes, and so does a test of Lean's own
library.

The account names each other function that `Spec` reaches first and that `check` or the
acceptance predicate also reaches. The kind does not establish that such a function is the
intended one, and no registration is refused for it. That function remains review, and the
account is the list. The [RG1007] and [RG1009] pages give the two classes of these functions and
the limits of the search.

State the kind about the function applied to every one of its arguments. [RG1007] refuses every
kind whose result is still a function. The restriction is structural and conservative: a kind
whose acceptance predicate reads that result at one fixed value of the remaining argument is
about one slice of the function and says nothing of it at another value, and a kind whose
acceptance predicate quantifies over that argument is refused too, because the rule does not
read the acceptance predicate. For both, supply the argument: add one more `Function.uncurry`
for each further argument, or use a structure of all the arguments.

Two forms cover the functions that this form does not reach (standard §3.8):

- **A dependent argument type, or a type, instance or proof argument.** Declare a structure
  whose fields are the arguments, and state the kind about the function applied to every field,
  in the order of the fields: `fun g => Regula.Decides accepts Spec (fun input : Input => g
  input.a input.b input.c)`, with `Spec` over `Input`. For two arguments a pair is enough
  (`Prod`, `Sigma`, `PSigma` or `Subtype`). Give each field once and leave none out: [RG1007]
  refuses a function that fixes an argument or repeats a field, because it decides the function
  on part of its domain, and a structure with a field the function does not take, because such
  a field can restrict the domain. The type must have one constructor and no index, as a type
  declared with `structure` has: a type with an index holds only some of the tuples of its
  fields. Do not nest dependent pairs for three or more arguments:
  each projection of a pair carries the pair's type, and the statement grows by a large factor
  with each argument. State a kind about a function with universe parameters at those
  parameters (`@check.{u}` in a theorem with the universe parameter `u`), with witnesses at
  every universe level, such as a list of `PUnit`; [RG1007] refuses a kind stated at other
  levels.
- **A result type that depends on the arguments**, such as `Except String (Admitted x)`. State
  one of the three kinds about an erasure of the result that `Regula.Contract` provides:
  `Regula.Dependent.isOk g` (whether an `Except` result is `.ok`) or `Regula.Dependent.isSome g`
  (whether an `Option` result is `some`). The registration is `fun g => Regula.Decides (· =
  true) Spec (Regula.Dependent.isOk g)`, or the same with `g` applied to the fields of a
  structure. [RG1007] reads these two erasures and no other: an erasure of your own can read
  the type of the payload, and so can accept or refuse by what the type is and not by what the
  function returns. A result type that neither erasure fits has no kind; return `Decidable p`,
  or register an ordinary requirement. A result of a subtype type that depends on the input,
  such as `{r : Nat // r ≤ x}`, is such a type until
  [#243](https://github.com/rbeauchamp/regula/issues/243) is decided: an erasure that returns
  the value of the subtype would keep a free acceptance predicate on a data value.

The account reports the kind of such a registration as it does for every other one.

To make that registration a requirement, mark the function with `@[regula_decision]` (`import
Regula.Decision`, or `meta import Regula.Decision` in a file that is a `module`). A function whose
own module cannot import `Regula.Decision` is marked from another module of the same library, with
`attribute [regula_decision] check`; marking a function of another library or of a dependency
stops the audit, which decides the requirement only for the functions its inventory declares. The
audit then rejects a marked function unless a decision registration in the same library decides
it, or its result type is `Decidable _`, which carries a proof either way ([RG1008]). So deleting the
theorem while the function stays marked fails `lake lint`. The editor does not report this rule,
because a registration normally follows its function. Which functions you mark, and whether
`Spec` is the specification you intend, stay your review
([standard §3.8](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#decision-kinds), [RG1007]).
The [RG1008] page shows a marked function with and without its registration.

## Limits

- `lake lint` exits 0 only for an accepted run: `Regula.Checker.Lint.accepted_sound` and
  `RegulaPolicy.accept_iff` prove the success direction. Which rule a failure receives is proved
  only where a rule page's *Proved linkage* says so.
- Some adapters are operational code, not proved: [RG2001]/[RG2002] routing of escaped errors by
  message prefix, [RG1007] contract extraction, [RG2004] inventory checks, the documentation fence
  scanner and the [RG5001] header observation. `init`'s lakefile edits are text edits confirmed by
  reading the project again, not proved to realize the model.
- The command-line transcript names a finding's file and declaration; exact source ranges are in
  `--json-out` and the editor.
- The only supported editor is VS Code with the Lean 4 extension, and there is no latency claim.
- Regula has run on small adopters only, including a Mathlib-importing library accepted
  incrementally and fresh; there is no Mathlib-scale adopter claim. These are bounded
  observations, not theorems about the tools.
- Each release supports exactly one Lean toolchain. The nine
  [residual review obligations](architecture.md#coverage-of-the-standard) stay open; every
  accepted account lists them.

## What you are not asked to do

- **Checker qualification is not adopter conformance.** The `MUT-*` rows and the
  `checkerSelftest` suite qualify a checker implementation. An adopter using the shipped
  checker unchanged does not rerun them.
- **`freshChecker`** (fresh `leanchecker` over the serialized module graph) is optional
  defense in depth for the separate `MUT-05` claim, not part of the ordinary loop.

[RG1001]: https://rbeauchamp.github.io/regula/dev/rules/RG1001/
[RG1002]: https://rbeauchamp.github.io/regula/dev/rules/RG1002/
[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
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
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
