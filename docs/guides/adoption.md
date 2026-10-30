# Adopt Regula

A strict linter for Lean. Regula refuses proof holes, project axioms and proofs that trust the compiler. Each finding links to its rule page, which gives the fix.

This guide is the full procedure to adopt Regula. For a first try on one module, see [Try it](../../README.md#try-it) in the README.

The four steps below take a project from `require` to its first `lake lint`. They use the layout, the module names and the lakefile format of your project. A pass of `lake lint` does not replace the semantic review of the [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/) (see [semantic review](#complete-semantic-review)).

The normative definitions behind the steps are in
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
| `v0.11.1` | `leanprover/lean4:v4.34.1` | [v/0.11.1/](https://rbeauchamp.github.io/regula/v/0.11.1/) |
| `v0.11.0` | `leanprover/lean4:v4.34.1` | [v/0.11.0/](https://rbeauchamp.github.io/regula/v/0.11.0/) |
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

The release steps generate the table from the release data, and Regula's checks refuse a table that
disagrees with it; a row is added when a release's pull request merges, shortly before CI
publishes the release. The [releases page](https://github.com/rbeauchamp/regula/releases)
has each release's notes. Choose the newest release for your `lean-toolchain`, set your
`lean-toolchain` to its toolchain if you move, then require its tag.

The first release, `v4.34.0`, is legacy. Its tag is the number of its Lean release, not a
version of Regula. Thus in version order, its tag is above the tag of each later release, for
example `v0.10.0`. `git tag --sort=-v:refname` and the tag list of GitHub show it first. Do not
select a release by its position in such a list of tags. Select it from the table.

The two snippets below require the release of the first row of the table. The release pull
request sets their release when it adds that row, and Regula's checks refuse a change that makes
them require a different release.

`lakefile.toml`:

```toml
[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "v0.11.1"
```

`lakefile.lean`:

```text
require regula from git
  "https://github.com/rbeauchamp/regula" @ "v0.11.1"
```

Then fetch it:

```sh
lake update regula
```

Requiring `regula` adds exactly one package to your `lake-manifest.json`: `regula` itself. It
requires nothing beyond the Lean toolchain (no Mathlib, no Batteries) and imports only Lean's
core libraries, so it never pins a package your project also uses, and a project with Mathlib
keeps the Mathlib revision it pins.

### A program that lists directories

Regula reads the names in a directory through an `ls` program. Lean's `System.FilePath.readDir` cannot tell the end of a directory from a failed read. An admitted `ls` stops with a nonzero exit code after a failed read, and then Regula stops too. Regula admits a program only when the source of the program itself shows that it lists all names and reports a failed read. That source must be the source of the release that the first line of `ls --version` names exactly. Regula uses the first program of this table that it finds:

| Platform | Program | Where to get it |
| --- | --- | --- |
| Linux and macOS | GNU coreutils `ls` 9.0 to 9.12, as `ls` or `gls` on `PATH` | Ubuntu 24.04 and Debian 12 have it. On macOS, `brew install coreutils` gives `gls`. |
| Linux | GNU coreutils `ls` 8.32, as `ls` or `gls` on `PATH` | Ubuntu 22.04 and Debian 11 have it. |

Regula does not admit the `ls` of macOS. It reads directories through the `fts` functions of the system C library, and nothing that it reports names the release of that library. On macOS, install GNU coreutils with Homebrew. If Regula finds no admitted program, it stops and gives the reason for each program that it examined. The [assumptions of the construction](proofs-and-boundaries.md#assumptions-of-directory-enumeration) give the source lines of each admitted release.

Regula does not admit the default `ls` of these platforms. On them, install GNU coreutils `ls` of an admitted release, as `ls` or `gls` on `PATH`:

- Ubuntu 25.10 and later. Their default `ls` is the `ls` of uutils coreutils.
- Ubuntu 20.04 and RHEL 8. They have GNU coreutils 8.30.
- Alpine Linux and the other systems that get `ls` from BusyBox.
- macOS.

Regula refuses a release of GNU coreutils that is later than `9.12`, the latest admitted release. Its reason gives the first line of `ls --version` that it refused. Use an admitted release until a later Regula release admits the new one.

### When your Lean release has no Regula release

Each Regula release supports one Lean release. A patch release of Lean, for example `v4.34.1`, is a different release. Do one of these:

- Move your project to the Lean release of a Regula release. Set `lean-toolchain`, move Mathlib to a revision for that release if you use it, and run `lake update`.
- Require an older Regula release that supports your Lean release, from the [compatibility table](#1-require-regula).

If the two Lean releases are different, the `lakefile.lean` of this release of Regula stops before it compiles the checker, with the message `Regula's compiler guard stopped`. Older releases give a different message, or have no such guard. The text below gives the details.

Lake loads Regula with the Lean your project
runs. Regula `v0.2.0` through `v0.5.0` stop in Regula's `lakefile.lean` before anything compiles
when that Lean's version differs, naming both releases; they compare only the version, not the
compiler's commit, and the earlier `v4.34.0` tag has no such guard:

```text
error: …/regula/lakefile.lean:…: this Regula release supports only Lean leanprover/lean4:v4.34.0, but Lake is running Lean 4.33.0. …
```

This source revision guards the exact compiler instead: it declares one exact compiler version and
commit in [`RegulaPolicy.Compiler`](../../lean/RegulaPolicy/Compiler.lean).
A fresh configuration invokes that identity guard before building the checker.
Elan aliases may differ when they resolve to the same compiler. A
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
`lake exe regula doctor` reports the same mismatch for the compiler that built it, which `lake exe`
takes from your `lean-toolchain` unless an override selects another.

When no other dependency pins a
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
| Library globs | The glob that includes each module below the root of a library, in one case only. The package has one `lean_lib`, with one root and declared at the top level with no `globs`. In `lakefile.toml` it is a `[[lean_lib]]` table, not an inline table such as `lean_lib = [{ name = "Demo" }]`, and the glob is `globs = ["Demo", "Demo.+"]`. In `lakefile.lean` the `lean_lib` declaration has a `where` block or no fields, and the glob is ``globs := #[.andSubmodules `Demo]``. `doctor` reports a module of the claimed modules' import closure below that root, which neither the library nor an executable root includes. Each module that the glob adds is in that closure, the claimed roots included, with the same source file. A project from `lake new` gets it: its umbrella module imports `Demo.Basic`, and the default of Lake includes only `Demo`. In other cases, `doctor` asks for the glob ([step 3](#3-review-the-claimed-surface)). |

It never changes a value you set: a lint driver of your own, an option with another value, the
`globs` of a library and an existing manifest stay as they are, and `lake exe regula doctor`
reports each with its fix. A
required option that a `-D` extra `lean` argument of a target sets counts as set for that target:
`init` adds it to no configuration that reaches the target (`Regula.Setup.added_unargued`, over the
modelled setup and reading every `-D` candidate as [RG2006] does, and checked again after writing,
target by target, as `Regula.Setup.arguedBy_run` states), and `doctor` reports once that [RG2006]
requires those options in `leanOptions`, naming the entries to write there. It edits the lakefile
in place, in its own format, then reads the project again and puts back what the files it wrote held unless
nothing is left to write. A second run therefore writes nothing:
`Regula.Setup.plan_idempotent` proves that the plan of the result is empty over the modelled
setup, and that runtime check confirms the files as written match it. `init` ends by running
`doctor`.

`lake exe regula doctor` changes nothing. It prints each missing or wrong piece in the linter's
finding form, with the exact fix: setup findings for the lint driver, options, manifest, agent
guidance, the compiler your `lean-toolchain` selects (the one that built `regula`, which
`lake exe` builds with that toolchain's Lean; `doctor` starts no process and installs
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
import is still inspected. `lake new` writes none. `init` adds one only in the case that the
[table of step 2](#2-run-lake-exe-regula-init) states. `doctor` names each module that a library
leaves out:

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

A surface can also name other claimed surfaces in `decides`. Then its decision registrations can
decide the marked decisions of those surfaces
([complete semantic review](#complete-semantic-review)).

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

Regula calculates this set with `Lean.collectAxioms` over the declarations that Lean loads from your
build, without the axiom table that Lean writes for each module. The set can be larger than the
set that `#print axioms` shows. For an imported declaration, `#print axioms` reads the
axiom table that Lean wrote for its module, and that table can omit axioms. For example, Lean
4.35.0 writes no axiom for `Float`, but the constructor of `Float` reaches `propext` and
`Quot.sound`.

`execution` states what you claim about compiled code
([standard §7.6](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#76-classify-lean-computation-mechanisms-exactly)):

| Mode | Meaning |
| --- | --- |
| `report` (default) | The checker checks that the execution closure of each claimed executable resolves ([RG3001]). It does not report the execution boundaries. |
| `checked` | The checker also fails on each boundary that the closure reaches and that no admitted theorem binds ([RG3002]). A boundary is a departure that no module of the toolchain makes, such as an `implemented_by` replacement, a `csimp` rewrite or a recursion helper. Its theorem must be safe, and the profile must admit its axioms. Code that no theorem can bind fails with any theorem: an `extern` constant, a `partial` definition that is not a recursion helper, and a value that `initialize` sets. |

In both modes an unresolved path blocks the execution claim. Native arithmetic, the Lean runtime
and the toolchain's own library code remain trusted in every mode; the checker verifies Lean
source, not the compiler or the machine.

## 4. Run `lake lint`

`lake lint` runs the checker of Regula on the finished build of your project. The checker does not build. Thus build the claimed targets first, with warnings as errors, and replay the build in Lean's kernel:

```sh
lake build --wfail
lake check
lake lint
```

`lake build --wfail` decides [RG2003]: a claimed module elaborates with no error and no warning. `lake check` decides [RG2005]: Lean's kernel checks each constant again from an export of the build. On macOS, it is `lake check --inadvisably-no-sandbox`. Run `lake lint` from the root of your project. It reads the workspace of its working directory, or of the one argument that you give after `--`.

`lake check` imports each module of the default targets into one environment, and Lean refuses two modules that declare the same name. Thus a project fails `lake check` when its default targets hold two programs, each with a top-level `main`. [RG2002] makes each claimed target a default target, so a project can claim one such program at most. Give each other program its entry in a namespace. Start it from the root of an executable that is not a default target, and exclude that executable from the claim.

The checker reads one closed input. That input is the declarations that Lean loads from your build, the targets and modules of Lake, and your `foundation_manifest.json`. It reads no source text, message, option set in source, build log or list of files. Each rule is a function over this input. The [specification of the smaller Regula](https://github.com/rbeauchamp/regula/blob/main/specification/README.md) states the input and the rules.

The exit status gives the verdict:

| Exit | Verdict |
| --- | --- |
| 0 | Pass: the input has the closed form, and no rule reports a subject. |
| 1 | Fail: a rule reports one or more subjects. |
| 2 | Incomplete ([RG2001]): Lake or Lean cannot load the build, or the input does not have the closed form. |

These are some causes of an incomplete run:

- A module of a target has no compiled files. Build the claimed targets first.
- Lean cannot read an `.olean` file. A read error is a refusal, not an absent file.
- The manifest does not parse, claims no target, or claims a target as `compiler-trusting`.
- `LEAN_SYSROOT` is not set. `lake lint` and `lake exe` set it to the toolchain that Lake runs.
- The current directory differs from the workspace that Lake selected with `-d`. Run `lake lint` from that workspace's root.

## Update Regula

To move to a new release, change the tag. Also change your `lean-toolchain` when the release supports a different toolchain. The [compatibility table](#1-require-regula) lists each. Then run these commands:

```sh
lake update regula
lake exe regula init
lake build --wfail
lake lint
```

`lake update regula` updates only `regula`. Run `init` again to rewrite a skill file that differs from the briefing of the new release, and to add each option that the new release requires. It changes nothing else. A project that also uses Mathlib moves Mathlib to the same Lean release in the usual way.

## Read a finding

The checker prints one line for each finding:

```text
RG1001 Widget.reflexive (module Widget.Basic): declares an axiom https://rbeauchamp.github.io/regula/dev/rules/RG1001/
regula: fail, 1 findings
```

The line gives the rule ID, the constant, module or target that the rule reports, the detail, and the page of the rule in the [rule reference](https://rbeauchamp.github.io/regula/dev/rules/). The last line gives the verdict. `lake exe regula explain <ID>` prints the full rule offline: its requirement, rationale, remedy, rewrites and example pair.

The checker reports each constant that violates a rule, also a constant that Lean generated, for example `Widget.reflexive.eq_1`. Change the declaration that you wrote, or a definition that it uses.

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
  first and that no import repeats, which review checks instead under the written guidance of
  [RG5001] (standard §5.3 and §6.4).
  In `lakefile.lean` the same options are
  ``leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`weak.linter.style.header, false⟩, ⟨`weak.linter.hashCommand, false⟩, ⟨`weak.linter.style.longFile, .ofNat 0⟩]``.
  The linters report through build warnings, so `lake build --wfail` refuses each of them
  ([RG2003]). [RG2006] reads the options of the configuration of each claimed target by Lake. It
  refuses an option outside its allowlist, and each `-D` in `moreLeanArgs` or `weakLeanArgs` that
  sets such an option. It also refuses a plugin, a dynamic library and each other extra Lean
  argument. It does not read an option that a source file sets, because no record of such an
  option exists. Where the guidance of the community accepts an exception, disable that linter for
  the one declaration (`set_option linter.style.longLine false in`) with a comment that gives the
  reason. Do not disable the default warnings of Lean, such as `linter.unusedVariables` or
  `warn.sorry`.

  To keep Mathlib's header linter on, replace `weak.linter.style.header = false` with `true` and
  give the license line it expects in `weak.linter.style.header.license`, a `String` that defaults
  to Mathlib's Apache 2.0 statement at the pinned Mathlib. The linter then also checks the
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
- **Batteries' environment linters** (`docBlame`, `simpNF`, `unusedArguments` and others) are
  recommended. They report through their own command and lint the built modules, so run
  `lake build` first. Keep one lint driver and run the other as its own command:

  ```sh
  # lintDriver = "regula/lint"
  lake build --wfail && lake lint && lake exe runLinter
  # lintDriver = "batteries/runLinter"
  lake build --wfail && lake lint && lake exe lint
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

An equivalence without a witness is the law `Regula.DecisionEquivalence accepts Spec check`. It
states the two directions and no outcome, so it does not satisfy [RG1008] for a function registered
with `Regula.RegisteredDecision`. `law.toSoundly` or `law.toCompletely` gives a kind from the law and an
input that `check` accepts or refuses. The accepted account reports each registration of a kind or
a law with the laws and outcomes it establishes, each as its proposition.

[RG1009] refuses the registration when `Spec` and `check` reach one function with a result of
`Bool` or `BEq`. The acceptance predicate counts as `check` does, the declaration of its result
type included, and the search reads at any depth. State that condition as a proposition in
`Spec`, and let `check` decide it. The rule compares names. A copy of a test under a second
name passes, and so does a test of Lean's own library.

The search does not enter the declaration of the input type from the input. It reads the body of
the function abstraction of `Spec` under its variable. When `Spec` is a definition, alone or
applied to its variable alone, the search reads the body of that definition's value. It does not
follow a projection of the input back to the input type, or to the type that an `abbrev` input
type gives. So a test that only an invariant of the input type names is not counted, and the
account names it apart.

A `Spec` that names the input type in a different way, or that states the invariant, reads the
test. So does a `Spec` that reads a field with a result type that has such an invariant, unless
that result type is the input type. A definition that the body names among other terms has its
type read too. An example is `fun input => Spec input ∧ 0 < input.amount`. The type of `Spec`
names the input type, so the search reads the declaration of the input type there.

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

To make that registration a requirement, register the function with a declaration of the type
`Regula.RegisteredDecision` (`import Regula.Decision`, or `public import Regula.Decision` in a file
that is a `module`), such as `theorem check_registered : Regula.RegisteredDecision @check := ⟨⟩`. A
function whose own module cannot import `Regula.Decision` is registered from another module of the
same library. The audit decides the requirement only for a registered function of a claimed module.
It then rejects a registered function unless a decision registration in the same library, or in a
surface that names that library in `decides` (below), decides it, or its result type is
`Decidable _`, which carries a proof either way ([RG1008]). So deleting the
theorem while the registration stays fails `lake lint`. Which functions you register, and whether
`Spec` is the specification you intend, stay your review
([standard §3.8](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#decision-kinds), [RG1007]).
The [RG1008] page shows a registered function with and without its contract.

A project can keep its executing definitions free of a proof dependency. One library holds the
functions and does not import a proof library such as Mathlib. To carry the registration, it imports only
the toolchain and `Regula.Decision`, as a `public import` in a file that is a `module`. A second library imports the first library and a proof library, and it holds the
theorems. If the proof of a kind uses the proof library, you can write the kind only in the second
library. Keep the registration in the first library, and name that library in the
`decides` of the second surface:

```json
{ "library": "WidgetProofs", "claim": "standard-logical", "decides": ["Widget"],
  "rationale": "..." }
```

The decision registrations of `WidgetProofs` then count toward the registered functions of `Widget`.
The audit counts a registration only as the record of the `WidgetProofs` environment in the same
run. Also, that environment must load the module of the function from the same build output. The
registration must meet all requirements of `WidgetProofs`, and the function keeps the execution
claim of `Widget`. The account names the surface that each counted registration comes from. The
audit refuses a `decides` entry that names its own surface or no claimed surface.

## Limits

- No theorem yet relates a rule function of the checker to the violation predicate of its rule. Leaf #487 proves these contracts. Until then, a pass of the checker is an observation of the functions of `Regula.Rules`.
- The seven documentation rules are written guidance, and no check of Regula reads them. Review checks them, by standard §5.1 to §5.3 and §7.7. The specification retires them because each failure that they found is cheap to see and cheap to correct by hand. Thus each such failure is an accepted risk:
  - [RG4001]: a misplaced fence marker, a fence that is not closed, or Lean code outside a first-column `lean` fence.
  - [RG4002]: a `lean` fence that does not elaborate as printed with no warning, or that has a declaration that fails the declaration and axiom rules.
  - [RG4003]: a `lean-fail` fence that does not fail with one error that matches its pattern.
  - [RG4004]: a `lean-trusted-compiler` fence that does not elaborate with no warning, or that contains no compiler-trusting declaration.
  - [RG5001]: a claimed module with no module docstring as its first command after the imports, or with a repeated import.
  - [RG5002]: a public declaration that states a material claim, with no docstring.
  - [RG5003]: the docstring of a public material declaration, with no `# Intent` section that has text.
- The checker reads no option that a source file sets, no message and no command of a module. A command that runs code, for example `#eval` or `run_cmd`, leaves no record that the checker can read.
- [RG2006] reads an option by its name alone, as Lake gives it. `Regula.Allowlist.options` lists the names. So `linter.unusedVariables` is refused at `true` too. A `weak.` entry is refused even for an option that no module declares, although Lean ignores that entry. Delete such an entry.
- [RG2007] reads the environment extensions that the `.olean` files of a claimed module record. `Regula.Allowlist.extensions` lists the names. A claimed module cannot have a project's own macro, notation, syntax, elaborator, initializer or attribute.
  - A default of the form `:= by tactic` is refused too, because Lean records it as a `meta` declaration.
  - Put such code in a library that the manifest excludes, which no claimed module may import ([RG2004]).
  - Notation, tactics and data attributes of a dependency stay usable. An attribute that registers code, such as `norm_num` or `positivity`, is refused in a claimed module.
  - A data attribute that the list does not name is refused until a change of Regula names it.
  - The rule cannot see what leaves no record: a command that runs code, such as `run_cmd`, or a local attribute on an ordinary definition, such as `@[local macro k]`.
- `init` edits your lakefile as text. Then it reads the project again to confirm the edits. No theorem proves that the edits realize the model.

## What you are not asked to do

- **Checker qualification is not adopter conformance.** The `MUT-*` rows qualify a checker implementation. An adopter that uses the shipped checker unchanged does not do them again.

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
[RG2007]: https://rbeauchamp.github.io/regula/dev/rules/RG2007/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
[RG4001]: https://rbeauchamp.github.io/regula/dev/rules/RG4001/
[RG4002]: https://rbeauchamp.github.io/regula/dev/rules/RG4002/
[RG4003]: https://rbeauchamp.github.io/regula/dev/rules/RG4003/
[RG4004]: https://rbeauchamp.github.io/regula/dev/rules/RG4004/
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
