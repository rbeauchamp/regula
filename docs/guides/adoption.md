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

Regula is a Lake package named `regula`, like any other Lean tool. Its releases are tagged with
the Lean release they support, the Lean ecosystem's convention: `v4.34.0` supports
`leanprover/lean4:v4.34.0` and no other toolchain. The
[releases page](https://github.com/rbeauchamp/regula/releases) lists them; before the first
release, pin an exact commit of `main` instead. Set your `lean-toolchain` to the release's Lean
version, then require the tag.

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

## 2. Run `lake exe regula init`

```sh
lake exe regula init            # or: lake exe regula init --skill
```

`init` reads your project through Lake, then writes only what is missing:

| Piece | What `init` writes when it is missing |
| --- | --- |
| Lint driver | `lintDriver = "regula/lint"` (`lakefile.toml`, top level) or `lintDriver := "regula/lint"` (`lakefile.lean`, in the `package` declaration), so `lake lint` runs Regula. |
| Options | The `leanOptions` the rules require for every claimed target, each only where neither the package nor the target gives it a value: in the package's configuration when every root target is claimed (as the starter manifest claims them all), and otherwise in each claimed target's own `[[lean_lib]]`/`[[lean_exe]]` table or `lean_lib`/`lean_exe` declaration, so no option reaches a target the manifest excludes; while an existing manifest does not load or classify every root target, none, until `doctor`'s RG2002 finding is fixed. They are `autoImplicit` and `relaxedAutoImplicit` false and `linter.missingDocs` true, and, when your workspace contains Mathlib, Mathlib's standard linter set with its three exclusions ([community linters](#community-conventions-and-linters)). |
| Manifest | A starter `foundation_manifest.json` that claims every `lean_lib` as `standard-logical` with `report` execution and lists every `lean_exe` with the first library ([step 3](#3-review-the-claimed-surface)). |
| Agent guidance | A short `## Lean standard: Regula` section in `AGENTS.md` (created if needed), or with `--skill` the briefing as `.agents/skills/regula/SKILL.md`. `init` also rewrites `.claude/skills/regula/SKILL.md`, where Claude Code discovers project skills, whenever that file exists and differs from the installed briefing, but never creates it (copy the `.agents` file there for Claude Code). Both files are generated and owned by `init`: re-running it replaces local edits and prints each file it replaced. |

It never changes a value you set: a lint driver of your own, an option with another value and an
existing manifest stay as they are, and `lake exe regula doctor` reports each with its fix. It
edits the lakefile in place, in its own format, then reads the project again and restores every
file it wrote unless nothing is left to write. A second run therefore writes nothing:
`Regula.Setup.plan_idempotent` proves that the plan of the result is empty over the modelled
setup, and that runtime check confirms the files as written match it. `init` ends by running
`doctor`.

`lake exe regula doctor` changes nothing. It prints each missing or wrong piece in the linter's
finding form, with the exact fix: setup findings for the lint driver, options, manifest, agent
guidance, toolchain and any module below a library root that no library includes but a claimed
module imports (which `lake lint` rejects), and, once a manifest exists, the linter's own
manifest validation (RG2002) and option decision (RG2006) for every claimed target. It exits 0
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

## 3. Review the claimed surface

Conformance is claimed per Lake library or executable, and the checker discovers modules through
Lake's elaborated inventory, not through your umbrella import or a file list
([standard §7.2](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#72-define-surfaces-through-lake-semantics)).
Give every claimed library a glob that covers its modules, so a module your umbrella does not
import is still inspected; `lake new` writes none, and `doctor` names each module a library leaves
out:

- `lakefile.lean`: ``globs := #[.andSubmodules `Widget]``
- `lakefile.toml`: `globs = ["Widget", "Widget.+"]` (`"Widget.+"` alone omits `Widget` itself)

`foundation_manifest.json` classifies every root `lean_lib` and `lean_exe`, claimed or excluded
with a rationale. Review the starter: strengthen each `claim` where the library allows, write
the real rationale, and exclude what you do not claim.

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

`execution` states what you claim about compiled code
([standard §7.6](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#76-classify-lean-computation-mechanisms-exactly)):

| Mode | Meaning |
| --- | --- |
| `report` (default) | Every execution boundary reached from an owned executable root is reported with its kind and correspondence state; trusted boundaries are recorded, not failed. |
| `checked` | Additionally fails on any trusted boundary other than the toolchain's own native-runtime primitives. |

In both modes an unresolved path blocks the execution claim. Native arithmetic and the Lean
runtime remain trusted in every mode; the checker verifies Lean source, not the compiler or the
machine.

## 4. Run `lake lint`

From the project root:

```sh
lake lint                                  # incremental elaboration + current policy
lake lint -- --fresh                       # isolated copy built from empty output
lake lint -- --json-out tmp/regula.json    # also write the JSON report
lake lint -- --explain-config              # read-only: manifest, scope, profiles, stages
```

The driver builds every manifested library and executable by its explicit Lake target, with
warnings as failures, and inspects the completed environment; it re-evaluates current policy
even when every module is cached. Run it from the project root without `-d`: it refuses a working
directory that is not the workspace that dispatched it. Its exit status separates the outcome:

| Exit | Outcome |
| --- | --- |
| 0 | `ACCEPTED`: the audit constructed its accepted result for the selected mode. |
| 1 | `VIOLATION`: completed policy rejections, for example RG1001–RG1007 or RG3002. |
| 2 | `INVALID CONFIGURATION`: only RG2002 manifest/scope rejections, an invalid driver argument, a working directory that is not the dispatching workspace, or `--help`/`--explain-config`, which run no audit. |
| 3 | `INCOMPLETE`: an incomplete finding, for example RG2001, RG2003, RG2005 or RG3001, a failed audit-worker build, a working directory outside any Lean project or whose workspace fails to load, or an error that escaped the audit. It takes precedence over violations reported in the same run. |

The success line names its coverage: an incremental run is "incremental project acceptance over
existing build state, not a fresh-source audit"; only `--fresh` is fresh whole-project
acceptance.

**A first run usually stops at build warnings.** Rules are inspected only after a build without
warnings (RG2003), so a warning, such as a missing docstring, makes the run `INCOMPLETE` (exit 3)
with the compiler's message before any foundation rule is checked. The same holds for your first
`sorry`: Lean warns `declaration uses 'sorry'`, so it is reported as RG2003, not RG1002; silencing
the warning does not help, because the hole is then reported as RG1002.

For CI, provision the toolchain and dependencies, then run the driver as its own step so its
exit status fails the job; use `--fresh` where the claim is fresh-source conformance, since
incremental evidence trusts Lake's build cache:

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
  project coverage. `lake exe docFenceAudit` checks Lean examples you keep in Markdown under
  `docs/` with the [fence protocol](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#77-check-lean-documentation-verbatim).

## Update Regula

To move to a new release, change the tag and your `lean-toolchain` together, then:

```sh
lake update regula
lake exe regula init
lake lint
```

`lake update regula` updates only `regula`. Running `init` again rewrites a skill file that
differs from the new release's briefing and adds any option the new release requires; it changes
nothing else. A project that also uses Mathlib moves Mathlib to the same Lean release the usual
way. Each finding's rule link then targets the new release's pages.

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

## Machine-readable report

`lake lint -- --json-out PATH` writes one JSON document, result schema 3, whatever the outcome;
the path is first written as an incomplete result, so a stale report is never mistaken for this
run's. Its main members:

| Member | Meaning |
| --- | --- |
| `schemaVersion` | `3`. Also `producerVersion`, `toolchain` and `sourceRevision` of the Regula build. |
| `status` | `completed` (accepted), `rejected` (a violation was established), `incomplete` (evidence was missing) or `classified` (a file inspection with no conforming claim). |
| `stages`, `stagesCompleted`, `stagesNotRun`, `complete` | The run's required stages and which completed. `complete` is `false` when the run stopped early, so fixing the reported findings can reveal more. |
| `diagnostics` | Every finding in printed order, with `id`, `impact`, `severity`, `mode`, `claim`, `location` (for source, byte and LSP ranges), `arguments`, `text`, `remedy` and `helpUrl`. |
| `rules` | Once per fired rule: `requirement`, `rationale`, `remedy`, `rewrites`, `compliantExample`, `correction`, `helpUrl` and the offline `explain` command. |

The exit status is the stable pass/fail contract; `status` and `complete` say why. Treat the
report as observations, never as a Lean proof: its consistency checks catch writer regressions,
not a report edited by hand.

## Receive diagnostics while editing

Import `Regula.Linter` from a module your project already imports widely (the
[TOML example](../../examples/lake-lint-toml/) imports it in `Gadget/Double.lean`). The
supported editor is VS Code with the Lean 4 extension. Completed commands and modules then show
warnings with codes `Regula.RG1001`–`RG1007`, `RG2002` and `RG2005` at the declaration, plus
`RG5001`–`RG5003` once the module elaborates without errors, each with its fix, rule link and
offline `explain` command; the infoview adds a **View explanation** link. `RG2005` means a
finding needs evidence only `lake lint` collects.

Execution closure (RG3001/RG3002), coverage (RG2004), build and warning checks (RG2003) and fresh
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
  (into each claimed target's own configuration instead when the manifest excludes a root target):

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
  first and that no import repeats, which RG5001 checks instead (standard §5.3 and §6.4). In
  `lakefile.lean` the same options are
  ``leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`weak.linter.style.header, false⟩, ⟨`weak.linter.hashCommand, false⟩, ⟨`weak.linter.style.longFile, .ofNat 0⟩]``.
  The linters report through build warnings, so `lake lint` reports each as RG2003 (`INCOMPLETE`,
  exit 3). RG2006 checks every option above in Lake's resolved configuration of each claimed
  target, and rejects a target-wide `false` for any other linter and any `-D` in `moreLeanArgs`
  or `weakLeanArgs` that overrides them (`VIOLATION`, exit 1); it does not read `set_option` in
  source, which review checks. Where the community's guidance accepts an exception, disable that
  linter for the one declaration (`set_option linter.style.longLine false in`) with a comment
  giving the reason. Never disable Lean's default warnings, such as `linter.unusedVariables` or
  `warn.sorry`.
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

## Limits

- `lake lint` exits 0 only for an accepted run: `Regula.Checker.Lint.accepted_sound` and
  `RegulaPolicy.accept_iff` prove the success direction. Which rule a failure receives is proved
  only where a rule page's *Proved linkage* says so.
- Some adapters are operational code, not proved: RG2001/RG2002 routing of escaped errors by
  message prefix, RG1007 contract extraction, RG2004 inventory checks, the documentation fence
  scanner and the RG5001 header observation. `init`'s lakefile edits are text edits confirmed by
  reading the project again, not proved to realize the model.
- The command-line transcript names a finding's file and declaration; exact source ranges are in
  `--json-out` and the editor.
- The only supported editor is VS Code with the Lean 4 extension, and there is no latency claim.
- Regula has run on small adopters only, including a Mathlib-importing library accepted
  incrementally and fresh; there is no Mathlib-scale adopter claim. These are bounded
  observations, not theorems about the tools.
- Each release supports exactly one Lean release. The nine
  [residual review obligations](architecture.md#coverage-of-the-standard) stay open; every
  accepted account lists them.

## What you are not asked to do

- **Checker qualification is not adopter conformance.** The `MUT-*` rows and the
  `checkerSelftest` suite qualify a checker implementation. An adopter using the shipped
  checker unchanged does not rerun them.
- **`freshChecker`** (fresh `leanchecker` over the serialized module graph) is optional
  defense in depth for the separate `MUT-05` claim, not part of the ordinary loop.
