# Adopt the standard

To adopt the [standard](https://rbeauchamp.github.io/regula/dev/standard/), identify the correctness claims your
project presents as established, express them precisely in types or propositions, and
supply kernel-checked evidence. Review whether those statements capture the intended
claims, including their assumptions and execution boundaries. Conformance requires every
applicable row of the [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/); the
checker supports that review by checking the mechanical requirements.

The steps below cover checker setup and the semantic review needed for a conformance
claim. Use the [supported toolchain](../../README.md#supported-toolchain).

This is the ordinary path from an existing Lean project to a conformance claim. It uses
your project's own layout, module names, and lakefile format; nothing named `Audit`,
`Fixtures`, or `tmp` from this repository is required. The normative definitions behind
each step are in [standard §8.11](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#811-adopting-the-checker-in-another-project).

## 0. Brief your agent

Regula is designed first for agents. Adopting it tells your agent that your Lean code and
proofs must meet a strict standard that may not be in its training data. Each mechanically
checked rule is one typed registry definition stating what it requires, why it matters, how
to comply (with the common compliant rewrites) and a checked compliant and noncompliant
example pair. The checker's findings, the offline rule reference and agent briefing below,
the machine-readable report and the rule-reference website are all generated from that
definition, so an agent can apply a rule before writing code and act on a finding without
consulting another source. Where a rule's checked files are qualification inputs rather than
project files (RG1003's stand-in dependency and RG2001's runner requests), agent-facing output
states the correction instead of showing them. Once the package is required (step 1), give
the agent the standard before it writes Lean:

```sh
lake exe regula agent-guide      # compact briefing of every rule, ordered for writing code
lake exe regula skill            # the same briefing as an Agent Skills SKILL.md
lake exe regula explain RG1001   # one rule in full: requirement, rationale, remedy, examples
lake exe regula rules            # the index of every rule
```

Each command prints Markdown generated from the installed package's rule registry, so it
needs no network and matches the pinned revision. It exits 0, or 2 for an invalid invocation
or an unknown rule ID. The briefing has a 15 KiB budget (`Regula.Guidance.agentGuideBudget`),
checked when the package builds.

Then either install the skill, for example
`lake exe regula skill > .agents/skills/regula/SKILL.md` (or your agent's own skills
directory, such as `.claude/skills/regula/SKILL.md`), regenerating it when you move the pin;
or paste the briefing into `AGENTS.md`; or add this snippet, which keeps `AGENTS.md` short and
always matches the installed version:

```markdown
## Lean standard: Regula

This project's Lean code and proofs must meet the Regula strict standard, which may not be in
your training data. Before writing or changing Lean, run `lake exe regula agent-guide` and
follow it. `lake lint` enforces the rules and exits 0 accepted, 1 violation, 2 invalid
configuration, 3 incomplete. Each finding states what is wrong, where, and the fix; for any
rule ID, `lake exe regula explain <ID>` prints the full rule offline. For machine-readable
findings run `lake lint -- --json-out tmp/regula.json`. Never disable a Lean warning, weaken a
statement or remove a registration to make a check pass; disable a community linter only for
one declaration, where its guidance allows, with the reason.
```

This repository dogfoods the skill in
[`.agents/skills/regula/SKILL.md`](../../.agents/skills/regula/SKILL.md); its acceptance
check fails when the committed file differs from the generated briefing.

## 1. Require the checker package

The repository and the Lake package are both named `regula`, and imports use `Regula.*`.
Use the repository URL below with those package and module identifiers.

Pin the package to an exact revision. A git dependency and a local path resolve through the
same Lake workspace discovery; use whichever your project already uses for dependencies.

`lakefile.lean`:

```text
require «regula» from git
  "https://github.com/rbeauchamp/regula" @ "<exact commit>"
```

`lakefile.toml`:

```toml
[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "<exact commit>"
```

Requiring `regula` adds exactly one package to your `lake-manifest.json`: `regula` itself.
The package requires nothing beyond the Lean toolchain (no Mathlib, no Batteries), and its
modules import only Lean's core libraries, so it never pins a package your project also uses.
Lake keeps one copy of each package per workspace; with Regula in it, a project keeps
whatever Mathlib revision it pins, and a project without Mathlib gets none. To move to a newer
Regula, change the revision above and run `lake update regula`, which updates only `regula`.
Only the checker repository's own Mathlib-dependent package (`audit/`, the standard's Mathlib
examples) requires Mathlib, and it is not part of the `regula` package.

Use the Lean release of the checker's [`lean-toolchain`](../../lean-toolchain) at that revision
for your own `lean-toolchain`. Lake builds every package of a workspace with one
toolchain, as with any Lean dependency, and the checker is qualified only on its pinned
release (see the [supported toolchain](../../README.md#supported-toolchain)).

## 2. Declare the claimed surface

Conformance is claimed per Lake library or executable, and the checker discovers modules
through Lake's elaborated inventory, not through your umbrella import or a file list
([standard §8.2](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#82-define-surfaces-through-lake-semantics)).
Give every claimed library a glob that covers its intended modules:

- `lakefile.lean`: ``globs := #[.andSubmodules `Widget]``
- `lakefile.toml`: `globs = ["Widget", "Widget.+"]` (`"Widget.+"` alone omits `Widget`
  itself)

A module inside the glob that your umbrella does not import is still part of the surface
and is still inspected. A `lakefile.toml` also needs `defaultTargets` for a bare
`lake build` to build anything; the gate builds the claimed surface explicitly either way.
For a runnable Core-only project using the enforcing ordinary-build integration, see
[`examples/build-lint/`](../../examples/build-lint/).

## 3. Choose foundation profiles and execution mode

Write `foundation_manifest.json` at your project root classifying every root-package
`lean_lib` and `lean_exe`. Empty exclusion arrays are valid when nothing is excluded:

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

Every declaration is labeled from its own exact axiom set and must fit the claim. Label
from the report, not from the kind of surface. For example, `def main : IO Unit := pure ()`
depends on no axiom. Neither an `IO` type nor recursion alone determines a declaration's
foundation profile; inspect its actual transitive dependencies. Compiler-trusting axioms
(for example from `native_decide`) never fit any profile and are reported separately.

`execution` states what you claim about compiled code
([standard §8.6](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#86-classify-lean-computation-mechanisms-exactly)):

| Mode | Meaning |
| --- | --- |
| `report` (default) | Every execution boundary reached from an owned executable root is reported with its kind and correspondence state; trusted boundaries are recorded, not failed. |
| `checked` | Additionally fails on any trusted boundary other than the toolchain's own native-runtime primitives. |

In both modes an unresolved path blocks the execution claim. Native arithmetic and the
Lean runtime remain trusted in every mode; the checker verifies Lean source, not the
compiler or the machine.

## 4. Run the ordinary conformance check

From your project root, or with `--project DIR`:

```sh
lake exe axiomGate --json-out tmp/axiom-report.json
```

The gate copies your project into an isolated temporary directory under your
`tmp/.regula-scratch/`, which Regula owns,
shares your pinned dependency checkouts, builds the claimed surface from empty output with
warnings as errors, inspects the elaborated environment, and removes the copy. The JSON
report holds every owned declaration with its exact transitive axiom set and every
execution root with its boundaries. The verdict is the printed transcript and the exit
status: each declaration failure is printed with its reason and that declaration's label,
the run ends with `axiom gate: PASS` (exit 0) or `FAIL: N violation(s)` (exit 1), and
`--verbose` prints every declaration's label. A PASS names what it covers (only a fresh
run is whole-project acceptance) and is preceded by its account: the relation Lean checked,
each registered `ExecutableContract` with its implementation and requirement, execution
counts, the trusted mechanisms, and the semantic-review obligations (`R-INTENT` and so on)
that remain open. A PASS is mechanical; it does not complete that review.

Two narrower commands are useful before a full run:

```sh
lake exe axiomGate --file F.lean --claim standard-logical   # audit one file under this profile
lake exe docFenceAudit --jobs 4                            # elaborate every docs/ Lean fence
```

`docFenceAudit` applies when your project keeps Lean teaching examples in Markdown under
`docs/` using the [Markdown fence protocol](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#87-check-lean-documentation-verbatim)
(`<!-- lean-fail: PATTERN -->` and `<!-- lean-trusted-compiler -->` markers).

## 5. Read a failure

Every finding is printed with everything needed to fix it. A project or file audit prints its
findings in a deterministic order (project and configuration findings, then module findings,
then source findings by file and position); a documentation audit prints each fence's findings
with that fence, in fence order:

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

The first line states what is wrong and where (`FILE:LINE:COLUMN` in Lean's own coordinates).
The first finding of each rule in a run adds the rule's requirement, rationale, common
rewrites and checked compliant example (or, for a rule whose checked files are qualification
inputs, the correction they demonstrate); later findings of that rule keep their own message and
fix and point back to it, so a run with hundreds of findings prints each rule's guidance once.
The rule page is a pointer for humans, never the only source of the fix.

Each failing declaration or root carries one reason. The reason names the Lean fact, not a
style preference:

| Reason | Meaning | Where the rule lives |
| --- | --- | --- |
| `project-axiom` | An owned `axiom` declaration outside Lean's foundation. Make the assumption a binder or proof-bearing field. | [standard §3.4](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#34-foundation-strength-axioms-are-reported-never-assumed) |
| `hole` | The declaration depends on `sorryAx` (`sorry`, `admit`, or an unfinished tactic). | [standard §3.4](https://rbeauchamp.github.io/regula/dev/standard/3-logic-proof-patterns/#34-foundation-strength-axioms-are-reported-never-assumed) |
| `unknown-axiom` | A transitive axiom outside `propext`, `Quot.sound`, `Classical.choice` other than `sorryAx` and the compiler-trusting axioms, which have their own reasons. | [standard §4.5](https://rbeauchamp.github.io/regula/dev/standard/4-mathematical-foundations/#45-foundation-strength-kernel-only-choice-free-standard-logical) |
| `label-exceeds-claim` | The declaration's exact label is stronger than the surface's `claim`. Prove the same statement using fewer axioms, or explicitly revise the permitted foundation profile and its rationale. | [standard §4.5](https://rbeauchamp.github.io/regula/dev/standard/4-mathematical-foundations/#45-foundation-strength-kernel-only-choice-free-standard-logical) |
| `compiler-trusting` | A native-evaluation proof axiom (for example `native_decide`) on a positive surface. | [standard §8.5](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#85-proof-completeness-and-foundation-strength) |
| `escape-hatch` | An authored `partial` or `unsafe` declaration on a positive surface. | [standard §8.6](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#86-classify-lean-computation-mechanisms-exactly) |
| `executable-contract` | An `ExecutableContract` registration is not closed, does not name a complete implementation constant, or names an ineligible implementation: missing, noncomputable, unsafe, partial, proposition-valued, type-producing, or not an executable definition. The Lean type checker separately checks the supplied proof against the registered predicate. | [standard §8.12](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#812-opt-in-enforcing-build-linter) |
| `execution-unresolved` | A compiled path whose replacement, `extern`, or unsafe target cannot be classified. Blocks the execution claim in every mode. | [standard §8.6](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#86-classify-lean-computation-mechanisms-exactly) |
| `execution-trusted-boundary` | A runtime replacement or `extern` boundary without kernel-checked correspondence on a surface claiming `checked` execution. | [standard §8.6](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#86-classify-lean-computation-mechanisms-exactly) |

Surface-level failures name the Lake fact. `build-failed` means the claimed surface did not
elaborate warning-free from empty output (a zero exit with a warning still fails);
`manifest-incomplete` means a root library or executable is neither claimed nor excluded,
an excluded name is not a root target, or a required name or rationale is missing or
malformed; a claimed surface library or executable that Lake does not discover fails
earlier with `manifest surface missing from Lake discovery` or `manifest executable missing
from Lake discovery`; `manifest-schema` means a manifest key, value, or schema version is invalid; `unexpected-project-module` means a claimed library imports an
excluded module or owns a module outside every manifested library.

## 6. Enforce with `lake lint`, `lake build` and CI

Configure the Regula lint driver in your package. Both lakefile formats are qualified:

- `lakefile.lean`: `package «my_project» where lintDriver := "regula/lint"`
- `lakefile.toml`: `lintDriver = "regula/lint"` at the top level

Then, from the project root:

```sh
lake lint                                  # incremental elaboration + current policy
lake lint -- --fresh                       # isolated copy built from empty output
lake lint -- --json-out tmp/regula.json     # also write the schema-3 JSON report
lake lint -- --explain-config              # read-only: manifest, scope, profiles, stages
```

The driver builds every manifested library and executable by its explicit Lake target and
inspects the completed environment. It re-evaluates current policy even when every module
is cached, and it never invokes your default target. It runs the same audit body as
`axiomGate`; it adds no second policy. Lake's lint dispatch builds only the driver, so the
driver first builds the `regula/axiomGate` executable that the audit runs as its worker, in
the workspace where you ran `lake lint` (never the `--project` directory). That workspace
built the driver itself, whether Regula is a git dependency under `.lake/packages`, a path
dependency or a custom `packagesDir`, so the worker uses the same dependencies and toolchain
and needs no second dependency download. If that build fails, the run is `INCOMPLETE`.
Run `lake lint` from the project root, without `-d`/`--dir`: Lake does not change the
driver's working directory, so the driver refuses with exit 2 when the workspace there is
positively identified as not the one that dispatched it, and stops with exit 3 when the
working directory is outside any Lean project or its workspace fails to load. Lake v4.34.0
passes the dispatching workspace's package library directories, then its own
`LEAN_SYSROOT/lib/lean`, then any inherited `LEAN_PATH`, as the driver's `LEAN_PATH`; the
driver requires the working-directory workspace's library directories and that directory to
begin it (`Regula.Checker.Lint.dispatchedFrom_iff`). A driver started outside Lake, or by a
Lake not collocated with the toolchain, is refused.
Its exit status separates the outcome:

| Exit | Outcome |
| --- | --- |
| 0 | `ACCEPTED`: the audit constructed its accepted result for the selected mode. |
| 1 | `VIOLATION`: completed policy rejections, for example RG1001–RG1007 or RG3002. |
| 2 | `INVALID CONFIGURATION`: only RG2002 manifest/scope rejections, an invalid driver argument, a working directory that is not the dispatching workspace, or `--help`/`--explain-config`, which run no audit. |
| 3 | `INCOMPLETE`: an incomplete finding, for example RG2001, RG2003, RG2005 or RG3001, a failed audit-worker build, a working directory outside any Lean project or whose workspace fails to load, or an error that escaped the audit. It takes precedence over violations reported in the same run. |

Exit 0 requires a zero audit exit and the audit's recorded `completed` status, which carries
the accepted account of the requested mode (`Regula.Checker.Lint.accepted_sound`: an accepted
run complete for its plan that meets every stage policy); any disagreement is `INCOMPLETE`.
The success line is the account's `regula lint: PASS — …` text, and it names the coverage: an
incremental run reads "incremental project acceptance over existing build state, not a
fresh-source audit"; only `--fresh` reads as fresh whole-project acceptance.
`lake lint` builds the claimed targets with Regula's audit-build marker
(`weak.regula.auditBuild`), which turns the local linter off whatever your sources set
`linter.regula` to, `set_option linter.regula true` included, so a live Regula finding is not a
build warning there: the audit's own policy stages report it, as a `VIOLATION`. Any other
warning or build failure stops the audit before policy inspection and is `INCOMPLETE`, with
the original compiler message printed as evidence. That includes Lean's default
`declaration uses 'sorry'` warning: an owned `sorry` is reported as RG2003, not RG1002 (with
`set_option warn.sorry false` it reaches the RG1002 stage instead). The marker is part of
Lake's module trace, and Lake scopes it to the whole package rather than to the modules that
import `Regula.Linter` (elsewhere it changes nothing; no source command can name or change
it), so modules last built with ordinary options (for example by `lake build` or the editor)
are rebuilt for the audit, and their replayed logs never enter its warning check.
`axiomGate` and the build-lint `policy` target keep ordinary options, so there a live finding
stops the build check as `INCOMPLETE`. `--json-out` carries the same status and diagnostics
for machines. `--help` and `--explain-config` run no audit, establish nothing and exit 2, so
putting either in `lintDriverArgs` cannot make `lake lint` succeed; neither accepts
`--json-out` or `--verbose`.

### Machine-readable report

`lake lint -- --json-out PATH` (and `axiomGate --json-out PATH`) writes one JSON document,
result schema 3, whatever the outcome. The path is written before the audit starts, as an
incomplete result, so a stale report is never mistaken for this run's. Its top-level members
include:

| Member | Meaning |
| --- | --- |
| `schemaVersion` | `3`. Also `producerVersion`, `toolchain` and `sourceRevision` of the Regula build. |
| `status` | `completed` (accepted), `rejected` (a violation was established), `incomplete` (evidence was missing) or `classified` (a file inspection with no conforming claim). |
| `stages` | The run's required stages, in run order: those its mode requires, plus the documentation stages of a `--with-docs` run. |
| `stagesCompleted` | The required stages that completed. A stage a finding stops (an incomplete finding, or an RG2002 or RG2003 refusal) is never among them, nor is any later stage. In a `--with-docs` run, a finding from the project stages leaves the documentation stages out, because they start only after the project stages pass. |
| `complete` | `true` exactly when every stage of the run completed. `false` when the run stopped early (for example at an RG2002 configuration refusal or a failed build) or an incomplete finding left a stage unfinished (for example an unelaborated module, RG2004): fixing the reported findings can then reveal more. An incomplete RG3001 does not, because its stage completed. |
| `stagesNotRun` | The required stages missing from `stagesCompleted`, in run order (for example `build`, `admission`, `declarationPolicy`); empty exactly when `complete` is `true`. |
| `diagnostics` | Every finding; for a project or file audit, in the printed run order. Each has `id` (rule ID), `impact` (`violation` or `incomplete`), `severity`, `mode`, `claim`, `location` (for source: `uri`, byte `range` and `selectionRange`, and zero-based LSP `lspRange` and `lspSelectionRange`; otherwise a module or project scope), `related` locations, `arguments` (subject and detail), `text` (the printed finding without the once-per-run guidance), `remedy` and `helpUrl`. |
| `rules` | Once per rule that fired, in registry order: `id`, `title`, `requirement`, `rationale`, `remedy`, `rewrites`, `compliantExample` (`path`, `language`, `text`; `null` where the checked files are qualification inputs), `correction`, `helpUrl` and `explain` (the offline command). |
| `unresolved` | Unresolved evidence, when the run is incomplete. |

The exit status is the stable contract for pass or fail (table above); the `status` and
`complete` members say why. Regula checks the report form the way it checks registry exports:
every diagnostic must decode to the canonical indexed finding (unknown fields, stale text or
remedies are refused), a result with a `mode` must record its `request` (with no configuration
when the configuration could not be read), `stages` must be the required stages of that `mode`
and `request`,
`stagesCompleted`, `complete`, `stagesNotRun` and `rules` must equal their derivation from the
status, `stages`, `stagesCompleted` and the diagnostics by the same function the writer uses
(so a `completed` result lists every stage as completed and no stopped stage is listed), and an
`incomplete` result without an incomplete finding must list a stage not run
(`Regula.Checker.ResultProtocol.admitGuidance`). These checks catch writer regressions and
omissions, not forgeries: a report edited by hand to be self-consistent, for example with its
`request.kind` rewritten, passes them. Treat the report as observations, never as a Lean proof.

Lake details that affect what ran:

- Arguments for the driver follow `--`; Lake prepends `lintDriverArgs`. Positional module
  arguments before `--` affect only Lake's builtin linters.
- `lake lint --builtin-only` skips the driver and is **not** Regula enforcement: it
  exits 0 with a Regula violation present. `lake lint --builtin-lint` runs builtin
  linters and then the driver; a failing driver determines the exit code. Builtin linting
  needs module arguments (for example `lake lint --builtin-lint Widget`) when the default
  target is not a library, such as the `policy` target below. `lake check-lint` only reports whether a lint command is configured.
- Lake has one `lintDriver` per package. A project that already uses another driver (for
  example Mathlib's `runLinter`) keeps it and runs `lake exe lint` as a separate
  command, or a composing script that succeeds only when both drivers succeed. Do not
  overwrite the other driver silently or call `lake lint` from within a driver.

`lake exe lint` runs the same driver without Lake's lint dispatch. The
`axiomGate --file` single-file audit remains a `freshFile` result, never project coverage.

A `lakefile.lean` project can also enforce during plain `lake build` with the
[build-lint example](../../examples/build-lint/)'s sole-default `policy` target; see
[standard §8.12](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#812-opt-in-enforcing-build-linter)
for its scope and cache semantics. `lakefile.toml` has no custom targets, so TOML projects
use `lake lint`. Direct `lean`, editor elaboration, an explicit build of another target and
`--builtin-only` do not run the strict gate and are never reported as enforced.

For CI, provision the pinned toolchain and dependencies, then run the driver as its own
step so its exit status fails the job:

```yaml
- name: Regula
  run: lake lint -- --json-out tmp/regula.json
```

Use `lake lint -- --fresh` where the CI claim is fresh-source conformance. Incremental
evidence trusts Lake's build cache. Upload `tmp/regula.json` if another step consumes
the machine result. Its `status` is `completed` only when the accepted result was
constructed.

### Community conventions and linters

Regula's rules are Lean correctness rules.
[Standard §6.7](https://rbeauchamp.github.io/regula/dev/standard/6-code-organization/#67-community-conventions-and-linters)
also requires the Lean community's baseline for style, naming and documentation form, as the
community's own linters enforce it. The conventions are Mathlib's [style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html) and
[documentation](https://leanprover-community.github.io/contribute/doc.html) guides for code that
depends on Mathlib, and Lean's
[standard library style guide](https://github.com/leanprover/lean4/blob/master/doc/std/style.md)
and [naming conventions](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md) for
core-only code.

- **Required options.** Every claimed library and executable enables Lean's `linter.missingDocs`, which
  reports every public definition without a docstring, and, in a project that depends on
  Mathlib, the syntax linters Mathlib builds with, except the three that enforce policies of
  the Mathlib repository itself. It also turns off automatic implicits
  ([standard §8.1](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#81-declare-the-elaboration-environment)):

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

  Omit the last four lines in a project without Mathlib. The three excluded linters enforce
  Mathlib's contribution header (copyright, Apache 2.0 license and authors), its ban on
  `#` commands such as a passing `#guard`, and its file-length limit; standard §6.7 gives the
  reasons. Turning off the header linter also turns off its checks that the module docstring is
  the first command after the imports and that no import is repeated. Both remain requirements
  (standard §5.3 and §6.4), and RG5001 checks both on every claimed module.
  `lake new NAME math` already writes `weak.linter.mathlibStandardSet` and
  `relaxedAutoImplicit`; add the rest. In `lakefile.lean` the same options are
  ``leanOptions := #[⟨`linter.missingDocs, true⟩, ⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`weak.linter.mathlibStandardSet, true⟩, ⟨`weak.linter.style.header, false⟩, ⟨`weak.linter.hashCommand, false⟩, ⟨`weak.linter.style.longFile, .ofNat 0⟩]``.
  The linters report through build warnings, so `lake lint` reports each finding as RG2003
  (`INCOMPLETE`, exit 3) with the linter's message. RG2006 checks, in Lake's resolved configuration
  of every claimed library and executable, every option above, and rejects a target-wide
  `false` for any other linter and any
  `-D name=value` in `moreLeanArgs` or `weakLeanArgs` that gives one of these options another
  value or turns such a linter off (set options in `leanOptions`, where it reads them); a
  violation is `VIOLATION`, exit 1. Other extra `lean` arguments are allowed. It does not read
  `set_option` in source, which review checks. Where the community's guidance accepts an
  exception, such as a long URL, disable that linter for the one declaration
  (`set_option linter.style.longLine false in`) with a comment giving the reason. The same
  holds for every community linter, including those Mathlib turns on for every importer, such
  as `linter.unusedTactic`. Never disable Lean's default warnings, such as
  `linter.unusedVariables` or `warn.sorry`. Regula sees only emitted warnings of a source-level
  disable, so it cannot tell these cases apart; review checks every such disable.
- **Batteries' environment linters** (`docBlame`, `simpNF`, `unusedArguments` and others) are
  recommended. They report through their own command, not build warnings. Run `lake build`
  first: `runLinter` reads the built modules and does not rebuild them. Lake has one
  `lintDriver` per package, so keep one driver and run the other as its own command:

  ```sh
  # lintDriver = "regula/lint"
  lake lint && lake build && lake exe runLinter
  # lintDriver = "batteries/runLinter"
  lake build && lake lint && lake exe lint
  ```

  Each command's exit status covers only its own checks, so CI requires both.

A community linter's pass establishes only what that linter checks. It discharges no other
Regula requirement, and a Regula pass says nothing about style that no enabled linter checks.
The configuration above was exercised on a Mathlib adopter in the `lake new` layout, and the
Batteries routes on an earlier small adopter
([product qualification](product-qualification.md#community-linters-beside-regula)).

## 7. Receive diagnostics while editing

Import `Regula.Linter` from a module your project already imports widely. The
[TOML example](../../examples/lake-lint-toml/) imports it in `Gadget/Double.lean`. The
supported editor is VS Code with the Lean 4 extension on the
[supported toolchain](../../README.md#supported-toolchain). While you edit, completed
commands and modules show:

- Warnings with codes `Regula.RG1001`–`RG1007`, `RG2002` and `RG2005`, at the actual declaration
  range, plus `RG5001`–`RG5003` when the module finishes elaborating without errors (with errors,
  `RG2005`).
- Message text that states the finding and its fix, then the same rule page URL and the
  offline `lake exe regula explain <ID>` command. Each editor message stands alone (the
  once-per-run guidance applies to command-line runs). In the infoview, Lean's own error-code
  widget adds a **View explanation** link to the rule page.
- `RG2005` when a finding needs fresh evidence that only the project command collects.
  The message says to run `lake lint`.

Execution closure (RG3001/RG3002), coverage (RG2004), build and warning checks (RG2003),
fresh admission and complete result assembly run only in `lake lint`, `lake build` with the
policy target, or `axiomGate`. A clean editor buffer means no current local findings, not a
project result. `set_option linter.regula false` and `regula.localFoundation`
change only local feedback. `lake lint` still rejects the same declaration.

Local findings are ordinary compiler warnings in the editor and in a plain `lake build`.
`lake lint` turns the linter off for its own build and reports the same rules itself, so
it exits `VIOLATION` (1), not `INCOMPLETE`, while one remains. Lean's own warnings are
unaffected: by default a `sorry` also makes Lean warn `declaration uses 'sorry'`, so under
`lake lint` an owned hole stops the audit at its warning-free build check (RG2003, `INCOMPLETE`, exit 3) before
the RG1002 stage; the editor shows both messages.
Rule links point to the development route
`https://rbeauchamp.github.io/regula/dev/rules/<ID>/` of the [rule reference](#rule-reference-website),
which describes the latest deployed revision of `main`.

## 8. Complete semantic review

A green gate establishes hole-freedom, exact axiom sets, module coverage, and boundary
classification. The current checker does not establish that your theorems say what your prose says, that your
required contracts are complete, or that your types encode the invariant you advertise.
Those are the semantic-review rows of [standard module 9](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/), including
`SCOPE-*`, `TYPE-*`, `THEOREM-*`, `COMP-01`, `COMP-04`, `DOC-01`, and `DOC-02`.
Conformance is the whole matrix with one terminal result (`PASS`, `FAIL`, or `INCOMPLETE`),
not the gate alone.

## What you are not asked to do

- **Checker qualification is not adopter conformance.** The `MUT-*` rows and the
  `checkerSelftest` suite qualify a checker implementation. An adopter using the shipped
  checker unchanged does not rerun them.
- **`DOGFOOD-*` rows apply only to this repository.**
- **`freshChecker`** (fresh `leanchecker` over the serialized module graph) is optional
  defense in depth for the separate `MUT-05` claim, not part of the ordinary loop.

## Rule reference website

Every diagnostic's help URL opens its page in the [rule reference](https://rbeauchamp.github.io/regula/dev/rules/),
a human view of the same registry that `lake exe regula explain` prints offline:
what triggers the rule, why it matters, how to fix it, a checked violating and corrected
example produced by the real checker, the exact configuration and exception boundaries, and
what a passing result does and does not establish. The site is generated from the
[registry](rule-registry.md) and the checked [rule examples](rule-examples.md) and published
from `main` by CI; see the [website guide](website.md) for its guarantees and version routes.
Canonical metadata and accepted-result design credit con-leche as detailed in the architecture.

## Accepted results and modes

Audit success is finalized against the exact requested claim and independently frozen
inventory. Project, explicit conforming-file and documentation drivers retain a
proof-bearing `AcceptedRun`; combined project/docs also checks the shared snapshot.
`--json-out` renders acceptance metadata from that value. Treat it as a report of
observations, never as a deserializable Lean proof or an authenticated external attestation.
See the [API and success-owner map](policy-acceptance.md).

`--build-lint`/`--incremental` still mean current policy inspection over an incremental
build. A fresh file claim covers the original file's bytes and its isolated compilation,
with incrementally built dependencies. No-profile and compiler-trusting file requests
report `CLASSIFIED`, not conforming success. Documentation accepts each configured
positive, rejection or teaching expectation without promoting negatives/teaching to
positive conformance. Help, worker and optional graph planning exits have no audit certificate.
In this repository, acceptance is `./scripts/verify.sh` (with cold root builds) and then
`./scripts/verify.sh docs`, each under its own hard 420-second deadline; external-adopter and
build-integration diagnostics and serialized-graph checking remain separate.

This boundary is informed by con-leche's complete indexed result assembly, without
importing its code or asserting its kernel/model guarantees for Lean/Lake, the filesystem,
JSON parsing, process completion or compiled machine code. Semantic adequacy and the
standard's residual review accounts remain separate obligations.
