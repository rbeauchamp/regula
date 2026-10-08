# Regula for Lean

A strict linter for Lean: no holes, no hidden axioms, no unstated trust, and a fix for every finding.

*Public review draft; not affiliated with the Lean FRO or Mathlib.*

`lake build` can succeed while a theorem still rests on a `sorry` behind an import, a helper
`axiom` or a `native_decide`, and while the code that actually runs is an `implemented_by`
replacement your proofs never mention. `#print axioms` shows this one declaration at a time.
Regula checks every declaration of the libraries you claim, on every run of `lake lint`:

- It rejects proof holes, project axioms, compiler-trusting proofs and any axiom outside the
  foundation you chose, found transitively, so "proved" means proved from Lean's kernel, your
  stated hypotheses and that foundation.
- It names every `extern` and `implemented_by` boundary your executables reach and refuses a
  path it cannot resolve; in `checked` mode it also rejects any boundary of your project or its
  dependencies whose correspondence you haven't proved, while the Lean toolchain's own are
  listed once as its trusted base. Code a program loads or evaluates by name at runtime is
  outside that account.

Every finding states what is wrong, where and how to fix it, in the terminal, the editor and
versioned JSON, and `lake lint` adds, once per fired rule, why it matters and a checked
example of the fix (or, where the checked files are qualification inputs, the correction they
demonstrate). The same guidance is a briefing for the coding agents that increasingly
write Lean, installed with the package and read before they write a line. A pass is
mechanical: whether each theorem states what you meant is still your review, and Regula says
so.

**Use it when** Lean code you rely on is written or changed by someone you don't review line by
line (a coding agent, a new contributor, you in six months), or when you publish results as
proved and want others to see exactly what they rest on.
**Don't use it** as a Mathlib PR check (Mathlib's CI is the authority), to judge an untrusted
proof against a fixed statement (comparator does that), or while exploring a proof. It
complements [comparator](https://github.com/leanprover/comparator): comparator checks
a proof against the statement its challenge fixes, and Regula gates the whole project. In the
terms of [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/),
Regula runs the `#print axioms` step over every declaration you claim; run `lean4checker` or
comparator beside it for the later steps. It also complements Lean's own warnings and the
Mathlib and Batteries linters, which it requires or recommends rather than replaces.

## What it checks, and what it doesn't

| `lake lint` does not accept | Left to your review, or trusted |
| --- | --- |
| `sorry` and `admit`, project `axiom`s and unknown axioms, anywhere in a declaration's transitive dependencies ([RG1001]–[RG1003]) | Whether each theorem states what you meant |
| Compiler-trusting proofs: `native_decide`, `decide +native`, `bv_decide` ([RG1004]) | Whether your invariants cover every write path |
| Axioms beyond the foundation each library claims: kernel-only (none), choice-free (`propext`, `Quot.sound`) or standard-logical (adds `Classical.choice`) ([RG1005]) | Whether your documentation describes the formal claim faithfully |
| `partial` or `unsafe` declarations you write ([RG1006]); unresolved `extern`/`implemented_by` paths ([RG3001]) and, in `checked` mode, unproved boundaries ([RG3002]) | Lean's kernel, compiler and runtime; Lake; the operating system |
| Build warnings ([RG2003]), modules outside the manifest ([RG2004]), automatic implicits or a missing `linter.missingDocs` ([RG2006]), modules without a module docstring ([RG5001]) | The packages you require, including a path dependency in your own repository: Regula does not replay their declarations through Lean's kernel |
| | Code that changes Lean's environment, compiler or build to make a check pass (see the [scope](SECURITY.md#scope) of the security policy) |

The [rule reference](https://rbeauchamp.github.io/regula/rules/) lists every rule, each
with a checked violating and corrected example.

## Try it

Regula is a Lake package with its own semantic versions, tagged `v<version>`; each release
supports exactly one Lean toolchain. Require the newest release for your `lean-toolchain` from
the [compatibility table](docs/guides/adoption.md#1-require-regula); the first release,
`v4.34.0`, is for `leanprover/lean4:v4.34.0`. When none matches, see
[when your Lean release has no Regula release](docs/guides/adoption.md#when-your-lean-release-has-no-regula-release).

1. **Require it** in `lakefile.toml`
   (`lakefile.lean`: `require regula from git "https://github.com/rbeauchamp/regula" @ "v4.34.0"`):
   ```toml
   [[require]]
   name = "regula"
   git = "https://github.com/rbeauchamp/regula"
   rev = "v4.34.0"
   ```
2. **Set it up and run it:**
   ```sh
   lake update regula
   lake exe regula init   # lint driver, leanOptions, foundation_manifest.json, AGENTS.md section
   lake lint              # 0 accepted · 1 violation · 2 invalid configuration · 3 incomplete
   ```
   `init` writes only what is missing, in either lakefile format, and never changes a value you
   set; running it again writes nothing. `lake exe regula doctor` reports anything missing or
   wrong with its exact fix.
3. **Review `foundation_manifest.json`.** The starter claims every library as
   `standard-logical`, which admits ordinary classical proofs; strengthen a claim where you can,
   and give each library a glob covering all its modules (`globs = ["MyLib", "MyLib.+"]`), which
   `doctor` reports when a module is left out.

**To update**, change the tag, and `lean-toolchain` when the new release supports another
toolchain, then run `lake update regula` and `lake exe regula init` again.

**Why your first `sorry` shows [RG2003] and INCOMPLETE.** Lean warns `declaration uses 'sorry'`,
and `lake lint` inspects its rules only after a build without warnings ([RG2003]). A warning
stops the audit before that inspection, so the evidence the proof rules need is missing and
the result is INCOMPLETE (exit 3), not a [RG1002] violation. Neither is accepted, and silencing
the warning does not help: the hole is then reported as [RG1002]. For the same reason, a first run
on an existing project usually reports build warnings, such as missing docstrings, before any
foundation rule.

The [adoption guide](docs/guides/adoption.md) covers fresh runs, CI and editor diagnostics.

## For coding agents

- `lake exe regula init` adds a short section to your repository's `AGENTS.md` (the nearest one
  from the Lake project up to the repository root) that tells your agent to run
  `lake exe regula agent-guide`, a compact briefing of every rule ordered for writing code, before
  it writes Lean; `lake exe regula init --skill` installs the briefing as an agent skill instead,
  and running `init` after an update refreshes it.
- The first finding of each rule in a run adds why it matters, the common compliant rewrites
  and a checked example of the fix (or, where the checked files are qualification inputs, the
  correction they demonstrate); `lake exe regula explain <RULE-ID>` prints the full rule
  offline.
- `lake lint -- --json-out PATH` writes one versioned JSON document with every finding, its
  remedy and each fired rule's guidance; exit codes are documented and stable.

## Learn more

- [Why: precise claims and kernel-checked evidence](https://rbeauchamp.github.io/regula/standard/0-precise-claims-and-kernel-checked-evidence/),
  including non-vacuity and the role of testing.
- [The standard](https://rbeauchamp.github.io/regula/standard/): the rulebook and review
  checklist behind the linter. Conformance means satisfying every applicable row of its
  [compliance checklist](https://rbeauchamp.github.io/regula/standard/8-compliance-audit/),
  which includes semantic review.
- [The roadmap](https://github.com/users/rbeauchamp/projects/8): where Regula is going, with no dates.
- [Standalone examples](examples/README.md), the [documentation index](docs/README.md), the
  [Lean module map](lean/README.md) and the
  [contributor guide](docs/guides/contributing.md#develop-and-verify).

**Challenge it.** This is a public review draft.
[Open an issue](https://github.com/rbeauchamp/regula/issues) for checker false positives or
omissions, unclear or unnecessarily restrictive requirements, incorrect Lean claims or
adoption difficulties. Cite the rule or section, and include a small Lean example and your
toolchain version where useful. Report a security vulnerability privately instead, for example
honest code that makes a violating project pass, as the [security policy](SECURITY.md) tells.

## Repository map

| Area | Purpose |
| --- | --- |
| [docs/](docs/README.md) | The guides, and where the standard's source lives. |
| [lean/](lean/README.md) | The `regula` package adopters require, with no dependency beyond the Lean toolchain: the linter, its rule registry and proofs, and checked examples. |
| [audit/](audit/lakefile.lean) | The package of the standard's example library (`Audit`), which imports only Lean's core libraries and requires `regula` by relative path as an adopter does. |
| [integration/mathlib/](integration/mathlib/lakefile.lean) | The Mathlib integration package (`MathlibAudit`): a Mathlib adopter of `regula` that checks the Mathlib-specific behaviour Regula supports. Only `./scripts/verify.sh mathlib` and its CI job use it. |
| [markdown/](markdown/lakefile.toml) | The package of the checks of the tracked Markdown documents. The checks are for the rule IDs in prose, for the writing rules with the baseline `prose-baseline.json`, and for the vocabulary [`CONTEXT.md`](CONTEXT.md). One more check is for the links of this file to the rule reference. Only `./scripts/verify.sh docs` uses it. |
| [examples/](examples/README.md) | Adopting projects and the rule-example sources. |
| [website/](docs/guides/website.md) | The standard's Verso source and the rule-reference site builder. |

## Supported toolchain

| Component | Authoritative pin |
| --- | --- |
| Lean | [lean-toolchain](lean-toolchain) |
| Mathlib (the separate Mathlib integration check only) | The `mathlib` entry in [integration/mathlib/lake-manifest.json](integration/mathlib/lake-manifest.json) |

Each release supports only the Lean toolchain pinned in its `lean-toolchain`; the [compatibility table](docs/guides/adoption.md#1-require-regula) lists each release's toolchain, and a move to another toolchain is a minor release. The `regula` package requires no other package and imports no Mathlib modules, so requiring it adds no Mathlib to your project. The repository's own build, both acceptance steps, the standard's examples and the site use no Mathlib either; Mathlib is used only by the separate [Mathlib integration check](docs/guides/contributing.md#mathlib-integration-check), whose result is about the Mathlib revision it pins. See the [adoption guide](docs/guides/adoption.md) for dependency resolution and the [contributor guide](docs/guides/contributing.md#develop-and-verify) for build commands.

## License

[MIT](LICENSE), except the adapted container recursion of Lean's JSON parser in
`lean/Regula/Checker/PolicyCodec.lean`, which keeps its upstream Apache 2.0 notice
([license text](LICENSES/Apache-2.0.txt); see [design influences](docs/guides/design-influences.md#adapted-code-and-licenses)).

[RG1001]: https://rbeauchamp.github.io/regula/rules/RG1001/
[RG1002]: https://rbeauchamp.github.io/regula/rules/RG1002/
[RG1003]: https://rbeauchamp.github.io/regula/rules/RG1003/
[RG1004]: https://rbeauchamp.github.io/regula/rules/RG1004/
[RG1005]: https://rbeauchamp.github.io/regula/rules/RG1005/
[RG1006]: https://rbeauchamp.github.io/regula/rules/RG1006/
[RG2003]: https://rbeauchamp.github.io/regula/rules/RG2003/
[RG2004]: https://rbeauchamp.github.io/regula/rules/RG2004/
[RG2006]: https://rbeauchamp.github.io/regula/rules/RG2006/
[RG3001]: https://rbeauchamp.github.io/regula/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/rules/RG3002/
[RG5001]: https://rbeauchamp.github.io/regula/rules/RG5001/
