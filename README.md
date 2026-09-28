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
  path it cannot resolve; in `checked` mode it also rejects any boundary whose correspondence
  you haven't proved.

Every finding states what is wrong, where and how to fix it, in the terminal, the editor and
versioned JSON, and `lake lint` adds, once per fired rule, why it matters and a checked
example of the fix. The same guidance is a briefing for the coding agents that increasingly
write Lean, installed with the package and read before they write a line. A pass is
mechanical: whether each theorem states what you meant is still your review, and Regula says
so.

**Use it when** Lean code you rely on is written or changed by someone you don't review line by
line (a coding agent, a new contributor, you in six months), or when you publish results as
proved and want others to see exactly what they rest on.
**Don't use it** as a Mathlib PR check (Mathlib's CI is the authority) or while exploring a
proof. It complements [comparator](https://github.com/leanprover/comparator): comparator checks
one statement against its challenge, and Regula gates the whole project. In the terms of
[Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/), Regula
runs the `#print axioms` step over every declaration you claim, against the foundation you
chose; run `leanchecker` or comparator beside it for the later steps. It also complements
Lean's own warnings and the Mathlib and Batteries linters, which it requires or recommends
rather than replaces.

## What it checks, and what it doesn't

| `lake lint` does not accept | Left to your review, or trusted |
| --- | --- |
| `sorry` and `admit`, project `axiom`s and unknown axioms, anywhere in a declaration's transitive dependencies (RG1001–RG1003) | Whether each theorem states what you meant |
| Compiler-trusting proofs: `native_decide`, `decide +native`, `bv_decide` (RG1004) | Whether your invariants cover every write path |
| Axioms beyond the foundation each library claims: kernel-only (none), choice-free (`propext`, `Quot.sound`) or standard-logical (adds `Classical.choice`) (RG1005) | Whether your documentation describes the formal claim faithfully |
| `partial` or `unsafe` declarations you write (RG1006); unresolved `extern`/`implemented_by` paths (RG3001) and, in `checked` mode, unproved boundaries (RG3002) | Lean's kernel, compiler and runtime; Lake; the operating system |
| Build warnings (RG2003), modules outside the manifest (RG2004), automatic implicits or a missing `linter.missingDocs` (RG2006), modules without a module docstring (RG5001) | |

The [rule reference](https://rbeauchamp.github.io/regula/dev/rules/) lists all 22 rules, each
with a checked violating and corrected example.

## Try it

Regula has no release yet. Pin an exact commit, and use the Lean release in its
[`lean-toolchain`](lean-toolchain) (v4.34.0), the only one it supports.

1. **Configure `lakefile.toml`:** the lint driver (a top-level key), the options Regula
   checks, Regula itself, and a glob covering every module of your library:
   ```toml
   lintDriver = "regula/lint"

   [leanOptions]
   linter.missingDocs = true
   autoImplicit = false
   relaxedAutoImplicit = false

   [[require]]
   name = "regula"
   git = "https://github.com/rbeauchamp/regula"
   rev = "<exact commit>"

   [[lean_lib]]
   name = "MyLib"
   globs = ["MyLib", "MyLib.+"]
   ```
   A project that uses Mathlib also enables
   [Mathlib's standard linters](docs/guides/adoption.md#community-conventions-and-linters).
2. **Classify the library** in `foundation_manifest.json` at the project root.
   `standard-logical` admits ordinary classical proofs:
   ```json
   {
     "schema-version": 2,
     "surfaces": [
       { "library": "MyLib", "claim": "standard-logical", "execution": "report",
         "rationale": "Classical proofs; compiled boundaries are reported." }
     ],
     "excluded-libraries": [],
     "excluded-executables": []
   }
   ```
3. **Run it:**
   ```sh
   lake update regula
   lake lint    # 0 accepted · 1 violation · 2 invalid configuration · 3 incomplete
   ```

**Why your first `sorry` shows RG2003 and INCOMPLETE.** Lean warns `declaration uses 'sorry'`,
and `lake lint` inspects its rules only after a build without warnings (RG2003). A warning
stops the audit before that inspection, so the evidence the proof rules need is missing and
the result is INCOMPLETE (exit 3), not a RG1002 violation. Neither is accepted, and silencing
the warning does not help: the hole is then reported as RG1002. For the same reason, a first run
on an existing project usually reports build warnings, such as missing docstrings, before any
foundation rule.

The [adoption guide](docs/guides/adoption.md) covers fresh runs, CI and editor diagnostics.

## For coding agents

- `lake exe regula agent-guide` prints a compact briefing of every rule, ordered for writing
  code, to place in `AGENTS.md`; `lake exe regula skill` prints it as an agent skill.
- The first finding of each rule in a run adds why it matters, the common compliant rewrites
  and a checked example of the fix; `lake exe regula explain <RULE-ID>` prints the full rule
  offline.
- `lake lint -- --json-out PATH` writes one versioned JSON document with every finding, its
  remedy and each fired rule's guidance; exit codes are documented and stable.

## Learn more

- [Why: precise claims and kernel-checked evidence](https://rbeauchamp.github.io/regula/dev/standard/0-precise-claims-and-kernel-checked-evidence/),
  including non-vacuity and the role of testing.
- [The standard](https://rbeauchamp.github.io/regula/dev/standard/): the rulebook and review
  checklist behind the linter. Conformance means satisfying every applicable row of its
  [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/),
  which includes semantic review.
- [Standalone examples](examples/README.md), the [documentation index](docs/README.md), the
  [Lean module map](lean/README.md) and the
  [contributor guide](docs/guides/contributing.md#develop-and-verify).

**Challenge it.** This is a public review draft.
[Open an issue](https://github.com/rbeauchamp/regula/issues) for checker false positives or
omissions, unclear or unnecessarily restrictive requirements, incorrect Lean claims or
adoption difficulties. Cite the rule or section, and include a small Lean example and your
toolchain version where useful.

## Repository map

| Area | Purpose |
| --- | --- |
| [docs/](docs/README.md) | The guides, and where the standard's source lives. |
| [lean/](lean/README.md) | The `regula` package adopters require, with no dependency beyond the Lean toolchain: the linter, its rule registry and proofs, and checked examples. |
| [audit/](audit/lakefile.lean) | The Mathlib-dependent package: the standard's Mathlib examples (`Audit`), which requires `regula` by relative path as a Mathlib adopter does. |
| [examples/](examples/README.md) | Adopting projects and the rule-example sources. |
| [website/](docs/guides/website.md) | The standard's Verso source and the rule-reference site builder. |

## Supported toolchain

| Component | Authoritative pin |
| --- | --- |
| Lean | [lean-toolchain](lean-toolchain) |
| Mathlib (the `audit/` package and the website only) | The `mathlib` entry in [audit/lake-manifest.json](audit/lake-manifest.json) |

Only the pinned Lean release is supported. The `regula` package requires no other package and imports no Mathlib modules, so requiring it adds no Mathlib to your project; Mathlib is used only by the standard's mathematical examples in the separate `audit/` package. See the [adoption guide](docs/guides/adoption.md) for dependency resolution and the [contributor guide](docs/guides/contributing.md#develop-and-verify) for build commands.

## License

[MIT](LICENSE), except the adapted container recursion of Lean's JSON parser in
`lean/Regula/Checker/PolicyCodec.lean`, which keeps its upstream Apache 2.0 notice
([license text](LICENSES/Apache-2.0.txt); see [design influences](docs/guides/design-influences.md#adapted-code-and-licenses)).
