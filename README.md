# Regula

A strict linter for Lean. Regula refuses proof holes, project axioms and proofs that trust the compiler. Each finding gives a fix.

Use Regula when you depend on Lean code that you do not read line by line, or when you publish results as proved. It checks each declaration in the libraries you select. It also checks proof dependencies through imports. You choose which foundation axioms each library can use.

## Why use it?

`lake build` accepts this module. Lean warns only at `double`, which contains the `sorry`:

```lean
/-! A theorem that depends on an unfinished proof. -/

/-- A lemma that nobody proved yet. -/
theorem double (n : Nat) : n + n = 2 * n := by sorry

/-- A theorem that uses the lemma. -/
theorem twice (n : Nat) : 2 * n = n + n := (double n).symm
```

Regula also refuses `twice`, because its proof depends on `double`. Here are the findings, with omitted text marked by `…`:

```text
…
RG1002 [violation; …]: double: … axioms=["sorryAx"] -> hole
  fix: Complete the proof. …
…
RG1002 [violation; …]: twice: … axioms=["sorryAx"] -> hole
…
```

Each finding gives the rule, the location and the fix. The [rule reference](https://rbeauchamp.github.io/regula/rules/) gives each rule and shows an example with its correction.

## Try it

Regula `v0.11.1` is for the Lean toolchain `leanprover/lean4:v4.34.1`. With [elan](https://lean-lang.org/install/) installed, make a project. Then add Regula:

```sh
lake +leanprover/lean4:v4.34.1 new demo
cd demo
cat >> lakefile.toml <<'EOF'

[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "v0.11.1"
EOF
lake update regula
```

Save the example above as `Shortcut.lean` in `demo`. Then examine the file:

```sh
lake exe axiomGate --file Shortcut.lean   # exit 1: proof holes in double and twice
```

The first command that runs Regula compiles it. This command checks one file, not the full project.

## Add it to your project

Add the `[[require]]` table above to your `lakefile.toml`. For `lakefile.lean`, add `require regula from git "https://github.com/rbeauchamp/regula" @ "v0.11.1"`.

```sh
lake update regula
lake exe regula init
lake lint
```

`init` adds missing configuration and runs `doctor`, which reports the remaining setup steps. It does not change values that you set. Correct each finding. Then run `lake lint` again.

`lake lint` requires a build with no warnings. The first run often stops at missing docstrings or a `sorry` warning ([RG2003], exit 3). Correct those warnings before the proof checks can run.

The starter `foundation_manifest.json` permits the usual classical axioms: `propext`, `Quot.sound` and `Classical.choice`. The [adoption guide](docs/guides/adoption.md) covers library selection, stricter foundations, CI, editor diagnostics and updates.

## What a pass means

Regula checks the libraries and executable roots that your manifest selects. Its checks include:

- Proof holes, project axioms, imported axioms outside the selected foundation, and proofs that trust the compiler, such as `native_decide`.
- Declaration and module coverage, required documentation, build warnings and Lean options.
- Reachable execution boundaries such as `extern` and `implemented_by`. In `checked` mode, boundaries outside the Lean toolchain require proofs of correspondence ([RG3002]).

A pass does not show that your theorems state the intended claims. Review their statements, assumptions, invariants and documentation against the [standard's compliance checklist](https://rbeauchamp.github.io/regula/standard/8-compliance-audit/).

Regula trusts Lean's kernel, compiler and runtime, Lake and the operating system. It also trusts packages outside your Git work tree. It does not replay those packages in Lean's kernel. Code loaded by name at runtime and spawned processes are outside its execution account. See the [assurance boundaries](docs/guides/proofs-and-boundaries.md) and [security scope](SECURITY.md#scope) for the full limits.

Keep Lean's warnings and the community linters. For independent kernel replay, run `lake env leanchecker` beside Regula, as described in [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

Regula accepts no `sorry`, so use it when you complete proofs. For Mathlib pull requests, use Mathlib's CI. Use [Comparator](https://github.com/leanprover/comparator) to check an untrusted proof against a fixed statement.

## For coding agents

`init` adds an `AGENTS.md` instruction to read `lake exe regula agent-guide` before the agent writes Lean. Use `lake exe regula init --skill` to install that briefing as a skill instead.

- `lake exe regula explain <RULE-ID>` gives the full rule without a network connection.
- `lake lint -- --json-out PATH` writes findings and fixes as versioned JSON. The [adoption guide](docs/guides/adoption.md#4-run-lake-lint) defines the exit codes.

## Supported toolchain

Each release is for one Lean toolchain. Use the [compatibility table](docs/guides/adoption.md#1-require-regula) to select a release for your project. This repository's pin is [lean-toolchain](lean-toolchain).

Regula adds no Mathlib dependency. Only the separate [Mathlib integration check](docs/guides/contributing.md#mathlib-integration-check) uses Mathlib. Before version 1.0, a minor release can add a rule or make a rule stricter.

## Learn more

- [The standard](https://rbeauchamp.github.io/regula/standard/): the requirements and their rationale.
- [Why proofs matter](https://rbeauchamp.github.io/regula/standard/0-precise-claims-and-kernel-checked-evidence/): precise claims and the limits of their evidence.
- [Examples](examples/README.md) and the [documentation index](docs/README.md).
- [Contributor guide](docs/guides/contributing.md#develop-and-verify) and [roadmap](https://github.com/users/rbeauchamp/projects/8).

[Open an issue](https://github.com/rbeauchamp/regula/issues) for incorrect findings, unclear rules or adoption problems. Include a small example and your toolchain version where useful. Report vulnerabilities privately through the [security policy](SECURITY.md).

## License

The parts of `lean/Regula/Checker/PolicyCodec.lean` adapted from the JSON parser and printer of Lean 4 keep their upstream Apache 2.0 notices ([license text](LICENSES/Apache-2.0.txt), [design influences](docs/guides/design-influences.md#adapted-code-and-licenses)). All other code uses [MIT](LICENSE).

Regula is not affiliated with the Lean FRO or Mathlib.

[RG2003]: https://rbeauchamp.github.io/regula/rules/RG2003/
[RG3002]: https://rbeauchamp.github.io/regula/rules/RG3002/
