# Regula

A strict linter for Lean. Regula refuses proof holes, project axioms and proofs that trust the compiler. Each finding links to its rule page, which gives the fix.

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

Regula also refuses `twice`, because its proof depends on `double`. Here are the findings of `lake lint` for this module as `Demo.Shortcut`, with omitted text marked by `…`:

```text
…
RG1002 double (module Demo.Shortcut): depends on sorryAx https://rbeauchamp.github.io/regula/dev/rules/RG1002/
…
RG1002 twice (module Demo.Shortcut): depends on sorryAx https://rbeauchamp.github.io/regula/dev/rules/RG1002/
…
regula: fail, … findings
```

Each finding gives the rule, the constant, its module, what is wrong and the page of the rule. The last line gives the verdict. A finding does not print the fix. The page of its rule gives the fix, and `lake exe regula explain <RULE-ID>` prints it offline. The [rule reference](https://rbeauchamp.github.io/regula/rules/) gives each rule and shows an example with its correction.

## Try it

Regula `v0.11.1` is for the Lean toolchain `leanprover/lean4:v4.34.1`. With [elan](https://lean-lang.org/install/) installed, make a project. Regula also requires GNU coreutils `ls` (see [A program that lists directories](docs/guides/adoption.md#a-program-that-lists-directories)). On macOS, run `brew install coreutils`. Then add Regula:

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

The release `v0.11.1` still has the earlier commands: `axiomGate`, the options of `lake lint` and its exit code 3. The [README of that release](https://github.com/rbeauchamp/regula/blob/v0.11.1/README.md) documents them. Until the next release, use that README with this pin. The rest of this README describes `main`.

Save the example above as `Demo/Shortcut.lean` in `demo`, and add `import Demo.Shortcut` to `Demo.lean`. Then set up Regula, build the project and examine its build:

```sh
lake exe regula init
lake build
lake lint   # exit 1: RG1002 for double and twice
```

The first command that runs Regula compiles it. `init` writes the configuration that is missing, for example the lint driver and the manifest. `lake build` builds the project with a warning at the `sorry`. `lake lint` reads that build.

## Add it to your project

Add the `[[require]]` table above to your `lakefile.toml`. For `lakefile.lean`, add `require regula from git "https://github.com/rbeauchamp/regula" @ "v0.11.1"`.

```sh
lake update regula
lake exe regula init
lake build --wfail
lake lint
```

`init` adds missing configuration and runs `doctor`, which reports the remaining setup steps. It does not change values that you set. Correct each finding. Then run `lake build --wfail` and `lake lint` again.

`lake lint` examines the finished build, and it builds nothing. Thus build first with `lake build --wfail`, which refuses each warning, also a `sorry` warning. That build decides [RG2003]. `lake lint` exits 0 for a pass and 1 for a fail. It exits 2 for an incomplete run, for example a module without its `.olean` file.

The starter `foundation_manifest.json` permits the usual classical axioms: `propext`, `Quot.sound` and `Classical.choice`. The [adoption guide](docs/guides/adoption.md) covers library selection, stricter foundations, CI and updates.

## What a pass means

Regula checks the libraries and executable roots that your manifest selects. Its checks include:

- Proof holes, project axioms, imported axioms outside the selected foundation, and proofs that trust the compiler, such as `native_decide`.
- The classification of targets, the coverage of modules and Lean options.
- Reachable execution boundaries such as `extern` and `implemented_by`. In `checked` mode, boundaries outside the Lean toolchain require proofs of correspondence ([RG3002]).

`lake lint` does not check documentation or build warnings. `lake build --wfail` refuses each warning, and the options that `init` writes turn on Lean's warning for a missing docstring.

A pass does not show that your theorems state the intended claims. Review their statements, assumptions, invariants and documentation against the [standard's compliance checklist](https://rbeauchamp.github.io/regula/standard/8-compliance-audit/).

Regula trusts Lean's kernel, compiler and runtime, Lake and the operating system. It reads the declarations of your project and of its packages from their builds. It replays no declaration in Lean's kernel. Code loaded by name at runtime and spawned processes are outside its execution account. See the [assurance boundaries](docs/guides/proofs-and-boundaries.md) and [security scope](SECURITY.md#scope) for the full limits.

Keep Lean's warnings and the community linters. Build with `lake build --wfail`, replay the build in Lean's kernel with `lake check`, and then run `lake lint`. On macOS, run it as `lake check --inadvisably-no-sandbox`. Kernel replay is a step of [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

Regula accepts no `sorry`, so use it when you complete proofs. For Mathlib pull requests, use Mathlib's CI. Use [Comparator](https://github.com/leanprover/comparator) to check an untrusted proof against a fixed statement.

## For coding agents

`init` adds an `AGENTS.md` instruction to read `lake exe regula agent-guide` before the agent writes Lean. Use `lake exe regula init --skill` to install that briefing as a skill instead.

- `lake exe regula explain <RULE-ID>` gives the full rule without a network connection.
- `lake lint` takes no options and writes no file. It prints one line for each finding, then the verdict. The [adoption guide](docs/guides/adoption.md#4-run-lake-lint) defines the exit codes.

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

The adapted container recursion of Lean's JSON parser and the adapted JSON printer in `lean/Regula/Checker/PolicyCodec.lean` keep their upstream Apache 2.0 notices ([license text](LICENSES/Apache-2.0.txt), [design influences](docs/guides/design-influences.md#adapted-code-and-licenses)). All other code uses [MIT](LICENSE).

Regula is not affiliated with the Lean FRO or Mathlib.

[RG2003]: https://rbeauchamp.github.io/regula/rules/RG2003/
[RG3002]: https://rbeauchamp.github.io/regula/rules/RG3002/
