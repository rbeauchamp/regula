# Regula

A strict linter for Lean projects. `lake lint` does not accept a theorem that depends on an `axiom` of your project, on `native_decide` or on a `sorry`, also through its imports.

Lean accepts such a theorem. It gives no warning for an `axiom` or for `native_decide`, and `lake build` succeeds. It warns about a `sorry` only at the declaration that contains the `sorry`. `#print axioms` shows these problems, but for one declaration at a time. Regula examines each declaration of the libraries that you claim, with the axioms that the declaration gets through its imports.

For example, `lake build` accepts this module with no warning:

```lean
/-! # Shortcut

A theorem that depends on an axiom, and a fact that compiled code checks. -/

/-- A shortcut that nobody proved. -/
axiom add_swap (a b : Nat) : a + b = b + a

/-- Addition commutes. -/
theorem swap (a b : Nat) : a + b = b + a := add_swap a b

/-- A fact that compiled code checks, not Lean's kernel. -/
theorem big : 2 ^ 20 = 1048576 := by native_decide
```

Regula gives these findings for it. Each `…` marks text that this copy leaves out:

```text
…
RG1001 [violation; freshFile; claim=classification-only; …/Shortcut.lean:6:6]: add_swap: … axioms=["add_swap"] -> unknown-axiom
  fix: Turn the assumption into a hypothesis (a binder or a proof-bearing structure field) of the results that need it, or replace the axiom with a proof.
  rule: …/rules/RG1001/ (offline: lake exe regula explain RG1001)
…
RG1003 [violation; freshFile; claim=classification-only; …/Shortcut.lean:9:8]: swap: … axioms=["add_swap"] -> unknown-axiom
  fix: Find where the axiom enters (often an imported dependency), and replace that dependency or its axiom with a proof or a hypothesis.
…
RG1004 [violation; freshFile; claim=classification-only; …/Shortcut.lean:12:8]: big: … -> compiler-trusting
  fix: Prove the same statement with a kernel-checked proof, for example `decide` (kernel reduction), `rfl` or an ordinary proof.
…
file audit: FAIL (4 violation(s), 0 incomplete finding(s))
```

Each finding gives the rule, the location and the fix. The first finding of each rule in a run also links the page of the rule. Later findings of that rule refer to the first. The [rule reference](https://rbeauchamp.github.io/regula/rules/) has a page for each rule, with an example that the checker rejects and its correction.

**Use Regula** when you depend on Lean code that you do not read line by line, or when you publish results as proved.

**Do not use Regula** for these jobs:

- To explore a proof. Regula accepts no `sorry`.
- To check a pull request to Mathlib. Mathlib's CI decides there.
- To judge a proof of a fixed statement from a source that you do not trust. [Comparator](https://github.com/leanprover/comparator) does that job.

Regula adds to the usual checks of a Lean project:

- Lean's warnings stay on. In a project with Mathlib, Regula also requires the Mathlib linters ([RG2006]).
- For an imported declaration, `#print axioms` reads a table that can omit axioms. Regula calculates the axioms from the declarations that Lean's kernel replayed.
- `lake env leanchecker` replays your compiled modules in Lean's kernel. Run it beside Regula. [Validating a Lean Proof](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) gives each step.

Regula is before version 1.0. A minor release can add a rule or make a rule stricter. Each release supports one Lean toolchain.

## Try it

Regula `v0.11.0` is for the Lean toolchain `leanprover/lean4:v4.34.1`. These commands use [elan](https://lean-lang.org/install/) to make a new project for that toolchain, and add Regula to it:

```sh
lake +leanprover/lean4:v4.34.1 new demo
cd demo
cat >> lakefile.toml <<'EOF'

[[require]]
name = "regula"
git = "https://github.com/rbeauchamp/regula"
rev = "v0.11.0"
EOF
lake update regula
```

Save the module of the example above as `Shortcut.lean` in `demo`. Then examine it:

```sh
lake exe axiomGate --file Shortcut.lean   # exit 1, with the findings above
```

The first command that runs Regula compiles it. On a laptop with 14 cores, that took 40 seconds. For the full text of a rule without a network, use `lake exe regula explain RG1001`.

## Add it to your project

Regula `v0.11.0` supports only the Lean toolchain `leanprover/lean4:v4.34.1`. For a different Lean release, use the [compatibility table](docs/guides/adoption.md#1-require-regula).

1. Add the `[[require]]` table above to `lakefile.toml`. For `lakefile.lean`, add `require regula from git "https://github.com/rbeauchamp/regula" @ "v0.11.0"`.
2. Get Regula, set up the project and run the linter:
   ```sh
   lake update regula
   lake exe regula init   # lint driver, leanOptions, foundation_manifest.json, AGENTS.md section
   lake lint              # 0 accepted · 1 violation · 2 invalid configuration · 3 incomplete
   ```
3. Correct each finding, and run `lake lint` again.

`init` writes only the items that are missing, and it does not change a value that you set. Then it runs `lake exe regula doctor`, which tells each missing item and its fix. On a project from `lake new`, `doctor` asks for `globs = ["Demo", "Demo.+"]` in the `[[lean_lib]]` table, so that the library contains each module.

`lake lint` examines its rules only after a build with no warnings. `init` turns on `linter.missingDocs`, thus the first run often stops at missing docstrings ([RG2003], exit 3). A `sorry` also gives a warning, thus it shows first as [RG2003] and not as [RG1002].

`foundation_manifest.json` claims each library as `standard-logical`, which permits `propext`, `Quot.sound` and `Classical.choice`. Where a library uses fewer axioms, change its claim to `choice-free` or `kernel-only` ([RG1005]).

The [adoption guide](docs/guides/adoption.md) tells how to read a finding, how to run Regula in CI and in the editor, and how to update Regula.

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
- [Standalone examples](examples/README.md), the [documentation index](docs/README.md) with the
  map of this repository, the [Lean module map](lean/README.md) and the
  [contributor guide](docs/guides/contributing.md#develop-and-verify).

**Challenge it.**
[Open an issue](https://github.com/rbeauchamp/regula/issues) for checker false positives or
omissions, unclear or unnecessarily restrictive requirements, incorrect Lean claims or
adoption difficulties. Cite the rule or section, and include a small Lean example and your
toolchain version where useful. Report a security vulnerability privately instead, for example
honest code that makes a violating project pass, as the [security policy](SECURITY.md) tells.

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

[RG1002]: https://rbeauchamp.github.io/regula/rules/RG1002/
[RG1005]: https://rbeauchamp.github.io/regula/rules/RG1005/
[RG2003]: https://rbeauchamp.github.io/regula/rules/RG2003/
[RG2006]: https://rbeauchamp.github.io/regula/rules/RG2006/
