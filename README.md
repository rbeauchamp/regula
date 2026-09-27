# Regula

A strict linter and correctness standard for Lean.

Regula pairs a Lean linter and linked rule-reference website with a standard requiring precise types, propositions, and kernel-checked evidence.

The [standard](https://rbeauchamp.github.io/regula/dev/standard/) defines normative meaning. The current checker enforces declaration, foundation, execution-boundary, and checked-example requirements; the [product architecture](docs/guides/linter-architecture.md) specifies the typed rule catalogue, editor integration, and GitHub Pages website. Adopters run it with `lake lint` and receive editor diagnostics from `import Regula.Linter` ([adoption guide](docs/guides/adoption.md)). Every diagnostic carries its fix and links to its explanation in the [rule reference](https://rbeauchamp.github.io/regula/dev/rules/), generated from the rule registry and checked examples and published by CI from `main` ([website guide](docs/guides/website.md)). Its scope is Lean: dependent types, theorem statements, proofs, foundations, elaboration, modules, and executable Lean code. It serves both mathematical research and application development, with explicit assumptions and execution boundaries.

## Agent-first

Regula is designed first for agents, which increasingly write and fix Lean; humans can still
review a rule or browse the site. Adopting Regula tells your agent that your Lean code and
proofs must meet a strict standard that may not be in its training data, so Regula gives it
that standard before code is written and complete feedback after the linter runs, from the
installed package, with no website or other tool:

- `lake exe regula agent-guide` prints a compact briefing of every rule, ordered for writing
  code, to place in `AGENTS.md` or an agent skill (`lake exe regula skill`).
- Every finding states what is wrong, where, and the fix. The first finding of each rule in a
  run adds why it matters, the common compliant rewrites and a checked compliant example (or,
  where the checked files are qualification inputs, the correction they demonstrate).
- `lake exe regula explain <RULE-ID>` prints the full rule; `lake exe regula rules` lists them.
- `lake lint -- --json-out PATH` writes one versioned JSON document with every finding, its
  remedy and each fired rule's guidance; exit codes are documented and stable.

All of this is generated from one typed source, the rule registry, so it cannot drift from
the diagnostics or the website. New rules and tooling follow the same principle: a rule must
carry its requirement, rationale, remedy and checked examples to compile. See the
[adoption guide](docs/guides/adoption.md#0-brief-your-agent).

## Community review

**Public review draft.** We invite the Lean community to challenge the rules, examples,
and checker behavior.

Please [open an issue](https://github.com/rbeauchamp/regula/issues) with
unclear or unnecessarily restrictive requirements, incorrect Lean claims, checker false
positives or omissions, or adoption difficulties. Cite the relevant section and include
a small Lean example and toolchain version where useful. Feedback should help establish
which requirements are sound, useful, and practical for real Lean projects.

## Start here

- **Read the standard:** begin with the [core philosophy](https://rbeauchamp.github.io/regula/dev/standard/0-core-philosophy/), then use the [document map](docs/README.md) to find the relevant rules.
- **Use it in a project:** follow the [adoption guide](docs/guides/adoption.md) and the [standalone examples](examples/README.md).
- **Inspect or improve it:** explore the [Lean module map](lean/README.md) and the [contributor guide](docs/guides/contributing.md).

Conformance means satisfying every applicable row of the [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/). A passing checker command establishes its stated property; semantic review still determines whether the theorems express the intended claims and complete contracts.

## Repository map

| Area | Purpose |
| --- | --- |
| [docs/](docs/README.md) | Practical guides and the map to the standard. |
| [lean/](lean/README.md) | The `regula` package adopters require, with no dependency beyond the Lean toolchain: contracts, checked Core examples, checkers, the rule registry and isolated qualification fixtures. |
| [audit/](audit/lakefile.lean) | The Mathlib-dependent package: the standard's Mathlib examples (`Audit`), which requires `regula` by relative path as a Mathlib adopter does. |
| [examples/](examples/README.md) | Self-contained adopting projects, each with its own README and Lake configuration. |
| [website/](docs/guides/website.md) | Pinned Verso package: the normative standard's only source (`RegulaStandard`) and the renderer of the rule reference that publishes it. |

Root configuration files keep this a directly usable Lake package. Tool-owned hidden directories stay in their expected locations; build output and temporary probes are not maintained content areas.

## Supported toolchain

| Component | Authoritative pin |
| --- | --- |
| Lean | [lean-toolchain](lean-toolchain) |
| Mathlib (the `audit/` package and the website only) | The `mathlib` entry in [audit/lake-manifest.json](audit/lake-manifest.json) |

Only the pinned Lean release is supported. The `regula` package requires no other package and imports no Mathlib modules, so requiring it adds no Mathlib to your project; Mathlib is used only by the standard's mathematical examples in the separate `audit/` package. See the [adoption guide](docs/guides/adoption.md) for dependency resolution and the [contributor guide](docs/guides/contributing.md#develop-and-verify) for build commands.

## Verification

Complete local acceptance is exactly two commands, run in order, each under its own hard
420-second deadline: `./scripts/verify.sh` (including cold root-package builds) and then
`./scripts/verify.sh docs` (which also accepts the `audit/` package). CI runs the same two commands after provisioning pinned toolchain
and dependency caches, and separately builds and checks the rule-reference site. See the
[contributor guide](docs/guides/contributing.md#develop-and-verify) for setup and focused
diagnostics, and the [product qualification](docs/guides/product-qualification.md) for what
the integrated linter and website establish.

## License

[MIT](LICENSE), except the adapted container recursion of Lean's JSON parser in
`lean/Regula/Checker/PolicyCodec.lean`, which keeps its upstream Apache 2.0 notice
([license text](LICENSES/Apache-2.0.txt); see [design influences](docs/guides/design-influences.md#adapted-code-and-licenses)).
