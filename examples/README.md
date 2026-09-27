# Adopter examples

[build-lint](build-lint/README.md) is the reference `lakefile.lean` integration: `lake lint`
and the enforcing ordinary `lake build`, with its own configuration and proof-required
executable contract. [lake-lint-toml](lake-lint-toml/README.md) is the `lakefile.toml`
integration: `lake lint` plus live editor diagnostics from `import Regula.Linter`. The linter implementation lives in
[`lean/Regula/Checker/`](../lean/Regula/Checker/).

Start with the [adoption guide](../docs/guides/adoption.md) for package setup and
conformance obligations. The repository's mathematical and application proof surfaces
are described in the [Lean module map](../lean/README.md).

The checked violating and corrected sources shown on the [rule reference](https://rbeauchamp.github.io/regula/dev/rules/) live in [rules](rules/README.md); they are qualification fixtures, not adopter projects.
