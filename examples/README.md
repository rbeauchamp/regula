# Adopter examples

[build-lint](build-lint/README.md) is the reference `lakefile.lean` integration: `lake build --wfail` and then `lake lint`, with its own configuration and an executable contract that a proof must satisfy. [lake-lint-toml](lake-lint-toml/README.md) is the `lakefile.toml` integration. The checker is in [`lean/Regula/`](../lean/Regula/).

Start with the [adoption guide](../docs/guides/adoption.md) for the setup of a package and the obligations of conformance. The [Lean module map](../lean/README.md) tells about the mathematical and application proof surfaces of this repository.

The violating and corrected sources that the [rule reference](https://rbeauchamp.github.io/regula/dev/rules/) shows are in [rules](rules/README.md). They are the example pairs of the registry, not adopter projects.
