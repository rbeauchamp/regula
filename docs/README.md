# Documentation

The [Regula standard](https://rbeauchamp.github.io/regula/dev/standard/) defines the rules for
mathematical proofs and verified functional programs in Lean. Its
[introduction](https://rbeauchamp.github.io/regula/dev/standard/introduction/) lists the modules
and where to start; every section and checklist row has a stable anchor, such as
`https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/#DOC-04`. The guides below
explain how to use Regula and how to work on this repository; they add no conformance rules.

The standard's only source is the Verso library `RegulaStandard` in [`website/`](../website/):
[`RegulaStandard.lean`](../website/RegulaStandard.lean) (front page and introduction) and
[`RegulaStandard/`](../website/RegulaStandard/) (modules 0–8 and Critical Violations). There is
no Markdown copy. The sources are plain text, so an agent without network access can read the
standard there, including from an adopting project's `.lake/packages/regula/`. Every `lean`
block of the standard and every Lean fence below `docs/` follows the
[checked example convention](https://rbeauchamp.github.io/regula/dev/standard/introduction/#lean-example-convention).

## Use Regula

- [Adopt Regula](guides/adoption.md): `require`, `lake exe regula init` and `doctor`, surfaces,
  profiles, `lake lint`, updating, editor diagnostics, limits, and the semantic obligations
  commands cannot establish.
- [Rule-reference website](guides/website.md): sources, guarantees, build, publication and
  versions of the generated rule reference, and the rule-change workflow.
- [Performance notes](guides/performance-notes.md): practical guidance for efficient Lean code.

## Work on Regula

- [Work on this repository](guides/contributing.md): layout, development, verification, the
  repository's own conformance, review, and releases.
- [Writing rules](guides/writing.md): the rules for new and changed Markdown documents, the
  checks of these rules, and the baseline.
- [Supported toolchain](guides/toolchains.md): the exact released compiler identity and
  the boundary for unsupported versions.
- [Architecture](guides/architecture.md): packages, the rule registry, findings, output
  schemas, enforcement paths, rule examples and how the rules cover the standard.
- [Proofs and boundaries](guides/proofs-and-boundaries.md): what the implementation proves,
  observes and trusts, boundary by boundary, and the qualification ledger.
- [Design influences and attribution](guides/design-influences.md): adapted code, dependencies
  and design influences.
- [Specification of the smaller Regula](../specification/README.md): the fate of each rule, the closed
  input and the new rules, with their formal statements.

### Map of the repository

| Area | Purpose |
| --- | --- |
| [docs/](README.md) | The guides, and the place of the source of the standard. |
| [lean/](../lean/README.md) | The `regula` package that adopters require. It contains the linter, its rule registry, its proofs and checked examples, and it requires only the Lean toolchain. |
| [audit/](../audit/lakefile.lean) | The package of the example library of the standard (`Audit`). It imports only the core libraries of Lean, and it requires `regula` by a relative path, as an adopter does. |
| [integration/mathlib/](../integration/mathlib/lakefile.lean) | The Mathlib integration package (`MathlibAudit`), an adopter of `regula` that uses Mathlib. It checks the behaviour of Regula that is specific to Mathlib. Only `./scripts/verify.sh mathlib`, its CI job and `./scripts/verify.sh diagnostics readers` use it. |
| [markdown/](../markdown/lakefile.toml) | The package of the checks of the tracked Markdown documents. It checks rule IDs in prose, the [writing rules](guides/writing.md), the vocabulary [`CONTEXT.md`](../CONTEXT.md) and the links of the root `README.md` to the rule-reference site. It also checks the example of the root `README.md`, and that the root `README.md` and the adoption guide open with the summary of Regula. Only `./scripts/verify.sh docs` and `./scripts/verify.sh diagnostics readers` use it. |
| [specification/](../specification/README.md) | The specification of the smaller Regula, and the Lean package of its formal statements. The package requires lean-intent and the root package. The first acceptance step builds it with warnings as errors. |
| [examples/](../examples/README.md) | Adopting projects and the sources of the rule examples. |
| [website/](guides/website.md) | The Verso source of the standard and the builder of the rule-reference site. |
