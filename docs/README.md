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
- [Development toolchains](guides/toolchains.md): exact compiler identities, isolated
  compatibility revisions, qualification, and using Regula while fixing Lean. No revision is
  qualified yet for a compiler newer than Lean 4.34.0.
- [Architecture](guides/architecture.md): packages, the rule registry, findings, output
  schemas, enforcement paths, rule examples and how the rules cover the standard.
- [Proofs and boundaries](guides/proofs-and-boundaries.md): what the implementation proves,
  observes and trusts, boundary by boundary, and the qualification ledger.
- [Design influences and attribution](guides/design-influences.md): adapted code, dependencies
  and design influences.
