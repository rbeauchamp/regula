# Documentation

The [Regula standard](https://rbeauchamp.github.io/regula/dev/standard/) defines the rules for
mathematical proofs and verified functional programs in Lean. The guides below explain how to use
Regula and how to work on this repository; they add no conformance rules.

## The standard

Start with the [core philosophy](https://rbeauchamp.github.io/regula/dev/standard/0-core-philosophy/),
then use the [chapter index](https://rbeauchamp.github.io/regula/dev/standard/introduction/#document-structure).
To review a project, read the
[critical violations](https://rbeauchamp.github.io/regula/dev/standard/critical-violations/) and
complete the [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/).
Every section and checklist row has a stable anchor, such as
`https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-04`.

The standard's only source is the Verso library `RegulaStandard` in [`website/`](../website/):
[`RegulaStandard.lean`](../website/RegulaStandard.lean) (front page and introduction) and
[`RegulaStandard/`](../website/RegulaStandard/) (modules 0–9 and Critical Violations). There is
no Markdown copy. The sources are plain text, so an agent without network access can read the
standard there, including from an adopting project's `.lake/packages/regula/`.

Every `lean` block of the standard and every Lean fence below `docs/`, including in the guides,
follows the
[checked example convention](https://rbeauchamp.github.io/regula/dev/standard/introduction/#lean-example-convention).

## Use Regula

- [Adopt the standard](guides/adoption.md): package setup, surfaces, profiles, `lake lint`,
  editor diagnostics, limits, and the semantic obligations commands cannot establish.
- [Rule-reference website](guides/website.md): sources, guarantees, build, publication and
  versions of the generated rule reference, and the rule-change workflow.

## Work on Regula

- [Work on this repository](guides/contributing.md): layout, development, verification and
  review.
- [Design influences and attribution](guides/design-influences.md): adapted code, dependencies
  and design influences.

Product contract and design:

- [Linter and website architecture](guides/linter-architecture.md): interfaces, pins and
  versioned help links.
- [Rule coverage](guides/rule-coverage.md): the twenty-two diagnostics, how the standard's clauses
  map to checklist rows, and the review obligations no rule discharges.
- [Rule registry and diagnostics](guides/rule-registry.md): typed interfaces, output schemas,
  source conventions and qualification.
- [Source-owned rule examples](guides/rule-examples.md): fixture inputs, exact expectations and
  unavailable-analysis demonstrations.

Implementation accounts:

- [Policy acceptance contract](guides/policy-acceptance.md): exact scope, complete results and
  the pure proof boundary.
- [Typed policy domain](guides/policy-domain.md): categories, admission invariants, worker
  bindings and proof boundaries.
- [Policy proofs](guides/policy-proofs.md): executable decision theorems, concrete acceptance and
  the remaining operational boundaries.
- [Native observation and local feedback](guides/native-linter.md): the editor linter's shared
  observers, local requests and their limits.
- [Project producer evidence](guides/engine-producers.md): extraction census, replay receipts,
  documentation diagnostics and source-owned examples.
- [Lean qualification tooling](guides/lean-qualification.md): qualification campaigns and what
  each proves, observes or trusts.
