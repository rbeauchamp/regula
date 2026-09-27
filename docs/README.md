# Documentation

The [Regula standard](https://rbeauchamp.github.io/regula/dev/standard/) defines the rules for mathematical proofs
and verified functional programs in Lean. The [guides](#practical-guides)
explain how to use and maintain this repository without adding conformance rules.
The standard's only source is Verso in [`website/RegulaStandard/`](../website/RegulaStandard/),
where it can also be read without network access; see the [standard's README](standard/README.md).

## Read the standard

Start with the [core philosophy](https://rbeauchamp.github.io/regula/dev/standard/0-core-philosophy/), then choose a route:

- **Understand the rules:** use the [chapter index](https://rbeauchamp.github.io/regula/dev/standard/introduction/#document-structure).
- **Review a Lean project:** read [critical violations](https://rbeauchamp.github.io/regula/dev/standard/critical-violations/),
  then complete the [compliance checklist](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/).
- **Understand the checker:** read [tooling and machine audit](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/),
  then follow the [Lean module map](../lean/README.md) into the implementation.

## Practical guides

Use the product:

- [Adopt the standard](guides/adoption.md): package setup, surfaces, profiles, `lake lint`, editor
  diagnostics, and the semantic obligations commands cannot establish.
- [Rule-reference website](guides/website.md): sources, guarantees, build and publication of the
  generated rule reference, and the rule-change workflow.
- [Product qualification](guides/product-qualification.md): per-rule capability and evidence,
  supported routes, adopter journeys, website status and residual limits.
- [Opt-in intent screening](guides/intent-screening.md): probabilistic R-INTENT screening with
  user-set severities, formal discharge first, its evidence boundary and calibration.

Product contract and design:

- [Linter and website architecture](guides/linter-architecture.md): selected interfaces, pins,
  versioned help links and delivery sequence.
- [Complete rule coverage](guides/rule-coverage.md): twenty-two selected diagnostics and all
  residual checklist obligations.
- [Rule registry and diagnostics](guides/rule-registry.md): implemented typed interfaces, output
  migration, source conventions and qualification.
- [Source-owned rule examples](guides/rule-examples.md): fixture inputs, exact expectations and
  separate unavailable-analysis demonstrations.
- [Ecosystem research and design](guides/ecosystem-design.md): evidence from Lean and other
  language tools, alternatives and selected architecture.
- [Developer experience](guides/developer-experience.md): the selected native workflows,
  diagnostics, configuration and website interactions.
- [Design influences and attribution](guides/design-influences.md): actual reuse, adapted code,
  specific inspiration, optional external checking and project scope.
- [Optional con-leche export research](guides/con-leche-research.md): the no-go decision, pins,
  checker protocol, boundary account and coverage ledger.

Implementation accounts:

- [Policy acceptance contract](guides/policy-acceptance.md): exact scope, complete results, pure
  proof boundary and migration.
- [Typed policy domain](guides/policy-domain.md): implemented categories, admission invariants,
  worker bindings and proof boundaries.
- [Policy proofs](guides/policy-proofs.md): executable decision theorems, concrete acceptance and
  remaining operational boundaries.
- [Native observation and local feedback](guides/native-linter.md): the editor linter's shared
  observers, local requests and their limits.
- [Project producer evidence](guides/engine-producers.md): extraction census, replay receipts,
  documentation diagnostics and source-owned examples.
- [Foundation status](guides/foundation-status.md): bounded contract and execution-linkage
  baseline, proved relations, trusted boundaries and the completed foundation work.
- [Lean qualification tooling](guides/lean-qualification.md): the Lean replacements for former
  scripts and their qualification.
- [Work on this repository](guides/contributing.md): artifact locations, development,
  verification, and review.

Every Lean fence anywhere below `docs/` follows the
[checked example convention](https://rbeauchamp.github.io/regula/dev/standard/introduction/#lean-example-convention), including
fences in guides. A guide's location does not exempt its teaching examples from checking.

Return to the [project overview](../README.md).
