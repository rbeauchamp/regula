# Lean sources

These modules implement the contracts and checkers and supply checked Core examples for
the [standard](https://rbeauchamp.github.io/regula/dev/standard/). They form the `regula` package that
projects require, whose source directory is `lean/`; it requires no package beyond the Lean
toolchain. Imports retain their Lean module names, such as `AuditApp.Limiter` and
`Regula.Contract`. The standard's Mathlib examples, such as `Audit.Research`, are the separate
`regula_audit` package in [`../audit/`](../audit/lakefile.lean), which requires this package by
relative path and Mathlib.

## Choose a starting point

| Purpose | Start here | Boundary |
| --- | --- | --- |
| Use the proof-bearing contract interface | [Regula.Contract](Regula/Contract.lean) | Public interface tying evidence to the named executable definition. |
| Register a material claim | [Regula.MaterialClaim](Regula/MaterialClaim.lean) | Public `@[regula_material]` attribute selecting the RG5002/RG5003 docstring and Intent-section obligations. |
| Inspect mathematical/specification examples | [Audit](../audit/Audit.lean) | Claimed abstract-specification surface of the Mathlib-dependent package; representative checks of the standard's claims. |
| Inspect the verified application | [Main](Main.lean), [AuditApp](AuditApp.lean) | Claimed limiter application; proofs concern its actual definitions and its IO boundary remains reported. |
| Use typed policy data and admission | [RegulaPolicy](RegulaPolicy.lean), [domain guide](../docs/guides/policy-domain.md) | Separate claimed pure library; representation proofs do not authenticate compiler observations or establish complete acceptance. |
| Inspect the proved checker core | [RegulaCore.Policy](RegulaCore/Policy.lean), [rule registry](RegulaCore/Rule.lean) | Claimed pure projections the checker runs (claim request, scope admission, [transcript coordinates](RegulaCore/Coordinates.lean), rules, labels), census assembly ([Assembly](RegulaCore/Assembly.lean)), the editor linter's request and declaration decisions ([EditorPolicy](RegulaCore/EditorPolicy.lean)) and the `lint` driver's exit classification ([Lint](RegulaCore/Lint.lean)); frontend, environment and process adapters stay operational. |
| Read or change the agent-facing rule guidance | [rule registry](RegulaCore/Rule.lean), [Feedback](RegulaCore/Feedback.lean), [Guidance](RegulaCore/Guidance.lean), [regula command](Regula/Cli/Main.lean) | Claimed requirement, rationale, remedy, rewrites and checked example pair of every rule; the proved run order and once-per-rule finding text; the offline `regula` explain, index, agent briefing and skill with a proved parser. The printing root stays operational. |
| Understand declaration and execution auditing | [AxiomGate](Regula/Checker/AxiomGate.lean) | Operational checker implementation, qualified separately from the claimed proof surfaces. |
| Use the Lake lint driver | [Lint](Regula/Checker/Lint.lean) | `lint`: the `axiomGate` project audit behind `lake lint`, with proved exit classification. |
| Understand documentation auditing | [DocFenceAudit](Regula/Checker/DocFenceAudit.lean) | Checks recursively discovered Markdown fences as printed and, with `--verso`, every `lean` block of the Verso standard, which it builds and renders. |
| Inspect the rule-reference site | [RegulaCore.Edition](RegulaCore/Edition.lean), [RegulaCore.Site](RegulaCore/Site.lean), [Guide](RegulaCore/Guide.lean), [site builder](Regula/Site/Artifact.lean), [guide](../docs/guides/website.md) | Claimed pure editions, version-matched help links, route policy, escaping, filters, diffs, release banners, link checks and page structure, and the typed rule explanations; the builder's evidence, Verso and filesystem steps stay operational. |
| Inspect cold-start verification | [RegulaVerification](RegulaVerification.lean) | Claimed argument-selection/recipe driver; process IO remains a reported boundary under the shell deadline. |
| Provision the shared local Mathlib | [RegulaProvision](RegulaProvision.lean) | Claimed toolchain-only setup run before the shell deadline; its receipt-admission, package-step and retention proofs do not authenticate Git, Lake, `cp`, `chmod` or locking effects. |
| Inspect proved qualification oracles | [RegulaQualification](RegulaQualification/Checks.lean), [guide](../docs/guides/lean-qualification.md) | Claimed pure observation predicates; separate Lean IO drivers do not authenticate the compiler or OS by proof. |
| Inspect checker qualification | [CheckerSelftest](Regula/Checker/CheckerSelftest.lean), [fixture manifest](Fixtures/fixtures.json) | Isolated positive controls and intended-failure mutations; never import mutations into a claimed surface. |
| Inspect optional serialized-graph checking | [FreshChecker](Regula/Checker/FreshChecker.lean) | Separate fresh replay and exact Lake coverage; no claim of native execution correctness. |

## Follow the sources

Module docstrings describe purpose and assumptions. The
[Lake configuration](../lakefile.lean) defines module/target discovery, and the
[surface manifest](../foundation_manifest.json) defines claims and exclusions; the
`audit/` package has its own [configuration](../audit/lakefile.lean) and
[surface manifest](../audit/foundation_manifest.json).
Those files, not this navigation table or folder names, own the inventory.

The checkers and the `ExecutableContract` interface share the `Regula`
library. The interface may be imported by a claimed surface as described in the
[standard](https://rbeauchamp.github.io/regula/dev/standard/8-tooling-and-machine-audit/#810-dogfooding);
this does not make the operational checker a claimed proof surface.

For runnable consumers with their own configurations, use the
[standalone examples](../examples/README.md). For commands and review instructions,
use the [contributor guide](../docs/guides/contributing.md).

The [linter product architecture](../docs/guides/linter-architecture.md) fixes the registry, diagnostic, editor and site modules. The [rule coverage](../docs/guides/rule-coverage.md) guide distinguishes the implemented detectors from semantic review.
