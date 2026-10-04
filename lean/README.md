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
| Use the proof-bearing contract interface | [Regula.Contract](Regula/Contract.lean) | Public interface tying evidence to the named executable definition, with the decision kinds (`Decides`, `DecidesSoundly`, `DecidesCompletely`) that state which directions of a checker are proved. |
| Register a material claim | [Regula.MaterialClaim](Regula/MaterialClaim.lean) | Public `@[regula_material]` attribute selecting the [RG5002]/[RG5003] docstring and Intent-section obligations. |
| Register a decision function | [Regula.Decision](Regula/Decision.lean) | Public `@[regula_decision]` attribute selecting the [RG1008] obligation: a decision contract in the function's inventory, or a `Decidable` result type. It does not find functions that are not registered. |
| Inspect mathematical/specification examples | [Audit](../audit/Audit.lean) | Claimed abstract-specification surface of the Mathlib-dependent package; representative checks of the standard's claims. |
| Inspect the verified application | [Main](Main.lean), [AuditApp](AuditApp.lean) | Claimed limiter application; proofs concern its actual definitions and its IO boundary remains reported. |
| Use typed policy data and admission | [RegulaPolicy](RegulaPolicy.lean), [proofs and boundaries](../docs/guides/proofs-and-boundaries.md#keys-census-and-collection) | Separate claimed pure library; representation proofs do not authenticate compiler observations or establish complete acceptance. |
| Inspect the proved checker core | [RegulaCore.Policy](RegulaCore/Policy.lean), [rule registry](RegulaCore/Rule.lean) | Claimed pure projections the checker runs (claim request, scope admission, [transcript coordinates](RegulaCore/Coordinates.lean), rules, labels), census assembly ([Assembly](RegulaCore/Assembly.lean)), the editor linter's request and declaration decisions ([EditorPolicy](RegulaCore/EditorPolicy.lean)) and the `lint` driver's exit classification ([Lint](RegulaCore/Lint.lean)); frontend, environment and process adapters stay operational. |
| Read or change the agent-facing rule guidance | [rule registry](RegulaCore/Rule.lean), [Feedback](RegulaCore/Feedback.lean), [Guidance](RegulaCore/Guidance.lean), [regula command](Regula/Cli/Main.lean) | Claimed requirement, rationale, remedy, rewrites and checked example pair of every rule; the proved run order and once-per-rule finding text; the offline `regula` explain, index, agent briefing and skill with a proved parser. The printing root stays operational. |
| Set up an adopting project | [RegulaCore.Setup](RegulaCore/Setup.lean), [Regula.Cli.Setup](Regula/Cli/Setup.lean) | Claimed setup decision of `regula init` and `regula doctor` (lint driver, options, manifest, agent guidance, toolchain, modules outside every library) with proved idempotence (`plan_idempotent`) and no added option beside a `-D` that sets it (`added_unargued`); observing the project through Lake, editing the lakefile and writing files stay operational, confirmed by observing again. |
| Cut a release | [Release](Regula/Release.lean), [workflow](../.github/workflows/release.yml), [procedure](../docs/guides/contributing.md#release) | Operational release steps (the Release workflow and the `candidate`, `release-verify`, `release-site` and `publish` jobs of CI on `main`) run with the toolchain alone, and the kernel checks the proved release decisions (`tagAction`; `nextVersion` and `admits`, which derive and admit the version; `covers`, which checks it against the commits the release contains; and `publishedExactly`, which keeps every published release listed) each time a step runs; the edited `RegulaCore.Edition` is kernel-checked by the release pull request's checks and by CI's checks of the release commit, which pass before anything is published, and GitHub and `git` are trusted. |
| Understand declaration and execution auditing | [AxiomGate](Regula/Checker/AxiomGate.lean) | Operational checker implementation, qualified separately from the claimed proof surfaces. |
| Use the Lake lint driver | [Lint](Regula/Checker/Lint.lean) | `lint`: the `axiomGate` project audit behind `lake lint`, with proved exit classification. |
| Understand documentation auditing | [DocFenceAudit](Regula/Checker/DocFenceAudit.lean) | Checks recursively discovered Markdown fences as printed and, with `--verso`, every `lean` block of the Verso standard, which it builds and renders, refusing a rule ID in the rendered standard's prose that is not a link to its rule page. |
| Inspect the rule-reference site | [RegulaCore.Edition](RegulaCore/Edition.lean), [RegulaCore.Site](RegulaCore/Site.lean), [Guide](RegulaCore/Guide.lean), [site builder](Regula/Site/Artifact.lean), [guide](../docs/guides/website.md) | Claimed pure editions, version-matched help links, route policy, escaping, filters, diffs, release banners, link checks and page structure, and the typed rule explanations; the builder's evidence, Verso and filesystem steps stay operational. |
| Inspect cold-start verification | [RegulaVerification](RegulaVerification.lean), [its decision contracts](RegulaVerification/Decisions.lean) | Claimed argument-selection/recipe driver; process IO remains a reported boundary under the shell deadline. |
| Provision the shared local Mathlib | [RegulaProvision](RegulaProvision.lean), [its decision contracts](RegulaProvision/Decisions.lean) | Claimed toolchain-only setup run before the shell deadline; its receipt-admission, package-step and retention proofs do not authenticate Git, Lake, `cp`, `chmod` or locking effects. |
| Inspect proved qualification oracles | [RegulaQualification](RegulaQualification/Checks.lean), [qualification ledger](../docs/guides/proofs-and-boundaries.md#qualification-ledger) | Claimed pure observation predicates; separate Lean IO drivers do not authenticate the compiler or OS by proof. |
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
[standard](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#710-adopting-the-checker-in-another-project);
this does not make the operational checker a claimed proof surface.

For runnable consumers with their own configurations, use the
[standalone examples](../examples/README.md). For commands and review instructions,
use the [contributor guide](../docs/guides/contributing.md).

The [architecture](../docs/guides/architecture.md) fixes the registry, diagnostic, editor and site modules and how the rules cover the standard.

[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
