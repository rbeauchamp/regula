# Lean sources

These modules implement the contracts and checkers and supply checked Core examples for
the [standard](https://rbeauchamp.github.io/regula/dev/standard/). They form the `regula` package that
projects require, whose source directory is `lean/`; it requires no package beyond the Lean
toolchain. Imports retain their Lean module names, such as `AuditApp.Limiter` and
`Regula.Contract`. The standard's example library, such as `Audit.Research`, is the separate
`regula_audit` package in [`../audit/`](../audit/lakefile.lean), which requires this package by
relative path and nothing else.

## Choose a starting point

| Purpose | Start here | Boundary |
| --- | --- | --- |
| Use the proof-bearing contract interface | [Regula.Contract](Regula/Contract.lean) | Public interface tying evidence to the named executable definition, with the decision kinds (`Decides`, `DecidesSoundly`, `DecidesCompletely`) that state which directions of a checker are proved, the law `DecisionEquivalence` that states the two directions and no outcome, and the erasures `Regula.Dependent.isSome` and `isOk` for a result type that depends on the input. |
| Register a decision function | [Regula.Decision](Regula/Decision.lean) | Public type `RegisteredDecision`. Its declarations select the [RG1008] obligation: a decision contract in the function's inventory, or a `Decidable` result type. It does not find functions that are not registered. |
| Declare an assumption about an external system | [Regula.Assumption](Regula/Assumption.lean), [RegulaCore.Filesystem](RegulaCore/Filesystem.lean), [guide](../docs/guides/proofs-and-boundaries.md#external-systems) | Public type `Assumed`. Its declarations give an assumption's system and sources. The model of the file system, its assumptions with their sources and its observer `Regula.Filesystem`. Regula trusts the assumptions and does not prove them. |
| Inspect mathematical/specification examples | [Audit](../audit/Audit.lean) | Claimed abstract-specification surface of the `audit/` package, which imports only Lean's core libraries; representative checks of the standard's claims. |
| Inspect the verified application | [Main](Main.lean), [AuditApp](AuditApp.lean) | Claimed limiter application; proofs concern its actual definitions and its IO boundary stays trusted. |
| Use typed policy data | [RegulaPolicy.Domain](RegulaPolicy/Domain.lean), [RegulaPolicy.Community](RegulaPolicy/Community.lean) | Separate claimed pure library: the types that the registry and the manifest reader use, and the options that `regula init` writes. [RegulaCore.Allowlist](RegulaCore/Allowlist.lean) holds the option allowlist of [RG2006]. |
| Use the checker | [Regula.Input](Regula/Input.lean), [Regula.Reach](Regula/Reach.lean), [Regula.Rules](Regula/Rules.lean), [Regula.Load](Regula/Load.lean), [Regula.Workspace](Regula/Workspace.lean), [Regula.Shell](Regula/Shell.lean) | The closed input, the search over it, the rule functions, the loader and the shell of `lake lint`. The [specification](../specification/README.md) proves the rule functions and the verdict against their statements. |
| Read or change the agent-facing rule guidance | [rule registry](RegulaCore/Rule.lean), [Feedback](RegulaCore/Feedback.lean), [Guidance](RegulaCore/Guidance.lean), [regula command](Regula/Cli/Main.lean) | Claimed requirement, rationale, remedy, rewrites and example pair of every rule; the proved run order and once-per-rule finding text, which no program of this version prints; the offline `regula` explain, index, agent briefing and skill with a proved parser. The printing root stays operational. |
| Set up an adopting project | [RegulaCore.Setup](RegulaCore/Setup.lean), [Regula.Cli.Setup](Regula/Cli/Setup.lean) | Claimed setup decision of `regula init` and `regula doctor` (lint driver, options, library globs, manifest, agent guidance, toolchain, modules outside every library) with proved idempotence (`plan_idempotent`) and no added option beside a `-D` that sets it (`added_unargued`); observing the project through Lake, editing the lakefile and writing files stay operational, confirmed by observing again. |
| Cut a release | [Release](Regula/Release.lean), [workflow](../.github/workflows/release.yml), [procedure](../docs/guides/contributing.md#release) | Operational release steps (the Release workflow and the `candidate`, `release-verify`, `release-site` and `publish` jobs of CI on `main`) run with the toolchain alone, and the kernel checks the proved release decisions (`tagAction`; `nextVersion` and `admits`, which derive and admit the version; `covers`, which checks it against the commits the release contains; `publishedExactly`, which keeps every published release listed; and `branchAction`, which refuses to create the branch of a release pull request while one for the version is observed open) each time a step runs; the edited `RegulaCore.Edition` is kernel-checked by the local gate on the release pull request and by CI's checks of the release commit, which pass before anything is published, and GitHub and `git` are trusted. |
| Inspect the rule-reference site | [RegulaCore.Edition](RegulaCore/Edition.lean), [RegulaCore.Site](RegulaCore/Site.lean), [Guide](RegulaCore/Guide.lean), [site builder](Regula/Site/Artifact.lean), [guide](../docs/guides/website.md) | Claimed pure editions, version-matched help links, route policy, escaping, filters, diffs, release banners, link checks and page structure, and the typed rule explanations; the Verso and filesystem steps of the builder stay operational. |
| Examine the checks of Markdown documents | [RegulaCore.Markdown](RegulaCore/Markdown.lean), [RegulaCore.Vocabulary](RegulaCore/Vocabulary.lean), [RegulaCore.ControlledText](RegulaCore/ControlledText.lean), [RegulaCore.ControlledProse](RegulaCore/ControlledProse.lean), [RegulaCore.ProseBaseline](RegulaCore/ProseBaseline.lean), [reader and executable](../markdown/MarkdownMain.lean), [writing rules](../docs/guides/writing.md) | Claimed decisions of the rule-ID check, of the checks C1 to C9 and of the baseline checks B1 and B2. `RegulaCore.Markdown` also has the claimed decisions of the checks of the links and the opening of the root `README.md`. `RegulaCore.ControlledText` has the definitions of a word and of a sentence. The md4c reader is in the `markdown/` package and has no theorem. The controls are in `Fixtures/ControlledProse`. |
| Inspect cold-start verification | [RegulaVerification](RegulaVerification/Driver.lean), [its launcher](RegulaVerification.lean), [its decision contracts](RegulaVerification/Decisions.lean) | Claimed argument-selection/recipe driver; process IO remains a reported boundary under the shell deadline. |
| Provision dependencies | [RegulaProvision](RegulaProvision/Driver.lean), [its launcher](RegulaProvision.lean) | Claimed toolchain-only setup run before the shell deadline, which acquires the specification package's lean-intent, and the website's Verso when asked. Git, Lake and filesystem effects stay trusted. |
| Inspect the proved assertions of the site | [RegulaQualification](RegulaQualification/Checks.lean) | Claimed pure assertions that the programs of the site evaluate. |

## Follow the sources

Module docstrings describe purpose and assumptions. The
[Lake configuration](../lakefile.lean) defines module/target discovery, and the
[surface manifest](../foundation_manifest.json) defines claims and exclusions; the
`audit/` package has its own [configuration](../audit/lakefile.lean) and
[surface manifest](../audit/foundation_manifest.json).
Those files, not this navigation table or folder names, own the inventory.

The interfaces, such as `ExecutableContract`, are the claimed `RegulaInterface` library. A claimed
surface may import them as described in the
[standard](https://rbeauchamp.github.io/regula/dev/standard/7-tooling-and-machine-audit/#78-adopting-the-checker-in-another-project);
this does not make the operational checker a claimed proof surface.

For runnable consumers with their own configurations, use the
[standalone examples](../examples/README.md). For commands and review instructions,
use the [contributor guide](../docs/guides/contributing.md).

The [architecture](../docs/guides/architecture.md) gives the registry, the checker and the site modules, and how the rules cover the standard.

[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
[RG2006]: https://rbeauchamp.github.io/regula/dev/rules/RG2006/
