# Architecture

This guide tells how Regula is built. One typed rule registry drives the checker, the offline `regula` command and the rule-reference site. Thus each surface shows the same rule. The [standard](https://rbeauchamp.github.io/regula/dev/standard/) owns normative meaning, and this guide owns the implementation contract. The [proofs and boundaries](proofs-and-boundaries.md) tell what each part proves, observes or trusts.

## Packages and libraries

The root `regula` package is the package that adopters require. It requires nothing beyond the Lean toolchain, and it imports no Mathlib. These are its libraries (`lakefile.lean`, `foundation_manifest.json`):

| Library | Role | Claim |
| --- | --- | --- |
| `RegulaInterface` | The checker interfaces that adopters import: executable contracts and decision kinds (`Regula.Contract`), decision registration (`Regula.Decision`) and assumptions. | Claimed, Standard-Logical |
| `RegulaPolicy` | Pure policy types and decisions that the registry, the manifest reader and the option allowlist read. | Claimed, Standard-Logical |
| `RegulaCore` | The rule registry, the guidance and setup decisions of the `regula` command, the decisions of the site and of the Markdown checks, and the shared filesystem constructor. | Claimed, Standard-Logical |
| `RegulaQualification` | The assertions that the programs of the site evaluate (`RegulaQualification.Checks`). | Claimed, Standard-Logical |
| `RegulaVerification`, `RegulaProvision` | The acceptance driver and the dependency provisioning, the modules `RegulaVerification.Driver` and `RegulaProvision.Driver`, which import only the toolchain and declare no `main`. The files `lean/RegulaVerification.lean` and `lean/RegulaProvision.lean`, in no target, launch them. A `Decisions` module of each library registers the kinds of its decisions. | Claimed, Standard-Logical |
| `AuditApp`, with the executable root `Main` | A complete application, with contracts that are proved about the definitions that its executable runs. | Claimed, Standard-Logical |
| `RegulaChecker` | The checker: the closed input and the rule functions that the specification proves, the manifest reader, the loader's reads of Lean and the shell. | Claimed, Standard-Logical |
| `Regula` | What the checker receives from outside its claim: Lake's load of the workspace (`Regula.Workspace`, because Lake's own axioms are outside each profile) and the root of the `lint` executable (`Regula.LintMain`, which holds the one `unsafe` call). Also the `regula` command, the site builder, the local gate, the release checks and the registry checks. | Excluded |

The `regula_audit` package in [`audit/`](../../audit/lakefile.lean) holds the `Audit` library of the examples of the standard. It requires the root package by its path, as an adopter does. The Verso package in [`website/`](../../website/) renders the standard and the rule reference. The `regula_markdown` package in [`markdown/`](../../markdown/lakefile.toml) reads the tracked Markdown documents with md4c for the documentation step.

The `regula_specification` package in [`specification/`](../../specification/lakefile.toml) holds the formal statements of the [specification of the smaller Regula](../../specification/README.md). It requires lean-intent and the root package. The first acceptance step builds it in its copy, with warnings as errors.

The executables are `lint` (the checker, which `lake lint` runs), `regula` (project setup and offline guidance), `site` (the rule reference) and `auditApp`.

## The checker

The checker reads one closed input and gives one verdict: pass, fail or incomplete. The [proofs and boundaries](proofs-and-boundaries.md#the-checker-of-a-finished-build) give the parts of the input and the interface of each part. These are the modules of the checker:

| Module | Role |
| --- | --- |
| `Regula.Input` | The types of the closed input, and the admission that refuses an input without the closed form. |
| `Regula.Load` | The loader, which fills the input from the load of the workspace by Lake and from the finished build. |
| `Regula.Rules` | The kept rules as functions over the input, and the verdict of a run. |
| `Regula.Shell` | The report of a run and its exit code. |
| `Regula.Effects` | The build-time check that the compiled code of a program starts no process and writes and removes no file (`Regula.Effects.check`). |
| `Regula.LintMain` | The root of the `lint` executable. |

Lean's own tools decide [RG2003] and [RG2005]: `lake build --wfail` and `lake check`. No check decides the documentation rules [RG4001] to [RG5003]. They are retired to written guidance, and the lifecycle of each in the registry records the retirement.

## The rule registry

`RuleId` ([`RegulaCore.RuleId`](../../lean/RegulaCore/RuleId.lean)) is a closed inductive type with 24 constructors. Its executed definitions are `spelling`, `parse?`, `all` and `route`. The function `descriptor` of [`RegulaCore.Rule`](../../lean/RegulaCore/Rule.lean) gives each rule its descriptor, and its match is exhaustive. Thus no rule can be missing from the registry. A descriptor has the title, the category, the scope, the normative clauses, the guidance for agents and the example pair of the rule. The `regula` command and the site print the registry.

## Rule reference site

The site builder (`lake exe site`) generates Verso source from the registry and `RegulaCore.Guide`,
with the example pair of each rule, renders it with the pinned Verso
package, and publishes the standard beside the rule pages. The [website guide](website.md) owns
its sources, guarantees, editions, help links and publication.

## Coverage of the standard

Every normative requirement has a disposition: a rule, proof evidence the standard requires, or
semantic review. The rules and review obligations cover the modules as follows; a row list means
the rows whose review or mechanical check the clauses feed, not that those rows pass.

| Normative clauses | Checklist obligations and treatment |
| --- | --- |
| Introduction (scope, keywords, example convention); module 0 | SCOPE-01–05, THEOREM-01/04/06/09, FOUND-01–05, DOC-03–05. Kernel truth, adequacy and non-vacuity remain distinct. |
| 1.1–1.2 | TYPE-01/02/06, THEOREM-01–05/07, FOUND-01/02, COMP-02. Intrinsic and justified raw-boundary alternatives both remain valid. |
| 1.3–1.6 | SCOPE-02–05, TYPE-02/05, THEOREM-01/07/08, DOC-01/02, DECL-01–04, COMP-01–04. Explicit constrained parameters fall under TYPE-01/02 and THEOREM-01/03. |
| 2.1–2.4 | TYPE-01–06, SCOPE-03, THEOREM-03/07/08. Tags, totalized domains, assumptions, reuse and refinement have distinct obligations. |
| 3.1–3.5 | THEOREM-01–06/10, TYPE-03/05, FOUND-01–05, DOC-01/02. Proof readability and economy recommendations are review guidance, not mandatory tactic or size rules. |
| 3.6–3.8 | COMP-01–04, SCOPE-03/05, THEOREM-01/03/05/07, BUILD-02/03. Metaprogram output validity is not producer correctness; §3.6's contract obligation includes optimizations, which meet the same contract ([performance notes](performance-notes.md) are guidance). |
| 3.9–3.10 | THEOREM-04/08/09, SCOPE-02/03, DOC-02, FOUND-01/02. Conditional and open claims are not rejected for lacking an antecedent witness. |
| 4.1–4.4 | TYPE-01–05, THEOREM-01/02/07/08, SCOPE-02/03. Numeric and mathematical-interface adequacy are specified-domain obligations. |
| 4.5 | FOUND-01–05, BUILD-02, COMP-01. The exact least label is reported separately from the selected maximum and from executable witnesses. |
| 5.1–5.4 | DOC-01/02, THEOREM-01, SCOPE-02. [RG5001] to [RG5003] are retired to written guidance. Thus review checks the presence and placement of docstrings, prose fidelity, intent adequacy and readability. |
| 6.1–6.7 | DECL-01/04 (acyclic imports and actual elaboration), DOC-01, TYPE-06, SCOPE-04. Naming, import minimality and layout are recommendations. The §6.7 community-linter settings are written guidance that review checks. [RG2006] checks the target options under §6.2, without requiring community linters to be enabled. [RG2003] rejects emitted warnings. Review checks every declaration-scoped disable (§6.2). Module-docstring placement (§5.3) and repeated imports (§6.4) are the written guidance of [RG5001], which review checks. Batteries' environment linters are recommended. No community linter discharges a row. |
| 7.1–7.5 | DECL-01–04, FOUND-01–05, THEOREM-01/07. Exact environment, ownership, admission, attribution and contract scope. |
| 7.6–7.7 | COMP-01–04, DOC-03–05. Conservative compiler closure, and the fence protocol of documentation examples, which review checks. |
| 7.8–7.9 | MUT-01–05; checker qualification and the optional serialized graph are conditional. |
| 7.10–7.11 | BUILD-01–04, DECL-01–04. The adoption mode and the actual enabled invocation determine supported enforcement. |
| 8 and Critical Violations | The checklist, the result rule and triage; no relaxed compliance level. |

The review obligations no mechanical result discharges are the checker's `Residual` type in
[`RegulaCore.Residual`](../../lean/RegulaCore/Residual.lean), each with one description
(`Residual.description`): `R-INTENT`, `R-INVARIANT`, `R-LAWS`, `R-BOUNDARY`, `R-NONVACUITY`,
`R-DOC`, `R-COST`, `R-QUALIFY` and `R-GRAPH`. The site's
[enforcement page](https://rbeauchamp.github.io/regula/dev/enforcement/) defines them, each rule
page links the ones its rule leaves open, and `lake exe regula explain` prints them. A pass of
the checker leaves each of them open. No heuristic detector replaces one.

The site's [checklist coverage](https://rbeauchamp.github.io/regula/dev/coverage/) page lists
every checklist row with the rules whose explanation lists it and the obligations it carries,
generated from each rule's `checklist` and each obligation's `Residual.rows` and inverted by
construction (`Regula.Site.mem_rulesOfRow`, `mem_residualsOfRow`). A row no rule lists is
semantic review only. Every obligation carries at least one row, each a checklist row
(`residual_rows_listed`), and every checklist row carries at least one obligation
(`residualsOfRow_ne_nil`), both kernel-checked. Which rows a rule lists and which an obligation
carries are reviewed with the rule or obligation, against each row's required verification; the
kernel checks cover only membership and coverage, and no row passes on a presence check or a
checker PASS alone.

## Credits

Lean's authors supply the linter, elaboration, message and Lake APIs; Verso's authors supply
rendering. Design influences (including con-leche and Microsoft CA1416) and the license notices
of adapted code are credited in [design influences](design-influences.md). No external tool
defines Lean policy or permits suppressing mandatory requirements.

[RG1001]: https://rbeauchamp.github.io/regula/dev/rules/RG1001/
[RG1003]: https://rbeauchamp.github.io/regula/dev/rules/RG1003/
[RG1005]: https://rbeauchamp.github.io/regula/dev/rules/RG1005/
[RG1007]: https://rbeauchamp.github.io/regula/dev/rules/RG1007/
[RG1008]: https://rbeauchamp.github.io/regula/dev/rules/RG1008/
[RG1009]: https://rbeauchamp.github.io/regula/dev/rules/RG1009/
[RG2001]: https://rbeauchamp.github.io/regula/dev/rules/RG2001/
[RG2002]: https://rbeauchamp.github.io/regula/dev/rules/RG2002/
[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/
[RG2004]: https://rbeauchamp.github.io/regula/dev/rules/RG2004/
[RG2005]: https://rbeauchamp.github.io/regula/dev/rules/RG2005/
[RG2006]: https://rbeauchamp.github.io/regula/dev/rules/RG2006/
[RG3001]: https://rbeauchamp.github.io/regula/dev/rules/RG3001/
[RG3002]: https://rbeauchamp.github.io/regula/dev/rules/RG3002/
[RG4001]: https://rbeauchamp.github.io/regula/dev/rules/RG4001/
[RG5001]: https://rbeauchamp.github.io/regula/dev/rules/RG5001/
[RG5002]: https://rbeauchamp.github.io/regula/dev/rules/RG5002/
[RG5003]: https://rbeauchamp.github.io/regula/dev/rules/RG5003/
