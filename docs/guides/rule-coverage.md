# Rule coverage and residual obligations

How the rules and the review obligations cover the standard; not a claim that every checklist
row passes. It accompanies [the architecture](linter-architecture.md). Normative meaning remains
in the standard (Verso source in `website/RegulaStandard/`); chapter 9 is the checklist source of
truth. A change to a requirement updates the affected rule descriptors and explanations together,
with semantic review.

See [native-linter.md](native-linter.md) for the delivered partial command feedback and complete module metadata observers.
The [project producer integration](engine-producers.md) also enforces RG5001–RG5003 on completed
project scopes; the [acceptance guide](policy-acceptance.md) owns claim-indexed mandatory
jobs and result composition.

## Exact selected diagnostic vocabulary

The sole registry defines twenty-two stable IDs for the initial product. Grouping related failures under one ID
does not discard their typed subreason, evidence or exact source. All apply as strict errors
when their condition is present. Missing/unsupported evidence has result status INCOMPLETE;
an established violation has FAIL. Neither can produce an accepted result. The existing checker
paths are under `lean/Regula/Checker/`; `Probe` and `Report` are in `lean/Regula/`.

| ID | Exact rejection predicate and domain | Implemented detector / adapter | Stage and supported product modes | Exceptions and evidence limits |
| --- | --- | --- | --- | --- |
| RG1001 | An owned `ConstantInfo.axiomInfo` is a project logical axiom, including unused/private/generated-looking declarations. | Policy.ruleForMember (equal to ruleFor)/project-axiom → RuleDiagnostics.declarationFinding. | Completed environment; project/fence, editor when current declaration record is complete. | Authenticated native teaching axioms are separately classified by RG1004, never conforming positives. No name-only exemption. |
| RG1002 | `sorryAx` belongs to an owned declaration's exact transitive axiom set. | collectAxioms; Policy.ruleForMember/hole → declarationFinding. | Environment; project/fence/editor. | No exception for theorem attributes, proof-valued definitions, instances, alternate syntax or imported holes. Lean's own `sorry` warning stops project and claimed-file audits at RG2003 first; RG1002 is reported there when no warning was emitted (for example an inherited hole). |
| RG1003 | A transitive axiom is outside the exact standard logical set and authenticated compiler classification. | Policy.labelOfMember/ruleForMember unknown-axiom → declarationFinding. | Environment; project/fence/editor. | Unknown classification fails; imported axioms are not exempt. |
| RG1004 | A positive declaration depends on compiler-trusting proof axioms (`native_decide`, `decide +native`, `bv_decide`, `bv_decide?`, `bv_check`, Lean's compiler axioms). | authorizedNativeAxioms/Frontend/compiler-trusting → declarationFinding. | Environment plus source attribution; project/fence; editor may defer authentication. | Teaching mode reports authenticated native proof separately, excluded from conforming positives. Final metadata alone cannot authorize origin. |
| RG1005 | Exact admissible transitive set exceeds the selected surface maximum. | Policy.permits/labelOfMember/ruleForMember label-exceeds-claim; #6 proofs; declarationFinding. | Environment and current configuration; project, claimed file, editor with a known local foundation. Not documentation fences (Standard-Logical or teaching). | Kernel-only empty; Choice-Free subset of propext/Quot.sound; Standard-Logical additionally choice. Classical erased proofs permitted under that maximum. |
| RG1006 | An owned declaration is unsafe or partial without the exact authenticated recursive-helper exception. | authorizedUnsafeRecHelpers/ruleForMember escape-hatch + fresh Frontend → declarationFinding. | Environment plus source; project/fence; incomplete editor evidence remains pending. | All §8.4 semantic/evaluator requirements jointly required. `partial_fixpoint` helpers are unsupported by that exception; no claim of logical unsoundness. |
| RG1007 | A closed `ExecutableContract f R` registration does not meet its exact supported root/evidence shape. | Probe contract inspection/ruleForMember executable-contract → declarationFinding; Lean checks R f. | Elaboration/environment; project/editor; proof admission required for accepted evidence. | Named computable safe nonpartial runtime roots, full domain in predicate; universe polymorphism supported; term-parameterized/partial-application registrations unsupported. Adequacy of R and caller linkage require review. |
| RG2001 | Declared elaboration environment cannot be loaded/identified or supported compiler assumptions cannot be established. | Workspace/Lake/Probe setup checks → ResultProtocol/contextFinding incomplete. | Project/setup; fresh, incremental and file audits. Documentation-audit setup failures print FAIL without a finding. | Exact Lean and dependency state required; setup failure is incomplete, not a source violation. Source identity remains an explicit trusted boundary. |
| RG2002 | Manifest/configuration violates schema 2 or cannot classify every root library/executable exactly once. | Manifest/Lake manifest-* target reconciliation → contextFinding. | Project/configuration; lint/build/fresh; editor must not guess omitted scope. | Nonempty library surface required by existing schema; executable-only unsupported. Unknown keys, duplicates, invalid mode, conflicts and missing targets fail. Exclusions do not waive imports. |
| RG2003 | Actual claimed source build fails or emits any warning, including local warningAsError=false. | Lake.buildChecked/Diagnostics/source compilation → ResultProtocol findings. | Elaboration/project; fresh, incremental, file (warnings only with `--claim`; source errors always). Not an editor rule; documentation-fence warnings are RG4002. | Source linter disabling can hide emission but cannot discharge semantic obligations. Wrong compiler/setup failures are incomplete. Preserve original compiler diagnostic as related evidence. |
| RG2004 | Lake-derived exact module/declaration inventory differs from attributed owned coverage, includes forbidden excluded/probe imports, or has unknown/omitted ownership. | Lake.surfaceInventory/Probe.ownedConstants/AxiomGate → contextFinding. | Whole project/environment; fresh/incremental only. The editor and single-file audits do not report it. | Include private/generated/unused and standalone roots. Library modules facet is cross-check, not replacement for configured array. No prefix/source-regex ownership. |
| RG2005 | Required owned logical admission, source freshness, or exact authentication evidence is missing, incomplete, unsupported or invalid. | Admission.validate/SourceAudit/Frontend typed admissionFailed → ResultProtocol RG2005. | Project/environment/source; fresh/fence; incremental admission does not establish fresh source. | Replay excludes owned entries from imported base; covers mutual inductives/dependencies. Imported unowned base remains trusted. Failed generated authentication cannot waive RG1001/1006. |
| RG2006 | A claimed library or executable's Lake-resolved build options (`leanOptions`, `weakLeanArgs`, `moreLeanArgs`) do not set `autoImplicit` and `relaxedAutoImplicit` to `false` and `linter.missingDocs` to `true`, set a `linter.*` option other than the three §6.7 exclusions to `false`, include a `-D name=value` extra `lean` argument that gives one of these options another value or sets such a linter to `false`, or, when the surface's loaded environment contains a `Mathlib` module, do not set `weak.linter.mathlibStandardSet` true with exactly those exclusions. One finding per target. | Lake.surfaceInventory reads `LeanLib.leanOptions`/`weakLeanArgs`/`leanArgs` (executables through their root module); proved `RegulaPolicy.Community.failures` (`failures_eq_nil_iff`); AxiomGate per-surface composition. | Completed environment plus configuration; project incremental/fresh. Not editor, file or documentation modes. | Source `set_option` commands and options on `lake`'s own command line are not read. A key's `weak.` prefix is read as the option it sets, and a string value as Lean parses it (`"false"` is `false`). Extra arguments other than `-D` (such as `--plugin` or `--setup`) are allowed and not read; every `-D` that `lean` reads starts at the first `D` of an argument beginning with a single `-`, and the rule reads every such candidate, so it can reject one that `lean` does not read as a `-D`; that correspondence with the `lean` command-line parser is assumed, read from Lean's `Lean.Shell` source and its getopt handling, neither proved nor observed. |
| RG3001 | Conservative execution closure has any unresolved path, unavailable retained code, unsupported history, or active replacement-only cycle. | Probe/Frontend histories; executionFailures execution-unresolved → executionFinding. | Completed project/environment plus compiler/source history; fresh/incremental and claimed file. The editor does not analyze execution. | Blocks report and checked modes. Ordinary recursion uses visited closure. Candidate edges are not claimed selected runtime edges. |
| RG3002 | In checked execution mode, a non-native-runtime boundary lacks exact admitted correspondence. | Probe.checkCorrespondenceProof; executionFailures execution-trusted-boundary → executionFinding. | Completed execution analysis; project fresh/incremental and file. | Origin-checked toolchain Init runtime remains trusted/reported. Report mode reports other trusted boundaries without rejecting them. Full dependent domain/universes, no extra theorem premises; external code is not proved by Lean equality. |
| RG4001 | Normative/example-tree fence structure or expected-error marker violates the exact §8.7 grammar. | Documentation scanner/Diagnostics → document-located contextFinding. | Documentation/project; docs CI; not native per-declaration editor lint. | All nested Markdown files in selected tree; malformed/orphan/double/misspelled markers and unclosed fences fail. Non-Lean sketches carry no elaboration claim. |
| RG4002 | A positive fence does not elaborate verbatim warning-free and complete its owned admission/foundation checks. | Documentation/SourceAudit/Admission → RG4002 + underlying findings. | DocumentationExample plus fresh claimed-import preparation. | No imports/wrappers inserted into checked source. Default Standard-Logical only; narrower/execution claims need explicit evidence. |
| RG4003 | A negative example lacks completed intended rejection matching its expected diagnostic within one effective-error message. | Diagnostics restricted matcher/worker completion; Website.validateBoundExample. | DocumentationExample. | Worker crash, timeout, wrong reason, info-only output and cross-message matching do not pass. Site lint violations may elaborate successfully before checker rejection. |
| RG4004 | A trusted-compiler teaching example fails warning-free elaboration or required authenticated compiler classification. | Documentation/SourceAudit/Frontend → RG4004 + typed underlying refusal. | DocumentationExample. | Never count teaching example as conforming positive. No blanket native-name whitelist. |
| RG5001 | A claimed module lacks module-doc metadata, its first command after the imports is not a module docstring, or its header repeats an import with the same modifiers. | Linter.Documentation.moduleObservation (Lean's `parseHeader`, one `topLevelCommandParserFn` parse of the first command, `HeaderSyntax.imports` without implicit `Init`) and proved `RegulaPolicy.ModuleHeader.failures` (`failures_eq_nil_iff`); AxiomGate project composition; #7 global jobs; self-audit worker. | Module/environment plus the bound module source; project and editor (when the module completed without errors). | Position and imports only: no headings, sections or content are imposed, and import minimality is not checked. A first command that does not parse is not a module docstring. |
| RG5002 | A public declaration explicitly registered as evidence for a material normative claim lacks a docstring. | regula_material/findDocString?; AxiomGate project composition; #7 global jobs. Core missingDocs broader. | Elaboration/environment; project/editor. | Checks registered declarations only; the §6.7 requirement that every public definition has a docstring is `linter.missingDocs` composed with RG2003, not this rule. Registration completeness and meaning remain semantic review; no name heuristic. |
| RG5003 | A public declaration explicitly registered as evidence for a material normative claim has a docstring without a nonempty labelled Intent section: a Markdown ATX heading whose text is exactly `Intent` followed, before the next heading of equal or higher level, by a non-heading line with non-whitespace text. Subsection text counts. | regula_material/findDocString?; proved `RegulaPolicy.materialDocumentationFailure` (`materialDocumentationFailure_eq_missingIntent_iff`, `hasIntentSection_iff`); AxiomGate project composition; #7 global jobs. | Elaboration/environment; project/editor. | A missing docstring is RG5002 only; the two rules partition failures. Presence and linkage only: no intent detector, length threshold or similarity check. Adequacy of the intent and agreement with the explanation and declaration remain R-INTENT review. Fenced code is not tracked. |

The engine must preserve every existing advertised failure condition, including warning and
worker completion handling, while grouping its presentation. A new or unclassified internal
failure is INCOMPLETE and blocks the affected result; it must not fall through an exhaustive
rule switch as success. Stable IDs do not erase legacy subreason distinctions needed by
qualification. #12/#13 must update positive controls and intended-reason mutations for the actual
modified implementation and invocation, retaining unchanged controls and evidence.

## Source-owned examples

The [rule-example corpus](rule-examples.md) supplies actual source/configuration pairs and
registry-backed diagnostic expectations. RG2001, RG2005 and RG3001 intentionally demonstrate
INCOMPLETE analysis using separately labelled diagnostic records. Their diagnostic production
must complete; these records do not satisfy an accepted positive or rejection expectation.
Corrections retain the intended claim and require their applicable completed positive checks.
The four accepted-example kinds remain unchanged. Qualification is scoped operational evidence,
not proof of universal detector correctness or complete product acceptance.

## Clause-to-obligation reconciliation

This accounts for normative requirements and recommendations beyond a superficial keyword scan:

| Normative clauses | Checklist obligations / treatment |
| --- | --- |
| README scope, keywords and example convention; chapter 0 | SCOPE-01–05, THEOREM-01/04/06/09, FOUND-01–05, DOC-03–05. Kernel truth, adequacy and non-vacuity remain distinct. |
| 1.1–1.2 | TYPE-01/02/06, THEOREM-01–05/07, FOUND-01/02, COMP-02. Intrinsic and justified raw-boundary alternatives both remain valid. |
| 1.3–1.6 | SCOPE-02–05, TYPE-02/05, THEOREM-01/07/08, DOC-01/02, DECL-01–04, COMP-01–04. Explicit constrained parameters fall under TYPE-01/02 and THEOREM-01/03. |
| 2.1–2.4 | TYPE-01–06, SCOPE-03, THEOREM-03/07/08. Tags, totalized domains, assumptions, reuse and refinement have distinct obligations. |
| 3.1–3.5 | THEOREM-01–06/10, TYPE-03/05, FOUND-01–05, DOC-01/02. Proof readability/economy recommendations are review guidance, not mandatory tactic or size rules. |
| 3.6–3.8 | COMP-01–04, SCOPE-03/05, THEOREM-01/03/05/07, BUILD-02/03. Metaprogram output validity is not producer correctness. |
| 3.9–3.10 | THEOREM-04/08/09, SCOPE-02/03, DOC-02, FOUND-01/02. Conditional/open claims are not rejected for lacking an antecedent witness. |
| 4.1–4.4 | TYPE-01–05, THEOREM-01/02/07/08, SCOPE-02/03. Numeric and mathematical-interface adequacy are specified-domain obligations. |
| 4.5 | FOUND-01–05, BUILD-02, COMP-01. Report exact least label separately from selected maximum and executable witnesses. |
| 5.1–5.4 | DOC-01/02, THEOREM-01, SCOPE-02. Presence checks are RG5001/5002/5003, and RG5001 also checks module-docstring placement; prose fidelity, intent adequacy and readability remain review. |
| 6.1–6.7 | DECL-01/04 (acyclic imports and actual elaboration), DOC-01, TYPE-06, SCOPE-04. Naming, import minimality/order and section layout are recommendations, not new rejection rules. The §6.7 community linters (`linter.missingDocs`; with Mathlib, `weak.linter.mathlibStandardSet` with its three Mathlib-repository linters off) are required configuration: RG2003 rejects their warnings, RG2006 checks their Lake enablement and rejects a target-wide linter disable, and every declaration-scoped disable (§6.2) is DECL-01 review. RG5001 checks module-docstring placement (§5.3) and repeated imports (§6.4). Batteries' environment linters are recommended; no community linter discharges a row. |
| 7.1–7.17 | THEOREM-05/10, COMP-01–04, SCOPE-02/03, TYPE-01/03 for changed semantics. All workload-conditioned performance practices remain guidance, not a new conformance checklist or required benchmarks. |
| 8.1–8.5 | DECL-01–04, FOUND-01–05, THEOREM-01/07, DOGFOOD-05. Exact environment, ownership, admission, attribution and contract scope preserved. |
| 8.6–8.7 | COMP-01–04, DOC-03–05. Conservative compiler closure and exact document-worker protocol retained. |
| 8.8–8.9 | MUT-01–05; qualification and optional serialized graph have conditional applicability. |
| 8.10–8.12 | DOGFOOD-01–05, BUILD-01–04, DECL-01–04. Adoption mode and actual enabled invocation determine supported enforcement. |
| 9 and critical-violations | Checklist/result rule and triage, no independent relaxed compliance level. |

## Residual review obligations

The review obligations that no mechanical result discharges are the checker's `Residual` type
in [`RegulaCore.Account`](../../lean/RegulaCore/Account.lean), each with its one description
(`Residual.description`): `R-INTENT`, `R-INVARIANT`, `R-LAWS`, `R-BOUNDARY`, `R-NONVACUITY`,
`R-DOC`, `R-COST`, `R-QUALIFY` and `R-GRAPH`. The site's
[enforcement page](https://rbeauchamp.github.io/regula/dev/enforcement/) lists them all, each
rule page and `lake exe regula explain` the ones its rule leaves open. Every accepted result
lists them as unresolved where applicable (`R-GRAPH` only for a serialized-graph claim), and each
RG1007 contract it reports carries `R-INTENT` and `R-INVARIANT` for the adequacy of its
requirement and its caller coverage. A listed identifier is an open obligation, not a completed
review. They are required where applicable, never waived: no heuristic detector replaces one,
and automation would first need a precise claim language, adequate registration and checked
implementation linkage.

## Checklist rows

The site's [checklist coverage](https://rbeauchamp.github.io/regula/dev/coverage/) page lists
every module 9 row with the rules whose explanation lists it and the obligations those rules
leave open. It is generated from each rule's `checklist` and `residuals` in
[`RegulaCore.Guide`](../../lean/RegulaCore/Guide.lean), inverted by construction
(`Regula.Site.mem_rulesOfRow`), so it cannot disagree with the rule pages; a row no rule lists
is semantic review only. `./scripts/verify.sh docs` renders the standard and requires its
checklist rows to be exactly `Regula.checklistRows`, each once and in order
(`Regula.Site.rowsMismatch_eq_none_iff`), and every row a rule lists is one of them
(`guide_checklist_listed`). Which rows a rule lists is reviewed with the rule, against each
row's required verification on the checklist; no row passes on a presence check or a checker
PASS alone.
