# Initial rule coverage and residual obligations

This is the complete PRODUCT-01 delivery inventory, not a claim that every rule is already
implemented or every checklist row passes. It accompanies [the architecture](linter-architecture.md).
Normative meaning remains in the standard (Verso source in `website/RegulaStandard/`); chapter 9
is the checklist source of truth.
The map was read against all numbered chapters, the standard README and critical-violations list
at baseline `f943f41c50876b25c8c5c2285e6ae4315645521e`. Changes to those requirements must update
this map and affected typed descriptors together, with semantic review.

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
| RG1004 | A positive declaration depends on compiler-trusting proof axioms. | authorizedNativeAxioms/Frontend/compiler-trusting → declarationFinding. | Environment plus source attribution; project/fence; editor may defer authentication. | Teaching mode reports authenticated native proof separately, excluded from conforming positives. Final metadata alone cannot authorize origin. |
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
| RG5003 | A public declaration explicitly registered as evidence for a material normative claim has a docstring without a nonempty labelled Intent section: a Markdown ATX heading whose text is exactly `Intent` followed, before the next heading of equal or higher level, by a non-heading line with non-whitespace text. Subsection text counts. | regula_material/findDocString?; proved `RegulaPolicy.materialDocumentationFailure` (`materialDocumentationFailure_eq_missingIntent_iff`, `hasIntentSection_iff`); AxiomGate project composition; #7 global jobs. | Elaboration/environment; project/editor. | A missing docstring is RG5002 only; the two rules partition failures. Presence and linkage only: no intent detector, length threshold or similarity check (the opt-in [intent screen](intent-screening.md) is separate and never a rule). Adequacy of the intent and agreement with the explanation and declaration remain R-INTENT review. Fenced code is not tracked. |

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
not proof of universal detector correctness or completed Project 8 acceptance.

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

## Residual semantic and research accounts

These obligations are required where applicable; they are not waived or declared impossible.
The initial engine does not claim to infer arbitrary natural-language intent. Future automation
must supply a precise claim language, adequate registration and checked implementation linkage
before it can replace the corresponding review. Responsible final reconciliation is #10, with
mechanical selectors/adapters in #13 and accepted-evidence construction in #7.

- **R-INTENT:** read back each material elaborated proposition, and its §5.2 explanation, against
  the written intent statement in the declaration's Intent section (RG5003 checks its presence);
  preserve quantifier order, hypotheses, totalized domain, existence/construction,
  conditional/open status and external limits. The requirement owner still confirms that the
  intent states what is needed; no proof or presence check discharges that validation. No closed
  syntactic detector for arbitrary prose is selected. A future claim DSL needs adequacy research,
  not a regex heuristic.
  No default-on heuristic intent detector becomes a diagnostic, let alone a hard error. The one
  amendment (#58) is the separate, opt-in
  [`intentScreen`](intent-screening.md). It is not a registry rule and never runs in
  acceptance. It is a separate executable rather than an in-elaboration rule because it calls a
  paid network service with source text; inside the linter it would bring network, cost and
  nondeterminism into every build and editor session. It reports probabilities; its guide owns
  the measured calibration and which judgments met the pre-registered criteria. The user
  chooses its thresholds and their severity mapping, in the rule-severity vocabulary (`error`,
  `warning`, `information`; rule severities themselves are fixed registry defaults, not user
  configuration). Its findings have the linter's diagnostic shape with a per-judgment
  `intentScreen/<judgment>` identifier, not a rule ID. Its results form their own `screened`
  evidence class. A low probability can raise a finding at the configured severity. A high
  probability never makes the claim checked and never completes this review. An intent clause
  can be discharged by a theorem, within the Standard-Logical foundation, proving that the
  claim implies the clause's formal statement. Lean's kernel re-checks that implication's own
  proof term; its guide states the trusted dependency boundary. Only that
  formal statement's match with the English clause is judged.
- **R-INVARIANT:** identify intended admitted-value, transition, frame, reachability and composition
  relations, inspect all admission/write/caller paths, then require exact proof-bearing interfaces
  or theorems. Existing Lean checks evidence once the obligation is explicit; they cannot infer
  that no intended write path/specification was omitted. #4/#7 encode the actual checker contracts.
- **R-LAWS:** compare selected canonical structures and actual instances/lawful mixins with the
  intended algebra/order and justify custom definitions. Missing required fields fail Lean;
  intentionally choosing an operations-only interface is not itself a detectable semantic defect.
- **R-BOUNDARY:** inspect producer/client module modes, exported constructors/recursors/projections,
  coercions, equations and actual callers. Positive/negative importing clients qualify exact
  exclusions, not universal privacy or external confidentiality.
- **R-NONVACUITY:** require a witness only at the strength actually claimed (inhabitance, joint
  satisfiability, reachability); conditional or deliberately empty claims need no unrelated witness.
  Detecting arbitrary inconsistency/adequacy is not a selected general linter capability.
- **R-DOC:** verify semantic completeness of material-claim registration and fidelity of module
  docs/docstrings to the actual definitions and requirements; existence/length is insufficient.
- **R-COST:** identify cost domain and exact mathematical argument or bounded observation, preserve
  semantic/effect order. No timing, proof count or sample is universal correctness evidence.
- **R-QUALIFY:** maintain claim-scoped positive controls, intended-reason mutations, isolated restored
  controls and exact invocation/toolchain evidence. Unrun campaigns remain unrun; universal pure
  policy proofs in #6 complement rather than replace collector/integration qualification.
- **R-GRAPH:** the optional serialized-graph claim is `freshChecker` (§8.9). The con-leche export
  route from #8/#9 ended in a [no-go](con-leche-research.md). Absence of either claim does
  not block core delivery. A claimed graph still requires every exact selected root covered.

The report account's `Residual` type in
[`RegulaCore.Account`](../../lean/RegulaCore/Account.lean) has exactly these nine
identifiers. Every accepted result lists them as unresolved where applicable (R-GRAPH only
for a serialized-graph claim), and each RG1007 contract it reports carries R-INTENT and
R-INVARIANT for the adequacy of its requirement and its caller coverage. A listed identifier
is an open obligation, not a completed review. Change this list and that type together.

## Complete chapter 9 row map

Each row links its requirement on the published checklist, the only source of its required result
and verification; the clause table above supplies its normative domain. This map adds only each
row's mechanical contribution and residual account. No row can be discharged solely by a
presence check or a checker PASS.

| Row | Mechanical contribution | Residual obligation |
| --- | --- | --- |
| [`SCOPE-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#SCOPE-01) | None; technical scope review | R-INTENT |
| [`SCOPE-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#SCOPE-02) | RG1007/2005 for named formal evidence only | R-INTENT |
| [`SCOPE-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#SCOPE-03) | RG1007/3001/3002 for registered correspondence | R-INVARIANT, R-INTENT |
| [`SCOPE-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#SCOPE-04) | None; rationale review | R-INTENT |
| [`SCOPE-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#SCOPE-05) | RG2002/2004/3001/3002 | R-INTENT, R-INVARIANT |
| [`TYPE-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#TYPE-01) | Lean type/contract checking, RG1007/2005 | R-INVARIANT |
| [`TYPE-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#TYPE-02) | Lean type/constructor checking | R-INTENT |
| [`TYPE-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#TYPE-03) | Lean domain/proof checking | R-INTENT |
| [`TYPE-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#TYPE-04) | RG1001/1002/1003 | R-INTENT |
| [`TYPE-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#TYPE-05) | Lean law fields and instance synthesis | R-LAWS |
| [`TYPE-06`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#TYPE-06) | Lean separate importing-client checks | R-BOUNDARY |
| [`THEOREM-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-01) | RG1001–1007/2005 and exact Lean evidence | R-INTENT, R-INVARIANT |
| [`THEOREM-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-02) | Lean required law fields/mixin synthesis | R-LAWS |
| [`THEOREM-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-03) | RG1007/2005 and actual boundary proofs | R-INVARIANT |
| [`THEOREM-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-04) | Lean exact witness/refutation proofs | R-NONVACUITY |
| [`THEOREM-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-05) | RG1006/3001/3002; Lean recursion checking | R-COST, R-INTENT |
| [`THEOREM-06`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-06) | RG1002/1004 reject holes/native proofs | R-INTENT, R-QUALIFY |
| [`THEOREM-07`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-07) | RG1007/2005 exact registered predicates | R-INVARIANT |
| [`THEOREM-08`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-08) | Lean checked simulation/transfer proofs | R-INVARIANT, R-INTENT |
| [`THEOREM-09`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-09) | RG1001–1003; Lean statement/proof distinction | R-INTENT, R-NONVACUITY |
| [`THEOREM-10`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#THEOREM-10) | RG1004/1005 actual dependencies | R-COST |
| [`FOUND-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#FOUND-01) | RG1001 | R-INTENT only for assumption presentation |
| [`FOUND-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#FOUND-02) | RG1002 | R-QUALIFY |
| [`FOUND-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#FOUND-03) | RG1003/1004/1005 | R-QUALIFY |
| [`FOUND-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#FOUND-04) | RG1005 | R-QUALIFY |
| [`FOUND-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#FOUND-05) | RG1004/2005 | R-QUALIFY |
| [`DECL-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DECL-01) | RG2001–2006; RG5001 repeated imports (§6.4) | R-QUALIFY; source/dependency identity boundary; review of source `set_option` commands and of every source-local linter disable (§6.2), which the audit cannot see |
| [`DECL-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DECL-02) | RG2004/2005 | R-QUALIFY |
| [`DECL-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DECL-03) | RG2004/2005 plus RG1001/1004/1006 | R-QUALIFY |
| [`DECL-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DECL-04) | RG2001/2002/2004/2005 | R-QUALIFY |
| [`COMP-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#COMP-01) | RG1004/1007 and metadata reporting | R-INTENT |
| [`COMP-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#COMP-02) | RG1006/2005 | R-QUALIFY |
| [`COMP-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#COMP-03) | RG3001/3002 | R-QUALIFY, R-INVARIANT for intended roots |
| [`COMP-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#COMP-04) | RG3002/2005 | R-INTENT; external execution remains trusted |
| [`BUILD-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#BUILD-01) | RG1001–1007/2002–2005/3001/3002 through the actual enabled build or lint driver | R-QUALIFY (build-policy and lint-driver campaigns) |
| [`BUILD-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#BUILD-02) | RG1005/1007 | R-QUALIFY |
| [`BUILD-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#BUILD-03) | RG1007/2004/3001/3002 | R-INVARIANT, R-QUALIFY |
| [`BUILD-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#BUILD-04) | RG2002/2004/2005; uncached policy job | R-QUALIFY |
| [`DOC-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-01) | RG5001 module-docstring presence and placement (§5.3), RG5002 presence for explicit selection; RG2006 checks that `linter.missingDocs` is enabled, whose reports RG2003 rejects | R-DOC |
| [`DOC-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-02) | RG5003 Intent-section presence for explicit selection; no general prose-equivalence detector | R-DOC, R-INTENT |
| [`DOC-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-03) | RG4001 | R-QUALIFY |
| [`DOC-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-04) | RG4002 and underlying declaration/admission rules | R-INTENT, R-QUALIFY |
| [`DOC-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOC-05) | RG4003/4004 | R-QUALIFY |
| [`MUT-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#MUT-01) | Focused actual profile controls | R-QUALIFY |
| [`MUT-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#MUT-02) | Intended-reason mutation harness | R-QUALIFY |
| [`MUT-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#MUT-03) | Unique disposable roots and restoration | R-QUALIFY |
| [`MUT-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#MUT-04) | Warning-free isolated baseline | R-QUALIFY |
| [`MUT-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#MUT-05) | Existing freshChecker, optional new adapter only on go | R-GRAPH |
| [`DOGFOOD-01`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOGFOOD-01) | All applicable selected rules over Audit/AuditApp/Main | R-INTENT, R-INVARIANT, R-LAWS, R-BOUNDARY, R-DOC |
| [`DOGFOOD-02`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOGFOOD-02) | RG2002/2004 | R-QUALIFY |
| [`DOGFOOD-03`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOGFOOD-03) | Generated registry/example agreement plus checks | R-INTENT, R-DOC |
| [`DOGFOOD-04`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOGFOOD-04) | Lean canonical definitions/proofs | R-LAWS, R-COST |
| [`DOGFOOD-05`](https://rbeauchamp.github.io/regula/dev/standard/9-compliance-audit/#DOGFOOD-05) | RG1007/2004/2005 plus actual application contracts | R-INVARIANT, R-QUALIFY |

`./scripts/verify.sh docs` renders the standard and requires this map's links into the checklist
page to be exactly the rendered checklist rows, each once and in the checklist's order, each
labelled with exactly its row identifier as one code span
(`Regula.Site.rowMapMismatch`, `rowMapMismatch_eq_none_iff`), so a row added, removed or renamed
in the standard fails acceptance until this map follows. The equality covers row identifiers,
not whether a row's contribution and residual account fit its current requirement: a changed
requirement updates this map with semantic review, and independent review confirms the mapping.
Semantic-review rows remain required after all twenty-two rules ship.

## Attribution

The normative predicates and existing implementation are Regula's. Canonical typed
metadata and complete accepted-result design credit [con-leche's Installed.lean](https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean)
and [PropWhen.lean](https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean),
not an imported proof of these rules. Lean/Std and applicable Mathlib authors supply language
semantics, lawful definitions and linter APIs. The [ecosystem study](ecosystem-design.md) records the distinct Lean/Verso and
cross-language presentation influences; CA1416 is one illustrative example. Generated pages identify actual rule/metadata influences and adapted code/licenses at the
appropriate component boundary; see [attribution scope](design-influences.md). Con-ron is excluded.
