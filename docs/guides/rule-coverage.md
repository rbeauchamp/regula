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

The sole registry defines twenty-one stable IDs for the initial product. Grouping related failures under one ID
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
| RG3001 | Conservative execution closure has any unresolved path, unavailable retained code, unsupported history, or active replacement-only cycle. | Probe/Frontend histories; executionFailures execution-unresolved → executionFinding. | Completed project/environment plus compiler/source history; fresh/incremental and claimed file. The editor does not analyze execution. | Blocks report and checked modes. Ordinary recursion uses visited closure. Candidate edges are not claimed selected runtime edges. |
| RG3002 | In checked execution mode, a non-native-runtime boundary lacks exact admitted correspondence. | Probe.checkCorrespondenceProof; executionFailures execution-trusted-boundary → executionFinding. | Completed execution analysis; project fresh/incremental and file. | Origin-checked toolchain Init runtime remains trusted/reported. Report mode reports other trusted boundaries without rejecting them. Full dependent domain/universes, no extra theorem premises; external code is not proved by Lean equality. |
| RG4001 | Normative/example-tree fence structure or expected-error marker violates the exact §8.7 grammar. | Documentation scanner/Diagnostics → document-located contextFinding. | Documentation/project; docs CI; not native per-declaration editor lint. | All nested Markdown files in selected tree; malformed/orphan/double/misspelled markers and unclosed fences fail. Non-Lean sketches carry no elaboration claim. |
| RG4002 | A positive fence does not elaborate verbatim warning-free and complete its owned admission/foundation checks. | Documentation/SourceAudit/Admission → RG4002 + underlying findings. | DocumentationExample plus fresh claimed-import preparation. | No imports/wrappers inserted into checked source. Default Standard-Logical only; narrower/execution claims need explicit evidence. |
| RG4003 | A negative example lacks completed intended rejection matching its expected diagnostic within one effective-error message. | Diagnostics restricted matcher/worker completion; Website.validateBoundExample. | DocumentationExample. | Worker crash, timeout, wrong reason, info-only output and cross-message matching do not pass. Site lint violations may elaborate successfully before checker rejection. |
| RG4004 | A trusted-compiler teaching example fails warning-free elaboration or required authenticated compiler classification. | Documentation/SourceAudit/Frontend → RG4004 + typed underlying refusal. | DocumentationExample. | Never count teaching example as conforming positive. No blanket native-name whitelist. |
| RG5001 | A claimed module lacks module-doc metadata. | Linter.Documentation.modulePresent; AxiomGate project composition; #7 global jobs. | Module/environment; project and editor (when the module completed without errors). | Presence alone says nothing about identifying all material declarations/assumptions. No imposed headings or layout. |
| RG5002 | A public declaration explicitly registered as evidence for a material normative claim lacks a docstring. | regula_material/findDocString?; AxiomGate project composition; #7 global jobs. Core missingDocs broader. | Elaboration/environment; project/editor. | Do not require all public/private/trivial declarations to have docs. Registration completeness and meaning remain semantic review; no name heuristic. |
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
| 5.1–5.4 | DOC-01/02, THEOREM-01, SCOPE-02. Presence checks are RG5001/5002/5003; prose fidelity, intent adequacy and readability remain review. |
| 6.1–6.6 | DECL-01/04 (acyclic imports and actual elaboration), DOC-01, TYPE-06, SCOPE-04. Naming, import minimality/order and section layout are recommendations, not new rejection rules. |
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

Each row below names its mechanical contribution and residual account. The linked chapter 9 row
states the full exact required result and verification, and the clause table above supplies its
normative domain. No row can be discharged solely by a presence check or a checker PASS.

| Row | Exact required result (normative summary) | Mechanical contribution | Residual obligation |
| --- | --- | --- | --- |
| `SCOPE-01` | Every normative requirement concerns Lean, dependent types, proofs, elaboration, modules, or a Lean-code claim. | None; technical scope review | R-INTENT |
| `SCOPE-02` | Prose states no result stronger than the exact Lean declaration it cites. | RG1007/2005 for named formal evidence only | R-INTENT |
| `SCOPE-03` | A theorem about a model is not presented as a theorem about an unrelated implementation, runtime, or external system. | RG1007/3001/3002 for registered correspondence | R-INVARIANT, R-INTENT |
| `SCOPE-04` | Universal rules are technical Lean rules, not arbitrary style or application-domain policy. | None; rationale review | R-INTENT |
| `SCOPE-05` | The object and kind of every material claim are clear: abstract mathematical, executable Lean definition, refinement/correspondence, or external/effectful boundary. Combined claims keep these scopes distinct. An unresolved execution path or a partial surface presented as whole-application coverage blocks the affected claim. | RG2002/2004/3001/3002 | R-INTENT, R-INVARIANT |
| `TYPE-01` | Each unary admitted-value invariant is enforced intrinsically by default; a justified raw representation has verified admission and every write boundary closing the same invariant. Reachability and relational claims are stated separately. | Lean type/contract checking, RG1007/2005 | R-INVARIANT |
| `TYPE-02` | Every semantic distinction claimed to be enforced by Lean is represented in the interface types or constructors, with its exact scope stated. | Lean type/constructor checking | R-INTENT |
| `TYPE-03` | Totalized operations and restricted domains are described accurately; a restriction appears in the API only when claimed. | Lean domain/proof checking | R-INTENT |
| `TYPE-04` | Abstract models express assumptions as parameters, hypotheses, or proof-bearing fields rather than project logical axioms. | RG1001/1002/1003 | R-INTENT |
| `TYPE-05` | Claimed orders, algebras, and other mathematical interfaces provide their laws and reuse matching Lean/Mathlib structures. | Lean law fields and instance synthesis | R-LAWS |
| `TYPE-06` | Every claimed abstraction boundary is the boundary Lean actually enforces. | Lean separate importing-client checks | R-BOUNDARY |
| `THEOREM-01` | Every material behavior claim presented as established has kernel-checked evidence in a type, proof-bearing construction, or theorem with the exact intended quantifiers, assumptions, and conclusion. | RG1001–1007/2005 and exact Lean evidence | R-INTENT, R-INVARIANT |
| `THEOREM-02` | Every claimed typeclass law follows from proof-requiring fields of the operational class or a required `Prop`-valued lawful mixin, directly or by checked derivation under the advertised hypotheses. Every law-bearing instance discharges its required primitive fields, and required instances are available directly or from stronger assumptions. | Lean required law fields/mixin synthesis | R-LAWS |
| `THEOREM-03` | Admission and every update establish the claimed invariant by proof-bearing results or the justified raw-boundary contracts; transition/history/resource-use claims have exact proofs, including initialization, preservation, and composition where the claim requires them. | RG1007/2005 and actual boundary proofs | R-INVARIANT |
| `THEOREM-04` | Important claims are non-vacuous at the exact strength claimed; non-vacuity is relative to the claim. | Lean exact witness/refutation proofs | R-NONVACUITY |
| `THEOREM-05` | Logical totality, termination, complexity, and native execution are distinguished; each claimed property has evidence about the exact definitions and semantics it concerns. | RG1006/3001/3002; Lean recursion checking | R-COST, R-INTENT |
| `THEOREM-06` | Sampled tests and unchecked evaluation do not replace proofs of universal or existential Lean claims. Counterexample search is an optional aid to refutation. | RG1002/1004 reject holes/native proofs | R-INTENT, R-QUALIFY |
| `THEOREM-07` | Material functional contracts state the component’s exact input/output meaning, rejection and normalization behavior, intended updates and frames, state/error composition, and promised fold relation where applicable. Admission completeness is proved when promised. | RG1007/2005 exact registered predicates | R-INVARIANT |
| `THEOREM-08` | Stateful safety transfer has checked correspondence over the exact state and transition semantics. The forward-simulation method in §3.9 supplies initialization, finite abstract matching, preservation, and relation-to-concrete implication; another method must prove the same claimed transfer. Observations and liveness are separate claims. | Lean checked simulation/transfer proofs | R-INVARIANT, R-INTENT |
| `THEOREM-09` | A research statement is adequate to its source mathematics, the presented result's status is exactly one of proved unconditionally, proved under explicit binder hypotheses, or open, and an open target is a `Prop` definition or binder rather than a hole, project axiom, or claimed proof. | RG1001–1003; Lean statement/proof distinction | R-INTENT, R-NONVACUITY |
| `THEOREM-10` | Every cost claim names its domain — elaboration/search, proof artifact, kernel replay, or native execution — and no speed, tactic name, native result, theorem count, sample, or audit digest is presented as evidence of correctness or foundation strength; a well-founded definition's own axiom set is reported exactly. | RG1004/1005 actual dependencies | R-COST |
| `FOUND-01` | No owned declaration is a project logical `axiom` (Lean 4 has no `constant` command; `opaque` is classified under `COMP-01`); domain assumptions are binders or proof-bearing fields. | RG1001 | R-INTENT only for assumption presentation |
| `FOUND-02` | No owned declaration depends transitively on `sorryAx`; no `sorry` or `admit` survives under alternate syntax, attributes, definitions, or instances. | RG1002 | R-QUALIFY |
| `FOUND-03` | Every owned declaration has its exact transitive axiom set reported. An admissible set receives the least permissive logical label containing it; the selected surface profile is an upper bound. Forbidden and compiler-trusting sets are rejected from conforming positive surfaces. | RG1003/1004/1005 | R-QUALIFY |
| `FOUND-04` | No Choice-Free surface depends directly or transitively on `Classical.choice`; a selected Standard-Logical surface may. | RG1005 | R-QUALIFY |
| `FOUND-05` | Native/compiler-generated proof axioms are classified separately and rejected from the conforming positive proof surface; final-environment metadata alone cannot spoof the classification. | RG1004/2005 | R-QUALIFY |
| `DECL-01` | Every exact module in each claimed Lake library and every claimed standalone executable root is discovered and elaborated from source in fresh root-package build state, warning-free, under the declared exact elaboration environment, with completed owned logical declaration and dependency admission under §8.3. | RG2001–2005 | R-QUALIFY; source/dependency identity boundary |
| `DECL-02` | Every constant in every owned module is inventoried; proof-valued definitions and instances are not omitted. | RG2004/2005 | R-QUALIFY |
| `DECL-03` | Ownership uses Lean/Lake semantics. Generated-role exceptions require fresh frontend attribution and the exact semantic relationship in §8.4–§8.5; names or forgeable final metadata alone cannot authorize them. | RG2004/2005 plus RG1001/1004/1006 | R-QUALIFY |
| `DECL-04` | Missing/malformed manifests, unknown metadata, omitted declarations, and unexpected project modules fail closed. | RG2001/2002/2004/2005 | R-QUALIFY |
| `COMP-01` | `noncomputable`, `opaque`, logical `Decidable`, executable decision procedures, kernel reduction, and native evaluation are distinguished accurately. | RG1004/1007 and metadata reporting | R-INTENT |
| `COMP-02` | Partial and unsafe declarations are excluded from positive proof surfaces, except for the range-less partial code-generation helper admitted under the exact semantic and fresh frontend conditions in §8.4 for a safe recursive `def`. | RG1006/2005 | R-QUALIFY |
| `COMP-03` | Every boundary in the §8.6 conservative execution closure has its exact kind and correspondence state reported; retained compiler edges are distinguished from candidates and historical choices. In `"execution": "checked"` mode, every non-native-runtime boundary in that closure is checked. Unresolved paths block the affected execution claim in every mode. | RG3001/3002 | R-QUALIFY, R-INVARIANT for intended roots |
| `COMP-04` | Transfer from a Lean reference definition to a replacement requires sufficient checked correspondence. Keep remaining trust assumptions for native and external execution explicit. | RG3002/2005 | R-INTENT; external execution remains trusted |
| `BUILD-01` | The documented enabled ordinary `lake build`, and `lake lint` with the `lint` driver, reject every emitted warning, policy violation, and unresolved claimed execution path. Source-local warning/linter options cannot authorize policy exceptions. | RG1001–1007/2002–2005/3001/3002 through the actual enabled build or lint driver | R-QUALIFY (build-policy and lint-driver campaigns) |
| `BUILD-02` | Declared profiles are transitively enforced, with classical erased proofs permitted under Standard-Logical and executable promises checked separately. | RG1005/1007 | R-QUALIFY |
| `BUILD-03` | Required executable evidence inhabits the exact predicate of the actual named implementation, and registered private/imported roots retain execution coverage. | RG1007/2004/3001/3002 | R-INVARIANT, R-QUALIFY |
| `BUILD-04` | Cached modules and changed configuration cannot reuse a stale policy verdict; exact claimed Lake coverage and supported-context limits are explicit. | RG2002/2004/2005; uncached policy job | R-QUALIFY |
| `DOC-01` | Public declarations supporting material normative claims have docstrings stating their formal purpose, relevant assumptions, result, and invariant boundary; every claimed module documents its material declarations and assumptions. | RG5001/5002 presence and explicit selection | R-DOC |
| `DOC-02` | English explanations of normative Lean statements faithfully convey their quantifiers, hypotheses, conclusions, relevant definitions, and limitations, and identify the authoritative Lean declaration. Each material claim's docstring carries a nonempty Intent section. | RG5003 Intent-section presence for explicit selection; no general prose-equivalence detector | R-DOC, R-INTENT |
| `DOC-03` | Every Lean fence in the normative documentation tree (here every `lean` block of the standard's Verso source, `website/RegulaStandard`) is structurally classified; malformed markers/fences fail closed. | RG4001 | R-QUALIFY |
| `DOC-04` | Every positive Lean fence elaborates exactly as printed, warning-free, then passes owned logical admission and declaration/axiom classification. | RG4002 and underlying declaration/admission rules | R-INTENT, R-QUALIFY |
| `DOC-05` | Every negative fence fails for its non-empty expected diagnostic, and trusted-compiler teaching fences are classified but never counted as conforming. | RG4003/4004 | R-QUALIFY |
| `MUT-01` | A checker that classifies foundation profiles has positive controls for all three profiles through its actual detection implementation, with public-path qualification as required by §8.8. | Focused actual profile controls | R-QUALIFY |
| `MUT-02` | A checker implementation has an independent intended-reason mutation for every violation class it advertises. | Intended-reason mutation harness | R-QUALIFY |
| `MUT-03` | A checker qualification harness cannot overwrite positive sources or leave stale Lean artifacts, and its restored control passes fresh. | Unique disposable roots and restoration | R-QUALIFY |
| `MUT-04` | Checker qualification establishes a fresh warning-free configured-module baseline and keeps mutation artifacts from satisfying restored controls. | Warning-free isolated baseline | R-QUALIFY |
| `MUT-05` | When separate serialized-graph checking is claimed, the exact claimed module graph is rechecked in a compatible fresh checker state. | Existing freshChecker, optional new adapter only on go | R-GRAPH |
| `DOGFOOD-01` | The repository's own claimed Lean surfaces — the `Audit` library of mathematical models, proofs, and executable examples and the `AuditApp` complete application with its standalone `Main` executable root — satisfy every applicable row above. | All applicable selected rules over Audit/AuditApp/Main | R-INTENT, R-INVARIANT, R-LAWS, R-BOUNDARY, R-DOC |
| `DOGFOOD-02` | Intentionally invalid fixtures are isolated from the positive elaborated environment. | RG2002/2004 | R-QUALIFY |
| `DOGFOOD-03` | Normative prose, representative Lean fixtures, checker diagnostics, and status text make no stronger claim than the same verified property. | Generated registry/example agreement plus checks | R-INTENT, R-DOC |
| `DOGFOOD-04` | Examples and fixtures reuse or extend matching Lean/Mathlib mathematical definitions. Custom mathematical definitions state their meaning and why existing definitions do not fit; proofs follow the economy guidance in §3.2.5. | Lean canonical definitions/proofs | R-LAWS, R-COST |
| `DOGFOOD-05` | The complete application enforces its explicit required propositions: omitting executable classification, removing or weakening required evidence while its proposition remains, or weakening admission fails the gate. Semantic review rejects a narrowed requirement set or bypassed application linkage. | RG1007/2004/2005 plus actual application contracts | R-INVARIANT, R-QUALIFY |

The 53-row equality check is an exhaustive check over this closed documentation inventory,
not a proof that natural-language requirements were interpreted adequately. Independent review
must confirm the mapping. Semantic-review rows remain required after all twenty-one rules ship.

## Attribution

The normative predicates and existing implementation are Regula's. Canonical typed
metadata and complete accepted-result design credit [con-leche's Installed.lean](https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Cached/Installed.lean)
and [PropWhen.lean](https://github.com/leanprover/con-leche/blob/c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0/ConLeche/Kernel/PropWhen.lean),
not an imported proof of these rules. Lean/Std and applicable Mathlib authors supply language
semantics, lawful definitions and linter APIs. The [ecosystem study](ecosystem-design.md) records the distinct Lean/Verso and
cross-language presentation influences; CA1416 is one illustrative example. Generated pages identify actual rule/metadata influences and adapted code/licenses at the
appropriate component boundary; see [attribution scope](design-influences.md). Con-ron is excluded.
