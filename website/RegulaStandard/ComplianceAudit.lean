import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "8. Compliance and Quality Audit" =>
%%%
tag := "8-compliance-and-quality-audit"
file := "8-compliance-audit"
number := false
%%%

{pageAnchor}

# Purpose
%%%
tag := "purpose"
number := false
%%%

This module provides the checklist for auditing a project against this standard. It defines no independent rules; each checklist item links to the normative module specifying the Lean requirement and rationale.

No reduced or minimum compliance levels exist. A project conforms only when every applicable row passes across its claimed Lean surfaces. A known violation is `FAIL`; missing, unknown, untested, unsupported, or timed-out required evidence is `INCOMPLETE`. Both block conformance.

Applicability follows the stated technical condition. `BUILD-*` applies to a claim that rests on a pass of the gate of {ref "7-tooling-and-machine-audit"}[module 7]. A conditional row passes when its condition is absent and that reason is recorded, or when every applicable occurrence conforms. An absent condition is not evidence that the corresponding checks ran.

This checklist does not address project management or general software assurance. It audits dependent types, theorem statements, proof terms, axioms, elaboration, modules, Lean computation mechanisms, and Lean documentation claims.

# Audit Matrix
%%%
tag := "audit-matrix"
number := false
%%%

Assess each row against the actual claimed surface. The verification column names what a pass of the gate establishes for the row and what review must establish beside it. Where it names a rule, a pass of `lake lint` establishes exactly that rule's statement on {repo "specification/README.md"}[the rule's page and specification entry], under the trusted base stated there; a rule that the specification hands to Lean is decided by Lean's command, and a retired rule is written guidance. A rule's result does not replace inspection of the current surface or semantic review of its claims. The matrix defines required results, not 43 separate commands or repeated review assignments.

## Scope and Claim Boundaries
%%%
tag := "scope-and-claim-boundaries"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[SCOPE-01]
  * Every normative requirement concerns Lean, dependent types, proofs, elaboration, modules, or a Lean-code claim.
  * {ref "scope"}[Set scope]
  * Read every normative `MUST`/`MUST NOT`; fail any generic lifecycle, release, deployment, organizational, certification, or other non-Lean mandate.
*
  * {checklistRow}[SCOPE-02]
  * Prose states no result stronger than the exact Lean declaration it cites.
  * {ref "why-this-matters"}[0: claim boundary], {ref "16-claim-boundaries-and-automated-checking"}[1 §1.6]
  * For every material claim, record the elaborated type, all quantifiers and hypotheses, and compare them with the prose conclusion.
*
  * {checklistRow}[SCOPE-03]
  * A theorem about a model is not presented as a theorem about an unrelated implementation, runtime, or external system.
  * {ref "13-the-specificationmodel-firewall"}[1 §1.3], {ref "16-claim-boundaries-and-automated-checking"}[1 §1.6]
  * Identify the exact model and implementation definitions. For distinct objects, require a checked relation sufficient to transfer the claimed property; reuse definitional equality or existing evidence where it suffices. State the external execution assumptions separately; otherwise narrow or remove the claim.
*
  * {checklistRow}[SCOPE-04]
  * Universal rules are technical Lean rules, not arbitrary style or application-domain policy. The style, naming, and documentation-form baseline is the Lean community's, adopted by requiring its linters, not restated as rules.
  * {ref "14-principled-mathematical-modeling"}[1 §1.4], {ref "6-code-organization"}[6], {ref "67-community-conventions-and-linters"}[6 §6.7]
  * For each universal rule, identify the precise type, proof, elaboration, resolution, module, or computation consequence. Confirm that the style, naming, and documentation-form requirements are the community's own linters (§6.7) and its guides, not conventions restated as rules of this standard.
*
  * {checklistRow}[SCOPE-05]
  * The object and kind of every material claim are clear: abstract mathematical, executable Lean definition, refinement/correspondence, or external/effectful boundary. Combined claims keep these scopes distinct. An unresolved execution path or a partial surface presented as whole-application coverage blocks the affected claim.
  * {ref "13-the-specificationmodel-firewall"}[1 §1.3], {ref "36-contracts-for-executable-and-effectful-mechanisms"}[3 §3.6], {ref "76-classify-lean-computation-mechanisms-exactly"}[7 §7.6]
  * Enumerate the claimed surfaces and material claims. Reconcile the executable roots and execution boundaries under `COMP-03`, and each executable contract under `BUILD-03` where applicable.
:::

## Dependent Types and Lawful APIs
%%%
tag := "dependent-types-and-lawful-apis"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[TYPE-01]
  * Each unary admitted-value invariant is enforced intrinsically by default; a justified raw representation has verified admission and every write boundary closing the same invariant. Reachability and relational claims are stated separately.
  * {ref "11-the-principle-of-representational-precision"}[1 §1.1], {ref "22-dependent-types-for-invariants"}[2 §2.2]
  * Inspect the elaborated type and invalid constructor/update terms; for raw representations, inspect the rationale, every admission/write theorem, and how consumers obtain the required proof. Do not apply an intrinsic-value claim to arbitrary raw states.
*
  * {checklistRow}[TYPE-02]
  * Every semantic distinction claimed to be enforced by Lean is represented in the interface types or constructors, with its exact scope stated.
  * {ref "21-semantic-types-typed-decoding-boundaries"}[2 §2.1], {ref "23-phantom-types-for-disambiguation"}[2 §2.3]
  * Inspect the typed decoding boundary and downstream API. An enumeration restricts the vocabulary but its constructors share one type. Where distinct types, indices, or refinements are claimed to prevent cross-use, check that use is rejected for the intended reason; parsing or validation at admission is permitted.
*
  * {checklistRow}[TYPE-03]
  * Totalized operations and restricted domains are described accurately; a restriction appears in the API only when claimed.
  * {ref "23-phantom-types-for-disambiguation"}[2 §2.3], {ref "321-totality-termination-and-totalized-operations"}[3 §3.2.1]
  * Check boundary cases by reduction/theorem and verify the exact hypothesis or subtype required at call sites.
*
  * {checklistRow}[TYPE-04]
  * Abstract models express assumptions as parameters, hypotheses, or proof-bearing fields rather than project logical axioms.
  * {ref "24-abstract-mathematical-models"}[2 §2.4]
  * Inspect binders and `ConstantInfo`; distinguish assumed propositions from definitions with checked bodies.
*
  * {checklistRow}[TYPE-05]
  * Claimed orders, algebras, and other mathematical interfaces provide their laws and reuse matching Lean/Mathlib structures.
  * {ref "14-principled-mathematical-modeling"}[1 §1.4], {ref "41-numeric-representations-mathematical-and-machine-arithmetic"}[4 §4.1–§4.2]
  * Inspect the selected structures, law-bearing instances, or explicit proof assumptions, including laws supplied by stronger instances. Compare the resulting operations and relations with the intended concept and matching Core/Mathlib definitions.
*
  * {checklistRow}[TYPE-06]
  * Every claimed abstraction boundary is the boundary Lean actually enforces.
  * {ref "13-the-specificationmodel-firewall"}[1 §1.3], {ref "65-visibility-and-encapsulation"}[6 §6.5]
  * State the client import context. Verify the intended API use succeeds and that each claimed exclusion fails from a separate importing module. Distinguish name resolution, unfolding, construction, and observation; inspect exported constructors, recursors, projections, coercions, operations, and equations. A failed probe establishes only that attempted exclusion.
:::

## Theorems, Proofs, and Non-Vacuity
%%%
tag := "theorems-proofs-and-non-vacuity"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[THEOREM-01]
  * Every material behavior claim presented as established has kernel-checked evidence in a type, proof-bearing construction, or theorem with the exact intended quantifiers, assumptions, and conclusion.
  * {ref "12-theorem-backed-claims"}[1 §1.2], {ref "31-what-must-be-proven"}[3 §3.1]
  * Enumerate prose claims and match each to an elaborated declaration type; unmatched or weakened claims fail. For executable components, inspect explicit proof requirements and their linkage to actual definitions; gate PASS alone does not establish specification adequacy or completeness.
*
  * {checklistRow}[THEOREM-02]
  * Every claimed typeclass law follows from proof-requiring fields of the operational class or a required `Prop`-valued lawful mixin, directly or by checked derivation under the advertised hypotheses. Every law-bearing instance discharges its required primitive fields, and required instances are available directly or from stronger assumptions.
  * {ref "323-typeclasses-for-lawful-abstractions"}[3 §3.2.3]
  * Inspect the actual primitive law fields, derived theorems, and selected instances. Every primitive obligation must be discharged; every derived guarantee must follow with exactly its advertised hypotheses. Required mixin evidence must be available at the use site; operations alone do not supply it.
*
  * {checklistRow}[THEOREM-03]
  * Admission and every update establish the claimed invariant by proof-bearing results or the justified raw-boundary contracts; transition/history/resource-use claims have exact proofs, including initialization, preservation, and composition where the claim requires them.
  * {ref "31-what-must-be-proven"}[3 §3.1]
  * Inspect admission, all writes, consumers, and exact relational theorem statements. Conditional preservation is not admission, functional behavior, reachability, liveness, or latest-state use.
*
  * {checklistRow}[THEOREM-04]
  * Important claims are non-vacuous at the exact strength claimed; non-vacuity is relative to the claim.
  * {ref "the-necessary-dual-non-vacuity"}[0: non-vacuity], {ref "310-research-statements-adequacy-conditional-completeness-and-open-targets"}[3 §3.10]
  * Require inhabitance, joint satisfiability, or reachability proofs according to the actual prose; stronger evidence may discharge a weaker requirement when the implication and any additional hypotheses are established. Do not reject a deliberately conditional, contradiction, or minimal-counterexample theorem for lacking an antecedent inhabitant when only the implication is claimed; when the development establishes that the antecedent is false, require the prose to acknowledge vacuity where it affects interpretation; the implication establishes neither an antecedent witness nor its conclusion unconditionally.
*
  * {checklistRow}[THEOREM-05]
  * Logical totality, termination, complexity, and native execution are distinguished; each claimed property has evidence about the exact definitions and semantics it concerns.
  * {ref "321-totality-termination-and-totalized-operations"}[3 §3.2.1]
  * Inspect recursive definitions and termination evidence. Match additional claims to the exact types, constructions, or theorems establishing them; logical totality alone does not establish complexity or native execution behavior.
*
  * {checklistRow}[THEOREM-06]
  * Sampled tests and unchecked evaluation do not replace proofs of universal or existential Lean claims. Counterexample search is an optional aid to refutation.
  * {ref "the-role-of-testing"}[0: role of testing], {ref "322-property-based-testing-as-refutation-aid"}[3 §3.2.2]
  * Reject proof claims supported only by samples, unchecked enumeration, `#eval`, or native output. Kernel-checked exhaustive finite proofs and checked existential witnesses are proof evidence. A control run against a checker is diagnostic evidence about the tool, not proof of the audited mathematics.
*
  * {checklistRow}[THEOREM-07]
  * Material functional contracts state the component’s exact input/output meaning, rejection and normalization behavior, intended updates and frames, state/error composition, and promised fold relation where applicable. Admission completeness is proved when promised.
  * {ref "37-a-compositional-method-for-complete-program-contracts"}[3 §3.7]
  * Inspect the actual executable definitions and the relations their contracts require. Check intermediate preconditions and the claimed success, error, and effect semantics. Reuse types, construction, library results, or another checked argument; initialization and preservation are required when the chosen argument needs them. Rule out degenerate implementations that violate the promised relation. Where a decision is registered with a kind (§3.8), read its direction from the kind that the contract states: a one-way kind leaves the other direction unclaimed, and the kind is not evidence that the specification is the intended one. The checker decides two parts. Every function of a claimed module that a claimed module registers with `Regula.RegisteredDecision` has a decision contract of a claimed module in the same environment, or a `Decidable` result type ({rule}[RG1008]). No decision contract of a claimed module has a specification and an implementation or acceptance predicate that reach one Boolean test outside the toolchain, where a field's projection function is no test ({rule}[RG1009], read as §7.9 states). Whether every function that acts as a checker is registered, whether the kind states the implementation on its whole domain, and whether each specification is adequate remain review: a copy of a test under a second name passes the second check. Separate finite totality and partial correctness from external liveness.
*
  * {checklistRow}[THEOREM-08]
  * Stateful safety transfer has checked correspondence over the exact state and transition semantics. The forward-simulation method in §3.9 supplies initialization, finite abstract matching, preservation, and relation-to-concrete implication; another method must prove the same claimed transfer. Observations and liveness are separate claims.
  * {ref "39-stateful-refinement-and-finite-prefix-safety"}[3 §3.9]
  * Inspect the transfer theorem’s exact hypotheses, conclusion, and executable linkage. For the forward-simulation method, check every related pair/concrete successor quantifier, the existential abstract match, stuttering semantics, and universal finite-path induction. Check initial-state reachability at the claimed strength and observation granularity. Require separate hypotheses/proofs for any progress, fairness, productivity, or liveness claim; safety alone supplies none.
*
  * {checklistRow}[THEOREM-09]
  * A research statement is adequate to its source mathematics, the presented result's status is exactly one of proved unconditionally, proved under explicit binder hypotheses, or open, and an open target is a `Prop` definition or binder rather than a hole, project axiom, or claimed proof.
  * {ref "310-research-statements-adequacy-conditional-completeness-and-open-targets"}[3 §3.10], {ref "52-faithful-explanation-of-formal-claims"}[5 §5.2]
  * Read each material statement back from the elaborated term: quantifier order and dependence, implicit parameters and universes, consequential definitions, notation, coercions, selected instances, totalized operations, and existence/construction/uniqueness/complexity distinctions. Reject strengthened prose or omitted domain assumptions. Keep reduction hypotheses explicit. Exclude intentionally incomplete sketches and adapters from positive surfaces and closed declarations’ dependency closures; a platform-accepted result needs evidence for the actual elaboration environment and foundation.
*
  * {checklistRow}[THEOREM-10]
  * Every cost claim names its domain — elaboration/search, proof artifact, kernel replay, or native execution — and no speed, tactic name, native result, theorem count, sample, or audit digest is presented as evidence of correctness or foundation strength; a well-founded definition's own axiom set is reported exactly.
  * {ref "325-proof-economy-four-cost-domains-and-one-trust-question"}[3 §3.2.5]
  * For each cost statement, identify its domain and inspect the argument or bounded observation supporting that exact claim. Recursive-step counts alone do not establish wall-clock complexity. Inspect elaborated recursion, produced terms, and exact axiom dependencies as relevant; cost or native output does not replace proof evidence.
:::

## Axioms and Foundation Strength
%%%
tag := "axioms-and-foundation-strength"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[FOUND-01]
  * No owned declaration is a project logical `axiom` (Lean 4 has no `constant` command; `opaque` is classified under `COMP-01`); domain assumptions are binders or proof-bearing fields.
  * {ref "34-foundation-strength-axioms-are-reported-never-assumed"}[3 §3.4], {ref "75-proof-completeness-and-foundation-strength"}[7 §7.5]
  * Inspect every owned `ConstantInfo`, including unused, private, internal-looking, and generated declarations. Review that each domain assumption, as a binder or proof-bearing field, presents the intended hypothesis.
*
  * {checklistRow}[FOUND-02]
  * No owned declaration depends transitively on `sorryAx`; no `sorry` or `admit` survives under alternate syntax, attributes, definitions, or instances.
  * {ref "11-the-principle-of-representational-precision"}[1 §1.1], {ref "75-proof-completeness-and-foundation-strength"}[7 §7.5]
  * The checker reads the transitive axiom set of every constant of a claimed module, proof-valued definitions and instances included, and reports each that holds `sorryAx` ({rule}[RG1002]). A proof of `rg1002_exact` in the specification states that it reports exactly those constants.
*
  * {checklistRow}[FOUND-03]
  * Every owned declaration's exact transitive axiom set lies within its surface's selected profile, which is an upper bound. Forbidden and compiler-trusting sets are rejected from conforming positive surfaces.
  * {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[4 §4.5], {ref "75-proof-completeness-and-foundation-strength"}[7 §7.5]
  * The checker compares each computed set with `{}`, `{propext, Quot.sound}`, and that set plus `Classical.choice` of the toolchain and reports what the profile does not admit ({rule}[RG1005]); unknown axioms fail ({rule}[RG1003]). It prints no label: `#print axioms` shows a declaration's set. The actual proof's dependencies do not establish minimal axioms among all possible proofs of its proposition.
*
  * {checklistRow}[FOUND-04]
  * No Choice-Free surface depends directly or transitively on `Classical.choice`; a selected Standard-Logical surface may.
  * {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[4 §4.5]
  * The checker reads the transitive sets under the selected surface profile ({rule}[RG1005]). Direct and transitive `Classical.choice` both fail a Choice-Free claim, because the set is transitive.
*
  * {checklistRow}[FOUND-05]
  * Native/compiler-generated proof axioms are named separately and rejected from the conforming positive proof surface; an axiom's name decides which rule reports it, not whether the verdict fails. The pinned toolchain declares no axiom by which the kernel trusts the compiler.
  * {ref "75-proof-completeness-and-foundation-strength"}[7 §7.5–§7.6]
  * The checker names an axiom by the form `<declaration>._native.<tactic>.<suffix>` and reports each constant that depends on it ({rule}[RG1004]), and it reports such an axiom declared in a claimed module ({rule}[RG1001]). An authored axiom of that name is reported under the same rules, and it fails the claim too. Each such axiom also violates {rule}[RG1005] for each profile, as the specification proves (`rg1005_of_compiler`).
:::

## Declaration and Module Coverage
%%%
tag := "declaration-and-module-coverage"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[DECL-01]
  * Every exact module in each claimed Lake library and every claimed executable root is discovered and elaborates from source, warning-free, under the declared exact elaboration environment with the community linters of §6.7 enabled, and Lean's kernel checks its constants again from an export of the build under §7.3.
  * {ref "71-declare-the-elaboration-environment"}[7 §7.1–§7.3], {ref "62-module-purpose-and-linter-discipline"}[6 §6.2], {ref "67-community-conventions-and-linters"}[6 §6.7]
  * Run `lake build --wfail` for the claimed targets ({rule}[RG2003]) and `lake check` ({rule}[RG2005]) on one finished build. The checker reads Lake's module arrays and executable roots, and it requires each module of a target to be loaded ({rule}[RG2001]) and each module of the root package to be covered ({rule}[RG2004]). Record toolchain and dependency source state, the identity the result is bound to. Dependency artifacts may be reused. The `modules` facet can include local imports beyond the configured array; it is a cross-check, not an interchangeable inventory. Check the Lake configuration of every claimed library and executable against {rule}[RG2006] as specified in {ref "62-module-purpose-and-linter-discipline"}[§6.2]. Separately review the required community-linter settings of §6.7: `linter.missingDocs` on and, when the surface imports Mathlib, `weak.linter.mathlibStandardSet` with exactly those exclusions, or with the header linter on and its license line configured. These settings are written guidance; the rule admits their option names without checking their values. Review every source `set_option` command, which the rule does not read, in particular that no claimed module sets `autoImplicit` or `relaxedAutoImplicit` back on or disables a Lean default warning; and every source-local linter disable, each disabled community linter being declaration-scoped with a stated reason (§6.2).
*
  * {checklistRow}[DECL-02]
  * Every constant of every claimed module is read by the rules; proof-valued definitions and instances are not omitted.
  * {ref "74-inventory-every-owned-declaration"}[7 §7.4]
  * The loader takes each constant whose module Lake lists for a claimed target from the environment that loads it, and it refuses an input that does not have the closed form. The checker prints its count of these constants; compare it with the environment where that matters. That the rules decide the same on the list they read as on every constant of the environment is argued, with no theorem.
*
  * {checklistRow}[DECL-03]
  * Ownership uses Lean/Lake semantics. Two exceptions go by form or name, as their rules state: a recursion helper of a safe definition in its own module ({rule}[RG1006], §7.4), and the rule that names a native-proof axiom ({rule}[RG1004], §7.5), which leaves the verdict as it is.
  * {ref "72-define-surfaces-through-lake-semantics"}[7 §7.2], {ref "74-inventory-every-owned-declaration"}[7 §7.4]
  * Inspect ownership and every claimed exception. A claimed module is one that Lake lists for a claimed target, whatever its name, so an exact-prefix lookalike is not claimed by its prefix. A forged helper of that form passes the rule: what a helper computes is the question of execution that {rule}[RG3002] decides under a checked claim.
*
  * {checklistRow}[DECL-04]
  * Missing/malformed manifests, omitted targets and unexpected project modules fail closed.
  * {ref "72-define-surfaces-through-lake-semantics"}[7 §7.2–§7.4]
  * A manifest the reader refuses, a read that fails and an input without the closed form make the run `incomplete` ({rule}[RG2001]). An omitted or unknown target is {rule}[RG2002], and a module in no target is {rule}[RG2004]. Review each rationale.
:::

## Lean Computation and Evaluation
%%%
tag := "lean-computation-and-evaluation"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[COMP-01]
  * `noncomputable`, `opaque`, logical `Decidable`, executable decision procedures, kernel reduction, and native evaluation are distinguished accurately.
  * {ref "324-decidability-logical-vs-executable"}[3 §3.2.4], {ref "76-classify-lean-computation-mechanisms-exactly"}[7 §7.6]
  * Inspect metadata and axiom sets; check representative reduction/evaluation behavior on the pinned toolchain.
*
  * {checklistRow}[COMP-02]
  * Partial and unsafe declarations are excluded from positive proof surfaces, except for the partial helper `f._unsafe_rec` of a safe, total definition `f` in the same module (§7.4). It keeps its execution boundary.
  * {ref "74-inventory-every-owned-declaration"}[7 §7.4–§7.6]
  * The checker reads `ConstantInfo.isUnsafe`/`isPartial` of each constant of a claimed module and reports each that is not such a helper ({rule}[RG1006]). A `partial def` is reported through its helper, because its base is an opaque constant. The rule identifies a helper by its form, not by what it computes.
*
  * {checklistRow}[COMP-03]
  * The closure of §7.6 resolves for each claimed executable: each name it holds is a constant of the input, and none is on a cycle of departures ({rule}[RG3001]). In `"execution": "checked"` mode, every boundary in that closure outside the toolchain's trusted base has a correspondence that the claim's profile admits, and no constant of it outside the toolchain is code that no theorem can bind ({rule}[RG3002]). A claim without that mode states nothing about boundaries.
  * {ref "76-classify-lean-computation-mechanisms-exactly"}[7 §7.6]
  * The checker reads the compiled code of `main` and the departures of each constant of its closure, and in `checked` mode each theorem that states a correspondence over the universes of the constants it relates. It reports nothing under `report` beyond {rule}[RG3001]. Observing a target in emitted code concerns discovery, not compiler or external-code correctness. Review that the executable roots are the intended ones.
*
  * {checklistRow}[COMP-04]
  * Transfer from a Lean reference definition to a replacement requires sufficient checked correspondence. Keep remaining trust assumptions for native and external execution explicit.
  * {ref "76-classify-lean-computation-mechanisms-exactly"}[7 §7.6]
  * Compare each theorem’s exact statement and dependencies with the claimed computation and admitted relation. A relation between Lean definitions does not itself verify external machine code or discharge reached extern/native boundaries.
:::

## The Gate of a Finished Build
%%%
tag := "the-gate-of-a-finished-build"
number := false
%%%

These rows apply when a claim rests on a pass of the gate of {ref "7-tooling-and-machine-audit"}[module 7]. The other applicable rows remain required for full conformance; a pass of the gate alone does not discharge them.

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[BUILD-01]
  * `lake build --wfail`, `lake check` and `lake lint` each pass on one finished build. An emitted warning, a kernel refusal, a rule's finding, and an input the checker cannot load each fail the gate. No source-local option authorizes an exception to a rule.
  * {ref "7-tooling-and-machine-audit"}[7], {ref "78-adopting-the-checker-in-another-project"}[7 §7.8]
  * Read the project's actual gate: the three commands, in order, on one checkout, and each exit status. `lake lint` runs the checker only when `lintDriver` is `regula/lint`; `lake lint --builtin-only` and a direct `lean` run do not. The checker reads no source option, so a source `set_option` cannot change its verdict. An option in source can stop a warning from reaching the build (§7.3), which review checks. That no process changes the build between the commands is assumed.
*
  * {checklistRow}[BUILD-02]
  * Declared profiles are transitively enforced, with classical erased proofs permitted under Standard-Logical and executable promises checked separately.
  * {ref "38-delivering-executable-witnesses-with-required-evidence"}[3 §3.8], {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[4 §4.5]
  * Read the profile findings ({rule}[RG1005]) and the executable contract findings ({rule}[RG1007]) separately. A classical proof of a contract is admitted under Standard-Logical, and a noncomputable implementation is reported under every profile.
*
  * {checklistRow}[BUILD-03]
  * Required executable evidence inhabits the exact predicate of the actual named implementation, and registered decisions keep their requirement.
  * {ref "79-executable-contracts-and-decision-registrations"}[7 §7.9]
  * Inspect each contract's predicate, its proof-bearing construction, and its actual callers. The checker decides {rule}[RG1007], {rule}[RG1008] and {rule}[RG1009] as §7.9 states: a contract fixes no argument and names a safe, computable implementation; a decision contract's specification does not reach its implementation; a registered function of a claimed module has a decision contract of a claimed module in the same environment, or a `Decidable` result type; and a decision contract's two sides reach no shared Boolean test outside the toolchain. Which functions are registered, whether the kind states the implementation on its whole domain and at its own universe parameters, and whether each specification is adequate remain review.
*
  * {checklistRow}[BUILD-04]
  * Cached modules and a changed claim cannot reuse a stale verdict; exact claimed Lake coverage and supported-context limits are explicit.
  * {ref "79-executable-contracts-and-decision-registrations"}[7 §7.9]
  * The checker reads the manifest and the finished build on each run and keeps no verdict, so a changed profile or execution mode is reevaluated without a source edit and cannot reuse an old verdict. The new claim may still pass if it satisfies the rules. `lake build --wfail` replays each saved log, so a cached warning also fails it. Build freshness rests on Lake's traces, which are trusted.
:::

## Documentation as a Lean Teaching Surface
%%%
tag := "documentation-as-a-lean-teaching-surface"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[DOC-01]
  * Public declarations supporting material normative claims have docstrings stating their formal purpose, relevant assumptions, result, and invariant boundary; every other public definition has a docstring; every claimed module documents its material declarations and assumptions.
  * {ref "51-inline-documentation-requirements"}[5 §5.1–§5.3], {ref "67-community-conventions-and-linters"}[6 §6.7]
  * Compare the documented claims with elaborated types, definitions, and supporting contracts; a function type alone need not specify its input/output relationship. Check actual module docstrings in owned modules, and that each is present and is the first command after the imports (§5.3): the retired rule {rule}[RG5001] states this as written guidance, which no check of Regula reads. Review the required enablement of `linter.missingDocs` in every claimed target (`DECL-01`); {rule}[RG2006] does not check that enablement. When the linter is enabled, {rule}[RG2003] rejects each warning it emits for a public definition without a docstring.
*
  * {checklistRow}[DOC-02]
  * English explanations of normative Lean statements faithfully convey their quantifiers, hypotheses, conclusions, relevant definitions, and limitations, and identify the authoritative Lean declaration. Each public declaration supporting a material normative claim carries a nonempty labelled Intent section in its docstring.
  * {ref "52-faithful-explanation-of-formal-claims"}[5 §5.2]
  * Read the explanation with its referenced definitions; check quantifier order and dependence, domains, hypotheses, conclusion, and limits affecting interpretation. Distinguish results proved without additional hypotheses, results proved under explicit hypotheses, and open targets, retaining stated domains and foundations. Locate the supporting declaration (including through an attached docstring), and compare its elaborated meaning and its explanation with the written intent statement, the requirement-side record of the intended mathematics or program specification. Section presence is written guidance of the retired rule {rule}[RG5003], which no check of Regula reads; presence, adequacy of the intent and agreement with it are review.
*
  * {checklistRow}[DOC-03]
  * Every Lean fence in the normative documentation tree is classified by the fence protocol: an unmarked fence is a positive example, and an exact marker, when present, sits directly before the fence it classifies. Every fence is closed and opens and closes in the first column outside quotations, list items and other fences.
  * {ref "lean-example-convention"}[Set convention], {ref "77-check-lean-documentation-verbatim"}[7 §7.7]
  * Review every Markdown document of the tree against §7.7. The retired rule {rule}[RG4001] states this as written guidance, and no check of Regula reads a project's documentation.
*
  * {checklistRow}[DOC-04]
  * Every positive Lean fence elaborates exactly as printed, warning-free, and its declarations meet the declaration and axiom rules under Standard-Logical.
  * {ref "77-check-lean-documentation-verbatim"}[7 §7.7]
  * Elaborate each positive fence as printed, with no import or wrapper added, then check its declarations and their axioms. The retired rule {rule}[RG4002] states this as written guidance, which no check of Regula reads. Narrower foundation or execution claims require separate evidence.
*
  * {checklistRow}[DOC-05]
  * Every negative fence fails for its non-empty expected diagnostic, and every trusted-compiler teaching fence contains a compiler-trusting declaration and never counts as conforming.
  * {ref "77-check-lean-documentation-verbatim"}[7 §7.7]
  * Match the whole pattern within one error message of the negative fence, never across messages or against informational output. Inspect each teaching fence's declarations and their axioms. The retired rules {rule}[RG4003] and {rule}[RG4004] state these as written guidance, which no check of Regula reads.
:::

# Result Rule
%%%
tag := "result-rule"
number := false
%%%

A conformance conclusion MUST identify the audited surfaces, cite this matrix by ID, and state one terminal result:

* *PASS*: every applicable row has sufficient Lean-specific evidence;
* *FAIL*: at least one row is violated; or
* *INCOMPLETE*: no violation has been established, but required evidence is missing, unknown, skipped, unsupported, timed out, or still running.

When a violation and missing evidence coexist, report `FAIL` and identify both. A scoped review may report findings and evidence for selected rows, but it MUST state that scope and MUST NOT present those results as full conformance.

Applicability is determined only by the Lean-specific condition stated in the row, not by project preference. `INCOMPLETE` is not partial compliance and cannot support a conformance claim.
