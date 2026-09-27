import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "9. Compliance and Quality Audit" =>
%%%
tag := "9-compliance-and-quality-audit"
file := "9-compliance-audit"
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

Applicability follows the stated technical condition. `MUT-01`–`MUT-04` apply to checker qualification claims under §8.8, with new execution required only for affected capabilities whose evidence is invalidated; `MUT-05` applies to a claimed separate serialized-graph check; `BUILD-*` applies to an enabled enforcing-build claim; and `DOGFOOD-*` applies only to this standards repository. A conditional row passes when its condition is absent and that reason is recorded, or when every applicable occurrence conforms. An absent condition is not evidence that the corresponding checks ran.

This checklist does not address project management or general software assurance. It audits dependent types, theorem statements, proof terms, axioms, elaboration, modules, Lean computation mechanisms, and Lean documentation claims.

# Audit Matrix
%%%
tag := "audit-matrix"
number := false
%%%

Assess each row against the actual claimed surface. The verification column includes both direct surface evidence and controls that qualify the supporting checker. Entries marked *Qualification* follow {ref "88-qualify-checker-implementations-with-independent-mutations"}[§8.8]: qualification evidence is scoped to the detection implementation, supported toolchain, and invocation behavior it exercised. Reuse requires establishing that a change does not invalidate that evidence; version identity alone is neither necessary nor sufficient. The matrix defines required results, not 53 separate commands or repeated review assignments. Such evidence does not replace inspection of the current surface or semantic review of its claims. A new or changed advertised detection capability requires its applicable qualification. An adopter does not rerun an unchanged checker’s entire suite for each audit.

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
  * {ref "13-the-specificationmodel-firewall"}[1 §1.3], {ref "36-contracts-for-executable-and-effectful-mechanisms"}[3 §3.6], {ref "86-classify-lean-computation-mechanisms-exactly"}[8 §8.6]
  * Enumerate the claimed surfaces and material claims. Reconcile the executable roots and boundary accounts under `COMP-03`, including additional registered roots under `BUILD-03` where applicable.
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
  * {ref "the-role-of-testing"}[0: role of testing], {ref "322-property-based-testing-as-refutation-aid"}[3 §3.2.2], {ref "88-qualify-checker-implementations-with-independent-mutations"}[8 §8.8]
  * Reject proof claims supported only by samples, unchecked enumeration, `#eval`, or native output. Kernel-checked exhaustive finite proofs and checked existential witnesses are proof evidence. Checker qualification under §8.8 is diagnostic evidence about the tool, not proof of the audited mathematics.
*
  * {checklistRow}[THEOREM-07]
  * Material functional contracts state the component’s exact input/output meaning, rejection and normalization behavior, intended updates and frames, state/error composition, and promised fold relation where applicable. Admission completeness is proved when promised.
  * {ref "37-a-compositional-method-for-complete-program-contracts"}[3 §3.7]
  * Inspect the actual executable definitions and the relations their contracts require. Check intermediate preconditions and the claimed success, error, and effect semantics. Reuse types, construction, library results, or another checked argument; initialization and preservation are required when the chosen argument needs them. Rule out degenerate implementations that violate the promised relation. Separate finite totality and partial correctness from external liveness.
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
  * {ref "34-foundation-strength-axioms-are-reported-never-assumed"}[3 §3.4], {ref "85-proof-completeness-and-foundation-strength"}[8 §8.5]
  * Inspect every owned `ConstantInfo`, including unused, private, internal-looking, and generated declarations.
*
  * {checklistRow}[FOUND-02]
  * No owned declaration depends transitively on `sorryAx`; no `sorry` or `admit` survives under alternate syntax, attributes, definitions, or instances.
  * {ref "11-the-principle-of-representational-precision"}[1 §1.1], {ref "85-proof-completeness-and-foundation-strength"}[8 §8.5]
  * Compute transitive axiom sets for every owned declaration, including proof-valued definitions and instances. Qualification: adversarial hole mutations cover all advertised declaration forms.
*
  * {checklistRow}[FOUND-03]
  * Every owned declaration has its exact transitive axiom set reported. An admissible set receives the least permissive logical label containing it; the selected surface profile is an upper bound. Forbidden and compiler-trusting sets are rejected from conforming positive surfaces.
  * {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[4 §4.5], {ref "85-proof-completeness-and-foundation-strength"}[8 §8.5]
  * Compare the computed set with `{}`, `{propext, Quot.sound}`, and that set plus `Classical.choice`; unknown axioms fail. The actual proof's dependencies do not establish minimal axioms among all possible proofs of its proposition.
*
  * {checklistRow}[FOUND-04]
  * No Choice-Free surface depends directly or transitively on `Classical.choice`; a selected Standard-Logical surface may.
  * {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[4 §4.5]
  * Inspect the transitive sets for the selected surface profile. Qualification: direct and transitive choice mutations fail the Choice-Free claim; a positive Standard-Logical control passes with its exact label.
*
  * {checklistRow}[FOUND-05]
  * Native/compiler-generated proof axioms are classified separately and rejected from the conforming positive proof surface; final-environment metadata alone cannot spoof the classification.
  * {ref "85-proof-completeness-and-foundation-strength"}[8 §8.5–§8.6]
  * Inspect generated proof axioms and dependent declarations; require exact semantic shape and native replay plus fresh built-in frontend attribution for the compiler-trusting classification. Qualification: distinguish a real native proof, a native-looking project axiom, and a custom frontend forging the final semantic shape.
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
  * Every exact module in each claimed Lake library and every claimed standalone executable root is discovered and elaborated from source in fresh root-package build state, warning-free, under the declared exact elaboration environment with the community linters of §6.7 enabled, with completed owned logical declaration and dependency admission under §8.3.
  * {ref "81-declare-the-elaboration-environment"}[8 §8.1–§8.3], {ref "62-module-purpose-and-linter-discipline"}[6 §6.2], {ref "67-community-conventions-and-linters"}[6 §6.7]
  * Read the elaborated Lake library module arrays and executable roots. Import every claimed module and reconcile exact attribution and additional root-owned imports. Record toolchain and dependency source state; reject emitted warnings and stale root-package artifacts. Dependency artifacts may be reused under §8.3. The `modules` facet can include local imports beyond the configured array; it is a cross-check, not an interchangeable inventory. Check the Lake options of every claimed library and executable (RG2006): `autoImplicit` and `relaxedAutoImplicit` off (§8.1), `linter.missingDocs` on (§6.7), no linter turned off for a whole target beyond the §6.7 exclusions (§6.2), and, when the surface imports Mathlib, `weak.linter.mathlibStandardSet` with exactly those exclusions, with no `-D` among the extra `lean` arguments setting any of these options otherwise. Review what the audit cannot see: no claimed module sets `autoImplicit` or `relaxedAutoImplicit` back on in source; no claimed module disables a Lean default warning; and each disabled community linter is declaration-scoped with a stated reason (§6.2).
*
  * {checklistRow}[DECL-02]
  * Every constant in every owned module is inventoried; proof-valued definitions and instances are not omitted.
  * {ref "84-inventory-every-owned-declaration"}[8 §8.4]
  * Compare environment constant counts and exact names; classify `isProp` from the elaborated type and validate the trusted-runner report. Qualification includes an audited module registering a colliding observer-command token.
*
  * {checklistRow}[DECL-03]
  * Ownership uses Lean/Lake semantics. Generated-role exceptions require fresh frontend attribution and the exact semantic relationship in §8.4–§8.5; names or forgeable final metadata alone cannot authorize them.
  * {ref "82-define-surfaces-through-lake-semantics"}[8 §8.2], {ref "84-inventory-every-owned-declaration"}[8 §8.4]
  * Inspect ownership and every claimed exception. Qualification: exact-prefix lookalikes, private and auxiliary-looking names, native-name spoofs, custom-command `addDecl`, and nested-`run_tac` generated-role forgeries receive their intended classification or rejection.
*
  * {checklistRow}[DECL-04]
  * Missing/malformed manifests, unknown metadata, omitted declarations, and unexpected project modules fail closed.
  * {ref "82-define-surfaces-through-lake-semantics"}[8 §8.2–§8.4]
  * Validate the manifest and report schemas and reconcile targets, modules, and declarations. Qualification: mutate each advertised configuration/coverage failure independently and require its intended diagnostic, including observer-command collisions.
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
  * {ref "324-decidability-logical-vs-executable"}[3 §3.2.4], {ref "86-classify-lean-computation-mechanisms-exactly"}[8 §8.6]
  * Inspect metadata and axiom sets; check representative reduction/evaluation behavior on the pinned toolchain.
*
  * {checklistRow}[COMP-02]
  * Partial and unsafe declarations are excluded from positive proof surfaces, except for the range-less partial code-generation helper admitted under the exact semantic and fresh frontend conditions in §8.4 for a safe recursive `def`.
  * {ref "84-inventory-every-owned-declaration"}[8 §8.4–§8.6]
  * Inspect `ConstantInfo.isUnsafe`/`isPartial` and every helper exception. Qualification: safe recursion, explicit `termination_by`, and namespaced well-founded recursion pass; authored helper-name spoofs, custom full-metadata and evaluator forgeries, partial definitions, unsafe definitions, and unsafe opaque declarations receive the intended rejection.
*
  * {checklistRow}[COMP-03]
  * Every boundary in the §8.6 conservative execution closure has its exact kind and correspondence state reported; retained compiler edges are distinguished from candidates and historical choices. In `"execution": "checked"` mode, every non-native-runtime boundary in that closure is checked. Unresolved paths block the affected execution claim in every mode.
  * {ref "86-classify-lean-computation-mechanisms-exactly"}[8 §8.6]
  * Reconcile all executable roots and their closures, retained IR, supported histories, boundaries, and exact admitted correspondence proofs over the full dependent domain and universes. Qualification covers legitimate and insufficient equalities, imported/chained/both-order replacements, local and overwritten histories, inlined targets, extern/unsafe/partial paths, and cycles or unsupported histories. A definitional comparison the kernel could not complete is unresolved, never trusted; only a completed negative comparison without another admitted proof leaves a replacement trusted. Observing a diagnostic target in emitted code qualifies discovery, not compiler or external-code correctness.
*
  * {checklistRow}[COMP-04]
  * Transfer from a Lean reference definition to a replacement requires sufficient checked correspondence. Keep remaining trust assumptions for native and external execution explicit.
  * {ref "86-classify-lean-computation-mechanisms-exactly"}[8 §8.6]
  * Compare each theorem’s exact statement and dependencies with the claimed computation and admitted relation. A relation between Lean definitions does not itself verify external machine code or discharge reached extern/native boundaries.
:::

## Opt-in Enforcing Build Integration
%%%
tag := "opt-in-enforcing-build-integration"
number := false
%%%

These rows apply when the §8.12 build-enforcement claim is made. The other applicable rows remain required for full conformance; a build-linter PASS alone does not discharge them.

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[BUILD-01]
  * The documented enabled ordinary `lake build`, and `lake lint` with the `lint` driver, reject every emitted warning, policy violation, and unresolved claimed execution path. Source-local warning/linter options cannot authorize policy exceptions.
  * {ref "812-opt-in-enforcing-build-linter"}[8 §8.12]
  * Run the enabled ordinary build or `lake lint` for the claimed adopter configuration. Qualification drives the actual default policy target, including disabled and re-enabled controls, intended diagnostics, and fresh restoration, and drives `lake lint` in both lakefile formats through every exit class; any other adapter needs corresponding qualification.
*
  * {checklistRow}[BUILD-02]
  * Declared profiles are transitively enforced, with classical erased proofs permitted under Standard-Logical and executable promises checked separately.
  * {ref "38-delivering-executable-witnesses-with-required-evidence"}[3 §3.8], {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[4 §4.5]
  * Inspect current profile and execution results separately. Qualification: all three positive profiles, direct/imported choice and configuration-change failures, a classical-contract positive, and noncomputable witness rejection.
*
  * {checklistRow}[BUILD-03]
  * Required executable evidence inhabits the exact predicate of the actual named implementation, and registered private/imported roots retain execution coverage.
  * {ref "812-opt-in-enforcing-build-linter"}[8 §8.12]
  * Inspect registered predicates, proof-bearing construction, and actual callers. Reconcile additional private/imported roots and review specification adequacy. Qualification mutates missing, unrelated, or weakened evidence and unsupported registrations, and exercises private/extern, replacement, imported csimp, and unsafe boundaries.
*
  * {checklistRow}[BUILD-04]
  * Cached modules and changed configuration cannot reuse a stale policy verdict; exact claimed Lake coverage and supported-context limits are explicit.
  * {ref "812-opt-in-enforcing-build-linter"}[8 §8.12]
  * Inspect target/job dependencies and the current manifest and report. Qualification covers unimported glob modules, unclassified targets, imported source and cached profile/execution changes, repeated cached failures, and fresh restoration. Incremental evidence does not establish fresh-source conformance.
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
  * Compare the documented claims with elaborated types, definitions, and supporting contracts; a function type alone need not specify its input/output relationship. Check actual module docstrings in owned modules; RG5001 checks that each is present and is the first command after the imports (§5.3). RG2006 checks that every claimed target enables `linter.missingDocs` (`DECL-01`), so that RG2003 rejects every public definition it reports without a docstring.
*
  * {checklistRow}[DOC-02]
  * English explanations of normative Lean statements faithfully convey their quantifiers, hypotheses, conclusions, relevant definitions, and limitations, and identify the authoritative Lean declaration. Each public declaration supporting a material normative claim carries a nonempty labelled Intent section in its docstring.
  * {ref "52-faithful-explanation-of-formal-claims"}[5 §5.2]
  * Read the explanation with its referenced definitions; check quantifier order and dependence, domains, hypotheses, conclusion, and limits affecting interpretation. Distinguish results proved without additional hypotheses, results proved under explicit hypotheses, and open targets, retaining stated domains and foundations. Locate the supporting declaration (including through an attached docstring), and compare its elaborated meaning and its explanation with the written intent statement, the requirement-side record of the intended mathematics or program specification. Section presence is mechanical; adequacy of the intent and agreement with it are semantic review. A screened (probabilistic) judgment of that agreement does not complete this row.
*
  * {checklistRow}[DOC-03]
  * Every Lean fence in the normative documentation tree (here every `lean` block of the standard's Verso source, `website/RegulaStandard`) is structurally classified; malformed markers/fences fail closed.
  * {ref "lean-example-convention"}[Set convention], {ref "87-check-lean-documentation-verbatim"}[8 §8.7]
  * Recursively scan the complete normative tree. Qualification mutates every malformed marker/fence state specified in §8.7.
*
  * {checklistRow}[DOC-04]
  * Every positive Lean fence elaborates exactly as printed, warning-free, then passes owned logical admission and declaration/axiom classification.
  * {ref "87-check-lean-documentation-verbatim"}[8 §8.7]
  * Elaborate raw source first; inspect the elaborated temporary module without injecting imports into the claimed source. The shipped fence checker uses Standard-Logical; narrower foundation or execution claims require separate evidence.
*
  * {checklistRow}[DOC-05]
  * Every negative fence fails for its non-empty expected diagnostic, and trusted-compiler teaching fences are classified but never counted as conforming.
  * {ref "87-check-lean-documentation-verbatim"}[8 §8.7]
  * Require a completed diagnostic-worker result and the whole pattern within one effective-error message, preserving multiline text and rejecting cross-message or informational matches. Inspect trusted declarations and their generated axioms.
:::

## Checker Implementation Qualification
%%%
tag := "checker-implementation-qualification"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[MUT-01]
  * A checker that classifies foundation profiles has positive controls for all three profiles through its actual detection implementation, with public-path qualification as required by §8.8.
  * {ref "88-qualify-checker-implementations-with-independent-mutations"}[8 §8.8]
  * For new or affected foundation-classification behavior, exercise the relevant positive profiles through the actual detection path; retain applicable evidence for other profiles.
*
  * {checklistRow}[MUT-02]
  * A checker implementation has an independent intended-reason mutation for every violation class it advertises.
  * {ref "88-qualify-checker-implementations-with-independent-mutations"}[8 §8.8]
  * Select intended-reason controls for affected advertised capabilities under §8.8. A complete-campaign claim additionally requires its complete applicable manifest. Reject masked or wrong-reason failures.
*
  * {checklistRow}[MUT-03]
  * A checker qualification harness cannot overwrite positive sources or leave stale Lean artifacts, and its restored control passes fresh.
  * {ref "83-clean-elaboration-and-diagnostics"}[8 §8.3], {ref "88-qualify-checker-implementations-with-independent-mutations"}[8 §8.8]
  * In a qualification run, use unique disposable paths/build state; verify red mutation and fresh restored green.
*
  * {checklistRow}[MUT-04]
  * Checker qualification establishes a fresh warning-free configured-module baseline and keeps mutation artifacts from satisfying restored controls.
  * {ref "83-clean-elaboration-and-diagnostics"}[8 §8.3], {ref "88-qualify-checker-implementations-with-independent-mutations"}[8 §8.8]
  * In a qualification run, use empty or isolated root-package output and reject every emitted warning. Share the unchanged baseline where valid; mutations may use isolated incremental rebuilds, with fresh restored controls under §8.8.
*
  * {checklistRow}[MUT-05]
  * When separate serialized-graph checking is claimed, the exact claimed module graph is rechecked in a compatible fresh checker state.
  * {ref "89-optional-fresh-serialized-graph-checking"}[8 §8.9]
  * Require successful results for every selected root. Reconcile the union of claimed modules in their import closures with the exact Lake inventory. Qualification covers root selection and additional-module coverage. Distinguish the driver’s incremental artifact build from its fresh checker state; it does not establish fresh-source elaboration.
:::

## This Repository's Dogfooding and Internal Consistency
%%%
tag := "this-repositorys-dogfooding-and-internal-consistency"
number := false
%%%

:::table +header
*
  * ID
  * Required result
  * Normative source
  * Required Lean-specific verification
*
  * {checklistRow}[DOGFOOD-01]
  * The repository's own claimed Lean surfaces — the `Audit` library of mathematical models, proofs, and executable examples and the `AuditApp` complete application with its standalone `Main` executable root — satisfy every applicable row above.
  * {ref "810-dogfooding"}[8 §8.10]
  * Audit each claimed Lake surface as an ordinary claimed surface with no special exemptions; the application's admission, update, and composition contracts are proved about the same computable definitions its executable runs, and its `IO` boundary is reported, never silently excluded.
*
  * {checklistRow}[DOGFOOD-02]
  * Intentionally invalid fixtures are isolated from the positive elaborated environment.
  * {ref "82-define-surfaces-through-lake-semantics"}[8 §8.2], {ref "810-dogfooding"}[8 §8.10]
  * Reconcile exact imported project modules. Qualification includes a contamination mutation.
*
  * {checklistRow}[DOGFOOD-03]
  * Normative prose, representative Lean fixtures, checker diagnostics, and status text make no stronger claim than the same verified property.
  * {ref "16-claim-boundaries-and-automated-checking"}[1 §1.6], {ref "810-dogfooding"}[8 §8.10]
  * Compare advertised capabilities with the checked implementation and applicable qualification evidence. Diagnostic qualification does not prove the checker is universally correct.
*
  * {checklistRow}[DOGFOOD-04]
  * Examples and fixtures reuse or extend matching Lean/Mathlib mathematical definitions. Custom mathematical definitions state their meaning and why existing definitions do not fit; proofs follow the economy guidance in §3.2.5.
  * {ref "14-principled-mathematical-modeling"}[1 §1.4], {ref "325-proof-economy-four-cost-domains-and-one-trust-question"}[3 §3.2.5]
  * Compare custom mathematical structures, classes, and aliases with the pinned libraries and inspect required justifications. Review proof reuse where it simplifies the argument. A domain definition or teaching proof does not need a claim that no library theorem exists.
*
  * {checklistRow}[DOGFOOD-05]
  * The complete application enforces its explicit required propositions: omitting executable classification, removing or weakening required evidence while its proposition remains, or weakening admission fails the gate. Semantic review rejects a narrowed requirement set or bypassed application linkage.
  * {ref "88-qualify-checker-implementations-with-independent-mutations"}[8 §8.8], {ref "810-dogfooding"}[8 §8.10]
  * Inspect `RequiredContracts`, its evidence, and `Main`’s call through `checked_executable.run` to `executeChecked` for adequacy and completeness. The diagnostic campaign includes `app-omitted-exe`, `app-unproved-update`, `app-trivial-update`, `app-weakened-update`, `app-missing-contract-field`, and `app-weakened-admission`, each with its intended diagnostic and a fresh restored control.
:::

# Repository Verification Sequence
%%%
tag := "repository-verification-sequence"
number := false
%%%

For this repository's ordinary settled-snapshot conformance check, use {repo "scripts/verify.sh"}[the local verification entrypoint] twice:

```sh
./scripts/verify.sh
./scripts/verify.sh docs
```

The first builds the checker tools, runs the fresh declaration gate over every claimed surface and records the content identity of the inputs it accepted. The second audits the complete documentation tree, including every `lean` block of this standard's Verso source, which it also builds fresh and renders, and refuses unless its own freshly captured inputs have that identity; `DOC-*` rows need both. Their repository-specific deadlines and provisioning requirements live in {repo "docs/guides/contributing.md"}[the contributor guide]. The declaration gate performs Lake-semantic discovery and a clean, warning-free build before inspection; a redundant preliminary clean build is unnecessary. `lake build` remains the development command.

Checker changes require focused verification of affected capabilities and public invocation paths under §8.8. The complete `checkerSelftest --build-bound` campaign remains available when broad diagnostic qualification is requested or justified by affected mechanisms; it is not the ordinary per-change conformance gate. A selected diagnostic that fails remains a defect; an unrun broader campaign is not reported as passed. Repository diagnostics use the same bounded entrypoint, for example:

```sh
./scripts/verify.sh diagnostics fixtures
```

When making the optional serialized-graph claim, obtain fresh checker-state evidence for the exact claimed graph. Run the driver when that graph, claim, or driver changes. Reuse equivalent coverage already obtained for the same inputs rather than repeating the same roots in a raw invocation:

```sh
lake exe freshChecker --verbose
```

The applicable command evidence is required but does not complete the matrix. Theorem, type, and prose rows still require semantic review. Record the Lean version, exact dependency source state (including Mathlib when present), claimed Lake modules, declaration coverage and exact axiom results, execution boundaries, applicable fence and checker-qualification results, and any failures or missing evidence. A required check that was skipped leaves its affected row or optional claim `INCOMPLETE`; it cannot support conformance.

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
