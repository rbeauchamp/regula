import VersoManual
import RegulaExample
import RegulaStandard.CorePhilosophy
import RegulaStandard.CorePrinciples
import RegulaStandard.TypeDesignPatterns
import RegulaStandard.LogicProofPatterns
import RegulaStandard.MathematicalFoundations
import RegulaStandard.DocumentationStandards
import RegulaStandard.CodeOrganization
import RegulaStandard.PerformanceBestPractices
import RegulaStandard.ToolingAndMachineAudit
import RegulaStandard.ComplianceAudit
import RegulaStandard.CriticalViolations

open Verso.Genre Manual RegulaExample

#doc (Manual) "The Regula Standard" =>
%%%
tag := "standard"
file := "standard"
number := false
%%%

{pageAnchor}

This standard specifies requirements for mathematical proofs and verified functional programs in Lean.

# Introduction
%%%
tag := "standard-introduction"
file := "introduction"
number := false
%%%

{pageAnchor}

## Overview
%%%
tag := "standard-overview"
number := false
%%%

The numbered modules define requirements for Lean types, definitions, proofs, and the claims made about them. Begin with {ref "0-core-philosophy-precise-claims-and-kernel-checked-evidence"}[Core Philosophy], which explains what kernel-checked evidence establishes and where its guarantees end. {ref "9-compliance-and-quality-audit"}[Module 9] is the single audit checklist; its rows link to the modules that define each requirement and its rationale. The {repo "docs/guides/adoption.md"}[adoption guide] provides setup steps, supported pins, and audit commands.

## Scope
%%%
tag := "scope"
number := false
%%%

The standard covers dependent types, theorem statements, proofs, axioms, elaboration, modules, namespaces, and Lean computation. It also covers mathematical models, executable definitions, monadic and effectful programs, and metaprograms. Each claimed surface must satisfy the applicable declaration, foundation, and computation rules; the claim kinds in {ref "13-the-specificationmodel-firewall"}[module 1 §1.3] distinguish what the evidence concerns.

A complete executable component has explicit behavioral proof requirements tied to its actual Lean definitions. Types, proof-bearing constructions, and existing theorems may discharge those requirements. Semantic review must still confirm that the requirements express the intended behavior and cover the actual call paths. A logical foundation label alone does not establish execution correctness. To transfer a result to another formal representation, provide checked correspondence sufficient for that transfer. Applying a result to native execution or an external system retains the stated compiler, runtime, and external assumptions ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6], {ref "85-proof-completeness-and-foundation-strength"}[module 8 §8.5–§8.6]).

These Lean requirements are intended for systems where correctness is critical. The standard does not certify or guarantee any external system. It does not address development lifecycles, organizational processes, traceability frameworks, CI/CD platforms, supply-chain provenance, releases, risk waivers, or certification schemes.

## Document Structure
%%%
tag := "document-structure"
number := false
%%%

:::table +header
*
  * Module
  * Subject
*
  * {ref "0-core-philosophy-precise-claims-and-kernel-checked-evidence"}[0. Core Philosophy]
  * Kernel-checked claims, assumptions, non-vacuity, and the limits of the evidence.
*
  * {ref "1-core-principles"}[1. Core Principles]
  * Representational precision, theorem-backed behavior, mathematical modeling, and claim boundaries.
*
  * {ref "2-type-design-patterns"}[2. Type Design Patterns]
  * Semantic types, refined values, phantom tags, and abstract models.
*
  * {ref "3-logic-and-proof-patterns"}[3. Logic and Proof Patterns]
  * Exact contracts, lawful interfaces, proof economy, refinement, and research statements.
*
  * {ref "4-mathematical-foundations"}[4. Mathematical Foundations]
  * Numeric representations, mathematical structures, and exact logical foundation profiles.
*
  * {ref "5-documentation-standards"}[5. Documentation Standards]
  * Faithful explanations of formal claims and useful declaration and module documentation.
*
  * {ref "6-code-organization"}[6. Code Organization]
  * Dependencies, namespaces, imports, visibility, and abstraction boundaries.
*
  * {ref "7-performance-best-practices"}[7. Performance Best Practices]
  * Representations, ownership, traversal, proof erasure, and conditional performance guidance.
*
  * {ref "8-tooling-and-machine-audit"}[8. Tooling and Machine Audit]
  * Elaboration, declaration and execution coverage, foundation checks, and checker qualification.
*
  * {ref "9-compliance-and-quality-audit"}[9. Compliance and Quality Audit]
  * The single checklist of applicable requirements and their verification.
:::

{ref "critical-violations-to-check-first"}[Critical Violations] lists issues that require immediate attention. The absence of a listed issue does not establish that a component conforms to the standard.

## Lean Example Convention
%%%
tag := "lean-example-convention"
number := false
%%%

The standard's Lean examples are Verso code blocks of its source, the `RegulaStandard` library of the Verso package in `website/`. This repository's documentation audit covers them completely, together with every `lean` fence of the Markdown below `docs/` (the guides, which scanning does not make normative). An explicit `--docs-root` or `--verso` option selects another audit scope, so a result must identify the scope it covers.

Every `lean` block is one complete Lean module with its own imports. Whenever the standard is built, it is elaborated where it is written, in a fresh environment containing exactly those imports; the audit then checks the same text as follows.

* *Unmarked `lean` block:* a positive elaboration example. It must first elaborate exactly as printed, with its own imports and no checker imports or wrappers inserted. The resulting module and its owned logical dependencies first pass completed kernel admission (§8.3); the module is then checked under the declaration policy with the Standard-Logical axiom allowance. Emitted warnings, proof holes, project or unknown axioms, compiler-trusting proof axioms, and forbidden declarations fail this check. The narrowly authenticated recursive-helper exception remains as specified in module 8 §8.4. A narrower foundation claim or an execution-correspondence claim requires separate evidence.
* *`lean (fails := "PATTERN")` block:* an expected elaboration failure. The nonempty pattern must be valid, the frontend must complete with source rejection, and one effective-error message must match the entire pattern. The restricted grammar supports `|` alternatives and `.*` between ordered literal fragments; it is not general regular-expression syntax. Unsupported syntax and empty fragments are rejected. The complete grammar and matching rules are in {ref "87-check-lean-documentation-verbatim"}[module 8 §8.7].
* *`lean +trustedCompiler` block:* an example of a compiler-trusting proof mechanism, such as `native_decide`. The example must elaborate warning-free and receive the required compiler-trusting classification. Such examples are not included in conforming positive proof surfaces or in the three logical foundation labels.
* *`leanSketch`, `text` or another non-Lean block:* pseudocode, a multi-file sketch, or tool output. It carries no claim that the displayed text elaborates as Lean; a `leanSketch` block says so where it is shown.

A positive example's result establishes the specified elaboration and declaration checks. It does not prove that the example satisfies its intended specification or every other rule. A valid Lean program may illustrate a semantic defect; the explanation must identify that defect. Use a negative example when claiming that Lean rejects the printed code for the stated diagnostic.

Any other code-block spelling (an unnamed block, or an unknown name or argument), an invalid diagnostic pattern, a Lean block that does not open in the first column, and an unclosed block fail the audit; {ref "87-check-lean-documentation-verbatim"}[module 8 §8.7] specifies the Markdown fence protocol with the same three kinds and its scanner requirements. `lean/Audit/` contains checked definitions and proofs supporting representative claims; `lean/Fixtures/` contains isolated controls and mutations. Their evidence scope is specified in {ref "8-tooling-and-machine-audit"}[module 8].


## Quick Start
%%%
tag := "quick-start"
number := false
%%%

1. Read {ref "0-core-philosophy-precise-claims-and-kernel-checked-evidence"}[Core Philosophy] for the meaning and limits of the evidence.
2. Use {ref "critical-violations-to-check-first"}[Critical Violations] for initial triage.
3. Read the chapters applicable to the claims you are making and complete {ref "9-compliance-and-quality-audit"}[the audit matrix]. Checker results do not replace its semantic review obligations.
4. Follow the {repo "docs/guides/adoption.md"}[adoption guide] to configure and run the checker in your project.

## Requirement Keywords
%%%
tag := "requirement-keywords"
number := false
%%%

Throughout this standard, uppercase requirement keywords carry the meanings defined in [RFC 2119](https://www.rfc-editor.org/rfc/rfc2119.html):

* *MUST / REQUIRED / SHALL:* a condition that conformance requires.
* *MUST NOT / SHALL NOT:* a prohibited condition or action.
* *SHOULD / RECOMMENDED:* the expected choice; departing from it needs a valid technical reason and consideration of the consequences.
* *SHOULD NOT / NOT RECOMMENDED:* a choice to avoid unless a valid technical reason and consideration of the consequences support it.
* *MAY / OPTIONAL:* a choice the standard permits. When an optional claim is made, its applicable requirements must still be met.

Formal Lean statements claimed as conforming SHALL elaborate on the declared toolchain. Their explanations SHALL preserve the quantifiers, assumptions, conclusions, and relevant definitions without strengthening the result ({ref "52-faithful-explanation-of-formal-claims"}[module 5 §5.2]). Kernel acceptance and fidelity to the intended claim are distinct obligations. Elaborating a `Prop`-valued definition establishes its statement, not a proof of that proposition. Every material result presented as established requires the checked evidence specified in module 0.

## Mathlib Reuse and Foundation Profiles
%%%
tag := "mathlib-reuse-and-foundation-profiles"
number := false
%%%

Mathematical concepts MUST use or extend Mathlib’s canonical definitions where they fit the intended concept. Custom definitions require a precise statement and an explanation of why no existing definition fits. {ref "14-principled-mathematical-modeling"}[Module 1 §1.4] defines this rule and its rationale; it does not require domain concepts to belong in Mathlib.

Library reuse and logical foundation strength are separate questions. {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[Module 4 §4.5] defines Kernel-only, Choice-Free, and Standard-Logical by their permitted axiom sets. The label comes from a declaration’s exact transitive dependencies, not from its library or tactic name, and does not rank overall software assurance. For an admissible set, the actual label is the least containing profile; the selected surface profile is an allowed maximum. Forbidden and compiler-trusting axioms remain excluded from conforming positive proofs.

{include 1 RegulaStandard.CorePhilosophy}

{include 1 RegulaStandard.CorePrinciples}

{include 1 RegulaStandard.TypeDesignPatterns}

{include 1 RegulaStandard.LogicProofPatterns}

{include 1 RegulaStandard.MathematicalFoundations}

{include 1 RegulaStandard.DocumentationStandards}

{include 1 RegulaStandard.CodeOrganization}

{include 1 RegulaStandard.PerformanceBestPractices}

{include 1 RegulaStandard.ToolingAndMachineAudit}

{include 1 RegulaStandard.ComplianceAudit}

{include 1 RegulaStandard.CriticalViolations}
