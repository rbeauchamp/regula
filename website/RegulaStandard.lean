import VersoManual
import RegulaExample
import RegulaStandard.PreciseClaims
import RegulaStandard.CorePrinciples
import RegulaStandard.TypeDesignPatterns
import RegulaStandard.LogicProofPatterns
import RegulaStandard.MathematicalFoundations
import RegulaStandard.DocumentationStandards
import RegulaStandard.CodeOrganization
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

*Public review draft; not affiliated with the Lean FRO or Mathlib.*

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

The numbered modules define requirements for Lean types, definitions, proofs, and the claims made about them. {ref "0-precise-claims-and-kernel-checked-evidence"}[Module 0] states the fundamental requirement and what kernel-checked evidence establishes; {ref "8-compliance-and-quality-audit"}[module 8] is the single audit checklist, whose rows link to the modules that define each requirement and its rationale. The {repo "docs/guides/adoption.md"}[adoption guide] sets up and runs the checker.

## Scope
%%%
tag := "scope"
number := false
%%%

The standard covers dependent types, theorem statements, proofs, axioms, elaboration, modules, namespaces, and Lean computation. It also covers mathematical models, executable definitions, monadic and effectful programs, and metaprograms. Each claimed surface must satisfy the applicable declaration, foundation, and computation rules; the claim kinds in {ref "13-the-specificationmodel-firewall"}[module 1 §1.3] distinguish what the evidence concerns.

A complete executable component has explicit behavioral proof requirements tied to its actual Lean definitions. Types, proof-bearing constructions, and existing theorems may discharge those requirements. Semantic review must still confirm that the requirements express the intended behavior and cover the actual call paths. A logical foundation label alone does not establish execution correctness. To transfer a result to another formal representation, provide checked correspondence sufficient for that transfer. Applying a result to native execution or an external system retains the stated compiler, runtime, and external assumptions ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6], {ref "75-proof-completeness-and-foundation-strength"}[module 7 §7.5–§7.6]).

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
  * {ref "0-precise-claims-and-kernel-checked-evidence"}[0. Precise Claims and Kernel-Checked Evidence]
  * The fundamental requirement, the elaborator/kernel/compiler trust model, non-vacuity, and the limits of the evidence.
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
  * {ref "7-tooling-and-machine-audit"}[7. Tooling and Machine Audit]
  * Elaboration, declaration and execution coverage, foundation checks, and checker qualification.
*
  * {ref "8-compliance-and-quality-audit"}[8. Compliance and Quality Audit]
  * The single checklist of applicable requirements and their verification.
:::

{ref "critical-violations-to-check-first"}[Critical Violations] lists issues for initial triage. The absence of a listed issue does not establish that a component conforms to the standard.

## Lean Example Convention
%%%
tag := "lean-example-convention"
number := false
%%%

Every `lean` block of this standard is one complete Lean module with its own imports. When the standard is built, each block is elaborated where it is written, in a fresh environment containing exactly those imports, with `autoImplicit` and `relaxedAutoImplicit` off ({ref "71-declare-the-elaboration-environment"}[module 7 §7.1]) and Lean's `linter.missingDocs` on ({ref "67-community-conventions-and-linters"}[module 6 §6.7]). Every line of every code block is at most 100 characters, the community's line limit; a longer line fails the build of the standard. The documentation audit ({ref "77-check-lean-documentation-verbatim"}[module 7 §7.7]) checks each block by its kind:

* *Unmarked `lean` block:* a positive elaboration example. It must first elaborate exactly as printed, with its own imports and no checker imports or wrappers inserted. The resulting module and its owned logical dependencies first pass completed kernel admission (§7.3); the module is then checked under the declaration policy with the Standard-Logical axiom allowance. Emitted warnings, proof holes, project or unknown axioms, compiler-trusting proof axioms, and forbidden declarations fail this check. The narrowly authenticated recursive-helper exception remains as specified in §7.4. A narrower foundation claim or an execution-correspondence claim requires separate evidence.
* *`lean (fails := "PATTERN")` block:* an expected elaboration failure. The nonempty pattern must be valid, the frontend must complete with source rejection and no warning, and one effective-error message must match the entire pattern under the restricted grammar of §7.7 (`|` alternatives and `.*` between ordered literal fragments, not general regular-expression syntax). The page shows such a block under the verdict *Rejected by Lean, as intended*, followed by the error message that matched its pattern.
* *`lean +trustedCompiler` block:* an example of a compiler-trusting proof mechanism, such as `native_decide`, `decide +native`, or `bv_decide`. The example must elaborate warning-free and receive the required compiler-trusting classification. Such examples are not included in conforming positive proof surfaces or in the three logical foundation labels.
* *`leanSketch`, `text` or another non-Lean block:* pseudocode, a multi-file sketch, or tool output. It carries no claim that the displayed text elaborates as Lean; a `leanSketch` block says so where it is shown.

Any other code-block spelling (an unnamed block, or an unknown name or argument), an invalid diagnostic pattern, a Lean block that does not open in the first column, and an unclosed block fail the audit. §7.7 specifies the same three kinds as a Markdown fence protocol.

A positive example establishes the specified elaboration and declaration checks. It does not prove that the example satisfies its intended specification or every other rule: a valid Lean program may illustrate a semantic defect, which the explanation must identify. Use a negative example to claim that Lean rejects the printed code.

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

{include 1 RegulaStandard.PreciseClaims}

{include 1 RegulaStandard.CorePrinciples}

{include 1 RegulaStandard.TypeDesignPatterns}

{include 1 RegulaStandard.LogicProofPatterns}

{include 1 RegulaStandard.MathematicalFoundations}

{include 1 RegulaStandard.DocumentationStandards}

{include 1 RegulaStandard.CodeOrganization}

{include 1 RegulaStandard.ToolingAndMachineAudit}

{include 1 RegulaStandard.ComplianceAudit}

{include 1 RegulaStandard.CriticalViolations}
