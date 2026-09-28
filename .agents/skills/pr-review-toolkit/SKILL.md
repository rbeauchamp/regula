---
name: pr-review-toolkit
description: Review Regula diffs, proof claims, and conformance; use for requested reviews and repository delivery review.
---

# Regula Review Toolkit

Determine whether the scoped claims follow from the Lean definitions, proofs, and checker
evidence. [AGENTS.md](../../../AGENTS.md) owns repository workflow and verification policy;
the [compliance checklist](../../../website/RegulaStandard/ComplianceAudit.lean) of the reviewed
revision owns normative rows ([published copy](https://rbeauchamp.github.io/regula/dev/standard/8-compliance-audit/)
of the last deployed `main`).

## Select the review

- **Diff or delivery review:** cover changed claims and dependencies, including baseline
  defects that contradict the claimed result. Use [review and closure](references/review-workflow.md).
- **Conceptual documentation review:** use the relevant [semantic-fidelity lenses](references/lean-lens-contracts.md),
  especially D; distinguish changed requirements from teaching improvements.
- **Full conformance:** reconcile every applicable checklist row over every claimed surface,
  using the workflow and relevant lenses. A scoped clean review is not full conformance.
- **Assigned reviewer:** inspect only the assigned frozen subject with the relevant lenses;
  return findings and coverage without editing or recursively coordinating reviewers.

Read only the references and normative modules needed for the selected scope. For non-Lean
administrative changes, inspect their actual instruction and link effects.

## Completion

Review-only work ends with findings, coverage, and unresolved evidence. Authorized repair
work includes fixes, affected checks, and independent verification under AGENTS.md. Report
what remains blocked; do not broaden a claim to match a green command. Complete external
steps only within current authorization, including any explicit user stopping point.
