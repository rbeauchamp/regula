import MathlibAudit.Basic
import MathlibAudit.DocPrelude
import MathlibAudit.DocClaims
import MathlibAudit.Economy
import MathlibAudit.Models
import MathlibAudit.Refinement
import MathlibAudit.Research

/-!
# Mathlib integration surface umbrella

Umbrella for the complete positive `MathlibAudit` Lake surface: the Mathlib-specific
behaviour Regula supports, checked on a real Mathlib adopter of the `regula` package. It
imports `MathlibAudit.Basic` (Mathlib's `Even` in a subtype), `MathlibAudit.DocPrelude`
and `MathlibAudit.DocClaims` (real-valued time, the exponential decay theorem and orders
lifted by `LinearOrder.lift'`), `MathlibAudit.Economy` (a `ring` proof and a lawful mixin
over `ℝ`), `MathlibAudit.Models` (Mathlib's unit interval, ordered-algebra mixins, real
exponential growth and the real metric), `MathlibAudit.Refinement` (the limiter
refinement over `Relation.ReflTransGen`) and `MathlibAudit.Research` (statements about
`Nat.Perfect`). This module owns no declarations. The declaration gate discovers the
`MathlibAudit` surface from Lake's inventory, not from this import list.

The standard's own examples and the repository's default verification import only Lean's
core libraries (`audit/`); `./scripts/verify.sh mathlib` checks this package separately.
-/
