import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Basic

/-!
# Real-valued glossary types

Mathlib integration control for the real-valued model of the standard's shared
glossary types. It provides nominal `Glossary.Time` over Mathlib's non-negative
reals with a lawful linear order lifted by `LinearOrder.lift'`, and
`ResourceAmount` as the canonical `NNReal`. The standard's own examples use the
exact-rational `Glossary.Time` of `audit/Audit/DocPrelude.lean`, which imports
only Lean's core library; this module keeps the continuous model that needs
Mathlib's `ℝ`, and the two are separate declarations in separate packages.

This module is part of the positive `MathlibAudit` surface, and the axiom gate
reports every declaration and foundation label below.
-/

namespace Glossary

/-- `Time`: a nominal wrapper around non-negative reals.

The wrapper is intentionally distinct from every other `NNReal`-backed domain
type: a time cannot be passed directly where a resource amount is required.
The `val` field exposes the underlying non-negative real when a formula needs
it. -/
structure Time where
  /-- The non-negative real this time wraps. -/
  val : NNReal

/-- Lawful linear order on `Time`, lifted from Mathlib's `NNReal` order. The
instance is noncomputable because `NNReal`'s inherited real order is. -/
noncomputable instance : LinearOrder Time :=
  LinearOrder.lift' Time.val (by
    intro a b h
    cases a
    cases b
    simp_all)

/-- Resource quantities reuse Mathlib's canonical non-negative reals. This is
definitionally `NNReal`, unlike the nominal `Time` wrapper. -/
abbrev ResourceAmount : Type := NNReal

end Glossary
