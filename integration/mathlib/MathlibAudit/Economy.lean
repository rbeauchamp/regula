import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-!
# A Mathlib tactic proof and a lawful mixin over the reals

Mathlib integration control for two lessons whose Lean/Std forms are
`audit/Audit/Economy.lean`. Every declaration is hole-free and uses no project axiom.

**A Mathlib tactic on a core definition.** `two_mul_sumTo` proves the Gauss
identity for the structurally recursive `sumTo` with Mathlib's `ring`; the
declaration gate reports the axiom set that proof actually has.

**Lawful mixin.** `Flourishable` holds operations only; `LawfulFlourishable`
is a `Prop`-valued mixin that holds every law, relative to Mathlib's `Preorder`.
A generic claim that uses a law requires the mixin directly
(`measure_enhance_ge`) or obtains its instance from stronger assumptions; a use
at a concrete type obtains it from a discharged instance; an instance of the
mixin must discharge every law. The class is retained rather than replaced by a
Mathlib structure because no pinned Core/Std/Mathlib class states an inflationary
binary operation together with a real-valued monotone measure; the ℝ instance
reuses `le_max_left` and `min_le_left` instead of re-proving them.
-/

namespace Economy

/-- Structural recursion: reducing `sumTo n` traverses its recursive cases.
This counts recursive steps, not the cost of arithmetic or total checker time. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- One induction discharges every instance; its cost does not grow with the
instance. -/
theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumTo, Nat.mul_add, ih]; ring

/-- Operations only. The lawful mixin takes the intended order separately,
so this instance does not select another relation for its laws. Bundled order
hierarchies are also valid when their instance paths agree. -/
class Flourishable (α : Type) where
  /-- Combines two values into one that the lawful mixin requires to be at least the first. -/
  enhance : α → α → α
  /-- Combines two values into one that the lawful mixin requires to be at most the first. -/
  diminish : α → α → α
  /-- A real-valued measurement of a value. -/
  measure : α → ℝ

/-- Lawful mixin: every law is a proof-requiring field over the operations,
relative to a separately supplied lawful order (`Preorder α`), as Mathlib's
`IsOrderedAddMonoid` is relative to `[Preorder α]`. An instance of this
class is the claim that `α`'s operations are lawful for that order. -/
class LawfulFlourishable (α : Type) [Preorder α] [Flourishable α] : Prop where
  /-- `enhance a b` is at least `a` in the supplied order. -/
  enhance_increases : ∀ a b : α, a ≤ Flourishable.enhance a b
  /-- `diminish a b` is at most `a` in the supplied order. -/
  diminish_decreases : ∀ a b : α, Flourishable.diminish a b ≤ a
  /-- `measure` is monotone from the supplied order to the order of `ℝ`. -/
  measure_monotone :
    ∀ a b : α, a ≤ b → Flourishable.measure a ≤ Flourishable.measure b

/-- Operations on ℝ. -/
instance : Flourishable ℝ where
  enhance := max
  diminish := min
  measure := id

/-- All laws discharged from Mathlib's lattice lemmas. -/
instance : LawfulFlourishable ℝ where
  enhance_increases := fun _ _ => le_max_left _ _
  diminish_decreases := fun _ _ => min_le_left _ _
  measure_monotone := fun _ _ h => h

/-- A claim that uses a law requires the mixin; without `[LawfulFlourishable α]`
this statement does not elaborate. -/
theorem measure_enhance_ge {α : Type} [Preorder α] [Flourishable α] [LawfulFlourishable α]
    (a b : α) :
    Flourishable.measure a ≤ Flourishable.measure (Flourishable.enhance a b) :=
  LawfulFlourishable.measure_monotone _ _ (LawfulFlourishable.enhance_increases a b)

end Economy
