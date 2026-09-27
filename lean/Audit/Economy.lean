import Mathlib.Tactic.Ring
import Mathlib.Basic.Real.Basic

/-!
# Proof economy and lawful mixins

Checked examples for proof economy (standard §3.2.5) and lawful mixins
(standard §3.2.3). Every declaration is hole-free and uses no project axiom.

**Cost domains.** `sumTo` and `sumWf` have the same recursive equations
and illustrate distinct elaboration and kernel-reduction behavior. Elaboration:
`sumTo` is structurally recursive and unfolds at default transparency, so
`decide` closes `sumTo 100 = 5050`; `sumWf` is well-founded and therefore
`@[irreducible]`, so the elaborator's `decide` stops at it (the negative
fence in standard §3.2.5). Kernel replay: the kernel can replay both, `sumTo`
by unfolding the recursor and `sumWf` through the fixpoint term it elaborated
to (`WellFounded.Nat.fix` for its `Nat` measure on this pin, unfolded by
`Nat.rec` on an eager fuel bound rather than through an accessibility
proof); `decide +kernel` hands `sumWf 10 = 55` to the kernel
directly (`sumWf_ten_kernel`). Foundation: `sumWf`'s own axiom set is
`[propext, Quot.sound]`, contributed by the `omega` call that discharges its
termination obligation, not by the recursion scheme itself. Native execution:
before `sumTo_csimp` each compiles to a recursive loop; after it, compiled
callers of `sumTo` run `closedSum` while callers of `sumWf` still run the
loop. The analytic theorem `two_mul_sumTo` replaces per-instance replay with
one induction for every `n`, and kernel reduction of `sumTo` is unchanged by
the `csimp` attribute.

Retention reason (standard checklist row `DOGFOOD-04`): Mathlib's
`Finset.sum_range_id_mul_two : (∑ i ∈ range n, i) * 2 = n * (n - 1)` states
the Gauss identity at a shifted index (`range (n + 1)` corresponds to
`sumTo n`), but that sum is a `Multiset`-quotient object whose kernel
reduction is not the recursion scheme under study; `sumTo` and `sumWf` are
retained because the example is about how the two recursion schemes
elaborate, replay, and compile, not about the arithmetic identity.

**Performance interface.** `closedSumWithProof` returns `closedSum n` with the exact
Gauss relation as an erased proof, reusing `sumTo_eq_closedSum` and
`two_mul_sumTo`. It connects the performance chapter to executable evidence
without duplicating the chapter's teaching functions.

**Lawful mixin.** `Flourishable` holds operations only; `LawfulFlourishable`
is a `Prop`-valued mixin that holds every law. A generic claim that uses a
law requires the mixin directly (`measure_enhance_ge`) or obtains its instance
from stronger assumptions; a use at a
concrete type obtains it from a discharged instance; an instance of the
mixin must discharge every law (standard §3.2.3 negative fences). The class is
retained rather than replaced by a Mathlib structure because no pinned
Core/Std/Mathlib class states an inflationary binary operation together with
a real-valued monotone measure; the ℝ instance reuses `le_max_left` and
`min_le_left` instead of re-proving them.
-/

namespace Economy

/-- Structural recursion: reducing `sumTo n` traverses its recursive cases.
This counts recursive steps, not the cost of arithmetic or total checker time. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- The same equations by well-founded recursion. The definition is
`@[irreducible]`, so elaborator-side `decide` and `rfl` stop at it at default
transparency; the kernel can still replay its elaborated `WellFounded.Nat.fix`
term. Its
own axiom set is `[propext, Quot.sound]`. -/
def sumWf (n : Nat) : Nat :=
  if _h : n = 0 then 0 else sumWf (n - 1) + n
termination_by n
decreasing_by omega

/-- Closed form: a fixed number of kernel-accelerated literal operations. -/
def closedSum (n : Nat) : Nat := n * (n + 1) / 2

/-- One induction discharges every instance; its cost does not grow with the
instance. -/
theorem two_mul_sumTo (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [sumTo, Nat.mul_add, ih]; ring

/-- Pointwise agreement of the reference with the closed form. -/
theorem sumTo_eq_closedSum (n : Nat) : sumTo n = closedSum n := by
  unfold closedSum
  have := two_mul_sumTo n
  omega

/-- Compute the closed form and return its exact arithmetic contract. The
proof is erased; runtime data is `closedSum n`, without traversing `sumTo`.
This proof-bearing interface reuses the existing universal sum theorem rather
than checking each input by replaying its recursive sum. It claims no timing
bound for arbitrary-precision arithmetic or native execution. -/
def closedSumWithProof (n : Nat) : {s : Nat // 2 * s = n * (n + 1)} :=
  ⟨closedSum n, by rw [← sumTo_eq_closedSum]; exact two_mul_sumTo n⟩

/-- Compiler simplification only: native calls to `sumTo` run `closedSum`.
Kernel reduction of `sumTo` is untouched by this attribute. -/
@[csimp] theorem sumTo_csimp : @sumTo = @closedSum := funext sumTo_eq_closedSum

/-- Kernel replay of the recursion, 100 unfoldings; small proof term,
replay cost grows with the literal. -/
example : sumTo 100 = 5050 := by decide

/-- The analytic route: one rewrite by the universal theorem, then
kernel-accelerated literal arithmetic. -/
example : sumTo 100 = 5050 := by rw [sumTo_eq_closedSum]; rfl

/-- The stable interface of the well-founded definition is its equation
theorem; proofs go through it rather than through transparency changes. This
wrapper presents the generated equation with a non-dependent `if`, matching
the equations taught in standard §3.2.5; `rw [sumWf]` reuses that generated
equation rather than proving the recursion again. -/
theorem sumWf_unfold (n : Nat) :
    sumWf n = if n = 0 then 0 else sumWf (n - 1) + n := by
  rw [sumWf]; rfl

/-- Kernel replay of the well-founded definition: `decide +kernel` skips the
elaborator's reduction and lets the kernel unfold the elaborated
`WellFounded.Nat.fix` term by structural recursion on its fuel bound. The cost
is paid in the kernel-replay domain. -/
theorem sumWf_ten_kernel : sumWf 10 = 55 := by decide +kernel

/-- The two definitions agree; proved by induction without `Classical.choice`. -/
theorem sumWf_eq_sumTo (n : Nat) : sumWf n = sumTo n := by
  induction n with
  | zero => rw [sumWf_unfold]; rfl
  | succ k ih =>
    rw [sumWf_unfold]
    split
    · exfalso; exact Nat.succ_ne_zero _ (by assumption)
    · simp [ih, sumTo]

/-- Operations only. The lawful mixin takes the intended order separately,
so this instance does not select another relation for its laws. Bundled order
hierarchies are also valid when their instance paths agree. -/
class Flourishable (α : Type) where
  enhance : α → α → α
  diminish : α → α → α
  measure : α → ℝ

/-- Lawful mixin: every law is a proof-requiring field over the operations,
relative to a separately supplied lawful order (`Preorder α`), as Mathlib's
`IsOrderedAddMonoid` is relative to `[Preorder α]`. An instance of this
class is the claim that `α`'s operations are lawful for that order. -/
class LawfulFlourishable (α : Type) [Preorder α] [Flourishable α] : Prop where
  enhance_increases : ∀ a b : α, a ≤ Flourishable.enhance a b
  diminish_decreases : ∀ a b : α, Flourishable.diminish a b ≤ a
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
