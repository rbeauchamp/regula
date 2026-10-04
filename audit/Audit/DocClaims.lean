import Audit.DocPrelude

/-!
# Dogfooding claims for standard examples

Dogfooding declarations for the standard's examples. The module owns the linear
`DecayingValue` formula over exact rationals, its antitonicity theorem and
joint-satisfiability witness, and nominal discrete `Tick` values with the natural
order; examples of the standard import them. Declarations the standard's own `lean`
blocks display, with their inhabitance, defining-equation and axiom claims, are
elaborated where they are written and are not repeated here.

Each result states only its displayed binders and hypotheses. The decay witness
proves only joint satisfiability of its listed hypotheses, and no definition or
theorem is promoted to a native-runtime or external-system claim. Core predicates
and structures are reused where they match. The curve is linear in elapsed time and
its arithmetic is exact rational arithmetic: it is not an exponential and makes no
claim about real numbers. The real-valued exponential curve, which needs Mathlib's
`Real.exp`, is `MathlibAudit.DocClaims` in the Mathlib integration package
(`integration/mathlib/`).
-/

namespace Glossary

/- ── Module 4 §4.1: the monotonic decay statement and its non-vacuity. ── -/

/-- Parameters for a rational-valued linear curve over nominal `Time`. -/
structure DecayingValue where
  /-- The value at `startTime`, a non-negative rational. -/
  initial : {value : Rat // 0 ≤ value}
  /-- The relative change per unit of elapsed time; a negative rate is a decay. -/
  decayRate : Rat
  /-- The time at which the curve takes its `initial` value. -/
  startTime : Time

/-- Reference value `initial * (1 + decayRate * (t.val - startTime.val))`: the
initial non-negative rational multiplied by one plus the decay rate times elapsed
nominal time. The formula is linear in `t`; nothing here bounds its sign, and no
claim is made about native evaluation or an external runtime. -/
def DecayingValue.valueAt (v : DecayingValue) (t : Time) : Rat :=
  v.initial.val * (1 + v.decayRate * (t.val - v.startTime.val))

/-- A negative decay rate makes the reference value antitone in time. The
quantifiers range over every `v`, `t₁`, and `t₂` satisfying the displayed
hypotheses, and the conclusion compares only `valueAt`. -/
theorem decay_monotone (v : DecayingValue) (h : v.decayRate < 0) :
    ∀ t₁ t₂ : Time, t₁ ≤ t₂ → v.valueAt t₂ ≤ v.valueAt t₁ := by
  intro t₁ t₂ ht
  have hval : t₁.val ≤ t₂.val := ht
  unfold DecayingValue.valueAt
  -- Elapsed time grows with `t`, and multiplying by the non-negative `-decayRate` keeps `≤`.
  have hsub : t₁.val - v.startTime.val ≤ t₂.val - v.startTime.val := by grind
  have flip : -v.decayRate * (t₁.val - v.startTime.val) ≤
      -v.decayRate * (t₂.val - v.startTime.val) :=
    Rat.mul_le_mul_of_nonneg_left hsub (by grind)
  exact Rat.mul_le_mul_of_nonneg_left (by grind) v.initial.property

/-- The hypotheses used by `decay_monotone` are jointly satisfiable: there is
a negative-rate curve and an ordered pair of times. This proves exactly that
existence statement, not reachability in an external system. -/
theorem decay_monotone_nonvacuous :
    ∃ (v : DecayingValue) (t₁ t₂ : Time), v.decayRate < 0 ∧ t₁ ≤ t₂ :=
  ⟨⟨⟨1, by decide +kernel⟩, -1, ⟨0, Rat.le_refl⟩⟩, ⟨0, Rat.le_refl⟩,
    ⟨1, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

/- ── Module 4 §4.3: nominal discrete time with the natural order. ── -/

/-- A discrete step count, nominally distinct from unrelated natural quantities.
The public `val` projection and constructor make conversion explicit. -/
structure Tick where
  /-- The number of steps this tick counts. -/
  val : Nat

/-- Ticks compare by their step counts. -/
instance : LE Tick := ⟨fun a b => a.val ≤ b.val⟩

/-- The comparison of two ticks is the decidable comparison of their counts. -/
instance : DecidableLE Tick := fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

/-- Any two ticks are comparable, as their counts are. -/
instance : Std.Total (α := Tick) (· ≤ ·) := ⟨fun a b => Nat.le_total a.val b.val⟩

/-- The comparison of ticks is transitive, as that of their counts is. -/
instance : Trans (α := Tick) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Nat.le_trans⟩

/-- Ticks that compare both ways are equal: `val` is injective. -/
instance : Std.Antisymm (α := Tick) (· ≤ ·) where
  antisymm a b hab hba := by
    cases a
    cases b
    simp only [Tick.mk.injEq]
    exact Nat.le_antisymm hab hba

/-- The natural linear order transported along the injective representation. Core's
`Std.LinearOrderPackage.ofLE` factory builds the lawful structure from the three laws
above, which are `Nat`'s. -/
instance : Std.LinearOrderPackage Tick := .ofLE Tick

/-- The transported order compares exactly the underlying natural counts. -/
theorem Tick.le_iff (a b : Tick) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

end Glossary
