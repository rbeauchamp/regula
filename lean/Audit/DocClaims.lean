import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Audit.DocPrelude

/-!
# Dogfooding claims for standard examples

Dogfooding declarations for the standard's examples. The module owns the exponential
`DecayingValue` formula, antitonicity theorem, and joint-satisfiability witness, and nominal
discrete `Tick` values with transported natural order; examples of the standard import them.
Declarations the standard's own `lean` blocks display, with their inhabitance, defining-equation
and axiom claims, are elaborated where they are written and are not repeated here.

Each result states only its displayed binders and hypotheses. The decay witness
proves only joint satisfiability of its listed hypotheses, and no definition or
theorem is promoted to a native-runtime or external-system claim. Mathlib/Core
predicates and structures are reused where they match.
-/

namespace Glossary

/- ── Module 4 §4.1: the monotonic decay statement and its non-vacuity. ── -/

/-- Parameters for a real-valued exponential curve over nominal `Time`. -/
structure DecayingValue where
  initial : NNReal
  decayRate : ℝ
  startTime : Time

/-- Reference value `initial * exp (decayRate * (t.val - startTime.val))`: the
initial non-negative real multiplied by the exponential of the decay rate times
elapsed nominal time. This mathematical definition makes no claim about native
evaluation or an external runtime. -/
noncomputable def DecayingValue.valueAt (v : DecayingValue) (t : Time) : ℝ :=
  v.initial * Real.exp (v.decayRate * ((t.val : ℝ) - v.startTime.val))

/-- A negative decay rate makes the reference value antitone in time. The
quantifiers range over every `v`, `t₁`, and `t₂` satisfying the displayed
hypotheses, and the conclusion compares only `valueAt`. -/
theorem decay_monotone (v : DecayingValue) (h : v.decayRate < 0) :
    ∀ t₁ t₂ : Time, t₁ ≤ t₂ → v.valueAt t₂ ≤ v.valueAt t₁ := by
  intro t₁ t₂ ht
  have hval : t₁.val ≤ t₂.val := ht
  unfold DecayingValue.valueAt
  have hvalReal : (t₁.val : ℝ) ≤ (t₂.val : ℝ) := hval
  have hsub : (t₁.val : ℝ) - v.startTime.val ≤
      (t₂.val : ℝ) - v.startTime.val := by
    exact sub_le_sub_right hvalReal _
  have flip : v.decayRate * ((t₂.val : ℝ) - v.startTime.val) ≤
      v.decayRate * ((t₁.val : ℝ) - v.startTime.val) :=
    mul_le_mul_of_nonpos_left hsub (le_of_lt h)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr flip) v.initial.property

/-- The hypotheses used by `decay_monotone` are jointly satisfiable: there is
a negative-rate curve and an ordered pair of times. This proves exactly that
existence statement, not reachability in an external system. -/
theorem decay_monotone_nonvacuous :
    ∃ (v : DecayingValue) (t₁ t₂ : Time), v.decayRate < 0 ∧ t₁ ≤ t₂ := by
  refine ⟨⟨(1 : NNReal), -1, Time.mk (0 : NNReal)⟩,
    Time.mk (0 : NNReal), Time.mk (1 : NNReal), by norm_num, ?_⟩
  change (0 : NNReal) ≤ 1
  exact zero_le_one

/- ── Module 4 §4.3: nominal discrete time with a transported order. ── -/

/-- A discrete step count, nominally distinct from unrelated natural quantities.
The public `val` projection and constructor make conversion explicit. -/
structure Tick where
  val : Nat

/-- The natural linear order transported along the injective representation.
All order laws come from Mathlib's `LinearOrder.lift'`. -/
instance : LinearOrder Tick :=
  LinearOrder.lift' Tick.val (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

/-- The transported order compares exactly the underlying natural counts. -/
theorem Tick.le_iff (a b : Tick) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

end Glossary
