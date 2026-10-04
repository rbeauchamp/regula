import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.UnitInterval

/-!
# Models that reuse Mathlib's canonical structures

Mathlib integration control for the lessons of the standard whose original examples
need real analysis or a Mathlib hierarchy. The standard's own examples teach the same
principles with Lean's core library; these declarations keep the Mathlib forms checked:

- `Probability` reuses Mathlib's closed unit interval, and `Probability.complement_val`
  states the defining equation of its complement by reusing `unitInterval.coe_symm_eq`
  (standard §2.2, §5.1).
- `GrowthFunction` bundles a real function with its monotonicity and non-negativity
  proof, and `exponentialGrowth` returns `Real.exp (rate * t)` with that proof
  (standard §1.2).
- `totalResources`, `combineResources` and `combineResources_le_combineResources` reuse
  Mathlib's `Monoid`, `AddCommMonoid` and the `Prop`-valued `IsOrderedAddMonoid` mixin
  (standard §1.4).
- `Location` reuses the real line's canonical metric, and `InRange` measures distance
  through it (standard §4.4).

Each result states only its displayed binders and hypotheses; no definition is promoted
to a native-runtime or external-system claim.
-/

namespace MathlibModels

/-- A real value in `[0, 1]`, reusing Mathlib's closed unit interval.
This type represents a scalar probability, not a probability distribution. -/
abbrev Probability : Type := unitInterval

/-- Smart constructor for probabilities. -/
def mkProbability (p : ℝ) (h : 0 ≤ p ∧ p ≤ 1) : Probability := ⟨p, h⟩

/-- Non-vacuity: at least one probability exists. This proves inhabitance,
nothing stronger. -/
example : Nonempty Probability := ⟨mkProbability 0 ⟨le_rfl, zero_le_one⟩⟩

/-- Unit-interval complement: the underlying value is `1 - p.val`.
Mathlib's `unitInterval.symm` constructs the result with its bound proof. -/
def Probability.complement (p : Probability) : Probability :=
  unitInterval.symm p

/-- For every probability, complement has underlying real value `1 - p.val`. -/
theorem Probability.complement_val (p : Probability) :
    p.complement.val = 1 - p.val :=
  unitInterval.coe_symm_eq p

/-- Specification: a function that is monotone and non-negative. -/
structure GrowthFunction where
  /-- The underlying real function. -/
  func : ℝ → ℝ
  /-- The function is monotone and non-negative. -/
  property : Monotone func ∧ ∀ t, 0 ≤ func t

/-- The exponential of a positive rate times time is monotone and non-negative. -/
theorem exp_mul_monotone_and_nonneg (rate : ℝ) (h : 0 < rate) :
    Monotone (fun t ↦ Real.exp (rate * t)) ∧ ∀ t, 0 ≤ Real.exp (rate * t) := by
  constructor
  · intro t₁ t₂ ht
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (le_of_lt h))
  · intro t
    exact le_of_lt (Real.exp_pos _)

/-- A function that returns the function and its proof, bundled.
The return type `GrowthFunction` guarantees the properties. -/
noncomputable def exponentialGrowth (rate : ℝ) (h : 0 < rate) : GrowthFunction :=
  ⟨fun t ↦ Real.exp (rate * t), exp_mul_monotone_and_nonneg rate h⟩

/-- Pure composition reuses Mathlib's lawful `Monoid` interface and `List.prod`;
there is no duplicate hand-written associativity/identity structure. -/
def totalResources {R : Type*} [Monoid R] (resources : List R) : R :=
  resources.prod

/-- A domain operation over Mathlib's lawful additive interface; no one-field
wrapper class duplicates the hierarchy. -/
def combineResources {R : Type*} [AddCommMonoid R] (a b : R) : R := a + b

/-- Its order law requires Mathlib's `IsOrderedAddMonoid` mixin directly. -/
theorem combineResources_le_combineResources {R : Type*} [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] {a b : R} (h : a ≤ b) (c : R) :
    combineResources a c ≤ combineResources b c :=
  add_le_add_left h c

/-- Mathlib already supplies the ordered-additive laws for `NNReal`. -/
example : IsOrderedAddMonoid NNReal := inferInstance

/-- One-dimensional locations reuse the real line's canonical Mathlib metric. -/
abbrev Location := ℝ

/-- Coordinate distance is Mathlib's lawful real metric, not a hand-written
distance relation. -/
noncomputable example : MetricSpace Location := inferInstance

/-- Locations within communication range, measured through the inherited metric. -/
def InRange (l₁ l₂ : Location) (range : ℝ) : Prop :=
  dist l₁ l₂ ≤ range

end MathlibModels
