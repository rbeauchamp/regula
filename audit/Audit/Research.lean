import Mathlib.NumberTheory.FactorisationProperties

/-!
# Audit.Research

Dogfooding declarations for research statements (module 3 §3.10): an open
`Prop`-valued target, conditional results about its hypothetical witnesses,
a bounded-search reduction, and one witnessed unconditional existence claim.

## Main Definitions

- `Research.OddPerfectExists` - the open target, stated as a `Prop`, not proved
  or refuted here
- `Research.oddPerfectExists_iff_sum` - the equivalent odd-number target with
  the proper-divisor sum equation; oddness already supplies positivity
- `Research.oddPerfect_nine_le` - every odd perfect number is at least `9`;
  a conditional theorem whose antecedent has no known inhabitant
- `Research.Perfect.not_isPrimePow` - no perfect number is a prime power,
  derived from Mathlib's `IsPrimePow.deficient`
- `Research.not_oddPerfectExists_of_bound` - a complete reduction: an explicit
  upper bound together with a finite search below it refutes the target
- `Research.search_below_nine` - the finite-search hypothesis discharged at `9`
- `Research.exists_even_perfect` - an unconditional existence claim with its
  witness `6`

## Implementation Notes

`Nat.Perfect n` is Mathlib's `∑ i ∈ n.properDivisors, i = n ∧ 0 < n`; the
positivity conjunct excludes `0` from the perfect-number predicate, because
the bare divisor-sum equation is satisfied by `0`
(`Research.zero_sum_properDivisors`). In the odd-perfect target, `Odd n`
already implies positivity (`Odd.pos`), so omitting that conjunct leaves an
equivalent target (`Research.oddPerfectExists_iff_sum`). `Odd n` is Mathlib's
`∃ m, n = 2 * m + 1`. Every result states only its displayed binders and
hypotheses. No theorem here asserts or denies `OddPerfectExists`; the
reduction moves that content into its explicit bound hypothesis. All proofs
reuse Mathlib results; the declaration gate reports each declaration's exact
axiom set within the `Audit` surface's Standard-Logical claim.
-/

namespace Research

/-- The open target: some natural number is both odd and perfect.

This is a `Prop`-valued definition, not a theorem. Read-back: one existential
over `ℕ`; `Odd n` is Mathlib's `∃ m, n = 2 * m + 1`; `Nat.Perfect n` requires
the proper-divisor sum to equal `n` *and* `0 < n`. Nothing in this module
proves or refutes it, and no project axiom stands in for a proof. -/
def OddPerfectExists : Prop := ∃ n : ℕ, Odd n ∧ n.Perfect

/-- Why `Nat.Perfect` carries a positivity conjunct: the bare divisor-sum
equation already holds at `0`, whose proper-divisor set is empty. Dropping
positivity changes that predicate, but not `OddPerfectExists`: zero is not odd,
and `oddPerfectExists_iff_sum` proves the target equivalence. -/
theorem zero_sum_properDivisors : ∑ i ∈ Nat.properDivisors 0, i = 0 := by simp

/-- The odd-perfect existence target is unchanged when the explicit positivity
conjunct of `Nat.Perfect` is omitted: `Odd.pos` supplies it. This specializes
Mathlib's `Nat.perfect_iff_sum_properDivisors` under the target's oddness
hypothesis; it proves equivalence of two statements, neither statement itself. -/
theorem oddPerfectExists_iff_sum :
    OddPerfectExists ↔ ∃ n : ℕ, Odd n ∧ (∑ i ∈ n.properDivisors, i) = n := by
  constructor
  · rintro ⟨n, hodd, hperfect⟩
    exact ⟨n, hodd, hperfect.1⟩
  · rintro ⟨n, hodd, hsum⟩
    exact ⟨n, hodd, (Nat.perfect_iff_sum_properDivisors hodd.pos).mpr hsum⟩

/-- No perfect number is a prime power. Derived from Mathlib: prime powers are
deficient, and a positive number is perfect exactly when it is neither
abundant nor deficient. The hypothesis is an ordinary binder. -/
theorem Perfect.not_isPrimePow {n : ℕ} (hp : n.Perfect) : ¬ IsPrimePow n := fun hpp =>
  ((Nat.perfect_iff_not_abundant_and_not_deficient hp.2.ne).mp hp).2 hpp.deficient

/-- Every odd perfect number is at least `9`.

This is a conditional theorem: it claims exactly the implication for every
`n` satisfying both hypotheses. It requires no witness for its antecedent and
would remain true if no odd perfect number existed. The proof is a closed
finite case analysis: an odd number below `9` is `1`, `3`, `5`, or `7`; `1`
has an empty proper-divisor set, and the other three are prime, hence not
perfect (`Nat.Prime.not_perfect`). -/
theorem oddPerfect_nine_le {n : ℕ} (hodd : Odd n) (hperf : n.Perfect) : 9 ≤ n := by
  by_contra hlt
  have hmod := Nat.odd_iff.mp hodd
  have hcases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · simp [Nat.Perfect] at hperf
  · exact Nat.prime_three.not_perfect hperf
  · exact Nat.prime_five.not_perfect hperf
  · exact Nat.prime_seven.not_perfect hperf

/-- A complete conditional reduction. If every odd perfect number were below
an explicit bound `B`, and no odd number below `B` were perfect, then no odd
perfect number would exist.

Both assumptions are binders. The theorem is complete as stated; it does not
establish `¬ OddPerfectExists`, and it provides no evidence for either
answer. Its content is the shape of a bounded-search argument: the open
research question lives entirely in `hbound`. -/
theorem not_oddPerfectExists_of_bound (B : ℕ)
    (hbound : ∀ n, Odd n → n.Perfect → n < B)
    (hsearch : ∀ n, n < B → Odd n → ¬ n.Perfect) : ¬ OddPerfectExists :=
  fun ⟨n, hodd, hperf⟩ => hsearch n (hbound n hodd hperf) hodd hperf

/-- The finite-search hypothesis of `not_oddPerfectExists_of_bound` at `B = 9`,
discharged by `oddPerfect_nine_le`. The bound hypothesis at `9` remains open;
this theorem does not supply it. -/
theorem search_below_nine : ∀ n, n < 9 → Odd n → ¬ n.Perfect :=
  fun _ hlt hodd hperf => absurd (oddPerfect_nine_le hodd hperf) (by omega)

/-- `6` is perfect: its proper divisors `1`, `2`, `3` sum to `6`. A closed
decidable statement, so `decide` produces the kernel-checked term. -/
theorem perfect_six : Nat.Perfect 6 := by
  unfold Nat.Perfect
  decide

/-- An unconditional existence claim carries its witness. Contrast with
`OddPerfectExists`, for which no witness is available: the claim kinds
differ, and only this one is proved. -/
theorem exists_even_perfect : ∃ n : ℕ, Even n ∧ n.Perfect := ⟨6, by decide, perfect_six⟩

/-- Quantifier order is part of the statement. The unswapped `∀ x, ∃ y, x < y`
is Mathlib's `exists_gt` at `ℕ` (`NoMaxOrder ℕ`); the swapped `∃ y, ∀ x, x < y`
proved false here is a different proposition. A read-back that reorders the
quantifiers describes the other one. -/
theorem no_greatest_nat_swapped : ¬ ∃ y : ℕ, ∀ x : ℕ, x < y :=
  fun ⟨y, h⟩ => lt_irrefl y (h y)

end Research
