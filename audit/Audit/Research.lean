/-!
# Audit.Research

Dogfooding declarations for research statements (module 3 §3.10): an open
`Prop`-valued target, conditional results about its hypothetical witnesses,
a bounded-search reduction, and one witnessed unconditional existence claim.

## Main Definitions

- `Research.collatzStep` - one step of the Collatz map on `Nat`
- `Research.ReachesOne` - some finite number of steps takes a number to `1`
- `Research.CounterexampleExists` - the open target, stated as a `Prop`, not
  proved or refuted here: a positive number that never reaches `1`
- `Research.exists_not_reachesOne` - the target without its positivity conjunct
  is a different proposition, proved here with the witness `0`
- `Research.counterexample_nine_le` - every counterexample is at least `9`;
  a conditional theorem whose antecedent has no known inhabitant
- `Research.Counterexample.ne_two_pow` - no counterexample is a power of two,
  derived from `Research.repeat_collatzStep_two_pow_mul`
- `Research.not_counterexampleExists_of_bound` - a complete reduction: an explicit
  upper bound together with a finite search below it refutes the target
- `Research.search_below_nine` - the finite-search hypothesis discharged at `9`
- `Research.exists_odd_reachesOne` - an unconditional existence claim with its
  witness `7`

## Implementation Notes

`collatzStep n` halves an even `n` and sends an odd `n` to `3 * n + 1`; iteration is
core's `Nat.repeat`. The Collatz conjecture says that every positive natural number
reaches `1`; `CounterexampleExists` is the existence of a number refuting it. The
conjecture implies `¬ CounterexampleExists` constructively and is classically equivalent
to it: the converse eliminates a double negation of `ReachesOne n`. The positivity
conjunct is part of the target:
`0` is a fixed point of `collatzStep` and never reaches `1`
(`Research.not_reachesOne_zero`), so the bare statement `∃ n, ¬ ReachesOne n` is true
and settles nothing. Every result states only its displayed binders and hypotheses.
No theorem here asserts or denies `CounterexampleExists`; the reduction moves that
content into its explicit bound hypothesis. These definitions are this module's own:
neither core nor Std states the Collatz map. The corresponding statements about
Mathlib's `Nat.Perfect` are `MathlibAudit.Research` in the Mathlib integration package
(`integration/mathlib/`). The declaration gate reports each declaration's exact
axiom set within the `Audit` surface's Standard-Logical claim.
-/

namespace Research

/-- One step of the Collatz map: an even number is halved, and an odd `n` goes to
`3 * n + 1`. Total on `Nat`; `0` is a fixed point. -/
def collatzStep (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Some finite number of Collatz steps takes `n` to `1`. Read-back: one existential
over the step count `k`; `Nat.repeat collatzStep k n` applies `collatzStep` exactly
`k` times, and `k = 0` is allowed, so `1` reaches `1`. -/
def ReachesOne (n : Nat) : Prop := ∃ k, Nat.repeat collatzStep k n = 1

/-- The open target: some positive natural number never reaches `1`.

This is a `Prop`-valued definition, not a theorem. Read-back: one existential
over `Nat`; the number is positive *and* no step count takes it to `1`. The
Collatz conjecture is classically equivalent to the negation of this proposition,
and implies that negation constructively. Nothing in this module proves or refutes
it, and no project axiom stands in for a proof. -/
def CounterexampleExists : Prop := ∃ n : Nat, 0 < n ∧ ¬ ReachesOne n

/-- Every iterate of `0` is `0`: `collatzStep` halves it. -/
theorem repeat_collatzStep_zero (k : Nat) : Nat.repeat collatzStep k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.repeat, ih]; rfl

/-- `0` never reaches `1`. -/
theorem not_reachesOne_zero : ¬ ReachesOne 0 := fun ⟨k, hk⟩ => by
  rw [repeat_collatzStep_zero] at hk
  contradiction

/-- Why the target carries a positivity conjunct: without it the existence
statement is already true at `0`, which is no counterexample to the conjecture.
Dropping positivity changes the proposition; this theorem proves the weaker one
and says nothing about `CounterexampleExists`. -/
theorem exists_not_reachesOne : ∃ n : Nat, ¬ ReachesOne n := ⟨0, not_reachesOne_zero⟩

/-- `k` steps halve `2 ^ k * m` down to `m`, for every `k` and `m`. -/
theorem repeat_collatzStep_two_pow_mul (k m : Nat) :
    Nat.repeat collatzStep k (2 ^ k * m) = m := by
  induction k generalizing m with
  | zero => simp [Nat.repeat]
  | succ k ih =>
    have double : 2 ^ (k + 1) * m = 2 ^ k * (2 * m) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [Nat.repeat, double, ih]
    simp [collatzStep]

/-- Every power of two reaches `1`, in as many steps as its exponent. -/
theorem reachesOne_two_pow (k : Nat) : ReachesOne (2 ^ k) :=
  ⟨k, by simpa using repeat_collatzStep_two_pow_mul k 1⟩

/-- No counterexample is a power of two. The hypothesis is an ordinary binder, and
the theorem needs no counterexample to exist. -/
theorem Counterexample.ne_two_pow {n : Nat} (h : ¬ ReachesOne n) (k : Nat) : n ≠ 2 ^ k :=
  fun heq => h (heq ▸ reachesOne_two_pow k)

/-- Every positive number below `9` reaches `1`: a closed finite case analysis, each
case discharged by an explicit step count that the kernel evaluates. -/
theorem search_below_nine : ∀ n, n < 9 → 0 < n → ReachesOne n := by
  intro n hlt hpos
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨7, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨8, by decide⟩
  · exact ⟨16, by decide⟩
  · exact ⟨3, by decide⟩

/-- Every counterexample is at least `9`.

This is a conditional theorem: it claims exactly the implication for every
`n` satisfying both hypotheses. It requires no witness for its antecedent and
would remain true if no counterexample existed. The proof is the finite search
`search_below_nine`. -/
theorem counterexample_nine_le {n : Nat} (hpos : 0 < n) (h : ¬ ReachesOne n) : 9 ≤ n :=
  Nat.le_of_not_lt fun hlt => h (search_below_nine n hlt hpos)

/-- A complete conditional reduction. If every counterexample were below
an explicit bound `B`, and every positive number below `B` reached `1`, then no
counterexample would exist.

Both assumptions are binders. The theorem is complete as stated; it does not
establish `¬ CounterexampleExists`, and it provides no evidence for either
answer. Its content is the shape of a bounded-search argument: the open
research question lives entirely in `hbound`. -/
theorem not_counterexampleExists_of_bound (B : Nat)
    (hbound : ∀ n, 0 < n → ¬ ReachesOne n → n < B)
    (hsearch : ∀ n, n < B → 0 < n → ReachesOne n) : ¬ CounterexampleExists :=
  fun ⟨n, hpos, h⟩ => h (hsearch n (hbound n hpos h) hpos)

/-- `7` reaches `1` in `16` steps. A closed decidable statement, so `decide`
produces the kernel-checked term. -/
theorem reachesOne_seven : ReachesOne 7 := ⟨16, by decide⟩

/-- An unconditional existence claim carries its witness. Contrast with
`CounterexampleExists`, for which no witness is available: the claim kinds
differ, and only this one is proved. -/
theorem exists_odd_reachesOne : ∃ n : Nat, n % 2 = 1 ∧ 1 < n ∧ ReachesOne n :=
  ⟨7, by decide, by decide, reachesOne_seven⟩

/-- Every natural number has a greater one: its successor. -/
theorem exists_greater_nat : ∀ x : Nat, ∃ y : Nat, x < y := fun x => ⟨x + 1, Nat.lt_succ_self x⟩

/-- Quantifier order is part of the statement. The unswapped `∀ x, ∃ y, x < y`
is `exists_greater_nat`; the swapped `∃ y, ∀ x, x < y` proved false here is a
different proposition. A read-back that reorders the quantifiers describes the
other one. -/
theorem no_greatest_nat_swapped : ¬ ∃ y : Nat, ∀ x : Nat, x < y :=
  fun ⟨y, h⟩ => Nat.lt_irrefl y (h y)

end Research
