module

/-
Support for `Fixtures.Mutations.SharedTestImported`: a `module` file with a test and a function
around it that are `public` without `@[expose]`, so Lean does not export their values. A file
with a `module` header that imports this one has each of the two as an axiom, and its editor
snapshot cannot read below them. The project check reads their values.

The theorems state all that an importing module can prove about the two functions. This module
registers no contract, so it must be accepted.
-/

/-- Whether `n` is below four. -/
public def fixtures_hidden_small (n : Nat) : Bool := decide (n < 4)

/-- `fixtures_hidden_small` accepts zero. -/
public theorem fixtures_hidden_small_zero : fixtures_hidden_small 0 = true := by decide

/-- `fixtures_hidden_small` refuses four. -/
public theorem fixtures_hidden_small_four : ¬ fixtures_hidden_small 4 = true := by decide

/-- The number of the elements of a list that `fixtures_hidden_small` accepts. -/
public def fixtures_hidden_count (numbers : List Nat) : Nat :=
  (numbers.filter fixtures_hidden_small).length

/-- `fixtures_hidden_count` is zero exactly when the test refuses each element. -/
public theorem fixtures_hidden_count_eq_zero_iff (numbers : List Nat) :
    fixtures_hidden_count numbers = 0 ↔ ∀ n ∈ numbers, fixtures_hidden_small n = false := by
  simp [fixtures_hidden_count]
