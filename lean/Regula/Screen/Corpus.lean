import Lean
import RegulaPolicy.Screening

/-! # Intent screen calibration corpus

Labelled calibration corpus for the intent screen (`docs/guides/intent-screening.md`).

Each item is a definition of type `Prop` whose value is a formal claim and whose docstring
holds a §5.2 explanation and an `# Intent` section. A *base* item is a correct intent/claim
pair; a *rewrite* states the same requirement differently (a false-positive control); a
*mutant* deliberately changes the base claim by one of the five mutation kinds of issue #58,
and its explanation faithfully describes the mutated claim. The calibration runner also pairs
every mutant's statement with its base's explanation (a *stale* explanation), so a mutation
is visible only in the Lean statement. All items of one base share the base's Intent
section; the runner refuses otherwise.

Labels are schematic, read from the statements: a clause is *uncovered* when the claim's own
content does not establish it without using the clause as a background fact about the named
operations (most clauses are true facts about `Nat` or `List`, so literal implication would
make every label vacuous); an exclusion clause is uncovered when the claim asserts the excluded
case. The strength and targeted labels follow the question criteria in
`Regula.Screen.Questions`; the quantifier-order label concerns literal order, so a swap to a
stronger claim is a defect there only. The statements need not be true: the screen reads
propositions, not proofs. Bases `A` and `B` are
the development split, used to exercise the runner and wording before the single test run;
all other bases are the test split. -/

namespace IntentCorpus

/-- Admission decision of a bounded-capacity limiter. -/
def admits (capacity used request : Nat) : Bool := decide (used + request ≤ capacity)

/-- Cost of an input: its remainder modulo seven. -/
def cost (i : Nat) : Nat := i % 7

/-! ### A (dev): append length -/

/-- For all lists `xs` and `ys` of natural numbers, the length of `xs ++ ys` equals the length
of `xs` plus the length of `ys`.

# Intent
- Appending two lists yields a list whose length is exactly the sum of their lengths.
- This holds for all lists, including empty ones. -/
def A_base : Prop := ∀ xs ys : List Nat, (xs ++ ys).length = xs.length + ys.length

/-- For all lists `xs` and `ys` of natural numbers, the length of `xs ++ ys` equals the length
of `ys` plus the length of `xs`.

# Intent
- Appending two lists yields a list whose length is exactly the sum of their lengths.
- This holds for all lists, including empty ones. -/
def A_rewrite : Prop := ∀ xs ys : List Nat, (xs ++ ys).length = ys.length + xs.length

/-- For all lists `xs` and `ys` of natural numbers, the length of `xs ++ ys` is at most the
length of `xs` plus the length of `ys`.

# Intent
- Appending two lists yields a list whose length is exactly the sum of their lengths.
- This holds for all lists, including empty ones. -/
def A_weaken : Prop := ∀ xs ys : List Nat, (xs ++ ys).length ≤ xs.length + ys.length

/-- For all lists `xs` and `ys` of natural numbers with `xs` nonempty, the length of `xs ++ ys`
equals the length of `xs` plus the length of `ys`.

# Intent
- Appending two lists yields a list whose length is exactly the sum of their lengths.
- This holds for all lists, including empty ones. -/
def A_hypothesis : Prop := ∀ xs ys : List Nat, xs ≠ [] → (xs ++ ys).length = xs.length + ys.length

/-! ### B (dev): maximum of a list -/

/-- For every list `l` of natural numbers and every `m`, if `l.max?` is `some m`, then `m` is an
element of `l` and every element of `l` is at most `m`.

# Intent
- When the list has a maximum, the maximum is one of the list's elements.
- Every element of the list is at most the maximum.
- An empty list has no maximum; the claim makes no statement about it. -/
def B_base : Prop := ∀ (l : List Nat) (m : Nat), l.max? = some m → m ∈ l ∧ ∀ x ∈ l, x ≤ m

/-- For every list `l` of natural numbers and every `m`, if `l.max?` is `some m`, then every
element of `l` is at most `m` and `m` is an element of `l`.

# Intent
- When the list has a maximum, the maximum is one of the list's elements.
- Every element of the list is at most the maximum.
- An empty list has no maximum; the claim makes no statement about it. -/
def B_rewrite : Prop := ∀ (l : List Nat) (m : Nat), l.max? = some m → (∀ x ∈ l, x ≤ m) ∧ m ∈ l

/-- For every list `l` of natural numbers and every `m`, if `l.max?` is `some m`, then every
element of `l` is at most `m`.

# Intent
- When the list has a maximum, the maximum is one of the list's elements.
- Every element of the list is at most the maximum.
- An empty list has no maximum; the claim makes no statement about it. -/
def B_drop : Prop := ∀ (l : List Nat) (m : Nat), l.max? = some m → ∀ x ∈ l, x ≤ m

/-- For every list `l` of natural numbers and every `m`, if `l.max?` is `some m`, then `m` is an
element of `l` and every element of `l` is at most `m + 1`.

# Intent
- When the list has a maximum, the maximum is one of the list's elements.
- Every element of the list is at most the maximum.
- An empty list has no maximum; the claim makes no statement about it. -/
def B_weaken : Prop := ∀ (l : List Nat) (m : Nat), l.max? = some m → m ∈ l ∧ ∀ x ∈ l, x ≤ m + 1

/-- For every list `l` of natural numbers, `l.max?.getD 0` (the maximum, or `0` for the empty
list) is an element of `l`, and every element of `l` is at most it.

# Intent
- When the list has a maximum, the maximum is one of the list's elements.
- Every element of the list is at most the maximum.
- An empty list has no maximum; the claim makes no statement about it. -/
def B_totalize : Prop := ∀ l : List Nat, l.max?.getD 0 ∈ l ∧ ∀ x ∈ l, x ≤ l.max?.getD 0

/-! ### C (test): sorting -/

/-- For every list `l` of natural numbers, `l.mergeSort` is pairwise nondecreasing and is a
permutation of `l`.

# Intent
- Sorting returns its output in nondecreasing order.
- The output contains exactly the input's elements, each as many times as in the input. -/
def C_base : Prop := ∀ l : List Nat, l.mergeSort.Pairwise (· ≤ ·) ∧ l.mergeSort.Perm l

/-- For every list `l` of natural numbers, `l.mergeSort` is a permutation of `l` and is pairwise
nondecreasing.

# Intent
- Sorting returns its output in nondecreasing order.
- The output contains exactly the input's elements, each as many times as in the input. -/
def C_rewrite : Prop := ∀ l : List Nat, l.mergeSort.Perm l ∧ l.mergeSort.Pairwise (· ≤ ·)

/-- For every list `l` of natural numbers, `l.mergeSort` is pairwise nondecreasing.

# Intent
- Sorting returns its output in nondecreasing order.
- The output contains exactly the input's elements, each as many times as in the input. -/
def C_drop : Prop := ∀ l : List Nat, l.mergeSort.Pairwise (· ≤ ·)

/-- For every list `l` of natural numbers, each element of `l.mergeSort` is at most one more
than every later element, and `l.mergeSort` is a permutation of `l`.

# Intent
- Sorting returns its output in nondecreasing order.
- The output contains exactly the input's elements, each as many times as in the input. -/
def C_weaken : Prop := ∀ l : List Nat, l.mergeSort.Pairwise (fun a b => a ≤ b + 1) ∧
    l.mergeSort.Perm l

/-- For every list `l` of natural numbers without duplicates, `l.mergeSort` is pairwise
nondecreasing and is a permutation of `l`.

# Intent
- Sorting returns its output in nondecreasing order.
- The output contains exactly the input's elements, each as many times as in the input. -/
def C_hypothesis : Prop := ∀ l : List Nat, l.Nodup → l.mergeSort.Pairwise (· ≤ ·) ∧
    l.mergeSort.Perm l

/-! ### D (test): division bounds -/

/-- For all natural numbers `n` and `d` with `d ≠ 0`, `n / d * d ≤ n` and `n < (n / d + 1) * d`.

# Intent
- For a nonzero divisor, the quotient times the divisor does not exceed the dividend.
- For a nonzero divisor, the dividend is less than the quotient plus one, times the divisor.
- Division by zero is undefined for this requirement; the claim must not assert anything about a
  zero divisor. -/
def D_base : Prop := ∀ n d : Nat, d ≠ 0 → n / d * d ≤ n ∧ n < (n / d + 1) * d

/-- For all natural numbers `n` and `d` with `0 < d`, `n / d * d ≤ n` and `n < (n / d + 1) * d`.

# Intent
- For a nonzero divisor, the quotient times the divisor does not exceed the dividend.
- For a nonzero divisor, the dividend is less than the quotient plus one, times the divisor.
- Division by zero is undefined for this requirement; the claim must not assert anything about a
  zero divisor. -/
def D_rewrite : Prop := ∀ n d : Nat, 0 < d → n / d * d ≤ n ∧ n < (n / d + 1) * d

/-- For all natural numbers `n` and `d`, `n / d * d ≤ n` (for `d = 0` this uses `n / 0 = 0`),
and if `d ≠ 0` then `n < (n / d + 1) * d`.

# Intent
- For a nonzero divisor, the quotient times the divisor does not exceed the dividend.
- For a nonzero divisor, the dividend is less than the quotient plus one, times the divisor.
- Division by zero is undefined for this requirement; the claim must not assert anything about a
  zero divisor. -/
def D_totalize : Prop := ∀ n d : Nat, n / d * d ≤ n ∧ (d ≠ 0 → n < (n / d + 1) * d)

/-- For all natural numbers `n` and `d` with `d ≠ 0`, `n / d * d ≤ n`.

# Intent
- For a nonzero divisor, the quotient times the divisor does not exceed the dividend.
- For a nonzero divisor, the dividend is less than the quotient plus one, times the divisor.
- Division by zero is undefined for this requirement; the claim must not assert anything about a
  zero divisor. -/
def D_drop : Prop := ∀ n d : Nat, d ≠ 0 → n / d * d ≤ n

/-- For all natural numbers `n` and `d` with `d ≠ 0`, `n / d * d ≤ n` and `n ≤ (n / d + 1) * d`.

# Intent
- For a nonzero divisor, the quotient times the divisor does not exceed the dividend.
- For a nonzero divisor, the dividend is less than the quotient plus one, times the divisor.
- Division by zero is undefined for this requirement; the claim must not assert anything about a
  zero divisor. -/
def D_weaken : Prop := ∀ n d : Nat, d ≠ 0 → n / d * d ≤ n ∧ n ≤ (n / d + 1) * d

/-- For all natural numbers `n` and `d` with `d ≠ 0` and `d ≤ n`, `n / d * d ≤ n` and
`n < (n / d + 1) * d`.

# Intent
- For a nonzero divisor, the quotient times the divisor does not exceed the dividend.
- For a nonzero divisor, the dividend is less than the quotient plus one, times the divisor.
- Division by zero is undefined for this requirement; the claim must not assert anything about a
  zero divisor. -/
def D_hypothesis : Prop := ∀ n d : Nat, d ≠ 0 → d ≤ n → n / d * d ≤ n ∧ n < (n / d + 1) * d

/-! ### E (test): an even number above every number -/

/-- For every natural number `n` there is a natural number `m` such that `m` is even and `n < m`.

# Intent
- Every natural number is exceeded by some even number, which may be chosen depending on it. -/
def E_base : Prop := ∀ n : Nat, ∃ m : Nat, m % 2 = 0 ∧ n < m

/-- For every natural number `n` there is a natural number `k` with `n < 2 * k`.

# Intent
- Every natural number is exceeded by some even number, which may be chosen depending on it. -/
def E_rewrite : Prop := ∀ n : Nat, ∃ k : Nat, n < 2 * k

/-- There is a natural number `m` such that `m` is even and every natural number `n` satisfies
`n < m`.

# Intent
- Every natural number is exceeded by some even number, which may be chosen depending on it. -/
def E_swap : Prop := ∃ m : Nat, m % 2 = 0 ∧ ∀ n : Nat, n < m

/-- For every natural number `n` there is a natural number `m` such that `m` is even and `n ≤ m`.

# Intent
- Every natural number is exceeded by some even number, which may be chosen depending on it. -/
def E_weaken : Prop := ∀ n : Nat, ∃ m : Nat, m % 2 = 0 ∧ n ≤ m

/-- For every natural number `n` there is a natural number `m` with `n < m`.

# Intent
- Every natural number is exceeded by some even number, which may be chosen depending on it. -/
def E_drop : Prop := ∀ n : Nat, ∃ m : Nat, n < m

/-! ### F (test): one bound for every input -/

/-- There is a natural number `b` such that every natural number `i` satisfies `cost i ≤ b`.

# Intent
- One bound, fixed before any input is chosen, limits the cost of every input. -/
def F_base : Prop := ∃ b : Nat, ∀ i : Nat, IntentCorpus.cost i ≤ b

/-- There is a natural number `b` such that every natural number `i` satisfies `cost i < b`.

# Intent
- One bound, fixed before any input is chosen, limits the cost of every input. -/
def F_rewrite : Prop := ∃ b : Nat, ∀ i : Nat, IntentCorpus.cost i < b

/-- For every natural number `i` there is a natural number `b` with `cost i ≤ b`.

# Intent
- One bound, fixed before any input is chosen, limits the cost of every input. -/
def F_swap : Prop := ∀ i : Nat, ∃ b : Nat, IntentCorpus.cost i ≤ b

/-- There is a natural number `b` such that every natural number `i < 100` satisfies
`cost i ≤ b`.

# Intent
- One bound, fixed before any input is chosen, limits the cost of every input. -/
def F_hypothesis : Prop := ∃ b : Nat, ∀ i : Nat, i < 100 → IntentCorpus.cost i ≤ b

/-! ### G (test): subtraction round trip -/

/-- For all natural numbers `a` and `b` with `b ≤ a`, `a - b + b = a`.

# Intent
- Subtracting `b` from `a` and adding `b` back returns `a`, whenever `b` does not exceed `a`.
- Subtraction with `b` greater than `a` is outside this requirement; the claim must not rely on
  truncated subtraction. -/
def G_base : Prop := ∀ a b : Nat, b ≤ a → a - b + b = a

/-- For all natural numbers `a` and `b` with `b ≤ a`, `b + (a - b) = a`.

# Intent
- Subtracting `b` from `a` and adding `b` back returns `a`, whenever `b` does not exceed `a`.
- Subtraction with `b` greater than `a` is outside this requirement; the claim must not rely on
  truncated subtraction. -/
def G_rewrite : Prop := ∀ a b : Nat, b ≤ a → b + (a - b) = a

/-- For all natural numbers `a` and `b`, `a - b + b = max a b` (natural-number subtraction
truncates at `0`).

# Intent
- Subtracting `b` from `a` and adding `b` back returns `a`, whenever `b` does not exceed `a`.
- Subtraction with `b` greater than `a` is outside this requirement; the claim must not rely on
  truncated subtraction. -/
def G_totalize : Prop := ∀ a b : Nat, a - b + b = max a b

/-- For all natural numbers `a` and `b` with `b ≤ a` and `b ≤ 5`, `a - b + b = a`.

# Intent
- Subtracting `b` from `a` and adding `b` back returns `a`, whenever `b` does not exceed `a`.
- Subtraction with `b` greater than `a` is outside this requirement; the claim must not rely on
  truncated subtraction. -/
def G_hypothesis : Prop := ∀ a b : Nat, b ≤ a → b ≤ 5 → a - b + b = a

/-- For all natural numbers `a` and `b` with `b ≤ a`, `a - b + b ≤ a`.

# Intent
- Subtracting `b` from `a` and adding `b` back returns `a`, whenever `b` does not exceed `a`.
- Subtraction with `b` greater than `a` is outside this requirement; the claim must not rely on
  truncated subtraction. -/
def G_weaken : Prop := ∀ a b : Nat, b ≤ a → a - b + b ≤ a

/-! ### H (test): limiter admission -/

/-- For all natural numbers `c`, `u` and `r`, `admits c u r` is true exactly when `u + r ≤ c`.

# Intent
- An admitted request never takes usage above capacity.
- A request is admitted whenever it fits within the remaining capacity. -/
def H_base : Prop := ∀ c u r : Nat, IntentCorpus.admits c u r = true ↔ u + r ≤ c

/-- For all natural numbers `c`, `u` and `r`, `admits c u r` is true exactly when `u + r < c + 1`.

# Intent
- An admitted request never takes usage above capacity.
- A request is admitted whenever it fits within the remaining capacity. -/
def H_rewrite : Prop := ∀ c u r : Nat, IntentCorpus.admits c u r = true ↔ u + r < c + 1

/-- For all natural numbers `c`, `u` and `r`, if `admits c u r` is true then `u + r ≤ c`.

# Intent
- An admitted request never takes usage above capacity.
- A request is admitted whenever it fits within the remaining capacity. -/
def H_drop : Prop := ∀ c u r : Nat, IntentCorpus.admits c u r = true → u + r ≤ c

/-- For all natural numbers `c`, `u` and `r`, `admits c u r` is true exactly when `u + r ≤ c + 1`.

# Intent
- An admitted request never takes usage above capacity.
- A request is admitted whenever it fits within the remaining capacity. -/
def H_weaken : Prop := ∀ c u r : Nat, IntentCorpus.admits c u r = true ↔ u + r ≤ c + 1

/-- For all natural numbers `c`, `u` and `r` with `u ≤ c`, `admits c u r` is true exactly when
`u + r ≤ c`.

# Intent
- An admitted request never takes usage above capacity.
- A request is admitted whenever it fits within the remaining capacity. -/
def H_hypothesis : Prop := ∀ c u r : Nat, u ≤ c → (IntentCorpus.admits c u r = true ↔ u + r ≤ c)

/-! ### I (test): reversing twice -/

/-- For every list `l` of natural numbers, reversing `l` twice gives `l`.

# Intent
- Reversing a list twice returns the original list. -/
def I_base : Prop := ∀ l : List Nat, l.reverse.reverse = l

/-- For every list `l` of natural numbers, `l` equals `l` reversed twice.

# Intent
- Reversing a list twice returns the original list. -/
def I_rewrite : Prop := ∀ l : List Nat, l = l.reverse.reverse

/-- For every list `l` of natural numbers with at most three elements, reversing `l` twice
gives `l`.

# Intent
- Reversing a list twice returns the original list. -/
def I_hypothesis : Prop := ∀ l : List Nat, l.length ≤ 3 → l.reverse.reverse = l

/-- For every list `l` of natural numbers, `l` reversed twice has at most as many elements as
`l`.

# Intent
- Reversing a list twice returns the original list. -/
def I_weaken : Prop := ∀ l : List Nat, l.reverse.reverse.length ≤ l.length

/-! ### J (test): filtering -/

/-- For every predicate `p` on natural numbers, list `l` and value `x`, if `x` is in
`l.filter p` then `p x` is true and `x` is in `l`.

# Intent
- Every element kept by filtering satisfies the predicate.
- Every element kept by filtering comes from the original list. -/
def J_base : Prop :=
  ∀ (p : Nat → Bool) (l : List Nat) (x : Nat), x ∈ l.filter p → p x = true ∧ x ∈ l

/-- For every predicate `p` on natural numbers, list `l` and value `x`, `x` is in `l.filter p`
exactly when `x` is in `l` and `p x` is true.

# Intent
- Every element kept by filtering satisfies the predicate.
- Every element kept by filtering comes from the original list. -/
def J_rewrite : Prop :=
  ∀ (p : Nat → Bool) (l : List Nat) (x : Nat), x ∈ l.filter p ↔ x ∈ l ∧ p x = true

/-- For every predicate `p` on natural numbers, list `l` and value `x`, if `x` is in
`l.filter p` then `p x` is true.

# Intent
- Every element kept by filtering satisfies the predicate.
- Every element kept by filtering comes from the original list. -/
def J_drop : Prop := ∀ (p : Nat → Bool) (l : List Nat) (x : Nat), x ∈ l.filter p → p x = true

/-- There is a natural number `x` such that for every predicate `p` and list `l`, if `x` is in
`l.filter p` then `p x` is true and `x` is in `l`.

# Intent
- Every element kept by filtering satisfies the predicate.
- Every element kept by filtering comes from the original list. -/
def J_swap : Prop :=
  ∃ x : Nat, ∀ (p : Nat → Bool) (l : List Nat), x ∈ l.filter p → p x = true ∧ x ∈ l

/-! ### K (test): minimum of a nonempty list -/

/-- For every nonempty list `l` of natural numbers there is `m` with `l.min? = some m` and `m` at
most every element of `l`.

# Intent
- Every nonempty list has a minimum that is at most each of its elements.
- The empty list is excluded; the claim makes no statement about it. -/
def K_base : Prop := ∀ l : List Nat, l ≠ [] → ∃ m, l.min? = some m ∧ ∀ x ∈ l, m ≤ x

/-- For every list `l` of natural numbers with positive length there is `m` with
`l.min? = some m` and `m` at most every element of `l`.

# Intent
- Every nonempty list has a minimum that is at most each of its elements.
- The empty list is excluded; the claim makes no statement about it. -/
def K_rewrite : Prop := ∀ l : List Nat, 0 < l.length → ∃ m, l.min? = some m ∧ ∀ x ∈ l, m ≤ x

/-- There is a natural number `m` such that every nonempty list `l` of natural numbers has
`l.min? = some m` and `m` at most every element of `l`.

# Intent
- Every nonempty list has a minimum that is at most each of its elements.
- The empty list is excluded; the claim makes no statement about it. -/
def K_swap : Prop := ∃ m, ∀ l : List Nat, l ≠ [] → l.min? = some m ∧ ∀ x ∈ l, m ≤ x

/-- For every nonempty list `l` of natural numbers there is `m` with `l.min? = some m`.

# Intent
- Every nonempty list has a minimum that is at most each of its elements.
- The empty list is excluded; the claim makes no statement about it. -/
def K_drop : Prop := ∀ l : List Nat, l ≠ [] → ∃ m, l.min? = some m

/-- For every nonempty list `l` of natural numbers there is `m` with `l.min? = some m` and `m` at
most one more than every element of `l`.

# Intent
- Every nonempty list has a minimum that is at most each of its elements.
- The empty list is excluded; the claim makes no statement about it. -/
def K_weaken : Prop := ∀ l : List Nat, l ≠ [] → ∃ m, l.min? = some m ∧ ∀ x ∈ l, m ≤ x + 1

/-! ### L (test): average of a nonempty list -/

/-- For every nonempty list `l` of natural numbers, `l.sum / l.length ≤ l.sum`.

# Intent
- For a nonempty list, the average (the sum divided by the length, rounded down) is at most the sum.
- The empty list has no average; the claim makes no statement about it. -/
def L_base : Prop := ∀ l : List Nat, l ≠ [] → l.sum / l.length ≤ l.sum

/-- For every list `l` of natural numbers with positive length, `l.sum / l.length ≤ l.sum`.

# Intent
- For a nonempty list, the average (the sum divided by the length, rounded down) is at most the sum.
- The empty list has no average; the claim makes no statement about it. -/
def L_rewrite : Prop := ∀ l : List Nat, 0 < l.length → l.sum / l.length ≤ l.sum

/-- For every list `l` of natural numbers, `l.sum / l.length ≤ l.sum` (for the empty list this
uses `0 / 0 = 0`).

# Intent
- For a nonempty list, the average (the sum divided by the length, rounded down) is at most the sum.
- The empty list has no average; the claim makes no statement about it. -/
def L_totalize : Prop := ∀ l : List Nat, l.sum / l.length ≤ l.sum

/-- For every nonempty list `l` of natural numbers with at most ten elements,
`l.sum / l.length ≤ l.sum`.

# Intent
- For a nonempty list, the average (the sum divided by the length, rounded down) is at most the sum.
- The empty list has no average; the claim makes no statement about it. -/
def L_hypothesis : Prop := ∀ l : List Nat, l ≠ [] → l.length ≤ 10 → l.sum / l.length ≤ l.sum

/-! ### M (test): predecessor -/

/-- For every natural number `n` with `0 < n`, `n - 1 + 1 = n`.

# Intent
- Every positive natural number is one more than its predecessor.
- Zero has no predecessor; the claim must not rely on subtraction truncating at zero. -/
def M_base : Prop := ∀ n : Nat, 0 < n → n - 1 + 1 = n

/-- For every natural number `n` with `n ≠ 0`, `n - 1 + 1 = n`.

# Intent
- Every positive natural number is one more than its predecessor.
- Zero has no predecessor; the claim must not rely on subtraction truncating at zero. -/
def M_rewrite : Prop := ∀ n : Nat, n ≠ 0 → n - 1 + 1 = n

/-- For every natural number `n`, `n - 1 + 1 = max n 1` (for `n = 0` this uses `0 - 1 = 0`).

# Intent
- Every positive natural number is one more than its predecessor.
- Zero has no predecessor; the claim must not rely on subtraction truncating at zero. -/
def M_totalize : Prop := ∀ n : Nat, n - 1 + 1 = max n 1

/-- For every natural number `n` with `0 < n`, `n - 1 + 1 ≤ n`.

# Intent
- Every positive natural number is one more than its predecessor.
- Zero has no predecessor; the claim must not rely on subtraction truncating at zero. -/
def M_weaken : Prop := ∀ n : Nat, 0 < n → n - 1 + 1 ≤ n

/-! ### O (test): a bound for each list -/

/-- For every list `l` of natural numbers there is a natural number `b` with every element of
`l` at most `b`.

# Intent
- Every list has an upper bound on its elements, which may be chosen depending on the list. -/
def O_base : Prop := ∀ l : List Nat, ∃ b : Nat, ∀ x ∈ l, x ≤ b

/-- For every list `l` of natural numbers there is a natural number `b` with every element of
`l` less than `b + 1`.

# Intent
- Every list has an upper bound on its elements, which may be chosen depending on the list. -/
def O_rewrite : Prop := ∀ l : List Nat, ∃ b : Nat, ∀ x ∈ l, x < b + 1

/-- There is a natural number `b` such that for every list `l` of natural numbers, every
element of `l` is at most `b`.

# Intent
- Every list has an upper bound on its elements, which may be chosen depending on the list. -/
def O_swap : Prop := ∃ b : Nat, ∀ l : List Nat, ∀ x ∈ l, x ≤ b

/-! ### P (test): common multiples -/

/-- For all natural numbers `a` and `b` there is a natural number `m` divisible by both.

# Intent
- Any two natural numbers have a common multiple, which may be chosen depending on them. -/
def P_base : Prop := ∀ a b : Nat, ∃ m : Nat, a ∣ m ∧ b ∣ m

/-- For all natural numbers `a` and `b` there is a natural number `m` divisible by `b` and by `a`.

# Intent
- Any two natural numbers have a common multiple, which may be chosen depending on them. -/
def P_rewrite : Prop := ∀ a b : Nat, ∃ m : Nat, b ∣ m ∧ a ∣ m

/-- There is a natural number `m` divisible by every pair of natural numbers `a` and `b`.

# Intent
- Any two natural numbers have a common multiple, which may be chosen depending on them. -/
def P_swap : Prop := ∃ m : Nat, ∀ a b : Nat, a ∣ m ∧ b ∣ m

/-! ### Q (test): first element -/

/-- For every nonempty list `l` of natural numbers there is `x` with `l.head? = some x` and
`x ∈ l`.

# Intent
- Every nonempty list has a first element, and it is one of the list's elements.
- The empty list has no first element; the claim makes no statement about it. -/
def Q_base : Prop := ∀ l : List Nat, l ≠ [] → ∃ x, l.head? = some x ∧ x ∈ l

/-- For every list `l` of natural numbers with positive length there is `x` with
`l.head? = some x` and `x ∈ l`.

# Intent
- Every nonempty list has a first element, and it is one of the list's elements.
- The empty list has no first element; the claim makes no statement about it. -/
def Q_rewrite : Prop := ∀ l : List Nat, 0 < l.length → ∃ x, l.head? = some x ∧ x ∈ l

/-- For every list `l` of natural numbers, `l.headD 0` (the first element, or `0` for the empty
list) is an element of `l`.

# Intent
- Every nonempty list has a first element, and it is one of the list's elements.
- The empty list has no first element; the claim makes no statement about it. -/
def Q_totalize : Prop := ∀ l : List Nat, l.headD 0 ∈ l

/-- For every nonempty list `l` of natural numbers there is `x` with `l.head? = some x`.

# Intent
- Every nonempty list has a first element, and it is one of the list's elements.
- The empty list has no first element; the claim makes no statement about it. -/
def Q_drop : Prop := ∀ l : List Nat, l ≠ [] → ∃ x, l.head? = some x

/-! ### Formal clauses for the correspondence judgment -/

/-- Formal clause labelled as stating the average clause: for a nonempty list, the sum divided
by the length is at most the sum. -/
def L_formal : Prop := ∀ l : List Nat, l ≠ [] → l.sum / l.length ≤ l.sum
/-- Formal clause labelled as not stating the average clause: it omits the nonempty hypothesis. -/
def L_formal_bad : Prop := ∀ l : List Nat, l.sum / l.length ≤ l.sum
/-- Formal clause labelled as stating the predecessor clause: for positive `n`,
`n - 1 + 1 = n`. -/
def M_formal : Prop := ∀ n : Nat, 0 < n → n - 1 + 1 = n
/-- Formal clause labelled as not stating the predecessor clause: it omits `0 < n`. -/
def M_formal_bad : Prop := ∀ n : Nat, n - 1 + 1 = n
/-- Formal clause labelled as stating the first-element clause: a nonempty list has a first
element, and it belongs to the list. -/
def Q_formal : Prop := ∀ l : List Nat, l ≠ [] → ∃ x, l.head? = some x ∧ x ∈ l
/-- Formal clause labelled as not stating the first-element clause: it omits that the first
element belongs to the list. -/
def Q_formal_bad : Prop := ∀ l : List Nat, l ≠ [] → ∃ x, l.head? = some x

/-- Formal clause labelled as stating the sorted-order clause: `mergeSort`'s output is pairwise
nondecreasing. -/
def C_formal_order : Prop := ∀ l : List Nat, l.mergeSort.Pairwise (· ≤ ·)
/-- Formal clause labelled as not stating the sorted-order clause: it requires nonincreasing
order. -/
def C_formal_order_bad : Prop := ∀ l : List Nat, l.mergeSort.Pairwise (· ≥ ·)
/-- Formal clause labelled as stating the same-elements clause: `mergeSort`'s output is a
permutation of its input. -/
def C_formal_perm : Prop := ∀ l : List Nat, l.mergeSort.Perm l
/-- Formal clause labelled as not stating the same-elements clause: equal membership ignores
multiplicity. -/
def C_formal_perm_bad : Prop := ∀ l : List Nat, ∀ x, x ∈ l.mergeSort ↔ x ∈ l
/-- Formal clause labelled as stating the quotient clause: for a nonzero divisor,
`n / d * d ≤ n`. -/
def D_formal_lower : Prop := ∀ n d : Nat, d ≠ 0 → n / d * d ≤ n
/-- Formal clause labelled as not stating the quotient clause: it omits `d ≠ 0`. -/
def D_formal_lower_bad : Prop := ∀ n d : Nat, n / d * d ≤ n
/-- Formal clause labelled as stating the even-number clause: every `n` is exceeded by some
even `m` chosen after `n`. -/
def E_formal : Prop := ∀ n : Nat, ∃ m : Nat, m % 2 = 0 ∧ n < m
/-- Formal clause labelled as not stating the even-number clause: its quantifiers are swapped,
so one even `m` must exceed every `n`. -/
def E_formal_bad : Prop := ∃ m : Nat, m % 2 = 0 ∧ ∀ n : Nat, n < m
/-- Formal clause labelled as stating the subtract-and-add clause: `a - b + b = a` whenever
`b ≤ a`. -/
def G_formal : Prop := ∀ a b : Nat, b ≤ a → a - b + b = a
/-- Formal clause labelled as not stating the subtract-and-add clause: it omits `b ≤ a`. -/
def G_formal_bad : Prop := ∀ a b : Nat, a - b + b = a
/-- Formal clause labelled as stating the admission clause: an admitted request keeps usage
within capacity. -/
def H_formal_sound : Prop := ∀ c u r : Nat, IntentCorpus.admits c u r = true → u + r ≤ c
/-- Formal clause labelled as not stating the admission clause: it states the converse. -/
def H_formal_sound_bad : Prop := ∀ c u r : Nat, u + r ≤ c → IntentCorpus.admits c u r = true
/-- Formal clause labelled as stating the double-reversal clause: reversing twice returns the
list. -/
def I_formal : Prop := ∀ l : List Nat, l.reverse.reverse = l
/-- Formal clause labelled as not stating the double-reversal clause: it states that reversal
keeps the length. -/
def I_formal_bad : Prop := ∀ l : List Nat, l.reverse.length = l.length
/-- Formal clause labelled as stating the filtering clause: every element `filter` keeps is
in the original list. -/
def J_formal_member : Prop := ∀ (p : Nat → Bool) (l : List Nat) (x : Nat), x ∈ l.filter p → x ∈ l
/-- Formal clause labelled as not stating the filtering clause: it concludes that the kept
element satisfies the predicate instead. -/
def J_formal_member_bad : Prop := ∀ (p : Nat → Bool) (l : List Nat) (x : Nat), x ∈ l.filter p →
    p x = true
/-- Formal clause labelled as stating the minimum clause: a nonempty list has a minimum at most
each of its elements. -/
def K_formal : Prop := ∀ l : List Nat, l ≠ [] → ∃ m, l.min? = some m ∧ ∀ x ∈ l, m ≤ x
/-- Formal clause labelled as not stating the minimum clause: its bound `m ≤ x + 1` is looser. -/
def K_formal_bad : Prop := ∀ l : List Nat, l ≠ [] → ∃ m, l.min? = some m ∧ ∀ x ∈ l, m ≤ x + 1

/-! ### A discharged clause, exercising the kernel-checked path -/

/-- For every list `l` of natural numbers, `l.mergeSort` is pairwise nondecreasing and is a
permutation of `l`.

# Intent
- Sorting returns its output in nondecreasing order.
- The output contains exactly the input's elements, each as many times as in the input. (discharged
  by `IntentCorpus.mergeSort_perm_of_correct`) -/
theorem mergeSort_correct : ∀ l : List Nat, l.mergeSort.Pairwise (· ≤ ·) ∧ l.mergeSort.Perm l :=
  fun l => ⟨by
    have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l
    simpa using this, List.mergeSort_perm l _⟩

/-- The claim `mergeSort_correct` implies the formal permutation clause. -/
theorem mergeSort_perm_of_correct :
    (∀ l : List Nat, l.mergeSort.Pairwise (· ≤ ·) ∧ l.mergeSort.Perm l) →
      ∀ l : List Nat, l.mergeSort.Perm l :=
  fun h l => (h l).2

end IntentCorpus

namespace Regula.Screen.Corpus

open RegulaPolicy.Screening

/-- The five mutation kinds of issue #58, `base` and `rewrite` for correct pairs, and the two
correspondence-pair kinds. -/
inductive Mutation where
  /-- A correct intent/claim pair. -/
  | base
  /-- The base requirement stated differently: a correct pair and false-positive control. -/
  | rewrite
  /-- The base claim with a required conjunct dropped. -/
  | dropConjunct
  /-- The base claim with its quantifier order changed. -/
  | swapQuantifiers
  /-- The base claim with an inequality or bound loosened. -/
  | weakenInequality
  /-- The base claim with an extra hypothesis. -/
  | addHypothesis
  /-- The base claim extended to a case the intent excludes, where it holds only by a partial
  operation's conventional value. -/
  | totalize
  /-- Correspondence pairs: a formal clause that does, or does not, state its English clause. -/
  | formalCorrect
  /-- A correspondence pair whose formal clause does not state its English clause. -/
  | formalWrong
  deriving Repr, DecidableEq

/-- The kind's kebab-case name in the evidence rows, such as `drop-conjunct`. -/
def Mutation.spelling : Mutation → String
  | .base => "base" | .rewrite => "rewrite" | .dropConjunct => "drop-conjunct"
  | .swapQuantifiers => "swap-quantifiers" | .weakenInequality => "weaken-inequality"
  | .addHypothesis => "add-hypothesis" | .totalize => "totalize"
  | .formalCorrect => "formal-correct" | .formalWrong => "formal-wrong"

/-- The part of the corpus an item belongs to; each calibration run judges one split. -/
inductive Split where
  /-- Bases `A` and `B`, used to exercise the runner and wording before the test run. -/
  | dev
  /-- Every other base, for the single test run; the correspondence pairs are also test items. -/
  | test
  deriving Repr, DecidableEq

/-- One labelled item. Targeted labels are `true` when the claim is acceptable in that
respect (the Noul's yes). -/
structure Item where
  /-- The item's `IntentCorpus` definition, read as a claim. -/
  name : Lean.Name
  /-- The base item it derives from (itself for a base), whose Intent clauses it must share
  and whose explanation its stale variant is paired with. -/
  base : Lean.Name
  /-- How the item's claim relates to its base's. -/
  mutation : Mutation
  /-- The split the item belongs to. -/
  split : Split
  /-- Indexes of intent clauses the claim does not imply. -/
  uncovered : List Nat := []
  /-- The labelled strength of the claim against the whole intent. -/
  strength : Strength
  /-- Label: the claim keeps the quantifier order and dependence the intent requires. -/
  quantifierOrder : Bool := true
  /-- Label: the claim does not depend on a partial operation's conventional value in a case
  the intent leaves undefined. -/
  totalization : Bool := true
  /-- Label: the claim honors every exclusion and limit the intent states. -/
  exclusions : Bool := true

/-- The labelled calibration items, grouped by base (`A` to `Q`), each base first. -/
def items : List Item := [
  -- A (dev)
  { name := ``IntentCorpus.A_base, base := ``IntentCorpus.A_base, mutation := .base, split := .dev,
      strength := .equivalent },
  { name := ``IntentCorpus.A_rewrite, base := ``IntentCorpus.A_base, mutation := .rewrite, split :=
      .dev, strength := .equivalent },
  { name := ``IntentCorpus.A_weaken, base := ``IntentCorpus.A_base, mutation := .weakenInequality,
      split := .dev,
    uncovered := [0, 1], strength := .weaker },
  { name := ``IntentCorpus.A_hypothesis, base := ``IntentCorpus.A_base, mutation := .addHypothesis,
      split := .dev,
    uncovered := [0, 1], strength := .weaker },
  -- B (dev)
  { name := ``IntentCorpus.B_base, base := ``IntentCorpus.B_base, mutation := .base, split := .dev,
      strength := .equivalent },
  { name := ``IntentCorpus.B_rewrite, base := ``IntentCorpus.B_base, mutation := .rewrite, split :=
      .dev, strength := .equivalent },
  { name := ``IntentCorpus.B_drop, base := ``IntentCorpus.B_base, mutation := .dropConjunct,
      split := .dev,
    uncovered := [0], strength := .weaker },
  { name := ``IntentCorpus.B_weaken, base := ``IntentCorpus.B_base, mutation := .weakenInequality,
      split := .dev,
    uncovered := [1], strength := .weaker },
  { name := ``IntentCorpus.B_totalize, base := ``IntentCorpus.B_base, mutation := .totalize,
      split := .dev,
    uncovered := [2], strength := .incomparable, totalization := false, exclusions := false },
  -- C
  { name := ``IntentCorpus.C_base, base := ``IntentCorpus.C_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.C_rewrite, base := ``IntentCorpus.C_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.C_drop, base := ``IntentCorpus.C_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [1], strength := .weaker },
  { name := ``IntentCorpus.C_weaken, base := ``IntentCorpus.C_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [0], strength := .weaker },
  { name := ``IntentCorpus.C_hypothesis, base := ``IntentCorpus.C_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0, 1], strength := .weaker },
  -- D
  { name := ``IntentCorpus.D_base, base := ``IntentCorpus.D_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.D_rewrite, base := ``IntentCorpus.D_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.D_totalize, base := ``IntentCorpus.D_base, mutation := .totalize,
      split := .test,
    uncovered := [2], strength := .incomparable, totalization := false, exclusions := false },
  { name := ``IntentCorpus.D_drop, base := ``IntentCorpus.D_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [1], strength := .weaker },
  { name := ``IntentCorpus.D_weaken, base := ``IntentCorpus.D_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [1], strength := .weaker },
  { name := ``IntentCorpus.D_hypothesis, base := ``IntentCorpus.D_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0, 1], strength := .weaker },
  -- E
  { name := ``IntentCorpus.E_base, base := ``IntentCorpus.E_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.E_rewrite, base := ``IntentCorpus.E_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.E_swap, base := ``IntentCorpus.E_base, mutation := .swapQuantifiers,
      split := .test,
    strength := .stronger, quantifierOrder := false },
  { name := ``IntentCorpus.E_weaken, base := ``IntentCorpus.E_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [0], strength := .weaker },
  { name := ``IntentCorpus.E_drop, base := ``IntentCorpus.E_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- F
  { name := ``IntentCorpus.F_base, base := ``IntentCorpus.F_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.F_rewrite, base := ``IntentCorpus.F_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.F_swap, base := ``IntentCorpus.F_base, mutation := .swapQuantifiers,
      split := .test,
    uncovered := [0], strength := .weaker, quantifierOrder := false },
  { name := ``IntentCorpus.F_hypothesis, base := ``IntentCorpus.F_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- G
  { name := ``IntentCorpus.G_base, base := ``IntentCorpus.G_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.G_rewrite, base := ``IntentCorpus.G_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.G_totalize, base := ``IntentCorpus.G_base, mutation := .totalize,
      split := .test,
    uncovered := [1], strength := .incomparable, totalization := false, exclusions := false },
  { name := ``IntentCorpus.G_hypothesis, base := ``IntentCorpus.G_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0], strength := .weaker },
  { name := ``IntentCorpus.G_weaken, base := ``IntentCorpus.G_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- H
  { name := ``IntentCorpus.H_base, base := ``IntentCorpus.H_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.H_rewrite, base := ``IntentCorpus.H_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.H_drop, base := ``IntentCorpus.H_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [1], strength := .weaker },
  { name := ``IntentCorpus.H_weaken, base := ``IntentCorpus.H_base, mutation := .weakenInequality,
      split := .test,
    -- Erratum after the test run, disclosed in the guide: the claim asserts admission when
    -- usage would reach capacity + 1, ignoring the stated limit.
    uncovered := [0], strength := .incomparable, exclusions := false },
  { name := ``IntentCorpus.H_hypothesis, base := ``IntentCorpus.H_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0, 1], strength := .weaker },
  -- I
  { name := ``IntentCorpus.I_base, base := ``IntentCorpus.I_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.I_rewrite, base := ``IntentCorpus.I_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.I_hypothesis, base := ``IntentCorpus.I_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0], strength := .weaker },
  { name := ``IntentCorpus.I_weaken, base := ``IntentCorpus.I_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- J
  { name := ``IntentCorpus.J_base, base := ``IntentCorpus.J_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.J_rewrite, base := ``IntentCorpus.J_base, mutation := .rewrite, split :=
      .test, strength := .stronger },
  { name := ``IntentCorpus.J_drop, base := ``IntentCorpus.J_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [1], strength := .weaker },
  { name := ``IntentCorpus.J_swap, base := ``IntentCorpus.J_base, mutation := .swapQuantifiers,
      split := .test,
    uncovered := [0, 1], strength := .weaker, quantifierOrder := false },
  -- K
  { name := ``IntentCorpus.K_base, base := ``IntentCorpus.K_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.K_rewrite, base := ``IntentCorpus.K_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.K_swap, base := ``IntentCorpus.K_base, mutation := .swapQuantifiers,
      split := .test,
    strength := .stronger, quantifierOrder := false },
  { name := ``IntentCorpus.K_drop, base := ``IntentCorpus.K_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [0], strength := .weaker },
  { name := ``IntentCorpus.K_weaken, base := ``IntentCorpus.K_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- L
  { name := ``IntentCorpus.L_base, base := ``IntentCorpus.L_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.L_rewrite, base := ``IntentCorpus.L_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.L_totalize, base := ``IntentCorpus.L_base, mutation := .totalize,
      split := .test,
    uncovered := [1], strength := .incomparable, totalization := false, exclusions := false },
  { name := ``IntentCorpus.L_hypothesis, base := ``IntentCorpus.L_base, mutation := .addHypothesis,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- M
  { name := ``IntentCorpus.M_base, base := ``IntentCorpus.M_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.M_rewrite, base := ``IntentCorpus.M_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.M_totalize, base := ``IntentCorpus.M_base, mutation := .totalize,
      split := .test,
    uncovered := [1], strength := .incomparable, totalization := false, exclusions := false },
  { name := ``IntentCorpus.M_weaken, base := ``IntentCorpus.M_base, mutation := .weakenInequality,
      split := .test,
    uncovered := [0], strength := .weaker },
  -- O
  { name := ``IntentCorpus.O_base, base := ``IntentCorpus.O_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.O_rewrite, base := ``IntentCorpus.O_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.O_swap, base := ``IntentCorpus.O_base, mutation := .swapQuantifiers,
      split := .test,
    strength := .stronger, quantifierOrder := false },
  -- P
  { name := ``IntentCorpus.P_base, base := ``IntentCorpus.P_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.P_rewrite, base := ``IntentCorpus.P_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.P_swap, base := ``IntentCorpus.P_base, mutation := .swapQuantifiers,
      split := .test,
    strength := .stronger, quantifierOrder := false },
  -- Q
  { name := ``IntentCorpus.Q_base, base := ``IntentCorpus.Q_base, mutation := .base, split := .test,
      strength := .equivalent },
  { name := ``IntentCorpus.Q_rewrite, base := ``IntentCorpus.Q_base, mutation := .rewrite, split :=
      .test, strength := .equivalent },
  { name := ``IntentCorpus.Q_totalize, base := ``IntentCorpus.Q_base, mutation := .totalize,
      split := .test,
    uncovered := [1], strength := .incomparable, totalization := false, exclusions := false },
  { name := ``IntentCorpus.Q_drop, base := ``IntentCorpus.Q_base, mutation := .dropConjunct,
      split := .test,
    uncovered := [0], strength := .weaker }]

/-- One labelled English-clause / Lean-clause pair (test split). -/
structure CorrespondenceItem where
  /-- The English clause. -/
  clause : String
  /-- The `IntentCorpus` definition whose value is the formal clause. -/
  formal : Lean.Name
  /-- Label: `true` when the formal clause states exactly the English clause. -/
  label : Bool

/-- The labelled correspondence pairs: for each of twelve English clauses, one formal clause
labelled as stating it and one labelled as not stating it. -/
def correspondenceItems : List CorrespondenceItem :=
  let sorted := "Sorting returns its output in nondecreasing order."
  let perm :=
      "The output contains exactly the input's elements, each as many times as in the input."
  let lower := "For a nonzero divisor, the quotient times the divisor does not exceed the dividend."
  let even :=
      "Every natural number is exceeded by some even number, which may be chosen depending on it."
  let round :=
      "Subtracting `b` from `a` and adding `b` back returns `a`, whenever `b` does not exceed `a`."
  let sound := "An admitted request never takes usage above capacity."
  let rev := "Reversing a list twice returns the original list."
  let member := "Every element kept by filtering comes from the original list."
  let minimum := "Every nonempty list has a minimum that is at most each of its elements."
  let average := "For a nonempty list, the average (the sum divided by the length, rounded down) \
    is at most the sum."
  let predecessor := "Every positive natural number is one more than its predecessor."
  let first := "Every nonempty list has a first element, and it is one of the list's elements."
  [⟨sorted, ``IntentCorpus.C_formal_order, true⟩,
      ⟨sorted, ``IntentCorpus.C_formal_order_bad, false⟩,
   ⟨perm, ``IntentCorpus.C_formal_perm, true⟩, ⟨perm, ``IntentCorpus.C_formal_perm_bad, false⟩,
   ⟨lower, ``IntentCorpus.D_formal_lower, true⟩, ⟨lower, ``IntentCorpus.D_formal_lower_bad, false⟩,
   ⟨even, ``IntentCorpus.E_formal, true⟩, ⟨even, ``IntentCorpus.E_formal_bad, false⟩,
   ⟨round, ``IntentCorpus.G_formal, true⟩, ⟨round, ``IntentCorpus.G_formal_bad, false⟩,
   ⟨sound, ``IntentCorpus.H_formal_sound, true⟩, ⟨sound, ``IntentCorpus.H_formal_sound_bad, false⟩,
   ⟨rev, ``IntentCorpus.I_formal, true⟩, ⟨rev, ``IntentCorpus.I_formal_bad, false⟩,
   ⟨member, ``IntentCorpus.J_formal_member, true⟩,
       ⟨member, ``IntentCorpus.J_formal_member_bad, false⟩,
   ⟨minimum, ``IntentCorpus.K_formal, true⟩, ⟨minimum, ``IntentCorpus.K_formal_bad, false⟩,
   ⟨average, ``IntentCorpus.L_formal, true⟩, ⟨average, ``IntentCorpus.L_formal_bad, false⟩,
   ⟨predecessor, ``IntentCorpus.M_formal, true⟩, ⟨predecessor, ``IntentCorpus.M_formal_bad, false⟩,
   ⟨first, ``IntentCorpus.Q_formal, true⟩, ⟨first, ``IntentCorpus.Q_formal_bad, false⟩]

end Regula.Screen.Corpus
