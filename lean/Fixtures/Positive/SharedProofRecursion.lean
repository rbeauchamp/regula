/-
Positive control (issue #162) at the compiler boundary: safe recursive
definitions whose nested proofs Lean abstracts into auxiliary theorems that the
checker's regeneration cannot name alike. Lean names such a theorem from a
counter and from a cache of the propositions it has already abstracted in the
same process; no `.olean` stores that cache.

- `fixtures_once` proves the proposition `fixtures_twice` already proved, so
  Lean reuses `fixtures_twice`'s theorem and adds none under `fixtures_once`.
- `fixtures_cast_second` shares a `simp` proof inside a `Vector.cast` with
  `fixtures_cast_first`.
- `fixtures_extend_run`, by well-founded recursion, reuses the theorem of the
  structure field declared before it.
- `fixtures_shuffle_loop`, by structural recursion, numbers its own theorems
  differently from the regeneration.

Exact match admits each helper: the comparison puts every theorem the
regeneration abstracted back as its value and erases the proof, so no such
name takes part.
-/

def fixtures_positive (n : Nat) (_ : 0 < n) : Nat := n

def fixtures_twice : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_positive (n + 1) (by omega) + fixtures_positive (n + 1) (by omega) +
      fixtures_twice n

def fixtures_once : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_positive (n + 1) (by omega) + fixtures_once n

def fixtures_cast_first {size : Nat} (items : Vector Nat (size + 1)) : Nat → Nat
  | 0 => 0
  | n + 1 => (items.cast (by simp [Nat.add_comm]) : Vector Nat (1 + size))[0] +
      fixtures_cast_first items n

def fixtures_cast_second {size : Nat} (items : Vector Nat (size + 1)) : Nat → Nat
  | 0 => 1
  | n + 1 => (items.cast (by simp [Nat.add_comm]) : Vector Nat (1 + size))[0] +
      fixtures_cast_second items n

structure FixturesMapRun (bytes : ByteArray) (start : Nat) (inside : start < bytes.size) where
  count : Nat
  positive : 0 < count
  countBound : count ≤ 65535
  fits : start + count ≤ bytes.size
  same : ∀ offset, (bound : offset < count) →
    bytes[start + offset]'(by omega) = bytes[start]

def fixtures_extend_run (bytes : ByteArray) (start : Nat) (inside : start < bytes.size)
    (run : FixturesMapRun bytes start inside) : FixturesMapRun bytes start inside :=
  if room : run.count < 65535 ∧ start + run.count < bytes.size then
    if same : bytes[start + run.count] = bytes[start] then
      fixtures_extend_run bytes start inside ⟨run.count + 1, by have := run.positive; omega,
        by omega, by omega, by
          intro offset bound
          by_cases last : offset = run.count
          · subst offset; exact same
          · exact run.same offset (by omega)⟩
    else run
  else run
termination_by 65535 - run.count

structure FixturesCount where
  word : UInt64
  positive : 0 < word.toNat

def fixtures_count_of_nat (count : Nat) (positive : 0 < count) (fits : count < 2 ^ 64) :
    FixturesCount :=
  ⟨count.toUInt64, by
    change 0 < count % (2 ^ 64)
    rwa [Nat.mod_eq_of_lt fits]⟩

theorem fixtures_count_of_nat_exact (count : Nat) (positive : 0 < count)
    (fits : count < 2 ^ 64) : (fixtures_count_of_nat count positive fits).word.toNat = count :=
  Nat.mod_eq_of_lt fits

def fixtures_next_below (state : UInt64) (count : FixturesCount) :
    { word : UInt64 // word.toNat < count.word.toNat } × UInt64 :=
  (⟨state % count.word, by
    have := count.positive
    rw [UInt64.toNat_mod]
    exact Nat.mod_lt _ this⟩, state + 1)

def fixtures_shuffle_loop {α : Type} {size : Nat} (fits : size < 2 ^ 64) :
    (remaining : Nat) → Vector α size → UInt64 → remaining ≤ size → Vector α size × UInt64
  | 0, items, stream, _ => (items, stream)
  | 1, items, stream, _ => (items, stream)
  | remaining + 2, items, stream, bounded =>
    let count := fixtures_count_of_nat (remaining + 2) (by omega)
      (Nat.lt_of_le_of_lt bounded fits)
    let (selected, next) := fixtures_next_below stream count
    let hi : remaining + 1 < size := by omega
    let hj : selected.val.toNat < size := by
      have hb := selected.property
      have hc := fixtures_count_of_nat_exact (remaining + 2) (by omega)
        (Nat.lt_of_le_of_lt bounded fits)
      change count.word.toNat = remaining + 2 at hc
      omega
    fixtures_shuffle_loop fits (remaining + 1)
      (items.swap (remaining + 1) selected.val.toNat hi hj) next (by omega)
