/-
Positive control (issue #125): exact match admits Lean's generated `_unsafe_rec`
helpers of safe, termination-checked definitions in each form Lean 4.34.0
compiles differently: well-founded recursion with a fixed parameter and the
default `decreasing_tactic`, a `where` helper with a `decreasing_by` tactic
block, a recursive definition carrying an attribute, a recursive `abbrev`,
structural recursion in a `mutual` block of private definitions, recursion
through the module's own notation beside `IO` code, a decreasing proof that
Lean's default tactics cannot find (regenerated with the proof elided, the
base's own proof standing), and a lexicographic measure over two arguments
(packed into a unary function).
-/

def fixtures_walk (bytes : ByteArray) (start : Nat) : Nat :=
  if start < bytes.size then fixtures_walk bytes (start + 1) else start
termination_by bytes.size - start

def fixtures_outer (n : Nat) : Nat := go n 0
where
  go (k acc : Nat) : Nat :=
    if h : k = 0 then acc else go (k - 1) (acc + 1)
  termination_by k
  decreasing_by
    simp_wf
    omega

@[simp] def fixtures_simp_sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + fixtures_simp_sum xs

abbrev FixturesDepth : Nat → Type
  | 0 => Unit
  | n + 1 => Option (FixturesDepth n)

mutual
private def fixtures_even : Nat → Bool
  | 0 => true
  | n + 1 => fixtures_odd n
private def fixtures_odd : Nat → Bool
  | 0 => false
  | n + 1 => fixtures_even n
end

notation:max "fixturesTwice " x:max => x + x

def fixtures_doubling : Nat → Nat
  | 0 => 1
  | n + 1 => fixturesTwice (fixtures_doubling n)

def fixtures_announce (message : String) : IO Unit :=
  IO.println message

def fixtures_self_div (n : Nat) : Nat :=
  if h : n = 0 then 0 else fixtures_self_div (n - n / n) + 1
termination_by n
decreasing_by
  rw [Nat.div_self (Nat.pos_of_ne_zero h)]
  omega

def fixtures_two_args (a b : Nat) : Nat :=
  if a = 0 then b else if b = 0 then fixtures_two_args (a - 1) 5 else fixtures_two_args a (b - 1)
termination_by (a, b)
