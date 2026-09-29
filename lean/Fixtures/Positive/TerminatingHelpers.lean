/-
Positive control (issue #125): Lean's generated `_unsafe_rec` helpers of safe,
termination-checked definitions are admitted in each literal form Lean 4.34.0
elaborates differently: well-founded recursion with a fixed parameter and the
default `decreasing_tactic` (whose nested tactic information nodes carry the
dispatching elaborator's name over sub-syntax), a `where` helper with a
`decreasing_by` tactic block, a recursive definition carrying an attribute
(recorded under the attribute implementation's reference), a recursive
`abbrev` (abbreviation-hinted), structural recursion in a `mutual` block of
private definitions (each helper calls only the other member's helper), and
recursion through the module's own notation in a module that also declares
`IO` code: a notation's macro only rewrites syntax and `IO` code does not run
with Lean's elaborator state.
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
