module

/-
Positive control (found in review of PR #161) at the compiler boundary: in a
`module` file, safe recursive definitions that are `public` without
`@[expose]`. Lean does not export such a body, so it names the theorems it
abstracts from the body privately (`_private.….fixtures_module_sum._proof_1`),
while the checker's regeneration, outside any `module` file, names its own
publicly. Each form Lean compiles differently is present: structural
recursion, a `mutual` block, well-founded recursion that passes a tactic proof
to its recursive call, a lexicographic measure over two arguments (packed
into a unary function), and the functions derived for a public recursive
inductive, whose `DecidableEq` carries proofs. The same definitions
`@[expose] public` and not public stand beside them. Exact match admits every
helper: the comparison puts each theorem the regeneration abstracted back as
its value and erases the proof, so neither its name nor its privacy takes part.

Two forms of issue #183 are here too, `public` only: a `match` on the measured
argument after an argument that also changes, and structural recursion on a
later argument selected by `termination_by structural`. The regeneration is
given each one's termination argument although Lean does not export the body:
the relation from the base's value, the argument position from Lean's record.
-/

public def fixtures_module_positive (n : Nat) (_ : 0 < n) : Nat := n

public def fixtures_module_sum : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_module_positive (n + 1) (by omega) + fixtures_module_sum n

@[expose] public def fixtures_module_sum_exposed : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_module_positive (n + 1) (by omega) + fixtures_module_sum_exposed n

def fixtures_module_sum_private : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_module_positive (n + 1) (by omega) + fixtures_module_sum_private n

mutual
public def fixtures_module_even : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_module_positive (n + 1) (by omega) + fixtures_module_odd n
public def fixtures_module_odd : Nat → Nat
  | 0 => 1
  | n + 1 => fixtures_module_positive (n + 1) (by omega) + fixtures_module_even n
end

public def fixtures_module_all_small (bytes : ByteArray) (start : Nat)
    (checked : ∀ (index : Nat), index < start → ∀ (bound : index < bytes.size),
      bytes[index].toNat < 8) : Bool :=
  if bound : start < bytes.size then
    if small : bytes[start].toNat < 8 then
      fixtures_module_all_small bytes (start + 1) (by
        intro index upper inside
        by_cases same : index = start
        · subst index; exact small
        · exact checked index (by omega) inside)
    else false
  else true
termination_by bytes.size - start

public def fixtures_module_two_args (a b : Nat) : Nat :=
  if ha : a = 0 then b
  else if b = 0 then
    fixtures_module_positive a (by omega) + fixtures_module_two_args (a - 1) 5
  else fixtures_module_two_args a (b - 1)
termination_by (a, b)

@[expose] public def fixtures_module_two_args_exposed (a b : Nat) : Nat :=
  if ha : a = 0 then b
  else if b = 0 then
    fixtures_module_positive a (by omega) + fixtures_module_two_args_exposed (a - 1) 5
  else fixtures_module_two_args_exposed a (b - 1)
termination_by (a, b)

public def fixtures_module_measured_later (index remaining : Nat) : Nat :=
  match remaining with
  | 0 => index
  | count + 1 => fixtures_module_measured_later (index + 1) count
termination_by remaining

public def fixtures_module_structural_later (a b : Nat) : Nat :=
  match a, b with
  | _, 0 => a
  | 0, _ => b
  | a + 1, b + 1 => fixtures_module_structural_later a b + 1
termination_by structural b

public inductive FixturesModuleTree where
  | leaf (value : Nat)
  | node (left right : FixturesModuleTree)
  deriving DecidableEq, BEq, Hashable, Repr
