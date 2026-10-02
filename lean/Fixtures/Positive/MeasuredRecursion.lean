/-
Positive control (issue #183) at the compiler boundary: safe recursive
definitions whose compiled value depends on the termination argument Lean
compiled them with. Lean's well-founded compiler passes the recursive-call
function through a `match` where that function's type, which holds the
relation and the measure, changes in an alternative; its structural compiler
recurses on one chosen argument. A regeneration that chooses its own termination argument
can therefore compile a different value where its choice differs from Lean's.

- `fixtures_measured_later` is the issue's reproduction: a `match` on the
  measured argument, after an argument that also changes.
- `fixtures_measured_slice` is the shape found in the audited library, with a
  fixed parameter and a proof argument.
- `fixtures_measured_lexicographic` matches on both components of a
  lexicographic measure, after an argument that changes.
- `fixtures_measured_sum` measures by an expression over two matched
  arguments.
- `fixtures_measured_fixed_between` has a fixed parameter between its varying
  ones, so the fixed parameters are no prefix.
- `fixtures_measured_even` and `fixtures_measured_odd` are mutually recursive,
  each measured on its later argument.
- `fixtures_measured_list` measures on a list, not a `Nat`, where structural
  recursion would also be accepted.
- `fixtures_measured_local_relation` is measured by a pair under a
  `WellFoundedRelation` instance local to its section, which reads the second
  component only; at the end of the module Lean would resolve the
  lexicographic instance, under which the `match` on `a` changes the measure
  (found in review).
- `fixtures_structural_later` recurses structurally on its second argument,
  selected by `termination_by structural`, where Lean's automatic choice
  accepts the first.
- `fixtures_structural_even` and `fixtures_structural_odd` are mutually
  recursive, each structurally on its last argument, after a fixed parameter
  and an argument that changes.
- `fixtures_structural_nested` accumulates in a nested inductive type before
  a `List` of it; Lean's automatic choice compiles it through the nested type
  former of the accumulator's type. A recorded position does not determine
  Lean's structural compilation, since the same position can be reached
  through another argument's inductive group (found in review).

Exact match admits every helper: structural recursion is tried with Lean's
automatic choice, then on the argument position Lean recorded for each base,
which admits a definition recursing on an argument `termination_by structural`
selects; well-founded recursion is given the relation the observed base's
fixpoint applies (its measure together with the instance Lean resolved for
it).
-/

def fixtures_measured_later (index remaining : Nat) : Nat :=
  match remaining with
  | 0 => index
  | count + 1 => fixtures_measured_later (index + 1) count
termination_by remaining

def fixtures_measured_slice (xs : Array Nat) (index remaining : Nat)
    (h : index + remaining ≤ xs.size) : Nat :=
  match remaining with
  | 0 => 0
  | count + 1 =>
    have hi : index < xs.size := by omega
    xs[index] + fixtures_measured_slice xs (index + 1) count (by omega)
termination_by remaining

def fixtures_measured_lexicographic (a b c : Nat) : Nat :=
  match c with
  | 0 =>
    match b with
    | 0 => a
    | b' + 1 => fixtures_measured_lexicographic (a + 1) b' (a + 5)
  | c' + 1 => fixtures_measured_lexicographic (a + 2) b c'
termination_by (b, c)

def fixtures_measured_sum (acc : Nat) (xs : List Nat) (fuel : Nat) : Nat :=
  match fuel, xs with
  | 0, _ => acc
  | _, [] => acc
  | fuel + 1, x :: rest => fixtures_measured_sum (acc + x) rest fuel
termination_by fuel + xs.length

def fixtures_measured_fixed_between (index : Nat) (xs : Array Nat) (remaining : Nat) : Nat :=
  match remaining with
  | 0 => index
  | count + 1 => fixtures_measured_fixed_between (index + xs.size) xs count
termination_by remaining

mutual
def fixtures_measured_even (acc n : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => fixtures_measured_odd (acc + 1) k
termination_by n
def fixtures_measured_odd (acc n : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => fixtures_measured_even (acc + 2) k
termination_by n
end

def fixtures_measured_list (acc : Nat) (xs : List Nat) : Nat :=
  match xs with
  | [] => acc
  | x :: rest => fixtures_measured_list (acc + x) rest
termination_by xs

section
local instance fixtures_second_relation : WellFoundedRelation (Nat × Nat) :=
  invImage Prod.snd Nat.lt_wfRel

def fixtures_measured_local_relation (a n : Nat) : Nat :=
  match a with
  | 0 =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_measured_local_relation 1 k
  | a' + 1 =>
    match n with
    | 0 => a' + 1
    | k + 1 => fixtures_measured_local_relation (a' + 2) k
termination_by (a, n)
decreasing_by all_goals exact Nat.lt_succ_self _
end

def fixtures_structural_later (a b : Nat) : Nat :=
  match a, b with
  | _, 0 => a
  | 0, _ => b
  | a + 1, b + 1 => fixtures_structural_later a b + 1
termination_by structural b

mutual
def fixtures_structural_even (xs : Array Nat) (acc a b : Nat) : Nat :=
  match a, b with
  | _, 0 => acc + xs.size
  | 0, _ => acc
  | a + 1, b + 1 => fixtures_structural_odd xs (acc + 1) a b
termination_by structural b
def fixtures_structural_odd (xs : Array Nat) (acc a b : Nat) : Nat :=
  match a, b with
  | _, 0 => acc
  | 0, _ => acc + xs.size
  | a + 1, b + 1 => fixtures_structural_even xs (acc + 2) a b
termination_by structural b
end

inductive FixturesAst where
  | var : String → FixturesAst
  | app : FixturesAst → FixturesAst → FixturesAst
  | call : String → List FixturesAst → FixturesAst

def fixtures_structural_nested (f : FixturesAst) (args : List FixturesAst) : FixturesAst :=
  match args with
  | [] => f
  | a :: rest => fixtures_structural_nested (FixturesAst.app f a) rest
