/-!
Two runtime replacements whose definitional correspondence the kernel decides by computing the
size of a binary tree with distinct leaves. The first comparison, of depth 12, adds about 57 MiB
to the process's resident memory, and the second, of depth 15, about 460 MiB, both well inside
the 1 GiB allowance of a check (`Regula.Probe.correspondenceMemoryBytes`), so a report decides
both in its own process. The checker's self-test inspects this module again with a 128 MiB
allowance: the first check raises the process's peak and completes, and the second exhausts its
limit in the report's process and is decided by a fresh worker, whose answer is the reported one.
-/

/-- A binary tree whose leaves carry labels, so that no two subtrees are equal. -/
inductive FixturesFreshTree where
  | leaf (label : Nat)
  | node (left right : FixturesFreshTree)

/-- The complete tree of `depth` whose leaves are labelled from `label`. -/
def FixturesFreshTree.build : Nat → Nat → FixturesFreshTree
  | 0, label => .leaf label
  | depth + 1, label => .node (build depth (2 * label)) (build depth (2 * label + 1))

/-- The number of leaves. -/
def FixturesFreshTree.size : FixturesFreshTree → Nat
  | .leaf _ => 1
  | .node left right => left.size + right.size

/-- The executed form of `fixtures_fresh_small`. -/
def fixtures_fresh_small_impl (k : Nat) : Nat := 4096 + k

/-- `k` plus the leaves of the tree of depth 12. -/
@[implemented_by fixtures_fresh_small_impl]
def fixtures_fresh_small (k : Nat) : Nat := (FixturesFreshTree.build 12 0).size + k

/-- The executed form of `fixtures_fresh_large`. -/
def fixtures_fresh_large_impl (k : Nat) : Nat := 32768 + k

/-- `k` plus the leaves of the tree of depth 15. -/
@[implemented_by fixtures_fresh_large_impl]
def fixtures_fresh_large (k : Nat) : Nat := (FixturesFreshTree.build 15 0).size + k
