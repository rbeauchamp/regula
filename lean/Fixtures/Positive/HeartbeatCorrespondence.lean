/-!
A runtime replacement whose definitional correspondence the kernel decides by computing the size
of a binary tree of depth 16 with distinct leaves. The check adds about 900 MiB to the process's
resident memory and stays within its heartbeat budgets, which alone bound it
(`Regula.Probe.runCheck`), so a report decides it as checked.
-/

/-- A binary tree whose leaves carry labels, so that no two subtrees are equal. -/
inductive FixturesHeartbeatTree where
  | leaf (label : Nat)
  | node (left right : FixturesHeartbeatTree)

/-- The complete tree of `depth` whose leaves are labelled from `label`. -/
def FixturesHeartbeatTree.build : Nat → Nat → FixturesHeartbeatTree
  | 0, label => .leaf label
  | depth + 1, label => .node (build depth (2 * label)) (build depth (2 * label + 1))

/-- The number of leaves. -/
def FixturesHeartbeatTree.size : FixturesHeartbeatTree → Nat
  | .leaf _ => 1
  | .node left right => left.size + right.size

/-- The executed form of `fixtures_heartbeat_tree`. -/
def fixtures_heartbeat_tree_impl (k : Nat) : Nat := 65536 + k

/-- `k` plus the leaves of the tree of depth 16. -/
@[implemented_by fixtures_heartbeat_tree_impl]
def fixtures_heartbeat_tree (k : Nat) : Nat := (FixturesHeartbeatTree.build 16 0).size + k
