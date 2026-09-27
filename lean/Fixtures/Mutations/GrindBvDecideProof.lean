/-
Mutation: a `bv_decide` proof in `grind =>` mode. `grind`'s own elaborator table runs
the tactic, and `grind` moves the proof into an auxiliary `_proof` theorem, which uses
the generated `._native.bv_decide.ax_…` axiom. It must be reported as compiler-trusting,
not as a project axiom, and rejected on a standard-logical surface.

-/
import Std.Tactic.BVDecide

theorem fixtures_grind_bv_decide_proof (x y : BitVec 2) :
    (x &&& y) + (x ||| y) = x + y := by
  grind => bv_decide
