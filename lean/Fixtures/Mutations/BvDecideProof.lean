/-
Mutation: a `bv_decide` proof. Its SAT certificate is checked by compiled code
through a generated `._native.bv_decide.ax_…` axiom, so it must be reported as
compiler-trusting, not as a project axiom, and rejected on a standard-logical surface.

-/
import Std.Tactic.BVDecide

theorem fixtures_bv_decide_proof (x y : BitVec 8) : x * y = y * x := by
  bv_decide
