import Std.Tactic.BVDecide

/-! Solver control, outside the project's claimed proof surface. -/

/-- The solver must actually run to establish this external-boundary control. -/
theorem processCadical_commute (x y : BitVec 8) : x * y = y * x := by bv_decide
