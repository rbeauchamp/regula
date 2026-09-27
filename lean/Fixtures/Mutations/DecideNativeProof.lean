/-
Mutation: a `decide +native` proof. `Lean.Meta.nativeEqTrue` names its generated
axiom after the `decide` tactic (`._native.decide.ax_…`), so it must be reported as
compiler-trusting, not as a project axiom, and rejected on a standard-logical surface.

-/
theorem fixtures_decide_native_proof : (List.range 1001).sum = 500500 := by
  decide +native
