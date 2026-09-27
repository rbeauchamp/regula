/-
Mutation: project axioms given the names `Lean.Meta.nativeEqTrue` generates for
`decide +native` and `bv_decide`. Name shape alone must not authorize them as
compiler-trusting.

-/
axiom Attack._native.decide.ax_1 : False

axiom Attack._native.bv_decide.ax_1 : False
