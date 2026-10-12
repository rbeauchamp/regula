/-
Mutation: a theorem that rests on two imported native-proof axioms, the first named under the
second as its generated prefix. Each is authenticated as an imported native-proof axiom, so the
theorem must be reported as compiler-trusting, whichever of the two the checker reaches first.

-/
import Fixtures.Mutations.NativeNestedPrefix

theorem fixtures_imported_nested_prefix : decide True = true ∧ decide True = true :=
  ⟨fixtures_nested_parent._native.native_decide.ax_1._native.native_decide.ax_1,
    fixtures_nested_parent._native.native_decide.ax_1⟩
