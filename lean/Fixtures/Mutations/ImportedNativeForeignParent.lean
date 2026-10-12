/-
Mutation: a theorem that rests on an imported axiom of native-proof shape whose statement
replays true, but whose generated prefix names a declaration of a different module than the
axiom's. Lean generates such a name only in the parent's own module, so it must not be
compiler-trusting: it is an unknown axiom.

-/
import Fixtures.Mutations.NativeForeignParent

theorem fixtures_imported_foreign_parent : decide (1 = 1) = true :=
  fixtures_native_proof._native.native_decide.ax_7
