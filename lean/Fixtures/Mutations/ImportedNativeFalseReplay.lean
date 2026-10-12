/-
Mutation: a theorem that rests on an imported axiom of native-proof name and shape whose
statement native replay refutes. It must not be compiler-trusting: it is an unknown axiom.

-/
import Fixtures.Mutations.NativeFalseAxiom

theorem fixtures_imported_false_replay : decide (1 = 2) = true :=
  fixtures_false_native_parent._native.native_decide.ax_1
