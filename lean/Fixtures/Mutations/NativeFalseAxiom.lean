/-
Mutation: a project axiom with a generated native-proof name under a declaration of its own
module and the statement of a native decision that is false. It is authored, so it is a
project axiom here; `ImportedNativeFalseReplay` imports it.

-/
theorem fixtures_false_native_parent : True := trivial

axiom fixtures_false_native_parent._native.native_decide.ax_1 : decide (1 = 2) = true
