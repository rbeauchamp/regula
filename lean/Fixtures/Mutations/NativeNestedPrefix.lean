/-
Mutation: two project axioms of native-proof name and natively true statement in one
module, the second named under the first as its generated prefix. They are authored, so they
are project axioms here; `ImportedNativeNestedPrefix` imports them.

-/
theorem fixtures_nested_parent : True := trivial

axiom fixtures_nested_parent._native.native_decide.ax_1 : decide True = true

axiom fixtures_nested_parent._native.native_decide.ax_1._native.native_decide.ax_1 :
  decide True = true
