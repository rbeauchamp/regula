import Fixtures.Mutations.IROnlyNativeParent

/-!
Mutation: a theorem using a dependency's native-named axiom whose generated prefix names only an
auxiliary declaration of Lean's code generator, which the kernel does not have. No declaration of
the axiom's module carries the prefix, so the axiom is unknown, and the inspection completes.
-/

theorem fixtures_imported_ir_only_native_parent : decide True = true :=
  fixtures_ir_parent._redArg._native.native_decide.ax_1
