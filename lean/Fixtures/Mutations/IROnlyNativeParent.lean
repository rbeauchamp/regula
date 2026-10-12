/-!
Mutation: a native-named axiom whose generated prefix names an auxiliary declaration that only
Lean's code generator has (`fixtures_ir_parent._redArg`), not the kernel. Declared directly, it
is a project axiom.
-/

def fixtures_ir_parent {α : Type} (_ : List α) (n : Nat) : Nat := n + 1

axiom fixtures_ir_parent._redArg._native.native_decide.ax_1 : decide True = true
