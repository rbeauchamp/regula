/-! # Zero notation

A claimed module that defines its own notation for zero. -/
/-- The term `zero!`, which Lean expands while it elaborates. -/
macro "zero!" : term => `(0)
/-- Zero is zero. -/
theorem zero_eq : (zero! : Nat) = 0 := rfl
