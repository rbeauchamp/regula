/-
Mutation, kept as the counterexample control of item 5 of issue #285
(https://github.com/rbeauchamp/regula/issues/285): a reference that `initialize` declares. Lean
compiles the constant to a stub that is never run, and compiled code reads the value its
initializer returned when the module was initialized, so the constant is a trusted
`initialized-value` boundary, which fails a checked execution claim with RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/). Before the fix, the constant was reported
as an opaque constant run through its kernel-checked body, and the claim passed.
-/

/-- A counter, which the module's initialization creates. -/
initialize fixtures_initialized_counter : IO.Ref Nat ← IO.mkRef 0

/-- Reads the counter. -/
def fixtures_read_counter : IO Nat :=
  fixtures_initialized_counter.get
