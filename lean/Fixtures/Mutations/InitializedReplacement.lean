/-
Mutation, kept as a control of item 5 of issue #285
(https://github.com/rbeauchamp/regula/issues/285) at the compiler-attribute boundary: what
`getImplementedBy?` and Lean's compiled IR report to the walk for a constant that also has an
initializer. It is not a substitute for `Regula.Probe.lowering_initialized_iff`, which states the
classification itself. The counter is declared by `initialize`, so Lean compiles it, and is then
given an `@[implemented_by]` target. A call compiled after that, as the reader's is, calls the
target, so the counter is a `runtime-replacement` boundary to the target, which the walk follows.
The target was compiled before the attribute, and its compiled body reads the counter, so
compiled code still reads the value the initializer returned: the counter is an
`initialized-value` boundary too. The replacement's correspondence is checked (the target unfolds
to the counter), so the initialized value alone fails a checked execution claim with RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/). When the counter was classified as a
runtime replacement alone, the claim passed.
-/

/-- A counter, which the module's initialization sets. -/
initialize fixtures_replaced_counter : Nat ← pure 1

/-- The code that calls of `fixtures_replaced_counter` compiled after its attribute run; its own
compiled body reads the counter's initialized value, and it is not inlined, so the reader's call
does not unfold back into the counter. -/
@[noinline] def fixtures_counter_replacement : Nat := fixtures_replaced_counter

attribute [implemented_by fixtures_counter_replacement] fixtures_replaced_counter

/-- Reads the counter. -/
def fixtures_read_replaced_counter : Nat :=
  fixtures_replaced_counter + 1
