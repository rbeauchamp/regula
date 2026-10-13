/-
Mutation, kept as a control of item 5 of issue #285
(https://github.com/rbeauchamp/regula/issues/285) at the compiler-attribute boundary: what
`getImplementedBy?` reports to the walk for a constant that also has an initializer. It is not a
substitute for `Regula.Probe.lowering_initialized_iff`, which states the classification itself.
The counter is declared by `initialize` and then given an `@[implemented_by]` target. Lean's
simplifier replaces every call of the counter compiled after that, as the reader's is, by a call
of the target, so the counter is a `runtime-replacement` boundary to the target, which the walk
follows, not an `initialized-value` boundary. The two values are not provably equal, so under a
checked execution claim the boundary fails RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/). Before the fix, the counter was reported
as an `initialized-value` boundary alone and the target was not followed.
-/

/-- The value that compiled calls of `fixtures_replaced_counter` read. -/
def fixtures_counter_replacement : Nat := 2

/-- A counter, which the module's initialization sets. -/
initialize fixtures_replaced_counter : Nat ← pure 1

attribute [implemented_by fixtures_counter_replacement] fixtures_replaced_counter

/-- Reads the counter. -/
def fixtures_read_replaced_counter : Nat :=
  fixtures_replaced_counter + 1
