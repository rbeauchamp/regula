/-
Mutation, kept as a control of item 5 of issue #285
(https://github.com/rbeauchamp/regula/issues/285): a constant given an initializer and an
`@[implemented_by]` target in one attribute list. Lean generates no code for it, so it has no IR
(`shouldGenerateCode`), and `Regula.Probe.lowering` classifies it as a runtime replacement alone.
Lean's interpreter cannot import the module, though: running the module's initializers looks up
the IR of the constant the initializer sets, and there is none. So the audit, which imports with
initializers enabled, stops without a verdict (RG2001) rather than reporting the replacement.
-/

/-- The value that compiled calls of `fixtures_uncompiled_counter` read. -/
def fixtures_uncompiled_replacement : Nat := 2

/-- The initializer, which no compiled code runs. -/
def fixtures_uncompiled_action : IO Nat := pure 1

/-- The reference; compiled code runs the replacement instead. -/
@[init fixtures_uncompiled_action, implemented_by fixtures_uncompiled_replacement]
opaque fixtures_uncompiled_counter : Nat

/-- Reads the counter. -/
def fixtures_read_uncompiled_counter : Nat := fixtures_uncompiled_counter + 1
