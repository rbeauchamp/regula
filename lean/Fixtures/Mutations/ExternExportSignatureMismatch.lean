/-
Mutation, kept as the counterexample control of item 5 of issue #285
(https://github.com/rbeauchamp/regula/issues/285): an `@[extern]` declaration whose C symbol is the
`@[export]` name of a Lean declaration whose compiled parameters differ from the `extern`'s. Lean
drops the erased type parameter from a call of the `extern` but keeps it as a parameter of the
exported function, so a compiled call passes one argument fewer than the exported code reads. The
pair is a trusted `exported-implementation` boundary, which fails a checked execution claim with
RG3002 (https://rbeauchamp.github.io/regula/dev/rules/RG3002/), though the two bodies are
definitionally equal. Such a difference is why Regula checks no extern/export pair.
-/

/-- The successor, compiled under the C symbol `fixtures_mismatch_symbol` with its type
parameter kept. -/
@[export fixtures_mismatch_symbol]
def fixtures_mismatch_implementation (_ : Type) (n : Nat) : Nat := n + 1

/-- The successor; its compiled calls pass `fixtures_mismatch_symbol` only `n`. -/
@[extern "fixtures_mismatch_symbol"]
def fixtures_mismatch_reference (_ : Type) (n : Nat) : Nat := n + 1
