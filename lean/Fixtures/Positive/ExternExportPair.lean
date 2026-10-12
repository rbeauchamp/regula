/-
Positive control of item 5 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): an
`@[extern]` declaration whose C symbol is the `@[export]` name of a Lean declaration. Compiled
calls of the reference run the exported implementation, so the report names the pair as an
`exported-implementation` boundary with that declaration as its replacement. The C linker's binding
of the two is trusted and never checked, even here, where the two bodies are definitionally equal
(`Fixtures.Mutations.ExternExportSignatureMismatch` shows a pair whose calling conventions differ).
Before the fix, every `extern` of a project was reported as an `external` boundary with no
replacement.
-/

/-- The successor, compiled under the C symbol `fixtures_pair_symbol`. -/
@[export fixtures_pair_symbol]
def fixtures_pair_implementation (n : Nat) : Nat := n + 1

/-- The successor; its compiled calls run the code exported as `fixtures_pair_symbol`. -/
@[extern "fixtures_pair_symbol"]
def fixtures_pair_reference (n : Nat) : Nat := n + 1
