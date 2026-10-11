/-
Positive control of item 5 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): an
`@[extern]` declaration whose C symbol is the `@[export]` name of a Lean declaration. Compiled
calls of the reference run the exported implementation, an `exported-implementation` boundary, and
the two bodies are definitionally equal, so its correspondence is checked and the surface passes a
checked execution claim. Before the fix, every `extern` of a project was a trusted `external`
boundary, which fails that claim with RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/).
-/

/-- The successor, compiled under the C symbol `fixtures_pair_symbol`. -/
@[export fixtures_pair_symbol]
def fixtures_pair_implementation (n : Nat) : Nat := n + 1

/-- The successor; its compiled calls run the code exported as `fixtures_pair_symbol`. -/
@[extern "fixtures_pair_symbol"]
def fixtures_pair_reference (n : Nat) : Nat := n + 1
