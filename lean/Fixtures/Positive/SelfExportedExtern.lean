/-
Positive control of item 5 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): an
`@[extern]` declaration that also gives its own C symbol as its `@[export]` name. The report
names it as a trusted `external` boundary with no execution edge, and names the declaration
itself as also exporting the symbol, with no claim about which body runs under it. Before this
change it was reported as an `exported-implementation` boundary whose replacement was the
declaration itself, with an execution edge to itself.
-/

/-- The successor; its compiled calls call the C symbol `fixtures_self_symbol`. -/
@[extern "fixtures_self_symbol", export fixtures_self_symbol]
def fixtures_self_reference (n : Nat) : Nat := n + 1
