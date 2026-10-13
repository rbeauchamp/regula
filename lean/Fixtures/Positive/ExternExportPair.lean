/-
Positive control of item 5 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): an
`@[extern]` declaration whose C symbol is the `@[export]` name of a Lean declaration. The reference
is a trusted `external` boundary, its report names the declaration that also exports the symbol,
and that match adds no execution edge. The names are read from the attributes alone:
the report does not claim which body runs under the symbol
(`Fixtures.Mutations.ExternExportSignatureMismatch` shows a pair whose calling conventions differ).
Before this change, the report did not name the exporting declaration.
-/

/-- The successor, exported under the C symbol `fixtures_pair_symbol`. -/
@[export fixtures_pair_symbol]
def fixtures_pair_implementation (n : Nat) : Nat := n + 1

/-- The successor; its compiled calls call the C symbol `fixtures_pair_symbol`. -/
@[extern "fixtures_pair_symbol"]
def fixtures_pair_reference (n : Nat) : Nat := n + 1
