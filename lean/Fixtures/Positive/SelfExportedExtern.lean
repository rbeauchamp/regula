/-
Positive control of item 5 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): an
`@[extern]` declaration that also gives its own C symbol as its `@[export]` name. Lean compiles the
declaration from its `extern` attribute alone and emits no Lean code for it, so a call runs the
external code, not an exported Lean implementation. The report names it as an `external` boundary,
with no replacement and no edge back to itself. Before this fix it was reported as an
`exported-implementation` boundary whose replacement was the declaration itself.
-/

/-- The successor; its compiled calls run the external code of `fixtures_self_symbol`. -/
@[extern "fixtures_self_symbol", export fixtures_self_symbol]
def fixtures_self_reference (n : Nat) : Nat := n + 1
