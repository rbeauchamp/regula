/-
Positive control of item 5 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): an
`@[extern]` declaration with an `@[implemented_by]` target. Lean generates code for the extern, so
it is a trusted `external` boundary, and compiled Lean calls of it call the target, so it is also
a `runtime-replacement` boundary to the target, which the walk follows and whose correspondence
is checked here (the two are definitionally equal). Before the fix, the report gave it the
`external` boundary alone.
-/

/-- The successor that compiled Lean calls of `fixtures_extern_reference` run. -/
def fixtures_extern_replacement (n : Nat) : Nat := n + 1

/-- The successor; compiled Lean calls run the replacement instead. -/
@[extern "lean_fixtures_extern_reference", implemented_by fixtures_extern_replacement]
def fixtures_extern_reference (n : Nat) : Nat := n + 1
