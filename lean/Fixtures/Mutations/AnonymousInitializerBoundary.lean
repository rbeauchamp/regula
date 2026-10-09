/-
Mutation, kept as the counterexample control of issue #289
(https://github.com/rbeauchamp/regula/issues/289): an anonymous `initialize` block is the only
code that reaches a runtime-replaced definition. Lean elaborates the block to a private `initFn`
with a hygienic, internal name and records it with the `[init]` attribute; no declaration
references it. No theorem relates the replacement to its reference and the values are not
definitionally equal, so under a checked execution claim the boundary must fail RG3002
(https://rbeauchamp.github.io/regula/dev/rules/RG3002/). Before the fix, executable roots were
the owned non-internal definitions, the block was no root, and the audit passed with the
boundary missing from its account. Roots now include the action of each initializer that an
owned module records. The block runs when the audit imports this module, and it changes nothing.
-/

/-- The code that compiled code runs in place of `fixtures_initializer_reference`. -/
private def fixtures_initializer_replacement (n : Nat) : Nat := 2 * n

/-- The reference definition; compiled code runs the replacement instead. -/
@[implemented_by fixtures_initializer_replacement]
private def fixtures_initializer_reference (n : Nat) : Nat := n + n

initialize do
  unless fixtures_initializer_reference 1 == 2 do
    throw <| IO.userError "the replacement disagrees with its reference"
