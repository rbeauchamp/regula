/-
Mutation (issue #125): a derived comparison's helper is admitted without a
binder record only when nothing the module registered could run unrecorded
while Lean elaborates the generated definitions with information trees
disabled. This module registers a macro for a built-in tactic kind, so the
derived helper stays an escape hatch even though the comparison is safe. A
notation or syntax the module declares itself would not have this effect.
-/

macro_rules
  | `(tactic| trivial) => `(tactic| rfl)

inductive FixturesMarked where
  | leaf
  | wrap (inner : FixturesMarked)
  deriving DecidableEq
