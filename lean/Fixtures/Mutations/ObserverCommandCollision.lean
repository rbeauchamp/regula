/-
Mutation: an audited module registers the command token `audit_dump_json`, which an
earlier probe registered as an interactive command, and also contains a forbidden declaration. The
public file gate must use its trusted runner, inventory the axiom, and fail for
`project-axiom` rather than invoking this handler.
-/
import Lean

open Lean Elab Command

axiom fixtures_observer_collision_axiom : False

elab "audit_dump_json" : command =>
  throwError "audited observer handler must not be selected"
