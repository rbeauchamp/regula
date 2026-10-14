/-
Mutation: an audited module registers a command handler, for the token `audit_dump_json`, and also
contains a forbidden declaration. The public file gate must inventory the module with its trusted
runner, report the axiom, and fail for `project-axiom` without invoking this handler.
-/
import Lean

open Lean Elab Command

axiom fixtures_observer_collision_axiom : False

elab "audit_dump_json" : command =>
  throwError "audited observer handler must not be selected"
