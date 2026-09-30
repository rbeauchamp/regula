import Lean

/-! Positive control (issue #125): a source-local replacement of the `specialize`
attribute runs while the definition below is elaborated, but the helper and base
are still exactly what Lean's recursion compiler generates from the helper's
recursion, so exact match admits the helper: admission does not depend on which
code ran during elaboration. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let .ok original := getAttributeImpl env `specialize
    | throwError "missing built-in specialization"
  let replacement := { original with add := fun name attrSyntax kind => do
    logInfo "source-local specialization wrapper"
    original.add name attrSyntax kind }
  let state := attributeExtension.getState env
  setEnv <| attributeExtension.setState env
    { state with map := state.map.insert `specialize replacement }

@[specialize] def fixtures_specialize_replaced (accept : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: xs => (if accept x then x else 0) + fixtures_specialize_replaced accept xs
