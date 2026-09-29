import Lean

/-
Mutation (issue #125): `Positive.AttributedRecursion` plus an earlier
source-local `simp` implementation that restores the built-in object while it
runs, so the environment at the end of the tagged definition's command shows
only the built-in attribute. The start of the command still holds the
replacement, and audited source ran to install it, so the helper is not
admitted.
-/
open Lean

run_cmd do
  let env ← getEnv
  let .ok original := getAttributeImpl env `simp
    | throwError "missing built-in simp"
  let replacement := { original with add := fun name attrSyntax kind => do
    original.add name attrSyntax kind
    modifyEnv fun env => attributeExtension.setState env
      { attributeExtension.getState env with
          map := (attributeExtension.getState env).map.insert `simp original } }
  let state := attributeExtension.getState env
  setEnv <| attributeExtension.setState env
    { state with map := state.map.insert `simp replacement }

@[simp] def fixtures_simp_restored : List Nat → Nat
  | [] => 0
  | x :: xs => x + fixtures_simp_restored xs
