import Lean

/-! An attribute application is recorded under the attribute implementation's
reference. A source-local implementation that keeps the built-in `simp`
reference is not the post-import object, so the recursive definition it tags
keeps its helper an escape hatch. -/
open Lean

run_cmd do
  let env ← getEnv
  let .ok original := getAttributeImpl env `simp
    | throwError "missing built-in simp"
  let replacement := { original with add := fun name attrSyntax kind => do
    logInfo "source-local simp wrapper"
    original.add name attrSyntax kind }
  let state := attributeExtension.getState env
  setEnv <| attributeExtension.setState env
    { state with map := state.map.insert `simp replacement }

@[simp] def fixtures_simp_replaced : List Nat → Nat
  | [] => 0
  | x :: xs => x + fixtures_simp_replaced xs
