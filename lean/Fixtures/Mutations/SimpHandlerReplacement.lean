import Lean

/-
Mutation (issue #125): `Positive.AttributedRecursion` plus an earlier
source-local implementation of `simp` that keeps the built-in reference. It is
not the post-import object, and audited source ran to install it, so the
helper of the definition it tags is not admitted.
-/
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
