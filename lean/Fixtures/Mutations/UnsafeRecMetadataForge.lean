/-
Mutation: public environment APIs can synthesize every final-environment field
that resembles Lean's range-less partial execution helper for safe recursion.
The base is tagged recursive and the helper has the expected type, group, body,
and flags, but the helper loops. Rejected by exact match: rerunning Lean's recursion compiler on the forged
helper's own recursion does not regenerate the forged base.
-/
import Lean

open Lean Elab Command

elab "forge_unsafe_rec_metadata" : command => do
      let stx ← getRef
      let baseName := `fixtures_forged_safe_rec
      let helperName := `fixtures_forged_safe_rec._unsafe_rec
      let nat := mkConst ``Nat
      let type := mkForall `_ .default nat nat
      let baseValue := mkLambda `n .default nat (mkBVar 0)
      liftCoreM <| addDecl (.defnDecl {
        name := baseName
        levelParams := []
        type
        value := baseValue
        hints := .regular 1
        safety := .safe
        all := [baseName]
      })
      -- Keep the safe base executable: missing code would be a second fault,
      -- independent of the forged helper this mutation isolates.
      liftCoreM <| compileDecls #[baseName]
      liftCoreM <| Lean.Meta.markAsRecursive baseName
      addDeclarationRangesFromSyntax baseName stx
      let helperValue := mkLambda `n .default nat <|
        mkApp (mkConst helperName) (mkBVar 0)
      liftCoreM <| addDecl (.mutualDefnDecl [{
        name := helperName
        levelParams := []
        type
        value := helperValue
        hints := .opaque
        safety := .partial
        all := [helperName]
      }])

forge_unsafe_rec_metadata
