/-
Mutation: public environment APIs can synthesize a native-looking Boolean
axiom and an exact `of_decide_eq_true` parent proof with nested source ranges
from a custom command. The axiom asserts only a Boolean fact that native replay
confirms, so it must be classified compiler-trusting, never logical, and still
rejected on a standard-logical surface.
-/
import Lean

open Lean Elab Command

elab "forge_native_semantics" : command => do
      let stx ← getRef
      let parentName := `fixtures_forged_native
      let axiomName := `fixtures_forged_native._native.native_decide.ax_1
      let proposition := mkConst ``True
      let instanceType := mkApp (mkConst ``Decidable) proposition
      let inst ← liftTermElabM <| Meta.synthInstance instanceType
      let decideExpr := mkApp2 (mkConst ``Decidable.decide) proposition inst
      let axiomType := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
        decideExpr (mkConst ``Bool.true)
      liftCoreM <| addDecl (.axiomDecl {
        name := axiomName
        levelParams := []
        type := axiomType
        isUnsafe := false
      })
      addDeclarationRangesFromSyntax axiomName stx
      let proof := mkApp3 (mkConst ``of_decide_eq_true)
        proposition inst (mkConst axiomName)
      liftCoreM <| addDecl (.thmDecl {
        name := parentName
        levelParams := []
        type := proposition
        value := proof
        all := [parentName]
      })
      addDeclarationRangesFromSyntax parentName stx

forge_native_semantics
