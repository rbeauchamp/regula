/-
Mutation: `run_tac` nested inside an ordinary built-in `def` can use public
environment APIs to add a range-less partial helper in the same frontend
command, with forged metadata, stored predefinition and a looping body.
Rejected by exact match: rerunning Lean's recursion compiler on the forged
helper's own recursion does not regenerate the forged base.
-/
import Lean
import Lean.Elab.PreDefinition.Structural.Eqns

open Lean Elab Tactic

def fixtures_run_tac_safe_rec (n : Nat) : Nat := by
  run_tac do
    let baseName := `fixtures_run_tac_safe_rec
    let helperName := `fixtures_run_tac_safe_rec._unsafe_rec
    let nat := mkConst ``Nat
    let type := mkForall `n .default nat nat
    let eqnValue := mkLambda `n .default nat <|
      mkApp (mkConst baseName) (mkBVar 0)
    liftM (m := CoreM) <| Meta.markAsRecursive baseName
    liftM (m := CoreM) do
      modifyEnv fun env => Elab.Structural.eqnInfoExt.insert env baseName {
        declName := baseName
        levelParams := []
        type
        value := eqnValue
        recArgPos := 0
        declNames := #[baseName]
        fixedParamPerms := { numFixed := 0, perms := #[#[]], revDeps := #[] }
      }
    let helperValue := mkLambda `n .default nat <|
      mkApp (mkConst helperName) (mkBVar 0)
    liftM (m := CoreM) <| addDecl (.mutualDefnDecl [{
      name := helperName
      levelParams := []
      type
      value := helperValue
      hints := .opaque
      safety := .partial
      all := [helperName]
    }])
  exact n
