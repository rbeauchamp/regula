import Lean

/-
Mutation (issue #125, adversarial): a module-local command elaborator installs,
through the process-global `derivingHandlersRef`, a module-defined deriving
handler that forges a safe base with the victim command's exact range, its
recursion tag, stored predefinition and looping helper. The installer's syntax
kind is the module's own and it runs in `CommandElabM`. Exact match rejects the
forged helper because Lean's recursion compiler does not regenerate the forged
base from it; the genuine derived helper is admitted.
-/
open Lean Elab Command

def _fixturesEvilHandler : DerivingHandler := fun _ => do
  let baseName := `fixtures_forged_by_command
  unless (← getEnv).contains baseName do
    let helperName := baseName ++ `_unsafe_rec
    let nat := Lean.mkConst ``Nat
    let type := mkForall `n .default nat nat
    liftCoreM <| addDecl (.defnDecl {
      name := baseName, levelParams := [], type
      value := mkLambda `n .default nat (mkBVar 0)
      hints := .regular 1, safety := .safe, all := [baseName] })
    liftCoreM <| compileDecls #[baseName]
    liftCoreM <| Meta.markAsRecursive baseName
    modifyEnv fun env => Elab.Structural.eqnInfoExt.insert env baseName {
      declName := baseName, levelParams := [], type
      value := mkLambda `n .default nat (mkApp (Lean.mkConst baseName) (mkBVar 0))
      recArgPos := 0, declNames := #[baseName]
      fixedParamPerms := { numFixed := 0, perms := #[#[]], revDeps := #[] } }
    liftCoreM <| addDecl (.mutualDefnDecl [{
      name := helperName, levelParams := [], type
      value := mkLambda `n .default nat (mkApp (Lean.mkConst helperName) (mkBVar 0))
      hints := .opaque, safety := .partial, all := [helperName] }])
    let range : DeclarationRange :=
      { pos := ⟨46, 0⟩, charUtf16 := 0, endPos := ⟨49, 22⟩, endCharUtf16 := 22 }
    liftCoreM <| addDeclarationRanges baseName { range, selectionRange := range }
  return false

elab "fixtures_install_handler" : command =>
  derivingHandlersRef.modify fun handlers =>
    handlers.insert ``DecidableEq (_fixturesEvilHandler :: (handlers.find? ``DecidableEq).getD [])

fixtures_install_handler

inductive FixturesCommandVictim where
  | leaf
  | wrap (inner : FixturesCommandVictim)
  deriving DecidableEq
