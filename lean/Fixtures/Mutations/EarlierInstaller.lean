import Lean

/-
Mutation (issue #125, adversarial): in an earlier command, a module-local term
elaborator for `match` runs unrecorded inside the `DecidableEq` deriving
handler, installs a module-defined deriving handler through the process-global
`derivingHandlersRef`, and removes its own dispatch entry from every scope
level, so the environment at the victim command's start and end holds only
post-import entries and no code runner is recorded. The installed handler then
forges a safe base with the victim command's exact range, its recursion tag,
stored predefinition and looping helper. Provenance-based admission admitted it
and the file audit passed; exact match rejects it because Lean's recursion
compiler does not regenerate the forged base from the helper.
-/
open Lean Elab Term Command

def _fixturesEvilHandler : DerivingHandler := fun _ => do
  let baseName := `fixtures_forged_by_handler
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
      { pos := ⟨60, 0⟩, charUtf16 := 0, endPos := ⟨63, 22⟩, endCharUtf16 := 22 }
    liftCoreM <| addDeclarationRanges baseName { range, selectionRange := range }
  return false

@[term_elab Lean.Parser.Term.match] def _fixturesInstaller : TermElab := fun stx expectedType? => do
  derivingHandlersRef.modify fun handlers =>
    handlers.insert ``DecidableEq (_fixturesEvilHandler :: (handlers.find? ``DecidableEq).getD [])
  modifyEnv fun env => termElabAttribute.ext.ext.modifyState env fun stack =>
    { stack with stateStack := stack.stateStack.map fun level =>
        { level with state := { level.state with
            table := match level.state.table.find? ``Lean.Parser.Term.match with
              | some entries => level.state.table.insert ``Lean.Parser.Term.match
                  (entries.filter (·.declName != `_fixturesInstaller))
              | none => level.state.table } } }
  Lean.Elab.Term.elabMatch stx expectedType?

inductive FixturesTrigger where
  | a (n : Nat)
  | b
  deriving DecidableEq

inductive FixturesVictim where
  | leaf
  | wrap (inner : FixturesVictim)
  deriving DecidableEq
