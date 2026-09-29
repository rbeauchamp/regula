import Lean

/-
Mutation (issue #125, adversarial): a module-local term elaborator for the
built-in `match` syntax forges a safe base, its recursion tag, its stored
predefinition and a looping `_unsafe_rec` helper, with the base's declaration
range set to the inductive command below. It runs, unrecorded, when Lean's
`DecidableEq` deriving handler elaborates its generated `match` with
information trees disabled, so every recorded evaluator of that command is
pinned. The registered module-local elaborator (`Command.sourceLocalCode`) keeps
the forged helper an escape hatch; before that condition it was admitted.
-/
open Lean Elab Term

@[term_elab Lean.Parser.Term.match] def _fixturesForgeOnMatch : TermElab := fun stx expectedType? => do
  let baseName := `fixtures_forged_by_match
  unless (← getEnv).contains baseName do
    let helperName := baseName ++ `_unsafe_rec
    let nat := Lean.mkConst ``Nat
    let type := mkForall `n .default nat nat
    addDecl (.defnDecl {
      name := baseName, levelParams := [], type
      value := mkLambda `n .default nat (mkBVar 0)
      hints := .regular 1, safety := .safe, all := [baseName] })
    compileDecls #[baseName]
    Meta.markAsRecursive baseName
    modifyEnv fun env => Elab.Structural.eqnInfoExt.insert env baseName {
      declName := baseName, levelParams := [], type
      value := mkLambda `n .default nat (mkApp (Lean.mkConst baseName) (mkBVar 0))
      recArgPos := 0, declNames := #[baseName]
      fixedParamPerms := { numFixed := 0, perms := #[#[]], revDeps := #[] } }
    addDecl (.mutualDefnDecl [{
      name := helperName, levelParams := [], type
      value := mkLambda `n .default nat (mkApp (Lean.mkConst helperName) (mkBVar 0))
      hints := .opaque, safety := .partial, all := [helperName] }])
    let range : DeclarationRange :=
      { pos := ⟨41, 0⟩, charUtf16 := 0, endPos := ⟨44, 22⟩, endCharUtf16 := 22 }
    addDeclarationRanges baseName { range, selectionRange := range }
  Lean.Elab.Term.elabMatch stx expectedType?

inductive FixturesForgeShape where
  | leaf
  | wrap (inner : FixturesForgeShape)
  deriving DecidableEq
