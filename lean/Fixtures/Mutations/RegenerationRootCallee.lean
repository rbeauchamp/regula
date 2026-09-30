import Lean

/-
Mutation (issue #125, adversarial): the module's own
`_regula_regeneration.fixtures_step`, under the root a regeneration names the
definitions it adds under, stands beside `fixtures_step`. A custom command
forges a safe base with the kernel value Lean compiles for
`fixtures_descent`, which calls `fixtures_step`, and a range-less
`_unsafe_rec` helper that calls `_regula_regeneration.fixtures_step` instead
and so never terminates. Exact match rejects it: a regeneration renames back
only the definitions it added, so the regenerated base still calls the
module's `_regula_regeneration.fixtures_step` and does not equal the forged
base.
-/
open Lean Elab Command

def fixtures_step (n : Nat) : Nat := n - 1

def _regula_regeneration.fixtures_step (n : Nat) : Nat := n + 1

def fixtures_descent (n : Nat) : Nat :=
  if _h : n = 0 then 0 else fixtures_descent (fixtures_step n)
termination_by n
decreasing_by
  unfold fixtures_step
  omega

elab "forge_unsafe_rec_under_regeneration_root" : command => do
  let baseName := `fixtures_forged_under_root
  let helperName := baseName ++ `_unsafe_rec
  let honestHelperName := ``fixtures_descent ++ `_unsafe_rec
  let env ← getEnv
  let some (.defnInfo base) := env.find? ``fixtures_descent | throwError "missing base"
  let some (.defnInfo helper) := env.find? honestHelperName | throwError "missing helper"
  liftCoreM <| addDecl (.defnDecl { base with name := baseName, all := [baseName] })
  liftCoreM <| Lean.Meta.markAsRecursive baseName
  addDeclarationRangesFromSyntax baseName (← getRef)
  let helperValue := helper.value.replace fun
    | .const n us =>
      if n == honestHelperName then some (mkConst helperName us)
      else if n == ``fixtures_step then some (mkConst `_regula_regeneration.fixtures_step us)
      else none
    | _ => none
  liftCoreM <| addDecl (.mutualDefnDecl [{ helper with
    name := helperName, value := helperValue, all := [helperName] }])
  liftCoreM <| compileDecls #[helperName]

forge_unsafe_rec_under_regeneration_root
