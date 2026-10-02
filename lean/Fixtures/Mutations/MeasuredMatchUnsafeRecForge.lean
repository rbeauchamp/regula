import Lean

/-
Mutation (issue #183, adversarial) at the compiler boundary: a forged helper
on the path that admits a helper by regenerating its base with the base's own
relation. `fixtures_forged_measured_honest` matches on its measured argument
after an argument that also changes, so its base holds the relation the
regeneration reads. A custom command copies its base, the unary definition
that holds its well-founded fixpoint and its range-less `_unsafe_rec` helper
twice:

- `fixtures_forged_measured_faithful` renames only, and
- `fixtures_forged_measured_divergent` also makes the helper call
  `fixtures_forged_measured_skip` where the kernel-checked base calls
  `fixtures_forged_measured_step`, so the code Lean runs for it is not the
  definition the kernel checked.

Exact match admits the honest helper and the faithful copy, and rejects the
divergent one alone: the relation read from a base selects only which
regeneration runs, and the regenerated functional, which calls
`fixtures_forged_measured_skip`, still has to equal the observed one, which
calls `fixtures_forged_measured_step`.
-/
open Lean Elab Command

def fixtures_forged_measured_step (n : Nat) : Nat := n + 1

def fixtures_forged_measured_skip (n : Nat) : Nat := n + 2

def fixtures_forged_measured_honest (index remaining : Nat) : Nat :=
  match remaining with
  | 0 => index
  | count + 1 => fixtures_forged_measured_honest (fixtures_forged_measured_step index) count
termination_by remaining

/-- `forge_measured_helper name diverge`: copy `fixtures_forged_measured_honest`, its unary
definition and its helper under `name`; with `diverge`, the copied helper calls
`fixtures_forged_measured_skip` in place of `fixtures_forged_measured_step`. -/
elab "forge_measured_helper " id:ident diverge:(&"diverge")? : command => do
  let honest := ``fixtures_forged_measured_honest
  let forged := id.getId
  let copies := [honest, honest ++ `_unary, honest ++ `_unsafe_rec]
  let env ← getEnv
  let copied := fun (suffix : Name) (swap : Bool) => do
    let some (.defnInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    let value := info.value.replace fun
      | .const n us =>
        if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
        else if swap && n == ``fixtures_forged_measured_step then
          some (mkConst ``fixtures_forged_measured_skip us)
        else none
      | _ => none
    pure { info with name := forged ++ suffix, value, all := [forged ++ suffix] }
  liftCoreM <| addDecl (.defnDecl (← copied `_unary false))
  liftCoreM <| addDecl (.defnDecl (← copied .anonymous false))
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  liftCoreM <| addDecl (.mutualDefnDecl [← copied `_unsafe_rec diverge.isSome])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_measured_helper fixtures_forged_measured_faithful

forge_measured_helper fixtures_forged_measured_divergent diverge
