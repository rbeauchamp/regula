import Lean

/-
Mutation (issue #162, adversarial) at the compiler boundary: a forged helper
on the path that admits a helper whose definition shares a nested proof with
an earlier declaration. `fixtures_shared_honest` proves the proposition
`fixtures_shared_earlier` already proved, so Lean adds no theorem under it. A
custom command copies its base, its functional, its smart-unfolding definition
and its range-less `_unsafe_rec` helper twice:

- `fixtures_shared_faithful` renames only, and
- `fixtures_shared_divergent` also makes the helper call `fixtures_shared_drop`
  where the kernel-checked base calls `fixtures_shared_keep`, so the code Lean
  runs for it is not the definition the kernel checked.

Exact match admits the honest helper and the faithful copy, and rejects the
divergent one alone: with every theorem the regeneration abstracted put back
and erased, the regenerated functional calls `fixtures_shared_drop` and the
observed one `fixtures_shared_keep`. Putting the theorems back erases proofs
only; a difference in what a helper computes still fails.
-/
open Lean Elab Command

def fixtures_shared_keep (n : Nat) (_ : 0 < n + 1) : Nat := n

def fixtures_shared_drop (n : Nat) (_ : 0 < n + 1) : Nat := n + 1

def fixtures_shared_earlier : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_shared_keep n (by omega) + fixtures_shared_earlier n

def fixtures_shared_honest : Nat → Nat
  | 0 => 0
  | n + 1 => fixtures_shared_keep n (by omega) + fixtures_shared_honest n

/-- `forge_shared_proof_helper name diverge`: copy `fixtures_shared_honest`, its functional, its
smart-unfolding definition and its helper under `name`; with `diverge`, the copied helper calls
`fixtures_shared_drop` in place of `fixtures_shared_keep`. -/
elab "forge_shared_proof_helper " id:ident diverge:(&"diverge")? : command => do
  let honest := ``fixtures_shared_honest
  let forged := id.getId
  let env ← getEnv
  let copied := fun (suffix : Name) (swap : Bool) => do
    let some (.defnInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    let value := info.value.replace fun
      | .const n us =>
        if n.getPrefix == honest || n == honest then
          some (mkConst (n.replacePrefix honest forged) us)
        else if swap && n == ``fixtures_shared_keep then
          some (mkConst ``fixtures_shared_drop us)
        else none
      | _ => none
    pure { info with name := forged ++ suffix, value, all := [forged ++ suffix] }
  liftCoreM <| addDecl (.defnDecl (← copied `_f false))
  liftCoreM <| addDecl (.defnDecl (← copied .anonymous false))
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  liftCoreM <| addDecl (.defnDecl (← copied `_sunfold false))
  liftCoreM <| addDecl (.mutualDefnDecl [← copied `_unsafe_rec diverge.isSome])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_shared_proof_helper fixtures_shared_faithful

forge_shared_proof_helper fixtures_shared_divergent diverge
