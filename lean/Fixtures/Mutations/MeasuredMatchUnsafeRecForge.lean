import Lean

/-
Mutation (issue #183, adversarial) at the compiler boundary: a forged helper
on the path that admits a helper by regenerating its base with the base's own
relation. `fixtures_forged_measured_honest` matches on its measured argument
after an argument that also changes, so its base holds the relation the
regeneration reads. A custom command copies its base, the unary definition
that holds its well-founded fixpoint and its range-less `_unsafe_rec` helper
three times:

- `fixtures_forged_measured_faithful` renames only, and also copies the
  unfolding theorems Lean proved with the definition (`eq_def` of the
  definition and of its unary definition), so that the copy has a theorem of
  that name (issue #210). The command declares the copies, not Lean's
  compiler, and it could as well prove them itself: the kernel checks a
  theorem of that name against the checker's statement, whoever declared it;
- `fixtures_forged_measured_divergent` copies the same and also makes the
  helper call `fixtures_forged_measured_skip` where the kernel-checked base
  calls `fixtures_forged_measured_step`, so the code Lean runs for it is not
  the definition the kernel checked; and
- `fixtures_forged_measured_bare` renames only and copies no theorem.

Exact match admits the honest helper and the faithful copy, and rejects the
other two. The relation read from a base selects only which regeneration runs,
and the functional regenerated from the divergent helper, which calls
`fixtures_forged_measured_skip`, still has to equal the observed one, which
calls `fixtures_forged_measured_step`. The bare copy is a helper that computes
its base, rejected all the same: the kernel has to check the base's recursion
equation, and for a well-founded definition the checker looks for a proof in
a theorem named `eq_def`, which Lean adds with the definition and this copy
lacks. That rejection is a limit of the checker's proof search (standard
§7.4), not a claim that the helper is wrong.
-/
open Lean Elab Command

def fixtures_forged_measured_step (n : Nat) : Nat := n + 1

def fixtures_forged_measured_skip (n : Nat) : Nat := n + 2

def fixtures_forged_measured_honest (index remaining : Nat) : Nat :=
  match remaining with
  | 0 => index
  | count + 1 => fixtures_forged_measured_honest (fixtures_forged_measured_step index) count
termination_by remaining

/-- `forge_measured_helper name diverge bare`: copy `fixtures_forged_measured_honest`, its unary
definition and its helper under `name`, and, without `bare`, the unfolding theorems of both
definitions; with `diverge`, the copied helper calls `fixtures_forged_measured_skip` in place of
`fixtures_forged_measured_step`. -/
elab "forge_measured_helper " id:ident diverge:(&"diverge")? bare:(&"bare")? : command => do
  let honest := ``fixtures_forged_measured_honest
  let forged := id.getId
  let diverge := diverge.isSome
  let theorems := if bare.isSome then [] else [`_unary ++ `eq_def, `eq_def]
  let copies := [.anonymous, `_unary, `_unsafe_rec, `_unary ++ `eq_def, `eq_def].map (honest ++ ·)
  let env ← getEnv
  let renamed := fun (swap : Bool) (e : Expr) => e.replace fun
    | .const n us =>
      if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
      else if swap && n == ``fixtures_forged_measured_step then
        some (mkConst ``fixtures_forged_measured_skip us)
      else none
    | _ => none
  let copied := fun (suffix : Name) (swap : Bool) => do
    let some (.defnInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    pure { info with
      name := forged ++ suffix, value := renamed swap info.value, all := [forged ++ suffix] }
  liftCoreM <| addDecl (.defnDecl (← copied `_unary false))
  liftCoreM <| addDecl (.defnDecl (← copied .anonymous false))
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  -- The theorem of the definition cites that of its unary definition.
  for suffix in theorems do
    let some (.thmInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    liftCoreM <| addDecl (.thmDecl { info with
      name := forged ++ suffix, type := renamed false info.type
      value := renamed false info.value, all := [forged ++ suffix] })
  liftCoreM <| addDecl (.mutualDefnDecl [← copied `_unsafe_rec diverge])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_measured_helper fixtures_forged_measured_faithful

forge_measured_helper fixtures_forged_measured_divergent diverge

forge_measured_helper fixtures_forged_measured_bare bare
