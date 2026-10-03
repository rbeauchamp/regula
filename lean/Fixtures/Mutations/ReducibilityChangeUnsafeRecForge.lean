import Lean

/-
Mutation (issue #188, adversarial) at the compiler boundary: forged helpers
on the two paths that admit a helper whose base Lean compiled under another
reducibility than the audit inspects.

`fixtures_forged_threaded_honest` is measured through
`fixtures_forged_threaded_second`, `irreducible` only inside its section, so
its base passes the recursive-call function through the `match` on `a` and
the regeneration does not: the comparison takes the two forms of that `match`
as one. `fixtures_forged_alias_honest` recurses structurally on an argument
whose type is made `irreducible` afterwards, so only the regeneration with no
definition irreducible reproduces its base. A custom command copies each
definition, the auxiliary definitions Lean compiled it into (`_unary` for well-founded
recursion, `_f` and `_sunfold` for structural), the unfolding theorems Lean
proved with the well-founded definition (`eq_def`, issue #210: the kernel has
to check the base's recursion equation, and for a well-founded definition the
checker finds its proof in that theorem; for a structural one Lean realizes
the theorem for the regenerated definition) and its range-less `_unsafe_rec`
helper twice:

- `fixtures_forged_threaded_faithful` and `fixtures_forged_alias_faithful`
  rename only, and
- `fixtures_forged_threaded_divergent` and `fixtures_forged_alias_divergent`
  also make the helper call `fixtures_forged_reducibility_skip` where the
  kernel-checked base calls `fixtures_forged_reducibility_step`, so the code
  Lean runs for each is not the definition the kernel checked.

Exact match admits the honest helpers and the faithful copies, and rejects the
divergent ones alone. Passing a variable through a `match` relates only the
variable the alternative binds to the variable passed: inside the alternative
the regenerated functional still calls `fixtures_forged_reducibility_skip`
where the observed one calls `fixtures_forged_reducibility_step`. The second
regeneration environment only selects which regeneration runs, and what it
adds still has to equal the observed definitions.
-/
open Lean Elab Command

def fixtures_forged_reducibility_step (n : Nat) : Nat := n + 1

def fixtures_forged_reducibility_skip (n : Nat) : Nat := n + 2

def fixtures_forged_threaded_second (_ n : Nat) : Nat := n

theorem fixtures_forged_threaded_second_eq (a n : Nat) :
    fixtures_forged_threaded_second a n = n := rfl

section
attribute [local irreducible] fixtures_forged_threaded_second

def fixtures_forged_threaded_honest (a n : Nat) : Nat :=
  match a with
  | 0 =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_forged_threaded_honest (fixtures_forged_reducibility_step 0) k
  | a' + 1 =>
    match n with
    | 0 => a' + 1
    | k + 1 => fixtures_forged_threaded_honest (fixtures_forged_reducibility_step (a' + 1)) k
termination_by fixtures_forged_threaded_second a n
decreasing_by
  all_goals
    rw [fixtures_forged_threaded_second_eq, fixtures_forged_threaded_second_eq]
    exact Nat.lt_succ_self _
end

def FixturesForgedAlias := List Nat

def fixtures_forged_alias_honest (xs : FixturesForgedAlias) : Nat :=
  match xs with
  | [] => 0
  | x :: rest => fixtures_forged_reducibility_step x + fixtures_forged_alias_honest rest

attribute [irreducible] FixturesForgedAlias

/-- `forge_reducibility_helper honest name diverge`: copy `honest`, its auxiliary definitions
(`_unary`, or `_f` and `_sunfold`), the unfolding theorems Lean proved with a well-founded
definition and its helper under `name`; with `diverge`, the copied helper calls
`fixtures_forged_reducibility_skip` in place of `fixtures_forged_reducibility_step`. -/
elab "forge_reducibility_helper " source:ident id:ident diverge:(&"diverge")? : command => do
  let honest := source.getId
  let forged := id.getId
  let auxiliaries := [`_unary, `_f, `_sunfold]
  let theorems := [`_unary ++ `eq_def, `eq_def]
  let copies := ([.anonymous, `_unsafe_rec] ++ auxiliaries ++ theorems).map (honest ++ ·)
  let env ← getEnv
  let renamed := fun (swap : Bool) (e : Expr) => e.replace fun
    | .const n us =>
      if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
      else if swap && n == ``fixtures_forged_reducibility_step then
        some (mkConst ``fixtures_forged_reducibility_skip us)
      else none
    | _ => none
  let copied := fun (suffix : Name) (swap : Bool) => do
    let some (.defnInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    pure { info with
      name := forged ++ suffix, value := renamed swap info.value, all := [forged ++ suffix] }
  -- `_sunfold` mentions the definition; the definition mentions the other two.
  for suffix in [`_unary, `_f, .anonymous, `_sunfold] do
    if env.contains (honest ++ suffix) then
      liftCoreM <| addDecl (.defnDecl (← copied suffix false))
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  -- The theorem of the definition cites that of `_unary`.
  for suffix in theorems do
    if let some (.thmInfo info) := env.find? (honest ++ suffix) then
      liftCoreM <| addDecl (.thmDecl { info with
        name := forged ++ suffix, type := renamed false info.type
        value := renamed false info.value, all := [forged ++ suffix] })
  liftCoreM <| addDecl (.mutualDefnDecl [← copied `_unsafe_rec diverge.isSome])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_reducibility_helper fixtures_forged_threaded_honest fixtures_forged_threaded_faithful

forge_reducibility_helper fixtures_forged_threaded_honest fixtures_forged_threaded_divergent diverge

forge_reducibility_helper fixtures_forged_alias_honest fixtures_forged_alias_faithful

forge_reducibility_helper fixtures_forged_alias_honest fixtures_forged_alias_divergent diverge
