import Lean

/-
Mutation (issue #196, adversarial) at the compiler boundary: forged helpers
where a candidate reducibility assignment exists, in each direction.

`fixtures_forged_after_honest` passes a parameter through
`fixtures_forged_after_keep`, made `reducible` afterwards, so its base packs
that parameter and no regeneration in the inspected environment does: only the
assignment that gives `fixtures_forged_after_keep` back as semireducible
reproduces the base. `fixtures_forged_before_honest` is the other way round:
`fixtures_forged_before_keep` is `@[reducible]` where the definition is
compiled and `irreducible` afterwards, and only the assignment that gives it
back as `reducible` reproduces the base. A custom command copies each
definition, the `_unary` definition Lean compiled it into where there is one,
the unfolding theorems Lean proved with them (`eq_def`, issue #210: the kernel
has to check the base's recursion equation, and for a well-founded definition
the checker looks for its proof in a theorem of that name, whoever declared
it) and its range-less `_unsafe_rec` helper twice:

- `fixtures_forged_after_faithful` and `fixtures_forged_before_faithful`
  rename only, and
- `fixtures_forged_after_divergent` and `fixtures_forged_before_divergent`
  also make the helper call `fixtures_forged_after_skip` at its non-recursive
  leaf, where the kernel-checked base calls `fixtures_forged_after_step`, so
  the code Lean runs for each is not the definition the kernel checked.

`fixtures_forged_bound_honest` passes each of two parameters through a function
made `reducible` afterwards, and its leaf calls five more functions that are
`@[reducible]` from their declaration: the shape for which the search once
stopped without a verdict, when it enumerated every definition of the module
the helper reaches (seven of them, 127 assignments, more than the 63 it
tries). Only the two functions in the recursive call change a decision of
Lean's compilers, so the search is exhaustive over three assignments and each
of the three helpers is decided: the honest one and its faithful copy are
admitted, and the divergent copy is rejected, where it was undecided before.

Exact match admits the honest helpers and the faithful copies, and rejects the
divergent ones alone. An assignment only selects which regeneration runs: the
one that reproduces the honest base regenerates, from a divergent helper, a
definition whose leaf calls `fixtures_forged_after_skip`, which the comparison,
made in the inspected environment against the observed base, rejects.
-/
open Lean Elab Command

def fixtures_forged_after_step (n : Nat) : Nat := n + 1

def fixtures_forged_after_skip (n : Nat) : Nat := n + 2

def fixtures_forged_after_keep (a : Nat) : Nat := a

def fixtures_forged_after_honest (a n : Nat) : Nat :=
  match n with
  | 0 => fixtures_forged_after_step a
  | k + 1 => fixtures_forged_after_honest (fixtures_forged_after_keep a) k
termination_by n

attribute [reducible] fixtures_forged_after_keep

@[reducible] def fixtures_forged_before_keep (a : Nat) : Nat := a

def fixtures_forged_before_honest (a n : Nat) : Nat :=
  match n with
  | 0 => fixtures_forged_after_step a
  | k + 1 => fixtures_forged_before_honest (fixtures_forged_before_keep a) k
termination_by n

set_option allowUnsafeReducibility true in
attribute [irreducible] fixtures_forged_before_keep

def fixtures_forged_bound_first (a : Nat) : Nat := a

def fixtures_forged_bound_second (a : Nat) : Nat := a

@[reducible] def fixtures_forged_bound_one (a : Nat) : Nat := a

@[reducible] def fixtures_forged_bound_two (a : Nat) : Nat := a

@[reducible] def fixtures_forged_bound_three (a : Nat) : Nat := a

@[reducible] def fixtures_forged_bound_four (a : Nat) : Nat := a

@[reducible] def fixtures_forged_bound_five (a : Nat) : Nat := a

def fixtures_forged_bound_honest (a b n : Nat) : Nat :=
  match n with
  | 0 =>
    fixtures_forged_after_step (fixtures_forged_bound_one (fixtures_forged_bound_two
      (fixtures_forged_bound_three (fixtures_forged_bound_four
        (fixtures_forged_bound_five (a + b))))))
  | k + 1 =>
    fixtures_forged_bound_honest (fixtures_forged_bound_first a) (fixtures_forged_bound_second b) k
termination_by n

attribute [reducible] fixtures_forged_bound_first fixtures_forged_bound_second

/-- `forge_reducible_after_helper honest name diverge`: copy `honest`, its `_unary` definition
where there is one, the unfolding theorems Lean proved for them and its helper under `name`; with
`diverge`, the copied helper calls `fixtures_forged_after_skip` in place of
`fixtures_forged_after_step`. -/
elab "forge_reducible_after_helper " source:ident id:ident diverge:(&"diverge")? : command => do
  let honest := source.getId
  let forged := id.getId
  let theorems := [`_unary ++ `eq_def, `eq_def]
  let copies := ([.anonymous, `_unsafe_rec, `_unary] ++ theorems).map (honest ++ ·)
  let env ← getEnv
  let renamed := fun (swap : Bool) (e : Expr) => e.replace fun
    | .const n us =>
      if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
      else if swap && n == ``fixtures_forged_after_step then
        some (mkConst ``fixtures_forged_after_skip us)
      else none
    | _ => none
  let copied := fun (suffix : Name) (swap : Bool) => do
    let some (.defnInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    pure { info with
      name := forged ++ suffix, value := renamed swap info.value, all := [forged ++ suffix] }
  -- The definition mentions `_unary`.
  for suffix in [`_unary, .anonymous] do
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

forge_reducible_after_helper fixtures_forged_after_honest fixtures_forged_after_faithful

forge_reducible_after_helper fixtures_forged_after_honest fixtures_forged_after_divergent diverge

forge_reducible_after_helper fixtures_forged_before_honest fixtures_forged_before_faithful

forge_reducible_after_helper fixtures_forged_before_honest fixtures_forged_before_divergent diverge

forge_reducible_after_helper fixtures_forged_bound_honest fixtures_forged_bound_faithful

forge_reducible_after_helper fixtures_forged_bound_honest fixtures_forged_bound_divergent diverge
