import Lean

/-
Mutation (issue #196, adversarial) at the compiler boundary: forged helpers
on the two search paths that admit a helper whose base depends on a
reducibility status Lean's recursion compilers ask about where the search
once recorded nothing, or found no change.

`fixtures_forged_match_honest` recurses structurally and passes its parameter
through a `match` on `fixtures_forged_where_flag`, an `abbrev` that is
irreducible only where the definition is compiled, so the `match` is stuck
there and its base keeps the parameter varying. At the end of the audit the
`match` reduces, with Lean's unfolding predicate put aside, so the parameter is
fixed and nothing is recorded for the flag: only the analysis recorded with no
definition unfolding for its status asks about it, and only the assignment
that gives the flag back as semireducible reproduces the base.

`fixtures_forged_typed_honest` maps over its argument through
`fixtures_forged_where_map`, and the argument's type goes through
`FixturesForgedList` and `FixturesForgedItem`, all three `reducible` only where
the definition is compiled. The toolchain's `List.map` rule matches only where
all three unfold, the preprocessing asks about each before any change, and the
two type functions are mentioned only in types, so the mentions the base keeps
say nothing about them: only following the change of the first function
through the questions it newly raises reaches the assignment that reproduces
the base.

A custom command copies each definition, the auxiliary definitions Lean
compiled it into (`_unary` for well-founded recursion, `_f` and `_sunfold` for
structural), the unfolding theorems Lean proved with the well-founded
definition (`eq_def`, issue #210) and its range-less `_unsafe_rec` helper
twice:

- `fixtures_forged_match_faithful` and `fixtures_forged_typed_faithful`
  rename only, and
- `fixtures_forged_match_divergent` and `fixtures_forged_typed_divergent`
  also make the helper call `fixtures_forged_where_skip` at its non-recursive
  leaf, where the kernel-checked base calls `fixtures_forged_where_step`, so
  the code Lean runs for each is not the definition the kernel checked.

Exact match admits the honest helpers and the faithful copies, and rejects the
divergent ones alone: an assignment only selects which regeneration runs, and
the one that reproduces the honest base regenerates, from a divergent helper,
a definition whose leaf calls `fixtures_forged_where_skip`, which the
comparison, made in the inspected environment against the observed base,
rejects. No bound of the search is reached for the divergent helpers, so each
is a violation, not an incomplete audit.

A definition by structural recursion over an inductive predicate, the third
form of the issue, has no control here: its type is a proposition, its helper
and its base are proofs of that proposition, and Lean's code generator erases
both, so no helper of that type runs other code than its base.
-/
open Lean Elab Command

def fixtures_forged_where_step (n : Nat) : Nat := n + 1

def fixtures_forged_where_skip (n : Nat) : Nat := n + 2

abbrev fixtures_forged_where_flag : Bool := true

set_option allowUnsafeReducibility true in
attribute [local irreducible] fixtures_forged_where_flag in
def fixtures_forged_match_honest (a : Nat) : List Nat → Nat
  | [] => fixtures_forged_where_step a
  | _ :: xs =>
    fixtures_forged_match_honest
      (match fixtures_forged_where_flag with | true => a | false => a) xs

inductive FixturesForgedTree where
  | node : List FixturesForgedTree → FixturesForgedTree

def fixtures_forged_where_map {α β : Type} (f : α → β) (xs : List α) : List β := List.map f xs

def FixturesForgedList (α : Type) : Type := List α

def FixturesForgedItem (α : Type) : Type := α

def fixtures_forged_where_typed (_ : Type) (n : Nat) : Nat := n

set_option allowUnsafeReducibility true in
attribute [local reducible] fixtures_forged_where_map FixturesForgedList FixturesForgedItem in
def fixtures_forged_typed_honest
    (trees : FixturesForgedList (FixturesForgedItem FixturesForgedTree)) (fuel : Nat) : Nat :=
  match fuel with
  | 0 =>
    fixtures_forged_where_step
      (fixtures_forged_where_typed (FixturesForgedList (FixturesForgedItem FixturesForgedTree)) 0)
  | fuel + 1 =>
    (fixtures_forged_where_map
      (fun (tree : FixturesForgedTree) =>
        match tree with
        | .node children => 1 + fixtures_forged_typed_honest children fuel) trees).sum
termination_by fuel

/-- `forge_where_compiled_helper honest name diverge`: copy `honest`, its auxiliary definitions
(`_unary`, or `_f` and `_sunfold`), the unfolding theorems Lean proved with a well-founded
definition and its helper under `name`; with `diverge`, the copied helper calls
`fixtures_forged_where_skip` in place of `fixtures_forged_where_step`. -/
elab "forge_where_compiled_helper " source:ident id:ident diverge:(&"diverge")? : command => do
  let honest := source.getId
  let forged := id.getId
  let auxiliaries := [`_unary, `_f, `_sunfold]
  let theorems := [`_unary ++ `eq_def, `eq_def]
  let copies := ([.anonymous, `_unsafe_rec] ++ auxiliaries ++ theorems).map (honest ++ ·)
  let env ← getEnv
  let renamed := fun (swap : Bool) (e : Expr) => e.replace fun
    | .const n us =>
      if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
      else if swap && n == ``fixtures_forged_where_step then
        some (mkConst ``fixtures_forged_where_skip us)
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

forge_where_compiled_helper fixtures_forged_match_honest fixtures_forged_match_faithful

forge_where_compiled_helper fixtures_forged_match_honest fixtures_forged_match_divergent diverge

forge_where_compiled_helper fixtures_forged_typed_honest fixtures_forged_typed_faithful

forge_where_compiled_helper fixtures_forged_typed_honest fixtures_forged_typed_divergent diverge
