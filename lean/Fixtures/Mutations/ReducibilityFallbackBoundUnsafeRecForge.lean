import Lean

/-
Mutation (issue #196, adversarial) at the compiler boundary: a forged helper
for which the assignments tried after the search for a reducibility assignment
stop at their bound. The audit this fixture expects is incomplete: the checker
reports the forged helper as undecided, neither admitted nor rejected.

`fixtures_reached_honest` passes each of two parameters through a function
made `reducible` afterwards, and its leaf calls five more functions that are
`@[reducible]` from their declaration. Only the two functions in the recursive
call change a decision of Lean's compilers, so the search for the statuses
that change one is exhaustive over three assignments, and the honest helper is
admitted under one of them (`fixtures_forged_bound_honest` of
`Fixtures.Mutations.ReducibleAfterUnsafeRecForge` is that shape, admitted
beside its faithful copy).

A custom command copies the definition, its `_unary` definition, the
unfolding theorems Lean proved with them and its range-less `_unsafe_rec`
helper as `fixtures_forged_bound_divergent`, and makes the copied helper call
`fixtures_reached_skip` at its non-recursive leaf, where the kernel-checked
base calls `fixtures_reached_step`. None of the three assignments reproduces
it: each regenerates a definition whose leaf calls `fixtures_reached_skip`,
which the comparison rejects. The checker then tries the assignments of the
search that one replaces, which gives the definitions of the helper's module
that the helper reaches the statuses a global attribute can have replaced.
The helper reaches seven such definitions, which allow 127 assignments, more
than the 63 the checker enumerates, so only the seven single changes are
tried, and none reproduces the helper either. Not every assignment was tried,
so the checker reports no rejection: a helper no attempt within the bound
reproduces is undecided, and the audit is incomplete, with no violation
reported for it.
-/
open Lean Elab Command

def fixtures_reached_step (n : Nat) : Nat := n + 1

def fixtures_reached_skip (n : Nat) : Nat := n + 2

def fixtures_reached_first (a : Nat) : Nat := a

def fixtures_reached_second (a : Nat) : Nat := a

@[reducible] def fixtures_reached_one (a : Nat) : Nat := a

@[reducible] def fixtures_reached_two (a : Nat) : Nat := a

@[reducible] def fixtures_reached_three (a : Nat) : Nat := a

@[reducible] def fixtures_reached_four (a : Nat) : Nat := a

@[reducible] def fixtures_reached_five (a : Nat) : Nat := a

def fixtures_reached_honest (a b n : Nat) : Nat :=
  match n with
  | 0 =>
    fixtures_reached_step (fixtures_reached_one (fixtures_reached_two
      (fixtures_reached_three (fixtures_reached_four (fixtures_reached_five (a + b))))))
  | k + 1 =>
    fixtures_reached_honest (fixtures_reached_first a) (fixtures_reached_second b) k
termination_by n

attribute [reducible] fixtures_reached_first fixtures_reached_second

/-- `forge_fallback_bound_helper honest name`: copy `honest`, its `_unary` definition, the
unfolding theorems Lean proved for them and its helper under `name`; the copied helper calls
`fixtures_reached_skip` in place of `fixtures_reached_step`. -/
elab "forge_fallback_bound_helper " source:ident id:ident : command => do
  let honest := source.getId
  let forged := id.getId
  let theorems := [`_unary ++ `eq_def, `eq_def]
  let copies := ([.anonymous, `_unsafe_rec, `_unary] ++ theorems).map (honest ++ ·)
  let env ← getEnv
  let renamed := fun (swap : Bool) (e : Expr) => e.replace fun
    | .const n us =>
      if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
      else if swap && n == ``fixtures_reached_step then some (mkConst ``fixtures_reached_skip us)
      else none
    | _ => none
  let copied := fun (suffix : Name) (swap : Bool) => do
    let some (.defnInfo info) := env.find? (honest ++ suffix)
      | throwError "missing {honest ++ suffix}"
    pure { info with
      name := forged ++ suffix, value := renamed swap info.value, all := [forged ++ suffix] }
  -- The definition mentions `_unary`.
  for suffix in [`_unary, .anonymous] do
    liftCoreM <| addDecl (.defnDecl (← copied suffix false))
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  -- The theorem of the definition cites that of `_unary`.
  for suffix in theorems do
    if let some (.thmInfo info) := env.find? (honest ++ suffix) then
      liftCoreM <| addDecl (.thmDecl { info with
        name := forged ++ suffix, type := renamed false info.type
        value := renamed false info.value, all := [forged ++ suffix] })
  liftCoreM <| addDecl (.mutualDefnDecl [← copied `_unsafe_rec true])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_fallback_bound_helper fixtures_reached_honest fixtures_forged_bound_divergent
