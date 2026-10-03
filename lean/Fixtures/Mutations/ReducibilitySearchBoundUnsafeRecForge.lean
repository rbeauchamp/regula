import Lean

/-
Mutation (issue #196, adversarial) at the compiler boundary: a forged helper
for which the search for a reducibility assignment stops at its bound. The
audit this fixture expects is incomplete: the checker reports the forged
helper as undecided, neither admitted nor rejected.

`fixtures_over_honest` passes each of seven parameters through its own
function made `reducible` afterwards, so seven definitions each change which
parameters Lean finds fixed, and they allow 127 assignments of another status,
more than the 63 the search enumerates. The honest helper does not need the
enumeration: its observed base keeps no parameter fixed, which selects the
assignment that gives all seven back as semireducible, and the regeneration
under it reproduces the base (`fixtures_where_seven` of
`Fixtures.Positive.ReducibleWhereCompiled` is that shape, admitted).

A custom command copies the definition, its `_unary` definition, the
unfolding theorems Lean proved with them and its range-less `_unsafe_rec`
helper as `fixtures_over_divergent`, and makes the copied helper call
`fixtures_over_skip` at its non-recursive leaf, where the kernel-checked base
calls `fixtures_over_step`. The assignment its base selects regenerates a
definition whose leaf calls `fixtures_over_skip`, which the comparison
rejects, and so does each of the seven single changes the search then tries.
The search has not tried every assignment, so it reports no rejection: a
helper no attempt within the bound reproduces is undecided, and the audit is
incomplete, with no violation reported for it.
-/
open Lean Elab Command

def fixtures_over_step (n : Nat) : Nat := n + 1

def fixtures_over_skip (n : Nat) : Nat := n + 2

def fixtures_over_first (a : Nat) : Nat := a

def fixtures_over_second (a : Nat) : Nat := a

def fixtures_over_third (a : Nat) : Nat := a

def fixtures_over_fourth (a : Nat) : Nat := a

def fixtures_over_fifth (a : Nat) : Nat := a

def fixtures_over_sixth (a : Nat) : Nat := a

def fixtures_over_seventh (a : Nat) : Nat := a

def fixtures_over_honest (a b c d e f g n : Nat) : Nat :=
  match n with
  | 0 => fixtures_over_step (a + b + c + d + e + f + g)
  | k + 1 =>
    fixtures_over_honest (fixtures_over_first a) (fixtures_over_second b) (fixtures_over_third c)
      (fixtures_over_fourth d) (fixtures_over_fifth e) (fixtures_over_sixth f)
      (fixtures_over_seventh g) k
termination_by n

attribute [reducible] fixtures_over_first fixtures_over_second fixtures_over_third
  fixtures_over_fourth fixtures_over_fifth fixtures_over_sixth fixtures_over_seventh

/-- `forge_over_bound_helper honest name`: copy `honest`, its `_unary` definition, the unfolding
theorems Lean proved for them and its helper under `name`; the copied helper calls
`fixtures_over_skip` in place of `fixtures_over_step`. -/
elab "forge_over_bound_helper " source:ident id:ident : command => do
  let honest := source.getId
  let forged := id.getId
  let theorems := [`_unary ++ `eq_def, `eq_def]
  let copies := ([.anonymous, `_unsafe_rec, `_unary] ++ theorems).map (honest ++ ·)
  let env ← getEnv
  let renamed := fun (swap : Bool) (e : Expr) => e.replace fun
    | .const n us =>
      if copies.contains n then some (mkConst (n.replacePrefix honest forged) us)
      else if swap && n == ``fixtures_over_step then some (mkConst ``fixtures_over_skip us)
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

forge_over_bound_helper fixtures_over_honest fixtures_over_divergent
