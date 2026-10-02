import Lean

/-
Mutation (issue #209, adversarial, found in review) at the compiler boundary:
forged helpers behind an authored `_sunfold` declaration. Both were admitted
on Regula v0.4.2.

Lean's smart unfolding replaces the unfolding of `g` by that of a declaration
named `g._sunfold`, which it finds by that name alone. Lean generates one for
a structurally recursive definition; nothing stops a module from writing one
for any function, with another body and even another type, and the kernel
checks it as the ordinary definition it is.

- `fixtures_sunfold_next` is the successor function and `reducible`, and
  `fixtures_sunfold_next._sunfold` is authored as the identity. With smart
  unfolding, Lean's fixed-parameter analysis takes `fixtures_sunfold_next a`
  for `a`. `fixtures_sunfold_fixed_forged` copies the base of
  `fixtures_sunfold_fixed_honest`, whose recursive call passes `a`, beside a
  helper whose recursive call passes `fixtures_sunfold_next a`: the base
  returns `a` and the helper `a + n`. A regeneration that reads the authored
  declaration finds `a` fixed, drops the argument and reproduces the base.
- `FixturesSunfoldData ()` is `Nat`, and `FixturesSunfoldData._sunfold` is
  authored, after the definitions and helpers that use it, as `Type`. With smart
  unfolding, a value of type `FixturesSunfoldData ()` looks like a type, which
  the comparison erases. `fixtures_sunfold_erased_forged` copies the base of
  `fixtures_sunfold_erased_honest`, whose leaf is `fixtures_sunfold_one`,
  beside a helper whose leaf is `fixtures_sunfold_two`.

The honest helpers are admitted and both forged helpers are rejected: the
regeneration and the comparison run with smart unfolding off, so no
declaration is taken for another's unfolding by its name.
-/
open Lean Elab Command

@[reducible] def fixtures_sunfold_next (a : Nat) : Nat := a + 1

def fixtures_sunfold_next._sunfold (a : Nat) : Nat := a

def fixtures_sunfold_fixed_honest (a n : Nat) : Nat :=
  match n with
  | 0 => a
  | k + 1 => fixtures_sunfold_fixed_honest a k
termination_by n

def FixturesSunfoldData (_ : Unit) : Type := Nat

def fixtures_sunfold_one : FixturesSunfoldData () := (1 : Nat)

def fixtures_sunfold_two : FixturesSunfoldData () := (2 : Nat)

def fixtures_sunfold_erased_honest (n : Nat) : FixturesSunfoldData () :=
  match n with
  | 0 => fixtures_sunfold_one
  | k + 1 => fixtures_sunfold_erased_honest k
termination_by n

/-- `forge_sunfold_helper honest name`: copy `honest` and its helper under `name`, the copied
helper passing `fixtures_sunfold_next a` for the first argument `a` of a two-argument recursive
call and returning `fixtures_sunfold_two` where the base returns `fixtures_sunfold_one`. -/
elab "forge_sunfold_helper " source:ident id:ident : command => do
  let honest := source.getId
  let forged := id.getId
  let env ← getEnv
  let some (.defnInfo base) := env.find? honest | throwError "missing {honest}"
  let some (.defnInfo helper) := env.find? (honest ++ `_unsafe_rec)
    | throwError "missing helper of {honest}"
  let rename := fun (value : Expr) => value.replace fun
    | .const n us =>
      if n == honest then some (mkConst forged us)
      else if n == honest ++ `_unsafe_rec then some (mkConst (forged ++ `_unsafe_rec) us)
      else none
    | _ => none
  liftCoreM <| addDecl (.defnDecl
    { base with name := forged, value := rename base.value, all := [forged] })
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  let value := (rename helper.value).replace fun
    | .app (.app call@(.const n _) a) k =>
      if n == forged ++ `_unsafe_rec then
        some (mkApp2 call (mkApp (mkConst ``fixtures_sunfold_next) a) k)
      else none
    | .const n us =>
      if n == ``fixtures_sunfold_one then some (mkConst ``fixtures_sunfold_two us) else none
    | _ => none
  liftCoreM <| addDecl (.mutualDefnDecl
    [{ helper with name := forged ++ `_unsafe_rec, value, all := [forged ++ `_unsafe_rec] }])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_sunfold_helper fixtures_sunfold_fixed_honest fixtures_sunfold_fixed_forged

forge_sunfold_helper fixtures_sunfold_erased_honest fixtures_sunfold_erased_forged

-- Authored last: Lean's own code generator reads it too, and compiles no code for a function
-- whose result then looks like a type.
def FixturesSunfoldData._sunfold (_ : Unit) : Type 1 := Type
