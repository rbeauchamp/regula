import Lean

/-
Mutation (issue #210, adversarial, found in review) at the compiler boundary:
a helper behind an authored `brecOn` of an inductive type the module adds by
metaprogram. It was admitted on `main` at 2e741c6, after Regula v0.4.2 and
before the kernel-checked recursion equation.

Lean's structural compiler finds `T.below` and `T.brecOn` by name and checks
the type of the application it builds, never the body of `T.brecOn`. The
`inductive` command generates both; a module that adds an inductive type
through `addDecl` generates, or writes, its own.

`FixturesCompanion` is a type of unary numbers added that way, with Lean's own
`casesOn` and `below`. `FixturesCompanion.brecOn` is authored: it takes the
arguments the compiler passes for a function into `Nat`, ignores them and
returns `0`. `fixtures_companion_forged` is then an ordinary definition, and
everything about it is Lean's own: its structural compiler produces a base
that is `FixturesCompanion.brecOn` applied, so the base is `0` everywhere
(`fixtures_companion_base_zero`), and its helper returns `1` at
`FixturesCompanion.zero`, the code Lean runs.

A regeneration from the helper runs the same compiler over the same authored
`brecOn` and reproduces the base, so reproducing the base does not show that
the helper computes it. The helper is rejected because the kernel checks no
proof of its recursion equation for the base,

`fixtures_companion_forged t = match t with | zero => 1 | succ p => fixtures_companion_forged p`

which is false at `zero`. `fixtures_companion_honest` is the same definition
over `Nat`, whose `brecOn` Lean generated, and its helper is admitted.
-/
open Lean Elab Command Meta

/-- `declare_companion_forge`: add `FixturesCompanion` with constructors `zero` and `succ`, Lean's
`casesOn` and `below` for it, and an authored `brecOn` that returns `0`. -/
elab "declare_companion_forge" : command => do
  let type := mkConst `FixturesCompanion
  liftCoreM <| addDecl <| .inductDecl [] 0
    [{ name := `FixturesCompanion, type := mkSort 1
       ctors := [{ name := `FixturesCompanion.zero, type },
                 { name := `FixturesCompanion.succ, type := mkForall `p .default type type }] }]
    false
  liftCoreM <| compileDecls #[`FixturesCompanion]
  liftTermElabM do
    mkCasesOn `FixturesCompanion
    mkBelow `FixturesCompanion
    let u := mkLevelParam `u
    let motiveType := mkForall `t .default type (mkSort u)
    let nat := mkConst ``Nat
    -- `(motive : T → Sort u) (t : T) (F : (t : T) → T.below motive t → Nat) : Nat := 0`
    let step := mkForall `t .default type
      (mkForall `f .default (mkApp2 (mkConst `FixturesCompanion.below [u]) (.bvar 2) (.bvar 0)) nat)
    addDecl <| .defnDecl {
      name := `FixturesCompanion.brecOn, levelParams := [`u]
      type := mkForall `motive .implicit motiveType
        (mkForall `t .default type (mkForall `F_1 .default step nat))
      value := mkLambda `motive .implicit motiveType
        (mkLambda `t .default type (mkLambda `F_1 .default step (mkNatLit 0)))
      hints := .abbrev, safety := .safe, all := [`FixturesCompanion.brecOn] }
    compileDecls #[`FixturesCompanion.brecOn]
  for name in [`FixturesCompanion, `FixturesCompanion.zero, `FixturesCompanion.succ,
      `FixturesCompanion.brecOn] do
    addDeclarationRangesFromSyntax name (← getRef)

declare_companion_forge

def fixtures_companion_honest (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => fixtures_companion_honest k

def fixtures_companion_forged (t : FixturesCompanion) : Nat :=
  match t with
  | .zero => 1
  | .succ p => fixtures_companion_forged p

set_option smartUnfolding false in
/-- The base Lean compiled is `0` everywhere, also where its helper returns `1`. -/
theorem fixtures_companion_base_zero (t : FixturesCompanion) : fixtures_companion_forged t = 0 :=
  rfl
