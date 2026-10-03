import Lean

/-
Mutation (issue #210, adversarial, found in review) at the compiler boundary:
a helper behind matcher metadata that Lean's own well-founded compiler reads
while it compiles the definition. It was admitted on `main` at 2e741c6, after
Regula v0.4.2 and before the kernel-checked recursion equation.

Where a `match` refines the type of the function that stands for the
recursive calls, Lean's compiler passes that function through the `match`
(`MatcherApp.addArg`): it adds one binder to every alternative after the
pattern variables Lean's matcher metadata says the alternative binds. That
count is metadata the audited module can write.

`fixtures_threaded.match_1` is no matcher: it applies its one alternative to
the constant function `fun _ _ => 42`, of type `FixturesThreadedCalls n`. A
command registers it as a matcher whose alternative binds no pattern variable.
`FixturesThreadedCalls n` is the type of the recursive-call function of a
definition measured by `n`, behind `FixturesThreadedRel`, which is irreducible
where the definition is compiled: Lean's test that the alternative's type was
refined then succeeds, while the kernel, which unfolds everything, accepts the
new binder in the place of the alternative's own argument. The recursive call
of `fixtures_threaded_forged` therefore becomes a call of the function the
fake matcher supplies. The base is `42` at `1`
(`fixtures_threaded_base_differs`) and the helper, the code Lean runs, returns
`0`.

Lean itself refuses the definition: it cannot prove the unfolding equation
`fixtures_threaded_forged.eq_def`, which is false. It has added the base and
the helper by then, so `forge_definition` drops the error and keeps them, as a
metaprogram that adds both declarations directly would.

A regeneration from the helper runs the same compiler over the same metadata
and reproduces the base, with no application left for the comparison's
threading law to check. The helper is rejected because the kernel checks no
proof of its recursion equation for the base, which is false at `1`.
`fixtures_threaded_honest` is an ordinary definition and its helper is
admitted.
-/
open Lean Elab Command

def FixturesThreadedRel (y n : Nat) : Prop := y < n

theorem fixtures_threaded_rel_succ (k : Nat) : FixturesThreadedRel k (k + 1) :=
  Nat.lt_succ_self k

def FixturesThreadedCalls (n : Nat) : Type := ∀ y, FixturesThreadedRel y n → Nat

def fixtures_threaded.match_1.{u} (motive : Nat → Sort u) (n : Nat)
    (k : FixturesThreadedCalls n → motive n) : motive n :=
  k (fun _ _ => 42)

attribute [irreducible] FixturesThreadedRel

/-- `register_threaded_matcher name`: describe `name` to Lean as a matcher with no parameters, one
discriminant and one alternative that binds no pattern variable. -/
elab "register_threaded_matcher " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftCoreM <| Lean.Meta.Match.addMatcherInfo name {
    numParams := 0, numDiscrs := 1
    altInfos := #[{ numFields := 0, numOverlaps := 0, hasUnitThunk := false }]
    uElimPos? := some 0, discrInfos := #[{}], overlaps := {} }

register_threaded_matcher fixtures_threaded.match_1

/-- `forge_definition cmd`: elaborate `cmd` and keep the declarations it added, dropping the errors
it reported. -/
elab "forge_definition " cmd:command : command => do
  let messages := (← get).messages
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    try elabCommand cmd catch _ => pure ()
  modify ({ · with messages })

forge_definition
def fixtures_threaded_forged (n : Nat) : Nat :=
  fixtures_threaded.match_1 (fun _ => Nat) n fun _ =>
    match n with
    | 0 => 0
    | k + 1 => fixtures_threaded_forged k
termination_by n
decreasing_by all_goals exact fixtures_threaded_rel_succ _

def fixtures_threaded_honest (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => fixtures_threaded_honest k
termination_by n

/-- The base Lean compiled is `42` at `1`, where its helper returns `0`. -/
theorem fixtures_threaded_base_differs : fixtures_threaded_forged 1 = 42 := by
  delta fixtures_threaded_forged
  rw [WellFounded.Nat.fix_eq]
