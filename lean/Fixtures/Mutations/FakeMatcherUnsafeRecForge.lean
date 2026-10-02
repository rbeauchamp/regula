import Lean

/-
Mutation (issue #188, adversarial, found in review) at the compiler boundary:
forged helpers behind constants that only Lean's matcher metadata calls
matchers. The comparison takes a `match` that passes a variable through as the
`match` that uses the variable directly. Which constants are matchers, and how
many pattern variables each alternative binds, is metadata the audited module
can write, so the comparison applies that rule only where the kernel checks
the law for the constant itself.

`fixtures_fake.match_1` and `fixtures_fake.match_2` return their last argument
and are no matchers. A command registers each as one, with one discriminant
and one alternative that binds one pattern variable. Under that description

- `fixtures_fake.match_1 (Nat → Nat → Nat) 0 (fun _ w => w) v` passes `v`
  through and binds it as `w`, and
- `fixtures_fake.match_1 (Nat → Nat) 0 (fun _ => v)` uses `v` directly,

yet the first is the identity and the second the constant function `v`
(`fixtures_fake_leaves_differ`). `fixtures_fake.match_2` is the same with a
motive of the shape a matcher has, so the law can be stated for it and is
false. `fixtures_fake_threaded` and `fixtures_fake_direct` are honest
definitions with those two leaves, and so are `fixtures_fake_motive_threaded`
and `fixtures_fake_motive_direct`. `fixtures_fake_forged` and
`fixtures_fake_motive_forged` each copy the definition of the first of their
pair and take the range-less `_unsafe_rec` helper of the second, so the code
Lean runs for them is not the definition the kernel checked.

Exact match admits the four honest helpers and rejects the two forged ones: no
theorem "for every alternative and argument, passing the argument through
equals using it directly" is checked by the kernel for either constant (for
the first it cannot be stated, for the second it is false), and the two leaves
are compared as the different applications they are.
-/
open Lean Elab Command

def fixtures_fake.match_1 (T : Type) (_ : Nat) (k : T) : T := k

def fixtures_fake.match_2 (motive : Nat → Type) (d : Nat) (k : motive d) : motive d := k

def fixtures_fake_threaded (v : Nat) : Nat → Nat → Nat
  | 0 => fixtures_fake.match_1 (Nat → Nat → Nat) 0 (fun _ w => w) v
  | n + 1 => fixtures_fake_threaded v n

def fixtures_fake_direct (v : Nat) : Nat → Nat → Nat
  | 0 => fixtures_fake.match_1 (Nat → Nat) 0 (fun _ => v)
  | n + 1 => fixtures_fake_direct v n

def fixtures_fake_motive_threaded (v : Nat) : Nat → Nat → Nat
  | 0 => fixtures_fake.match_2 (fun _ => Nat → Nat → Nat) 0 (fun _ w => w) v
  | n + 1 => fixtures_fake_motive_threaded v n

def fixtures_fake_motive_direct (v : Nat) : Nat → Nat → Nat
  | 0 => fixtures_fake.match_2 (fun _ => Nat → Nat) 0 (fun _ => v)
  | n + 1 => fixtures_fake_motive_direct v n

/-- The two leaves differ, under either constant: a forged helper returns `0` where its
definition has the value `1`. -/
theorem fixtures_fake_leaves_differ :
    fixtures_fake_threaded 0 0 1 = 1 ∧ fixtures_fake_direct 0 0 1 = 0 ∧
      fixtures_fake_motive_threaded 0 0 1 = 1 ∧ fixtures_fake_motive_direct 0 0 1 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `register_fake_matcher name`: describe `name` to Lean as a matcher with no parameters, one
discriminant and one alternative binding one pattern variable. -/
elab "register_fake_matcher " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftCoreM <| Lean.Meta.Match.addMatcherInfo name {
    numParams := 0, numDiscrs := 1
    altInfos := #[{ numFields := 1, numOverlaps := 0, hasUnitThunk := false }]
    uElimPos? := none, discrInfos := #[{}], overlaps := {} }

/-- `forge_fake_helper threaded direct name`: copy the definition `threaded` and its auxiliary
definitions under `name`, with the helper of `direct` as `name._unsafe_rec`. -/
elab "forge_fake_helper " threaded:ident direct:ident id:ident : command => do
  let forged := id.getId
  let env ← getEnv
  let copied := fun (source suffix : Name) => do
    let names := [.anonymous, `_f, `_sunfold, `_unsafe_rec].map (source ++ ·)
    let some (.defnInfo info) := env.find? (source ++ suffix)
      | throwError "missing {source ++ suffix}"
    let value := info.value.replace fun
      | .const n us =>
        if names.contains n then some (mkConst (n.replacePrefix source forged) us) else none
      | _ => none
    pure { info with name := forged ++ suffix, value, all := [forged ++ suffix] }
  -- `_sunfold` mentions the definition; the definition mentions `_f`.
  for suffix in [`_f, .anonymous, `_sunfold] do
    if env.contains (threaded.getId ++ suffix) then
      liftCoreM <| addDecl (.defnDecl (← copied threaded.getId suffix))
  liftCoreM <| Lean.Meta.markAsRecursive forged
  addDeclarationRangesFromSyntax forged (← getRef)
  liftCoreM <| addDecl (.mutualDefnDecl [← copied direct.getId `_unsafe_rec])
  liftCoreM <| compileDecls #[forged ++ `_unsafe_rec]

forge_fake_helper fixtures_fake_threaded fixtures_fake_direct fixtures_fake_forged

forge_fake_helper fixtures_fake_motive_threaded fixtures_fake_motive_direct
  fixtures_fake_motive_forged

register_fake_matcher fixtures_fake.match_1

register_fake_matcher fixtures_fake.match_2
