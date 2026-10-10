/-! Lean's generated constructor-index constructions (`T.ctorIdx`) for parameters, indices, an empty
type and private types pass: the pinned compiler builds each by `casesOn`, safe, with no unsafe
helper. -/

universe u

inductive FixturesConstructorIndex (α : Type u) where
  | left : α → FixturesConstructorIndex α
  | right : FixturesConstructorIndex α

inductive FixturesIndexed : Nat → Type where
  | zero : FixturesIndexed 0
  | successor {n : Nat} : FixturesIndexed n → FixturesIndexed (n + 1)

inductive FixturesEmpty : Type

private inductive FixturesPrivateIndex where
  | left
  | right

inductive FixturesSingle where
  | sole : Nat → FixturesSingle

inductive FixturesPredicate : Prop where
  | left
  | right
