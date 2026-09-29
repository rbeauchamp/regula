/-
Positive control (issue #125): `deriving DecidableEq` on a recursive inductive
generates a structurally recursive comparison, with Lean's `_unsafe_rec`
helper, inside the inductive's own declaration command and with information
trees disabled. The module registers no macro or elaborator for a syntax kind
it does not declare, so the helper is admitted without a binder record. The
stored predefinition abstracts the comparison's nested proofs into auxiliary
theorems that the helper keeps inline; the helper is compared up to proofs.
-/

inductive FixturesShape where
  | leaf
  | wrap (inner : FixturesShape)
  | pair (left right : FixturesShape)
  deriving DecidableEq
