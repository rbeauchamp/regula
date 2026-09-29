import Lean

/-
Mutation (issue #125): `Positive.AttributedRecursion` plus one module value of
an imported record type whose fields are simprocs (`Lean.Meta.Simp.Methods`),
the shape of a library extension record (such as a `MetaM` evaluation field)
that an imported tactic can run without an evaluator record. The value's own
type is not a function, but its structure's fields reach `Lean.Core.Context`,
so later helpers of the module are not admitted.
-/
open Lean

def fixturesMethods : Meta.Simp.Methods := {}

@[simp] def fixtures_record_sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + fixtures_record_sum xs
