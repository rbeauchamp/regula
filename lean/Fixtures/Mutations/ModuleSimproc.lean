import Lean

/-
Mutation (issue #125): `Positive.AttributedRecursion` plus one simproc the
module declares before the recursive definition. A simproc is `MetaM` code that
`simp` runs without an evaluator record, so later helpers of the module are not
admitted, although this one never runs.
-/
open Lean

simproc fixturesNoop (Nat.succ _) := fun _ => return .continue

@[simp] def fixtures_simproc_sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + fixtures_simproc_sum xs
