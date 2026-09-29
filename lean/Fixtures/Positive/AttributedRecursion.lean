import Lean

/-
Positive control (issue #125): a structurally recursive definition carrying
the built-in `simp` attribute, whose application Lean records under the
attribute implementation's reference. The mutations `SimpHandlerReplacement`
and `SelfRestoringSimpHandler` each add one fault to this control.
-/
open Lean

@[simp] def fixtures_attr_sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + fixtures_attr_sum xs
