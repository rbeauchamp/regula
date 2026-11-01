/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

/-!
# The verdict

The three verdicts of a run of the checker, and the exit code and the word of each.
-/

public section

namespace Regula.Closed

/-- The verdict of a run. -/
inductive Verdict where
  /-- The input has the closed form, and no rule reports a subject. -/
  | pass
  /-- A rule reports a subject. -/
  | fail
  /-- The build could not be loaded, or the input does not have the closed form. -/
  | incomplete
  deriving DecidableEq, Repr

/-- The exit code of each verdict. -/
def Verdict.exitCode : Verdict → UInt32
  | .pass => 0
  | .fail => 1
  | .incomplete => 2

/-- Distinct verdicts have distinct exit codes. -/
theorem Verdict.exitCode_injective : Function.Injective Verdict.exitCode := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Only a pass exits with 0. -/
theorem Verdict.exitCode_eq_zero_iff (v : Verdict) : v.exitCode = 0 ↔ v = .pass := by
  cases v <;> decide

/-- The one Lean release that this revision of Regula reads, by its version and commit. The rules read a name
form and a recursion helper's form that this release gives. -/
def pinnedLean : String × String :=
  ("4.35.0", "eb6cafb7290e8bd5f2937522d8d804f58f02bafc")

/-- The word of each verdict, which the last line of a run prints. -/
def Verdict.label : Verdict → String
  | .pass => "pass"
  | .fail => "fail"
  | .incomplete => "incomplete"

/-- Distinct verdicts have distinct words. -/
theorem Verdict.label_injective : Function.Injective Verdict.label := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The last line of a run with the proof verdict `v`: a function of the verdict alone. -/
def Verdict.proofLine : Verdict → String
  | .pass => "regula: proof verdict: pass, which says nothing about what ran during the build"
  | .fail => "regula: proof verdict: fail"
  | .incomplete => "regula: proof verdict: incomplete (RG2001)"

end Regula.Closed
