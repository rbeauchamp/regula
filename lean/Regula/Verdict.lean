/-!
# The verdict

The three verdicts of a run of the checker, and the exit code of each.
-/

namespace Regula.Closed

/-- The verdict of a run. -/
inductive Verdict where
  /-- The input has the closed form, and no rule reports a subject. -/
  | pass
  /-- A rule reports a subject. -/
  | fail
  /-- The build could not be loaded, or the input does not have the closed form. -/
  | incomplete
  deriving DecidableEq, Repr, Inhabited

/-- The exit code of each verdict. -/
def Verdict.exitCode : Verdict → UInt32
  | .pass => 0
  | .fail => 1
  | .incomplete => 2

/-- Only a pass exits with 0. -/
theorem Verdict.exitCode_eq_zero_iff (v : Verdict) : v.exitCode = 0 ↔ v = .pass := by
  cases v <;> decide

/-- The word of each verdict, which the last line of a run prints. -/
def Verdict.label : Verdict → String
  | .pass => "pass"
  | .fail => "fail"
  | .incomplete => "incomplete"

end Regula.Closed
