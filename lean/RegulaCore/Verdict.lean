/-! # The verdict of Regula's checker

The three verdicts of a run of `lake lint` (the specification's `gateRecord`) and the exit code of
each, which the checker sets (`Regula.Shell.report`) and the agent guide and the rule reference
state (`Verdict.exitCodes`). -/

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

/-- Each verdict once. -/
def Verdict.all : List Verdict := [.pass, .fail, .incomplete]

theorem Verdict.mem_all (v : Verdict) : v ∈ Verdict.all := by cases v <;> decide

/-- The exit code of `lake lint` for each verdict. -/
def Verdict.exitCode : Verdict → UInt32
  | .pass => 0
  | .fail => 1
  | .incomplete => 2

/-- Distinct verdicts have distinct exit codes. -/
theorem Verdict.exitCode_injective : Function.Injective Verdict.exitCode := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The word of each verdict, which the last line of a run prints. -/
def Verdict.label : Verdict → String
  | .pass => "pass"
  | .fail => "fail"
  | .incomplete => "incomplete"

/-- The exit codes of `lake lint`, each with its verdict, in `Verdict.all` order. -/
def Verdict.exitCodes : String :=
  ", ".intercalate (Verdict.all.map fun v => s!"`{v.exitCode}` {v.label}")

/-- The form of the line that `lake lint` prints for one finding (`Regula.Shell.line`): the rule,
the constant, its module when it is not the constant itself, what is wrong, and the rule's page. -/
def findingForm : String :=
  "RGxxxx <constant> (module <module>): <what is wrong> <rule page>"

/-- The form of the line that `lake lint` prints for an incomplete run (`Regula.Shell.report`),
which is how it reports RG2001: the verdict, the rule's page and the reason. -/
def incompleteForm : String :=
  "regula: incomplete (<rule page>): <reason>"

end Regula.Closed
