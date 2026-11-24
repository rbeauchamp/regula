module

public section

namespace Regula.Closed

inductive Verdict where
  | pass
  | fail
  | incomplete
  deriving DecidableEq, Repr

def Verdict.exitCode : Verdict → UInt32
  | .pass => 0
  | .fail => 1
  | .incomplete => 2

theorem Verdict.exitCode_injective : Function.Injective Verdict.exitCode := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem Verdict.exitCode_eq_zero_iff (v : Verdict) : v.exitCode = 0 ↔ v = .pass := by
  cases v <;> decide

def pinnedLean : String × String :=
  ("4.36.0", "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9")

def Verdict.label : Verdict → String
  | .pass => "pass"
  | .fail => "fail"
  | .incomplete => "incomplete"

theorem Verdict.label_injective : Function.Injective Verdict.label := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def Verdict.proofLine : Verdict → String
  | .pass => "regula: proof verdict: pass, which says nothing about what ran during the build"
  | .fail => "regula: proof verdict: fail"
  | .incomplete => "regula: proof verdict: incomplete (RG2001)"

def detailText (text : String) : String :=
  String.ofList (text.toList.flatMap fun c =>
    if c == '\n' then ['\\', 'n'] else if c == '\r' then ['\\', 'r'] else [c])

def Verdict.proofLineOn (subject : String) : Verdict → String
  | .pass => Verdict.pass.proofLine ++ ", on " ++ detailText subject
  | v => v.proofLine

end Regula.Closed
