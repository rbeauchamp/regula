module

public import Regula.Rule

public section

namespace Regula.Rules.RG1002

open Regula.Closed

def fixGuidance : Guidance :=
  { text := "complete the proof or remove the unfinished declaration rather than leaving sorry or admit; \
      if inherited from a dependency, complete that declaration first"
    nonblank := by simp [Char.isWhitespace] }

def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if (t.axiomSet d.name).contains ``sorryAx then
      some (violation d "depends on sorryAx" fixGuidance)
    else none

@[expose] def rule : Rule := { spelling := "RG1002", check := check }

end Regula.Rules.RG1002
