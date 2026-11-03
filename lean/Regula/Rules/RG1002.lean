module

public import Regula.Rule

/-!
# RG1002: proof holes

A constant of a claimed module depends on `sorryAx`. `specification/RegulaSpecification/Rules/RG1002.lean`
states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1002

open Regula.Closed

/-- The constants of claimed modules that depend on `sorryAx`. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if (t.axiomSet d.name).contains ``sorryAx then
      some (violation d "depends on sorryAx")
    else none

/-- RG1002, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1002", check := check }

end Regula.Rules.RG1002
