module

public import Regula.Rule

/-!
# RG1005: the profile

A constant of a claimed module depends on an axiom that the project's profile does not admit.
`specification/RegulaSpecification/Rules/RG1005.lean` states the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1005

open Regula.Closed

/-- The constants of claimed modules that depend on an axiom that the project's profile does not
admit. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let excess := (t.axiomSet d.name).filter (!t.admits i.profile ·)
    if !excess.isEmpty then
      some (violation d s!"depends on {excess}, outside the profile")
    else none

/-- RG1005, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1005", check := check }

end Regula.Rules.RG1005
