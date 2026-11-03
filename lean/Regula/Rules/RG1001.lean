module

public import Regula.Rule

/-!
# RG1001: project axioms

A constant of a claimed module is an axiom. `specification/RegulaSpecification/Rules/RG1001.lean` states
the rule and proves this check against it.
-/

public section

namespace Regula.Rules.RG1001

open Regula.Closed

/-- The constants of claimed modules that are axioms. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    if d.kind == .axiom then some (violation d "declares an axiom") else none

/-- RG1001, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1001", check := check }

end Regula.Rules.RG1001
