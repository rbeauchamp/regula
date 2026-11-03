module

public import Regula.Rule

/-!
# RG1003: unknown axioms

A constant of a claimed module depends on an axiom that is not known, and that RG1002 and RG1004 do
not name. `specification/RegulaSpecification/Rules/RG1003.lean` states the rule and proves this check
against it.
-/

public section

namespace Regula.Rules.RG1003

open Regula.Closed

/-- The constants of claimed modules that depend on an axiom that is not known, and that RG1002 and
RG1004 do not name. -/
def check {i : Input} (t : Tables i) : List Violation :=
  t.claimed.filterMap fun d =>
    let unknown := (t.axiomSet d.name).filter fun a =>
      !t.known a && a != ``sorryAx && !nativeProofAxiom a && !compilerAxioms.contains a
    if !unknown.isEmpty then
      some (violation d s!"depends on the unknown axioms {unknown}")
    else none

/-- RG1003, for the registry. Its body is exposed so that the registry reads its spelling (`Regula.Closed.spellings_nodup`). -/
@[expose] def rule : Rule := { spelling := "RG1003", check := check }

end Regula.Rules.RG1003
