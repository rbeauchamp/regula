import Regula.Findings
import Regula.Checker.Policy

/-! # Rule diagnostic adapters

Checker compatibility adapters for the public diagnostic constructors. -/
namespace Regula.Checker.RuleDiagnostics
open Lean
/-- The structural name of a declaration, refusing an anonymous one
(`Regula.Findings.declarationName`). -/
abbrev declarationName := Regula.Findings.declarationName
/-- The violation finding of a declaration-scoped rule (`Regula.Findings.declarationFinding`). -/
abbrev declarationFinding := Regula.Findings.declarationFinding
/-- A project-scoped finding of a context rule (`Regula.Findings.contextFinding`). -/
abbrev contextFinding := Regula.Findings.contextFinding
/-- The source location of a declaration's ranges in a snapshot, or its module when either is
missing (`Regula.Findings.declarationLocation`). -/
abbrev declarationLocation := Regula.Findings.declarationLocation

/-- The diagnostic of one execution failure kind, typed by `Policy.executionRule` of that
kind, so its rule is the registry bridge's by construction. -/
def executionDiagnostic : (kind : RegulaPolicy.ExecutionFailureKind) → ExecutionArguments →
    Location → EvidenceMode → Policy.ExecutionClaim → Except String
        (Diagnostic (Policy.executionRule kind))
  | .executionUnresolved, a, location, mode, claim =>
      makeDiagnostic .executionUnresolved a location mode (some claim.toString) .incomplete
  | .executionBoundary, a, location, mode, claim =>
      makeDiagnostic .executionBoundary a location mode (some claim.toString) .violation

/-- The finding of one execution failure at `location`: the diagnostic of its kind's rule, with
the failure's root and detail; an anonymous root is refused. -/
def executionFinding (failure : Policy.ExecutionFailure) (location : Location)
    (mode : EvidenceMode) (claim : Policy.ExecutionClaim) : Except String Finding := do
  let name := failure.root.name
  unless name != .anonymous do throw "anonymous execution root identity"
  return ⟨Policy.executionRule failure.id,
    ← executionDiagnostic failure.id ⟨name, failure.detail⟩ location mode claim⟩

end Regula.Checker.RuleDiagnostics
