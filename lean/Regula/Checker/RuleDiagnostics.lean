import Regula.Findings
import Regula.Checker.Policy

/-! # Rule diagnostic adapters

Checker compatibility adapters for the public diagnostic constructors. -/
namespace Regula.Checker.RuleDiagnostics
open Lean
abbrev declarationName := Regula.Findings.declarationName
abbrev declarationFinding := Regula.Findings.declarationFinding
abbrev contextFinding := Regula.Findings.contextFinding
abbrev declarationLocation := Regula.Findings.declarationLocation

/-- The diagnostic of one execution failure kind, typed by `Policy.executionRule` of that
kind, so its rule is the registry bridge's by construction. -/
def executionDiagnostic : (kind : RegulaPolicy.ExecutionFailureKind) → ExecutionArguments →
    Location → EvidenceMode → Policy.ExecutionClaim → Except String (Diagnostic (Policy.executionRule kind))
  | .executionUnresolved, a, location, mode, claim =>
      makeDiagnostic .executionUnresolved a location mode (some claim.toString) .incomplete
  | .executionBoundary, a, location, mode, claim =>
      makeDiagnostic .executionBoundary a location mode (some claim.toString) .violation

def executionFinding (failure : Policy.ExecutionFailure) (location : Location)
    (mode : EvidenceMode) (claim : Policy.ExecutionClaim) : Except String Finding := do
  let name := failure.root.name
  unless name != .anonymous do throw "anonymous execution root identity"
  return ⟨Policy.executionRule failure.id,
    ← executionDiagnostic failure.id ⟨name, failure.detail⟩ location mode claim⟩

end Regula.Checker.RuleDiagnostics
