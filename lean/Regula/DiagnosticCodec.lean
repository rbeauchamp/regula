import Regula.RegistryCodec

/-! # Fail-closed diagnostic transport

Fail-closed diagnostic transport. Decode to the indexed domain, then compare with
canonical re-encoding to reject unknown fields and redundant-coordinate disagreement.
Payloads are indexed by the registry's closed `RuleId` (design credit in Regula.RuleId). -/
namespace Regula.DiagnosticCodec
open Lean RegistryCodec

private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
private def string (j : Json) (k : String) : Except String String := do
  (← field j k).getStr?
private def nat (j : Json) (k : String) : Except String Nat := do
  (← field j k).getNat?

private def byteRange (j : Json) : Except String ByteRange := do
  return ⟨← nat j "startByte", ← nat j "endByte"⟩

/-- Decode a module, project or source location; a source location's coordinates must pass
`admitSource`, and the input must equal the canonical `locationJson` of the result. -/
def parseLocation (j : Json) : Except String Location := do
  let value ← match ← string j "kind" with
    | "module" => pure <| Location.module (← parseName (← field j "name"))
    | "project" => pure <| Location.project (← string j "identity")
    | "source" => do
        let c : SourceCandidate := {
          snapshot := ⟨← string j "uri", ← string j "source"⟩
          full := ← byteRange (← field j "range")
          selection := ← byteRange (← field j "selectionRange") }
        pure <| Location.source (← admitSource c)
    | _ => throw "unknown location kind"
  unless j == locationJson value do throw "noncanonical location or unknown fields"
  return value

private def parseArguments (id : RuleId) (j : Json) : Except String (Payload id) := do
  let detail ← string j "detail"
  match (dependent := true) id with
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .materialDocumentation | .materialIntent =>
      return ⟨← parseName (← field j "declaration"), detail⟩
  | .executionUnresolved | .executionBoundary =>
      return ⟨← parseName (← field j "root"), detail⟩
  | .environment | .configuration | .sourceBuild | .coverage | .admission | .communityConfiguration
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample
  | .moduleDocumentation => return ⟨← string j "subject", detail⟩

/-- Decode one finding: its rule, payload, location, mode, claim, impact, severity and related
locations, built through `makeDiagnostic`; the input must equal the canonical `diagnosticJson`
of the result, so unknown fields and inconsistent coordinates are refused. -/
def parseDiagnostic (j : Json) : Except String Finding := do
  let id ← parseRule (← field j "id")
  let arguments ← parseArguments id (← field j "arguments")
  let location ← parseLocation (← field j "location")
  let mode ← parseMode (← string j "mode")
  let claim ← match ← field j "claim" with
    | .null => pure none
    | .str s => pure (some s)
    | _ => throw "invalid claim"
  let impact ← match ← string j "impact" with
    | "violation" => pure Impact.violation | "incomplete" => pure Impact.incomplete
    | _ => throw "unknown strict impact"
  let severity ← match ← string j "severity" with
    | "error" => pure Severity.error | "warning" => pure Severity.warning
    | "information" => pure Severity.information | _ => throw "unknown display severity"
  let related ← (← (← field j "related").getArr?).mapM fun r => do
    let relation ← string r "relation"
    let location ← parseLocation (← field r "location")
    return ({ relation, location } : RelatedLocation)
  let d ← makeDiagnostic id arguments location mode claim impact severity related
  let f : Finding := ⟨id, d⟩
  unless j == diagnosticJson f do throw "noncanonical diagnostic or unknown fields"
  return f
end Regula.DiagnosticCodec
