module

public import Regula.Diagnostic

/-! # Diagnostic finding adapters

Import-safe adapters to the canonical diagnostic schema. Policy decisions
remain in the policy core; these functions preserve identity, mode and location. -/

public section

namespace Regula.Findings
open Lean

/-- New diagnostic identity is recovered from the original structural Name only. -/
def declarationName (decl : RegulaPolicy.Declaration) : Except String Name := do
  unless decl.name != .anonymous do throw "anonymous declaration identity"
  return decl.name

def declarationFinding (id : RuleId) (name : Name) (detail : String)
    (location : Location) (mode : EvidenceMode) (claim : Option String) : Except String Finding :=
  let a : DeclarationArguments := ⟨name, detail⟩
  match id with
  | .projectAxiom => (fun d => ⟨.projectAxiom, d⟩) <$> makeDiagnostic .projectAxiom a location mode claim .violation
  | .proofHole => (fun d => ⟨.proofHole, d⟩) <$> makeDiagnostic .proofHole a location mode claim .violation
  | .unknownAxiom => (fun d => ⟨.unknownAxiom, d⟩) <$> makeDiagnostic .unknownAxiom a location mode claim .violation
  | .compilerTrusting => (fun d => ⟨.compilerTrusting, d⟩) <$> makeDiagnostic .compilerTrusting a location mode claim .violation
  | .profileExceeded => (fun d => ⟨.profileExceeded, d⟩) <$> makeDiagnostic .profileExceeded a location mode claim .violation
  | .escapeHatch => (fun d => ⟨.escapeHatch, d⟩) <$> makeDiagnostic .escapeHatch a location mode claim .violation
  | .executableContract => (fun d => ⟨.executableContract, d⟩) <$> makeDiagnostic .executableContract a location mode claim .violation
  | .materialDocumentation => (fun d => ⟨.materialDocumentation, d⟩) <$> makeDiagnostic .materialDocumentation a location mode claim .violation
  | .materialIntent => (fun d => ⟨.materialIntent, d⟩) <$> makeDiagnostic .materialIntent a location mode claim .violation
  | _ => .error s!"rule {id} is not a declaration policy diagnostic"

/-- Known context conditions keep their ID; unknown conditions remain incomplete. -/
def contextFinding (id : RuleId) (subject detail : String) (mode : EvidenceMode)
    (impact : Impact) : Except String Finding :=
  let a : ContextArguments := ⟨subject, detail⟩
  let location := Location.project subject
  match id with
  | .environment => (fun d => ⟨.environment, d⟩) <$> makeDiagnostic .environment a location mode none impact
  | .configuration => (fun d => ⟨.configuration, d⟩) <$> makeDiagnostic .configuration a location mode none impact
  | .sourceBuild => (fun d => ⟨.sourceBuild, d⟩) <$> makeDiagnostic .sourceBuild a location mode none impact
  | .coverage => (fun d => ⟨.coverage, d⟩) <$> makeDiagnostic .coverage a location mode none impact
  | .admission => (fun d => ⟨.admission, d⟩) <$> makeDiagnostic .admission a location mode none impact
  | .fenceStructure => (fun d => ⟨.fenceStructure, d⟩) <$> makeDiagnostic .fenceStructure a location mode none impact
  | .positiveExample => (fun d => ⟨.positiveExample, d⟩) <$> makeDiagnostic .positiveExample a location mode none impact
  | .negativeExample => (fun d => ⟨.negativeExample, d⟩) <$> makeDiagnostic .negativeExample a location mode none impact
  | .trustedExample => (fun d => ⟨.trustedExample, d⟩) <$> makeDiagnostic .trustedExample a location mode none impact
  | _ => .error s!"rule {id} requires another argument domain"

/-- A missing range has honest module attribution. A bad supplied range is an error. -/
def declarationLocation (decl : RegulaPolicy.Declaration) (snapshot : Option SourceSnapshot) :
    Except String Location := do
  match decl.ranges, snapshot with
  | some ranges, some source => return .source (← sourceFromReport source ranges)
  | _, _ => return .module decl.module

end Regula.Findings
