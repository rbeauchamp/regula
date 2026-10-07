module

public import Regula.Collect
public import Regula.Findings
public import RegulaCore.EditorPolicy

/-! # Local declaration rule decisions

Local declaration decisions run the claimed `RegulaCore.EditorPolicy` registrations
(`checked_editorRequest`, `checked_editorDecision`); `RegulaCore.Policy` proves they select the
project's request and `ruleForMember` rule for the same member (`editor_request_sound`,
`editor_decision_rule`). Deferred role observations are explicit; a snapshot result is never
whole-project acceptance. -/

public section

namespace Regula.Linter.Rules
open Lean
open RegulaPolicy

/-- Feedback contains actual findings and names that still need fresh evidence.
No accepted/project-PASS constructor exists at this scope. -/
structure SnapshotResult where
  /-- The rule findings the selected declarations already have. -/
  findings : Array Finding := #[]
  /-- Declarations whose decision needs fresh evidence that a local snapshot cannot supply. -/
  pending : Array Name := #[]

/-- The editor's optional foundation request never supplies Lake surface authority. -/
def request (value : String) : Except String InspectionRequest :=
  match editorRequest value with
  | some inspection => .ok inspection
  | none => .error s!"unsupported local foundation request: {value}"

/-- Assess the selected records, retaining original structural identities/ranges.
This runs no native replay, external process, project build or global role scan. -/
def declarations (observed : Compiler.LegacyCompilerTrust)
    (ds : Array RegulaPolicy.Declaration) (source : SourceSnapshot)
    (inspection : InspectionRequest) : Except String SnapshotResult := do
  let compiler ← Compiler.admitCapability observed
  let inventory ← admitInventory compiler ds #[]
  let roles := authorize inventory
  let claim := match inspection with
    | .conforming p => some p.spelling
    | .classification => none
    | .teaching => some "compiler-trusting"
  let mut result : SnapshotResult := {}
  -- `admitInventory_exact` retains `ds`; iterating the inventory supplies membership.
  for h : d in inventory.declarations do
    match editorDecision inventory roles d h inspection with
    | none => pure ()
    | some .pending => result := { result with pending := result.pending.push d.name }
    | some (.rule id) =>
        let location ← Findings.declarationLocation d (some source)
        let finding ← Findings.declarationFinding id d.name
          (Findings.ruleDetail id d) location .editorSnapshot claim
        result := { result with findings := result.findings.push finding }
  return result

end Regula.Linter.Rules
