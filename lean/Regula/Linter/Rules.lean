module

public import Regula.Collect
public import Regula.Findings
public import RegulaCore.EditorPolicy

/-! Local declaration decisions run the claimed `RegulaCore.EditorPolicy` registrations
(`checkedEditorRequest`, `checkedEditorDecision`); `RegulaCore.Policy` proves they select the
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
  findings : Array Finding := #[]
  pending : Array Name := #[]

/-- The editor's optional foundation request never supplies Lake surface authority. -/
def request (value : String) : Except String InspectionRequest :=
  match editorRequest value with
  | some inspection => .ok inspection
  | none => .error s!"unsupported local foundation request: {value}"

/-- Assess the selected records, retaining original structural identities/ranges.
This runs no native replay, external process, project build or global role scan. -/
def declarations (ds : Array RegulaPolicy.Declaration) (source : SourceSnapshot)
    (inspection : InspectionRequest) : Except String SnapshotResult := do
  let inventory ← admitInventory ds #[]
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
          (descriptor id).applicability location .editorSnapshot claim
        result := { result with findings := result.findings.push finding }
  return result

end Regula.Linter.Rules
