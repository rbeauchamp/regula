import Regula.Checker.Frontend
import RegulaCore.Policy

/-! # Operational policy adapter

Operational adapter over the claimed `RegulaCore.Policy` projections: it binds
scope admission to the frontend's source-coordinate check and renders policy results
as text. This file defines `admitScope` (running `checked_scope`), `executionSummary` (running
`RegulaPolicy.checked_summary`), `toolchainBase` (running `RegulaPolicy.checked_toolchainBase`)
and the unproved renderers `describeBoundaryAs`, `describeBoundary`, `describeToolchainBoundary`,
`executionAccountLines`, `toolchainBaseLines`, `toolchainBaseJson`, `classify`, `classifyMember`
and `subjectDetail`; `executionFindings` is the claimed findings of the decision itself. The
rules, member labels and `executionFailures` in this namespace are defined in claimed
`RegulaCore.Policy`. -/

namespace Regula.Checker.Policy

open Lean (Name)
open Regula.Report
open RegulaPolicy (FoundationClass)

/-- The execution claim of a surface or single-file audit, `report` or `checked`
(`RegulaPolicy.ExecutionClaim`). -/
abbrev ExecutionClaim := RegulaPolicy.ExecutionClaim
/-- The execution claim `s` spells, if any (`RegulaPolicy.ExecutionClaim.parse?`). -/
abbrev ExecutionClaim.parse? (s : String) : Option ExecutionClaim :=
    RegulaPolicy.ExecutionClaim.parse? s
/-- The text of an execution claim, `report` or `checked`
(`RegulaPolicy.ExecutionClaim.spelling`). -/
abbrev ExecutionClaim.toString (x : ExecutionClaim) : String :=
    RegulaPolicy.ExecutionClaim.spelling x

/-- Admit the scope through `checked_scope` with the frontend's coordinate check, itself
`checked_coordinates.run`. `ScopeContract`, instantiated at `Frontend.validateCoordinates`,
is its exact relation, and `CoordinateContract` that check's. Transcript bytes are not
authenticated. -/
def admitScope (observed : RegulaPolicy.Compiler.LegacyCompilerTrust)
    (ds : Array Declaration) (ts : Array Frontend.Transcript := #[]) :
    Except String PolicyScope := do
  let compiler ← RegulaPolicy.Compiler.admitCapability observed
  checked_scope.run compiler Frontend.validateCoordinates ds ts

/-- Whether a declaration with these fields could receive a generated-role exception and so
needs a fresh frontend transcript (`RegulaPolicy.declarationNeedsTranscript`). -/
abbrev declarationNeedsTranscript := RegulaPolicy.declarationNeedsTranscript
/-- Whether any of the declarations needs a fresh frontend transcript
(`RegulaPolicy.needsFrontendTranscript`). -/
abbrev needsFrontendTranscript := RegulaPolicy.needsFrontendTranscript

/-- Execution roots admitted with a proof of their structural validity
(`RegulaPolicy.ExecutionInventory`). -/
abbrev ExecutionInventory := RegulaPolicy.ExecutionInventory
/-- Admit execution roots unchanged when they are structurally valid, and refuse them
otherwise (`RegulaPolicy.admitExecution`). -/
abbrev admitExecution := RegulaPolicy.admitExecution
/-- One execution-claim failure: its rule, root and detail (`RegulaPolicy.ExecutionFailure`). -/
abbrev ExecutionFailure := RegulaPolicy.ExecutionFailure

/-- The findings the gate reports: the decision's records
(`RegulaPolicy.executionFailureRecords`) with each folded boundary's record (a later record of a
trusted boundary, or a `partial` implementation) reported in the finding of the boundary it is
reported with (`RegulaPolicy.executionFindings`). Kind, root and order are the records' own,
preserved by identity rather than by a second record type. -/
abbrev executionFindings := RegulaPolicy.executionFindings

/-- One-line rendering of a single execution boundary, introduced by `label`. -/
def describeBoundaryAs (label : String) (boundary : Regula.Report.ExecutionBoundary) : String :=
  let replacement := boundary.replacement.map (fun value => s!" replacement={value}") |>.getD ""
  let evidence := boundary.evidence.map (fun value => s!" evidence={value}") |>.getD ""
  let owned := if boundary.owned then " owned" else ""
  let callers := if boundary.compilerCallers.isEmpty then "" else
    s!" compiler-callers={boundary.compilerCallers}"
  s!"{label} {boundary.name} [{boundary.boundary}] " ++
    s!"correspondence={boundary.correspondence}{replacement}{evidence}{owned}{callers} " ++
    s!"(module {boundary.«module»})"

/-- One-line rendering of a single execution boundary. -/
def describeBoundary (boundary : Regula.Report.ExecutionBoundary) : String :=
  describeBoundaryAs "boundary" boundary

/-- The toolchain trusted base of an audit's labeled execution accounts: each toolchain-owned
boundary once, with every environment and root that reaches it, through
`RegulaPolicy.checked_toolchainBase`. -/
def toolchainBase (environments : Array (String × ExecutionInventory)) :
    Array RegulaPolicy.ToolchainBoundary :=
  RegulaPolicy.checked_toolchainBase.run environments

/-- An entry's reaches grouped by environment, in their sorted order: each environment's label
with the roots in it that reach the entry. -/
private def reachGroups (entry : RegulaPolicy.ToolchainBoundary) : Array (String × Array Name) :=
  entry.reachedBy.foldl (init := #[]) fun groups (label, root) =>
    match groups.back? with
    | some (last, roots) =>
        if last == label then groups.pop.push (last, roots.push root)
        else groups.push (label, #[root])
    | none => groups.push (label, #[root])

/-- One-line rendering of one toolchain trusted-base entry: always trusted, attributed to the
toolchain, with the environments and roots that reach it. -/
def describeToolchainBoundary (entry : RegulaPolicy.ToolchainBoundary) : String :=
  let replacement := entry.replacement.map (fun value => s!" replacement={value}") |>.getD ""
  let reached := (reachGroups entry).toList.map fun (label, roots) =>
    s!"{label}: {", ".intercalate (roots.toList.map toString)}"
  s!"boundary {entry.name} [{entry.boundary}] correspondence=trusted{replacement} toolchain " ++
    s!"(module {entry.module}) reached-by={"; ".intercalate reached}"

/-- The JSON form of one toolchain trusted-base entry, with its admitted origin and the
environments and roots that reach it. -/
def toolchainBoundaryJson (entry : RegulaPolicy.ToolchainBoundary) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.toJson entry.name), ("module", Lean.toJson entry.module),
    ("boundary", Lean.toJson entry.boundary), ("replacement", Lean.toJson entry.replacement),
    ("toolchainOrigin", Lean.toJson entry.origin),
    ("reachedBy", Lean.Json.arr <| (reachGroups entry).map fun (label, roots) =>
      Lean.Json.mkObj [("environment", Lean.toJson label), ("roots", Lean.toJson roots)])]

/-- A toolchain trusted base (`toolchainBase`) as JSON, in its order. -/
def toolchainBaseJson (base : Array RegulaPolicy.ToolchainBoundary) : Lean.Json :=
  Lean.Json.arr (base.map toolchainBoundaryJson)

/-- The text lines of one execution account: each root with a boundary the toolchain does not
own or an unresolved path, listing those boundaries and paths. A folded boundary
(`RegulaPolicy.ExecutionRoot.folded`) is not listed as a boundary of its own: a later record of
a trusted boundary is listed under the first record as `restated`, and a `partial` implementation
under each boundary that carries it as its `implementation`. Toolchain-owned boundaries are
listed by `toolchainBaseLines` instead. -/
def executionAccountLines (inventory : ExecutionInventory) : Array String := Id.run do
  let mut lines : Array String := #[]
  for root in inventory.roots do
    let reported := root.reported.filter (·.toolchainOrigin?.isNone)
    if !reported.isEmpty || !root.unresolved.isEmpty then
      lines := lines.push s!"  execution root {root.name}"
      for boundary in reported do
        lines := lines.push s!"    {describeBoundary boundary}"
        for restated in root.restatements boundary do
          lines := lines.push s!"      {describeBoundaryAs "restated" restated}"
        for implementation in root.implementations boundary do
          lines := lines.push s!"      {describeBoundaryAs "implementation" implementation}"
      for item in root.unresolved do
        lines := lines.push s!"    unresolved {item}"
  return lines

/-- The text lines of a toolchain trusted base (`toolchainBase`): its size, then, when `listed`,
each entry once with the environments and roots that reach it. Otherwise the size line alone
names where the entries are listed. -/
def toolchainBaseLines (base : Array RegulaPolicy.ToolchainBoundary) (listed : Bool) :
    Array String :=
  if listed then
    #[s!"toolchain trusted base: {base.size} boundary(ies), each listed once:"] ++
      base.map fun entry => s!"  {describeToolchainBoundary entry}"
  else
    #[s!"toolchain trusted base: {base.size} boundary(ies) (listed once each with --verbose \
      and in --json-out)"]

/-- Execution-coverage counts, through `RegulaPolicy.checked_summary`. -/
def executionSummary (inventory : ExecutionInventory) : RegulaPolicy.ExecutionSummary :=
  RegulaPolicy.checked_summary.run inventory

private def classifyWith (decl : Declaration) (foundation : String) : String :=
  let flags := Id.run do
    let mut values : Array String := #[]
    if decl.kind == .«axiom» then values := values.push "AXIOM"
    if decl.isProp then values := values.push "Prop"
    if decl.«instance» then values := values.push "instance"
    if decl.«noncomputable» then values := values.push "noncomputable"
    if decl.isUnsafe then values := values.push "unsafe"
    if decl.isPartial then values := values.push "partial"
    if let some implementation := decl.implementedBy then
      values := values.push s!"implemented_by={implementation}"
    if decl.«extern» then values := values.push "extern"
    values
  let roles := Id.run do
    let mut values : Array String := #[]
    if decl.internal then values := values.push "internal"
    if decl.«private» then values := values.push "private"
    if decl.projection then values := values.push "projection"
    if decl.matcher then values := values.push "matcher"
    if let some base := decl.unsafeRecBase then values := values.push s!"unsafe-rec-for={base}"
    values
  let flagText := if flags.isEmpty then "" else s!" [{", ".intercalate flags.toList}]"
  let roleText := if roles.isEmpty then "" else s!" roles={repr roles.toList}"
  let contractText := decl.executableContract.map (fun contract =>
    s!" executable-contract={contract.root}" ++
      (contract.kind.map (s!" decision-kind={·.spelling}")).getD "" ++
      s!" requires={contract.requirement}" ++
      (contract.failure.map (s!" failure={·}")).getD "") |>.getD ""
  s!"{decl.name} ({decl.kind}){flagText}{roleText} type={decl.prettyType} " ++
    s!"axioms={repr (decl.axioms.toList.map (·.toString))} -> {foundation}{contractText}"

/-- One-line text of a declaration for `--verbose` output: its name, kind, flags, roles,
type, axioms and foundation label, or `invalid-inventory` when the scope has no label for it. -/
def classify (decl : Declaration) (scope : PolicyScope) : String :=
  classifyWith decl ((labelOf decl scope).toOption.map (·.spelling) |>.getD "invalid-inventory")

/-- `classify` for a member, without the inventory scan or the unreachable fallback. -/
def classifyMember (decl : Declaration) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) : String :=
  classifyWith decl (labelOfMember decl scope member).spelling

/-- Finding detail for a member: `classifyMember`'s text, or, when the finding names the member's
partial parent (`subject`), that parent's text followed by the member's, the helper Lean runs in
the parent's place. -/
def subjectDetail (decl : Declaration) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) : String :=
  let named := subject decl scope member
  if named.name == decl.name then classifyMember decl scope member
  else s!"{classify named scope} is a `partial` definition; Lean runs its generated helper \
    {classifyMember decl scope member}"

theorem classifyMember_eq (decl : Declaration) (scope : PolicyScope)
    (member : decl ∈ scope.inventory.declarations) :
    classifyMember decl scope member = classify decl scope := by
  simp [classifyMember, classify, labelOf_member decl scope member, Except.toOption]

end Regula.Checker.Policy
