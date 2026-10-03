import RegulaPolicy.Domain
import Lean.Data.Json
import Regula.Checker.PolicyCodec
import Regula.StructuralName

/-! # Policy observation JSON instances

Operational JSON instances for policy observations. Finite tags are validated
by the pure codecs. This module remains checker infrastructure. -/
namespace Regula.Report
open Lean RegulaPolicy
open Regula.Checker.PolicyCodec (exactFields)

/-- A name as Lean prints it, or its structural components where Lean's parser would not read
that text back (`RegistryCodec.printedNameJson`), in producer reports and the result documents
that render them. -/
scoped instance : ToJson Name := ⟨Regula.RegistryCodec.printedNameJson⟩
/-- Read a name `RegistryCodec.printedNameJson` wrote (`printedNameJson_roundtrip`). -/
scoped instance : FromJson Name := ⟨Regula.RegistryCodec.parsePrintedNameJson⟩
open scoped Regula.Report

instance : ToJson Compiler.LegacyCompilerTrust := ⟨fun x => .str x.spelling⟩
instance : FromJson Compiler.LegacyCompilerTrust := ⟨fun j => do
  let s ← j.getStr?
  match Compiler.LegacyCompilerTrust.parse? s with
  | some x => return x
  | none => throw "unknown legacy compiler capability"⟩

instance : ToJson DeclarationKind := ⟨fun x => .str x.spelling⟩
instance : FromJson DeclarationKind := ⟨fun j => do
  let s ← j.getStr?
  match DeclarationKind.parse? s with
  | some x => return x
  | none => throw "unknown DeclarationKind"⟩

instance : ToJson BoundaryKind := ⟨fun x => .str x.spelling⟩
instance : FromJson BoundaryKind := ⟨fun j => do
  let s ← j.getStr?
  match BoundaryKind.parse? s with
  | some x => return x
  | none => throw "unknown BoundaryKind"⟩

instance : ToJson Correspondence := ⟨fun x => .str x.spelling⟩
instance : FromJson Correspondence := ⟨fun j => do
  let s ← j.getStr?
  match Correspondence.parse? s with
  | some x => return x
  | none => throw "unknown Correspondence"⟩

instance : ToJson FoundationClass := ⟨fun x => .str x.spelling⟩
instance : FromJson FoundationClass := ⟨fun j => do
  let s ← j.getStr?
  match FoundationClass.parse? s with
  | some x => return x
  | none => throw "unknown FoundationClass"⟩

instance : ToJson ConformingProfile := ⟨fun x => .str x.spelling⟩
instance : FromJson ConformingProfile := ⟨fun j => do
  let s ← j.getStr?
  match ConformingProfile.parse? s with
  | some x => return x
  | none => throw "unknown ConformingProfile"⟩

instance : ToJson ExecutionClaim := ⟨fun x => .str x.spelling⟩
instance : FromJson ExecutionClaim := ⟨fun j => do
  let s ← j.getStr?
  match ExecutionClaim.parse? s with
  | some x => return x
  | none => throw "unknown ExecutionClaim"⟩

instance : ToJson EvidenceMode := ⟨fun x => .str x.spelling⟩
instance : FromJson EvidenceMode := ⟨fun j => do
  let s ← j.getStr?
  match EvidenceMode.parse? s with
  | some x => return x
  | none => throw "unknown EvidenceMode"⟩

instance : ToJson Safety := ⟨fun x => .str x.spelling⟩
instance : FromJson Safety := ⟨fun j => do
  let s ← j.getStr?
  match Safety.parse? s with
  | some x => return x
  | none => throw "unknown Safety"⟩

instance : ToJson Reducibility := ⟨fun x => .str x.spelling⟩
instance : FromJson Reducibility := ⟨fun j => do
  let s ← j.getStr?
  match Reducibility.parse? s with
  | some x => return x
  | none => throw "unknown Reducibility"⟩

instance : ToJson RecursionOrigin := ⟨fun x => .str x.spelling⟩
instance : FromJson RecursionOrigin := ⟨fun j => do
  let s ← j.getStr?
  match RecursionOrigin.parse? s with
  | some x => return x
  | none => throw "unknown RecursionOrigin"⟩

instance : ToJson DecisionKind := ⟨fun x => .str x.spelling⟩
instance : FromJson DecisionKind := ⟨fun j => do
  let s ← j.getStr?
  match DecisionKind.parse? s with
  | some x => return x
  | none => throw "unknown DecisionKind"⟩

instance : ToJson EvaluatorRole := ⟨fun x => .str x.spelling⟩
instance : FromJson EvaluatorRole := ⟨fun j => do
  match EvaluatorRole.parse? (← j.getStr?) with
  | some role => return role
  | none => throw "unknown evaluator role"⟩

/-- A source position, line and column (`RegulaPolicy.Position`), with its exact-field JSON
codec. -/
abbrev Position := RegulaPolicy.Position
deriving instance ToJson for RegulaPolicy.Position
instance : FromJson RegulaPolicy.Position := ⟨fun j => do
  exactFields j ["line", "column"]
  return {
    line := ← j.getObjValAs? _ "line"
    column := ← j.getObjValAs? _ "column"
  }⟩

/-- A source range with codepoint and UTF-16 columns (`RegulaPolicy.Range`), with its
exact-field JSON codec. -/
abbrev Range := RegulaPolicy.Range
deriving instance ToJson for RegulaPolicy.Range
instance : FromJson RegulaPolicy.Range := ⟨fun j => do
  exactFields j ["start", "end", "startUtf16", "endUtf16"]
  return {
    start := ← j.getObjValAs? _ "start"
    «end» := ← j.getObjValAs? _ "end"
    startUtf16 := ← j.getObjValAs? _ "startUtf16"
    endUtf16 := ← j.getObjValAs? _ "endUtf16"
  }⟩

/-- The full and selection ranges Lean records for a declaration (`RegulaPolicy.Ranges`),
with its exact-field JSON codec. -/
abbrev Ranges := RegulaPolicy.Ranges
deriving instance ToJson for RegulaPolicy.Ranges
instance : FromJson RegulaPolicy.Ranges := ⟨fun j => do
  exactFields j ["range", "selectionRange"]
  return {
    range := ← j.getObjValAs? _ "range"
    selectionRange := ← j.getObjValAs? _ "selectionRange"
  }⟩

/-- The collector's record of a registered executable contract: its root, rendered
requirement, any refusal and its decision kind, `null` for a requirement that states none
(`RegulaPolicy.ExecutableContract`), with its exact-field JSON codec. -/
abbrev ExecutableContract := RegulaPolicy.ExecutableContract
deriving instance ToJson for RegulaPolicy.ExecutableContract
instance : FromJson RegulaPolicy.ExecutableContract := ⟨fun j => do
  exactFields j ["root", "requirement", "failure", "kind"]
  return {
    root := ← j.getObjValAs? _ "root"
    requirement := ← j.getObjValAs? _ "requirement"
    failure := ← j.getObjValAs? _ "failure"
    kind := ← j.getObjValAs? _ "kind"
  }⟩

/-- The Lean-semantic record of one owned constant (`RegulaPolicy.Declaration`), with its
exact-field JSON codec. The `ranges` member is the pair Lean recorded (`recordedRanges`); the
admitted pair (`RegulaPolicy.Declaration.ranges`) is computed from it and is not transported. -/
abbrev Declaration := RegulaPolicy.Declaration
instance : ToJson RegulaPolicy.Declaration := ⟨fun d => Json.mkObj [
  ("name", toJson d.name), ("module", toJson d.module), ("kind", toJson d.kind),
  ("type", toJson d.type), ("prettyType", toJson d.prettyType), ("isProp", toJson d.isProp),
  ("isUnsafe", toJson d.isUnsafe), ("isPartial", toJson d.isPartial),
  ("safety", toJson d.safety), ("instance", toJson d.instance),
  ("noncomputable", toJson d.noncomputable), ("implementedBy", toJson d.implementedBy),
  ("extern", toJson d.extern), ("internal", toJson d.internal), ("private", toJson d.private),
  ("projection", toJson d.projection), ("matcher", toJson d.matcher),
  ("recursive", toJson d.recursive), ("unsafeRecBase", toJson d.unsafeRecBase),
  ("levelParams", toJson d.levelParams), ("all", toJson d.all), ("hints", toJson d.hints),
  ("valueConstants", toJson d.valueConstants),
  ("unsafeRecRegenerated", toJson d.unsafeRecRegenerated),
  ("constructorIndex", toJson d.constructorIndex),
  ("nativeStatement", toJson d.nativeStatement), ("nativeReplay", toJson d.nativeReplay),
  ("ranges", toJson d.recordedRanges), ("generatedFrom", toJson d.generatedFrom),
  ("axioms", toJson d.axioms), ("executableContract", toJson d.executableContract)]⟩
instance : FromJson RegulaPolicy.Declaration := ⟨fun j => do
  exactFields j ["name", "module", "kind", "type", "prettyType", "isProp", "isUnsafe", "isPartial",
      "safety", "instance", "noncomputable", "implementedBy", "extern", "internal", "private",
          "projection", "matcher", "recursive", "unsafeRecBase", "levelParams", "all", "hints",
              "valueConstants", "unsafeRecRegenerated", "constructorIndex", "nativeStatement", "nativeReplay",
                  "ranges", "generatedFrom", "axioms", "executableContract"]
  return {
    name := ← j.getObjValAs? _ "name"
    «module» := ← j.getObjValAs? _ "module"
    kind := ← j.getObjValAs? _ "kind"
    «type» := ← j.getObjValAs? _ "type"
    prettyType := ← j.getObjValAs? _ "prettyType"
    isProp := ← j.getObjValAs? _ "isProp"
    isUnsafe := ← j.getObjValAs? _ "isUnsafe"
    isPartial := ← j.getObjValAs? _ "isPartial"
    safety := ← j.getObjValAs? _ "safety"
    «instance» := ← j.getObjValAs? _ "instance"
    «noncomputable» := ← j.getObjValAs? _ "noncomputable"
    implementedBy := ← j.getObjValAs? _ "implementedBy"
    «extern» := ← j.getObjValAs? _ "extern"
    internal := ← j.getObjValAs? _ "internal"
    «private» := ← j.getObjValAs? _ "private"
    projection := ← j.getObjValAs? _ "projection"
    matcher := ← j.getObjValAs? _ "matcher"
    recursive := ← j.getObjValAs? _ "recursive"
    unsafeRecBase := ← j.getObjValAs? _ "unsafeRecBase"
    levelParams := ← j.getObjValAs? _ "levelParams"
    all := ← j.getObjValAs? _ "all"
    hints := ← j.getObjValAs? _ "hints"
    valueConstants := ← j.getObjValAs? _ "valueConstants"
    unsafeRecRegenerated := ← j.getObjValAs? _ "unsafeRecRegenerated"
    constructorIndex := ← j.getObjValAs? _ "constructorIndex"
    nativeStatement := ← j.getObjValAs? _ "nativeStatement"
    nativeReplay := ← j.getObjValAs? _ "nativeReplay"
    recordedRanges := ← j.getObjValAs? _ "ranges"
    generatedFrom := ← j.getObjValAs? _ "generatedFrom"
    axioms := ← j.getObjValAs? _ "axioms"
    executableContract := ← j.getObjValAs? _ "executableContract"
  }⟩

/-- One execution boundary a root's closure reaches (`RegulaPolicy.ExecutionBoundary`), with a
JSON codec whose decoder admits the boundary evidence through `admitBoundaryEvidence` and
refuses a noncanonical payload. -/
abbrev ExecutionBoundary := RegulaPolicy.ExecutionBoundary
instance : ToJson RegulaPolicy.ToolchainOrigin := ⟨fun o => Json.mkObj [
  ("module", toJson o.moduleName), ("actual", toJson o.actual), ("expected", toJson o.expected)]⟩
instance : FromJson RegulaPolicy.ToolchainOrigin := ⟨fun j => do
  exactFields j ["module", "actual", "expected"]
  RegulaPolicy.admitToolchainOrigin (← j.getObjValAs? Name "module")
    (← j.getObjValAs? String "actual") (← j.getObjValAs? String "expected")⟩

/- The four objects of a root's account list their members in the order of their keys, as the
result reader builds them (`Regula.SharedExecution`; `Regula.ExecutionShare` proves each codec
builds the reader's object), so an account this codec writes, one the reader rebuilds and one the
JSON parser reads are the same tree. This module is in the probe's import closure, so it does not
import the reader. -/
instance : ToJson ExecutionBoundary := ⟨fun b => Json.mkObj [
  ("boundary", toJson b.boundary), ("compilerCallers", toJson b.compilerCallers),
  ("correspondence", toJson b.correspondence), ("evidence", toJson b.evidence),
  ("module", toJson b.module), ("name", toJson b.name), ("occurrence", toJson b.occurrence),
  ("owned", toJson b.owned), ("replacement", toJson b.replacement),
  ("toolchainOrigin", toJson b.toolchainOrigin?)]⟩
instance : FromJson ExecutionBoundary := ⟨fun j => do
  exactFields j
      ["occurrence", "name", "module", "boundary", "correspondence", "owned", "replacement",
          "evidence", "compilerCallers", "toolchainOrigin"]
  let boundary ← j.getObjValAs? BoundaryKind "boundary"
  let state ← j.getObjValAs? Correspondence "correspondence"
  let detail ← j.getObjValAs? (Option String) "evidence"
  let origin ← j.getObjValAs? (Option ToolchainOrigin) "toolchainOrigin"
  let account ← admitBoundaryEvidence boundary state detail origin
  unless account.detail == detail && account.toolchainOrigin? == origin do
    throw "noncanonical boundary evidence payload"
  return {
    occurrence := ← j.getObjValAs? Nat "occurrence"
    name := ← j.getObjValAs? Name "name", «module» := ← j.getObjValAs? Name "module"
    boundary, account, owned := ← j.getObjValAs? Bool "owned"
    replacement := ← j.getObjValAs? (Option Name) "replacement"
    compilerCallers := ← j.getObjValAs? (Array Name) "compilerCallers" }⟩

/-- The execution account of one owned executable root (`RegulaPolicy.ExecutionRoot`), with
the exact-field JSON codecs of it, its closure and its visits. -/
abbrev ExecutionRoot := RegulaPolicy.ExecutionRoot
instance : ToJson RegulaPolicy.ExecutionVisit := ⟨fun v => Json.mkObj [
  ("moduleName", toJson v.moduleName), ("name", toJson v.name), ("parent", toJson v.parent)]⟩
instance : FromJson RegulaPolicy.ExecutionVisit := ⟨fun j => do
  exactFields j ["name", "moduleName", "parent"]
  return { name := ← j.getObjValAs? _ "name"
           moduleName := ← j.getObjValAs? _ "moduleName"
           parent := ← j.getObjValAs? _ "parent" }⟩
instance : ToJson RegulaPolicy.ExecutionClosure := ⟨fun c => Json.mkObj [
  ("activeSimplificationEdges", toJson c.activeSimplificationEdges),
  ("candidateEdges", toJson c.candidateEdges),
  ("currentReplacementEdges", toJson c.currentReplacementEdges),
  ("helperEdges", toJson c.helperEdges), ("historyEdges", toJson c.historyEdges),
  ("logicalEdges", toJson c.logicalEdges), ("nodes", toJson c.nodes),
  ("requiredCode", toJson c.requiredCode), ("unavailableCode", toJson c.unavailableCode),
  ("visits", toJson c.visits)]⟩
instance : FromJson RegulaPolicy.ExecutionClosure := ⟨fun j => do
  exactFields j ["nodes", "visits", "logicalEdges", "candidateEdges", "historyEdges",
    "currentReplacementEdges", "activeSimplificationEdges", "helperEdges", "requiredCode",
        "unavailableCode"]
  return {
    nodes := ← j.getObjValAs? _ "nodes"
    visits := ← j.getObjValAs? _ "visits"
    logicalEdges := ← j.getObjValAs? _ "logicalEdges"
    candidateEdges := ← j.getObjValAs? _ "candidateEdges"
    historyEdges := ← j.getObjValAs? _ "historyEdges"
    currentReplacementEdges := ← j.getObjValAs? _ "currentReplacementEdges"
    activeSimplificationEdges := ← j.getObjValAs? _ "activeSimplificationEdges"
    helperEdges := ← j.getObjValAs? _ "helperEdges"
    requiredCode := ← j.getObjValAs? _ "requiredCode"
    unavailableCode := ← j.getObjValAs? _ "unavailableCode"
  }⟩
instance : ToJson RegulaPolicy.ExecutionRoot := ⟨fun r => Json.mkObj [
  ("boundaries", toJson r.boundaries), ("closure", toJson r.closure),
  ("compilerEdges", toJson r.compilerEdges), ("module", toJson r.module),
  ("name", toJson r.name), ("unresolved", toJson r.unresolved)]⟩
instance : FromJson RegulaPolicy.ExecutionRoot := ⟨fun j => do
  exactFields j ["name", "module", "boundaries", "unresolved", "compilerEdges", "closure"]
  return {
    name := ← j.getObjValAs? _ "name"
    «module» := ← j.getObjValAs? _ "module"
    boundaries := ← j.getObjValAs? _ "boundaries"
    unresolved := ← j.getObjValAs? _ "unresolved"
    compilerEdges := ← j.getObjValAs? _ "compilerEdges"
    closure := ← j.getObjValAs? _ "closure"
  }⟩

/-- The resolved `.olean` path and direct imports of one loaded module
(`RegulaPolicy.ModuleOrigin`), with its exact-field JSON codec. -/
abbrev ModuleOrigin := RegulaPolicy.ModuleOrigin
deriving instance ToJson for RegulaPolicy.ModuleOrigin
instance : FromJson RegulaPolicy.ModuleOrigin := ⟨fun j => do
  exactFields j ["name", "olean", "imports"]
  return {
    name := ← j.getObjValAs? _ "name"
    olean := ← j.getObjValAs? _ "olean"
    imports := ← j.getObjValAs? _ "imports"
  }⟩

/-- The environment report of one requested module set (`RegulaPolicy.Environment`), with its
exact-field JSON codec. -/
abbrev Environment := RegulaPolicy.Environment
deriving instance ToJson for RegulaPolicy.Environment
instance : FromJson RegulaPolicy.Environment := ⟨fun j => do
  exactFields j ["toolchain", "compilerCapability", "modules", "moduleOrigins", "declarations", "execution"]
  let compilerCapability ← j.getObjValAs? _ "compilerCapability"
  let _ ← Compiler.admitCapability compilerCapability
  return {
    toolchain := ← j.getObjValAs? _ "toolchain"
    compilerCapability
    modules := ← j.getObjValAs? _ "modules"
    moduleOrigins := ← j.getObjValAs? _ "moduleOrigins"
    declarations := ← j.getObjValAs? _ "declarations"
    execution := ← j.getObjValAs? _ "execution"
  }⟩

/-- Declaration/root keys are frozen before their observations; history requests are registered
before each on-demand lookup during the walk.
These are unbound operational inputs to POLICY-04's claim-indexed `Census`, not acceptance. -/
structure Census where
  /-- The owned modules the report was requested for. -/
  modules : Array Name
  /-- The `(module, declaration)` key of every owned declaration, frozen before its record was
  collected. -/
  declarations : Array (Name × Name)
  /-- The `(module, root)` key of every executable root, when execution was inspected;
  `none` otherwise. -/
  executionRoots : Option (Array (Name × Name))
  /-- (execution root, module) requests registered before consulting history results. -/
  historyRequests : Array (Name × Name)
  deriving Repr

/-- Extraction keys alongside the original pure policy report. Operational transport
and receipt validation live in the checker layer, outside the force-loaded replay closure. -/
structure Collected extends RegulaPolicy.Environment where
  /-- The keys collected alongside the report. -/
  census : Census
  deriving Repr

end Regula.Report
