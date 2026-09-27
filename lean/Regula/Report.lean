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

scoped instance : ToJson Name := ⟨Regula.RegistryCodec.nameJson⟩
scoped instance : FromJson Name := ⟨Regula.RegistryCodec.parseName⟩
open scoped Regula.Report

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
requirement and any refusal (`RegulaPolicy.ExecutableContract`), with its exact-field JSON
codec. -/
abbrev ExecutableContract := RegulaPolicy.ExecutableContract
deriving instance ToJson for RegulaPolicy.ExecutableContract
instance : FromJson RegulaPolicy.ExecutableContract := ⟨fun j => do
  exactFields j ["root", "requirement", "failure"]
  return {
    root := ← j.getObjValAs? _ "root"
    requirement := ← j.getObjValAs? _ "requirement"
    failure := ← j.getObjValAs? _ "failure"
  }⟩

/-- The Lean-semantic record of one owned constant (`RegulaPolicy.Declaration`), with its
exact-field JSON codec. -/
abbrev Declaration := RegulaPolicy.Declaration
deriving instance ToJson for RegulaPolicy.Declaration
instance : FromJson RegulaPolicy.Declaration := ⟨fun j => do
  exactFields j ["name", "module", "kind", "type", "prettyType", "isProp", "isUnsafe", "isPartial", "safety", "instance", "noncomputable", "implementedBy", "extern", "internal", "private", "projection", "matcher", "recursive", "unsafeRecBase", "levelParams", "all", "hints", "valueConstants", "unsafeRecValueOrigin", "unsafeRecValueExact", "unsafeRecValueDefeq", "unsafeRecEquationExact", "unsafeRecEquationDefeq", "unsafeRecEquationAxioms", "nativeBoolShape", "nativeReplay", "nativeUseParents", "ranges", "axioms", "executableContract"]
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
    unsafeRecValueOrigin := ← j.getObjValAs? _ "unsafeRecValueOrigin"
    unsafeRecValueExact := ← j.getObjValAs? _ "unsafeRecValueExact"
    unsafeRecValueDefeq := ← j.getObjValAs? _ "unsafeRecValueDefeq"
    unsafeRecEquationExact := ← j.getObjValAs? _ "unsafeRecEquationExact"
    unsafeRecEquationDefeq := ← j.getObjValAs? _ "unsafeRecEquationDefeq"
    unsafeRecEquationAxioms := ← j.getObjValAs? _ "unsafeRecEquationAxioms"
    nativeBoolShape := ← j.getObjValAs? _ "nativeBoolShape"
    nativeReplay := ← j.getObjValAs? _ "nativeReplay"
    nativeUseParents := ← j.getObjValAs? _ "nativeUseParents"
    ranges := ← j.getObjValAs? _ "ranges"
    axioms := ← j.getObjValAs? _ "axioms"
    executableContract := ← j.getObjValAs? _ "executableContract"
  }⟩

/-- One execution boundary a root's closure reaches (`RegulaPolicy.ExecutionBoundary`), with a
JSON codec whose decoder admits the boundary evidence through `admitBoundaryEvidence` and
refuses a noncanonical payload. -/
abbrev ExecutionBoundary := RegulaPolicy.ExecutionBoundary
instance : ToJson RegulaPolicy.NativeOrigin := ⟨fun o => Json.mkObj [
  ("module", toJson o.moduleName), ("actual", toJson o.actual), ("expected", toJson o.expected)]⟩
instance : FromJson RegulaPolicy.NativeOrigin := ⟨fun j => do
  exactFields j ["module", "actual", "expected"]
  RegulaPolicy.admitNativeOrigin (← j.getObjValAs? Name "module")
    (← j.getObjValAs? String "actual") (← j.getObjValAs? String "expected")⟩

instance : ToJson ExecutionBoundary := ⟨fun b => Json.mkObj [
  ("occurrence", toJson b.occurrence), ("name", toJson b.name), ("module", toJson b.module),
  ("boundary", toJson b.boundary), ("correspondence", toJson b.correspondence),
  ("owned", toJson b.owned), ("replacement", toJson b.replacement),
  ("evidence", toJson b.evidence), ("compilerCallers", toJson b.compilerCallers),
  ("nativeOrigin", toJson b.account.nativeOrigin?)]⟩
instance : FromJson ExecutionBoundary := ⟨fun j => do
  exactFields j ["occurrence", "name", "module", "boundary", "correspondence", "owned", "replacement", "evidence", "compilerCallers", "nativeOrigin"]
  let boundary ← j.getObjValAs? BoundaryKind "boundary"
  let state ← j.getObjValAs? Correspondence "correspondence"
  let detail ← j.getObjValAs? (Option String) "evidence"
  let origin ← j.getObjValAs? (Option NativeOrigin) "nativeOrigin"
  let account ← admitBoundaryEvidence boundary state detail origin
  unless account.detail == detail && account.nativeOrigin? == origin do
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
deriving instance ToJson for RegulaPolicy.ExecutionVisit
instance : FromJson RegulaPolicy.ExecutionVisit := ⟨fun j => do
  exactFields j ["name", "moduleName", "parent"]
  return { name := ← j.getObjValAs? _ "name"
           moduleName := ← j.getObjValAs? _ "moduleName"
           parent := ← j.getObjValAs? _ "parent" }⟩
deriving instance ToJson for RegulaPolicy.ExecutionClosure
instance : FromJson RegulaPolicy.ExecutionClosure := ⟨fun j => do
  exactFields j ["nodes", "visits", "logicalEdges", "candidateEdges", "historyEdges",
    "currentReplacementEdges", "activeSimplificationEdges", "helperEdges", "requiredCode", "unavailableCode"]
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
deriving instance ToJson for RegulaPolicy.ExecutionRoot
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
  exactFields j ["toolchain", "modules", "moduleOrigins", "declarations", "execution"]
  return {
    toolchain := ← j.getObjValAs? _ "toolchain"
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
