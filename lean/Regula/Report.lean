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

instance : ToJson DecisionResult := ⟨fun x => .str x.spelling⟩
instance : FromJson DecisionResult := ⟨fun j => do
  let s ← j.getStr?
  match DecisionResult.parse? s with
  | some x => return x
  | none => throw "unknown DecisionResult"⟩

instance : ToJson Carrier := ⟨fun x => .str x.spelling⟩
instance : FromJson Carrier := ⟨fun j => do
  match Carrier.parse? (← j.getStr?) with
  | some x => return x
  | none => throw "unknown Carrier"⟩

instance : ToJson Binding := ⟨fun
  | .default => "default" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"⟩
instance : FromJson Binding := ⟨fun j => do
  match ← j.getStr? with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | other => throw s!"unknown binding {other}"⟩

/-- An entry of a term's table of levels (`RegulaPolicy.LevelNode`), as an array: its constructor's
tag, then its arguments in order. -/
instance : ToJson LevelNode := ⟨fun
  | .zero => toJson ["zero"]
  | .succ of => .arr #["succ", toJson of]
  | .max left right => .arr #["max", toJson left, toJson right]
  | .imax left right => .arr #["imax", toJson left, toJson right]
  | .param name => .arr #["param", toJson name]
  | .mvar name => .arr #["mvar", toJson name]⟩
instance : FromJson LevelNode := ⟨fun j => do
  match (← j.getArr?).toList with
  | [.str "zero"] => return .zero
  | [.str "succ", of] => return .succ (← fromJson? of)
  | [.str "max", left, right] => return .max (← fromJson? left) (← fromJson? right)
  | [.str "imax", left, right] => return .imax (← fromJson? left) (← fromJson? right)
  | [.str "param", name] => return .param (← fromJson? name)
  | [.str "mvar", name] => return .mvar (← fromJson? name)
  | _ => throw s!"unknown level node {j.compress}"⟩

/-- An entry of a term's table of subterms (`RegulaPolicy.TermNode`), as an array: its
constructor's tag, then its arguments in order. -/
instance : ToJson TermNode := ⟨fun
  | .bvar index => .arr #["bvar", toJson index]
  | .fvar name => .arr #["fvar", toJson name]
  | .mvar name => .arr #["mvar", toJson name]
  | .sort level => .arr #["sort", toJson level]
  | .const name levels => .arr #["const", toJson name, toJson levels]
  | .app function argument => .arr #["app", toJson function, toJson argument]
  | .lam binder type body binding =>
      .arr #["lam", toJson binder, toJson type, toJson body, toJson binding]
  | .forallE binder type body binding =>
      .arr #["forall", toJson binder, toJson type, toJson body, toJson binding]
  | .letE binder type value body nondep =>
      .arr #["let", toJson binder, toJson type, toJson value, toJson body, toJson nondep]
  | .natLit value => .arr #["nat", toJson value]
  | .strLit value => .arr #["str", toJson value]
  | .proj typeName index value => .arr #["proj", toJson typeName, toJson index, toJson value]⟩
instance : FromJson TermNode := ⟨fun j => do
  match (← j.getArr?).toList with
  | [.str "bvar", index] => return .bvar (← fromJson? index)
  | [.str "fvar", name] => return .fvar (← fromJson? name)
  | [.str "mvar", name] => return .mvar (← fromJson? name)
  | [.str "sort", level] => return .sort (← fromJson? level)
  | [.str "const", name, levels] => return .const (← fromJson? name) (← fromJson? levels)
  | [.str "app", function, argument] => return .app (← fromJson? function) (← fromJson? argument)
  | [.str "lam", binder, type, body, binding] =>
      return .lam (← fromJson? binder) (← fromJson? type) (← fromJson? body) (← fromJson? binding)
  | [.str "forall", binder, type, body, binding] =>
      return .forallE (← fromJson? binder) (← fromJson? type) (← fromJson? body)
        (← fromJson? binding)
  | [.str "let", binder, type, value, body, nondep] =>
      return .letE (← fromJson? binder) (← fromJson? type) (← fromJson? value) (← fromJson? body)
        (← fromJson? nondep)
  | [.str "nat", value] => return .natLit (← fromJson? value)
  | [.str "str", value] => return .strLit (← fromJson? value)
  | [.str "proj", typeName, index, value] =>
      return .proj (← fromJson? typeName) (← fromJson? index) (← fromJson? value)
  | _ => throw s!"unknown term node {j.compress}"⟩

/-- An exact term (`RegulaPolicy.Term`): its table of levels and its table of subterms. -/
instance : ToJson RegulaPolicy.Term := ⟨fun t =>
  Json.mkObj [("levels", toJson t.levels), ("nodes", toJson t.nodes)]⟩
instance : FromJson RegulaPolicy.Term := ⟨fun j => do
  exactFields j ["levels", "nodes"]
  return { levels := ← j.getObjValAs? _ "levels", nodes := ← j.getObjValAs? _ "nodes" }⟩

/-- An expression of a report (`RegulaPolicy.Shown`): `exact`, its exact term, and `display`,
Lean's display of it for a reader. -/
instance : ToJson Shown := ⟨fun s =>
  Json.mkObj [("exact", toJson s.exact), ("display", toJson s.display)]⟩
instance : FromJson Shown := ⟨fun j => do
  exactFields j ["exact", "display"]
  return { exact := ← j.getObjValAs? _ "exact", display := ← j.getObjValAs? _ "display" }⟩

/-- A linkage conclusion of a carrier (`RegulaPolicy.Linkage`): `state` is `linked`, with the
applications of `Function.uncurry` and one proposition for each fact of the carrier, which the
decoder admits through `admitStatements`; or `unsupported` or `mismatch`, with the reason. Each
state has exactly its own members. -/
instance (carrier : Carrier) : ToJson (Linkage carrier) := ⟨fun
  | .linked conclusion => Json.mkObj [("state", toJson "linked"),
      ("uncurries", toJson conclusion.uncurries), ("statements", toJson conclusion.statements)]
  | .unlinked (.unsupported reason) =>
      Json.mkObj [("state", toJson "unsupported"), ("reason", toJson reason)]
  | .unlinked (.mismatch reason) =>
      Json.mkObj [("state", toJson "mismatch"), ("reason", toJson reason)]⟩
instance (carrier : Carrier) : FromJson (Linkage carrier) := ⟨fun j => do
  match ← j.getObjValAs? String "state" with
  | "linked" =>
    exactFields j ["state", "uncurries", "statements"]
    let uncurries ← j.getObjValAs? Nat "uncurries"
    let ⟨statements, exact⟩ ← admitStatements carrier (← j.getObjValAs? _ "statements")
    return .linked ⟨uncurries, statements, exact⟩
  | "unsupported" =>
    exactFields j ["state", "reason"]
    return .unlinked (.unsupported (← j.getObjValAs? _ "reason"))
  | "mismatch" =>
    exactFields j ["state", "reason"]
    return .unlinked (.mismatch (← j.getObjValAs? _ "reason"))
  | state => throw s!"unknown linkage state {state}"⟩

/-- The law observer's report of a registration (`RegulaPolicy.ContractEvidence`), with its
exact-field JSON codec; the linkage is decoded at the decoded carrier. -/
instance : ToJson ContractEvidence := ⟨fun e => Json.mkObj [
  ("carrier", toJson e.carrier), ("implementation", toJson e.implementation),
  ("universes", toJson e.universes), ("requirement", toJson e.requirement),
  ("domain", toJson e.domain), ("result", toJson e.result),
  ("accepts", toJson e.accepts), ("spec", toJson e.spec), ("decided", toJson e.decided),
  ("linkage", toJson e.linkage)]⟩
instance : FromJson ContractEvidence := ⟨fun j => do
  exactFields j ["carrier", "implementation", "universes", "requirement", "domain", "result",
    "accepts", "spec", "decided", "linkage"]
  let carrier ← j.getObjValAs? Carrier "carrier"
  return {
    carrier
    implementation := ← j.getObjValAs? _ "implementation"
    universes := ← j.getObjValAs? _ "universes"
    requirement := ← j.getObjValAs? _ "requirement"
    domain := ← j.getObjValAs? _ "domain"
    result := ← j.getObjValAs? _ "result"
    accepts := ← j.getObjValAs? _ "accepts"
    spec := ← j.getObjValAs? _ "spec"
    decided := ← j.getObjValAs? _ "decided"
    linkage := ← j.getObjValAs? (Linkage carrier) "linkage" }⟩

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
requirement, any refusal, its decision kind, `null` for a requirement that states none, and the
names of the functions that its specification shares with its implementation, by class
(`RegulaPolicy.ExecutableContract`, `RegulaPolicy.SharedNames`), with its exact-field JSON
codec. -/
abbrev ExecutableContract := RegulaPolicy.ExecutableContract
deriving instance ToJson for RegulaPolicy.SharedNames
instance : FromJson RegulaPolicy.SharedNames := ⟨fun j => do
  exactFields j ["booleans", "others", "throughTypes"]
  return {
    booleans := ← j.getObjValAs? _ "booleans"
    others := ← j.getObjValAs? _ "others"
    throughTypes := ← j.getObjValAs? _ "throughTypes"
  }⟩
deriving instance ToJson for RegulaPolicy.ExecutableContract
instance : FromJson RegulaPolicy.ExecutableContract := ⟨fun j => do
  exactFields j ["root", "requirement", "failure", "kind", "shared"]
  return {
    root := ← j.getObjValAs? _ "root"
    requirement := ← j.getObjValAs? _ "requirement"
    failure := ← j.getObjValAs? _ "failure"
    kind := ← j.getObjValAs? _ "kind"
    shared := ← j.getObjValAs? _ "shared"
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
  ("nativeStatement", toJson d.nativeStatement), ("nativeReplay", toJson d.nativeReplay),
  ("ranges", toJson d.recordedRanges), ("generatedFrom", toJson d.generatedFrom),
  ("axioms", toJson d.axioms), ("executableContract", toJson d.executableContract),
  ("decisionResult", toJson d.decisionResult), ("tableOmissions", toJson d.tableOmissions),
  ("contractEvidence", toJson d.contractEvidence),
  ("assumptions", toJson d.assumptions), ("checkedOperations", toJson d.checkedOperations)]⟩
instance : FromJson RegulaPolicy.Declaration := ⟨fun j => do
  exactFields j ["name", "module", "kind", "type", "prettyType", "isProp", "isUnsafe", "isPartial",
      "safety", "instance", "noncomputable", "implementedBy", "extern", "internal", "private",
          "projection", "matcher", "recursive", "unsafeRecBase", "levelParams", "all", "hints",
              "valueConstants", "unsafeRecRegenerated", "nativeStatement", "nativeReplay",
                  "ranges", "generatedFrom", "axioms", "executableContract", "decisionResult",
                      "tableOmissions", "contractEvidence", "assumptions", "checkedOperations"]
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
    nativeStatement := ← j.getObjValAs? _ "nativeStatement"
    nativeReplay := ← j.getObjValAs? _ "nativeReplay"
    recordedRanges := ← j.getObjValAs? _ "ranges"
    generatedFrom := ← j.getObjValAs? _ "generatedFrom"
    axioms := ← j.getObjValAs? _ "axioms"
    executableContract := ← j.getObjValAs? _ "executableContract"
    decisionResult := ← j.getObjValAs? _ "decisionResult"
    tableOmissions := ← j.getObjValAs? _ "tableOmissions"
    contractEvidence := ← j.getObjValAs? _ "contractEvidence"
    assumptions := ← j.getObjValAs? _ "assumptions"
    checkedOperations := ← j.getObjValAs? _ "checkedOperations"
  }⟩

/-- The proof and the required proposition of a checked correspondence
(`RegulaPolicy.CorrespondenceTerms`): `proof` and `required`, each an expression of a report. -/
instance : ToJson RegulaPolicy.CorrespondenceTerms := ⟨fun t => Json.mkObj [
  ("proof", toJson t.proof), ("required", toJson t.required)]⟩
instance : FromJson RegulaPolicy.CorrespondenceTerms := ⟨fun j => do
  exactFields j ["proof", "required"]
  return { proof := ← j.getObjValAs? _ "proof", required := ← j.getObjValAs? _ "required" }⟩

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
  ("exact", toJson b.terms?), ("module", toJson b.module), ("name", toJson b.name), ("occurrence", toJson b.occurrence),
  ("owned", toJson b.owned), ("replacement", toJson b.replacement),
  ("toolchainOrigin", toJson b.toolchainOrigin?)]⟩
instance : FromJson ExecutionBoundary := ⟨fun j => do
  exactFields j
      ["occurrence", "name", "module", "boundary", "correspondence", "owned", "replacement",
          "evidence", "exact", "compilerCallers", "toolchainOrigin"]
  let boundary ← j.getObjValAs? BoundaryKind "boundary"
  let state ← j.getObjValAs? Correspondence "correspondence"
  let detail ← j.getObjValAs? (Option String) "evidence"
  let origin ← j.getObjValAs? (Option ToolchainOrigin) "toolchainOrigin"
  let terms ← j.getObjValAs? (Option RegulaPolicy.CorrespondenceTerms) "exact"
  let account ← admitBoundaryEvidence boundary state detail origin terms
  unless account.detail == detail && account.toolchainOrigin? == origin &&
      account.terms? == terms do
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
  exactFields j ["toolchain", "compilerCapability", "modules", "moduleOrigins", "declarations",
    "execution", "imported"]
  let compilerCapability ← j.getObjValAs? _ "compilerCapability"
  let _ ← Compiler.admitCapability compilerCapability
  return {
    toolchain := ← j.getObjValAs? _ "toolchain"
    compilerCapability
    modules := ← j.getObjValAs? _ "modules"
    moduleOrigins := ← j.getObjValAs? _ "moduleOrigins"
    declarations := ← j.getObjValAs? _ "declarations"
    execution := ← j.getObjValAs? _ "execution"
    imported := ← j.getObjValAs? _ "imported"
  }⟩

/-- Declaration/root keys are frozen before their observations; history requests are registered
before each on-demand lookup during the walk.
These are unbound operational inputs to POLICY-04's claim-indexed `Census`, not acceptance. -/
structure Census where
  /-- The owned modules the report was requested for. -/
  modules : Array Name
  /-- The modules of the owned dependencies that the requested modules import, whose
  declarations and executable roots the report also records. -/
  dependencyModules : Array Name := #[]
  /-- The `(module, declaration)` key of every owned declaration, of `modules` and of
  `dependencyModules`, frozen before its record was collected. -/
  declarations : Array (Name × Name)
  /-- The `(module, root)` key of every executable root, when execution was inspected;
  `none` otherwise. -/
  executionRoots : Option (Array (Name × Name))
  /-- (execution root, module) requests registered before consulting history results. -/
  historyRequests : Array (Name × Name)
  deriving Repr

/-- The modules whose declarations, executable roots and documentation the report records: the
requested modules, then the modules of owned dependencies. -/
def Census.inspectedModules (c : Census) : Array Name :=
  c.modules ++ c.dependencyModules

/-- Extraction keys alongside the original pure policy report. Operational transport
and receipt validation live in the checker layer, outside the force-loaded replay closure. -/
structure Collected extends RegulaPolicy.Environment where
  /-- The keys collected alongside the report. -/
  census : Census
  deriving Repr

end Regula.Report
