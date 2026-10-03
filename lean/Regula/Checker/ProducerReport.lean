import Regula.Report
import Regula.SourceTexts
import RegulaPolicy.Admission
import RegulaPolicy.ModuleHeader
import RegulaPolicy.Guards
import Regula.Contract
import RegulaCore.Assembly
import Lean.Elab.Command

/-! # Producer report transport

Operational producer transport and key reconciliation. Kept outside the force-loaded
report module so ordinary admission does not replay JSON-validator implementation. -/
namespace Regula.Checker.ProducerReport
open Lean RegulaPolicy
open Regula.Checker.PolicyCodec (exactFields)
open scoped Regula.Report

/-- Required owned-admission or frozen source/configuration evidence is unavailable
or invalid. Trusted operational checks supply this outcome; raw data construction
does not authenticate it. Generic worker/import failures retain their own path. -/
structure AdmissionFailure where
  /-- What was unavailable or invalid; the decoder refuses an empty detail. -/
  detail : String
  deriving Repr, ToJson

instance : FromJson AdmissionFailure := ⟨fun j => do
  exactFields j ["detail"]
  let detail ← j.getObjValAs? String "detail"
  if detail.isEmpty then throw "empty owned-admission failure"
  return ⟨detail⟩⟩

/-- The operational census of one report (`Regula.Report.Census`), with its exact-field JSON
codec. -/
abbrev Census := Regula.Report.Census
deriving instance ToJson for Regula.Report.Census

instance : FromJson Census := ⟨fun j => do
  exactFields j ["modules", "declarations", "executionRoots", "historyRequests"]
  return { modules := ← j.getObjValAs? _ "modules"
           declarations := ← j.getObjValAs? _ "declarations"
           executionRoots := ← j.getObjValAs? _ "executionRoots"
           historyRequests := ← j.getObjValAs? _ "historyRequests" }⟩

/-- Replay scope can exceed report scope. Required keys come from the replayed modules' own data
in the original environment; admitted keys are observed in the separately replayed kernel after
`Environment.replay` and the copy checks (`Admission.validate`). The keys of a reused module that
the environment itself reports come from that module's own data too, and are admitted by the
earlier environment that replayed it (`Admission.reuseJustified_admitted`). -/
structure AdmissionReceipt where
  /-- The replay set: the owned modules other than `reused` and the checker reporter modules that
  import one of them, without duplicates. The environment replays those of them it loaded. One
  with a key in `required` is a loaded module with at least one constant that is neither `unsafe`
  nor `partial`; a loaded module with no such constant has no key, and a module the environment
  did not load is listed here too. -/
  modules : Array Name
  /-- The `(module, declaration)` key of every constant a replayed module's own data contains
  that is neither `unsafe` nor `partial`; a name several replayed modules contain has one key per
  module. Then the same keys of each reused module among the environment's requested modules. -/
  required : Array (Name × Name)
  /-- The required keys admitted by replay and the copy checks, or, for a reused module's, by
  the environment that replayed it, in the same order. -/
  admitted : Array (Name × Name)
  /-- The owned modules not replayed here because an earlier environment of the same audit
  admitted them over the identical import closure (`Admission.reusedModules`). One of the
  environment's own requested modules is among them only when an earlier environment loaded it
  first (claimed libraries that import one another). -/
  reused : Array Name
  /-- The replayed modules containing a copy of a name that the replay base or another replayed
  module also declares. Their admission depends on which copy this environment keeps, so no
  later environment reuses it. -/
  shared : Array Name
  deriving Repr, DecidableEq, ToJson

instance : FromJson AdmissionReceipt := ⟨fun j => do
  exactFields j ["modules", "required", "admitted", "reused", "shared"]
  return { modules := ← j.getObjValAs? _ "modules"
           required := ← j.getObjValAs? _ "required"
           admitted := ← j.getObjValAs? _ "admitted"
           reused := ← j.getObjValAs? _ "reused"
           shared := ← j.getObjValAs? _ "shared" }⟩

instance : ToJson ModuleHeader.ImportSpec := ⟨fun s => Json.mkObj [
  ("module", toJson s.module), ("importAll", toJson s.importAll),
  ("isExported", toJson s.isExported), ("isMeta", toJson s.isMeta)]⟩

instance : FromJson ModuleHeader.ImportSpec := ⟨fun j => do
  exactFields j ["module", "importAll", "isExported", "isMeta"]
  return ⟨← j.getObjValAs? _ "module", ← j.getObjValAs? _ "importAll",
    ← j.getObjValAs? _ "isExported", ← j.getObjValAs? _ "isMeta"⟩⟩

instance : ToJson ModuleHeader.Observation := ⟨fun o => Json.mkObj [
  ("documented", toJson o.documented), ("documentationFirst", toJson o.documentationFirst),
  ("imports", toJson o.imports)]⟩

instance : FromJson ModuleHeader.Observation := ⟨fun j => do
  exactFields j ["documented", "documentationFirst", "imports"]
  return ⟨← j.getObjValAs? _ "documented", ← j.getObjValAs? _ "documentationFirst",
    ← j.getObjValAs? _ "imports"⟩⟩

/-- Metadata presence is deliberately separate from prose adequacy. The material selector
is frozen before docstring lookup and retains exact owning modules, including empty modules.
Each module carries its RG5001 header observation (`RegulaPolicy.ModuleHeader`). -/
structure DocumentationObservation where
  /-- Each claimed module with its RG5001 header observation, read from its bound source. -/
  modules : Array (Name × ModuleHeader.Observation)
  /-- The `(module, declaration)` key of every owned declaration the material selector chose,
  frozen before any docstring was read. -/
  materialDeclarations : Array (Name × Name)
  /-- Each material key with the docstring `findDocString?` returned for it, if any. -/
  declarations : Array ((Name × Name) × Option String)
  deriving Repr, ToJson

instance : FromJson DocumentationObservation := ⟨fun j => do
  exactFields j ["modules", "materialDeclarations", "declarations"]
  return { modules := ← j.getObjValAs? _ "modules"
           materialDeclarations := ← j.getObjValAs? _ "materialDeclarations"
           declarations := ← j.getObjValAs? _ "declarations" }⟩

instance : ToJson HistoryOutcome := ⟨fun
  | .completed path before after edges => Json.mkObj [
      ("kind", toJson "completed"), ("path", toJson path), ("before", toJson before),
      ("after", toJson after), ("replacements", toJson edges)]
  | .unavailable detail => Json.mkObj [("kind", toJson "unavailable"), ("detail", toJson detail)]⟩

instance : FromJson HistoryOutcome := ⟨fun j => do
  match ← j.getObjValAs? String "kind" with
  | "completed" =>
    exactFields j ["kind", "path", "before", "after", "replacements"]
    return .completed (← j.getObjValAs? _ "path") (← j.getObjValAs? _ "before")
      (← j.getObjValAs? _ "after") (← j.getObjValAs? _ "replacements")
  | "unavailable" =>
    exactFields j ["kind", "detail"]
    return .unavailable (← j.getObjValAs? _ "detail")
  | _ => throw "producer-history: unknown outcome"⟩

/-- Only a completed receipt supplies execution edges; failure remains explicit. -/
def HistoryOutcome.edges : HistoryOutcome → Except String (Array (Name × Name))
  | .completed _ _ _ edges => .ok edges
  | .unavailable detail => .error detail

/-- Exact source observed for one owned module; the caller binds it to the build
request. Paths identify files, while content equality binds their actual text. -/
structure SourceBinding where
  /-- The owned module the source belongs to. -/
  moduleName : Name
  /-- The path of the source file read. -/
  path : String
  /-- The exact text read from that file. -/
  content : String
  deriving Repr, DecidableEq, ToJson

instance : FromJson SourceBinding := ⟨fun j => do
  exactFields j ["moduleName", "path", "content"]
  return { moduleName := ← j.getObjValAs? _ "moduleName"
           path := ← j.getObjValAs? _ "path"
           content := ← j.getObjValAs? _ "content" }⟩

/-- Operational producer account extends the pure policy observations.
The interactive probe alone has no admission/documentation receipt. Trusted loaders supply
both; a consumer must validate the account before using its results. -/
structure Environment extends Regula.Report.Collected where
  /-- The kernel-replay receipt of the owned declarations, when the loader produced one. -/
  admission : Option AdmissionReceipt := none
  /-- The documentation observation of the claimed modules, when the loader produced one. -/
  documentation : Option DocumentationObservation := none
  /-- The replacement-history outcome of each module whose history was requested. -/
  histories : Array (Name × HistoryOutcome) := #[]
  /-- The exact source observed for each owned module. -/
  sourceBindings : Array SourceBinding := #[]
  deriving Repr

instance : ToJson Environment := ⟨fun r => Json.mkObj [
  ("toolchain", toJson r.toolchain), ("modules", toJson r.modules),
  ("compilerCapability", toJson r.compilerCapability),
  ("moduleOrigins", toJson r.moduleOrigins), ("declarations", toJson r.declarations),
  ("execution", toJson r.execution), ("census", toJson r.census),
  ("admission", toJson r.admission), ("documentation", toJson r.documentation),
  ("histories", toJson r.histories), ("sourceBindings", toJson r.sourceBindings)]⟩

/-- Result-file rendering of a source binding: its module, path and text, the text as a
`sourceText` member, which a result file stores once (`SourceTexts.intern`). -/
def SourceBinding.resultJson (s : SourceBinding) : Json := Json.mkObj [
  ("moduleName", toJson s.moduleName), ("path", toJson s.path),
  (SourceTexts.textKey, toJson s.content)]

/-- Read a source binding `SourceBinding.resultJson` wrote, from an expanded result document. -/
def SourceBinding.ofResultJson (j : Json) : Except String SourceBinding := do
  exactFields j ["moduleName", "path", SourceTexts.textKey]
  return { moduleName := ← j.getObjValAs? _ "moduleName"
           path := ← j.getObjValAs? _ "path"
           content := ← j.getObjValAs? _ SourceTexts.textKey }

/-- The `sourceAccount` member of a result document: the sources a run observed, each by
`SourceBinding.resultJson`. -/
def sourceAccountJson (sources : Array SourceBinding) : Json :=
  toJson (sources.map SourceBinding.resultJson)

/-- Result-file rendering of a history outcome: the transport fields, with a completed
receipt's `before` and `after` texts each as a `sourceText` member (`SourceTexts.textJson`). -/
def HistoryOutcome.resultJson : HistoryOutcome → Json
  | .completed path before after edges => Json.mkObj [
      ("kind", toJson "completed"), ("path", toJson path),
      ("before", SourceTexts.textJson before), ("after", SourceTexts.textJson after),
      ("replacements", toJson edges)]
  | .unavailable detail => toJson (HistoryOutcome.unavailable detail)

/-- Result-file rendering of a declaration: the transport fields, without `type`, the `repr` of
the kernel type expression, unless `kernelTypes` asks for it (`axiomGate --kernel-types`). That
text is recomputable from the pinned inputs; `prettyType` is the type as Lean prints it. Checker
decisions use the in-memory record, which keeps `type`. -/
def declarationResultJson (d : Regula.Report.Declaration) (kernelTypes : Bool := false) : Json :=
  match toJson d with
  | .obj members => if kernelTypes then .obj members else .obj (members.erase "type")
  | other => other

/-- Result-file rendering: the transport fields except `modules` and `moduleOrigins`, which
list every module of the imported environment (the whole import closure) and are
recomputable from the pinned inputs, and, unless `kernelTypes`, except each declaration's `type`
(`declarationResultJson`). Owned modules remain in `census.modules`. Source texts, in
`sourceBindings` and completed `histories`, are `sourceText` members. `execution` is the array of
root accounts; a result file holds what `SharedExecution.intern` writes for it. Checker
decisions use the in-memory report; worker transport keeps the full `ToJson` shape. -/
def Environment.resultJson (r : Environment) (kernelTypes : Bool := false) : Json := Json.mkObj [
  ("toolchain", toJson r.toolchain),
  ("compilerCapability", toJson r.compilerCapability),
  ("declarations", toJson (r.declarations.map (declarationResultJson · kernelTypes))),
  ("execution", toJson r.execution), ("census", toJson r.census),
  ("admission", toJson r.admission), ("documentation", toJson r.documentation),
  ("histories", toJson (r.histories.map fun (name, outcome) => (name, outcome.resultJson))),
  ("sourceBindings", toJson (r.sourceBindings.map SourceBinding.resultJson))]

/-- The result rendering is independent of the import closure (kernel-checked by `rfl`). -/
theorem Environment.resultJson_imports_independent (r : Environment) (modules : Array Name)
    (moduleOrigins : Array RegulaPolicy.ModuleOrigin) (kernelTypes : Bool) :
    Environment.resultJson { r with modules, moduleOrigins } kernelTypes =
      r.resultJson kernelTypes := rfl

/-- Every owned source binding is unique, located, loaded and covers each claimed
module and each declaration's ranges: its admitted ranges (`Declaration.ranges`) and the
selection range Lean recorded (`Declaration.recordedRanges`), which the admitted pair drops when
it leaves the full range. -/
def Environment.sourceEvidenceOK (r : Environment) : Bool :=
  (canonicalNames (r.sourceBindings.map (·.moduleName))).size == r.sourceBindings.size &&
    r.sourceBindings.all (fun s => !s.path.isEmpty && r.modules.contains s.moduleName) &&
    r.census.modules.all (fun m => r.sourceBindings.any (·.moduleName == m)) &&
    r.declarations.all (fun d => r.sourceBindings.any (fun s => s.moduleName == d.module &&
      d.ranges.all (·.validFor s.content) &&
      d.recordedRanges.all (·.selectionRange.validFor s.content)))

/-- Succeed when `sourceEvidenceOK` holds, and otherwise fail with a `producer-source`
admission failure. -/
def Environment.validateSourceEvidence (r : Environment) : Except AdmissionFailure Unit := do
  unless r.sourceEvidenceOK do
    throw ⟨"producer-source: source coverage or coordinates mismatch"⟩

/-- Claimed modules are nonempty, unique and loaded. -/
def Environment.censusModulesOK (r : Environment) : Bool :=
  !r.census.modules.isEmpty &&
    (canonicalNames r.census.modules).size == r.census.modules.size &&
    r.census.modules.all r.modules.contains

/-- The declaration census is unique, exactly the reported declaration keys in order,
and owned by claimed modules. -/
def Environment.censusDeclarationsOK (r : Environment) : Bool :=
  (canonicalEdges r.census.declarations).size == r.census.declarations.size &&
    r.census.declarations == r.declarations.map (fun d => (d.module, d.name)) &&
    r.census.declarations.all (fun k => r.census.modules.contains k.1)

/-- Execution results are present exactly for the requested unique roots, in order. -/
def Environment.validateExecutionCensus (r : Environment) : Except String Unit :=
  match r.census.executionRoots with
  | none => unless r.execution.isEmpty do throw "producer-census: unrequested execution results"
  | some roots =>
    unless (canonicalEdges roots).size == roots.size &&
        roots == r.execution.map (fun root => (root.module, root.name)) &&
        roots.all (fun key => r.modules.contains key.1) do
      throw "producer-census: execution root coverage mismatch"

/-- The replay receipt covers unique modules and requirements, admits exactly what it
requires, requires only keys of replayed or reused modules, replays or reuses every claimed
module, requires every safe total declaration, and lists no module as both replayed and
reused. -/
def Environment.receiptOK (r : Environment) (receipt : AdmissionReceipt) : Bool :=
  let requiredSet := receipt.required.foldl (fun s k => s.insert k)
    ({} : Std.HashSet (Name × Name))
  (canonicalNames receipt.modules).size == receipt.modules.size &&
    (canonicalEdges receipt.required).size == receipt.required.size &&
    receipt.admitted == receipt.required &&
    receipt.required.all (fun k => receipt.modules.contains k.1 || receipt.reused.contains k.1) &&
    r.census.modules.all (fun m => receipt.modules.contains m || receipt.reused.contains m) &&
    r.declarations.all (fun d => d.isUnsafe || d.isPartial ||
      requiredSet.contains (d.module, d.name)) &&
    receipt.reused.all (fun m => !receipt.modules.contains m)

/-- Documentation observations cover exactly the claimed modules, and exactly the
unique material declarations the census contains, in order. -/
def Environment.documentationOK (r : Environment) (docs : DocumentationObservation) : Bool :=
  docs.modules.map (·.1) == r.census.modules &&
    (canonicalEdges docs.materialDeclarations).size == docs.materialDeclarations.size &&
    docs.materialDeclarations.all r.census.declarations.contains &&
    docs.declarations.map (·.1) == docs.materialDeclarations

/-- History requests are unique, name executed roots in loaded modules, and the
recorded histories are exactly one per requested module. -/
def Environment.historyRequestsOK (r : Environment) : Bool :=
  let requests := r.census.historyRequests
  (canonicalEdges requests).size == requests.size &&
    requests.all (fun (root, mod) => r.execution.any (·.name == root) && r.modules.contains mod) &&
    r.histories.map (·.1) == canonicalNames (requests.map (·.2))

/-- One recorded module history: a completed receipt is located, source-stable and
bound to the owned source snapshot; an unavailable one leaves every root it was
requested for with unresolved execution evidence. -/
def Environment.validateHistory (r : Environment) : Name × HistoryOutcome → Except String Unit
  | (mod, .completed path before after edges) => do
    unless !path.isEmpty && before == after &&
        edges.all (fun (a, b) => !a.isAnonymous && !b.isAnonymous) do
      throw "producer-history: invalid completed source observation"
    if let some source := r.sourceBindings.find? (·.moduleName == mod) then
      unless path == source.path && before == source.content do
        throw "producer-source: history differs from owned source snapshot"
  | (mod, .unavailable detail) =>
    unless !detail.isEmpty && r.census.historyRequests.all
        (fun (root, requested) => requested != mod ||
        r.execution.any (fun e => e.name == root && !e.unresolved.isEmpty)) do
      throw "producer-history: unavailable history without unresolved execution"

/-- A runtime replacement the toolchain does not own is requested, and a resolved root's
replacement edge is in its module's completed history. A toolchain replacement has no history
obligation (`ExecutionBoundary.needsHistory`). -/
def Environment.validateReplacementBoundary (r : Environment) (root : ExecutionRoot)
    (boundary : ExecutionBoundary) : Except String Unit := do
  if boundary.needsHistory then
    unless r.census.historyRequests.contains (root.name, boundary.module) do
      throw "producer-history: unrequested runtime replacement"
    if root.unresolved.isEmpty then
      let some (_, .completed _ _ _ edges) := r.histories.find? (·.1 == boundary.module)
        | throw "producer-history: completed execution lacks history"
      let some replacement := boundary.replacement
        | throw "producer-history: runtime replacement target missing"
      unless edges.contains (boundary.name, replacement) do
        throw "producer-history: completed execution omits replacement history edge"

/-- The root and every boundary are reached in their own modules, and every reached
module is loaded. -/
def Environment.attributionOK (r : Environment) (root : ExecutionRoot) : Bool :=
  let visits := root.closure.visits
  (visits.find? (·.name == root.name)).any (·.moduleName == some root.module) &&
    visits.all (fun v => v.moduleName.all r.modules.contains) &&
    root.boundaries.all (fun b =>
      (visits.find? (·.name == b.name)).any (·.moduleName == some b.module))

/-- Replacement edges of each boundary kind, as a canonical edge set. -/
def boundaryEdges (root : ExecutionRoot) (kind : BoundaryKind) : Array (Name × Name) :=
  canonicalEdges <| root.boundaries.filterMap fun b =>
    if b.boundary == kind then b.replacement.map (b.name, ·) else none

/-- Compiler simplifications are exactly the candidate edges; runtime replacements
are exactly the historical plus current replacement edges. -/
def boundaryChannelsOK (root : ExecutionRoot) : Bool :=
  boundaryEdges root .compilerSimplification == root.closure.candidateEdges &&
    boundaryEdges root .runtimeReplacement == canonicalEdges
      (root.closure.historyEdges ++ root.closure.currentReplacementEdges)

/-- The current replacement edges with a history obligation: every one except those whose
reference is a runtime-replacement boundary the toolchain owns. -/
def historyReplacementEdges (root : ExecutionRoot) : Array (Name × Name) :=
  root.closure.currentReplacementEdges.filter fun edge =>
    !root.boundaries.any fun b =>
      b.boundary == .runtimeReplacement && b.name == edge.1 && b.toolchainOrigin?.isSome

/-- The completed-history edges recorded for one current replacement edge. -/
def Environment.recordedHistoryEdges (r : Environment) (root : ExecutionRoot)
    (edge : Name × Name) : Except String (Array (Name × Name)) := do
  let some visit := root.closure.visits.find? (·.name == edge.1)
    | throw "producer-closure: replacement reference is not reached"
  let some mod := visit.moduleName
    | throw "producer-closure: replacement module is unavailable"
  unless r.census.historyRequests.contains (root.name, mod) do
    throw "producer-closure: replacement history request is missing"
  let some (_, outcome) := r.histories.find? (·.1 == mod)
    | throw "producer-closure: replacement history outcome is missing"
  if let .completed _ _ _ edges := outcome then return edges.filter (·.1 == edge.1)
  return #[]

/-- One execution root's replacement, attribution and history-edge accounts. -/
def Environment.validateRoot (r : Environment) (root : ExecutionRoot) : Except String Unit := do
  root.boundaries.forM (r.validateReplacementBoundary root)
  unless r.attributionOK root do
    throw "producer-closure: reached module attribution mismatch"
  unless boundaryChannelsOK root do
    throw "producer-closure: replacement boundary coverage mismatch"
  let expectedHistory ← (historyReplacementEdges root).foldlM
    (fun acc edge => return acc ++ (← r.recordedHistoryEdges root edge)) #[]
  unless canonicalEdges expectedHistory == root.closure.historyEdges do
    throw "producer-closure: historical edges differ from their source receipts"

/-- Exact key reconciliation at the producer and transport admission boundaries. This
checks supplied observations; truthful Lean/Lake extraction remains the trusted boundary.
The guards run in this order and the first failure is the refusal. -/
def Environment.validate (r : Environment) : Except String Unit := do
  unless decide (r.compilerCapability = Compiler.legacyCompilerTrust) do
    throw "compiler capability differs from this Regula build"
  unless r.censusModulesOK do throw "producer-census: missing or duplicate claimed modules"
  unless r.censusDeclarationsOK do throw "producer-census: declaration coverage mismatch"
  r.validateExecutionCensus
  match admitExecution r.execution with
  | .error _ => throw "producer-closure: invalid reached-node, edge, or boundary account"
  | .ok _ => pure ()
  r.validateSourceEvidence.mapError (·.detail)
  let some receipt := r.admission | throw "producer-admission: missing replay receipt"
  unless r.receiptOK receipt do throw "producer-admission: replay coverage mismatch"
  let some docs := r.documentation | throw "producer-documentation: missing observations"
  unless r.documentationOK docs do throw "producer-documentation: selector coverage mismatch"
  unless r.historyRequestsOK do throw "producer-history: request coverage mismatch"
  r.histories.forM r.validateHistory
  r.execution.forM r.validateRoot


/-! ### What a successful transport validation establishes

`validate_eq_ok` decomposes the executed guard sequence exactly. The named propositions
below restate each guard in terms of the report's own fields, and `validate_sound`
proves every one of them for every admitted report, replacing the former sampled
transport mutations. They concern supplied observations only; truthful Lean/Lake
extraction remains the trusted boundary. -/

open RegulaPolicy.Guards

/-- Exact decomposition: the executed validator succeeds iff every guard succeeds. The
converse direction excludes an always-refusing implementation. -/
theorem validate_eq_ok (r : Environment) :
    r.validate = .ok () ↔
      r.compilerCapability = Compiler.legacyCompilerTrust ∧
      r.censusModulesOK = true ∧ r.censusDeclarationsOK = true ∧
      r.validateExecutionCensus = .ok () ∧ (∃ i, admitExecution r.execution = .ok i) ∧
      r.validateSourceEvidence = .ok () ∧
      (∃ receipt, r.admission = some receipt ∧ r.receiptOK receipt = true) ∧
      (∃ docs, r.documentation = some docs ∧ r.documentationOK docs = true) ∧
      r.historyRequestsOK = true ∧
      (∀ h ∈ r.histories, r.validateHistory h = .ok ()) ∧
      (∀ root ∈ r.execution, r.validateRoot root = .ok ()) := by
  unfold Environment.validate
  cases admitExecution r.execution <;> cases r.admission <;> cases r.documentation <;>
    simp [forM_eq_ok]

/-- Claimed modules are nonempty, unique and loaded; the declaration census is exactly
the reported declaration keys in order, unique, and owned by claimed modules. -/
def Environment.CensusSound (r : Environment) : Prop :=
  r.census.modules ≠ #[] ∧ r.census.modules.toList.Nodup ∧
  (∀ m ∈ r.census.modules, m ∈ r.modules) ∧
  r.census.declarations = r.declarations.map (fun d => (d.module, d.name)) ∧
  r.census.declarations.toList.Nodup ∧
  (∀ k ∈ r.census.declarations, k.1 ∈ r.census.modules)

/-- Execution results exist only when requested, and then exactly for the unique
requested roots, in order, from loaded modules. -/
def Environment.ExecutionCensusSound (r : Environment) : Prop :=
  match r.census.executionRoots with
  | none => r.execution = #[]
  | some roots => roots.toList.Nodup ∧
      roots = r.execution.map (fun root => (root.module, root.name)) ∧
      ∀ key ∈ roots, key.1 ∈ r.modules

/-- Source bindings have unique modules, nonempty paths and loaded modules; they cover
every claimed module, and each declaration's ranges are valid in its module's source. -/
def Environment.SourceEvidenceSound (r : Environment) : Prop :=
  (r.sourceBindings.map (·.moduleName)).toList.Nodup ∧
  (∀ s ∈ r.sourceBindings, s.path ≠ "" ∧ s.moduleName ∈ r.modules) ∧
  (∀ m ∈ r.census.modules, ∃ s ∈ r.sourceBindings, s.moduleName = m) ∧
  (∀ d ∈ r.declarations, ∃ s ∈ r.sourceBindings, s.moduleName = d.module ∧
    ∀ range, d.ranges = some range → range.validFor s.content = true)

/-- Every declaration has a source binding of its module in which the full range and the
selection range Lean recorded for it (`Declaration.recordedRanges`) are valid.
`SourceEvidenceSound` states this of the admitted pair, which drops a recorded selection range
that leaves the full range. -/
def Environment.RecordedRangesSound (r : Environment) : Prop :=
  ∀ d ∈ r.declarations, ∃ s ∈ r.sourceBindings, s.moduleName = d.module ∧
    ∀ range, d.recordedRanges = some range →
      range.range.validFor s.content = true ∧ range.selectionRange.validFor s.content = true

/-- The replay receipt exists, admits exactly its unique requirements, each a key of one of its
unique replayed modules or of a reused module, replays or reuses every claimed module, requires
every safe total declaration, and lists no module as both replayed and reused. That a key of a
reused module was admitted by the environment that replayed the module is the coordinator's
check (`Admission.reuseJustified_admitted`), not this one. -/
def Environment.AdmissionSound (r : Environment) : Prop :=
  ∃ receipt, r.admission = some receipt ∧ receipt.admitted = receipt.required ∧
    receipt.modules.toList.Nodup ∧ receipt.required.toList.Nodup ∧
    (∀ k ∈ receipt.required, k.1 ∈ receipt.modules ∨ k.1 ∈ receipt.reused) ∧
    (∀ m ∈ r.census.modules, m ∈ receipt.modules ∨ m ∈ receipt.reused) ∧
    (∀ d ∈ r.declarations,
      d.isUnsafe = true ∨ d.isPartial = true ∨ (d.module, d.name) ∈ receipt.required) ∧
    ∀ m ∈ receipt.reused, m ∉ receipt.modules

/-- Documentation observations exist, cover exactly the claimed modules in order, and
record exactly the unique census-declared material selection in order. -/
def Environment.DocumentationSound (r : Environment) : Prop :=
  ∃ docs, r.documentation = some docs ∧ docs.modules.map (·.1) = r.census.modules ∧
    docs.materialDeclarations.toList.Nodup ∧
    (∀ k ∈ docs.materialDeclarations, k ∈ r.census.declarations) ∧
    docs.declarations.map (·.1) = docs.materialDeclarations

/-- History requests are unique and name executed roots in loaded modules; recorded
histories are exactly one per requested module. -/
def Environment.HistoryRequestsSound (r : Environment) : Prop :=
  r.census.historyRequests.toList.Nodup ∧
  (∀ request ∈ r.census.historyRequests,
    (∃ e ∈ r.execution, e.name = request.1) ∧ request.2 ∈ r.modules) ∧
  r.histories.map (·.1) = canonicalNames (r.census.historyRequests.map (·.2))

/-- A completed history is located, source-stable, has named edge endpoints and is bound
to the owned snapshot when its module has one; an unavailable one is explained and leaves every root
requested
from its module with unresolved execution evidence. -/
def Environment.HistoriesSound (r : Environment) : Prop :=
  (∀ mod path before after edges, (mod, .completed path before after edges) ∈ r.histories →
    path ≠ "" ∧ before = after ∧
    (∀ edge ∈ edges, edge.1 ≠ .anonymous ∧ edge.2 ≠ .anonymous) ∧
    ∀ source, r.sourceBindings.find? (·.moduleName == mod) = some source →
      path = source.path ∧ before = source.content) ∧
  (∀ mod detail, (mod, .unavailable detail) ∈ r.histories → detail ≠ "" ∧
    ∀ root, (root, mod) ∈ r.census.historyRequests →
      ∃ e ∈ r.execution, e.name = root ∧ e.unresolved ≠ #[])

/-- Every runtime replacement the toolchain does not own is requested; for a resolved root its
replacement edge is in its module's completed history. -/
def Environment.ReplacementsSound (r : Environment) : Prop :=
  ∀ root ∈ r.execution, ∀ b ∈ root.boundaries, b.needsHistory = true →
    (root.name, b.module) ∈ r.census.historyRequests ∧
    (root.unresolved = #[] → ∃ mod path before after edges replacement,
      r.histories.find? (·.1 == b.module) = some (mod, .completed path before after edges) ∧
      b.replacement = some replacement ∧ (b.name, replacement) ∈ edges)

/-- Every root and boundary is reached in its own module, every reached module is
loaded, and each boundary kind's replacement edges are exactly the closure's
corresponding edges. -/
def Environment.ClosureAccountSound (r : Environment) : Prop :=
  ∀ root ∈ r.execution,
    (∃ v, root.closure.visits.find? (·.name == root.name) = some v ∧
      v.moduleName = some root.module) ∧
    (∀ v ∈ root.closure.visits, ∀ m, v.moduleName = some m → m ∈ r.modules) ∧
    (∀ b ∈ root.boundaries, ∃ v, root.closure.visits.find? (·.name == b.name) = some v ∧
      v.moduleName = some b.module) ∧
    boundaryEdges root .compilerSimplification = root.closure.candidateEdges ∧
    boundaryEdges root .runtimeReplacement =
      canonicalEdges (root.closure.historyEdges ++ root.closure.currentReplacementEdges)

/-- Every current replacement reference with a history obligation (`historyReplacementEdges`)
is reached in a module whose history its root requested and recorded, and the root's
historical edges are the canonical form of exactly the completed-history edges leaving those
references. -/
def Environment.HistoryEdgesSound (r : Environment) : Prop :=
  ∀ root ∈ r.execution,
    (∀ edge ∈ historyReplacementEdges root, ∃ v mod entry,
      root.closure.visits.find? (·.name == edge.1) = some v ∧ v.moduleName = some mod ∧
      (root.name, mod) ∈ r.census.historyRequests ∧ r.histories.find? (·.1 == mod) = some entry) ∧
    ∃ recorded, canonicalEdges recorded = root.closure.historyEdges ∧
      ∀ e, e ∈ recorded ↔ ∃ edge ∈ historyReplacementEdges root, e.1 = edge.1 ∧
        ∃ v mod entryMod path before after edges,
          root.closure.visits.find? (·.name == edge.1) = some v ∧ v.moduleName = some mod ∧
          r.histories.find? (·.1 == mod) = some (entryMod, .completed path before after edges) ∧
          e ∈ edges

/-- Everything a successful transport validation establishes about a report. -/
def Environment.Admissible (r : Environment) : Prop :=
  r.compilerCapability = Compiler.legacyCompilerTrust ∧
  r.CensusSound ∧ r.ExecutionCensusSound ∧ ExecutionValid r.execution ∧
  r.SourceEvidenceSound ∧ r.RecordedRangesSound ∧ r.AdmissionSound ∧ r.DocumentationSound ∧
  r.HistoryRequestsSound ∧ r.HistoriesSound ∧ r.ReplacementsSound ∧
  r.ClosureAccountSound ∧ r.HistoryEdgesSound

section Soundness
attribute [local simp] and_assoc Bool.and_eq_true beq_iff_eq Array.isEmpty_eq_false_iff
  Array.all_eq_true' Array.any_eq_true' Array.contains_iff_mem String.isEmpty_iff
attribute [-simp] Array.all_eq_true Array.any_eq_true

theorem censusSound_of (r : Environment) (h₁ : r.censusModulesOK = true)
    (h₂ : r.censusDeclarationsOK = true) : r.CensusSound := by
  simp only [Environment.censusModulesOK, Array.contains_eq_mem, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, Array.isEmpty_eq_false_iff, ne_eq, beq_iff_eq,
    Array.all_eq_true', decide_eq_true_eq, and_assoc, Environment.censusDeclarationsOK,
    Prod.forall] at h₁ h₂
  obtain ⟨m₁, m₂, m₃⟩ := h₁
  obtain ⟨d₁, d₂, d₃⟩ := h₂
  exact ⟨m₁, nodup_of_canonicalNames_size _ m₂, m₃, d₂,
    nodup_of_canonicalEdges_size _ d₁, fun k hk => d₃ k.1 k.2 hk⟩


theorem executionCensusSound_of (r : Environment) (h : r.validateExecutionCensus = .ok ()) :
    r.ExecutionCensusSound := by
  unfold Environment.validateExecutionCensus at h
  unfold Environment.ExecutionCensusSound
  cases hroots : r.census.executionRoots <;> simp only [hroots] at h ⊢
  · simpa using h
  · simp only [Array.contains_eq_mem, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true',
      decide_eq_true_eq, Prod.forall, and_assoc, ite_throw_eq_ok, pure_eq_ok, and_true] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    exact ⟨nodup_of_canonicalEdges_size _ h₁, h₂, fun k hk => h₃ k.1 k.2 hk⟩

theorem sourceEvidenceSound_of (r : Environment) (h : r.validateSourceEvidence = .ok ()) :
    r.SourceEvidenceSound := by
  unfold Environment.validateSourceEvidence at h
  simp only [Environment.sourceEvidenceOK, Array.contains_eq_mem, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, String.isEmpty_eq_false_iff, ne_eq,
    decide_eq_true_eq, Array.any_eq_true', and_assoc, ite_throw_eq_ok, pure_eq_ok, and_true] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨nodup_of_canonicalNames_size _ (by simpa using h₁), h₂, h₃, fun d hd => ?_⟩
  obtain ⟨s, hs, hm, hr, -⟩ := h₄ d hd
  exact ⟨s, hs, hm, (Option.all_eq_true _ _).mp hr⟩

/-- Admitted source evidence also holds every range Lean recorded, not only the admitted pair:
each declaration's recorded full and selection ranges are valid in its module's source. With
`sourceEvidenceSound_of` this is all of the requirement on the recorded pair that reads the
source (`Ranges.validForLines_iff_admitted`): what it no longer includes is that the recorded
selection range lies within the recorded full range. -/
theorem recordedRangesValid_of (r : Environment) (h : r.validateSourceEvidence = .ok ()) :
    r.RecordedRangesSound := by
  unfold Environment.validateSourceEvidence at h
  simp only [Environment.sourceEvidenceOK, Array.contains_eq_mem, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, String.isEmpty_eq_false_iff, ne_eq,
    decide_eq_true_eq, Array.any_eq_true', and_assoc, ite_throw_eq_ok, pure_eq_ok, and_true] at h
  intro d hd
  obtain ⟨s, hs, hm, admitted, selection⟩ := h.2.2.2 d hd
  refine ⟨s, hs, hm, fun range recorded => ?_⟩
  simp only [RegulaPolicy.Declaration.ranges, recorded, Option.map_some, Option.all_some]
    at admitted selection
  refine ⟨?_, selection⟩
  have full := RegulaPolicy.Ranges.admitted_validForLines range (s.content.splitOn "\n")
  change range.admitted.validFor s.content = _ at full
  rw [admitted] at full
  cases nested : range.nested
  · simp only [nested, Bool.false_eq_true, ↓reduceIte] at full
    exact full.symm
  · simp only [nested, ↓reduceIte] at full
    exact (RegulaPolicy.Ranges.validForLines_parts full.symm).1

private theorem mem_of_foldl_insert {l : List (Name × Name)} {s : Std.HashSet (Name × Name)}
    {k : Name × Name} (h : (l.foldl (fun s k => s.insert k) s).contains k = true) :
    s.contains k = true ∨ k ∈ l := by
  induction l generalizing s with
  | nil => exact .inl h
  | cons a t ih =>
    rcases ih h with h | h
    · rw [Std.HashSet.contains_insert] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact .inr List.mem_cons_self
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

/-- The executed hash-set membership test decides membership in the required keys. -/
private theorem mem_of_requiredSet_contains {required : Array (Name × Name)} {k : Name × Name}
    (h : (required.foldl (fun s k => s.insert k) ({} : Std.HashSet (Name × Name))).contains
        k = true) :
    k ∈ required := by
  rw [← Array.foldl_toList] at h
  rcases mem_of_foldl_insert h with h | h
  · simp at h
  · simpa using h

theorem admissionSound_of (r : Environment) (receipt : AdmissionReceipt)
    (hr : r.admission = some receipt) (h : r.receiptOK receipt = true) : r.AdmissionSound := by
  simp only [Environment.receiptOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ := h
  simp only [beq_iff_eq, Array.contains_eq_mem, Array.all_eq_true', decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    Prod.forall] at h₁ h₂ h₃ h₄ h₅ h₇
  rw [Array.all_eq_true'] at h₆
  refine ⟨receipt, hr, h₃, nodup_of_canonicalNames_size _ h₁,
    nodup_of_canonicalEdges_size _ h₂, fun k hk => h₄ k.1 k.2 hk, h₅, fun d hd => ?_, h₇⟩
  have h₆ := h₆ d hd
  simp only [Bool.or_eq_true] at h₆
  rcases h₆ with (hu | hp) | hc
  · exact .inl hu
  · exact .inr (.inl hp)
  · exact .inr (.inr (mem_of_requiredSet_contains hc))

theorem documentationSound_of (r : Environment) (docs : DocumentationObservation)
    (hd : r.documentation = some docs) (h : r.documentationOK docs = true) :
    r.DocumentationSound := by
  simp only [Environment.documentationOK, Array.contains_eq_mem, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true', decide_eq_true_eq, Prod.forall, and_assoc] at h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨docs, hd, h₁, nodup_of_canonicalEdges_size _ h₂, fun k hk => h₃ k.1 k.2 hk, h₄⟩

theorem historyRequestsSound_of (r : Environment) (h : r.historyRequestsOK = true) :
    r.HistoryRequestsSound := by
  simp only [Environment.historyRequestsOK, Array.contains_eq_mem, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true', Array.any_eq_true', decide_eq_true_eq, Prod.forall, and_assoc] at h
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨nodup_of_canonicalEdges_size _ h₁, fun request hreq => ?_, h₃⟩
  obtain ⟨⟨e, he, hn⟩, hm⟩ := h₂ request.1 request.2 hreq
  exact ⟨⟨e, he, hn⟩, hm⟩


theorem historiesSound_of (r : Environment)
    (h : ∀ entry ∈ r.histories, r.validateHistory entry = .ok ()) :
    r.HistoriesSound := by
  constructor
  · intro mod path before after edges hmem
    have h := h _ hmem
    unfold Environment.validateHistory at h
    have named : ∀ n : Name, n.isAnonymous = false → n ≠ .anonymous := by
      rintro n hn rfl
      cases hn
    cases hf : r.sourceBindings.find? (·.moduleName == mod) <;>
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        String.isEmpty_eq_false_iff, ne_eq, beq_iff_eq, Array.all_eq_true', Prod.forall, and_assoc,
        hf, bind_pure_comp, id_map', throw_bind, ite_throw_eq_ok, pure_eq_ok, and_true] at h
    · exact ⟨h.1, h.2.1, fun edge he => (h.2.2 edge.1 edge.2 he).imp (named _) (named _), by simp⟩
    · refine ⟨h.1, h.2.1, fun edge he => (h.2.2.1 edge.1 edge.2 he).imp (named _) (named _),
        fun source hs => ?_⟩
      cases hs
      exact h.2.2.2
  · intro mod detail hmem
    have h := h _ hmem
    unfold Environment.validateHistory at h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, String.isEmpty_eq_false_iff,
      ne_eq, Array.all_eq_true', Bool.or_eq_true, bne_iff_ne, Array.any_eq_true', beq_iff_eq,
      Array.isEmpty_eq_false_iff, Prod.forall, ite_throw_eq_ok, pure_eq_ok, and_true] at h
    refine ⟨h.1, fun root hreq => ?_⟩
    obtain ⟨e, he, hn, hu⟩ := (h.2 root mod hreq).resolve_left (by simp)
    exact ⟨e, he, hn, hu⟩

theorem validateRoot_eq_ok (r : Environment) (root : ExecutionRoot)
    (h : r.validateRoot root = .ok ()) :
    (∀ b ∈ root.boundaries, r.validateReplacementBoundary root b = .ok ()) ∧
    r.attributionOK root = true ∧ boundaryChannelsOK root = true ∧
    ∃ expected, (historyReplacementEdges root).foldlM
        (fun acc edge => return acc ++ (← r.recordedHistoryEdges root edge)) #[] = .ok expected ∧
      canonicalEdges expected = root.closure.historyEdges := by
  unfold Environment.validateRoot at h
  simp only [bind_eq_ok] at h
  obtain ⟨⟨⟩, hb, rest⟩ := h
  simp only [beq_iff_eq, throw_bind, ite_throw_eq_ok, bind_eq_ok, pure_eq_ok, and_true] at rest
  exact ⟨forM_eq_ok.mp hb, rest.1, rest.2.1, rest.2.2⟩

/-- A recorded-history lookup succeeds only for a reached, attributed, requested and
recorded replacement reference, and returns exactly its completed-history edges. -/
theorem recordedHistoryEdges_eq_ok (r : Environment) (root : ExecutionRoot) (edge : Name × Name)
    (ys : Array (Name × Name)) (h : r.recordedHistoryEdges root edge = .ok ys) :
    ∃ v mod entryMod outcome,
      root.closure.visits.find? (·.name == edge.1) = some v ∧ v.moduleName = some mod ∧
      (root.name, mod) ∈ r.census.historyRequests ∧
      r.histories.find? (·.1 == mod) = some (entryMod, outcome) ∧
      ∀ e, e ∈ ys ↔ e.1 = edge.1 ∧
        ∃ path before after edges, outcome = .completed path before after edges ∧ e ∈ edges := by
  unfold Environment.recordedHistoryEdges at h
  cases hv : root.closure.visits.find? (·.name == edge.1) with
  | none => simp [hv] at h
  | some v =>
  cases hmod : v.moduleName with
  | none => simp [hv, hmod] at h
  | some mod =>
  cases hfind : r.histories.find? (·.1 == mod) with
  | none => simp [hv, hmod, hfind] at h
  | some entry =>
  obtain ⟨entryMod, outcome⟩ := entry
  simp only [hv, hmod, Array.contains_eq_mem, decide_eq_true_eq, hfind, throw_bind,
    ite_throw_eq_ok] at h
  refine ⟨v, mod, entryMod, outcome, rfl, hmod, h.1, hfind, fun e => ?_⟩
  cases outcome <;> simp only [pure_eq_ok, Array.empty_eq] at h <;> obtain ⟨-, rfl⟩ := h <;>
    simp [and_comm]

theorem historyEdgesSound_of (r : Environment)
    (h : ∀ root ∈ r.execution, ∃ expected, (historyReplacementEdges root).foldlM
        (fun acc edge => return acc ++ (← r.recordedHistoryEdges root edge)) #[] = .ok expected ∧
      canonicalEdges expected = root.closure.historyEdges) :
    r.HistoryEdgesSound := by
  intro root hroot
  obtain ⟨expected, hf, hc⟩ := h root hroot
  obtain ⟨hall, hmem⟩ := foldlM_append_eq_ok hf
  refine ⟨fun edge he => ?_, expected, hc, fun e => ?_⟩
  · obtain ⟨ys, hys⟩ := hall edge he
    obtain ⟨v, mod, entryMod, outcome, hv, hm, hq, hh, -⟩ :=
      recordedHistoryEdges_eq_ok r root edge ys hys
    exact ⟨v, mod, (entryMod, outcome), hv, hm, hq, hh⟩
  · rw [hmem]
    constructor
    · rintro (h | ⟨edge, he, ys, hys, hy⟩)
      · simp at h
      · obtain ⟨v, mod, entryMod, outcome, hv, hm, -, hh, hys⟩ :=
          recordedHistoryEdges_eq_ok r root edge ys hys
        obtain ⟨h₁, path, before, after, edges, rfl, he'⟩ := (hys e).mp hy
        exact ⟨edge, he, h₁, v, mod, entryMod, path, before, after, edges, hv, hm, hh, he'⟩
    · rintro ⟨edge, he, h₁, v, mod, entryMod, path, before, after, edges, hv, hm, hh, he'⟩
      obtain ⟨ys, hys⟩ := hall edge he
      obtain ⟨v', mod', entryMod', outcome, hv', hm', -, hh', hmem'⟩ :=
        recordedHistoryEdges_eq_ok r root edge ys hys
      rw [hv] at hv'
      cases hv'
      rw [hm] at hm'
      cases hm'
      rw [hh] at hh'
      cases hh'
      exact .inr ⟨edge, he, ys, hys, (hmem' e).mpr ⟨h₁, path, before, after, edges, rfl, he'⟩⟩


theorem replacementBoundary_sound (r : Environment) (root : ExecutionRoot) (b : ExecutionBoundary)
    (h : r.validateReplacementBoundary root b = .ok ()) (hk : b.needsHistory = true) :
    (root.name, b.module) ∈ r.census.historyRequests ∧
    (root.unresolved = #[] → ∃ mod path before after edges replacement,
      r.histories.find? (·.1 == b.module) = some (mod, .completed path before after edges) ∧
      b.replacement = some replacement ∧ (b.name, replacement) ∈ edges) := by
  unfold Environment.validateReplacementBoundary at h
  simp only [hk, ite_true] at h
  by_cases hreq : r.census.historyRequests.contains (root.name, b.module) = true
  · refine ⟨Array.contains_iff_mem.mp hreq, fun hu => ?_⟩
    have hu : root.unresolved.isEmpty = true := by simp [hu]
    simp only [hreq, hu, ite_true] at h
    split at h
    · rename_i mod path before after edges hf
      split at h
      · rename_i replacement hrep
        exact ⟨mod, path, before, after, edges, replacement, hf, hrep,
          Array.contains_iff_mem.mp (by simpa using h)⟩
      · simp at h
    · simp at h
  · simp only [Array.contains_eq_mem, decide_eq_true_eq, Array.isEmpty_iff, throw_bind,
      ite_throw_eq_ok] at h
    exact absurd (Array.contains_iff_mem.mpr h.1) hreq


theorem closureAccountSound_of (r : Environment)
    (h : ∀ root ∈ r.execution, r.attributionOK root = true ∧ boundaryChannelsOK root = true) :
    r.ClosureAccountSound := by
  intro root hroot
  obtain ⟨ha, hc⟩ := h root hroot
  simp only [Environment.attributionOK, Bool.and_eq_true, Option.any_eq_true, beq_iff_eq,
    Array.all_eq_true', Option.all_eq_true, Array.contains_eq_mem, decide_eq_true_eq,
    and_assoc] at ha
  simp only [boundaryChannelsOK, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨v, hv, hm⟩, hvisits, hbounds⟩ := ha
  refine ⟨⟨v, hv, hm⟩, fun v hv m hm => hvisits v hv m hm, fun b hb => ?_, hc.1, hc.2⟩
  obtain ⟨w, hw, hwm⟩ := hbounds b hb
  exact ⟨w, hw, hwm⟩

/-- Every report the executed validator admits satisfies every named account. -/
theorem validate_sound (r : Environment) (h : r.validate = .ok ()) : r.Admissible := by
  obtain ⟨hc, hm, hd, he, ⟨i, hi⟩, hs, ⟨receipt, hr, hro⟩, ⟨docs, hdo, hdok⟩, hq, hh, hroots⟩ :=
    (validate_eq_ok r).mp h
  have roots := fun root hroot => validateRoot_eq_ok r root (hroots root hroot)
  exact ⟨hc, censusSound_of r hm hd, executionCensusSound_of r he,
    (admitExecution_preserves _ i hi).2, sourceEvidenceSound_of r hs,
    recordedRangesValid_of r hs,
    admissionSound_of r receipt hr hro, documentationSound_of r docs hdo hdok,
    historyRequestsSound_of r hq, historiesSound_of r hh,
    fun root hroot b hb hk => replacementBoundary_sound r root b ((roots root hroot).1 b hb) hk,
    closureAccountSound_of r (fun root hroot => ⟨(roots root hroot).2.1, (roots root hroot).2.2.1⟩),
    historyEdgesSound_of r fun root hroot => (roots root hroot).2.2.2⟩

end Soundness

/-- A concrete one-module report that the executed validator admits, decided by kernel
reduction: the soundness theorem is not satisfied by an always-refusing validator. -/
theorem validate_nonvacuous : ∃ r : Environment, r.validate = .ok () := by
  let r : Environment := {
    toolchain := "", modules := #[`A], moduleOrigins := #[], declarations := #[], execution := #[]
    compilerCapability := Compiler.legacyCompilerTrust
    census :=
        { modules := #[`A], declarations := #[], executionRoots := none, historyRequests := #[] }
    admission := some
      { modules := #[`A], required := #[], admitted := #[], reused := #[], shared := #[] }
    documentation := some {
      modules := #[(`A, ⟨true, true, []⟩)], materialDeclarations := #[], declarations := #[] }
    sourceBindings := #[{ moduleName := `A, path := "A.lean", content := "" }] }
  refine ⟨r, (validate_eq_ok r).mpr ⟨rfl, by decide +kernel, by decide +kernel, rfl,
    ⟨_, admitExecution_exact _ (by decide +kernel)⟩, ?_, ⟨_, rfl, by decide +kernel⟩,
        ⟨_, rfl, by decide +kernel⟩,
    by decide +kernel, by simp [r], by simp [r]⟩⟩
  change (unless r.sourceEvidenceOK do throw _ : Except AdmissionFailure Unit) = .ok ()
  rw [unless_eq_ok]
  decide +kernel

/-- Required behavior of the executed transport validator, as a sound decision
(`Regula.DecidesSoundly`): every admitted report satisfies every named account, and some report
is admitted. The kind is one-way by design: a refusal fails closed, so no claim is made that
every report satisfying the accounts is admitted (`validate_eq_ok` is two-way against the guard
Booleans, not against `Admissible`). -/
def TransportContract (run : Environment → Except String Unit) : Prop :=
  Regula.DecidesSoundly (· = .ok ()) Environment.Admissible run

/-- Producers, transport decoding and acceptance call `checked_validate.run`, which is
definitionally `Environment.validate`, so this evidence is required at each call site. The
project report worker leaves the call to its coordinator, whose decoder runs it once and
retains the success as an `Admitted` proof; `Acceptance.freezeEnvironment` consumes that proof. -/
theorem checked_validate : Regula.ExecutableContract Environment.validate TransportContract :=
  ⟨⟨validate_sound, validate_nonvacuous⟩⟩

/-- Field decoding only; admission is the separate `checked_validate` step. -/
def Environment.decodeFields (j : Json) : Except String Environment := do
  exactFields j ["toolchain", "compilerCapability", "modules", "moduleOrigins", "declarations", "execution",
    "census", "admission", "documentation", "histories", "sourceBindings"]
  let compilerCapability ← j.getObjValAs? _ "compilerCapability"
  let _ ← Compiler.admitCapability compilerCapability
  return {
    toolchain := ← j.getObjValAs? _ "toolchain"
    compilerCapability
    modules := ← j.getObjValAs? _ "modules"
    moduleOrigins := ← j.getObjValAs? _ "moduleOrigins"
    declarations := ← j.getObjValAs? _ "declarations"
    execution := ← j.getObjValAs? _ "execution"
    census := ← j.getObjValAs? _ "census"
    admission := ← j.getObjValAs? _ "admission"
    documentation := ← j.getObjValAs? _ "documentation"
    histories := ← j.getObjValAs? _ "histories"
    sourceBindings := ← j.getObjValAs? _ "sourceBindings"
  }

instance : FromJson Environment := ⟨fun j => do
  let r ← Environment.decodeFields j
  checked_validate.run r
  return r⟩

/-- Every report the transport decoder returns is admissible. -/
theorem fromJson_admissible (j : Json) (r : Environment)
    (h : (fromJson? j : Except String Environment) = .ok r) : r.Admissible := by
  simp only [fromJson?, bind_eq_ok, pure_eq_ok] at h
  obtain ⟨decoded, -, ⟨⟩, hv, rfl⟩ := h
  exact validate_sound decoded hv

/-- A report together with the proof that the executed validator admitted it. Holding
this value replaces re-running `validate` or `admitExecution` on the same report. -/
structure Admitted where
  /-- The admitted report. -/
  report : Environment
  /-- The executed validator accepted this report. -/
  valid : report.validate = .ok ()

/-- Run `checked_validate` once and retain its success as a proof. -/
def admit (r : Environment) : Except String Admitted :=
  match h : checked_validate.run r with
  | .ok () => .ok ⟨r, h⟩
  | .error detail => .error detail

/-- `admit` refuses exactly as the validator does and otherwise keeps the report intact. -/
theorem admit_eq_ok (r : Environment) (a : Admitted) :
    admit r = .ok a ↔ a.report = r ∧ r.validate = .ok () := by
  unfold admit
  split
  next h =>
    constructor
    · intro e; cases e; exact ⟨rfl, h⟩
    · rintro ⟨rfl, -⟩; rfl
  next detail h =>
    constructor
    · intro e; cases e
    · rintro ⟨-, hv⟩; simp_all [Regula.ExecutableContract.run]

/-- The admitted report's execution inventory, built from the retained proof. -/
def Admitted.execution (a : Admitted) : ExecutionInventory :=
  ⟨a.report.execution, (validate_sound _ a.valid).2.2.2.1⟩

/-- Equal to what `admitExecution` returns on the same roots, for every admitted report:
consumers may use it instead of deciding `ExecutionValid` again. -/
theorem Admitted.admitExecution_eq (a : Admitted) :
    admitExecution a.report.execution = .ok a.execution :=
  admitExecution_exact _ _

/-- The transport decoder with its admission proof: fields, then one `admit`. -/
instance : FromJson Admitted := ⟨fun j => do admit (← Environment.decodeFields j)⟩

/-- The proof-retaining decoder accepts and refuses exactly as the plain decoder does. -/
theorem fromJson_admitted (j : Json) :
    (fromJson? j : Except String Admitted).map (·.report) = fromJson? j := by
  simp only [fromJson?]
  cases Environment.decodeFields j with
  | error => rfl
  | ok r =>
    simp only [bind, Except.bind, admit, Regula.ExecutableContract.run]
    split <;> rename_i h <;> simp [h, Except.map, pure, Except.pure]

/-- A module the audited environment loads from the owned build output although no requested
module or source binding owns it, with the loaded modules that import it directly. -/
structure UnownedModule where
  /-- The module outside every owned module. -/
  «module» : Name
  /-- The loaded modules whose direct imports name it. -/
  importers : Array Name
  deriving Repr, ToJson

instance : FromJson UnownedModule := ⟨fun j => do
  exactFields j ["module", "importers"]
  return {
    «module» := ← j.getObjValAs? _ "module", importers := ← j.getObjValAs? _ "importers" }⟩

/-- The RG2004 detail of one unowned module: the module and the modules that import it, each
named by `importer` (its module name unless given). -/
def UnownedModule.detail (unowned : UnownedModule) (importer : Name → String := toString) :
    String :=
  s!"unexpected-project-module: root-owned module {unowned.module} is outside every Lake \
    library" ++
  (if unowned.importers.isEmpty then ""
  else s!"; imported by {", ".intercalate (unowned.importers.map importer).toList}")

/-- Why a producer completed without a report. The two refusals have different impacts, so
they are distinct constructors, never distinguished by their text. -/
inductive Refusal where
  /-- Required admission or source evidence was unavailable or invalid: incomplete evidence
  (RG2005). -/
  | admission (failure : AdmissionFailure)
  /-- The environment loads owned build output that belongs to no owned module: the owned
  coverage does not match the Lake inventory, a violation (RG2004). -/
  | unowned (modules : Array UnownedModule)
  deriving Repr

/-- The refusal's text: the admission failure's detail, or each unowned module's. -/
def Refusal.detail : Refusal → String
  | .admission failure => failure.detail
  | .unowned modules => "; ".intercalate (modules.map (·.detail)).toList

/-- Successful transport completion is distinct from successful logical admission. -/
inductive Outcome where
  /-- The producer completed and returned its report. -/
  | reported (report : Environment)
  /-- The producer completed without a report because required admission or source evidence
  was unavailable or invalid. -/
  | admissionFailed (failure : AdmissionFailure)
  /-- The producer completed without a report because the environment loads owned build output
  that belongs to no owned module. -/
  | unowned (modules : Array UnownedModule)

/-- A report as `.reported`, and each refusal as its own constructor. -/
def Outcome.ofExcept : Except Refusal Environment → Outcome
  | .ok report => .reported report
  | .error (.admission failure) => .admissionFailed failure
  | .error (.unowned modules) => .unowned modules

instance : ToJson Outcome := ⟨fun
  | .reported report => Json.mkObj [("kind", toJson "reported"), ("report", toJson report)]
  | .admissionFailed failure =>
      Json.mkObj [("kind", toJson "admissionFailed"), ("failure", toJson failure)]
  | .unowned modules => Json.mkObj [("kind", toJson "unowned"), ("modules", toJson modules)]⟩

/-- One outcome grammar for every report decoder `ρ`. -/
def decodeOutcome (ρ : Type) [FromJson ρ] (j : Json) : Except String (Except Refusal ρ) := do
  match ← j.getObjValAs? String "kind" with
  | "reported" =>
    exactFields j ["kind", "report"]
    return .ok (← j.getObjValAs? ρ "report")
  | "admissionFailed" =>
    exactFields j ["kind", "failure"]
    return .error (.admission (← j.getObjValAs? _ "failure"))
  | "unowned" =>
    exactFields j ["kind", "modules"]
    let modules : Array UnownedModule ← j.getObjValAs? _ "modules"
    if modules.isEmpty then throw "empty unowned-module refusal"
    return .error (.unowned modules)
  | _ => throw "unknown environment producer outcome"

instance : FromJson Outcome := ⟨fun j => Outcome.ofExcept <$> decodeOutcome Environment j⟩

/-- The same `Outcome` wire format decoded once into an admitted report. -/
abbrev AdmittedOutcome := Except Refusal Admitted

instance : FromJson AdmittedOutcome := ⟨decodeOutcome Admitted⟩

end Regula.Checker.ProducerReport

-- Exact dependency ceiling for the transport-admission guarantees above: Standard-Logical.
run_cmd do
  for name in #[``Regula.Checker.ProducerReport.validate_eq_ok,
      ``Regula.Checker.ProducerReport.validate_sound,
      ``Regula.Checker.ProducerReport.validate_nonvacuous,
      ``Regula.Checker.ProducerReport.checked_validate,
      ``Regula.Checker.ProducerReport.fromJson_admissible,
      ``Regula.Checker.ProducerReport.admit_eq_ok,
      ``Regula.Checker.ProducerReport.Admitted.admitExecution_eq,
      ``Regula.Checker.ProducerReport.fromJson_admitted] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => #[`propext, `Quot.sound, `Classical.choice].contains ax) do
      throwError "transport theorem {name} exceeds Standard-Logical: {axioms}"
