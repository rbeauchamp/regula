import Regula.Checker.PolicyCodec
import Regula.Checker.Environment
import Regula.Checker.Frontend
import Regula.Checker.Policy

/-! Verbatim source compilation followed by separate typed environment inspection. -/

namespace Regula.Checker.SourceAudit

open Lean System
open scoped Regula.Report
open Regula.Checker

structure SourceSpec where
  «module» : String
  source : String
  warningAsError : Bool := false
  rejectWarnings : Bool := false
  captureRejection : Bool := false
  deriving Repr, ToJson

instance : FromJson SourceSpec := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["module", "source", "warningAsError", "rejectWarnings", "captureRejection"]
  return {
    «module» := ← j.getObjValAs? _ "module"
    source := ← j.getObjValAs? _ "source"
    warningAsError := ← j.getObjValAs? _ "warningAsError"
    rejectWarnings := ← j.getObjValAs? _ "rejectWarnings"
    captureRejection := ← j.getObjValAs? _ "captureRejection"
  }⟩

structure Compilation where
  spec : SourceSpec
  sourcePath : FilePath
  oleanPath : FilePath
  ileanPath : FilePath
  process : ProcessResult
  errors : Option (Array String) := none
  deriving Repr, ToJson

instance : FromJson Compilation := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["spec", "sourcePath", "oleanPath", "ileanPath", "process", "errors"]
  return {
    spec := ← j.getObjValAs? _ "spec"
    sourcePath := ← j.getObjValAs? _ "sourcePath"
    oleanPath := ← j.getObjValAs? _ "oleanPath"
    ileanPath := ← j.getObjValAs? _ "ileanPath"
    process := ← j.getObjValAs? _ "process"
    errors := ← j.getObjValAs? _ "errors"
  }⟩

structure Inspected where
  compilation : Compilation
  report : Regula.Checker.ProducerReport.Environment
  transcripts : Array Frontend.Transcript
  deriving Repr

/-- A worker owns every imported region for one compatible inspection group.
Only JSON data crosses the process boundary; extension-held references die
with the worker instead of accumulating across groups in the coordinator. -/
structure GroupRequest where
  modules : Array Name
  sourceBindings : Array ProducerReport.SourceBinding
  ownedOutput : Option String := none
  includeExecution : Bool := true
  includeModuleOrigins : Bool := true
  deriving ToJson

instance : FromJson GroupRequest := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["modules", "sourceBindings", "ownedOutput", "includeExecution", "includeModuleOrigins"]
  return {
    modules := ← j.getObjValAs? _ "modules"
    sourceBindings := ← j.getObjValAs? _ "sourceBindings"
    ownedOutput := ← j.getObjValAs? _ "ownedOutput"
    includeExecution := ← j.getObjValAs? _ "includeExecution"
    includeModuleOrigins := ← j.getObjValAs? _ "includeModuleOrigins"
  }⟩

structure GroupReport where
  report : Regula.Checker.ProducerReport.Environment
  transcripts : Array Frontend.Transcript
  deriving Repr

unsafe def inspectGroupWorker (request : GroupRequest) : IO ProducerReport.Outcome := do
  let outcome ← SourceBinding.withUnchanged request.sourceBindings #[] do
    let moduleSources := request.sourceBindings.map fun source =>
      (source.moduleName, FilePath.mk source.path)
    let outcome ← Environment.loadReportCurrentSearchPathOutcome request.modules moduleSources
      (request.ownedOutput.map FilePath.mk) request.includeExecution request.includeModuleOrigins
    if let .ok report := outcome then
      if let .error failure := SourceBinding.validateAgainst request.sourceBindings report then
        return .error failure
    return outcome
  return ProducerReport.Outcome.ofExcept (outcome.bind id)

def inspectGroupCurrentSearchPath (modules : Array Name)
    (transcriptSources : Array (Name × FilePath) := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (compiledSources : Array ProducerReport.SourceBinding := #[]) :
    IO (Except ProducerReport.AdmissionFailure GroupReport) := do
  return (← SourceBinding.withUnchanged compiledSources #[] do
    let binary ← workerBinary
    let mut resolvedSources := moduleSources ++ transcriptSources
    for name in modules do
      if !resolvedSources.any (·.1 == name) then
        resolvedSources := resolvedSources.push (name, (← Lean.findOLean name).withExtension "lean")
    let sourceBindings ← SourceBinding.capture resolvedSources
    return (← SourceBinding.withUnchanged sourceBindings #[] do
      unless compiledSources.all sourceBindings.contains do
        return .error ⟨"producer-source: grouped inspection differs from compiled source"⟩
      withScratch (← IO.currentDir) "inspection-group" fun scratch => do
        let input := scratch / "request.json"
        let output := scratch / "report.json"
        let request : GroupRequest := {
          modules
          sourceBindings
          ownedOutput := ownedOutput.map (·.toString)
          includeExecution
          includeModuleOrigins
        }
        writeJson input (toJson request)
        let result ← runProcess (← IO.currentDir) binary.toString
          #["--inspection-group-worker", input.toString, output.toString]
          #[("LEAN_PATH", some (SearchPath.toString (← Lean.searchPathRef.get)))]
        -- Put the actual failure before timing stdout: documentation displays a
        -- bounded diagnostic excerpt, so progress must not hide the rejection.
        if !result.succeeded then throw <| IO.userError (result.stderr ++ result.stdout)
        let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
        let payload ← IO.ofExcept <| readWorkerPacket (toJson request) json
        let outcome : ProducerReport.Outcome ← IO.ofExcept (fromJson? payload)
        SourceBinding.unchanged sourceBindings
        if let .admissionFailed failure := outcome then return .error failure
        let .reported report := outcome
          | throw <| IO.userError "unreachable admission outcome"
        if let .error failure := SourceBinding.validateAgainst sourceBindings report then
          return .error failure
        unless report.census.modules == modules &&
            report.census.executionRoots.isSome == includeExecution do
          throw <| IO.userError "producer-census: inspection response scope mismatch"
        -- The report worker has exited before any frontend imports are loaded.
        -- Each transcript likewise releases its imports before the next one.
        let mut transcripts := #[]
        for (name, path) in transcriptSources do
          let declarations := report.declarations.filter (·.«module» == name)
          if Policy.needsFrontendTranscript declarations then
            transcripts := transcripts.push (← Frontend.buildIsolated name path)
        if let .error failure := SourceBinding.transcriptsMatch sourceBindings transcripts then
          return .error failure
        SourceBinding.unchanged sourceBindings
        return .ok { report, transcripts }
    ).bind id
  ).bind id

private def compileIn (repo scratch : FilePath) (spec : SourceSpec)
    (insideLakeEnv : Bool) : IO (Except ProducerReport.AdmissionFailure Compilation) := do
  let spawn := fun cmd args =>
    if insideLakeEnv then runProcess repo cmd args
    else runProcess repo "lake" (#["env", cmd] ++ args) scrubbedLeanPathEnv
  let sourcePath := scratch / s!"{spec.«module»}.lean"
  let oleanPath := scratch / s!"{spec.«module»}.olean"
  let ileanPath := scratch / s!"{spec.«module»}.ilean"
  if !insideLakeEnv then IO.FS.writeFile sourcePath spec.source
  SourceBinding.withUnchanged #[{
    moduleName := spec.module.toName, path := sourcePath.toString, content := spec.source }] #[] do
    if spec.captureRejection then
      let binary ← workerBinary
      let output := scratch / s!"{spec.«module»}.diagnostics.json"
      let workerStart ← IO.monoMsNow
      let process ← spawn binary.toString
        #["--diagnostic-worker", (Regula.RegistryCodec.nameJson spec.module.toName).compress, sourcePath.toString, output.toString]
      IO.println s!"diagnostic span: compileIn diagnostic-worker: {(← IO.monoMsNow) - workerStart}ms"
      let errors ← if process.succeeded then
          try
            let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
            let payload ← IO.ofExcept <| readWorkerPacket
              (sourceWorkerRequest "diagnostic" spec.module.toName sourcePath spec.source) json
            unless (← IO.FS.readFile sourcePath) == spec.source do throw <| IO.userError "diagnostic snapshot changed"
            pure <| some (← IO.ofExcept <| fromJson? payload)
          catch _ => pure none
        else pure none
      return { spec, sourcePath, oleanPath, ileanPath, process, errors }
    let warningArgs := if spec.warningAsError then #["-DwarningAsError=true"] else #[]
    let args := warningArgs ++
      #["-o", oleanPath.toString, "-i", ileanPath.toString, sourcePath.toString]
    -- The worker sees only the workspace's own search path: an import that the
    -- fresh claimed-surface build did not produce fails here instead of
    -- resolving from the invoking checkout's inherited `LEAN_PATH`.
    let compiler ← if insideLakeEnv then do
        let some path ← IO.getEnv "LEAN"
          | throw <| IO.userError "Lake batch environment has no LEAN executable"
        if path.isEmpty || !(FilePath.mk path).isAbsolute then
          throw <| IO.userError "Lake batch LEAN executable must be absolute"
        pure path
      else pure "lean"
    let compileStart ← IO.monoMsNow
    let process ← spawn compiler args
    IO.println s!"diagnostic span: compileIn compile: {(← IO.monoMsNow) - compileStart}ms"
    return { spec, sourcePath, oleanPath, ileanPath, process }

/-- Standalone compilation still obtains its environment through Lake. -/
def compile (repo scratch : FilePath) (spec : SourceSpec) : IO (Except ProducerReport.AdmissionFailure Compilation) :=
  compileIn repo scratch spec false

structure CompileBatch where
  scratch : FilePath
  jobs : Nat
  specs : Array SourceSpec
  deriving ToJson

instance : FromJson CompileBatch := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["scratch", "jobs", "specs"]
  return {
    scratch := ← j.getObjValAs? _ "scratch"
    jobs := ← j.getObjValAs? _ "jobs"
    specs := ← j.getObjValAs? _ "specs"
  }⟩

/-- Entered only through a scrubbed `lake env` invocation. Each example still
has its own compiler/diagnostic process; only Lake environment setup is shared. -/
def compileBatchWorker (request : CompileBatch) : IO (Array Compilation) := do
  if request.jobs == 0 then throw <| IO.userError "compile batch requires positive jobs"
  let repo ← IO.currentDir
  mapWorkQueue request.jobs request.specs fun spec => do
    IO.ofExcept <| (← compileIn repo request.scratch spec true).mapError (·.detail)

/-- Resolve the complete subprocess environment with Lake once, preserving
PATH, Lean paths, dynamic-loader paths, and all other Lake environment entries. -/
def compileBatch (repo scratch : FilePath) (jobs : Nat) (specs : Array SourceSpec) :
    IO (Except ProducerReport.AdmissionFailure (Array Compilation)) := do
  let sources ← specs.mapM fun spec => do
    let path := scratch / s!"{spec.module}.lean"
    IO.FS.writeFile path spec.source
    pure ({ moduleName := spec.module.toName, path := path.toString, content := spec.source } : ProducerReport.SourceBinding)
  SourceBinding.withUnchanged sources #[] do
    let binary ← workerBinary
    withScratch repo "compile-batch" fun work => do
      let input := work / "request.json"
      let output := work / "result.json"
      writeJson input (toJson ({ scratch, jobs, specs } : CompileBatch))
      let result ← runProcess repo "lake"
        #["env", binary.toString, "--compile-batch-worker", input.toString, output.toString]
        scrubbedLeanPathEnv
      if !result.succeeded then throw <| IO.userError result.output
      let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
      let payload ← IO.ofExcept <| readWorkerPacket (toJson ({ scratch, jobs, specs } : CompileBatch)) json
      let binding (i : Nat) (actual : Compilation) : Bool :=
        match specs[i]? with
        | none => false
        | some expected => toJson actual.spec == toJson expected &&
            actual.sourcePath == scratch / s!"{expected.module}.lean" &&
            actual.oleanPath == scratch / s!"{expected.module}.olean" &&
            actual.ileanPath == scratch / s!"{expected.module}.ilean"
      -- `checked_indexedResults` proves one bound result per request, in request order.
      let compilations ← IO.ofExcept <| admitIndexedWorkerResults specs.size binding payload
      for (expected, actual) in specs.zip compilations do
        unless (← IO.FS.readFile actual.sourcePath) == expected.source do
          throw <| IO.userError "compile batch source snapshot changed"
      return compilations

def compilationPassed (value : Compilation) : Bool :=
  value.process.succeeded
    && (!value.spec.rejectWarnings || (warningLines value.process.output).isEmpty)

/-- A normal compiler exit with a source-located error/warning establishes an emitted
source diagnostic. Crashes, termination and unrelated tool messages remain incomplete.
The pinned compiler's exit and textual diagnostic protocol is a trusted boundary. -/
def sourceDiagnosticFailure (value : Compilation) : Bool :=
  value.process.exitCode ≤ 1 && (outputLines value.process.output).any (fun line =>
    line.startsWith (value.sourcePath.toString ++ ":") && (isErrorLine line || isWarningLine line))

unsafe def inspectOutcome (value : Compilation) (extraSearchRoots : Array FilePath := #[])
    (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none) :
    IO (Except ProducerReport.AdmissionFailure Inspected) := do
  if !compilationPassed value then
    throw <| IO.userError s!"source did not elaborate: {value.spec.«module»}"
  let some scratch := value.sourcePath.parent
    | throw <| IO.userError "compiled source has no parent directory"
  let source : ProducerReport.SourceBinding := {
    moduleName := value.spec.module.toName, path := value.sourcePath.toString, content := value.spec.source }
  return (← SourceBinding.withUnchanged #[source] #[] do
    SourceBinding.unchanged #[source]
    let sources ← SourceBinding.capture (moduleSources.push (source.moduleName, value.sourcePath))
    return (← SourceBinding.withUnchanged sources #[] do
      let reportResult ← Environment.loadReportOutcome #[value.spec.«module».toName] (#[scratch] ++ extraSearchRoots) sourceRoots
        (sources.map fun s => (s.moduleName, FilePath.mk s.path)) ownedOutput
      if let .error failure := reportResult then return .error failure
      let .ok report := reportResult
        | throw <| IO.userError "unreachable admission outcome"
      if let .error failure := SourceBinding.validateAgainst sources report then
        return .error failure
      let declarations := report.declarations
      let transcripts : Array Frontend.Transcript ←
        if Policy.needsFrontendTranscript declarations then
          pure #[← Frontend.build value.spec.«module».toName value.sourcePath extraSearchRoots]
        else pure #[]
      if let .error failure := SourceBinding.transcriptsMatch sources transcripts then
        return .error failure
      SourceBinding.unchanged sources
      SourceBinding.unchanged #[source]
      return .ok { compilation := value, report, transcripts }
    ).bind id
  ).bind id

unsafe def inspect (value : Compilation) (extraSearchRoots : Array FilePath := #[])
    (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none) :
    IO Inspected := do
  IO.ofExcept <| (← inspectOutcome value extraSearchRoots sourceRoots moduleSources ownedOutput).mapError (·.detail)

/-- Inspect with a caller-owned, already configured Lean search path. -/
unsafe def inspectCurrentSearchPath (value : Compilation)
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none) : IO Inspected := do
  if !compilationPassed value then
    throw <| IO.userError s!"source did not elaborate: {value.spec.«module»}"
  let source : ProducerReport.SourceBinding := {
    moduleName := value.spec.module.toName, path := value.sourcePath.toString, content := value.spec.source }
  let outcome ← SourceBinding.withUnchanged #[source] #[] do
    SourceBinding.unchanged #[source]
    let sources ← SourceBinding.capture (moduleSources.push (source.moduleName, value.sourcePath))
    let outcome ← SourceBinding.withUnchanged sources #[] do
      let report ← Environment.loadReportCurrentSearchPath #[value.spec.«module».toName]
        (sources.map fun s => (s.moduleName, FilePath.mk s.path)) ownedOutput
      IO.ofExcept <| (SourceBinding.validateAgainst sources report).mapError (·.detail)
      let declarations := report.declarations
      let transcripts : Array Frontend.Transcript ←
        if Policy.needsFrontendTranscript declarations then
          pure #[← Frontend.buildCurrentSearchPath value.spec.«module».toName value.sourcePath]
        else pure #[]
      IO.ofExcept <| (SourceBinding.transcriptsMatch sources transcripts).mapError (·.detail)
      SourceBinding.unchanged sources
      SourceBinding.unchanged #[source]
      return { compilation := value, report, transcripts }
    IO.ofExcept <| outcome.mapError (·.detail)
  IO.ofExcept <| outcome.mapError (·.detail)

unsafe def compileAndInspect (repo scratch : FilePath) (spec : SourceSpec)
    (extraSearchRoots : Array FilePath := #[]) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none) :
    IO (Except String Inspected) := do
  let compilation ← IO.ofExcept <| (← compile repo scratch spec).mapError (·.detail)
  if !compilationPassed compilation then
    return .error compilation.process.output
  try
    return .ok (← inspect compilation extraSearchRoots sourceRoots moduleSources ownedOutput)
  catch error =>
    return .error s!"{error}\n{compilation.process.output}"

end Regula.Checker.SourceAudit
