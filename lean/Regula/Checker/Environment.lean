import RegulaPolicy.Plan
import Regula.Checker.PolicyCodec
import Regula.Probe
import Regula.Checker.Common
import Regula.Checker.Admission
import Regula.Checker.SourceBinding
import Regula.Linter.Documentation

/-!
# Trusted environment loading

Trusted environment loading for checker policy. The fully qualified reporter
is called directly; audited syntax extensions cannot replace the observation.
-/

namespace Regula.Checker.Environment

open Lean System
open scoped Regula.Report

/-- The checker-owned probe modules force-imported into every report so the
trusted reporter is always available: the probe and its transitive imports
inside the checker library. They are never part of an audited surface, so
their presence in an environment is not evidence about the claimed modules.

The force import loads the whole import closure of `Regula.Probe` into the audited
environment, and the gate's excluded-module scan (`AxiomGate.auditSurfaceAt`) exempts only
`RegulaPolicy.infrastructureModuleNames`. So every module of that closure outside the
toolchain (roots `Init`, `Std`, `Lean` and `Lake`) is a `RegulaPolicy` module or one of
`RegulaPolicy.infrastructureModuleNames`: in a project that hosts this package and claims
`RegulaPolicy`, the scan then reports no module that only the probe loaded. The command
below refuses to elaborate this module otherwise. It walks the imports recorded in the module
data this module loaded, starting at `Regula.Probe`, so it is a fact about this package's
modules as built here. `infrastructureOrigins` authenticates the infrastructure modules'
artifacts in an audited environment; what the `RegulaPolicy` names resolve to there is the
audited project's own build, which this command does not see. -/
def probeModuleNames : Array String :=
  RegulaPolicy.reporterModuleNames.map (·.toString)

run_cmd do
  let env ← getEnv
  let mut pending := [`Regula.Probe]
  let mut closure : NameSet := {}
  repeat
    let name :: rest := pending | break
    pending := rest
    if closure.contains name then continue
    closure := closure.insert name
    let some data := (env.getModuleIdx? name).bind fun index =>
        env.header.moduleData[(index : Nat)]?
      | throwError "probe import closure: module {name} is not loaded"
    pending := data.imports.toList.map (·.module) ++ pending
  for name in closure do
    unless #[`Init, `Std, `Lean, `Lake, `RegulaPolicy].contains name.getRoot ||
        RegulaPolicy.infrastructureModuleNames.contains name do
      throwError "probe import closure: {name} is neither a RegulaPolicy module nor one of \
        RegulaPolicy.infrastructureModuleNames, so a project that hosts this package and \
        excludes its library would import an excluded module through the force-loaded probe; \
        move what the probe needs from it into RegulaPolicy"

/-- The probe modules no claimed module may import. `Regula.Contract` (the
executable-contract interface, standard §7.11), `Regula.MaterialClaim` (the
`@[regula_material]` registration, §5.2) and `Regula.Decision` (the `@[regula_decision]`
registration, §7.11) are the published interfaces a claimed surface
imports by design (§7.10); the probe and its report records are
checker tooling that reach an audited environment only through the force
import, never through a claimed module's own imports. -/
def probeOnlyModuleNames : Array String :=
  RegulaPolicy.reporterOnlyModuleNames.map (·.toString)

/-- The checker-owned probe module force-imported into every report so the
trusted reporter is always available. It is never part of an audited surface. -/
def probeModuleName : String := "Regula.Probe"

/-- Imported module metadata, before any declaration admission or policy inspection. A clear
graph permits inspection to continue; this observation grants no acceptance authority. -/
structure ModuleGraph where
  /-- Every loaded module, in the complete report's canonical name order. -/
  modules : Array Name
  /-- The canonical artifact and recorded direct imports of every loaded module. -/
  moduleOrigins : Array Regula.Report.ModuleOrigin
  deriving ToJson

instance : FromJson ModuleGraph := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["modules", "moduleOrigins"]
  return { modules := ← j.getObjValAs? _ "modules"
           moduleOrigins := ← j.getObjValAs? _ "moduleOrigins" }⟩

/-- The same module metadata carried by a completed report, without its policy observations. -/
def ModuleGraph.ofReport (report : ProducerReport.Environment) : ModuleGraph :=
  ⟨report.modules, report.moduleOrigins⟩

/-- The reporter also force-loads this public, neutral name codec. Its presence is
not a source import of excluded policy machinery. Validate the exact durable artifact
before distinguishing it from a claimed module's ordinary imports. -/
private def forcedPublicModule (moduleOrigins : Array Regula.Report.ModuleOrigin) (name : Name)
    (description : String) : IO Name := do
  let origins := moduleOrigins.filter (·.name == name)
  let some origin := origins[0]? | throw <| IO.userError s!"missing {description} origin"
  unless origins.size == 1 do throw <| IO.userError s!"ambiguous {description} origin"
  let some lib ← checkerPackageLibDir | throw <| IO.userError "checker library path unavailable"
  let expected ← IO.FS.realPath (Lean.modToFilePath lib name "olean")
  unless (← IO.FS.realPath origin.olean) == expected do
    throw <| IO.userError s!"{description} origin mismatch"
  return name

/-- Returns `Regula.StructuralName` after checking that the report records exactly one origin
for it and that its `.olean` is the running checker's own artifact; throws otherwise. -/
def forcedStructuralName (report : Regula.Checker.ProducerReport.Environment) : IO Name :=
  forcedPublicModule report.moduleOrigins `Regula.StructuralName "structural-name codec"

private def forcedCollectorFrom (origins : Array Regula.Report.ModuleOrigin) :
    IO (Option Name) := do
  let name ← forcedPublicModule origins `Regula.Collect "shared collector"
  if origins.any (fun origin =>
      !probeModuleNames.contains origin.name.toString && origin.imports.contains name) then
    return none
  return some name

private def forcedCompilerObserverFrom (origins : Array Regula.Report.ModuleOrigin) :
    IO (Option Name) := do
  let name ← forcedPublicModule origins `Regula.CompilerObservation "compiler capability observer"
  let collector ← forcedCollectorFrom origins
  if origins.any (fun origin => origin.imports.contains name &&
      !(RegulaPolicy.reporterModuleNames.contains origin.name || some origin.name == collector)) then
    return none
  return some name

/-- The extracted constructor is also force-loaded by Probe. Its artifact must
be the checker's exact artifact. Unlike the neutral name codec, it remains in
the excluded-library scan whenever another module actually imports it. -/
def forcedCollectorOnly (report : Regula.Checker.ProducerReport.Environment) : IO
    (Option Name) := forcedCollectorFrom report.moduleOrigins

/-- The compiler observer is infrastructure only through authenticated reporters or an
already force-only collector. A claimed import of either module keeps it in the owned scan. -/
def forcedCompilerObserverOnly (report : Regula.Checker.ProducerReport.Environment) : IO
    (Option Name) := forcedCompilerObserverFrom report.moduleOrigins

/-- The ordinary loaded modules after authenticating the existing force-only exemptions. -/
def ModuleGraph.ordinaryModules (graph : ModuleGraph) : IO (Array Name) := do
  let codec ← forcedPublicModule graph.moduleOrigins `Regula.StructuralName "structural-name codec"
  let collector ← forcedCollectorFrom graph.moduleOrigins
  let observer ← forcedCompilerObserverFrom graph.moduleOrigins
  return graph.modules.filter fun name =>
    !(probeModuleNames.map String.toName).contains name && name != codec &&
      some name != collector && some name != observer

/-- Bind this environment's requested roots and every other positively assigned module it
loads before using the graph for violations. Excluded modules remain scope observations. -/
def ModuleGraph.scopeRequests (graph : ModuleGraph) (requested assigned : Array Name) :
    Array Name :=
  requested ++ assigned.filter (fun name => graph.modules.contains name && !requested.contains name)

/-- The early binding domain always retains every requested root. -/
theorem ModuleGraph.scopeRequests_requested (graph : ModuleGraph) (requested assigned : Array Name)
    (name : Name) (present : name ∈ requested) : name ∈ graph.scopeRequests requested assigned := by
  simp [scopeRequests, present]

/-- Every positively assigned module loaded in this environment receives the same origin
guard as its requested roots, including positive dependencies owned by another environment. -/
theorem ModuleGraph.scopeRequests_loaded (graph : ModuleGraph) (requested assigned : Array Name)
    (name : Name) (positive : name ∈ assigned) (loaded : name ∈ graph.modules) :
    name ∈ graph.scopeRequests requested assigned := by
  by_cases present : name ∈ requested
  · exact graph.scopeRequests_requested requested assigned name present
  · simp [scopeRequests, positive, loaded, present]

/-- Bind every requested module to a unique origin under the Lake output directory before
using its graph for scope findings. The completed-report check uses this same predicate. -/
def ModuleGraph.requestedFailures (graph : ModuleGraph) (ordinary requested : Array Name)
    (ownedOutput : FilePath) : IO (Array String) := do
  let mut failures := #[]
  for name in requested do
    unless ordinary.contains name do
      failures := failures.push s!"surface-omission: Lake module {name} was not elaborated"
    let origins := graph.moduleOrigins.filter (·.name == name)
    let fresh ← match origins[0]? with
      | some origin => pathWithin (FilePath.mk origin.olean) ownedOutput
      | none => pure false
    if origins.size != 1 || !fresh then
      failures := failures.push
        s!"surface-not-fresh: {name} did not resolve from the fresh Lake output"
  return failures

/-- Root-output modules outside the requested or source-bound ownership, retaining every
direct importer in header order. The metadata phase and full loader share this refusal. -/
def ModuleGraph.unownedModules (graph : ModuleGraph) (owned : Array Name)
    (ownedOutput : FilePath) : IO (Array ProducerReport.UnownedModule) := do
  let mut unowned := #[]
  for origin in graph.moduleOrigins do
    if !owned.contains origin.name && !probeModuleNames.contains origin.name.toString then
      if ← pathWithin (FilePath.mk origin.olean) ownedOutput then
        unowned := unowned.push origin.name
  return unowned.map fun name => {
    «module» := name
    importers := graph.moduleOrigins.filterMap fun origin =>
      if origin.imports.any (· == name) then some origin.name else none }

/-- A forbidden edge retained with its exact membership in the observed import graph. -/
private structure ReporterImport (origins : Array Regula.Report.ModuleOrigin) where
  origin : Regula.Report.ModuleOrigin
  present : origin ∈ origins
  imported : Name
  direct : imported ∈ origin.imports
  outside : origin.name ∉ RegulaPolicy.reporterModuleNames
  forbidden : imported ∈ RegulaPolicy.reporterOnlyModuleNames

/-- Each retained edge contradicts the actual infrastructure predicate on the same origins. -/
private theorem ReporterImport.incompatible (claim : RegulaPolicy.Claim)
    (census : RegulaPolicy.EnvironmentCensus) (edge : ReporterImport census.origins) :
    ¬ RegulaPolicy.InfrastructureOK claim census := by
  intro valid
  exact edge.outside
    ((valid.2.2.2.2.1 edge.origin edge.present edge.imported edge.direct edge.forbidden).1)

/-- Collect direct reporter imports in their original order, carrying the rejection witness. -/
private def reporterImports (origins : Array Regula.Report.ModuleOrigin) :
    Array (ReporterImport origins) := Id.run do
  let mut result := #[]
  for present : origin in origins do
    if outside : origin.name ∉ RegulaPolicy.reporterModuleNames then
      for direct : imported in origin.imports do
        if forbidden : imported ∈ RegulaPolicy.reporterOnlyModuleNames then
          result := result.push ⟨origin, present, imported, direct, outside, forbidden⟩
  return result

/-- The scope violations witnessed by imported metadata. Callers first authenticate the
force-only exemptions with `ordinaryModules`; the early path also requires `requestedFailures`
to be empty. Both paths use the same Lake-owned scope and graph fields here. -/
def ModuleGraph.importDetails (graph : ModuleGraph) (ordinary excluded configured : Array Name)
    (ownedOutput : FilePath) (library : String) : IO (Array String) := do
  let mut details := #[]
  for name in ordinary do
    if excluded.contains name then
      details := details.push s!"unexpected-project-module: excluded module \
        {name} was imported into positive library {library}"
  for edge in reporterImports graph.moduleOrigins do
    details := details.push s!"unexpected-project-module: checker probe \
      module {edge.imported} was imported into positive library {library} \
      by {edge.origin.name}"
  for origin in graph.moduleOrigins do
    if (probeModuleNames.map String.toName).contains origin.name then continue
    if ← pathWithin (FilePath.mk origin.olean) ownedOutput then
      if !configured.contains origin.name then
        details := details.push s!"unexpected-project-module: root-owned \
          module {origin.name} is outside every manifested Lake library"
  return details

/-- Authenticate the narrow infrastructure partition against the running checker's
canonical artifacts, retaining the request snapshot. Import restrictions are subsequently
rechecked over the complete census by `InfrastructureOK`; these receipts alone do not
allow a source import of a reporter or change any replay ownership. -/
def infrastructureOrigins (snapshot : RegulaPolicy.AdmittedSnapshot)
    (report : ProducerReport.Environment) : IO (Array RegulaPolicy.InfrastructureOrigin) := do
  let some lib ← checkerPackageLibDir
    | throw <| IO.userError "checker library path unavailable"
  let collector ← forcedCollectorOnly report
  let observer ← forcedCompilerObserverOnly report
  let mut receipts := #[]
  for name in RegulaPolicy.infrastructureModuleNames do
    if name == `Regula.Collect && collector.isNone then continue
    if name == `Regula.CompilerObservation && observer.isNone then continue
    let origins := report.moduleOrigins.filter (·.name == name)
    let some origin := origins[0]?
      | throw <| IO.userError s!"missing infrastructure origin: {name}"
    unless origins.size == 1 do
      throw <| IO.userError s!"ambiguous infrastructure origin: {name}"
    let expected ← IO.FS.realPath (Lean.modToFilePath lib name "olean")
    let actual ← IO.FS.realPath origin.olean
    unless origin.olean == actual.toString do
      throw <| IO.userError s!"noncanonical infrastructure origin: {name}"
    let key : RegulaPolicy.ModuleKey := ⟨snapshot, ← IO.ofExcept (RegulaPolicy.admitIdentity name)⟩
    receipts := receipts.push (← IO.ofExcept <|
      RegulaPolicy.admitInfrastructureOrigin key actual.toString expected.toString)
  return receipts

/-- One memoized replacement-history worker run: its complete inputs and the exact bytes
it wrote. A record is used only when every input is equal to the requester's own. -/
private structure HistoryMemo where
  moduleName : String
  source : String
  sourceBefore : String
  searchIdentity : String
  binary : String
  output : String
  deriving ToJson, FromJson, BEq

/-- The history worker's output bytes for exactly these inputs, shared by the surface
workers of one audit through `memo` (a directory the coordinator owns for the audit).
Trusted assumption (the §7.5 supported-process boundary): the worker's output is a
deterministic function of the module source, the effective search path (`searchIdentity`,
see `loadReportCore`) and the pinned binary, with the audit's inherited environment and
unchanged imported artifacts. Every field is compared exactly before a record is used, so
under that assumption a reused record carries the bytes this worker would have produced;
the requester still validates the packet and its own before/after source comparison. The first
worker
to claim a key (an exclusive-create lock) runs the subprocess; the others wait for its
record, and run the subprocess themselves if the record does not appear or does not match.
Without `memo`, or on any memo failure, the worker runs as before; a failure to publish a
record never changes the returned output. -/
private def historyWorkerOutput (memo : Option FilePath) (inputs : HistoryMemo)
    (run : IO String) : IO String := do
  let some directory := memo | run
  let key := toString (hash (inputs.moduleName, inputs.source, inputs.sourceBefore,
    inputs.searchIdentity, inputs.binary))
  let record := directory / s!"{key}.json"
  let lock := directory / s!"{key}.lock"
  let reuse : IO (Option String) := do
    unless ← record.pathExists do return none
    let stored : HistoryMemo ← IO.ofExcept <| (Json.parse (← IO.FS.readFile record)).bind fromJson?
    return if { stored with output := "" } == inputs then some stored.output else none
  if let some output ← (reuse <|> pure none) then return output
  let claimed ← (do discard <| IO.FS.Handle.mk lock .writeNew; pure true) <|> pure false
  if claimed then
    try
      -- Another worker may have published while this one claimed the key.
      if let some output ← (reuse <|> pure none) then return output
      let output ← run
      try
        let staged := directory / s!"{key}.staged"
        IO.FS.writeFile staged (toJson { inputs with output }).compress
        IO.FS.rename staged record
      catch _ => pure ()
      return output
    finally
      try IO.FS.removeFile lock catch _ => pure ()
  -- Another worker holds the key: wait while it does, for at most ten minutes (beyond the
  -- audit's own deadline), then compute here.
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) - start < 600000 do
    if let some output ← (reuse <|> pure none) then return output
    unless ← lock.pathExists do
      if let some output ← (reuse <|> pure none) then return output
      break
    IO.sleep 50
  run

/-- Re-elaboration recovers overwritten `implemented_by` choices that neither
the final attribute map nor optimized IR preserves. Isolate the frontend's
initializers, memoize once per module in one worker, and share the worker output across
the audit's workers through `historyWorkerOutput`. -/
private def replacementHistory (sourceRoots : Array FilePath)
    (moduleSources : Array (Name × FilePath)) (moduleName : Name)
    (memo : Option (FilePath × String) := none) :
    IO ProducerReport.HistoryOutcome := do
  try
    let olean ← Lean.findOLean moduleName
    let alongside := olean.withExtension "lean"
    -- Owned modules use their exact Lake-resolved source. Prefix-based source
    -- search can otherwise stop at an unrelated dependency directory such as
    -- proofwidgets/Widget before reaching the adopter's actual Widget.lean.
    let source ← if let some (_, source) := moduleSources.find? (·.1 == moduleName) then
        pure source
      else if ← alongside.pathExists then pure alongside else
        Lean.findLean (sourceRoots.toList ++ (← Lean.getSrcSearchPath) ++
          [(← Lean.findSysroot) / "src" / "lean"])
          moduleName
    let some bin := (← IO.appPath).parent
      | throw <| IO.userError "checker binary directory unavailable"
    withScratch (← IO.currentDir) "replacement-history" fun scratch => do
      let output := scratch / "history.json"
      let sourceBefore ← IO.FS.readFile source
      let request := sourceWorkerRequest "history" moduleName source sourceBefore
      let searchPath := System.SearchPath.toString (← Lean.searchPathRef.get)
      let inputs : HistoryMemo := {
        moduleName := (Regula.RegistryCodec.nameJson moduleName).compress, source := source.toString
        sourceBefore, searchIdentity := (memo.map (·.2)).getD searchPath
        binary := (bin / "axiomGate").toString, output := "" }
      let written ← historyWorkerOutput (memo.map (·.1)) inputs do
        let result ← IO.Process.output {
          cmd := (bin / "axiomGate").toString
          args :=
              #["--replacement-history-worker", (Regula.RegistryCodec.nameJson moduleName).compress,
                  source.toString,
            output.toString]
          env := #[("LEAN_PATH", some searchPath)] }
        if result.exitCode != 0 then
          throw <| IO.userError s!"{result.stdout}{result.stderr}"
        IO.FS.readFile output
      let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse written
      let payload ← IO.ofExcept <| readWorkerPacket request json
      let sourceAfter ← IO.FS.readFile source
      unless sourceAfter == sourceBefore do
        throw <| IO.userError "replacement history source changed"
      let edges : Array (Name × Name) ← IO.ofExcept <| fromJson? payload
      return .completed source.toString sourceBefore sourceAfter edges
  catch error => return .unavailable error.toString

/-- The import operation shared by metadata refusal and full declaration reporting. -/
private unsafe def importReportEnvironment (modules : Array Name) : IO Lean.Environment := do
  if modules.isEmpty || modules.toList.eraseDups.length != modules.size then
    throw <| IO.userError "environment report requires unique nonempty modules"
  Lean.enableInitializersExecution
  let importNames :=
    if modules.contains probeModuleName.toName then modules
    else modules.push probeModuleName.toName
  let imports := importNames.map fun module => ({ module, importAll := true } : Import)
  timedPhase "environment imports" <| importModules imports {} 0 (loadExts := true)
    (level := .private)

private unsafe def loadReportCoreAtSearchPath (modules : Array Name)
    (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (validateReport : Bool := true) (historyMemo : Option (FilePath × String) := none)
    (priors : Array Admission.PriorAdmission := #[])
    (publish : Option FilePath := none) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) := do
  if modules.isEmpty || modules.toList.eraseDups.length != modules.size then
    throw <| IO.userError "environment report requires unique nonempty modules"
  let mut resolvedSources := moduleSources
  for name in modules do
    if !resolvedSources.any (·.1 == name) then
      -- Compiled verbatim snippets live alongside their exact isolated source.
      -- Ordinary project modules already have authoritative Lake source entries.
      let source := (← Lean.findOLean name).withExtension "lean"
      resolvedSources := resolvedSources.push (name, source)
  let sourceBindings ← SourceBinding.capture resolvedSources
  return (← SourceBinding.withUnchanged
      (α := Except ProducerReport.Refusal ProducerReport.Environment) sourceBindings #[] do
    let requested := modules
    let env ← importReportEnvironment requested
    let ownedModules := requested ++ moduleSources.map (·.1) |>.filter
      (fun name => !probeModuleNames.contains name.toString)
    let loadedOrigins ← Regula.Probe.loadedModuleOrigins env
    let graph : ModuleGraph := ⟨RegulaPolicy.canonicalNames env.header.moduleNames, loadedOrigins⟩
    -- Kernel admission cannot classify a module loaded from the owned output that no requested
    -- module or source binding owns, so the environment is refused with those modules and their
    -- direct importers: a coverage violation, not a failed inspection.
    if let some root := ownedOutput then
      let unowned ← graph.unownedModules ownedModules root
      unless unowned.isEmpty do
        return .error (.unowned unowned)
    let origins := if priors.isEmpty && publish.isNone then #[] else loadedOrigins
    let reused := if priors.isEmpty then #[] else
      Admission.reusedModules env origins ownedModules priors
    let admissionResult ← timedPhase "kernel admission" <|
      Admission.validate env ownedModules reused requested
    if let .error failure := admissionResult then return .error (.admission failure)
    let .ok admission := admissionResult
      | throw <| IO.userError "unreachable admission outcome"
    -- Later environments of the audit may start from this admission while the report below is
    -- still being built; the coordinator compares it with the finished report
    -- (`Inspection.inspect`). The rename makes the file appear complete or not at all.
    if let some path := publish then
      let staged := path.addExtension "staged"
      IO.FS.writeFile staged
        (toJson ({ receipt := admission, origins } : Admission.Completed)).compress
      IO.FS.rename staged path
    -- Freeze the selector from the completed environment before reading docstrings.
    -- Loading server/private data above is necessary for both Lean doc formats.
    let own := Regula.Probe.ownedConstants env requested.toList
    let mut selected := #[]
    for (name, _) in own do
      if Regula.Linter.Documentation.selected env name then
        let some idx := env.getModuleIdxFor? name
          | throw <| IO.userError s!"material declaration has no module: {name}"
        selected := selected.push (env.header.modules[(idx : Nat)]!.module, name)
    let documentation : Regula.Checker.ProducerReport.DocumentationObservation := {
      -- RG5001 reads each module's header from the exact bound source text.
      modules := ← requested.mapM fun name => do
        let some binding := sourceBindings.find? (·.moduleName == name)
          | throw <| IO.userError s!"module-header: no bound source for {name}"
        return (name, ← Regula.Linter.Documentation.moduleObservation env name binding.content
          binding.path)
      materialDeclarations := selected
      declarations := ← selected.mapM fun key => do
        return (key, ← Lean.findDocString? env key.2)
    }
    let histories ← IO.mkRef ({} : NameMap ProducerReport.HistoryOutcome)
    let loadHistory (moduleName : Name) := do
      if let some result := (← histories.get).find? moduleName then return result.edges
      let result ← replacementHistory sourceRoots resolvedSources moduleName historyMemo
      histories.modify (·.insert moduleName result)
      return result.edges
    let ctx : Elab.Command.Context := {
      fileName := "<trusted-environment-probe>"
      fileMap := FileMap.ofString ""
      snap? := none
      cancelTk? := none
    }
    let state := Elab.Command.mkState env
    match ← timedPhase "declaration report" <| EIO.toIO' <|
        (Regula.Probe.environmentReport requested.toList loadHistory includeExecution
            includeModuleOrigins).run ctx |>.run state with
    | .error ex => throw <| IO.userError (← ex.toMessageData.toString)
    | .ok (report, _) =>
      let historyTable ← histories.get
      let historyKeys := RegulaPolicy.canonicalNames (historyTable.toArray.map (·.1))
      let historyRecords ← historyKeys.mapM fun name => do
        let some outcome := historyTable.find? name
          | throw <| IO.userError "producer-history: missing recorded lookup"
        pure (name, outcome)
      let report : ProducerReport.Environment := {
        toCollected := report
        admission := some admission
        documentation := some documentation
        histories := historyRecords
        sourceBindings := sourceBindings.filter (fun s => report.modules.contains s.moduleName)
      }
      SourceBinding.unchanged report.sourceBindings
      if let .error failure := report.validateSourceEvidence then return .error (.admission failure)
      -- The project coordinator's decoder runs this exact check once and keeps its success as a
      -- `ProducerReport.Admitted` proof for `Acceptance.freezeEnvironment`; only that caller opts
      -- out.
      if validateReport then IO.ofExcept (ProducerReport.checked_validate.run report)
      return .ok report
  ).mapError ProducerReport.Refusal.admission |>.bind id

/-- Lean resolves a whole module prefix at the first matching directory.
A fresh project that builds only `Contract` must not mask the trusted probe,
and putting the entire checker output first would mask fresh audited modules.
Expose only the checker-owned prefix ahead of the audited search roots. -/
private def withProbeSearch {α : Type} (action : String → IO α) : IO α := do
  let some selfLib ← checkerPackageLibDir
    | throw <| IO.userError "trusted checker library directory unavailable"
  withScratch (← IO.currentDir) "probe-search" fun overlay => do
    let probeDirectory ← IO.FS.realPath (selfLib / "Regula")
    let linked ← runProcess overlay "ln" #["-s", probeDirectory.toString,
      (overlay / "Regula").toString]
    if !linked.succeeded then
      throw <| IO.userError s!"could not expose trusted probe prefix: {linked.output}"
    let oldSearchPath ← Lean.searchPathRef.get
    Lean.searchPathRef.set (overlay :: oldSearchPath)
    -- The overlay holds only the `Regula` link to `probeDirectory`, so the effective search
    -- path is determined by that directory and the search path below it. Shared history
    -- worker output is keyed on this identity, not on the per-worker overlay name.
    let searchIdentity := s!"probe={probeDirectory};path={System.SearchPath.toString oldSearchPath}"
    try action searchIdentity
    finally Lean.searchPathRef.set oldSearchPath

private unsafe def loadReportCore (modules : Array Name) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (validateReport : Bool := true) (historyMemo : Option FilePath := none)
    (priors : Array Admission.PriorAdmission := #[]) (publish : Option FilePath := none) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) :=
  withProbeSearch fun searchIdentity =>
    loadReportCoreAtSearchPath modules sourceRoots moduleSources ownedOutput includeExecution
      includeModuleOrigins validateReport (historyMemo.map (·, searchIdentity)) priors publish

private def withReportSearchRoots {α : Type} (extraSearchRoots : Array FilePath)
    (action : IO α) : IO α := do
  let selfLib ← checkerPackageLibDir
  let oldSearchPath ← Lean.searchPathRef.get
  Lean.searchPathRef.set (extraSearchRoots.toList ++ selfLib.toList ++ oldSearchPath)
  try action finally Lean.searchPathRef.set oldSearchPath

/-- Read only the loaded module graph through the full reporter's import and search setup.
The caller binds source bytes; the result has no declaration, admission, or success fields. -/
unsafe def loadModuleGraph (modules : Array Name) (searchRoots : Array FilePath) :
    IO ModuleGraph :=
  withReportSearchRoots searchRoots <| withProbeSearch fun _ => do
    let env ← importReportEnvironment modules
    return { modules := RegulaPolicy.canonicalNames env.header.moduleNames
             moduleOrigins := ← Regula.Probe.loadedModuleOrigins env }

/-- Load exact modules using the already configured search path. This variant
supports bounded parallel, read-only imports while a caller owns the global
search-path scope. -/
unsafe def loadReportCurrentSearchPathOutcome (modules : Array Name)
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) :=
  loadReportCore modules #[] moduleSources ownedOutput includeExecution includeModuleOrigins

/-- Load exact modules through Lean's import semantics and return their typed
declaration report. Extra search roots are temporary and restored afterward. Kernel admission
reuses the admission `priors` completed for owned modules (`Admission.reusedModules`), and its
receipt and module origins are written to `publish` (`Admission.Completed`) as soon as it
succeeds. -/
unsafe def loadReportOutcome (modules : Array Name)
    (extraSearchRoots : Array FilePath := #[]) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (validateReport : Bool := true) (historyMemo : Option FilePath := none)
    (priors : Array Admission.PriorAdmission := #[]) (publish : Option FilePath := none) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) :=
  withReportSearchRoots extraSearchRoots <|
    loadReportCore modules sourceRoots moduleSources ownedOutput includeExecution
      includeModuleOrigins validateReport historyMemo priors publish

/-- Compatibility wrapper for callers that report every refusal as an inspection failure at their
own stage. Public rule adapters use the typed outcome variant above. -/
unsafe def loadReportCurrentSearchPath (modules : Array Name)
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    IO ProducerReport.Environment := do
  IO.ofExcept <| (← loadReportCurrentSearchPathOutcome modules moduleSources ownedOutput
    includeExecution includeModuleOrigins).mapError (·.detail)

/-- `loadReportOutcome` with any refusal raised as an `IO` error carrying its detail. -/
unsafe def loadReport (modules : Array Name)
    (extraSearchRoots : Array FilePath := #[]) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownedOutput : Option FilePath := none)
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    IO ProducerReport.Environment := do
  IO.ofExcept <| (← loadReportOutcome modules extraSearchRoots sourceRoots moduleSources ownedOutput
    includeExecution includeModuleOrigins).mapError (·.detail)

end Regula.Checker.Environment
