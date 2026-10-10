import RegulaPolicy.Acceptance
import RegulaCore.Assembly
import Regula.Checker.Environment
import Regula.Checker.Lake
import Regula.Checker.Snapshot

/-! # Operational acceptance bridge

Operational bridge to the pure, request-indexed acceptance boundary. The census
comes from Lake and completed producer extraction before policy jobs are collected.
Raw packets never carry proofs. Canonical path resolution, source stability, Lean/Lake
extraction, process completion and compiled execution remain trusted IO boundaries.
The checked collection architecture is informed by con-leche's CheckedRecord,
collectChecks, FullyChecked and checkDeclsIO; no con-leche dependency is introduced. -/
namespace Regula.Checker.Acceptance
open Lean System RegulaPolicy
open scoped Regula.Report

/-- One independently requested report and its completed raw observations. The expected
module array is supplied by the coordinator's discovery, never copied from the response.
The report is held with its transport admission proof, so freezing never re-validates it. -/
structure RequestedInspection where
  /-- The modules the coordinator requested this report for, from its own discovery. -/
  expectedModules : Array Name
  /-- The producer's environment report, with the proof that it passed transport validation. -/
  admitted : ProducerReport.Admitted
  /-- The frontend transcripts the producer recorded while elaborating those modules. -/
  transcripts : Array RegulaPolicy.Frontend.Transcript
  /-- The modules of owned dependencies the coordinator's module graph shows this report must
  inspect with its own (`Environment.EnvironmentOwnership.dependencies`). -/
  expectedDependencies : Array Name := #[]
  /-- The source bindings of those modules, each from the owned package the environment loads it
  from (`Environment.dependencyBindings`). -/
  dependencySources : Array ProducerReport.SourceBinding := #[]

/-- The admitted report itself. -/
abbrev RequestedInspection.report (inspection : RequestedInspection) : ProducerReport.Environment :=
  inspection.admitted.report

instance : ToJson RequestedInspection := ⟨fun value => Json.mkObj [
  ("expectedModules", toJson value.expectedModules), ("report", toJson value.report),
  ("transcripts", toJson value.transcripts),
  ("expectedDependencies", toJson value.expectedDependencies),
  ("dependencySources", toJson value.dependencySources)]⟩

instance : FromJson RequestedInspection := ⟨fun value => do
  PolicyCodec.exactFields value
    ["expectedModules", "report", "transcripts", "expectedDependencies", "dependencySources"]
  return {
    expectedModules := ← value.getObjValAs? _ "expectedModules",
    admitted := ← value.getObjValAs? _ "report", transcripts :=
        ← value.getObjValAs? _ "transcripts"
    expectedDependencies := ← value.getObjValAs? _ "expectedDependencies"
    dependencySources := ← value.getObjValAs? _ "dependencySources" }⟩

/-- Retain one exact source per URI; repeated identical file observations are shared,
while conflicting bytes are refused. This normalizes source maps, never job results. -/
def sourceSnapshots (sources : Array ProducerReport.SourceBinding)
    (histories : Array HistoryObservation) (additional : Array SourceSnapshot := #[]) : IO
    (Array SourceSnapshot) := do
  let mut observed := sources.map fun source => (⟨source.path, source.content⟩ : SourceSnapshot)
  for history in histories do
    unless history.before == history.after &&
        (← IO.FS.readFile history.before.uri) == history.before.source do
      throw <| IO.userError s!"history snapshot changed: {history.moduleName}"
    observed := observed.push history.before
  let mut files : Array SourceSnapshot := #[]
  for source in observed ++ additional do
    if let some previous := files.find? (·.uri == source.uri) then
      unless previous == source do throw <|
                                    IO.userError s!"conflicting source snapshot: {source.uri}"
    else files := files.push source
  return files

/-- Observed process completion is not a theorem of external process semantics. -/
def buildObservation (process : ProcessResult) : BuildObservation :=
  ⟨process.exitCode.toNat, warningLines process.output, errorLines process.output⟩

private def moduleKey (snapshot : AdmittedSnapshot) (name : Name) : Except String ModuleKey := do
  return ⟨snapshot, ← admitIdentity name⟩

private def declarationKey (snapshot : AdmittedSnapshot) (key : Name × Name) :
    Except String DeclarationKey := do
  return ⟨← moduleKey snapshot key.1, ← admitIdentity key.2⟩

/-- Every report's history outcomes, in report order, through `checked_histories`. -/
def historyObservations (reports : Array RequestedInspection) : Except String
    (Array HistoryObservation) :=
  histories (reports.flatMap (·.report.histories))

/-- Reconcile full producer censuses with an independently selected positive domain. Full
replay selection and both replay key arrays survive the infrastructure partition. Sources
must already belong to the same frozen claim; no source or profile is invented here. -/
private def freezeEnvironment (claim : Claim) (request : EnvironmentRequest)
    (discovered : Array DiscoveredTarget)
    (sources : Array ProducerReport.SourceBinding) (ownedOutput : FilePath)
    (inspected : RequestedInspection) (fileSource : Option FileSourceBinding := none) :
        IO FrozenEnvironment := do
  -- This environment's sources: the root package's, then those of the dependency modules it
  -- inspects, each from the package it loads the module from.
  let sources := sources ++ inspected.dependencySources
  let snapshot : AdmittedSnapshot := ⟨claim.val.snapshot, claim.property.2.1⟩
  let positive := request.modules.map (·.name.name)
  let report := inspected.report
  let dependencyNames := request.dependencies.map (·.name.name)
  unless inspected.expectedModules == positive && report.census.modules == positive &&
      report.census.dependencyModules == dependencyNames &&
      report.census.executionRoots.isSome do
    throw <| IO.userError "producer census differs from independently requested environment"
  -- `inspected.admitted.valid` proves `checked_validate` (which includes the source-evidence
  -- guard) succeeded on this exact report; only the bindings to `sources` remain to check.
  timedPhase "freeze report validation" do
    IO.ofExcept (← IO.lazyPure fun _ => (SourceBinding.validateAgainst sources report).mapError
                                         (·.detail))
    IO.ofExcept
        (← IO.lazyPure fun _ =>
            (SourceBinding.transcriptsMatch sources inspected.transcripts).mapError (·.detail))
  let some replay := report.admission
    | throw <| IO.userError "missing completed logical admission"
  let some documentation := report.documentation
    | throw <| IO.userError "missing completed documentation observation"
  let scope ← IO.ofExcept <|
    Policy.admitScope report.compilerCapability report.declarations inspected.transcripts
  -- Equal to `admitExecution report.execution` (`Admitted.admitExecution_eq`).
  let execution := inspected.admitted.execution
  let origins := report.moduleOrigins
  let infrastructure ← Environment.infrastructureOrigins snapshot report
  let histories ← IO.ofExcept <| historyObservations #[inspected]
  let modules := request.modules
  let infrastructureNames := infrastructure.map (·.moduleKey.name.name)
  let importedNames := origins.map (·.name) |>.filter fun name =>
    !positive.contains name && !dependencyNames.contains name && !infrastructureNames.contains name
  let importedModules ← IO.ofExcept <| importedNames.mapM (moduleKey snapshot)
  let mut allSources := sources
  for history in histories do
    let binding : ProducerReport.SourceBinding :=
      ⟨history.moduleName, history.before.uri, history.before.source⟩
    if let some previous := allSources.find? (·.moduleName == history.moduleName) then
      unless previous == binding do throw <| IO.userError "history/module source binding conflict"
    else allSources := allSources.push binding
  let sourceFor (key : ModuleKey) : IO (ModuleKey × SourceSnapshot) := do
    let some source := allSources.find? (·.moduleName == key.name.name)
      | throw <| IO.userError s!"missing independently captured source: {key.name.name}"
    return (key, ⟨source.path, source.content⟩)
  -- The census binds the source of each module it inspects: the requested ones, then those of
  -- owned dependencies (`EnvironmentCensus.inspectedModules`).
  let moduleSources ← (modules ++ request.dependencies).mapM sourceFor
  let importedSources
      ← (importedModules.filter (fun m => allSources.any (·.moduleName == m.name.name))).mapM
          sourceFor
  let infrastructureSources ← ((infrastructure.map (·.moduleKey)).filter
    (fun m => allSources.any (·.moduleName == m.name.name))).mapM sourceFor
  -- A reused module of this environment's own request has its keys among `required`, admitted
  -- by the environment that replayed it (`Admission.reuseJustified_admitted`), so it is an
  -- admission module here too; the receipt lists no module as both replayed and reused.
  let replayModules ← IO.ofExcept <|
    (replay.modules ++ replay.reused.filter positive.contains).mapM (moduleKey snapshot)
  let required ← IO.ofExcept <| replay.required.mapM (declarationKey snapshot)
  let admitted ← IO.ofExcept <| replay.admitted.mapM (declarationKey snapshot)
  let declarations ← IO.ofExcept <|
      (scope.inventory.declarations.map (fun d => (d.module, d.name))).mapM
    (declarationKey snapshot)
  let rootKeys ← IO.ofExcept <| (execution.roots.map (fun r => (r.module, r.name))).mapM
      (declarationKey snapshot)
  let material ← IO.ofExcept <| documentation.materialDeclarations.mapM (declarationKey snapshot)
  let mut unclassifiedRootImports := #[]
  let configuredModules := discovered.flatMap (·.modules)
  for origin in origins do
    if claim.val.scope == .project && !configuredModules.contains origin.name &&
        !positive.contains origin.name &&
        !infrastructureNames.contains origin.name && (← pathWithin origin.olean ownedOutput) then
      unclassifiedRootImports := unclassifiedRootImports.push
        (← IO.ofExcept (moduleKey snapshot origin.name))
  let census : EnvironmentCensus := {
    request, policy := scope.inventory, execution, modules,
    dependencyModules := request.dependencies, importedModules,
        infrastructure, origins,
    moduleSources, fileSource, importedSources, infrastructureSources, unclassifiedRootImports,
    admissionModules := replayModules, admissionDeclarations := required, declarations,
    roots := rootKeys, materialDeclarations := material }
  return {
    census, roles := scope.roles, admission := ⟨replayModules, required, admitted, #[]⟩,
    -- A module's documentation-presence evidence is the proved RG5001 decision on its header
    -- observation (`RegulaPolicy.ModuleHeader.failures_eq_nil_iff`).
    moduleDocumentation := documentation.modules.map fun (name, observation) =>
      (name, (RegulaPolicy.ModuleHeader.failures observation).isEmpty)
    declarationDocumentation := documentation.declarations, histories }

/-- Requests are the coordinator's ordered module assignments. Responses cannot alter
their count, index, module partition or snapshot; each complete packet is admitted intact. -/
def freeze (claim : Claim) (expected : Array (Array Name))
    (configured : Array TargetAssignment) (discovered : Array DiscoveredTarget)
    (sources : Array ProducerReport.SourceBinding) (ownedOutput : FilePath)
    (reports : Array RequestedInspection) (fileSource : Option FileSourceBinding := none) : IO
    (Frozen claim) := do
  let snapshot : AdmittedSnapshot := ⟨claim.val.snapshot, claim.property.2.1⟩
  unless reports.size == expected.size do
    throw <| IO.userError "missing, duplicate or unrequested environment inspection"
  let requests ← expected.mapIdxM fun index names => do
    let modules ← IO.ofExcept <| names.mapM (moduleKey snapshot)
    -- The dependency modules of the request are the coordinator's own, from its module graph.
    let dependencies ← IO.ofExcept <|
      ((reports[index]?.map (·.expectedDependencies)).getD #[]).mapM (moduleKey snapshot)
    pure ({ key := ⟨snapshot, index⟩, modules, dependencies } : EnvironmentRequest)
  let environments ← requests.mapIdxM fun index request => do
    let some inspected := reports[index]?
      | throw <| IO.userError "missing requested environment inspection"
    freezeEnvironment claim request discovered sources ownedOutput inspected fileSource
  let census : Census := {
    requests, environments := environments.map (·.census),
    modules := requests.flatMap (·.modules),
    moduleSources := environments.flatMap (·.census.moduleSources),
    configuredTargets := configured, discoveredTargets := discovered }
  let plan ← timedPhase "plan admission" do
    IO.ofExcept (← IO.lazyPure fun _ => buildPlan claim census)
  return {
    census, plan, roles := frozenEnvironmentRoles environments, environments }

/-- Final operational admission returns evidence indexed by the exact requested claim.
Consumer APIs must keep this package until projecting `AcceptedRun.report`. -/
def finish {claim : Claim} (frozen : Frozen claim) (build : BuildObservation) :
    IO (AcceptedRun claim) := do
  let inputs ← timedPhase "observation construction" do
    IO.ofExcept (← IO.lazyPure fun _ => observations frozen build)
  -- Keep the computed collection and its equality together across the IO timer. The
  -- proof is erased; the exact collector runs once, on the complete original inputs.
  let collected ← timedPhase "result collection" <| IO.lazyPure fun _ =>
    (⟨ResultState.collect (required := requiredSlots frozen.plan)
        (bound := ResultBound frozen.plan) .empty inputs, rfl⟩ :
      { result // ResultState.collect (required := requiredSlots frozen.plan)
          (bound := ResultBound frozen.plan) .empty inputs = result })
  let result : { result // result = finalize frozen.plan frozen.roles inputs } ←
    match hc : collected.val with
    | .error failure => pure ⟨.error (.collection failure), by
        exact (finalize_collection_error _ _ _ _ (collected.property.trans hc)).symm⟩
    | .ok table => do
      let accepted ← timedPhase "result acceptance" <| IO.lazyPure fun _ =>
        (⟨accept frozen.plan frozen.roles table, rfl⟩ :
          { result // accept frozen.plan frozen.roles table = result })
      pure <| match ha : accepted.val with
        | .error failure =>
            ⟨.error (.acceptance failure), by
              rw [finalize_of_collected _ _ _ _ (collected.property.trans hc),
                  accepted.property.trans ha]⟩
        | .ok evidence =>
            ⟨.ok ⟨table, collected.property.trans hc, evidence⟩, by
              rw [finalize_of_collected _ _ _ _ (collected.property.trans hc),
                  accepted.property.trans ha]⟩
  let result ← IO.ofExcept <| result.val.mapError fun failure =>
      s!"acceptance refused: {repr failure}"
  return ⟨frozen.census, frozen.plan, frozen.roles, inputs, result⟩

end Regula.Checker.Acceptance
