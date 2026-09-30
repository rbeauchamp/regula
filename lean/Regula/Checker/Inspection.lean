import Regula.Checker.Acceptance
import Regula.Checker.Frontend
import Regula.Checker.Manifest
import Regula.Checker.Policy

/-! # Surface environment inspection

The project audit's acquisition of every claimed surface environment's report, shared by the
audit and the environment-census qualification so both observe the same reports. Each report
comes from its own `--declaration-report-worker` process: a report's correspondence checks run
under a resource limit fixed once per process (`Regula.Probe`), so a process that inspected an
earlier environment is not a fresh one for the next. Process launch, the worker's Lean
elaboration and filesystem reads are trusted IO boundaries. -/
namespace Regula.Checker.Inspection

open Lean System
open Regula.Checker

/-- The Lake inventory of one audited library or surface environment: its modules and their
source files. -/
structure LibraryInfo where
  /-- The Lake library name; for an executable's environment, the executable's name. -/
  name : String
  /-- Its modules as Lake reports them; for a surface environment, the modules that environment
  owns: the library's modules other than its claimed executables' roots, or one executable's
  root. -/
  modules : Array Name
  /-- The source file Lake resolves for each of those modules. -/
  sources : Array Lake.SourceEntry

private def infoFor (libraries : Array LibraryInfo) (name : String) :
    IO LibraryInfo :=
  match libraries.find? (·.name == name) with
  | some info => return info
  | none => throw <| IO.userError s!"internal error: missing library inventory for {name}"

/-- The inventory of each library the manifest names, in the manifest's order. A library Lake
did not report is refused. -/
def manifestedLibraries (manifest : Manifest) (inventory : Lake.SurfaceInventory) :
    IO (Array LibraryInfo) := do
  let mut libraries : Array LibraryInfo := #[]
  for library in Manifest.libraries manifest do
    let some info := inventory.libraries.find? (·.library == library)
      | throw <| IO.userError s!"lake-query-malformed: auditPlan omitted {library}"
    libraries := libraries.push {
      name := library, modules := info.modules, sources := info.sources
    }
  return libraries

private def candidateModules (decls : Array Regula.Report.Declaration) : Array Name :=
  Id.run do
    let mut modules : Array Name := #[]
    for decl in decls do
      if Policy.needsFrontendTranscript #[decl]
          && !modules.contains decl.«module» then
        modules := modules.push decl.«module»
    modules

/-- Only typed data crosses these worker boundaries. Each imported environment
and frontend's persistent import regions die before that surface's next operation. -/
structure ReportWorkerRequest where
  /-- The environment's owned modules, imported together and reported on. -/
  modules : Array Name
  /-- The module search path the worker resolves the imports on. -/
  searchRoots : Array String
  /-- The source search path the worker's replacement-history lookups use. -/
  sourceRoots : Array String
  /-- The coordinator's captured sources, which must stay unchanged and bind the report. -/
  sourceBindings : Array ProducerReport.SourceBinding
  /-- The root package's compiled-module output directory. -/
  ownedOutput : String
  /-- Directory the coordinator owns for this audit, where surface workers share
  replacement-history worker output (`Environment.historyWorkerOutput`). -/
  historyMemo : String
  /-- The library environments' completed admissions, which an executable's environment reuses
  (`Admission.reusedModules`); empty for a library's environment. -/
  priors : Array Admission.PriorAdmission
  deriving ToJson

instance : FromJson ReportWorkerRequest := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j
      ["modules", "searchRoots", "sourceRoots", "sourceBindings", "ownedOutput",
    "historyMemo", "priors"]
  return {
    modules := ← j.getObjValAs? _ "modules"
    searchRoots := ← j.getObjValAs? _ "searchRoots"
    sourceRoots := ← j.getObjValAs? _ "sourceRoots"
    sourceBindings := ← j.getObjValAs? _ "sourceBindings"
    ownedOutput := ← j.getObjValAs? _ "ownedOutput"
    historyMemo := ← j.getObjValAs? _ "historyMemo"
    priors := ← j.getObjValAs? _ "priors"
  }⟩

/-- One Lean environment the project audit loads for a claimed surface, in the order of
`RegulaPolicy.SurfaceAssignment.environments`: the surface's library, or one claimed
executable whose root module it loads without any other executable root. -/
structure SurfaceEnvironment where
  /-- The manifest surface the environment belongs to; its claim and execution claim apply. -/
  surface : Manifest.Surface
  /-- The claimed executable whose root the environment loads; `none` for the library. -/
  executable : Option Lake.ExecutableInventory
  /-- The environment's owned modules, as the claim assigns them, and their source files. -/
  info : LibraryInfo

/-- The environment's name in progress lines and findings: the surface's library, followed by
the executable's name for an executable's environment. -/
def SurfaceEnvironment.label (environment : SurfaceEnvironment) : String :=
  match environment.executable with
  | none => environment.surface.library
  | some exe => s!"{environment.surface.library} executable {exe.executable}"

/-- The environments of every claimed surface, in claim order, with the modules of
`assignments.flatMap (·.environmentNames)`: each surface's library, then each executable root
alone. `checked_surfaceAssignments` assigns the surfaces in manifest order and gives the `i`th
root as the root of the manifest's `i`th executable name, so the size checks cannot fail. -/
def surfaceEnvironments (manifest : Manifest) (inventory : Lake.SurfaceInventory)
    (assignments : Array RegulaPolicy.SurfaceAssignment) (libraries : Array LibraryInfo) :
    IO (Array SurfaceEnvironment) := do
  unless manifest.surfaces.size == assignments.size do
    throw <| IO.userError "internal error: surface assignments differ from the manifest"
  let mut environments : Array SurfaceEnvironment := #[]
  for (surface, assignment) in manifest.surfaces.zip assignments do
    let library ← infoFor libraries surface.library
    environments := environments.push {
      surface, executable := none
      info := { library with modules := assignment.library.map (·.name) } }
    unless surface.executables.size == assignment.executables.size do
      throw <| IO.userError s!"internal error: executable assignments differ for {surface.library}"
    for (name, root) in surface.executables.zip assignment.executables do
      let some exe := inventory.executables.find? (·.executable == name)
        | throw <| IO.userError s!"lake-query-malformed: auditPlan omitted {name}"
      environments := environments.push {
        surface, executable := some exe
        info := {
          name, modules := #[root.name]
          sources := #[{ «module» := root.name, source := exe.source }] } }
  return environments

/-- One environment's completed inspection: its admitted report and frontend transcripts. -/
structure SurfaceInspection where
  /-- The environment's owned modules and their source files. -/
  info : LibraryInfo
  /-- The worker's report, with the proof that it passed transport validation. -/
  admitted : Regula.Checker.ProducerReport.Admitted
  /-- The isolated frontend transcripts of the modules whose declarations need one. -/
  transcripts : Array Frontend.Transcript
  /-- The frontend attributions that could not be built, as failure details. -/
  frontendFailures : Array String

/-- The bytes of every part Lean reads for the module whose `.olean` is `olean`, in
`OLeanLevel` order, `none` for an absent part: the exported `.olean`, and for a module-system
file its `.olean.server` and `.olean.private`, from which `importModules (level := .private)`
takes the kernel constants. -/
private def oleanParts (olean : FilePath) : IO (Array (Option ByteArray)) :=
  #[Lean.OLeanLevel.exported, .server, .private].mapM fun level => do
    let part := level.adjustFileName olean
    if ← part.pathExists then some <$> IO.FS.readBinFile part else pure none

/-- A claimed library module's `.olean` parts, frozen before any environment is inspected. -/
structure FrozenArtifact where
  /-- The module. -/
  moduleName : Name
  /-- The canonical path of its `.olean` file. -/
  canonical : String
  /-- Its `.olean` path under the root package's output directory. -/
  path : FilePath
  /-- The bytes of each part (`oleanParts`). -/
  parts : Array (Option ByteArray)

/-- The first frozen module whose `.olean` parts now differ from, or can no longer be read as,
the frozen parts. -/
def changedArtifact? (artifacts : Array FrozenArtifact) : IO (Option Name) := do
  for artifact in artifacts do
    let current ← (oleanParts artifact.path).toBaseIO
    unless (match current with | .ok found => found == artifact.parts | .error _ => false) do
      return some artifact.moduleName
  return none

/-- The completed admissions of the library environments, as an executable's environment may
reuse them: each offers the modules it replayed, except those containing a copy of a shared name
(the receipt's `shared`), whose import closure loads every `owned` module from the canonical
`.olean` path whose parts `frozen` records for it. -/
private def libraryPriors (owned : NameSet) (frozen : Std.HashMap Name String)
    (inspections : Array (Except IO.Error
      (Except ProducerReport.Refusal SurfaceInspection))) :
    Array Admission.PriorAdmission :=
  inspections.filterMap fun
    | .ok (.ok inspected) =>
        let report := inspected.admitted.report
        let index := Admission.originIndex report.moduleOrigins
        let shared := (report.admission.map (·.shared)).getD #[]
        let offered := ((report.admission.map (·.modules)).getD #[]).filter fun m =>
          !shared.contains m && match Admission.importClosure index m with
          | none => false
          | some closure => closure.all fun origin =>
              !owned.contains origin.name || frozen[origin.name]? == some origin.olean
        if offered.isEmpty then none
        else some { modules := offered, origins := report.moduleOrigins }
    | _ => none

/-- Wait for one of the three shared slots, run `act` in it, then release the slot. -/
private def withSlot {β : Type} (slots : Std.Mutex Nat) (act : IO β) : IO β := do
  while !(← slots.atomically do
      let free ← get
      if free > 0 then set (free - 1); return true else return false) do
    IO.sleep 20
  try act finally slots.atomically (modify (· + 1))

/-- Inspect every environment, each through its own `--declaration-report-worker` process, and
return the frozen library artifacts with each environment's outcome, in `environments` order.
Every library's environment completes before any executable's, which reuses the admissions they
offer (`Admission.reusedModules`) only over the `.olean` parts frozen here; the caller compares
those parts again after the inspections (`changedArtifact?`). A refusal (an admission failure, or
root-package output outside every owned module) is an `.error` outcome; an IO failure is kept as
a value, so every started worker is joined. -/
def inspect (inventory : Lake.SurfaceInventory)
    (sourceBindings : Array ProducerReport.SourceBinding)
    (assignments : Array RegulaPolicy.SurfaceAssignment)
    (environments : Array SurfaceEnvironment) :
    IO (Array FrozenArtifact × Array (SurfaceEnvironment ×
      Except IO.Error (Except ProducerReport.Refusal SurfaceInspection))) := do
  -- At most three slot holders (surface report workers and frontend attributions) run
  -- at once, as before; each report worker may still run its history helper. A surface's
  -- frontend attributions share
  -- those three slots, so they run in parallel on slots other surfaces released
  -- instead of one after another behind their own report. A report may retain its
  -- environment while awaiting an existing replacement-history helper.
  let slots ← Std.Mutex.new (3 : Nat)
  let inspectEnvironment (historyMemo : FilePath) (priors : Array Admission.PriorAdmission)
      (environment : SurfaceEnvironment) :
      IO (Except ProducerReport.Refusal SurfaceInspection) := do
    let info := environment.info
    let request : ReportWorkerRequest := {
      modules := info.modules
      searchRoots := inventory.leanPath.map (·.toString)
      sourceRoots := inventory.leanSrcPath.map (·.toString)
      sourceBindings
      ownedOutput := inventory.leanLibDir.toString
      historyMemo := historyMemo.toString
      priors
    }
    -- The decoder validates the report once and keeps that success as a proof.
    let outcome : ProducerReport.AdmittedOutcome ← withSlot slots <|
        timedPhase s!"declaration inspection {environment.label}" <|
      runTypedWorker "--declaration-report-worker" request
    if let .error failure := outcome then return .error failure
    let .ok admitted := outcome
      | throw <| IO.userError "unreachable admission outcome"
    let report := admitted.report
    if let .error failure := SourceBinding.validateAgainst sourceBindings report then
      return .error (.admission failure)
    unless Admission.reuseJustified priors report do
      return .error (.admission ⟨s!"{Admission.failureTag} {environment.label} reused an \
        admission no library environment offered over the same import closure"⟩)
    -- `mapWorkQueue` returns results in module order, so transcripts and failures
    -- keep the order of the former sequential loop.
    let modules := candidateModules report.declarations
    let attempts ← mapWorkQueue 3 modules fun moduleName => do
      let some source := info.sources.find? (·.«module» == moduleName)
        | return Sum.inl s!"frontend-source-missing: {moduleName}"
      try
        return Sum.inr (← withSlot slots <| timedPhase s!"frontend attribution {moduleName}" <|
          Frontend.buildIsolated moduleName source.source inventory.leanPath)
      catch error =>
        return Sum.inl s!"frontend-transcript-failed: {moduleName}: {error}"
    let mut frontendFailures : Array String := #[]
    let mut transcripts : Array Frontend.Transcript := #[]
    for attempt in attempts do
      match attempt with
      | .inl failure => frontendFailures := frontendFailures.push failure
      | .inr transcript => transcripts := transcripts.push transcript
    if let .error failure := SourceBinding.transcriptsMatch sourceBindings transcripts then
      return .error (.admission failure)
    return .ok { info, admitted, transcripts, frontendFailures }
  -- An executable's environment reuses a library module's admission only over the `.olean`
  -- parts frozen here, and every frozen part is compared again after the last inspection.
  let frozenArtifacts ← if environments.any (·.executable.isSome) then
      (assignments.flatMap (·.library)).filterMapM fun identity => do
        let path := Lean.modToFilePath inventory.leanLibDir identity.name "olean"
        unless ← path.pathExists do return none
        return some { moduleName := identity.name, canonical := (← IO.FS.realPath path).toString,
                      path, parts := ← oleanParts path }
    else pure #[]
  let inspectGroup (historyMemo : FilePath) (priors : Array Admission.PriorAdmission)
      (group : Array (Nat × SurfaceEnvironment)) :=
    mapWorkQueue 3 group fun (index, environment) => do
      -- Capture failures as values so every started worker is joined, then choose
      -- fatal errors in claim order instead of worker-completion order.
      return (index, environment,
        ← (inspectEnvironment historyMemo priors environment).toBaseIO)
  let inspections ← withScratch (← IO.currentDir) "history-memo" fun historyMemo => do
    let indexed := environments.mapIdx fun index environment => (index, environment)
    -- Every library's environment completes before any executable's, which reuses the
    -- admissions they offer (`Admission.reusedModules`).
    let libraries ← inspectGroup historyMemo #[] (indexed.filter (·.2.executable.isNone))
    let executableGroup := indexed.filter (·.2.executable.isSome)
    let priors := if executableGroup.isEmpty then #[] else
      libraryPriors
        (NameSet.ofArray ((sourceBindings.map (·.moduleName)).filter fun name =>
          !Environment.probeModuleNames.contains name.toString))
        (frozenArtifacts.foldl (fun paths artifact =>
          paths.insert artifact.moduleName artifact.canonical) {})
        (libraries.map (·.2.2))
    let executables ← inspectGroup historyMemo priors executableGroup
    return ((libraries ++ executables).qsort (·.1 < ·.1)).map (·.2)
  return (frozenArtifacts, inspections)

end Regula.Checker.Inspection
