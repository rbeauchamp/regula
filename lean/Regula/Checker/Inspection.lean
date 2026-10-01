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
  /-- What the completed admissions of earlier environments of the audit offer this one
  (`Admission.currentOffers`), which its admission reuses (`Admission.reusedModules`): for a
  library's environment, those of the environments that replay the claimed library modules it
  loads; for an executable's, every library's. -/
  priors : Array Admission.PriorAdmission
  /-- The file the worker writes its completed admission to (`Admission.Completed`) as soon as
  kernel admission succeeds, for the environments after it. -/
  publish : String
  deriving ToJson

instance : FromJson ReportWorkerRequest := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j
      ["modules", "searchRoots", "sourceRoots", "sourceBindings", "ownedOutput",
    "historyMemo", "priors", "publish"]
  return {
    modules := ← j.getObjValAs? _ "modules"
    searchRoots := ← j.getObjValAs? _ "searchRoots"
    sourceRoots := ← j.getObjValAs? _ "sourceRoots"
    sourceBindings := ← j.getObjValAs? _ "sourceBindings"
    ownedOutput := ← j.getObjValAs? _ "ownedOutput"
    historyMemo := ← j.getObjValAs? _ "historyMemo"
    priors := ← j.getObjValAs? _ "priors"
    publish := ← j.getObjValAs? _ "publish"
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

/-- The module's `.olean` parts as they are now, with the canonical path of its `.olean`, or
`none` when it has no `.olean` at `path`. -/
def freezeArtifact (moduleName : Name) (path : FilePath) :
    IO (Option Admission.FrozenArtifact) := do
  unless ← path.pathExists do return none
  return some { moduleName, canonical := (← IO.FS.realPath path).toString, path,
                parts := ← oleanParts path }

/-- A reading of each artifact's parts as they are now (`Admission.Reading`): the parts, or
`none` for an artifact whose parts can no longer be read. Reading the files is the trusted
boundary; what a reading supports is decided by `Admission.unchanged?`. -/
def readings (artifacts : Array Admission.FrozenArtifact) :
    BaseIO (Array Admission.Reading) :=
  artifacts.mapM fun artifact => do
    match ← (oleanParts artifact.path).toBaseIO with
    | .ok parts => return (artifact, some parts)
    | .error _ => return (artifact, none)

/-- The first frozen module whose `.olean` parts, read now, are not the frozen parts, by the
comparison offers are made on (`Admission.unchangedOf`). -/
def changedArtifact? (artifacts : Array Admission.FrozenArtifact) : IO (Option Name) := do
  for artifact in artifacts do
    if (Admission.unchangedOf (← readings #[artifact])).isEmpty then
      return some artifact.moduleName
  return none

/-! ## Start order

An environment reuses the admission of a claimed library module only once the environment that
replays the module has completed its own admission, so each environment waits for the
environments that replay the modules it loads. Only the wait is decided here: what an environment
may reuse is decided by `Admission.currentOffers`, `Admission.reusedModules` and
`Admission.reuseJustified`, whatever the order. An import this section misses costs a replay,
never an unreplayed module. -/

/-- The modules with a bound source that the modules `roots` import, directly or through other
such modules, and `roots` themselves, by the imports each bound source's header declares
(`Lean.parseImports'`). The walk ends at a module without a bound source or whose header does not
parse. -/
private def sourceClosure (sources : Std.HashMap Name ProducerReport.SourceBinding)
    (roots : Array Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut pending := roots.toList
  repeat
    let name :: rest := pending | break
    pending := rest
    if seen.contains name then continue
    seen := seen.insert name
    let some source := sources[name]? | continue
    let imports ← try
        pure ((← Lean.parseImports' source.content source.path).imports.map (·.module)).toList
      catch _ => pure []
    pending := imports ++ pending
  return seen

/-- For each environment, the source-bound modules a library's environment loads: those its own
modules or the force-imported probe reach (`sourceClosure`); `none` for an executable's. -/
private def environmentLoads (sourceBindings : Array ProducerReport.SourceBinding)
    (environments : Array SurfaceEnvironment) : IO (Array (Option NameSet)) := do
  let sources : Std.HashMap Name ProducerReport.SourceBinding :=
    sourceBindings.foldl (fun index source => index.insert source.moduleName source) {}
  environments.mapM fun environment => do
    if environment.executable.isSome then return none
    return some (← sourceClosure sources
      (environment.info.modules.push Environment.probeModuleName.toName))

/-- For each environment, by index, the library environments it needs: for a library's
environment (`loads` has its modules), the other libraries one of whose requested modules it
loads; for an executable's, every library. -/
def libraryNeeds (requests : Array (Array Name)) (loads : Array (Option NameSet)) :
    Array (Array Nat) :=
  let libraries := (Array.range loads.size).filter fun index => (loads.getD index none).isSome
  loads.mapIdx fun index loaded =>
    match loaded with
    | none => libraries
    | some loaded => libraries.filter fun other =>
        other != index && (requests.getD other #[]).any loaded.contains

/-- The order in which the environments become eligible to start: repeatedly the first
environment, in claim order, every one of whose `needs` is already placed. Where none is left,
because the remaining environments need one another, the first of them in claim order that
another of them needs is placed, so an environment nothing waits for (an executable's) still
comes after the libraries it needs. -/
def startOrder (needs : Array (Array Nat)) : Array Nat := Id.run do
  let count := needs.size
  let mut placed := Array.replicate count false
  let mut order : Array Nat := #[]
  for _ in [:count] do
    let unplaced := (Array.range count).filter fun index => !placed.getD index true
    let ready := unplaced.find? fun index =>
      (needs.getD index #[]).all fun needed => needed == index || placed.getD needed true
    let needed := unplaced.find? fun index => unplaced.any fun other =>
      other != index && (needs.getD other #[]).contains index
    let some next := ready <|> needed <|> unplaced[0]? | break
    placed := placed.set! next true
    order := order.push next
  return order

/-- For each environment, by index, the environments whose completed admissions it can reuse,
given the start order: for a library's environment, the first library environment in `order` to
load each module that it loads and a library requests, which is the one that replays the module
(its own library's, unless claimed libraries import one another); for an executable's, every
library. -/
def replayers (order : Array Nat) (requests : Array (Array Name))
    (loads : Array (Option NameSet)) : Array (Array Nat) :=
  let libraries := (Array.range loads.size).filter fun index => (loads.getD index none).isSome
  let claimed := libraries.flatMap fun index => requests.getD index #[]
  let first (m : Name) : Option Nat := order.find? fun index =>
    match loads.getD index none with
    | some loaded => loaded.contains m
    | none => false
  loads.mapIdx fun index loaded =>
    match loaded with
    | none => libraries
    | some loaded =>
        (((claimed.filter loaded.contains).filterMap first).filter (· != index)).toList.eraseDups
          |>.toArray


/-- The environments that environment `index` waits for: those it needs that come before it in
`order`. -/
def prerequisites (order : Array Nat) (needs : Array (Array Nat)) (index : Nat) : Array Nat :=
  (needs.getD index #[]).filter fun needed => order.idxOf needed < order.idxOf index

/-- Every prerequisite comes strictly before its environment in the start order, whatever the
order and the needs are. So no environments wait for one another: of the environments not yet
started, the one that comes first in the order waits only for environments already started. -/
theorem prerequisites_earlier {order : Array Nat} {needs : Array (Array Nat)} {index needed : Nat}
    (h : needed ∈ prerequisites order needs index) :
    order.idxOf needed < order.idxOf index := by
  unfold prerequisites at h
  simpa using (Array.mem_filter.mp h).2

/-- Wait for one of the three shared slots, run `act` in it, then release the slot. -/
private def withSlot {β : Type} (slots : Std.Mutex Nat) (act : IO β) : IO β := do
  while !(← slots.atomically do
      let free ← get
      if free > 0 then set (free - 1); return true else return false) do
    IO.sleep 20
  try act finally slots.atomically (modify (· + 1))

/-- The completed admission a worker published at `path`, when the file is there. -/
private def publishedAdmission (path : FilePath) : IO (Option Admission.Completed) := do
  unless ← path.pathExists do return none
  return some (← IO.ofExcept <|
    (Regula.Checker.PolicyCodec.parse (← IO.FS.readFile path)).bind fromJson?)

/-- Inspect every environment, each through its own `--declaration-report-worker` process, and
return the frozen library artifacts with each environment's outcome, in `environments` order.

An environment starts once the environments it waits for (`prerequisites` of `replayers`, over
`startOrder`) have published their completed admission or ended without one; environments that
wait for nothing, or for the same ones, run side by side, three at a time. It is offered those
admissions and reuses them (`Admission.reusedModules`) only over the `.olean` parts frozen here
whose reading, taken as it starts, is the frozen one (`readings`, `Admission.currentOffers`); the
caller compares every frozen part again after the inspections (`changedArtifact?`). A
worker publishes its admission as soon as kernel admission succeeds, before it builds its report,
and its report is accepted only when it records that same admission, reuses nothing its offers
do not justify (`Admission.reuseJustified`) and leaves no owned module it loaded unreplayed
(`Admission.accountsFor`). A refusal (an admission failure, or root-package output outside every
owned module) is an `.error` outcome; an IO failure is kept as a value, so every started worker
is joined. -/
def inspect (inventory : Lake.SurfaceInventory)
    (sourceBindings : Array ProducerReport.SourceBinding)
    (assignments : Array RegulaPolicy.SurfaceAssignment)
    (environments : Array SurfaceEnvironment) :
    IO (Array Admission.FrozenArtifact × Array (SurfaceEnvironment ×
      Except IO.Error (Except ProducerReport.Refusal SurfaceInspection))) := do
  -- At most three slot holders (surface report workers and frontend attributions) run
  -- at once, as before; each report worker may still run its history helper. A surface's
  -- frontend attributions share
  -- those three slots, so they run in parallel on slots other surfaces released
  -- instead of one after another behind their own report. A report may retain its
  -- environment while awaiting an existing replacement-history helper.
  let slots ← Std.Mutex.new (3 : Nat)
  let owned := NameSet.ofArray ((sourceBindings.map (·.moduleName)).filter fun name =>
    !Environment.probeModuleNames.contains name.toString)
  -- An environment reuses a library module's admission only over the `.olean` parts frozen
  -- here, and every frozen part is compared again after the last inspection.
  let frozenArtifacts : Array Admission.FrozenArtifact ← if environments.size > 1 then
      (assignments.flatMap (·.library)).filterMapM fun identity =>
        freezeArtifact identity.name (Lean.modToFilePath inventory.leanLibDir identity.name "olean")
    else pure #[]
  let loads ← environmentLoads sourceBindings environments
  let requests := environments.map (·.info.modules)
  let order := startOrder (libraryNeeds requests loads)
  let needs := replayers order requests loads
  let inspectEnvironment (historyMemo publication : FilePath)
      (priors : Array Admission.PriorAdmission) (environment : SurfaceEnvironment) :
      IO (Except ProducerReport.Refusal SurfaceInspection) := do
    let info := environment.info
    let request : ReportWorkerRequest := {
      modules := info.modules
      searchRoots := inventory.leanPath.map (·.toString)
      sourceRoots := inventory.leanSrcPath.map (·.toString)
      sourceBindings
      ownedOutput := inventory.leanLibDir.toString
      historyMemo := historyMemo.toString
      -- The worker selects modules by the offered modules and origins; the admitted keys are
      -- the coordinator's own check of the report (`Admission.reuseJustified`).
      priors := priors.map fun prior => { prior with admitted := #[] }
      publish := publication.toString
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
        admission no earlier environment offered over the same import closure"⟩)
    unless Admission.accountsFor owned report do
      return .error (.admission ⟨s!"{Admission.failureTag} {environment.label} loaded an owned \
        module that its admission neither replayed nor reused"⟩)
    -- Later environments started from the published admission, so it must be the report's.
    unless (← publishedAdmission publication) == Admission.Completed.ofReport report do
      return .error (.admission ⟨s!"{Admission.failureTag} {environment.label} published an \
        admission that differs from its report's"⟩)
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
  let count := environments.size
  let root ← IO.currentDir
  let inspections ← withScratch root "history-memo" fun historyMemo =>
      withScratch root "admissions" fun publications => do
    let publication (index : Nat) : FilePath := publications / s!"{index}.json"
    -- What each environment has made available to those that wait for it: nothing yet, its
    -- published admission, or (the inner `none`) that it ended without publishing one.
    let available ← IO.mkRef (Array.replicate count (none : Option (Option Admission.Completed)))
    let availability (index : Nat) : BaseIO (Option (Option Admission.Completed)) := do
      if let some known := (← available.get).getD index none then return some known
      match ← (publishedAdmission (publication index)).toBaseIO with
      | .ok (some completed) =>
          available.modify (·.modify index (· <|> some (some completed)))
          return some (some completed)
      | _ => return none
    let results ← IO.mkRef (Array.replicate count
      (none : Option (Except IO.Error (Except ProducerReport.Refusal SurfaceInspection))))
    let started ← Std.Mutex.new (Array.replicate count false)
    let priority := order ++ (Array.range count).filter (!order.contains ·)
    let waits := (Array.range count).map (prerequisites order needs)
    -- Three workers keep the environments going without batch barriers. Each takes the first
    -- environment in start order that is not started and whose prerequisites are available;
    -- `prerequisites_earlier` gives the first unstarted one only started prerequisites, and a
    -- started environment always becomes available below, so the workers finish.
    let claim (index : Nat) : IO Bool := started.atomically do
      if (← get).getD index true then return false
      modify (·.set! index true)
      return true
    let worker : IO Unit := do
      repeat
        let flags ← started.atomically get
        if flags.all id then break
        -- Only a started environment can have become available since the last look.
        for index in [:count] do
          if flags.getD index false then discard <| availability index
        let cells ← available.get
        let mut claimed : Option Nat := none
        for index in priority do
          if flags.getD index true then continue
          if (waits.getD index #[]).all fun needed => (cells.getD needed none).isSome then
            if ← claim index then
              claimed := some index
              break
        let some index := claimed
          | IO.sleep 20
            continue
        let some environment := environments[index]?
          | throw <| IO.userError "internal error: invalid environment index"
        let completed := (waits.getD index #[]).filterMap fun needed =>
          (cells.getD needed none).join
        -- An admission is offered only over the frozen artifacts whose parts, read now, are the
        -- frozen ones, so a module whose `.olean`, `.olean.server` or `.olean.private` changed
        -- since it was frozen is replayed here (`Admission.replayed_of_changed`), and the
        -- caller's comparison after the last inspection then leaves the audit incomplete.
        let current ← if completed.isEmpty then pure #[] else readings frozenArtifacts
        let priors := Admission.currentOffers owned current completed
        -- Capture failures as values so every started worker is joined, then choose
        -- fatal errors in claim order instead of worker-completion order.
        let outcome ←
          (inspectEnvironment historyMemo (publication index) priors environment).toBaseIO
        discard <| availability index
        available.modify (·.modify index (· <|> some none))
        results.modify (·.set! index (some outcome))
    let workers ← (Array.range (min 3 count)).mapM fun _ =>
      IO.asTask (prio := .dedicated) worker
    let finished ← workers.mapM fun task => IO.wait task
    for outcome in finished do IO.ofExcept outcome
    let outcomes ← results.get
    let mut inspections := #[]
    for environment in environments, outcome in outcomes do
      let some outcome := outcome
        | throw <| IO.userError s!"internal error: {environment.label} was not inspected"
      inspections := inspections.push (environment, outcome)
    return inspections
  return (frozenArtifacts, inspections)

end Regula.Checker.Inspection
