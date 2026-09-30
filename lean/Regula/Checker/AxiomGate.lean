import Regula.Checker.Acceptance
import Regula.Checker.AcceptanceLink
import Regula.Checker.PolicyCodec
import Regula.Checker.Lake
import Regula.Checker.SourceAudit
import Regula.Checker.Diagnostics
import Regula.Checker.Documentation
import Regula.Checker.ResultProtocol
import Regula.Checker.RunFeedback
import Regula.DiagnosticCodec
import RegulaCore.Lint
import Regula.Website

/-!
# Declaration and foundation gate

Lake-semantic declaration, computation, and foundation gate implemented
entirely in Lean.
-/

namespace Regula.Checker.AxiomGate

open Lean System
open scoped Regula.Report
open Regula.Checker
open Regula.Checker.Policy

/-- The command-line options of one `axiomGate` invocation, as `parseArgs` reads them; `run`
rejects the combinations the usage text does not allow. -/
structure Options where
  /-- `--file FILE`: audit this one source file instead of the manifested project surfaces. -/
  file : Option FilePath := none
  /-- `--claim PROFILE`: the foundation profile a single-file audit checks; only with `--file`. -/
  claim : Option Profile := none
  /-- `--execution MODE`: the execution claim of a single-file audit (`report` by default). -/
  execution : ExecutionClaim := .report
  /-- `--manifest PATH`: the surface manifest, by default `foundation_manifest.json` at the
  project root. -/
  manifest : Option FilePath := none
  /-- `--project DIR`: audit the nearest directory at or above `DIR` that has a Lake
  configuration and a `lean-toolchain`, instead of the current one. -/
  project : Option FilePath := none
  /-- `--json-out PATH`: where to write the versioned result JSON. -/
  resultOut : Option FilePath := none
  /-- `--acceptance-link PATH`: where a fresh project success records the identity of its
  accepted inputs for the separately timed documentation step. -/
  acceptanceLink : Option FilePath := none
  /-- `--verso DIR:LIBRARY:RENDER`: the Verso package whose sources the acceptance link also
  brackets; only with `--acceptance-link`. -/
  verso : Option Documentation.VersoPackage := none
  /-- `--with-docs`: also run the documentation stage on the same fresh snapshot and combine
  its result with the project result. -/
  withDocs : Bool := false
  /-- `--incremental`: audit the project in place with an incremental build instead of in an
  isolated fresh copy. -/
  incremental : Bool := false
  /-- `--build-lint`: run as the enforcing build linter, which also sets `incremental`. -/
  buildLint : Bool := false
  /-- `--verbose`: also print every classified declaration and every execution root with a
  boundary or an unresolved path. -/
  verbose : Bool := false
  /-- `--help` or `-h`: print the usage text and exit. -/
  help : Bool := false

private def usage : String :=
  "usage: lake exe axiomGate -- [--verbose] [--project DIR] [--manifest PATH] [--json-out PATH] \
    [--with-docs] [--acceptance-link PATH [--verso DIR:LIBRARY:RENDER]]\n" ++
  "       lake exe axiomGate -- (--incremental | --build-lint) [--verbose] [--project DIR] \
    [--manifest PATH] [--json-out PATH]\n" ++
  "       lake exe axiomGate -- --file FILE [--claim PROFILE] [--execution MODE] [--json-out \
    PATH]\n" ++
  "The project audit builds an isolated fresh copy by default. --incremental inspects current \
    policy over the project's incremental build instead; --build-lint does the same as the \
    enforcing build linter (the build-lint `policy` target) and implies --incremental.\n" ++
  "profiles: kernel-only, choice-free, standard-logical, compiler-trusting\n" ++
  "execution modes: report (default), checked"

private def parseArgs : List String → Options → IO Options
  | [], options => return options
  | "--" :: rest, options => parseArgs rest options
  | "--file" :: value :: rest, options =>
      parseArgs rest { options with file := some (FilePath.mk value) }
  | "--claim" :: value :: rest, options => do
      let some claim := Profile.parse? value
        | throw <| IO.userError s!"unknown foundation profile: {value}"
      parseArgs rest { options with claim := some claim }
  | "--execution" :: value :: rest, options => do
      let some mode := ExecutionClaim.parse? value
        | throw <| IO.userError s!"unknown execution mode: {value}"
      parseArgs rest { options with execution := mode }
  | "--manifest" :: value :: rest, options =>
      parseArgs rest { options with manifest := some (FilePath.mk value) }
  | "--project" :: value :: rest, options =>
      parseArgs rest { options with project := some (FilePath.mk value) }
  | "--json-out" :: value :: rest, options =>
      parseArgs rest { options with resultOut := some (FilePath.mk value) }
  | "--acceptance-link" :: value :: rest, options =>
      parseArgs rest { options with acceptanceLink := some (FilePath.mk value) }
  | "--verso" :: value :: rest, options => do
      parseArgs rest
          { options with verso := some (← IO.ofExcept (Documentation.parseVersoOption value)) }
  | "--with-docs" :: rest, options =>
      parseArgs rest { options with withDocs := true }
  | "--incremental" :: rest, options =>
      parseArgs rest { options with incremental := true }
  | "--build-lint" :: rest, options =>
      parseArgs rest { options with buildLint := true, incremental := true }
  | "--verbose" :: rest, options =>
      parseArgs rest { options with verbose := true }
  | "--help" :: rest, options => parseArgs rest { options with help := true }
  | "-h" :: rest, options => parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def resolve (repo path : FilePath) : FilePath :=
  if path.isAbsolute then path else repo / path.toString

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

private def sameStringSet (left right : Array String) : Bool :=
  left.size == right.size && left.all right.contains && right.all left.contains

/-- The terminal status of the current invocation, recorded wherever a project or
combined documentation audit decides its result status, including without `--json-out`.
`lint` derives its exit class from this and the exit code (`Lint.classify`). -/
initialize terminalObservation : IO.Ref (Option Lint.Observation) ← IO.mkRef none

/-- The stages the current invocation performs, set when its options are admitted; until then
every stage, so no result claims a stage it never started. -/
initialize expectedStages : IO.Ref (List ResultProtocol.Stage) ← IO.mkRef ResultProtocol.allStages

/-- The claimed-source build of a project audit: the ordinary `lake build`, or
`Lake.buildAuditTargets` when the `lint` driver selects it for its own audit. -/
initialize claimedBuild : IO.Ref (FilePath → Array String → IO ProcessResult) ←
  IO.mkRef Lake.buildTargets

private def recordStatus (status : ResultProtocol.Status) (findings : Array Regula.Finding) :
    IO Unit :=
  terminalObservation.set (some ⟨status, !findings.isEmpty && findings.all (·.1 == .configuration)⟩)

/-- The first executable whose root lies in a library the manifest classifies differently,
described with its remedy, for the refusal `checkClassification` reports when
`RegulaPolicy.RootsClassifiedAlike` fails. The description is diagnostic text; the decision is
the predicate. -/
private def rootConflict (manifest : Manifest) (inventory : Lake.SurfaceInventory) : String :=
  let configured := Acceptance.configuredTargets manifest
  let classOf (kind : RegulaPolicy.TargetKind) (name : String) : Option (Option String) :=
    (configured.find? fun a => a.kind == kind && a.name == name).map (·.surface)
  let conflicts := inventory.executables.filterMap fun exe =>
    let libraries := inventory.libraries.filter (·.modules.contains exe.root)
    let exeClass := classOf .executable exe.executable
    let mismatched := libraries.filter fun library => classOf .library library.library != exeClass
    let classes := libraries.map fun library => classOf .library library.library
    mismatched[0]?.map fun library =>
      if classes.any (fun c => some c != classes[0]?) then
        s!"executable '{exe.executable}' root {exe.root} is a module of libraries \
          ({", ".intercalate (libraries.map (·.library)).toList}) that the manifest classifies \
          differently from each other: keep the root in one library, and classify \
          '{exe.executable}' with it"
      else match exeClass, classOf .library library.library with
      | some (some surface), some (some owner) =>
          s!"claimed executable '{exe.executable}' root {exe.root} is a module of library \
            '{owner}', which its own surface claims: a root keeps its library's claim, so list \
            '{exe.executable}' in the executables of surface '{owner}' instead of '{surface}'"
      | some (some _), some none =>
          s!"claimed executable '{exe.executable}' root {exe.root} is a module of excluded \
            library '{library.library}': a root keeps its library's classification, so claim \
            '{library.library}' as a surface listing '{exe.executable}', or exclude \
            '{exe.executable}' too"
      | some none, some (some owner) =>
          s!"excluded executable '{exe.executable}' root {exe.root} is a module of claimed \
            library '{owner}': a root keeps its library's claim, so list '{exe.executable}' in \
            the executables of surface '{owner}'"
      | _, _ => s!"executable '{exe.executable}' root {exe.root} is a module of library \
          '{library.library}', which the manifest classifies differently"
  conflicts[0]?.getD "an executable root is classified differently from a library containing it"

/-- Every root-package Lean library and executable is classified exactly once by the
manifest; every executable root is classified alike with each library containing it:
`RegulaPolicy.RootsClassifiedAlike` over `Acceptance.configuredTargets` and
`Acceptance.discoveredTargets`, the predicate the claimed acceptance decides again in
`RegulaPolicy.TargetPartitionOK`; and every claimed library keeps a module besides its claimed
executables' roots: `∀ s ∈ assignments, s.library.size > 0` over the executed
`Acceptance.surfaceAssignments`, the library conjunct of `RegulaPolicy.ClaimCandidate.Valid`
over the surfaces the audit's claim is admitted with. Shared by the audit, `doctor` and the
read-only configuration explanation. -/
def checkClassification (manifest : Manifest) (inventory : Lake.SurfaceInventory) : IO Unit := do
  let rootLibraries := inventory.libraries.map (·.library)
  let manifested := Manifest.libraries manifest
  if !sameStringSet manifested rootLibraries then
    let missing := rootLibraries.filter fun name => !manifested.contains name
    let extra := manifested.filter fun name => !rootLibraries.contains name
    let details := (if missing.isEmpty then #[] else
      #[s!"unclassified root Lean libraries {repr missing.toList}"]) ++
      (if extra.isEmpty then #[] else #[s!"non-root Lean libraries {repr extra.toList}"])
    throw <| IO.userError s!"manifest-incomplete: {"; ".intercalate details.toList}"
  let manifestedExes := Manifest.executables manifest
  let discoveredExes := inventory.executables.map (·.executable)
  if !sameStringSet manifestedExes discoveredExes then
    let missing := discoveredExes.filter fun name => !manifestedExes.contains name
    let extra := manifestedExes.filter fun name => !discoveredExes.contains name
    let details := (if missing.isEmpty then #[] else
      #[s!"unclassified root Lean executables {repr missing.toList}"]) ++
      (if extra.isEmpty then #[] else #[s!"non-root Lean executables {repr extra.toList}"])
    throw <| IO.userError s!"manifest-incomplete: {"; ".intercalate details.toList}"
  unless decide (RegulaPolicy.RootsClassifiedAlike (Acceptance.configuredTargets manifest)
      (Acceptance.discoveredTargets inventory)) do
    throw <| IO.userError s!"manifest-conflict: {rootConflict manifest inventory}"
  let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  unless decide (∀ s ∈ assignments, s.library.size > 0) do
    let surface := ((manifest.surfaces.zip assignments).find? (·.2.library.isEmpty)).map (·.1)
    throw <| IO.userError <| "manifest-conflict: " ++ match surface with
      | some surface => s!"every module of claimed library '{surface.library}' is the root of one \
          of its claimed executables {repr surface.executables.toList}, so the library's own \
          environment would have no module: add a module to '{surface.library}' that is not an \
          executable root, such as its umbrella module"
      | none => "a claimed library has no module besides its claimed executables' roots"

private def manifestJson (manifest : Manifest) : Json :=
  Json.mkObj [
    ("schema-version", Json.num 2),
    ("surfaces", Json.arr <| manifest.surfaces.map fun surface => Json.mkObj [
      ("library", Json.str surface.library),
      ("executables", Json.arr <| surface.executables.map Json.str),
      ("claim", Json.str surface.claim.toString),
      ("execution", Json.str surface.execution.spelling),
      ("rationale", Json.str surface.rationale)
    ]),
    ("excluded-libraries", Json.arr <| manifest.excludedLibraries.map fun item =>
      Json.mkObj [
        ("library", Json.str item.library),
        ("rationale", Json.str item.rationale)
      ]),
    ("excluded-executables", Json.arr <| manifest.excludedExecutables.map fun item =>
      Json.mkObj [
        ("executable", Json.str item.executable),
        ("rationale", Json.str item.rationale)
      ])
  ]

private def libraryInfoJson (info : LibraryInfo) : Json :=
  Json.mkObj [
    ("library", Json.str info.name),
    ("modules", Json.arr <| info.modules.map (fun n => Json.str n.toString)),
    ("sources", Json.arr <| info.sources.map fun source => Json.mkObj [
      ("module", Json.str source.«module».toString),
      ("source", Json.str source.source.toString)
    ])
  ]

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
private structure ReportWorkerRequest where
  modules : Array Name
  searchRoots : Array String
  sourceRoots : Array String
  sourceBindings : Array ProducerReport.SourceBinding
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
private structure SurfaceEnvironment where
  /-- The manifest surface the environment belongs to; its claim and execution claim apply. -/
  surface : Manifest.Surface
  /-- The claimed executable whose root the environment loads; `none` for the library. -/
  executable : Option Lake.ExecutableInventory
  /-- The environment's owned modules, as the claim assigns them, and their source files. -/
  info : LibraryInfo

/-- The environment's name in progress lines and findings: the surface's library, followed by
the executable's name for an executable's environment. -/
private def SurfaceEnvironment.label (environment : SurfaceEnvironment) : String :=
  match environment.executable with
  | none => environment.surface.library
  | some exe => s!"{environment.surface.library} executable {exe.executable}"

/-- The environments of every claimed surface, in claim order, with the modules of
`assignments.flatMap (·.environmentNames)`: each surface's library, then each executable root
alone. `checked_surfaceAssignments` assigns the surfaces in manifest order and gives the `i`th
root as the root of the manifest's `i`th executable name, so the size checks cannot fail. -/
private def surfaceEnvironments (manifest : Manifest)
    (assignments : Array RegulaPolicy.SurfaceAssignment) (libraries : Array LibraryInfo)
    (exeInfoFor : String → IO Lake.ExecutableInventory) : IO (Array SurfaceEnvironment) := do
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
      let exe ← exeInfoFor name
      environments := environments.push {
        surface, executable := some exe
        info := {
          name, modules := #[root.name]
          sources := #[{ «module» := root.name, source := exe.source }] } }
  return environments

private structure SurfaceInspection where
  info : LibraryInfo
  admitted : Regula.Checker.ProducerReport.Admitted
  transcripts : Array Frontend.Transcript
  frontendFailures : Array String

/-- The bytes of every part Lean reads for the module whose `.olean` is `olean`, in
`OLeanLevel` order, `none` for an absent part: the exported `.olean`, and for a module-system
file its `.olean.server` and `.olean.private`, from which `importModules (level := .private)`
takes the kernel constants. -/
private def oleanParts (olean : FilePath) : IO (Array (Option ByteArray)) :=
  #[Lean.OLeanLevel.exported, .server, .private].mapM fun level => do
    let part := level.adjustFileName olean
    if ← part.pathExists then some <$> IO.FS.readBinFile part else pure none

/-- The completed admissions of the library environments, as an executable's environment may
reuse them: each offers the modules it replayed, except those containing a copy of a shared name
(the receipt's `shared`), whose import closure loads every `owned` module from the canonical
`.olean` path whose parts `frozen` records for it. -/
private def libraryPriors (owned : NameSet) (frozen : Std.HashMap Name String)
    (inspections : Array (Except IO.Error
      (Except ProducerReport.AdmissionFailure SurfaceInspection))) :
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

private def capturedSourceAccount (resultOut : Option FilePath)
    (sources : Array ProducerReport.SourceBinding) : IO Json := do
  if sources.isEmpty then
    if let some output := resultOut then
      if ← output.pathExists then
        let value ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
        if let .ok captured := value.getObjVal? "sourceAccount" then return captured
  return toJson sources

private def retainSourceAccount (resultOut : Option FilePath)
    (composed : IO.Ref (Option Json))
    (sources : Array ProducerReport.SourceBinding) : IO Unit := do
  match ← composed.get with
  | some _ => pure ()
  | none =>
    if let some output := resultOut then
      if ← output.pathExists then
        let captured ← capturedSourceAccount resultOut sources
        let value ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
        writeJson output (value.setObjVal! "sourceAccount" captured)

private def withRetainedSources {α : Type} (resultOut : Option FilePath)
    (composed : IO.Ref (Option Json))
    (captured : IO.Ref (Array ProducerReport.SourceBinding)) (action : IO α) : IO α := do
  try action
  finally retainSourceAccount resultOut composed (← captured.get)

private def reportContextFailure (id : Regula.RuleId) (scope : String)
    (mode : Regula.EvidenceMode) (impact : Regula.Impact) (completed : List ResultProtocol.Stage)
    (detail : String) (composed : IO.Ref (Option Json)) (resultOut : Option FilePath)
    (sources : Array ProducerReport.SourceBinding := #[]) : IO Unit := do
  composed.set none
  let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding id scope detail mode impact
  RunFeedback.emit IO.println finding
  recordStatus (if impact == .violation then .rejected else .incomplete) #[finding]
  if let some output := resultOut then
    let captured ← capturedSourceAccount resultOut sources
    writeJson output <| (ResultProtocol.resultJson (Json.str scope) mode
      (if impact == .violation then .rejected else .incomplete) #[finding] (← expectedStages.get)
      completed #[]).setObjVal!
      "sourceAccount" captured

private def withSourceEvidenceOr {α : Type} (refused : α)
    (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String)) (scope : String)
    (mode : Regula.EvidenceMode) (composed : IO.Ref (Option Json)) (resultOut : Option FilePath)
    (action : IO α) : IO α := do
  match ← SourceBinding.withUnchanged sources configuration action with
  | .ok result => return result
  | .error failure =>
      reportContextFailure .admission scope mode .incomplete
          [] failure.detail composed resultOut sources
      return refused

private def withSourceEvidence (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String)) (scope : String)
    (mode : Regula.EvidenceMode) (composed : IO.Ref (Option Json)) (resultOut : Option FilePath)
    (action : IO UInt32) : IO UInt32 :=
  withSourceEvidenceOr 1 sources configuration scope mode composed resultOut action

/-- Accepted project evidence handed, in the same process, to the same-snapshot
documentation stage and to the ordinary acceptance link. Nothing is serialized. -/
private structure ProjectEvidence where
  inventory : Lake.SurfaceInventory
  sources : Array ProducerReport.SourceBinding
  configuration : Array (FilePath × Option String)
  dependencies : Array Snapshot.DependencyObservation
  snapshot : RegulaPolicy.AdmittedSnapshot
  build : RegulaPolicy.BuildObservation
  claim : RegulaPolicy.Claim
  accepted : RegulaPolicy.AcceptedRun claim

/-- One freshness bracket: dependency inputs are captured once at the start and
rechecked once at the end. With `documentationPending`, the documentation stage that
follows in this process owns that terminal recheck and the final success. -/
private unsafe def auditSurfaceAt (repo manifestPath : FilePath)
    (fresh verbose : Bool) (reportRoot : FilePath)
    (composed : IO.Ref (Option Json)) (resultOut : Option FilePath := none)
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ())
    (documents : Array RegulaPolicy.SourceSnapshot := #[])
    (observeProject : ProjectEvidence → IO Unit := fun _ => pure ())
    (documentationPending : Bool := false) (buildLint : Bool := false) : IO UInt32 := do
  let configuration ← SourceBinding.configuration repo manifestPath
  withSourceEvidence #[] configuration reportRoot.toString
      (if fresh then .freshProject else .incrementalProject) composed resultOut do
    let inventory ← Lake.surfaceInventory repo
    let sourceBindings ← SourceBinding.capture inventory.moduleSources observeSources
    let manifest ← Manifest.load manifestPath
    let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
    let dependencies ← Snapshot.dependencies inventory
    let rootInventory : Lake.RootInventory := {
      libraries := inventory.libraries.map (·.library)
      leanLibDir := inventory.leanLibDir
    }
    checkClassification manifest inventory
    let manifested := Manifest.libraries manifest
    let mut libraries : Array LibraryInfo := #[]
    for library in manifested do
      let some info := inventory.libraries.find? (·.library == library)
        | throw <| IO.userError s!"lake-query-malformed: auditPlan omitted {library}"
      libraries := libraries.push {
        name := library, modules := info.modules, sources := info.sources
      }
    let exeInfoFor (name : String) : IO Lake.ExecutableInventory :=
      match inventory.executables.find? (·.executable == name) with
      | some info => return info
      | none => throw <| IO.userError s!"lake-query-malformed: auditPlan omitted {name}"
    -- Two executable roots that each declare `main` cannot be imported into one environment,
    -- so each root is inspected alone (`RegulaPolicy.census_executable_alone`).
    let environments ← surfaceEnvironments manifest assignments libraries exeInfoFor
    withSourceEvidence sourceBindings configuration reportRoot.toString
        (if fresh then .freshProject else .incrementalProject) composed resultOut do
      let snapshotFor (name : Name) : Option Regula.SourceSnapshot :=
        (sourceBindings.find? (·.moduleName == name)).map fun s => ⟨s.path, s.content⟩
      SourceBinding.configurationUnchanged configuration
      let positiveTargets := Manifest.positiveTargets manifest
      let (buildProcess, buildResult) ← timedPhase "claimed-source build" <|
          Lake.buildCheckedObservation repo positiveTargets
              (if fresh then "fresh" else "incrementally") (← claimedBuild.get)
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      if let some lines := buildResult then
        reportContextFailure .sourceBuild reportRoot.toString
          (if fresh then .freshProject else .incrementalProject) .incomplete
              [.configuration, .discovery]
          ("\n".intercalate lines.toList) composed resultOut sourceBindings
        return 1
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      let excludedModules := Id.run do
        let mut result : Array Name := #[]
        for excluded in manifest.excludedLibraries do
          let info := libraries.find? (·.name == excluded.library)
          if let some info := info then result := result ++ info.modules
        for excluded in manifest.excludedExecutables do
          let info := inventory.executables.find? (·.executable == excluded.executable)
          if let some info := info then result := result.push info.root
        result
      let configuredModules := libraries.foldl (fun result info => result ++ info.modules) #[]
        ++ inventory.executables.map (·.root)
      -- At most three slot holders (surface report workers and frontend attributions) run
      -- at once, as before; each report worker may still run its history helper. A surface's
      -- frontend attributions share
      -- those three slots, so they run in parallel on slots other surfaces released
      -- instead of one after another behind their own report. A report may retain its
      -- environment while awaiting an existing replacement-history helper.
      let slots ← Std.Mutex.new (3 : Nat)
      let withSlot {β : Type} (act : IO β) : IO β := do
        while !(← slots.atomically do
            let free ← get
            if free > 0 then set (free - 1); return true else return false) do
          IO.sleep 20
        try act finally slots.atomically (modify (· + 1))
      let inspectEnvironment (historyMemo : FilePath) (priors : Array Admission.PriorAdmission)
          (environment : SurfaceEnvironment) :
          IO (Except ProducerReport.AdmissionFailure SurfaceInspection) := do
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
        let outcome : ProducerReport.AdmittedOutcome ← withSlot <|
            timedPhase s!"declaration inspection {environment.label}" <|
          runTypedWorker "--declaration-report-worker" request
        if let .error failure := outcome then return .error failure
        let .ok admitted := outcome
          | throw <| IO.userError "unreachable admission outcome"
        let report := admitted.report
        if let .error failure := SourceBinding.validateAgainst sourceBindings report then
          return .error failure
        unless Admission.reuseJustified priors report do
          return .error ⟨s!"{Admission.failureTag} {environment.label} reused an \
            admission no library environment offered over the same import closure"⟩
        -- `mapWorkQueue` returns results in module order, so transcripts and failures
        -- keep the order of the former sequential loop.
        let modules := candidateModules report.declarations
        let attempts ← mapWorkQueue 3 modules fun moduleName => do
          let some source := info.sources.find? (·.«module» == moduleName)
            | return Sum.inl s!"frontend-source-missing: {moduleName}"
          try
            return Sum.inr (← withSlot <| timedPhase s!"frontend attribution {moduleName}" <|
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
          return .error failure
        return .ok { info, admitted, transcripts, frontendFailures }
      -- An executable's environment reuses a library module's admission only over the `.olean`
      -- parts frozen here, and every frozen part is compared again after the last inspection.
      let frozenArtifacts ← if environments.any (·.executable.isSome) then
          (assignments.flatMap (·.library)).filterMapM fun identity => do
            let path := Lean.modToFilePath inventory.leanLibDir identity.name "olean"
            unless ← path.pathExists do return none
            return some (identity.name, (← IO.FS.realPath path).toString, path,
              ← oleanParts path)
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
            (frozenArtifacts.foldl (fun paths (name, real, _) => paths.insert name real) {})
            (libraries.map (·.2.2))
        let executables ← inspectGroup historyMemo priors executableGroup
        return ((libraries ++ executables).qsort (·.1 < ·.1)).map (·.2)
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      for (name, _, path, parts) in frozenArtifacts do
        let current ← (oleanParts path).toBaseIO
        unless (match current with | .ok found => found == parts | .error _ => false) do
          reportContextFailure .admission reportRoot.toString
            (if fresh then .freshProject else .incrementalProject) .incomplete
                [.configuration, .discovery, .build]
            s!"producer-artifact: the .olean files of {name} changed during the audit" composed
            resultOut sourceBindings
          return 1
      -- Freeze the complete discovery domain before the per-declaration policy loop.
      -- Expected modules are the coordinator's Lake assignments, never response fields.
      for (_, outcome) in inspections do
        let response ← IO.ofExcept outcome
        if let .error failure := response then
          reportContextFailure .admission reportRoot.toString
            (if fresh then .freshProject else .incrementalProject) .incomplete
                [.configuration, .discovery, .build]
            failure.detail composed resultOut sourceBindings
          return 1
      let rawInspections ← inspections.mapM fun (environment, outcome) => do
        let response ← IO.ofExcept outcome
        let inspected ← IO.ofExcept <| response.mapError (·.detail)
        pure ({
          expectedModules := environment.info.modules, admitted := inspected.admitted,
          transcripts := inspected.transcripts } : Acceptance.RequestedInspection)
      let freezeRequest : IO (RegulaPolicy.AdmittedSnapshot ×
          ((c : RegulaPolicy.Claim) × Acceptance.Frozen c)) := do
        let histories ← IO.ofExcept <| Acceptance.historyObservations rawInspections
        let snapshotSources ← Acceptance.sourceSnapshots sourceBindings histories documents
        let snapshot ← IO.ofExcept <| Snapshot.make repo configuration snapshotSources dependencies
        let request ← IO.ofExcept <| RegulaPolicy.admitClaim {
          scope := .project, mode := if fresh then .freshProject else .incrementalProject,
          snapshot := snapshot.val, surfaces := assignments }
        let frozen ← Acceptance.freeze request (environments.map (·.info.modules))
          (Acceptance.configuredTargets manifest) (Acceptance.discoveredTargets inventory)
          sourceBindings inventory.leanLibDir rawInspections
        pure (snapshot, ⟨request, frozen⟩)
      let frozenResult ← (timedPhase "project request freeze" freezeRequest).toBaseIO
      let mut failures : Array String := #[]
      let mut findings : Array Regula.Finding := #[]
      let mut totalDeclarations := 0
      let mut reportedImports : Std.HashSet (String × String) := {}
      -- Each surface's library entry, with the entries of its executables' environments.
      let mut resultSurfaces : Array (Json × Array Json) := #[]
      -- RG2006 reads whether a surface imports Mathlib from all of its environments together;
      -- they load exactly the import closure of the surface's library and executable roots.
      let mathlibSurfaces := inspections.filterMap fun (environment, outcome) =>
        match outcome with
        | .ok (.ok inspected) =>
            if inspected.admitted.report.modules.any (·.getRoot == `Mathlib) then
              some environment.surface.library
            else none
        | _ => none
      for (environment, outcome) in inspections do
        let surface := environment.surface
        let inspection ← IO.ofExcept outcome
        if let .error failure := inspection then
          reportContextFailure .admission reportRoot.toString
            (if fresh then .freshProject else .incrementalProject) .incomplete
                [.configuration, .discovery, .build]
            failure.detail composed resultOut sourceBindings
          return 1
        let .ok inspected := inspection
          | throw <| IO.userError "unreachable admission outcome"
        let { info, admitted, transcripts, frontendFailures } := inspected
        let report := admitted.report
        unless report.census.modules == info.modules && report.census.executionRoots.isSome do
          throw <| IO.userError "producer-census: report does not match requested project scope"
        let forcedNameCodec ← Environment.forcedStructuralName report
        let forcedCollector ← Environment.forcedCollectorOnly report
        let envModules := report.modules.filter
          (fun n => !(Environment.probeModuleNames.map String.toName).contains n &&
            n != forcedNameCodec && some n != forcedCollector)
        for moduleName in info.modules do
          if !envModules.contains moduleName then
            failures :=
                failures.push s!"surface-omission: Lake module {moduleName} was not elaborated"
            findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
              reportRoot.toString
                  (s!"surface-omission: Lake module {moduleName} was not elaborated")
                  (if fresh then .freshProject else .incrementalProject) .incomplete)
          let origins := report.moduleOrigins.filter (·.name == moduleName)
          let freshOrigin ← match origins[0]? with
            | some origin => pathWithin (FilePath.mk origin.olean) rootInventory.leanLibDir
            | none => pure false
          if origins.size != 1 || !freshOrigin then
            failures :=
                failures.push
                    s!"surface-not-fresh: {moduleName} did not resolve from the fresh Lake output"
            findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
              reportRoot.toString
                  (s!"surface-not-fresh: {moduleName} did not resolve from the fresh Lake output")
                  (if fresh then .freshProject else .incrementalProject) .incomplete)
        let mut importDetails : Array String := #[]
        for moduleName in envModules do
          if excludedModules.contains moduleName then
            importDetails := importDetails.push s!"unexpected-project-module: excluded module \
              {moduleName} was imported into positive library {surface.library}"
        -- The probe modules are exempt from the environment-level exclusion check
        -- because the force import always brings them in. Any other module in the
        -- audited environment that imports the probe or its report records is
        -- contamination by an excluded checker module, whatever package owns the
        -- importer: Lake resolves imports workspace-wide, so a dependency module
        -- can import root modules, and only a scan of every module's recorded
        -- direct imports closes every chain from a claimed module to the probe.
        for origin in report.moduleOrigins do
          if (Environment.probeModuleNames.map String.toName).contains origin.name then continue
          for imported in origin.imports do
            if (Environment.probeOnlyModuleNames.map String.toName).contains imported then
              importDetails := importDetails.push s!"unexpected-project-module: checker probe \
                module {imported} was imported into positive library {surface.library} \
                by {origin.name}"
        for origin in report.moduleOrigins do
          if (Environment.probeModuleNames.map String.toName).contains origin.name then continue
          if ← pathWithin (FilePath.mk origin.olean) rootInventory.leanLibDir then
            if !configuredModules.contains origin.name then
              importDetails := importDetails.push s!"unexpected-project-module: root-owned \
                module {origin.name} is outside every manifested Lake library"
        for detail in importDetails do
          unless reportedImports.contains (surface.library, detail) do
            reportedImports := reportedImports.insert (surface.library, detail)
            failures := failures.push detail
            findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
              reportRoot.toString detail (if fresh then .freshProject else .incrementalProject)
                .violation)
        if report.declarations.any fun decl => !info.modules.contains decl.«module» then
          failures := failures.push s!"declaration-attribution-mismatch: {environment.label}"
          findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
            reportRoot.toString (s!"declaration-attribution-mismatch: {environment.label}")
                (if fresh then .freshProject else .incrementalProject) .incomplete)
        failures := failures ++ frontendFailures
        for failure in frontendFailures do
          findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .admission
            reportRoot.toString failure (if fresh then .freshProject else .incrementalProject)
                .incomplete)
        let scope ← IO.ofExcept <| Policy.admitScope report.declarations transcripts
        let native := scope.native
        let unsafeHelpers := scope.helpers
        totalDeclarations := totalDeclarations + report.declarations.size
        let mode : Regula.EvidenceMode := if fresh then .freshProject else .incrementalProject
        let some documentation := report.documentation
          | throw <| IO.userError "producer-documentation: project observations unavailable"
        -- RG5001: the proved `RegulaPolicy.ModuleHeader.failures` decides each module's header
        -- observation (documentation present, first after the imports, no repeated import).
        for (moduleName, observation) in documentation.modules do
          let moduleFindings ← IO.ofExcept <| Regula.Linter.Documentation.moduleFindings
            moduleName observation mode (some surface.claim.toString)
          for finding in moduleFindings do
            findings := findings.push finding
            let detail := (Regula.argumentParts finding.1 finding.2.arguments).2
            failures := failures.push s!"{detail} ({moduleName})"
        -- RG2006: the options Lake builds the claimed target this environment owns with,
        -- decided by the proved `RegulaPolicy.Community.failures` (`failures_eq_nil_iff`). The
        -- surface imports Mathlib when one of its environments contains a `Mathlib` module.
        let mathlib := mathlibSurfaces.contains surface.library
        let (target, options) ← match environment.executable with
          | some exe => pure (exe.executable, exe.options)
          | none => do
              let some libraryInventory :=
                  inventory.libraries.find? (·.library == surface.library)
                | throw <| IO.userError
                    s!"lake-query-malformed: auditPlan omitted {surface.library}"
              pure (surface.library, libraryInventory.options)
        let failed := RegulaPolicy.Community.failures options mathlib
        unless failed.isEmpty do
          let finding ← IO.ofExcept <| Regula.makeDiagnostic .communityConfiguration
            ⟨target, RegulaPolicy.Community.detail failed⟩ (.project reportRoot.toString) mode
            (some surface.claim.toString) .violation
          findings := findings.push ⟨.communityConfiguration, finding⟩
          failures := failures.push s!"community-configuration: {target}"
        for (key, docstring) in documentation.declarations do
          -- The proved classification (`materialDocumentationFailure_eq_none_iff`) of the
          -- recorded docstring decides RG5002 (none attached) or RG5003 (no Intent section).
          let some failure := RegulaPolicy.materialDocumentationFailure docstring | continue
          let id := Regula.ruleForMaterialDocumentation failure
          let some decl := report.declarations.find? (fun d => (d.module, d.name) == key)
            | throw <| IO.userError "producer-documentation: selected declaration missing"
          let snapshot := snapshotFor key.1
          let location ← IO.ofExcept <| RuleDiagnostics.declarationLocation decl snapshot
          findings := findings.push (← IO.ofExcept <| RuleDiagnostics.declarationFinding
            id key.2 (Regula.materialDocumentationDetail failure)
            location mode (some surface.claim.toString))
          failures := failures.push s!"{(Regula.descriptor id).applicability}: {key.2}"
        -- `ScopeContract` retains `report.declarations` as the inventory, so iterating the
        -- inventory visits the same sequence and supplies each membership proof.
        for h : decl in scope.inventory.declarations do
          if let some id := Policy.ruleForMember decl (some surface.claim) scope h then
            let reason := (Regula.descriptor id).applicability
            -- The finding names the declaration the author wrote (`Policy.subject_contract`).
            let named := Policy.subject decl scope h
            let classification := Policy.subjectDetail decl scope h
            failures :=
                failures.push s!"{reason}: {named.name} [claim: {surface.claim}] {classification}"
            let snapshot := snapshotFor named.module
            let location ← IO.ofExcept <| RuleDiagnostics.declarationLocation named snapshot
            let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding id
                (← IO.ofExcept (RuleDiagnostics.declarationName named))
              classification location
              (if fresh then .freshProject else .incrementalProject) (some surface.claim.toString)
            findings := findings.push finding
        -- Equal to `Policy.admitExecution report.execution` (`Admitted.admitExecution_eq`).
        let executionInventory := admitted.execution
        failures := failures ++ Policy.executionFailures executionInventory surface.execution
        for failure in Policy.executionFailureRecords executionInventory surface.execution do
          let location ← match report.declarations.find? (·.name == failure.root.name) with
            | some decl => do
                let snapshot := snapshotFor decl.module
                IO.ofExcept <| RuleDiagnostics.declarationLocation decl snapshot
            | none => pure (Regula.Location.module failure.root.module)
          findings := findings.push
              (← IO.ofExcept <| RuleDiagnostics.executionFinding failure location
            (if fresh then .freshProject else .incrementalProject) surface.execution)
        if verbose then
          for moduleName in info.modules do
            IO.println s!"module {moduleName} [claimed: {surface.claim}]"
            let declarations := report.declarations.filter (·.«module» == moduleName)
              |>.qsort fun left right => Name.quickLt left.name right.name
            for decl in declarations do IO.println s!"  {Policy.classify decl scope}"
        let summary := Policy.executionSummary executionInventory
        IO.println <| s!"execution coverage for {environment.label} " ++
          s!"[claim: {surface.execution}]: {summary.roots} root(s), " ++
          s!"{summary.boundaries} boundary(ies) ({summary.checked} checked, " ++
          s!"{summary.trusted} trusted), {summary.unresolved} unresolved"
        -- Every root and boundary is always in `--json-out`; text lists them only on request.
        if verbose then
          for root in report.execution do
            if !root.boundaries.isEmpty || !root.unresolved.isEmpty then
              IO.println s!"  execution root {root.name}"
              for boundary in root.boundaries do
                IO.println s!"    {Policy.describeBoundary boundary}"
              for item in root.unresolved do
                IO.println s!"    unresolved {item}"
        let environmentFields (report : Json) : List (String × Json) := [
          ("modules", Json.arr <| info.modules.map (fun n => Json.str n.toString)),
          ("authorizedNativeAxioms", Json.arr <| native.map (Json.str ∘ Name.toString)),
          ("authorizedUnsafeRecHelpers", Json.arr <| unsafeHelpers.map (Json.str ∘ Name.toString)),
          ("frontendTranscripts", Json.arr <| transcripts.map toJson),
          ("report", report)
        ]
        -- Built only for the result output, which omits the import closure; it affects no
        -- decision. A library's entry opens its surface, and each executable's environment
        -- follows it in claim order.
        if resultOut.isSome then
          let fields := environmentFields report.resultJson
          match environment.executable, resultSurfaces.back? with
          | none, _ =>
              resultSurfaces := resultSurfaces.push (Json.mkObj <| [
                ("library", Json.str surface.library),
                ("claim", Json.str surface.claim.toString),
                ("execution", Json.str surface.execution.spelling)] ++ fields, #[])
          | some exe, some (library, executables) =>
              resultSurfaces := resultSurfaces.pop.push (library, executables.push
                (Json.mkObj <| ("executable", Json.str exe.executable) :: fields))
          | some _, none =>
              throw <| IO.userError "internal error: executable environment before its library"
      let ownedModules := environments.foldl (fun count environment =>
        count + environment.info.modules.size) 0
      let claimedExes := manifest.surfaces.foldl
        (fun count surface => count + surface.executables.size) 0
      IO.println <| s!"claimed libraries: {manifest.surfaces.size}   " ++
        s!"claimed executables: {claimedExes}   " ++
        s!"owned modules: {ownedModules}   owned declarations: {totalDeclarations}"
      for surface in manifest.surfaces do
        IO.println <| s!"claimed profile for {surface.library}: {surface.claim} " ++
          s!"(execution: {surface.execution})"
      for excluded in manifest.excludedLibraries do
        let count := (libraries.find? (·.name == excluded.library)).map (·.modules.size) |>.getD 0
        IO.println s!"excluded library {excluded.library}: {count} module(s)"
      for excluded in manifest.excludedExecutables do
        IO.println s!"excluded executable {excluded.executable}"
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      unless documentationPending do Snapshot.inputsUnchanged inventory dependencies
      for document in documents do
        unless (← IO.FS.readFile document.uri) == document.source do
          throw <| IO.userError s!"documentation snapshot changed: {document.uri}"
      let build := Acceptance.buildObservation buildProcess
      let accepted : Option (RegulaPolicy.AdmittedSnapshot ×
          ((c : RegulaPolicy.Claim) × RegulaPolicy.AcceptedRun c)) ←
        if failures.isEmpty then do
          let (snapshot, ⟨request, frozen⟩) ← IO.ofExcept frozenResult
          let accepted ← timedPhase "project acceptance finalization" do
            Acceptance.finish frozen build
          pure (some (snapshot, ⟨request, accepted⟩))
        else pure none
      let unresolved := if failures.size == findings.size then #[] else
        #["additional checker failures: " ++ "\n".intercalate failures.toList]
      -- The same decision as the `status` written below, recorded even without `--json-out`.
      let status : ResultProtocol.Status := match accepted with
        | some (_, ⟨_, run⟩) => if documentationPending then .incomplete else .completed
                                                                               (Account.account run)
        | none => if !unresolved.isEmpty || findings.any (·.2.impact == .incomplete) then
                   .incomplete else .rejected
      recordStatus status findings
      if let some output := resultOut then
        let ownedModuleNames := environments.flatMap (·.info.modules)
        let sources :=
            (sourceBindings.filter (fun s => ownedModuleNames.contains s.moduleName)).map fun s =>
          Json.mkObj
              [("module", toJson s.moduleName), ("path", toJson s.path),
                  ("source", toJson s.content)]
        let surfaceEntries := resultSurfaces.map fun (library, executables) =>
          library.setObjVal! "executables" (Json.arr executables)
        let resultScope := Json.mkObj
            [("project", toJson reportRoot.toString), ("manifest", manifestJson manifest),
            ("modules", toJson ownedModuleNames),
            ("declarations", toJson totalDeclarations),
            ("sources", toJson sources), ("surfaces", toJson surfaceEntries),
            ("configuration", toJson configuration), ("configurationRoot", toJson repo.toString),
            ("libraries", toJson (libraries.map libraryInfoJson)),
            ("completedStages", toJson
                #["claimedSourceBuild", "ownedAdmission", "declarationPolicy",
                    "executionInspection"])]
        let mode : Regula.EvidenceMode := if fresh then .freshProject else .incrementalProject
        let expected ← expectedStages.get
        if let some (_, ⟨_, accepted⟩) := accepted then
          if documentationPending then
            ResultProtocol.write output resultScope mode .incomplete #[] expected
              (ResultProtocol.stagesOf mode) #["documentation audit has not completed"]
          else ResultProtocol.writeAccepted output accepted resultScope
        else
          ResultProtocol.write output resultScope mode status findings expected
            (ResultProtocol.stagesOf mode) unresolved
      RunFeedback.emitAll IO.println findings
      if !failures.isEmpty then
        IO.println s!"\nFAIL: {failures.size} violation(s)"
        for failure in failures do
          let reason := (failure.splitOn ":").head?.getD "violation"
          IO.println s!"  [{reason}] {failure}"
        return 1
      let some (snapshot, ⟨claim, accepted⟩) := accepted
        | throw <| IO.userError "missing accepted evidence for project success"
      observeProject ⟨inventory, sourceBindings, configuration, dependencies, snapshot, build,
        claim, accepted⟩
      if documentationPending then return 0
      -- Every success line below is a projection of this one accepted run's account.
      let account := Account.account accepted
      IO.println s!"accepted {account.val.jobs} policy jobs for {account.val.mode.spelling}"
      for line in account.lines do IO.println line
      IO.println s!"\n{account.pass "axiom gate"}"
      if buildLint then
        IO.println
            s!"{account.pass "build policy linter"} ({account.val.jobs} accepted policy \
              jobs; {account.val.mode.spelling})"
      return 0

/-- Fresh audits copy the project into an owned isolated workspace. With `--with-docs`,
the documentation stage runs afterwards in this same process against the same frozen
snapshot and build; project and documentation acceptance are then combined. With
`acceptanceLink`, a fresh success also returns the pending identity of its accepted inputs;
only the caller records it, after its own outer recheck. -/
private unsafe def auditSurface (repo : FilePath) (manifest : Option FilePath)
    (incremental verbose : Bool) (withDocs : Bool)
    (composed : IO.Ref (Option Json)) (resultOut : Option FilePath := none)
    (observeConfiguration : FilePath → Array (FilePath × Option String) → IO Unit :=
        fun _ _ => pure ())
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ())
    (buildLint : Bool := false) (acceptanceLink : Bool := false)
    (verso : Option Documentation.VersoPackage := none) :
    IO (UInt32 × Option AcceptanceLink.Pending) :=
  if incremental then do
    let configuration ← SourceBinding.configuration repo (manifest.getD (Manifest.defaultPath repo))
    observeConfiguration repo configuration
    (·, none) <$> withSourceEvidence #[] configuration repo.toString .incrementalProject
        composed resultOut
      (auditSurfaceAt repo (manifest.getD (Manifest.defaultPath repo)) false verbose repo composed
          resultOut observeSources (buildLint := buildLint))
  else withScratch repo "axiom-gate" fun scratch => do
    let copy := scratch / "project"
    timedPhase "isolated source copy" <| copyProject repo copy scratch
    let manifestPath := manifest.getD (Manifest.defaultPath copy)
    observeConfiguration copy (← SourceBinding.configuration copy manifestPath)
    if withDocs then Documentation.snapshotMarkdown (repo / "docs") (copy / "docs")
    let documents ← if withDocs then Documentation.captureMarkdown (copy / "docs") else pure #[]
    -- The link covers the Markdown and Verso sources the separate documentation step audits.
    let linkedSources : Documentation.Sources := ⟨repo / "docs", verso⟩
    let linkedDocuments ← if acceptanceLink then linkedSources.captureLinked repo else pure #[]
    let project ← IO.mkRef (none : Option ProjectEvidence)
    let linked ← IO.mkRef (none : Option AcceptanceLink.Pending)
    -- The identity is computed after acceptance and before the success line, so an identity
    -- failure can never follow a printed PASS.
    let observe (evidence : ProjectEvidence) : IO Unit := do
      project.set (some evidence)
      if acceptanceLink then
        linkedSources.checkLinked repo linkedDocuments
        let digest ← AcceptanceLink.identity scratch copy (repo / "docs") evidence.sources
          evidence.configuration evidence.dependencies linkedDocuments
        linked.set (some { digest, account := Account.account evidence.accepted })
    let result ← timedPhase "complete declaration audit" <|
      auditSurfaceAt copy manifestPath true verbose repo composed resultOut observeSources
        documents observe withDocs
    if result != 0 then return (result, none)
    let some evidence ← project.get
      | throw <| IO.userError "missing accepted project evidence"
    if !withDocs then return (0, ← linked.get)
    let docFindings ← IO.mkRef (#[] : Array Regula.Finding)
    let documentAccepted ← IO.mkRef
        (none : Option ((c : RegulaPolicy.Claim) × RegulaPolicy.AcceptedRun c))
    -- The documentation stage performs the run's terminal freshness recheck.
    let docsResult ← Documentation.auditBuiltProject copy (copy / "docs") evidence.inventory
      evidence.sources evidence.configuration evidence.dependencies documents
          evidence.build 4 verbose
      (fun finding => docFindings.modify (·.push finding)) (fun _ => pure ())
      (fun claim accepted => documentAccepted.set (some ⟨claim, accepted⟩)) (some evidence.snapshot)
    let combined ← if docsResult == 0 then do
        let some ⟨docClaim, accepted⟩ ← documentAccepted.get
          | throw <| IO.userError "missing accepted documentation evidence"
        let receipt ← IO.ofExcept <|
            RegulaPolicy.combineAccepted documents evidence.accepted accepted
        pure (some (⟨docClaim, receipt⟩ : (dc : RegulaPolicy.Claim) ×
          RegulaPolicy.CombinedAccepted evidence.claim dc documents))
      else pure none
    let docs ← docFindings.get
    -- The same decision as the `status` written below, recorded even without `--json-out`.
    let status : ResultProtocol.Status := match combined with
      | some ⟨_, receipt⟩ => .completed (Account.account receipt.project)
      | none => if docs.isEmpty || docs.any (·.2.impact == .incomplete) then
                 .incomplete else .rejected
    recordStatus status docs
    if let some output := resultOut then
      let value ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
      let scope ← IO.ofExcept (value.getObjVal? "scope")
      let previous ← IO.ofExcept <| (← IO.ofExcept (value.getObjVal? "diagnostics")).getArr?
      let previous ← IO.ofExcept <| previous.mapM Regula.DiagnosticCodec.parseDiagnostic
      let all := Regula.sortFindings (previous ++ docs).toList
      let value := value.setObjVal! "diagnostics"
          (toJson (all.map Regula.RegistryCodec.diagnosticJson))
      let value := value.setObjVal! "status" (.str status.spelling)
      let scanned := combined.isSome || !docs.isEmpty
      let value := ResultProtocol.guidanceFields (ResultProtocol.acceptedStatus status.spelling)
        (← expectedStages.get) (ResultProtocol.stagesOf .freshProject ++
          (if scanned then ResultProtocol.documentationStages else [])) all
        |>.foldl (fun value (key, field) => value.setObjVal! key field) value
      let value := value.setObjVal! "scope"
          (scope.setObjVal! "documentation" (.str (repo / "docs").toString))
      let value := value.setObjVal! "unresolved"
          (toJson (if combined.isSome then (#[] : Array String)
        else #["documentation requirements failed; see emitted diagnostics"]))
      let value := match combined with
        | some ⟨_, receipt⟩ =>
            (value.setObjVal! "acceptance" (ResultProtocol.acceptedJson receipt.project)).setObjVal!
              "documentationAcceptance" (ResultProtocol.acceptedJson receipt.documentation)
        | none => value
      writeJson output value
    if let some ⟨_, receipt⟩ := combined then
      let account := Account.account receipt.project
      IO.println s!"combined audit: accepted {account.val.jobs} project \
        and {(Account.account receipt.documentation).val.jobs} documentation jobs"
      for line in account.lines do IO.println line
      IO.println s!"\n{account.pass "axiom gate"}"
      return (0, none)
    return (docsResult, none)

private unsafe def auditFile (repo path : FilePath) (claim : Option Profile)
    (execution : ExecutionClaim) (manifest : Option FilePath)
    (composed : IO.Ref (Option Json)) (resultOut : Option FilePath := none)
    (observeConfiguration : FilePath → Array (FilePath × Option String) → IO Unit :=
        fun _ _ => pure ())
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ()) :
        IO UInt32 := do
  let manifestPath := manifest.getD (Manifest.defaultPath repo)
  let configuration ← SourceBinding.configuration repo manifestPath
  observeConfiguration repo configuration
  if !(← path.pathExists) then
    reportContextFailure .environment path.toString .freshFile .incomplete []
      s!"missing source file {path}" composed resultOut
    return 1
  withSourceEvidence #[] configuration path.toString .freshFile composed resultOut do
    let source ← IO.FS.readFile path
    let moduleName := s!"AuditFile_{← IO.monoNanosNow}"
    let fileSource : ProducerReport.SourceBinding := {
      moduleName := moduleName.toName, path := path.toString, content := source }
    observeSources #[fileSource]
    let inventory ← Lake.surfaceInventory repo
    let dependencies ← Snapshot.dependencies inventory
    let dependencySources ← SourceBinding.capture inventory.moduleSources fun captured =>
      observeSources (captured.push fileSource)
    let sources := dependencySources.push fileSource
    withSourceEvidence sources configuration path.toString .freshFile composed resultOut do
      if manifest.isSome || (← manifestPath.pathExists) then
        let claimed ← Manifest.load manifestPath
        let buildResult ← Lake.buildChecked repo (Manifest.positiveTargets claimed) "incrementally"
        SourceBinding.unchanged sources
        SourceBinding.configurationUnchanged configuration
        if let some lines := buildResult then
          reportContextFailure .sourceBuild repo.toString .freshFile .incomplete [.discovery]
            ("\n".intercalate lines.toList) composed resultOut sources
          return 1
      SourceBinding.unchanged dependencySources
      SourceBinding.configurationUnchanged configuration
      withScratch repo "file-audit" fun scratch => do
        let compilationOutcome ← SourceAudit.compile repo scratch
            { «module» := moduleName, source, rejectWarnings := claim.isSome }
        if let .error failure := compilationOutcome then
          reportContextFailure .admission path.toString .freshFile .incomplete
              [.discovery] failure.detail composed resultOut sources
          return 1
        let .ok compilation := compilationOutcome
          | throw <| IO.userError "unreachable compilation outcome"
        let sourceRejected := !SourceAudit.compilationPassed compilation &&
            SourceAudit.sourceDiagnosticFailure compilation
        let result : Except String (Except ProducerReport.AdmissionFailure SourceAudit.Inspected) ←
          if !SourceAudit.compilationPassed compilation then pure
                                                              (.error compilation.process.output)
          else try
            pure
                (.ok
                    (← SourceAudit.inspectOutcome compilation inventory.leanPath
                        inventory.leanSrcPath
              inventory.moduleSources (some inventory.leanLibDir)))
          catch error => pure (.error s!"{error}\n{compilation.process.output}")
        SourceBinding.unchanged dependencySources
        SourceBinding.configurationUnchanged configuration
        SourceBinding.unchanged #[{
          moduleName := moduleName.toName, path := path.toString, content := source }]
        match result with
        | .error output =>
            IO.println s!"FAIL: {path} does not elaborate:"
            let diagnostics := if !(errorLines output).isEmpty then errorLines output
              else takeLast 10 (outputLines output)
            reportContextFailure .sourceBuild path.toString .freshFile
              (if sourceRejected then .violation else .incomplete) [.discovery]
              ("\n".intercalate diagnostics.toList) composed resultOut sources
            return 1
        | .ok (.error failure) =>
            reportContextFailure .admission path.toString .freshFile .incomplete
                [.discovery, .build] failure.detail composed resultOut sources
            return 1
        | .ok (.ok inspected) =>
            let declarations := inspected.report.declarations.qsort fun left right =>
              Name.quickLt left.name right.name
            let scope ← IO.ofExcept <| Policy.admitScope declarations inspected.transcripts
            let native := scope.native
            let unsafeHelpers := scope.helpers
            let mut reasons : Array String := #[]
            let mut findings : Array Regula.Finding := #[]
            -- The admitted inventory is exactly `declarations` (`ScopeContract`). One member
            -- rule per declaration; its reason is `reasonFor`'s by definition.
            for h : decl in scope.inventory.declarations do
              let rule := Policy.ruleForMember decl claim scope h
              -- A violation line names the finding's subject, as its finding does.
              let (verdict, classification) := match rule with
                | none => ("OK", Policy.classifyMember decl scope h)
                | some id => (s!"VIOLATION[{(Regula.descriptor id).applicability}]",
                    Policy.subjectDetail decl scope h)
              IO.println s!"[{verdict}] {classification}"
              if let some id := rule then
                reasons := reasons.push (Regula.descriptor id).applicability
                -- The finding names the declaration the author wrote (`Policy.subject_contract`).
                let named := Policy.subject decl scope h
                let location ← IO.ofExcept <| RuleDiagnostics.declarationLocation named
                  (some ⟨path.toString, source⟩)
                let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding id
                    (← IO.ofExcept (RuleDiagnostics.declarationName named))
                  (Policy.subjectDetail decl scope h) location .freshFile (claim.map Profile.toString)
                findings := findings.push finding
            let executionInventory ← IO.ofExcept <| Policy.admitExecution inspected.report.execution
            let executionViolations := Policy.executionFailures executionInventory execution
            for failure in Policy.executionFailureRecords executionInventory execution do
              let location ← match declarations.find? (·.name == failure.root.name) with
                | some decl => IO.ofExcept <| RuleDiagnostics.declarationLocation decl
                                (some ⟨path.toString, source⟩)
                | none => pure (Regula.Location.module failure.root.module)
              let finding ← IO.ofExcept <| RuleDiagnostics.executionFinding failure location
                  .freshFile execution
              findings := findings.push finding
            RunFeedback.emitAll IO.println findings
            let summary := Policy.executionSummary executionInventory
            IO.println <| s!"execution coverage [claim: {execution}]: {summary.roots} root(s), " ++
              s!"{summary.boundaries} boundary(ies) ({summary.checked} checked, {summary.trusted} \
                trusted), " ++
              s!"{summary.unresolved} unresolved"
            for root in inspected.report.execution do
              if !root.boundaries.isEmpty || !root.unresolved.isEmpty then
                IO.println s!"  execution root {root.name}"
                for boundary in root.boundaries do
                  IO.println s!"    {Policy.describeBoundary boundary}"
                for item in root.unresolved do
                  IO.println s!"    unresolved {item}"
            for violation in executionViolations do
              let reason := (violation.splitOn ":").head?.getD "execution-unresolved"
              IO.println s!"[VIOLATION[{reason}]] {violation}"
              reasons := reasons.push reason
            let accepted ← if reasons.isEmpty then
                match claim with
                | some .kernelOnly | some .choiceFree | some .standardLogical => do
                    let some selected := claim | throw <| IO.userError "missing requested profile"
                    let profile ← IO.ofExcept <| Acceptance.conformingProfile selected
                    let compiledSource : ProducerReport.SourceBinding := {
                      moduleName := moduleName.toName, path := compilation.sourcePath.toString,
                      content := compilation.spec.source }
                    let bindings := dependencySources.push compiledSource
                    SourceBinding.unchanged bindings
                    SourceBinding.unchanged #[fileSource]
                    SourceBinding.configurationUnchanged configuration
                    Snapshot.inputsUnchanged inventory dependencies
                    let admitted ← IO.ofExcept <| ProducerReport.admit inspected.report
                    let inspection : Acceptance.RequestedInspection := {
                      expectedModules := #[moduleName.toName], admitted,
                      transcripts := inspected.transcripts }
                    let histories ← IO.ofExcept <| Acceptance.historyObservations #[inspection]
                    let requested : RegulaPolicy.SourceSnapshot := ⟨path.toString, source⟩
                    let actual : RegulaPolicy.SourceSnapshot :=
                        ⟨compiledSource.path, compiledSource.content⟩
                    let binding ← IO.ofExcept <|
                        RegulaPolicy.admitFileSourceBinding requested actual
                    let snapshots ← Acceptance.sourceSnapshots bindings histories #[requested]
                    let snapshot ← IO.ofExcept <| Snapshot.make repo configuration snapshots
                        dependencies
                    let request ← IO.ofExcept <| RegulaPolicy.admitClaim {
                      scope := .file requested profile execution, mode := .freshFile,
                      snapshot := snapshot.val, surfaces := #[] }
                    let frozen ← Acceptance.freeze request #[#[moduleName.toName]] #[] #[] bindings
                      inventory.leanLibDir #[inspection] (some binding)
                    let accepted ← Acceptance.finish frozen
                      (Acceptance.buildObservation compilation.process)
                    pure
                        (some
                            (⟨request, accepted⟩ :
                                (c : RegulaPolicy.Claim) × RegulaPolicy.AcceptedRun c))
                | _ => pure none
              else pure none
            if let some output := resultOut then
              let resultScope := Json.mkObj
                  [("file", toJson path.toString), ("source", toJson source),
                  ("execution", toJson execution.toString),
                  ("claim", toJson (claim.map Profile.toString)),
                  ("declarations", toJson declarations.size),
                  ("report", inspected.report.resultJson),
                  ("authorizedNativeAxioms", toJson native),
                  ("authorizedUnsafeRecHelpers", toJson unsafeHelpers),
                  ("frontendTranscripts", toJson inspected.transcripts),
                  ("configuration", toJson configuration),
                  ("configurationRoot", toJson repo.toString),
                  ("completedStages", toJson
                      #["incrementalDependencies", "freshFileCompilation", "ownedAdmission",
                          "declarationPolicy", "executionInspection"])]
              if let some ⟨_, accepted⟩ := accepted then
                composed.set (some (ResultProtocol.acceptedValue accepted resultScope))
              else
                let expected ← expectedStages.get
                ResultProtocol.write output resultScope .freshFile
                  (if findings.any (·.2.impact == .incomplete) then .incomplete
                    else if !reasons.isEmpty then .rejected else if claim.isNone || claim ==
                                                                  some .compilerTrusting
                    then .classified else .incomplete)
                  findings expected (ResultProtocol.stagesOf .freshFile) #[]
            if !reasons.isEmpty then
              IO.println <| s!"\nfile audit: FAIL ({reasons.size} violation(s))" ++
                (claim.map (fun profile => s!" against claim '{profile}'")).getD ""
              return 1
            if claim.isNone || claim == some .compilerTrusting then
              IO.println s!"\nfile inspection: CLASSIFIED ({declarations.size} declaration(s)); no \
                conforming claim"
              return 0
            let some ⟨_, accepted⟩ := accepted
              | throw <| IO.userError "missing accepted evidence for file success"
            let account := Account.account accepted
            for line in account.lines do IO.println line
            IO.println
                s!"\n{account.pass "file audit"} ({account.val.jobs} accepted policy \
                  jobs, {account.val.mode.spelling})"
            return 0

private def optionValues (flag : String) : List String → List String
  | option :: value :: rest =>
      if option == flag then value :: optionValues flag rest
      else optionValues flag (value :: rest)
  | _ => []

/-- Before any argument validation, mark every recognisable `--json-out` destination
incomplete, so an earlier completed result cannot be mistaken for this attempt's. -/
def invalidateResults (args : List String) : IO Unit := do
  let destinations := (optionValues "--json-out" args).eraseDups.map FilePath.mk
  let invalidate (path : FilePath) :=
    writeJson path (Json.mkObj (ResultProtocol.identityFields ++ [
      ("scope", Json.null), ("mode", Json.null), ("status", .str "incomplete"),
      ("diagnostics", toJson (#[] : Array Json)),
      ("unresolved", toJson #["configuration has not been validated"])] ++
      ResultProtocol.guidanceFields false ResultProtocol.allStages [] []))
  -- Absolute destinations do not depend on project configuration being valid.
  for path in destinations.filter (·.isAbsolute) do invalidate path
  let relative := destinations.filter (!·.isAbsolute)
  if !relative.isEmpty then
    let root ← match optionValues "--project" args with
      | [dir] => findRepoRoot dir
      | [] => repoRoot
      | _ => throw <| IO.userError "duplicate --project option"
    for path in relative do invalidate (resolve root path)

/-- Run one `axiomGate` invocation and return its exit code. The internal forms
`--validate-site`, `--registry-out`, `--validate-registry` and `--replacement-history-worker`
do only that job; otherwise it invalidates earlier results at the requested output paths,
parses and checks the options, audits the single file or the manifested project surfaces, and
writes the result JSON and the acceptance link that were requested. -/
unsafe def run (args : List String) : IO UInt32 := do
  terminalObservation.set none
  RunFeedback.reset
  expectedStages.set ResultProtocol.allStages
  invalidateResults args
  if let ["--validate-site", registryPath, artifactPath] := args then
    let registry ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile registryPath)
    let artifact ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile artifactPath)
    IO.ofExcept <| Regula.Website.validateArtifact ResultProtocol.producer registry artifact
    return 0
  if let ["--registry-out", output] := args then
    writeJson output (Regula.RegistryCodec.registryJson ResultProtocol.producer)
    return 0
  if let ["--validate-registry", input] := args then
    let value ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    IO.ofExcept <| Regula.RegistryCodec.validateRegistry ResultProtocol.producer value
    return 0
  if let ["--declaration-report-worker", input, out] := args then
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request : ReportWorkerRequest ← IO.ofExcept (fromJson? json)
    let guarded ← SourceBinding.withUnchanged request.sourceBindings #[] do
      let outcome ← Environment.loadReportOutcome request.modules
        (request.searchRoots.map FilePath.mk) (request.sourceRoots.map FilePath.mk)
        (request.sourceBindings.map fun source => (source.moduleName, FilePath.mk source.path))
        (some (FilePath.mk request.ownedOutput)) (validateReport := false)
        (historyMemo := some (FilePath.mk request.historyMemo)) (priors := request.priors)
      if let .ok report := outcome then
        if let .error failure := SourceBinding.validateAgainst request.sourceBindings report then
          return .error failure
      return outcome
    writeJson out (workerPacket json (toJson (ProducerReport.Outcome.ofExcept (guarded.bind id))))
    return 0
  if let ["--frontend-worker", input, out] := args then
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request : Frontend.WorkerRequest ← IO.ofExcept (fromJson? json)
    let transcript ← Frontend.build request.moduleName request.source
      (request.searchRoots.map FilePath.mk)
    writeJson out (workerPacket json (toJson transcript))
    return 0
  if let ["--compile-batch-worker", input, out] := args then
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request ← IO.ofExcept (fromJson? json)
    writeJson out
        (workerPacket json (indexedWorkerPayload (← SourceAudit.compileBatchWorker request)))
    return 0
  if let ["--inspection-group-worker", input, out] := args then
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request ← IO.ofExcept (fromJson? json)
    writeJson out (workerPacket json (toJson (← SourceAudit.inspectGroupWorker request)))
    return 0
  if let ["--diagnostic-worker", moduleWire, source, out] := args then
    let moduleName ← IO.ofExcept <| Regula.RegistryCodec.parseName
        (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse moduleWire)
    let before ← IO.FS.readFile source
    let errors ← Diagnostics.errors moduleName source
    unless (← IO.FS.readFile source) == before do throw <| IO.userError "diagnostic source changed"
    writeJson out
        (workerPacket (sourceWorkerRequest "diagnostic" moduleName source before) (toJson errors))
    return 0
  if let ["--replacement-history-worker", moduleWire, source, out] := args then
    let moduleName ← IO.ofExcept <| Regula.RegistryCodec.parseName
        (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse moduleWire)
    let transcript ← Frontend.buildReplacementHistoryCurrentSearchPath moduleName source
    if !transcript.replacementHistoryUnsupported.isEmpty then
      throw <|
          IO.userError s!"unsupported replacement-history \
            evaluators: {transcript.replacementHistoryUnsupported}"
    writeJson out
        (workerPacket (sourceWorkerRequest "history" moduleName source transcript.sourceContent)
      (toJson transcript.runtimeReplacements))
    return 0
  for flag in #["--json-out", "--acceptance-link", "--project", "--file",
      "--manifest", "--claim", "--execution"] do
    if (optionValues flag args).length > 1 then
      throw <| IO.userError s!"duplicate {flag} option"
  let options ← parseArgs args {}
  if options.help then IO.println usage; return 0
  if options.file.isNone && options.claim.isSome then
    throw <| IO.userError "--claim requires --file"
  if options.file.isNone && options.execution != .report then
    throw <| IO.userError "--execution requires --file (surface mode uses the manifest)"
  if options.file.isSome && options.incremental then
    throw <| IO.userError "--incremental applies only to surface mode"
  if options.withDocs && (options.file.isSome || options.incremental) then
    throw <| IO.userError "--with-docs requires fresh surface mode"
  if options.acceptanceLink.isSome &&
      (options.file.isSome || options.incremental || options.withDocs) then
    throw <| IO.userError "--acceptance-link requires fresh surface mode without --with-docs"
  if options.verso.isSome && options.acceptanceLink.isNone then
    throw <| IO.userError "--verso applies only to --acceptance-link"
  let repo ← match options.project with
    | some dir => findRepoRoot dir
    | none => repoRoot
  let resultOut := options.resultOut.map (resolve repo)
  let acceptanceLink := options.acceptanceLink.map (resolve repo)
  if let some path := acceptanceLink then AcceptanceLink.invalidate path
  let mode : Regula.EvidenceMode := if options.file.isSome then .freshFile
    else if options.incremental then .incrementalProject else .freshProject
  expectedStages.set (ResultProtocol.stagesOf mode ++
    (if options.withDocs then ResultProtocol.documentationStages else []))
  if let some output := resultOut then
    ResultProtocol.write output (Json.str repo.toString) mode .incomplete #[]
        (← expectedStages.get) []
      #["audit has not completed"]
  let capturedSources ← IO.mkRef (#[] : Array ProducerReport.SourceBinding)
  let observeSources := fun sources => capturedSources.set sources
  let effective ← IO.mkRef (none : Option Json)
  let composed ← IO.mkRef (none : Option Json)
  let observeConfiguration := fun (root : FilePath)
      (configuration : Array (FilePath × Option String)) =>
    effective.set
        (some
            (Json.mkObj [("root", toJson root.toString), ("configuration", toJson configuration)]))
  let reportFailure : IO.Error → IO UInt32 := fun error => do
    composed.set none
    let configError := error.toString.startsWith "manifest-"
    let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding
      (if configError then .configuration else .environment) repo.toString
      error.toString mode (if configError then .violation else .incomplete)
    RunFeedback.emit IO.eprintln finding
    recordStatus (if configError then .rejected else .incomplete) #[finding]
    if let some output := resultOut then
      let captured ← capturedSourceAccount resultOut (← capturedSources.get)
      writeJson output <| (ResultProtocol.resultJson (Json.str repo.toString) mode
        (if configError then .rejected else .incomplete) #[finding] (← expectedStages.get) []
        #[error.toString]).setObjVal!
        "sourceAccount" captured
    return 1
  let action : IO (UInt32 × Option AcceptanceLink.Pending) := do
    try
      match options.file with
      | some path =>
          return (← auditFile repo (resolve repo path) options.claim options.execution
            (options.manifest.map (resolve repo)) composed resultOut observeConfiguration
                observeSources, none)
      | none =>
          if options.buildLint then
            IO.println "build policy linter: enforcing all manifested Lake modules (incremental \
              elaboration; fresh policy inspection)"
          let result ← auditSurface repo (options.manifest.map (resolve repo))
            options.incremental options.verbose options.withDocs composed resultOut
                observeConfiguration observeSources
            (buildLint := options.buildLint) (acceptanceLink := acceptanceLink.isSome)
            (verso := options.verso.map fun verso =>
                { verso with dir := repo / verso.dir.toString })
          return result
    catch error => return (← reportFailure error, none)
  -- A configuration-read failure still records the request, with no configuration read.
  let (configuration, readFailure) ← try
      pure (← SourceBinding.configuration repo
        ((options.manifest.map (resolve repo)).getD (Manifest.defaultPath repo)), none)
    catch error => pure (#[], some error)
  let request := ResultProtocol.requestJson
      (if options.file.isSome then "file" else if options.withDocs then "projectWithDocs" else
                                                                         "project")
    repo.toString ((options.file.map (fun path => (resolve repo path).toString)).getD repo.toString)
    (options.claim.map Profile.toString)
    (if options.file.isSome then some options.execution.toString else none) configuration
  let (code, linked) ← withRetainedSources resultOut composed capturedSources <|
    match readFailure with
    | some error => return (← reportFailure error, none)
    | none => withSourceEvidenceOr (1, none) #[] configuration repo.toString mode composed
               resultOut action
  if let some output := resultOut then
    match ResultProtocol.composeDecision code (← composed.get) with
    | some base =>
      writeJson output (ResultProtocol.composedFinal base
        (← capturedSourceAccount resultOut (← capturedSources.get))
        (toJson (← capturedSources.get)) request (toJson (← effective.get)))
    | none =>
      let value ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile output)
      let captured ← capturedSources.get
      let value := if (value.getObjVal? "sourceAccount").isOk then value
        else value.setObjVal! "sourceAccount" (toJson captured)
      writeJson output
          ((value.setObjVal! "request" request).setObjVal! "effective" (toJson (← effective.get)))
  if code == 0 then
    if let (some path, some pending) := (acceptanceLink, linked) then
      AcceptanceLink.record path pending
      IO.println s!"acceptance link: recorded {pending.digest}"
  return code

/-- The `axiomGate` executable body: search-path initialization, then `run`, with
any escaping error reported as `FAIL` and exit 1. `AxiomGateMain` is the
user-facing entry; the qualification-only `ruleExamples --injected-git-facts`
entry reuses this exact body. -/
unsafe def entry (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1

end Regula.Checker.AxiomGate
