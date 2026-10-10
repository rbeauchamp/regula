import Regula.Checker.Acceptance
import Regula.Checker.Inspection
import Regula.Checker.AcceptanceLink
import Regula.Checker.PolicyCodec
import Regula.Checker.Lake
import Regula.Checker.SourceAudit
import Regula.Checker.Diagnostics
import Regula.Checker.Documentation
import Regula.Checker.ResultProtocol
import RegulaCore.ScratchCopy
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
open Regula.Checker.Inspection

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
  /-- `--driver-copy PATH`: an internal option of `scripts/verify.sh`. The audit makes no copy of
  its own and audits the copy of the project that the verification driver made at `PATH`
  (`driverCopy`). -/
  driverCopy : Option FilePath := none
  /-- `--verbose`: also print every classified declaration, timing spans and, for a project
  audit, every execution root with a boundary the toolchain does not own or an unresolved path
  and every entry of the toolchain trusted base, which the file audit always lists. -/
  verbose : Bool := false
  /-- `--kernel-types`: also write, in `--json-out`, each declaration's `type`, the `repr` of
  its kernel type expression, which the result otherwise omits. -/
  kernelTypes : Bool := false
  /-- `--help` or `-h`: print the usage text and exit. -/
  help : Bool := false

private def usage : String :=
  "usage: lake exe axiomGate -- [--verbose] [--project DIR] [--manifest PATH] [--json-out PATH \
    [--kernel-types]] [--with-docs] [--acceptance-link PATH [--verso DIR:LIBRARY:RENDER]]\n" ++
  "       lake exe axiomGate -- (--incremental | --build-lint) [--verbose] [--project DIR] \
    [--manifest PATH] [--json-out PATH [--kernel-types]]\n" ++
  "       lake exe axiomGate -- --file FILE [--claim PROFILE] [--execution MODE] [--json-out \
    PATH [--kernel-types]] [--verbose]\n" ++
  "The project audit builds an isolated fresh copy by default. --incremental inspects current \
    policy over the project's incremental build instead; --build-lint does the same as the \
    enforcing build linter (the build-lint `policy` target) and implies --incremental.\n" ++
  "--verbose also prints every classified declaration, timing spans and, for a project audit, \
    each execution root with a boundary the toolchain does not own or an unresolved path and \
    every entry of the toolchain trusted base; the file audit always lists its execution account \
    and toolchain trusted base.\n" ++
  "--kernel-types also writes, in --json-out, each declaration's kernel type expression as \
    `type`; the result otherwise carries only the printed `prettyType`.\n" ++
  "profiles: kernel-only, choice-free, standard-logical, compiler-trusting\n" ++
  "execution modes: report (default), checked\n" ++
  "exit codes: 0 accepted (or, for --file without a conforming claim, classified), 1 violation, \
    2 invalid configuration or invocation, 3 incomplete; --help exits 0 unless another argument \
    fails"

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
  | "--driver-copy" :: value :: rest, options =>
      parseArgs rest { options with driverCopy := some (FilePath.mk value) }
  | "--verbose" :: rest, options =>
      parseArgs rest { options with verbose := true }
  | "--kernel-types" :: rest, options =>
      parseArgs rest { options with kernelTypes := true }
  | "--help" :: rest, options => parseArgs rest { options with help := true }
  | "-h" :: rest, options => parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def resolve (repo path : FilePath) : FilePath :=
  if path.isAbsolute then path else repo / path.toString

/-- The recorded result of the current invocation, set wherever a project, file or combined
documentation audit decides its result status, including without `--json-out`. Its status is
the one the result output renders, its tally the summary counts, and its exit code the one
`run` returns (`Lint.Observation`); `lint` derives its exit class from it and the exit code
(`Lint.classify`). -/
initialize terminalObservation : IO.Ref (Option Lint.Observation) ← IO.mkRef none

/-- The stages the current invocation performs, set when its options are admitted; until then
every stage, so no result claims a stage it never started. -/
initialize expectedStages : IO.Ref (List ResultProtocol.Stage) ← IO.mkRef ResultProtocol.allStages

/-- Whether the current invocation's result output also carries each declaration's kernel type
expression (`--kernel-types`), set when its options are admitted. It changes only what the result
file renders, never a decision. -/
initialize kernelTypes : IO.Ref Bool ← IO.mkRef false

/-- The claimed-source build of a project audit: the build with the project's own options,
showing Lake's progress line for each job as it runs (`Lake.buildTargetsShowing`), or
`Lake.buildAuditTargets` when the `lint` driver selects it for its own audit. Either way it is a
`Lake.Build`, so it runs without Lake's artifact cache (`Lake.Build.run`). -/
initialize claimedBuild : IO.Ref Lake.Build ← IO.mkRef Lake.buildTargetsShowing

/-- Whether the workspace owner asserted that the workspace's lakefiles are ordinary configuration
(`lake lint -- --ordinary-lakefiles`), set by the `lint` driver for its own audit. The project
result records it as `scope.ordinaryLakefiles`. -/
initialize ordinaryLakefiles : IO.Ref Bool ← IO.mkRef false

/-- Record the invocation's result and return the status it decides, for the result output. -/
private def record (observation : Lint.Observation) : IO ResultProtocol.Status := do
  terminalObservation.set (some observation)
  return observation.status

/-- The result of a run that did not accept: the rule and impact of each of its findings, and
whether it left evidence unresolved that no finding reports. -/
private def refused (findings : Array Regula.Finding) (unresolved : Bool := false) :
    Lint.Observation :=
  .refused (findings.toList.map fun f => (f.1, f.2.impact)) unresolved

/-- The summary line of a run that did not accept: its findings counted by impact. -/
private def printSummary (observation : Lint.Observation) : IO Unit :=
  IO.println s!"\nFAIL: {observation.tally.text}"

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

/-- Every root-package Lean library and executable is classified by the manifest: `manifest` is
one `Manifest.loadFor` admitted for `inventory`, which names only root libraries and root
executables, each once (`Manifest.parseFor_ok`, `Manifest.parse_sound`), so only an
unclassified library or executable is left to refuse here. Every
executable root is classified alike with each library containing it:
`RegulaPolicy.RootsClassifiedAlike` over `Acceptance.configuredTargets` and
`Acceptance.discoveredTargets`, the predicate the claimed acceptance decides again in
`RegulaPolicy.TargetPartitionOK`; and every claimed library keeps a module besides its claimed
executables' roots: `∀ s ∈ assignments, s.library.size > 0` over the executed
`Acceptance.surfaceAssignments`, the library conjunct of `RegulaPolicy.ClaimCandidate.Valid`
over the surfaces the audit's claim is admitted with. Shared by the audit, `doctor` and the
read-only configuration explanation. -/
def checkClassification (manifest : Manifest) (inventory : Lake.SurfaceInventory) : IO Unit := do
  let manifested := Manifest.libraries manifest
  let missing := (inventory.libraries.map (·.library)).filter fun name =>
    !manifested.contains name
  unless missing.isEmpty do
    throw <| IO.userError
      s!"manifest-incomplete: unclassified root Lean libraries {repr missing.toList}"
  let manifestedExes := Manifest.executables manifest
  let missing := (inventory.executables.map (·.executable)).filter fun name =>
    !manifestedExes.contains name
  unless missing.isEmpty do
    throw <| IO.userError
      s!"manifest-incomplete: unclassified root Lean executables {repr missing.toList}"
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
    ("modules", toJson info.modules),
    ("sources", Json.arr <| info.sources.map fun source => Json.mkObj [
      ("module", toJson source.«module»),
      ("source", Json.str source.source.toString)
    ])
  ]

private def capturedSourceAccount (resultOut : Option FilePath)
    (sources : Array ProducerReport.SourceBinding) : IO Json := do
  if sources.isEmpty then
    if let some output := resultOut then
      if ← output.pathExists then
        let value ← ResultProtocol.readDocument output
        if let .ok captured := value.getObjVal? "sourceAccount" then return captured
  return ProducerReport.sourceAccountJson sources

private def retainSourceAccount (resultOut : Option FilePath)
    (composed : IO.Ref (Option Json))
    (sources : Array ProducerReport.SourceBinding) : IO Unit := do
  match ← composed.get with
  | some _ => pure ()
  | none =>
    if let some output := resultOut then
      if ← output.pathExists then
        let captured ← capturedSourceAccount resultOut sources
        let value ← ResultProtocol.readDocument output
        ResultProtocol.writeDocument output (value.setObjVal! "sourceAccount" captured)

private def withRetainedSources {α : Type} (resultOut : Option FilePath)
    (composed : IO.Ref (Option Json))
    (captured : IO.Ref (Array ProducerReport.SourceBinding)) (action : IO α) : IO α := do
  try action
  finally retainSourceAccount resultOut composed (← captured.get)

/-- Stop the run with `findings`: print them and the summary, record the result they decide and
write it, with the stages the call site completed. -/
private def reportContextFindings (findings : Array Regula.Finding) (scope : String)
    (mode : Regula.EvidenceMode) (completed : List ResultProtocol.Stage)
    (composed : IO.Ref (Option Json)) (resultOut : Option FilePath)
    (sources : Array ProducerReport.SourceBinding := #[]) : IO Unit := do
  composed.set none
  RunFeedback.emitAll IO.println findings
  let observation := refused findings
  let status ← record observation
  printSummary observation
  if let some output := resultOut then
    let captured ← capturedSourceAccount resultOut sources
    ResultProtocol.writeDocument output <|
      (ResultProtocol.resultJson (Json.str scope) mode status findings
        (← expectedStages.get) completed #[]).setObjVal! "sourceAccount" captured

/-- `reportContextFindings` with the one context finding of rule `id`. -/
private def reportContextFailure (id : Regula.RuleId) (scope : String)
    (mode : Regula.EvidenceMode) (impact : Regula.Impact) (completed : List ResultProtocol.Stage)
    (detail : String) (composed : IO.Ref (Option Json)) (resultOut : Option FilePath)
    (sources : Array ProducerReport.SourceBinding := #[]) : IO Unit := do
  let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding id scope detail mode impact
  reportContextFindings #[finding] scope mode completed composed resultOut sources

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

/-- Merge each module's directly observed importers across environments: keep its first
position and append incoming importers not already recorded for it. -/
private def mergeUnowned (known incoming : Array ProducerReport.UnownedModule) :
    Array ProducerReport.UnownedModule := Id.run do
  let mut result := known
  for unowned in incoming do
    match result.findIdx? (·.module == unowned.module) with
    | some index =>
        result := result.modify index fun known => { known with
          importers := known.importers ++ unowned.importers.filter (!known.importers.contains ·) }
    | none => result := result.push unowned
  return result

/-- A private copy of a project in a scratch directory, with no build output of an earlier run:
one that this process made with `copyProject` in a scratch directory it created (`isolatedCopy`),
or one that the verification driver made and that passed what this process can observe of it
(`driverCopy`). The constructor is private to this module, and those two functions are the only
ones that give a value. -/
structure Copied where
  private mk ::
  /-- The root of the copy. -/
  project : FilePath

/-- Copy the project at `repo` into the new scratch directory `scratch`, which holds no build
output. -/
private def isolatedCopy (repo scratch : FilePath) : IO Copied := do
  let copy := scratch / "project"
  timedPhase "isolated source copy" <| copyProject repo copy scratch
  return ⟨copy⟩

/-- The copy of the project at `repo` that the verification driver made at `path`
(`RegulaVerification.makeCopy`), admitted by what this process can observe of it:

* `path` is the directory `project` of a directory of this project's scratch area
  (`ScratchCopy.name?`), and that directory has its ownership marker, so it was made by the
  scratch protocol (`Regula.Scratch`);
* this process's own executable is below the build directory that Lake gives for the copy
  (`ScratchCopy.inside`), so the build output it audits is the one that made this gate.

**Not observed, and trusted:** that the driver made the copy new in this run, so that its build
output held nothing before the driver's build. No file of the directory shows that. A caller that
puts earlier build output into a directory of this shape, with a gate built there, gets a value.
So a result of this origin says that it rests on the driver (`Origin.qualification`), and
`--driver-copy` is an internal option of `scripts/verify.sh`. -/
private def driverCopy (repo path : FilePath) : IO Copied := do
  let refuse {α : Type} (reason : String) : IO α :=
    throw <| IO.userError s!"driver copy refused: {path} {reason}"
  let area ← match ← (IO.FS.realPath (Regula.Scratch.directory repo)).toBaseIO with
    | .ok area => pure area
    | .error _ => refuse s!"is not in the scratch area of {repo}, which has none"
  let copy ← match ← (IO.FS.realPath path).toBaseIO with
    | .ok copy => pure copy
    | .error _ => refuse "is not there"
  let some name := ScratchCopy.name? area.normalize.components copy.normalize.components
    | refuse s!"is not the directory `project` of a scratch directory of {area}"
  let marker := area / s!"{name}.{Regula.Scratch.markerExtension}"
  let marked ← match ← marker.symlinkMetadata.toBaseIO with
    | .ok metadata => pure (metadata.type == .file)
    | .error _ => pure false
  unless marked do refuse s!"has no ownership marker {marker}"
  let build ← match ← (Workspace.withRootWorkspace copy fun workspace =>
      IO.FS.realPath workspace.root.buildDir).toBaseIO with
    | .ok build => pure build
    | .error error => refuse s!"has no build directory that Lake gives ({error})"
  let own ← IO.FS.realPath (← IO.appPath)
  unless ScratchCopy.inside build.normalize.components own.normalize.components do
    refuse s!"did not build this gate: {own} is not below {build}"
  return ⟨copy⟩

/-- Where the root-package build output that a project audit inspects comes from. A project audit
reports the fresh mode only for the first two (`Origin.mode_fresh_iff`), and each of those two
holds a `Copied` value. -/
inductive Origin where
  /-- The audit made an isolated copy of the project and builds in it. -/
  | copied (copy : Copied)
  /-- The verification driver made the copy and built in it, and the audit admitted the copy by
  what it can observe (`driverCopy`). -/
  | driverCopy (copy : Copied)
  /-- The checkout's existing build output, brought up to date by an incremental build. -/
  | incremental

/-- The evidence mode an audit of that origin reports. -/
def Origin.mode : Origin → Regula.EvidenceMode
  | .copied _ | .driverCopy _ => .freshProject
  | .incremental => .incrementalProject

/-- How a build-failure line names the build of that origin. -/
def Origin.label : Origin → String
  | .copied _ | .driverCopy _ => "fresh"
  | .incremental => "incrementally"

/-- The name of the origin in a result document (`scope.buildOrigin`) and in the acceptance
link. -/
def Origin.spelling : Origin → String
  | .copied _ => "isolatedCopy"
  | .driverCopy _ => "driverCopy"
  | .incremental => "incrementalBuild"

/-- What the success line of an audit adds for its origin. An audit of a copy that the
verification driver made says what its fresh mode rests on: the audit did not make the copy, and
it has no observation of its own that the copy was new. -/
def Origin.qualification : Origin → String
  | .driverCopy _ => " (in a copy of this checkout that the verification driver made: that the \
      copy was new and held no earlier build output rests on the driver)"
  | .copied _ | .incremental => ""

/-- An audit reports the fresh mode only for a `Copied` value: a copy it made, or a copy of the
verification driver that it admitted. So an audit of a checkout in place cannot report it. That a
`Copied` value comes from one of those two functions rests on its private constructor, which is
an ergonomic boundary. -/
theorem Origin.mode_fresh_iff (origin : Origin) :
    origin.mode = .freshProject ↔
      ∃ copy, origin = .copied copy ∨ origin = .driverCopy copy := by
  cases origin with
  | copied copy => exact ⟨fun _ => ⟨copy, .inl rfl⟩, fun _ => rfl⟩
  | driverCopy copy => exact ⟨fun _ => ⟨copy, .inr rfl⟩, fun _ => rfl⟩
  | incremental => simp [Origin.mode]

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
    (origin : Origin) (verbose : Bool) (reportRoot : FilePath)
    (composed : IO.Ref (Option Json)) (resultOut : Option FilePath := none)
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ())
    (documents : Array RegulaPolicy.SourceSnapshot := #[])
    (observeProject : ProjectEvidence → IO Unit := fun _ => pure ())
    (documentationPending : Bool := false) (buildLint : Bool := false) : IO UInt32 := do
  let configuration ← SourceBinding.configuration repo manifestPath
  withSourceEvidence #[] configuration reportRoot.toString
      origin.mode composed resultOut do
    let inventory ← Lake.surfaceInventory repo
    let sourceBindings ← SourceBinding.capture inventory.moduleSources observeSources
    let manifest ← Manifest.loadFor manifestPath inventory
    let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
    let dependencies ← Snapshot.dependencies inventory
    let rootInventory : Lake.RootInventory := {
      libraries := inventory.libraries.map (·.library)
      leanLibDir := inventory.leanLibDir
    }
    checkClassification manifest inventory
    let libraries ← manifestedLibraries manifest inventory
    -- Two executable roots that each declare `main` cannot be imported into one environment,
    -- so each root is inspected alone (`RegulaPolicy.census_executable_alone`).
    let environments ← surfaceEnvironments manifest inventory assignments libraries
    withSourceEvidence sourceBindings configuration reportRoot.toString
        origin.mode composed resultOut do
      let snapshotFor (name : Name) : Option Regula.SourceSnapshot :=
        (sourceBindings.find? (·.moduleName == name)).map fun s => ⟨s.path, s.content⟩
      SourceBinding.configurationUnchanged configuration
      let buildPlan := Lake.claimedBuildPlan manifest inventory
      let (initialBuild, buildResult) ← timedPhase "claimed-source build" <|
          Lake.buildCheckedObservation repo buildPlan.initialTargets
              origin.label (← claimedBuild.get)
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      if let some lines := buildResult then
        reportContextFailure .sourceBuild reportRoot.toString
          origin.mode .incomplete
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
      let mode : Regula.EvidenceMode := origin.mode
      let gather (found : Array Regula.Finding) (finding : Regula.Finding) :=
        if found.any (·.entry == finding.entry) then found else found.push finding
      -- Complete this refusal-only phase before starting any declaration workers. A clear
      -- graph supplies no evidence to those workers or to acceptance finalization.
      let graphArtifacts ← (assignments.flatMap (·.library)).filterMapM fun identity =>
        freezeArtifact identity.name (Lean.modToFilePath inventory.leanLibDir identity.name "olean")
      let positiveModules := environments.flatMap (·.info.modules)
      let mut scopeFindings : Array Regula.Finding := #[]
      let mut scopeUnowned : Array ProducerReport.UnownedModule := #[]
      for environment in environments do
        let request : ModuleGraphRequest := {
          modules := environment.info.modules
          searchRoots := inventory.leanPath.map (·.toString)
          sourceBindings
        }
        let observed ← (do
          let graph : Environment.ModuleGraph ← timedPhase s!"module scope {environment.label}" <|
            runTypedWorker "--module-graph-worker" request
          let ordinary ← graph.ordinaryModules
          let failures ← graph.requestedFailures ordinary
            (graph.scopeRequests request.modules positiveModules) inventory.leanLibDir
          unless failures.isEmpty do
            return (failures, (#[] : Array ProducerReport.UnownedModule), (#[] : Array String))
          let owned := request.modules ++ request.sourceBindings.map
            ProducerReport.SourceBinding.moduleName
          let unowned ← graph.unownedModules owned inventory.leanLibDir
          unless unowned.isEmpty do return (#[], unowned, #[])
          let details ← graph.importDetails ordinary excludedModules configuredModules
            inventory.leanLibDir environment.surface.library
          return (#[], #[], details)).toBaseIO
        match observed with
          | .ok (failures, unowned, details) =>
            scopeUnowned := mergeUnowned scopeUnowned unowned
            for detail in failures do
              scopeFindings := gather scopeFindings (← IO.ofExcept <|
                RuleDiagnostics.contextFinding .coverage reportRoot.toString detail mode .incomplete)
            for detail in details do
              scopeFindings := gather scopeFindings (← IO.ofExcept <|
                RuleDiagnostics.contextFinding .coverage reportRoot.toString detail mode .violation)
          | .error error =>
            let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding .environment
              reportRoot.toString
              s!"declaration inspection of {environment.label} failed: module scope: {error}"
              mode .incomplete
            scopeFindings := gather scopeFindings finding
      for unowned in scopeUnowned do
        scopeFindings := scopeFindings.push (← IO.ofExcept <|
          RuleDiagnostics.contextFinding .coverage reportRoot.toString unowned.detail mode .violation)
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      if let some name ← changedArtifact? graphArtifacts then
        reportContextFailure .admission reportRoot.toString mode .incomplete
          buildPlan.completedBeforeScope
          s!"producer-artifact: the .olean files of {name} changed during the audit" composed
          resultOut sourceBindings
        return 1
      unless scopeFindings.isEmpty do
        Snapshot.inputsUnchanged inventory dependencies
        for document in documents do
          unless (← IO.FS.readFile document.uri) == document.source do
            throw <| IO.userError s!"documentation snapshot changed: {document.uri}"
        reportContextFindings scopeFindings reportRoot.toString mode
          buildPlan.completedBeforeScope composed resultOut sourceBindings
        return 1
      let (buildProcess, buildResult) ← match buildPlan.completionTargets with
        | none => pure (initialBuild, none)
        | some targets => do
            let build ← claimedBuild.get
            timedPhase "deferred claimed-source build" (Lake.buildCheckedObservation repo targets
              origin.label build)
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      if let some lines := buildResult then
        reportContextFailure .sourceBuild reportRoot.toString mode .incomplete
          [.configuration, .discovery]
          ("\n".intercalate lines.toList) composed resultOut sourceBindings
        return 1
      if buildPlan.completionTargets.isSome then
        if let some name ← changedArtifact? graphArtifacts then
          reportContextFailure .admission reportRoot.toString mode .incomplete
            [.configuration, .discovery, .build]
            s!"producer-artifact: the .olean files of {name} changed during the audit" composed
            resultOut sourceBindings
          return 1
      -- Each environment's report comes from its own worker process (`Inspection.inspect`).
      let (frozenArtifacts, inspections) ←
        Inspection.inspect inventory sourceBindings assignments environments
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      if let some name ← changedArtifact? frozenArtifacts then
        reportContextFailure .admission reportRoot.toString
          origin.mode .incomplete
              [.configuration, .discovery, .build]
          s!"producer-artifact: the .olean files of {name} changed during the audit" composed
          resultOut sourceBindings
        return 1
      -- Freeze the complete discovery domain before the per-declaration policy loop.
      -- Expected modules are the coordinator's Lake assignments, never response fields.
      -- An environment whose inspection stopped yields its finding by how it stopped, in claim
      -- order: a refused admission is incomplete (RG2005), owned output outside every owned
      -- module is a coverage violation (RG2004, each module once, with its importers in every
      -- environment whose inspection reached that check), and a failed worker or inspection is
      -- incomplete with its own error (RG2001). A finding identical to one already gathered
      -- (same rule and detail), such as one refused declaration that several environments
      -- replay, is gathered once. Configuration, discovery and the build completed before any
      -- inspection.
      let mut stopped : Array Regula.Finding := #[]
      let mut unownedModules : Array ProducerReport.UnownedModule := #[]
      for (environment, outcome) in inspections do
        match outcome with
        | .ok (.ok _) => pure ()
        | .ok (.error (.admission failure)) =>
            stopped := gather stopped (← IO.ofExcept <| RuleDiagnostics.contextFinding .admission
              reportRoot.toString failure.detail mode .incomplete)
        | .ok (.error (.unowned modules)) =>
            unownedModules := mergeUnowned unownedModules modules
        | .error error =>
            stopped := gather stopped (← IO.ofExcept <| RuleDiagnostics.contextFinding .environment
              reportRoot.toString s!"declaration inspection of {environment.label} failed: {error}"
              mode .incomplete)
      for unowned in unownedModules do
        stopped := stopped.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
          reportRoot.toString unowned.detail mode .violation)
      unless stopped.isEmpty do
        reportContextFindings stopped reportRoot.toString mode [.configuration, .discovery, .build]
          composed resultOut sourceBindings
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
          scope := .project, mode := origin.mode,
          snapshot := snapshot.val, surfaces := assignments }
        let frozen ← Acceptance.freeze request (environments.map (·.info.modules))
          (Acceptance.configuredTargets manifest) (Acceptance.discoveredTargets inventory)
          sourceBindings inventory.leanLibDir rawInspections
        pure (snapshot, ⟨request, frozen⟩)
      let frozenResult ← (timedPhase "project request freeze" freezeRequest).toBaseIO
      let mut failures : Array String := #[]
      -- The indices in `failures` of RG1005 failures about declarations Lean generated from
      -- another: the summary folds them into one count, since their findings print under it.
      let mut attributedFailures : Std.HashSet Nat := {}
      let mut findings : Array Regula.Finding := #[]
      let mut totalDeclarations := 0
      let mut reportedImports : Std.HashSet (String × String) := {}
      -- Each surface's library entry, with the entries of its executables' environments.
      let mut resultSurfaces : Array (Json × Array Json) := #[]
      -- Every environment's execution account, labeled, for the audit's toolchain trusted base.
      let mut executionAccounts : Array (String × Policy.ExecutionInventory) := #[]
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
        -- Every stopped inspection was reported above.
        let .ok (.ok inspected) := outcome
          | throw <| IO.userError "unreachable inspection outcome"
        let { info, admitted, transcripts, frontendFailures } := inspected
        let report := admitted.report
        unless report.census.modules == info.modules && report.census.executionRoots.isSome do
          throw <| IO.userError "producer-census: report does not match requested project scope"
        let graph := Environment.ModuleGraph.ofReport report
        let envModules ← graph.ordinaryModules
        let requestedFailures ← graph.requestedFailures envModules info.modules
          rootInventory.leanLibDir
        for detail in requestedFailures do
          failures := failures.push detail
          findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
            reportRoot.toString detail mode .incomplete)
        let importDetails ← graph.importDetails envModules excludedModules configuredModules
          rootInventory.leanLibDir surface.library
        for detail in importDetails do
          unless reportedImports.contains (surface.library, detail) do
            reportedImports := reportedImports.insert (surface.library, detail)
            failures := failures.push detail
            findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
              reportRoot.toString detail origin.mode
                .violation)
        if report.declarations.any fun decl => !info.modules.contains decl.«module» then
          failures := failures.push s!"declaration-attribution-mismatch: {environment.label}"
          findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .coverage
            reportRoot.toString (s!"declaration-attribution-mismatch: {environment.label}")
                origin.mode .incomplete)
        failures := failures ++ frontendFailures
        for failure in frontendFailures do
          findings := findings.push (← IO.ofExcept <| RuleDiagnostics.contextFinding .admission
            reportRoot.toString failure origin.mode
                .incomplete)
        let scope ← IO.ofExcept <|
          Policy.admitScope report.compilerCapability report.declarations transcripts
        let native := scope.native
        let unsafeHelpers := scope.helpers
        totalDeclarations := totalDeclarations + report.declarations.size
        let mode : Regula.EvidenceMode := origin.mode
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
        -- A declaration Lean generated, or an admitted recursion helper, names the declaration it
        -- was generated from (`Findings.sourceName?_eq_some_iff`), and is located at it when it
        -- has no range of its own.
        let index := Regula.Findings.declarationIndex report.declarations
        -- `ScopeContract` retains `report.declarations` as the inventory, so iterating the
        -- inventory visits the same sequence and supplies each membership proof.
        for h : decl in scope.inventory.declarations do
          if let some id := Policy.ruleForMember decl (some surface.claim) scope h then
            let reason := (Regula.descriptor id).applicability
            -- The finding names the declaration the author wrote (`Policy.subject_contract`).
            let named := Policy.subject decl scope h
            let classification := Policy.subjectDetail decl scope h
            let (sourceDeclaration, related) :=
              Regula.Findings.attribution index unsafeHelpers named
            if id == .profileExceeded && sourceDeclaration.isSome then
              attributedFailures := attributedFailures.insert failures.size
            failures :=
                failures.push s!"{reason}: {named.name} [claim: {surface.claim}] {classification}"
            let location ← IO.ofExcept <|
              Regula.Findings.findingLocation index unsafeHelpers named snapshotFor
            let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding id
                (← IO.ofExcept (RuleDiagnostics.declarationName named))
              classification location
              origin.mode (some surface.claim.toString)
              sourceDeclaration related
            findings := findings.push finding
        -- Equal to `Policy.admitExecution report.execution` (`Admitted.admitExecution_eq`).
        let executionInventory := admitted.execution
        failures := failures ++ Policy.executionFailures executionInventory surface.execution
        for failure in Policy.executionFindings executionInventory surface.execution do
          let location ← match report.declarations.find? (·.name == failure.root.name) with
            | some decl => do
                let snapshot := snapshotFor decl.module
                IO.ofExcept <| RuleDiagnostics.declarationLocation decl snapshot
            | none => pure (Regula.Location.module failure.root.module)
          findings := findings.push
              (← IO.ofExcept <| RuleDiagnostics.executionFinding failure location
            origin.mode surface.execution)
        if verbose then
          for moduleName in info.modules do
            IO.println s!"module {moduleName} [claimed: {surface.claim}]"
            let declarations := report.declarations.filter (·.«module» == moduleName)
              |>.qsort fun left right => Name.quickLt left.name right.name
            for decl in declarations do IO.println s!"  {Policy.classify decl scope}"
        let summary := Policy.executionSummary executionInventory
        executionAccounts := executionAccounts.push (environment.label, executionInventory)
        IO.println <| s!"execution coverage for {environment.label} " ++
          s!"[claim: {surface.execution}]: {summary.roots} root(s), " ++
          s!"{summary.boundaries} boundary(ies) ({summary.checked} checked, " ++
          s!"{summary.trusted} trusted), {summary.unresolved} unresolved"
        -- Every root and boundary is always in `--json-out`; text lists them only on request.
        -- Toolchain-owned boundaries are listed once for the whole audit, after every
        -- environment.
        if verbose then
          for line in Policy.executionAccountLines executionInventory do
            IO.println line
        let withKernelTypes ← kernelTypes.get
        let environmentFields (report : Json) : List (String × Json) := [
          ("modules", toJson info.modules),
          ("authorizedNativeAxioms", toJson native),
          ("authorizedUnsafeRecHelpers", toJson unsafeHelpers),
          ("frontendTranscripts", Json.arr <| transcripts.map
            (Frontend.transcriptResultJson · withKernelTypes)),
          ("report", report)
        ]
        -- Built only for the result output, which omits the import closure; it affects no
        -- decision. A library's entry opens its surface, and each executable's environment
        -- follows it in claim order.
        if resultOut.isSome then
          let fields := environmentFields (report.resultJson withKernelTypes)
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
      let toolchainBase := Policy.toolchainBase executionAccounts
      -- Each toolchain-owned boundary once for the whole audit; its size always, its entries
      -- only on request.
      for line in Policy.toolchainBaseLines toolchainBase verbose do
        IO.println line
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
      -- The one recorded result, even without `--json-out`: its status is the `status` written
      -- below, its tally the summary counts, and its exit code the invocation's. A pending
      -- documentation stage leaves an accepted project incomplete until that stage records.
      let observation : Lint.Observation := match accepted with
        | some (_, ⟨_, run⟩) =>
            if documentationPending then .refused [] true else .accepted (Account.account run)
        | none => refused findings !unresolved.isEmpty
      let status ← record observation
      if let some output := resultOut then
        let ownedModuleNames := environments.flatMap (·.info.modules)
        let sources :=
            (sourceBindings.filter (fun s => ownedModuleNames.contains s.moduleName)).map fun s =>
          Json.mkObj
              [("module", toJson s.moduleName), ("path", toJson s.path),
                  (SourceTexts.textKey, toJson s.content)]
        let surfaceEntries := resultSurfaces.map fun (library, executables) =>
          library.setObjVal! "executables" (Json.arr executables)
        let resultScope := Json.mkObj
            [("project", toJson reportRoot.toString), ("manifest", manifestJson manifest),
            ("modules", toJson ownedModuleNames),
            ("declarations", toJson totalDeclarations),
            ("sources", toJson sources), ("surfaces", toJson surfaceEntries),
            ("toolchainBase", Policy.toolchainBaseJson toolchainBase),
            ("configuration", toJson configuration), ("configurationRoot", toJson repo.toString),
            ("buildOrigin", toJson origin.spelling),
            ("ordinaryLakefiles", toJson (← ordinaryLakefiles.get)),
            ("libraries", toJson (libraries.map libraryInfoJson)),
            ("completedStages", toJson
                #["claimedSourceBuild", "ownedAdmission", "declarationPolicy",
                    "executionInspection"])]
        let mode : Regula.EvidenceMode := origin.mode
        let expected ← expectedStages.get
        if let some (_, ⟨_, accepted⟩) := accepted then
          if documentationPending then
            ResultProtocol.write output resultScope mode status #[] expected
              (ResultProtocol.stagesOf mode) #["documentation audit has not completed"]
          else ResultProtocol.writeAccepted output accepted resultScope
        else
          ResultProtocol.write output resultScope mode status findings expected
            (ResultProtocol.stagesOf mode) unresolved
      RunFeedback.emitAll IO.println findings
      if !failures.isEmpty then
        printSummary observation
        for (failure, index) in failures.zipIdx do
          if attributedFailures.contains index then continue
          let reason := (failure.splitOn ":").head?.getD "violation"
          IO.println s!"  [{reason}] {failure}"
        unless attributedFailures.isEmpty do
          let applicability := (Regula.descriptor .profileExceeded).applicability
          IO.println s!"  [{applicability}] \
            {Regula.Feedback.countText attributedFailures.size "more finding"} on declarations \
            Lean generated, listed above under the declarations it generated them from"
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
      IO.println s!"\n{account.pass "axiom gate"}{origin.qualification}"
      if buildLint then
        IO.println
            s!"{account.pass "build policy linter"} ({account.val.jobs} accepted policy \
              jobs; {account.val.mode.spelling})"
      return 0

/-- Fresh audits copy the project into an owned isolated workspace, or, with `driverCopy`, audit
the copy that the verification driver made (`AxiomGate.driverCopy`). With `--with-docs`,
the documentation stage runs afterwards in this same process against the same frozen
snapshot and build; project and documentation acceptance are then combined. A change of a frozen
source or configuration file during that stage is reported as the project's admission refusal,
which replaces the stage's result. With
`acceptanceLink`, a fresh success also returns the pending identity of its accepted inputs;
only the caller records it, after its own outer recheck. -/
private unsafe def auditSurface (repo : FilePath) (manifest : Option FilePath)
    (incremental verbose : Bool) (withDocs : Bool)
    (composed : IO.Ref (Option Json)) (resultOut : Option FilePath := none)
    (observeConfiguration : FilePath → Array (FilePath × Option String) → IO Unit :=
        fun _ _ => pure ())
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ())
    (buildLint : Bool := false) (acceptanceLink : Bool := false)
    (verso : Option Documentation.VersoPackage := none) (driverCopy : Option FilePath := none) :
    IO (UInt32 × Option AcceptanceLink.Pending) :=
  if incremental then do
    let configuration ← SourceBinding.configuration repo (manifest.getD (Manifest.defaultPath repo))
    observeConfiguration repo configuration
    (·, none) <$> withSourceEvidence #[] configuration repo.toString .incrementalProject
        composed resultOut
      (auditSurfaceAt repo (manifest.getD (Manifest.defaultPath repo)) .incremental verbose repo
          composed resultOut observeSources (buildLint := buildLint))
  else withScratch repo "axiom-gate" fun scratch => do
    -- The copy to audit: the one the verification driver made, when the caller gives it and it
    -- passes what this process can observe, or else a copy this process makes now.
    let origin ← match driverCopy with
      | some path => Origin.driverCopy <$> AxiomGate.driverCopy repo path
      | none => Origin.copied <$> isolatedCopy repo scratch
    let copy := match origin with
      | .copied copied | .driverCopy copied => copied.project
      | .incremental => repo
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
        linked.set (some {
          digest, account := Account.account evidence.accepted, origin := origin.spelling })
    let result ← timedPhase "complete declaration audit" <|
      auditSurfaceAt copy manifestPath origin verbose repo composed resultOut observeSources
        documents observe withDocs
    if result != 0 then return (result, none)
    let some evidence ← project.get
      | throw <| IO.userError "missing accepted project evidence"
    if !withDocs then return (0, ← linked.get)
    let docFindings ← IO.mkRef (#[] : Array Regula.Finding)
    let documentAccepted ← IO.mkRef
        (none : Option ((c : RegulaPolicy.Claim) × RegulaPolicy.AcceptedRun c))
    -- The documentation stage performs the run's terminal freshness recheck. This caller owns
    -- its enclosing frozen-project guard: a source or configuration change during the stage
    -- replaces the stage's result with the project refusal, which the guard renders.
    let some docsResult ← withSourceEvidenceOr none evidence.sources evidence.configuration
        repo.toString .freshProject composed resultOut (some <$>
          Documentation.auditBuiltProject copy (copy / "docs") evidence.inventory
            evidence.sources evidence.configuration evidence.dependencies documents
            evidence.build 4 verbose
            (fun finding => docFindings.modify (·.push finding)) (fun _ => pure ())
            (fun claim accepted => documentAccepted.set (some ⟨claim, accepted⟩))
            (some evidence.snapshot))
      | return (1, none)
    let combined ← if docsResult == 0 then do
        let some ⟨docClaim, accepted⟩ ← documentAccepted.get
          | throw <| IO.userError "missing accepted documentation evidence"
        let receipt ← IO.ofExcept <|
            RegulaPolicy.combineAccepted documents evidence.accepted accepted
        pure (some (⟨docClaim, receipt⟩ : (dc : RegulaPolicy.Claim) ×
          RegulaPolicy.CombinedAccepted evidence.claim dc documents))
      else pure none
    let docs ← docFindings.get
    -- The one recorded result, even without `--json-out`: its status is the `status` written
    -- below. A failed documentation stage without a finding is incomplete.
    let observation : Lint.Observation := match combined with
      | some ⟨_, receipt⟩ => .accepted (Account.account receipt.project)
      | none => refused docs docs.isEmpty
    let status ← record observation
    if combined.isNone then printSummary observation
    if let some output := resultOut then
      let value ← ResultProtocol.readDocument output
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
      ResultProtocol.writeDocument output value
    if let some ⟨_, receipt⟩ := combined then
      let account := Account.account receipt.project
      IO.println s!"combined audit: accepted {account.val.jobs} project \
        and {(Account.account receipt.documentation).val.jobs} documentation jobs"
      for line in account.lines do IO.println line
      IO.println s!"\n{account.pass "axiom gate"}"
      return (0, none)
    return (docsResult, none)

private unsafe def auditFile (repo path : FilePath) (claim : Option Profile)
    (execution : ExecutionClaim) (manifest : Option FilePath) (verbose : Bool)
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
        let claimed ← Manifest.loadFor manifestPath inventory
        let (_, buildResult) ← Lake.buildCheckedObservation repo
          (Lake.claimedTargets claimed) "incrementally" Lake.buildTargetsShowing
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
        -- `none` when the source does not elaborate; otherwise the inspection's outcome, or the
        -- error that stopped the inspection of a source that elaborated.
        let inspection : Option (Except String
            (Except ProducerReport.Refusal SourceAudit.Inspected)) ←
          if !SourceAudit.compilationPassed compilation then pure none
          else try
            pure (some (.ok (← SourceAudit.inspectOutcome compilation inventory.leanPath
              inventory.leanSrcPath inventory.moduleSources (some inventory.leanLibDir))))
          catch error => pure (some (.error error.toString))
        SourceBinding.unchanged dependencySources
        SourceBinding.configurationUnchanged configuration
        SourceBinding.unchanged #[{
          moduleName := moduleName.toName, path := path.toString, content := source }]
        match inspection with
        | none =>
            let output := compilation.process.output
            IO.println s!"FAIL: {path} does not elaborate:"
            let diagnostics := if !(errorLines output).isEmpty then errorLines output
              else takeLast 10 (outputLines output)
            reportContextFailure .sourceBuild path.toString .freshFile
              (if sourceRejected then .violation else .incomplete) [.discovery]
              ("\n".intercalate diagnostics.toList) composed resultOut sources
            return 1
        | some (.error error) =>
            reportContextFailure .environment path.toString .freshFile .incomplete
                [.discovery, .build] s!"inspection of {path} failed: {error}" composed resultOut
                sources
            return 1
        | some (.ok (.error (.admission failure))) =>
            reportContextFailure .admission path.toString .freshFile .incomplete
                [.discovery, .build] failure.detail composed resultOut sources
            return 1
        | some (.ok (.error (.unowned modules))) =>
            let importer (name : Name) :=
              if name == moduleName.toName then path.toString else name.toString
            let findings ← modules.mapM fun unowned => IO.ofExcept <|
              RuleDiagnostics.contextFinding .coverage path.toString (unowned.detail importer)
                .freshFile .violation
            reportContextFindings findings path.toString .freshFile [.discovery, .build] composed
              resultOut sources
            return 1
        | some (.ok (.ok inspected)) =>
            let declarations := inspected.report.declarations.qsort fun left right =>
              Name.quickLt left.name right.name
            let scope ← IO.ofExcept <|
              Policy.admitScope inspected.report.compilerCapability declarations inspected.transcripts
            let native := scope.native
            let unsafeHelpers := scope.helpers
            let mut reasons : Array String := #[]
            let mut findings : Array Regula.Finding := #[]
            let index := Regula.Findings.declarationIndex declarations
            -- The admitted inventory is exactly `declarations` (`ScopeContract`). One member
            -- rule per declaration; its reason is `reasonFor`'s by definition.
            for h : decl in scope.inventory.declarations do
              let rule := Policy.ruleForMember decl claim scope h
              -- A violation line names the finding's subject, as its finding does.
              let (verdict, classification) := match rule with
                | none => ("OK", Policy.classifyMember decl scope h)
                | some id => (s!"VIOLATION[{(Regula.descriptor id).applicability}]",
                    Policy.subjectDetail decl scope h)
              -- Every declaration is in `--json-out`; text lists an accepted one only on request.
              if verbose || rule.isSome then IO.println s!"[{verdict}] {classification}"
              if let some id := rule then
                reasons := reasons.push (Regula.descriptor id).applicability
                -- The finding names the declaration the author wrote (`Policy.subject_contract`).
                let named := Policy.subject decl scope h
                let location ← IO.ofExcept <|
                  Regula.Findings.findingLocation index unsafeHelpers named
                    fun _ => some ⟨path.toString, source⟩
                let (sourceDeclaration, related) :=
                  Regula.Findings.attribution index unsafeHelpers named
                let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding id
                    (← IO.ofExcept (RuleDiagnostics.declarationName named))
                  (Policy.subjectDetail decl scope h) location .freshFile (claim.map Profile.toString)
                  sourceDeclaration related
                findings := findings.push finding
            let executionInventory ← IO.ofExcept <| Policy.admitExecution inspected.report.execution
            let executionViolations := Policy.executionFailures executionInventory execution
            for failure in Policy.executionFindings executionInventory execution do
              let location ← match declarations.find? (·.name == failure.root.name) with
                | some decl => IO.ofExcept <| RuleDiagnostics.declarationLocation decl
                                (some ⟨path.toString, source⟩)
                | none => pure (Regula.Location.module failure.root.module)
              let finding ← IO.ofExcept <| RuleDiagnostics.executionFinding failure location
                  .freshFile execution
              findings := findings.push finding
            RunFeedback.emitAll IO.println findings
            let summary := Policy.executionSummary executionInventory
            let toolchainBase := Policy.toolchainBase #[(path.toString, executionInventory)]
            IO.println <| s!"execution coverage [claim: {execution}]: {summary.roots} root(s), " ++
              s!"{summary.boundaries} boundary(ies) ({summary.checked} checked, {summary.trusted} \
                trusted), " ++
              s!"{summary.unresolved} unresolved"
            for line in Policy.executionAccountLines executionInventory ++
                Policy.toolchainBaseLines toolchainBase true do
              IO.println line
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
            -- The one recorded result: accepted, classified when it found nothing without a
            -- conforming claim, and otherwise refused with its findings, whose status is the one
            -- written below.
            let observation : Lint.Observation := match accepted with
              | some ⟨_, accepted⟩ => .accepted (Account.account accepted)
              | none =>
                  if findings.isEmpty && (claim.isNone || claim == some .compilerTrusting) then
                    .classified
                  else refused findings
            let status ← record observation
            if let some output := resultOut then
              let withKernelTypes ← kernelTypes.get
              let resultScope := Json.mkObj
                  [("file", toJson path.toString), (SourceTexts.textKey, toJson source),
                  ("execution", toJson execution.toString),
                  ("claim", toJson (claim.map Profile.toString)),
                  ("declarations", toJson declarations.size),
                  ("report", inspected.report.resultJson withKernelTypes),
                  ("toolchainBase", Policy.toolchainBaseJson toolchainBase),
                  ("authorizedNativeAxioms", toJson native),
                  ("authorizedUnsafeRecHelpers", toJson unsafeHelpers),
                  ("frontendTranscripts",
                    toJson (inspected.transcripts.map
                      (Frontend.transcriptResultJson · withKernelTypes))),
                  ("configuration", toJson configuration),
                  ("configurationRoot", toJson repo.toString),
                  ("completedStages", toJson
                      #["incrementalDependencies", "freshFileCompilation", "ownedAdmission",
                          "declarationPolicy", "executionInspection"])]
              if let some ⟨_, accepted⟩ := accepted then
                composed.set (some (ResultProtocol.acceptedValue accepted resultScope))
              else
                let expected ← expectedStages.get
                ResultProtocol.write output resultScope .freshFile status findings expected
                  (ResultProtocol.stagesOf .freshFile) #[]
            if !reasons.isEmpty then
              IO.println <| s!"\nfile audit: FAIL ({observation.tally.text})" ++
                (claim.map (fun profile => s!" against claim '{profile}'")).getD ""
              return 1
            if let .refused .. := observation then
              IO.println s!"\nfile audit: FAIL ({observation.tally.text})"
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

/-- A kind of output destination an invocation may name: a result document (`--json-out`) or an
acceptance link (`--acceptance-link`). -/
inductive Destination where
  /-- A result document, named by `--json-out`. -/
  | result
  /-- An acceptance link, named by `--acceptance-link`. -/
  | acceptanceLink
  deriving BEq

/-- The option that names a destination of this kind. -/
def Destination.flag : Destination → String
  | .result => "--json-out"
  | .acceptanceLink => "--acceptance-link"

/-- Before any argument validation, mark every recognisable destination of the `kinds` the calling
interface accepts incomplete, so an earlier completed result cannot be mistaken for this
attempt's. A destination of another kind is left untouched: that interface refuses its option. -/
def invalidateResults (kinds : List Destination) (args : List String) : IO Unit := do
  let destinations := kinds.flatMap fun kind =>
    (optionValues kind.flag args).eraseDups.map fun path =>
      (FilePath.mk path, kind == .acceptanceLink)
  let invalidate (path : FilePath) (link : Bool) :=
    if link then AcceptanceLink.invalidate path else
    ResultProtocol.writeDocument path (Json.mkObj (ResultProtocol.identityFields ++ [
      ("scope", Json.null), ("mode", Json.null), ("status", .str "incomplete"),
      ("diagnostics", toJson (#[] : Array Json)),
      ("unresolved", toJson #["configuration has not been validated"]),
      ResultProtocol.sourceTextsField] ++
      ResultProtocol.guidanceFields false ResultProtocol.allStages [] []))
  -- Absolute destinations do not depend on project configuration being valid.
  for (path, link) in destinations.filter (·.1.isAbsolute) do invalidate path link
  let relative := destinations.filter (!·.1.isAbsolute)
  if !relative.isEmpty then
    let root ← match optionValues "--project" args with
      | [dir] => findRepoRoot dir
      | [] => repoRoot
      | _ => throw <| IO.userError "duplicate --project option"
    for (path, link) in relative do invalidate (resolve root path) link

/-- The options of an audit invocation: parsed, without a duplicated option, and in a
combination the usage text allows; otherwise an error naming the problem. The usage text does
not list the internal `--driver-copy`, which is admitted only in the fresh surface mode of the
current project, without `--with-docs` and `--project`. -/
private def admitOptions (args : List String) : IO Options := do
  for flag in #["--json-out", "--acceptance-link", "--project", "--file",
      "--manifest", "--claim", "--execution", "--driver-copy"] do
    if (optionValues flag args).length > 1 then
      throw <| IO.userError s!"duplicate {flag} option"
  let options ← parseArgs args {}
  if options.help then return options
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
  if options.driverCopy.isSome &&
      (options.file.isSome || options.incremental || options.withDocs || options.project.isSome) then
    throw <| IO.userError "--driver-copy applies only to the fresh surface mode of the current \
      project, without --with-docs and --project"
  if options.verso.isSome && options.acceptanceLink.isNone then
    throw <| IO.userError "--verso applies only to --acceptance-link"
  if options.kernelTypes && options.resultOut.isNone then
    throw <| IO.userError "--kernel-types applies only to --json-out"
  return options

/-- Refuse an invalid invocation: the usage text and the problem, and the invalid-configuration
exit code, since no audit ran and no result was recorded. -/
private def refuseInvocation (message : String) : IO UInt32 := do
  IO.eprintln usage
  IO.eprintln s!"FAIL: invalid invocation: {message}"
  return Lint.Outcome.configuration.exitCode

/-- Run one `axiomGate` invocation and return its exit code. The internal forms
`--validate-site`, `--registry-out`, `--validate-registry` and `--replacement-history-worker`
do only that job; otherwise it invalidates earlier results at the requested output paths,
parses and checks the options, audits the single file or the manifested project surfaces, and
writes the result JSON and the acceptance link that were requested. An audit returns the exit code
of the result it recorded (`Lint.gateExitCode`): 0 accepted or classified, 1 violation, 2 invalid
configuration, 3 incomplete; an invalid invocation returns 2, and `--help` and the internal forms
0 when they succeed. -/
unsafe def run (args : List String) : IO UInt32 := do
  terminalObservation.set none
  RunFeedback.reset
  expectedStages.set ResultProtocol.allStages
  -- An invalid invocation is refused as one, though its destinations could not be invalidated.
  try invalidateResults [.result, .acceptanceLink] args
  catch error =>
    let admitted ← (admitOptions args).toBaseIO
    if let .error invalid := admitted then return ← refuseInvocation invalid.toString
    throw error
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
  if let ["--module-graph-worker", input, out] := args then
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request : ModuleGraphRequest ← IO.ofExcept (fromJson? json)
    let guarded ← SourceBinding.withUnchanged request.sourceBindings #[] <|
      Environment.loadModuleGraph request.modules (request.searchRoots.map FilePath.mk)
    let graph ← IO.ofExcept <| guarded.mapError (·.detail)
    writeJson out (workerPacket json (toJson graph))
    return 0
  if let ["--declaration-report-worker", input, out] := args then
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request : ReportWorkerRequest ← IO.ofExcept (fromJson? json)
    let guarded ← SourceBinding.withUnchanged
        (α := Except ProducerReport.Refusal ProducerReport.Environment)
        request.sourceBindings #[] do
      let outcome ← Environment.loadReportOutcome request.modules
        (request.searchRoots.map FilePath.mk) (request.sourceRoots.map FilePath.mk)
        (request.sourceBindings.map fun source => (source.moduleName, FilePath.mk source.path))
        (some (FilePath.mk request.ownedOutput)) (validateReport := false)
        (historyMemo := some (FilePath.mk request.historyMemo)) (priors := request.priors)
        (publish := some (FilePath.mk request.publish))
      if let .ok report := outcome then
        if let .error failure := SourceBinding.validateAgainst request.sourceBindings report then
          return .error (.admission failure)
      return outcome
    writeJson out (workerPacket json (toJson (ProducerReport.Outcome.ofExcept
      ((guarded.mapError ProducerReport.Refusal.admission).bind id))))
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
  let admitted ← (admitOptions args).toBaseIO
  if let .error error := admitted then return ← refuseInvocation error.toString
  let .ok options := admitted | return Lint.Outcome.configuration.exitCode
  if options.help then IO.println usage; return 0
  if options.verbose then timing.set true
  kernelTypes.set options.kernelTypes
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
    let observation := refused #[finding]
    let status ← record observation
    printSummary observation
    if let some output := resultOut then
      let captured ← capturedSourceAccount resultOut (← capturedSources.get)
      ResultProtocol.writeDocument output <|
        (ResultProtocol.resultJson (Json.str repo.toString) mode status #[finding]
          (← expectedStages.get) [] #[error.toString]).setObjVal! "sourceAccount" captured
    return 1
  let action : IO (UInt32 × Option AcceptanceLink.Pending) := do
    try
      match options.file with
      | some path =>
          return (← auditFile repo (resolve repo path) options.claim options.execution
            (options.manifest.map (resolve repo)) options.verbose composed resultOut
            observeConfiguration observeSources, none)
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
            (driverCopy := options.driverCopy)
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
      ResultProtocol.writeDocument output (ResultProtocol.composedFinal base
        (← capturedSourceAccount resultOut (← capturedSources.get))
        (ProducerReport.sourceAccountJson (← capturedSources.get)) request
        (toJson (← effective.get)))
    | none =>
      let value ← ResultProtocol.readDocument output
      let captured ← capturedSources.get
      let value := if (value.getObjVal? "sourceAccount").isOk then value
        else value.setObjVal! "sourceAccount" (ProducerReport.sourceAccountJson captured)
      ResultProtocol.writeDocument output
          ((value.setObjVal! "request" request).setObjVal! "effective" (toJson (← effective.get)))
  if code == 0 then
    if let (some path, some pending) := (acceptanceLink, linked) then
      AcceptanceLink.record path pending
      IO.println s!"acceptance link: recorded {pending.digest}"
  -- The exit code is the recorded result's (`Lint.gateExitCode`).
  return Lint.gateExitCode code (← terminalObservation.get)

/-- The `axiomGate` executable body: search-path initialization, then `run`, with
any escaping error reported as `FAIL` and the incomplete exit code 3, since no result was
established; a result recorded before the error is discarded, so for an audit invocation the
code returned is `Lint.gateExitCode` of what remains recorded whether `run` returns or an error
escapes it. `AxiomGateMain` is the user-facing entry; the qualification-only
`ruleExamples --injected-git-facts` entry reuses this exact body. -/
unsafe def entry (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    run args
  catch error =>
    terminalObservation.set none
    IO.eprintln s!"FAIL: {error}"
    return Lint.Outcome.incomplete.exitCode

end Regula.Checker.AxiomGate
