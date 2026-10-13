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

/-- The command-line options of one `axiomGate` invocation, as `admit` reads them; `admit`
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

/-- The options of `axiomGate`, as its one reading of its arguments (`arguments`) names them. -/
inductive Setting where
  /-- `--file FILE`. -/
  | file
  /-- `--claim PROFILE`. -/
  | claim
  /-- `--execution MODE`. -/
  | execution
  /-- `--manifest PATH`. -/
  | manifest
  /-- `--project DIR`. -/
  | project
  /-- `--json-out PATH`. -/
  | jsonOut
  /-- `--acceptance-link PATH`. -/
  | acceptanceLink
  /-- `--verso DIR:LIBRARY:RENDER`. -/
  | verso
  /-- `--driver-copy PATH`. -/
  | driverCopy
  /-- `--with-docs`. -/
  | withDocs
  /-- `--incremental`. -/
  | incremental
  /-- `--build-lint`. -/
  | buildLint
  /-- `--verbose`. -/
  | verbose
  /-- `--kernel-types`. -/
  | kernelTypes
  /-- `--help` or `-h`. -/
  | help
  deriving DecidableEq

/-- Every option of `axiomGate`. -/
def Setting.all : List Setting :=
  [.file, .claim, .execution, .manifest, .project, .jsonOut, .acceptanceLink, .verso, .driverCopy,
    .withDocs, .incremental, .buildLint, .verbose, .kernelTypes, .help]

/-- How `axiomGate` spells each option. -/
def Setting.spelling : Setting → String
  | .file => "--file" | .claim => "--claim" | .execution => "--execution"
  | .manifest => "--manifest" | .project => "--project" | .jsonOut => "--json-out"
  | .acceptanceLink => "--acceptance-link" | .verso => "--verso" | .driverCopy => "--driver-copy"
  | .withDocs => "--with-docs" | .incremental => "--incremental" | .buildLint => "--build-lint"
  | .verbose => "--verbose" | .kernelTypes => "--kernel-types" | .help => "--help"

/-- Whether an option takes a value. -/
def Setting.takesValue : Setting → Bool
  | .file | .claim | .execution | .manifest | .project | .jsonOut | .acceptanceLink | .verso
    | .driverCopy => true
  | .withDocs | .incremental | .buildLint | .verbose | .kernelTypes | .help => false

/-- The option an argument spells, and whether it takes a value. -/
def Setting.ofSpelling (argument : String) : Option (Setting × Bool) :=
  if argument = "-h" then some (.help, false)
  else (Setting.all.find? (·.spelling == argument)).map fun setting =>
    (setting, setting.takesValue)

/-- `axiomGate`'s one reading of its arguments (`Lint.tokenize`): an option's value is never read
as an option. `Plan.of` reads it one time, and the options (`admit`), the project root and every
destination the audit writes (`destinations`) come from that one reading. -/
def arguments (args : List String) : List (Lint.Arg Setting) :=
  Lint.tokenize Setting.ofSpelling args

/-- Apply one argument. An unknown or incomplete argument, a profile or execution mode that does
not parse and a malformed `--verso` are refused. The destinations of `--json-out` and
`--acceptance-link` are taken from `destinations`, not here. -/
private def Options.apply (o : Options) : Lint.Arg Setting → Except String Options
  | .separator => .ok o
  | .value .file value => .ok { o with file := some (FilePath.mk value) }
  | .value .claim value => match Profile.parse? value with
    | some claim => .ok { o with claim := some claim }
    | none => .error s!"unknown foundation profile: {value}"
  | .value .execution value => match ExecutionClaim.parse? value with
    | some mode => .ok { o with execution := mode }
    | none => .error s!"unknown execution mode: {value}"
  | .value .manifest value => .ok { o with manifest := some (FilePath.mk value) }
  | .value .project value => .ok { o with project := some (FilePath.mk value) }
  | .value .jsonOut _ | .value .acceptanceLink _ => .ok o
  | .value .verso value => (Documentation.parseVersoOption value).map fun verso =>
    { o with verso := some verso }
  | .value .driverCopy value => .ok { o with driverCopy := some (FilePath.mk value) }
  | .flag .withDocs => .ok { o with withDocs := true }
  | .flag .incremental => .ok { o with incremental := true }
  | .flag .buildLint => .ok { o with buildLint := true, incremental := true }
  | .flag .verbose => .ok { o with verbose := true }
  | .flag .kernelTypes => .ok { o with kernelTypes := true }
  | .flag .help => .ok { o with help := true }
  | .value setting _ | .flag setting =>
    .error s!"unknown or incomplete argument: {setting.spelling}"
  | .unknown argument => .error s!"unknown or incomplete argument: {argument}"

/-- Apply each argument in order, stopping at the first refusal. -/
private def Options.applyAll : List (Lint.Arg Setting) → Options → Except String Options
  | [], o => .ok o
  | a :: rest, o => do Options.applyAll rest (← o.apply a)

private def resolve (repo path : FilePath) : FilePath :=
  if path.isAbsolute then path else repo / path.toString

/-- The recorded result of the current invocation, set wherever a project, file or combined
documentation audit decides its result status, including without `--json-out`. Its status is
the one the result output renders, its tally the summary counts, and its exit code the one
`run` returns (`Lint.Observation`); `lint` derives its exit class from it and the exit code
(`Lint.classify`). -/
initialize terminalObservation : IO.Ref (Option Lint.Observation) ← IO.mkRef none

/-- The project root and manifest path the current invocation audits, set when its options are
admitted (`none` until then): the root of `--project` or of the working directory, and
`--manifest` resolved against that root or the root's `foundation_manifest.json`. A fresh audit
reads the default manifest from its isolated copy of that root, and an explicit `--manifest` at
that resolved path. `lint` names them in its success line. -/
initialize auditedTarget : IO.Ref (Option (FilePath × FilePath)) ← IO.mkRef none

/-- The result destination of the current invocation's plan (`Plan.target`), resolved and marked
incomplete, set when the plan is read, whether or not the invocation is admitted (`none` until then,
when it names none, or when it did not resolve). `ruleExamples` marks its injected result there.
-/
initialize resultTarget : IO.Ref (Option FilePath) ← IO.mkRef none

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
(`REGULA_ORDINARY_LAKEFILES=1` in the environment of `lake lint`), set by the `lint` driver for
its own audit. The project result records it as `scope.ordinaryLakefiles`. -/
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
      ("rationale", Json.str surface.rationale),
      ("decides", Json.arr <| surface.decides.map Json.str)
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

/-- `cleanup`, run after the run failed with `failure`: an error it throws is replaced by one
error whose text names `failure` first and then that error. -/
private def afterFailure {α : Type} (failure : IO.Error) (cleanup : IO α) : IO α :=
  try cleanup
  catch refusal => throw <| IO.userError s!"{failure}; then: {refusal}"

/-- `action`, then `retainSourceAccount`. When `action` throws, its error is rethrown, with any
error of `retainSourceAccount` added after it (`afterFailure`). -/
private def withRetainedSources {α : Type} (resultOut : Option FilePath)
    (composed : IO.Ref (Option Json))
    (captured : IO.Ref (Array ProducerReport.SourceBinding)) (action : IO α) : IO α := do
  let value ← try action catch failure => do
    afterFailure failure (retainSourceAccount resultOut composed (← captured.get))
    throw failure
  retainSourceAccount resultOut composed (← captured.get)
  return value

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
  /-- The root of the copied project. -/
  project : FilePath
  /-- The real directory of the copy, below which every owned module must resolve
  (`Lake.ProjectCopy.root`). -/
  root : FilePath
  /-- What the copy's Lake load must select (`Lake.ProjectCopy.selection`): the root package's
  targets and where each dependency package is loaded from, or `none` for a copy the verification
  driver made, which must own no dependency. -/
  selection : Option Lake.CopySelection
  /-- Captured source selections for configuration generated by this process, or none for the cold driver. -/
  configurationInputs : Option Regula.CopyConfiguration.Inputs

/-- Copy the project at `repo`, with each path dependency it owns, into the new scratch directory
`scratch`, which holds no build output (`copyProject`) but the running Regula's observer library
(`ProjectCopy.placeObservers`). -/
private def isolatedCopy (repo scratch : FilePath) (manifest : Option FilePath)
    (selectedFiles : List FilePath) : IO Copied := do
  let copy ← timedPhase "isolated source copy" <| Lake.copyProject repo (scratch / "project")
    scratch (facets := .replaced) (policy := manifest) (selectedFiles := selectedFiles)
  copy.placeObservers
  return ⟨copy.project, copy.root, some copy.selection, some copy.configurationInputs⟩

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
  return ⟨copy, copy, none, none⟩

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
  -- The modules that this audit's own builds elaborate, created here so no other audit reads them.
  let elaborated : Lake.Elaborated ← IO.mkRef #[]
  let configuration ← SourceBinding.configuration repo manifestPath
  withSourceEvidence #[] configuration reportRoot.toString
      origin.mode composed resultOut do
    -- A copy loads each dependency from where the original's Lake load requires, and each owned
    -- module that an environment loads must come from the copy's own build
    -- (`Environment.ModuleGraph.outsideCopy`). The audit's one facet report comes from this
    -- inventory, or for a copy that `isolatedCopy` made, from its inventory of the original.
    let inventory ← match origin with
      | .copied copy =>
          Lake.checkCopiedWorkspace copy.root copy.selection (← Lake.surfaceInventory repo)
      | .driverCopy copy =>
          Lake.checkCopiedWorkspace copy.root copy.selection
            (← Lake.surfaceInventory repo (facets := .replaced))
      | .incremental => Lake.surfaceInventory repo (facets := .replaced)
    let sourceBindings ← SourceBinding.capture inventory.moduleSources observeSources
    -- Each owned dependency's sources are captured with its package, since two packages can give
    -- one module name different sources; each environment binds those it loads
    -- (`Environment.dependencyBindings`).
    let packageBindings ← (inventory.dependencies.filter (·.owned)).mapM fun dependency => do
      return (dependency.leanLibDir, ← SourceBinding.capture
        (dependency.sources.map fun source => (source.«module», source.source)))
    let allBindings := sourceBindings ++ packageBindings.flatMap (·.2)
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
      SourceBinding.configurationUnchanged configuration
      let buildPlan := Lake.claimedBuildPlan manifest inventory
      let (initialBuild, buildResult) ← timedPhase "claimed-source build" <|
          Lake.buildCheckedObservation repo buildPlan.initialTargets
              origin.label (← claimedBuild.get) elaborated
      SourceBinding.unchanged allBindings
      SourceBinding.configurationUnchanged configuration
      if let some lines := buildResult then
        reportContextFailure .sourceBuild reportRoot.toString
          origin.mode .incomplete
              [.configuration, .discovery]
          ("\n".intercalate lines.toList) composed resultOut sourceBindings
        return 1
      SourceBinding.unchanged allBindings
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
      let requestOf (environment : SurfaceEnvironment) : ModuleGraphRequest := {
        modules := environment.info.modules
        searchRoots := inventory.leanPath.map (·.toString)
        sourceBindings
      }
      let observeOf (environment : SurfaceEnvironment) : IO Environment.ModuleGraph :=
        timedPhase s!"module scope {environment.label}" <|
          runTypedWorker "--module-graph-worker" (requestOf environment)
      -- Each environment's first graph comes from its own worker process, which reads only the
      -- environment's imports, so three run at once, as the inspections do. Each outcome, an
      -- error included, is kept as a value. The rest of each scope, which in a copy can build
      -- owned modules there, runs below one environment at a time in claim order. A first graph
      -- read before an earlier environment's build is read again (`builtEarlier`), so the
      -- builds, the findings and their order are those of observing the environments one by
      -- one.
      let firstGraphs ← mapWorkQueue 3 environments fun environment =>
        (observeOf environment).toBaseIO
      -- Whether an environment observed earlier below asked for an owned-module build in the
      -- copy.
      let builtEarlier ← IO.mkRef false
      -- Each environment with the modules of owned dependencies it inspects, from its graph.
      let mut graphedEnvironments : Array SurfaceEnvironment := #[]
      for (environment, firstGraph) in environments.zip firstGraphs do
        let request := requestOf environment
        let observed ← (do
          let observe := observeOf environment
          -- The declaration worker's ownership, from the same inputs
          -- (`Environment.EnvironmentOwnership.of`).
          let ownership := inventory.ownership
          let bound := request.sourceBindings.map ProducerReport.SourceBinding.moduleName
          let ownedIn (graph : Environment.ModuleGraph) :
              IO (Environment.EnvironmentOwnership × Array (Lean.Name × Nat)) := do
            -- A loaded module of an owned package that is not its artifact fails this
            -- environment's scope (`Environment.attributeLoaded`).
            let loaded ← IO.ofExcept (← Environment.attributeLoaded graph.moduleOrigins ownership)
            return (Environment.EnvironmentOwnership.of graph.moduleOrigins request.modules bound
              (loaded.map Prod.fst), loaded)
          let mut graph ← if ← builtEarlier.get then observe else IO.ofExcept firstGraph
          let mut fresh : Array String := #[]
          if let some copy := ownership.copy then
            -- In a copy, an owned module that the claimed build did not build, such as one that
            -- only the force-loaded reporter imports, resolves elsewhere: the copy builds each
            -- such module once, and the graph is observed again. One that still resolves outside
            -- the copy is refused.
            let mut built : Array Name := #[]
            repeat
              let current ← ownedIn graph
              let outside : Array (Lean.Name × String) ← graph.outsideCopy current.1 copy
              let pending := outside.filter fun (entry : Lean.Name × String) =>
                !built.contains entry.1
              if pending.isEmpty then
                fresh := outside.map (Environment.outsideCopyDetail copy)
                break
              built := built ++ pending.map (fun (entry : Lean.Name × String) => entry.1)
              builtEarlier.set true
              let (_, failed) ← timedPhase s!"owned module build {environment.label}" <|
                Lake.buildCheckedObservation repo
                  (pending.map fun (entry : Lean.Name × String) => .moduleArtifacts entry.1)
                  origin.label (← claimedBuild.get)
              if let some lines := failed then
                fresh := #[s!"surface-not-fresh: the copy did not build the owned modules \
                  {pending.map (fun (entry : Lean.Name × String) => entry.1)}: \
                  {"\n".intercalate lines.toList}"]
                break
              graph ← observe
          unless fresh.isEmpty do
            return (fresh, (#[] : Array ProducerReport.UnownedModule), (#[] : Array String),
              (#[] : Array Name), (#[] : Array ProducerReport.SourceBinding))
          let ordinary ← graph.ordinaryModules
          let failures ← graph.requestedFailures ordinary
            (graph.scopeRequests request.modules positiveModules) inventory.leanLibDir
          unless failures.isEmpty do
            return (failures, (#[] : Array ProducerReport.UnownedModule), (#[] : Array String),
              (#[] : Array Name), (#[] : Array ProducerReport.SourceBinding))
          let (owned, loaded) ← ownedIn graph
          -- The sources of the dependency modules it inspects, each from the package it loads the
          -- module from.
          let (dependencySources, unbound) :=
            Environment.dependencyBindings owned loaded (packageBindings.map Prod.snd)
          unless unbound.isEmpty do
            return (unbound.map (fun (name : Lean.Name) => s!"surface-omission: owned dependency \
                module {name} has no single owned package whose source it loads"),
              (#[] : Array ProducerReport.UnownedModule), (#[] : Array String),
              (#[] : Array Name), (#[] : Array ProducerReport.SourceBinding))
          let unowned ← graph.unownedModules owned ownership.outputs
          unless unowned.isEmpty do
            return (#[], unowned, #[], owned.dependencies, dependencySources)
          let details ← graph.importDetails ordinary excludedModules configuredModules
            inventory.leanLibDir environment.surface.library
          return (#[], #[], details, owned.dependencies, dependencySources)).toBaseIO
        match observed with
          | .ok (failures, unowned, details, dependencies, dependencySources) =>
            graphedEnvironments :=
              graphedEnvironments.push { environment with dependencies, dependencySources }
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
            graphedEnvironments := graphedEnvironments.push environment
      let environments := graphedEnvironments
      for unowned in scopeUnowned do
        scopeFindings := scopeFindings.push (← IO.ofExcept <|
          RuleDiagnostics.contextFinding .coverage reportRoot.toString unowned.detail mode .violation)
      SourceBinding.unchanged allBindings
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
              origin.label build elaborated)
      SourceBinding.unchanged allBindings
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
      SourceBinding.unchanged allBindings
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
          transcripts := inspected.transcripts, expectedDependencies := environment.dependencies
          dependencySources := environment.dependencySources } :
            Acceptance.RequestedInspection)
      -- The claim owns each dependency module some environment inspects, once.
      let dependencyNames := environments.foldl (fun names environment =>
        names ++ environment.dependencies.filter (!names.contains ·)) (#[] : Array Lean.Name)
      let ownedDependencies := dependencyNames.mapM RegulaPolicy.admitIdentity
      -- Each declaration's profile and each root's requests come from its own module's assignment
      -- in the claim, from the same values the claim admits (`RegulaPolicy.profileForModule_project`,
      -- `RegulaPolicy.executionForModule_project`), never from the surface that imports it.
      let assignedDependencies := match ownedDependencies with
        | .ok identities => identities
        | .error _ => #[]
      let profileOf (moduleName : Lean.Name) : Option Policy.Profile :=
        (RegulaPolicy.projectProfile assignments assignedDependencies moduleName).map
          Policy.Profile.ofConforming
      let freezeRequest : IO (RegulaPolicy.AdmittedSnapshot ×
          ((c : RegulaPolicy.Claim) × Acceptance.Frozen c)) := do
        let histories ← IO.ofExcept <| Acceptance.historyObservations rawInspections
        let snapshotSources ← Acceptance.sourceSnapshots allBindings histories documents
        let snapshot ← IO.ofExcept <| Snapshot.make repo configuration snapshotSources dependencies
        let ownedDependencies ← IO.ofExcept ownedDependencies
        let request ← IO.ofExcept <| RegulaPolicy.admitClaim {
          scope := .project, mode := origin.mode,
          snapshot := snapshot.val, surfaces := assignments, dependencies := ownedDependencies }
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
      let mut sourceReported : Std.HashSet Name := {}
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
      -- RG1008 counts, toward each environment's registered decisions, the recorded contracts of
      -- the surfaces the manifest relates to its own, from the declarations and module origins of
      -- every environment, as the census binds them (`RegulaPolicy.countedFor`).
      let countedInputs := inspections.filterMap fun (_, outcome) =>
        match outcome with
        | .ok (.ok inspected) =>
            some (inspected.admitted.report.declarations, inspected.admitted.report.moduleOrigins)
        | _ => none
      for (environment, outcome) in inspections do
        let surface := environment.surface
        -- Locations come from this environment's own bindings, those of the dependency modules it
        -- inspects included.
        let snapshotFor (name : Name) : Option Regula.SourceSnapshot :=
          ((sourceBindings ++ environment.dependencySources).find? (·.moduleName == name)).map
            fun s => ⟨s.path, s.content⟩
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
        -- A declaration belongs to a requested module or to an inspected dependency module.
        if report.declarations.any fun decl => !info.modules.contains decl.«module» &&
            !environment.dependencies.contains decl.«module» then
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
            report.imported
        let scope := scope.counting <| RegulaPolicy.countedContracts assignments countedInputs
          surface.library report.declarations report.moduleOrigins
        let native := scope.native
        let unsafeHelpers := scope.helpers
        totalDeclarations := totalDeclarations + report.declarations.size
        let mode : Regula.EvidenceMode := origin.mode
        let some documentation := report.documentation
          | throw <| IO.userError "producer-documentation: project observations unavailable"
        -- RG5001: the proved `RegulaPolicy.ModuleHeader.failures` decides each module's header
        -- observation (documentation present, first after the imports, no repeated import).
        -- A module of an owned dependency, which several environments can inspect, is reported
        -- once, under its own profile.
        for (moduleName, observation) in documentation.modules do
          let moduleFindings ← IO.ofExcept <| Regula.Linter.Documentation.moduleFindings
            moduleName observation mode ((profileOf moduleName).map (·.toString))
          for finding in moduleFindings do
            if findings.any (·.entry == finding.entry) then continue
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
        -- RG2006: the options that the source of each module of this environment set, from the
        -- claimed build's decision on its record (`Observer.decideRecord`), decided by the proved
        -- `RegulaPolicy.Community.sourceFailures` (`sourceFailures_eq_nil_iff`) under the
        -- target's options. A module that several environments inspect is decided once, under
        -- the first. A module without a record fails, since what its source set is unknown.
        for moduleName in info.modules do
          if sourceReported.contains moduleName then continue
          sourceReported := sourceReported.insert moduleName
          let detail := match buildProcess.verdicts.find? (·.1 == moduleName) with
            | some (_, verdict) => verdict.sourceDetail moduleName.toString options mathlib
            | none => some s!"community-configuration: {moduleName} has no record of \
                Regula's elaboration observer, so the options its source set are unknown"
          if let some detail := detail then
            let finding ← IO.ofExcept <| Regula.makeDiagnostic .communityConfiguration
              ⟨target, detail⟩ (.project reportRoot.toString) mode (some surface.claim.toString)
              .violation
            findings := findings.push ⟨.communityConfiguration, finding⟩
            failures := failures.push s!"community-configuration: {moduleName}"
        for (key, docstring) in documentation.declarations do
          -- The proved classification (`materialDocumentationFailure_eq_none_iff`) of the
          -- recorded docstring decides RG5002 (none attached) or RG5003 (no Intent section).
          let some failure := RegulaPolicy.materialDocumentationFailure docstring | continue
          let id := Regula.ruleForMaterialDocumentation failure
          let some decl := report.declarations.find? (fun d => (d.module, d.name) == key)
            | throw <| IO.userError "producer-documentation: selected declaration missing"
          let snapshot := snapshotFor key.1
          let location ← IO.ofExcept <| RuleDiagnostics.declarationLocation decl snapshot
          let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding
            id key.2 (Regula.materialDocumentationDetail failure)
            location mode ((profileOf key.1).map (·.toString))
          if findings.any (·.entry == finding.entry) then continue
          findings := findings.push finding
          failures := failures.push s!"{(Regula.descriptor id).applicability}: {key.2}"
        -- A declaration Lean generated, or an admitted recursion helper, names the declaration it
        -- was generated from (`Findings.sourceName?_eq_some_iff`), and is located at it when it
        -- has no range of its own.
        let index := Regula.Findings.declarationIndex report.declarations
        -- `ScopeContract` retains `report.declarations` as the inventory, so iterating the
        -- inventory visits the same sequence and supplies each membership proof.
        for h : decl in scope.inventory.declarations do
          let profile := profileOf decl.module
          if let some id := Policy.ruleForMember decl profile scope h then
            let reason := (Regula.descriptor id).applicability
            -- The finding names the declaration the author wrote (`Policy.subject_contract`).
            let named := Policy.subject decl scope h
            let classification := Policy.subjectDetail decl scope h
            let (sourceDeclaration, related) :=
              Regula.Findings.attribution index unsafeHelpers named
            let location ← IO.ofExcept <|
              Regula.Findings.findingLocation index unsafeHelpers named snapshotFor
            let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding id
                (← IO.ofExcept (RuleDiagnostics.declarationName named))
              classification location
              origin.mode (profile.map (·.toString))
              sourceDeclaration related
            -- A declaration of an owned dependency that several environments inspect is
            -- reported once.
            if findings.any (·.entry == finding.entry) then continue
            if id == .profileExceeded && sourceDeclaration.isSome then
              attributedFailures := attributedFailures.insert failures.size
            let claimText := (profile.map (·.toString)).getD "none"
            failures :=
                failures.push s!"{reason}: {named.name} [claim: {claimText}] {classification}"
            findings := findings.push finding
        -- Equal to `Policy.admitExecution report.execution` (`Admitted.admitExecution_eq`).
        let executionInventory := admitted.execution
        -- Each root is held to the strongest execution claim that the modules of the declarations
        -- naming it request (`RegulaPolicy.rootRequestsAmong`, as `RegulaPolicy.rootRequests`
        -- asks them of the claim); `RegulaPolicy.executionFindingsFor_empty_iff` relates these
        -- findings to acceptance's execution condition.
        let requestsOf (root : RegulaPolicy.ExecutionRoot) : Array RegulaPolicy.ExecutionClaim :=
          RegulaPolicy.rootRequestsAmong
            (RegulaPolicy.projectExecution assignments assignedDependencies)
            scope.inventory.declarations root.name
        for failure in RegulaPolicy.executionFindingsFor executionInventory requestsOf do
          let location ← match report.declarations.find? (·.name == failure.root.name) with
            | some decl => do
                let snapshot := snapshotFor decl.module
                IO.ofExcept <| RuleDiagnostics.declarationLocation decl snapshot
            | none => pure (Regula.Location.module failure.root.module)
          let finding ← IO.ofExcept <| RuleDiagnostics.executionFinding failure location
            origin.mode (RegulaPolicy.strongestClaim (requestsOf failure.root))
          if findings.any (·.entry == finding.entry) then continue
          failures := failures.push (Policy.executionFailureLine failure)
          findings := findings.push finding
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
        -- Toolchain-owned boundaries are listed for the whole audit, after every environment:
        -- each as an entry or as a `partial` implementation an entry names.
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
      -- The toolchain trusted base of the whole audit (`Policy.toolchainBase`); its size always,
      -- its entries only on request.
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
        let decides := if surface.decides.isEmpty then "" else
          s!"; its decision registrations count toward {", ".intercalate surface.decides.toList}"
        IO.println <| s!"claimed profile for {surface.library}: {surface.claim} " ++
          s!"(execution: {surface.execution}{decides})"
      for excluded in manifest.excludedLibraries do
        let count := (libraries.find? (·.name == excluded.library)).map (·.modules.size) |>.getD 0
        IO.println s!"excluded library {excluded.library}: {count} module(s)"
      for excluded in manifest.excludedExecutables do
        IO.println s!"excluded executable {excluded.executable}"
      SourceBinding.unchanged allBindings
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
            ("manifestPath", toJson ((← auditedTarget.get).map (·.2.toString))),
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
    (observeConfiguration : FilePath → Array (FilePath × Option String) →
        Option Regula.CopyConfiguration.Inputs → IO Unit := fun _ _ _ => pure ())
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ())
    (buildLint : Bool := false) (acceptanceLink : Bool := false)
    (verso : Option Documentation.VersoPackage := none) (driverCopy : Option FilePath := none) :
    IO (UInt32 × Option AcceptanceLink.Pending) :=
  if incremental then do
    let configuration ← SourceBinding.configuration repo (manifest.getD (Manifest.defaultPath repo))
    observeConfiguration repo configuration none
    (·, none) <$> withSourceEvidence #[] configuration repo.toString .incrementalProject
        composed resultOut
      (auditSurfaceAt repo (manifest.getD (Manifest.defaultPath repo)) .incremental verbose repo
          composed resultOut observeSources (buildLint := buildLint))
  else withScratch repo "axiom-gate" fun scratch => do
    let originalDocuments ← if withDocs then Documentation.captureMarkdown (repo / "docs") else pure #[]
    -- The copy to audit: the one the verification driver made, when the caller gives it and it
    -- passes what this process can observe, or else a copy this process makes now.
    let origin ← match driverCopy with
      | some path => Origin.driverCopy <$> AxiomGate.driverCopy repo path
      | none => Origin.copied <$> (isolatedCopy repo scratch manifest
          (originalDocuments.toList.map (FilePath.mk ·.uri)))
    let copy := match origin with
      | .copied copied | .driverCopy copied => copied.project
      | .incremental => repo
    let copyRoot := match origin with
      | .copied copied | .driverCopy copied => copied.root
      | .incremental => repo
    let manifestPath := (manifest.map (Lake.relocateConfigurationPath repo copy)).getD
      (Manifest.defaultPath copy)
    let inputs := match origin with
      | .copied copied | .driverCopy copied => copied.configurationInputs
      | .incremental => none
    observeConfiguration copy (← SourceBinding.configuration copy manifestPath) inputs
    let documents := Documentation.relocateMarkdown repo copy originalDocuments
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
        let digest ← AcceptanceLink.identity scratch copy copyRoot (repo / "docs")
          evidence.sources evidence.configuration evidence.dependencies linkedDocuments
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
        Documentation.checkMarkdown (repo / "docs") originalDocuments
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
    (observeConfiguration : FilePath → Array (FilePath × Option String) →
        Option Regula.CopyConfiguration.Inputs → IO Unit := fun _ _ _ => pure ())
    (observeSources : Array ProducerReport.SourceBinding → IO Unit := fun _ => pure ()) :
        IO UInt32 := do
  let manifestPath := manifest.getD (Manifest.defaultPath repo)
  let configuration ← SourceBinding.configuration repo manifestPath
  observeConfiguration repo configuration none
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
        -- The decision on the record of Regula's elaboration observer, which the compilation loaded
        -- (`Compilation.observe`), as a claimed build's: RG2003 here, what the compilation's
        -- messages do not show, and RG2006 with the declarations below, the options its source set.
        let verdict ← if claim.isSome && SourceAudit.compilationPassed compilation then
            some <$> compilation.observe path.toString
          else pure none
        if let some verdict := verdict then
          unless verdict.hidden.isEmpty do
            reportContextFailure .sourceBuild path.toString .freshFile .incomplete [.discovery]
              ("\n".intercalate
                (Observer.hiddenReport s!"the compilation of {path}" verdict.hidden).toList)
              composed resultOut sources
            return 1
        let sourceRejected := !SourceAudit.compilationPassed compilation &&
            SourceAudit.sourceDiagnosticFailure compilation
        -- `none` when the source does not elaborate; otherwise the inspection's outcome, or the
        -- error that stopped the inspection of a source that elaborated.
        let inspection : Option (Except String
            (Except ProducerReport.Refusal SourceAudit.Inspected)) ←
          if !SourceAudit.compilationPassed compilation then pure none
          else try
            pure (some (.ok (← SourceAudit.inspectOutcome compilation inventory.leanPath
              inventory.leanSrcPath inventory.moduleSources inventory.ownership)))
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
                inspected.report.imported
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
            -- RG2006: the options the file's source set, decided by the proved
            -- `RegulaPolicy.Community.sourceFailures` as a claimed module's are. The file belongs to
            -- no target, so no target option licenses Mathlib's header linter; the file imports
            -- Mathlib when its environment contains a `Mathlib` module. The file audit loads the
            -- observer itself, with `--plugin`.
            if let some verdict := verdict then
              let mathlib := inspected.report.modules.any (·.getRoot == `Mathlib)
              if let some detail :=
                  verdict.sourceDetail path.toString ⟨[], [], true, true⟩ mathlib then
                let finding ← IO.ofExcept <| Regula.makeDiagnostic .communityConfiguration
                  ⟨path.toString, detail⟩ (.project path.toString) .freshFile
                  (claim.map Profile.toString) .violation
                findings := findings.push ⟨.communityConfiguration, finding⟩
                reasons := reasons.push (Regula.descriptor .communityConfiguration).applicability
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
                      compilation.observation
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

/-- A kind of output destination an invocation may name: a result document (`--json-out`) or an
acceptance link (`--acceptance-link`). -/
inductive Destination where
  /-- A result document, named by `--json-out`. -/
  | result
  /-- An acceptance link, named by `--acceptance-link`. -/
  | acceptanceLink
  deriving BEq, DecidableEq

/-- Each output destination a reading (`arguments`) names, with its kind, in order, whether or not
its arguments are admitted. -/
def destinations (read : List (Lint.Arg Setting)) : List (Destination × FilePath) :=
  read.filterMap fun
    | .value .jsonOut path => some (.result, FilePath.mk path)
    | .value .acceptanceLink path => some (.acceptanceLink, FilePath.mk path)
    | _ => none

/-- The first destination of `kind` in `named`. -/
def destinationOf (kind : Destination) (named : List (Destination × FilePath)) : Option FilePath :=
  ((named.find? (decide <| ·.1 = kind))).map (·.2)

/-- The option that `read` gives a value more than once, if any. -/
private def duplicated (read : List (Lint.Arg Setting)) : Option Setting :=
  let given := read.filterMap fun
    | .value setting _ => some setting
    | _ => none
  Setting.all.find? fun setting => given.count setting > 1

/-- The reason the usage text does not allow these options together, if any. `--help` is
admitted with any. The usage text does not list the internal `--driver-copy`, which is admitted
only in the fresh surface mode of the current project, without `--with-docs` and `--project`. -/
private def combinationRefusal (options : Options) : Option String :=
  if options.help then none
  else if options.file.isNone && options.claim.isSome then some "--claim requires --file"
  else if options.file.isNone && options.execution != .report then
    some "--execution requires --file (surface mode uses the manifest)"
  else if options.file.isSome && options.incremental then
    some "--incremental applies only to surface mode"
  else if options.withDocs && (options.file.isSome || options.incremental) then
    some "--with-docs requires fresh surface mode"
  else if options.acceptanceLink.isSome &&
      (options.file.isSome || options.incremental || options.withDocs) then
    some "--acceptance-link requires fresh surface mode without --with-docs"
  else if options.driverCopy.isSome &&
      (options.file.isSome || options.incremental || options.withDocs || options.project.isSome) then
    some "--driver-copy applies only to the fresh surface mode of the current project, without \
      --with-docs and --project"
  else if options.verso.isSome && options.acceptanceLink.isNone then
    some "--verso applies only to --acceptance-link"
  else if options.kernelTypes && options.resultOut.isNone then
    some "--kernel-types applies only to --json-out"
  else none

/-- The options of an audit invocation, from its one reading `read` (`arguments`): without an
option given a value twice, each argument applied, its result and acceptance-link destinations the
first of each kind in `destinations`, and in a combination the usage text allows; otherwise the
reason for refusing it. -/
def admit (read : List (Lint.Arg Setting)) : Except String Options :=
  match duplicated read with
  | some setting => .error s!"duplicate {setting.spelling} option"
  | none => match Options.applyAll read {} with
    | .error reason => .error reason
    | .ok options =>
      let named := destinations read
      let options := { options with
        resultOut := destinationOf .result named
        acceptanceLink := destinationOf .acceptanceLink named }
      match combinationRefusal options with
      | some reason => .error reason
      | none => .ok options

/-- Mark the result document at `path` incomplete, so an earlier completed result there cannot be
mistaken for the current attempt's. Its unresolved reason is `reason`, by default that the
configuration has not been validated yet. -/
def invalidateResult (path : FilePath) (reason : String := "configuration has not been validated") :
    IO Unit :=
  ResultProtocol.writeDocument path (Json.mkObj (ResultProtocol.identityFields ++ [
    ("scope", Json.null), ("mode", Json.null), ("status", .str "incomplete"),
    ("diagnostics", toJson (#[] : Array Json)),
    ("unresolved", toJson #[reason]),
    ResultProtocol.sourceTextsField] ++
    ResultProtocol.guidanceFields false ResultProtocol.allStages [] []))

/-- The project root a reading names: that of its one `--project`, or of the working directory.
-/
private def rootOf (read : List (Lint.Arg Setting)) : IO FilePath :=
  match read.filterMap (fun | .value .project dir => some dir | _ => none) with
  | [dir] => findRepoRoot dir
  | [] => repoRoot
  | _ => throw <| IO.userError "duplicate --project option"

/-- An invocation's plan, from its one reading of its arguments (`arguments`): its options or the
reason for refusing them (`admit`), the project root that reading names, and each destination it
names (`destinations`) resolved against that root. The marking, the audit's writes and the
`ruleExamples` marker all take their destinations from this one value. -/
structure Plan where
  /-- The options, or the reason for refusing the invocation. -/
  admitted : Except String Options
  /-- The project root of the reading's `--project`, or of the working directory. -/
  root : Except IO.Error FilePath
  /-- Each destination named, without repeats: its kind, as given, and resolved against `root`
  when relative. -/
  targets : List (Destination × FilePath × Except IO.Error FilePath)

/-- The plan of `args`, read once. -/
def Plan.of (args : List String) : BaseIO Plan := do
  let read := arguments args
  let root ← (rootOf read).toBaseIO
  return { admitted := admit read, root,
           targets := (destinations read).eraseDups.map fun (kind, path) =>
             (kind, path, if path.isAbsolute then .ok path else root.map (resolve · path)) }

/-- The resolved destination of `kind` the plan writes: the first that the reading names, as
`admit` takes it. -/
def Plan.target (plan : Plan) (kind : Destination) : Option (Except IO.Error FilePath) :=
  (plan.targets.find? (decide <| ·.1 = kind)).map (·.2.2)

/-- Mark each resolved destination of `plan` incomplete, each on its own, whether or not the
invocation is admitted, so an earlier completed result cannot be mistaken for this attempt's;
return a line for each that could not be marked. With `reason`, each records it as the reason that
the run stops there. -/
private def markIncomplete (plan : Plan) (reason : Option String := none) : IO (List String) := do
  let mut failed := []
  for (kind, path, target) in plan.targets do
    let result ← match target with
      | .ok target => (if kind == .acceptanceLink then AcceptanceLink.invalidate target reason
          else match reason with
            | some reason => invalidateResult target reason
            | none => invalidateResult target).toBaseIO
      | .error error => pure (.error error)
    if let .error error := result then failed := failed ++ [s!"{path}: {error}"]
  return failed

/-- The job that the arguments of one `axiomGate` invocation name, read once from their whole
shape (`Invocation.of`): one of the internal forms, each with what names the files that
it writes (`Invocation.outputs`), or an audit with its plan (`Plan.of`). `run` does the job, and
the refusal without a task manager marks the files of the same reading
(`Invocation.markIncomplete`), so the two take their destinations from one parser. -/
inductive Invocation where
  /-- `--validate-site REGISTRY ARTIFACT`: writes nothing. -/
  | validateSite (registry artifact : String)
  /-- `--registry-out OUTPUT`: writes the registry to `output`. -/
  | registryOut (output : String)
  /-- `--validate-registry INPUT`: writes nothing. -/
  | validateRegistry (input : String)
  /-- `--module-graph-worker INPUT OUT`. -/
  | moduleGraphWorker (input out : String)
  /-- `--declaration-report-worker INPUT OUT`, with the request that `INPUT` holds, decoded once
  (`ReportWorkerRequest`): besides `OUT`, its member `publish` names the file where the worker
  publishes its completed admission. -/
  | declarationReportWorker (input out : String)
      (request : Except String (Json × ReportWorkerRequest))
  /-- `--frontend-worker INPUT OUT`. -/
  | frontendWorker (input out : String)
  /-- `--compile-batch-worker INPUT OUT`. -/
  | compileBatchWorker (input out : String)
  /-- `--inspection-group-worker INPUT OUT`. -/
  | inspectionGroupWorker (input out : String)
  /-- `--diagnostic-worker MODULE SOURCE OUT`. -/
  | diagnosticWorker (moduleWire source out : String)
  /-- `--replacement-history-worker MODULE SOURCE OUT`. -/
  | replacementHistoryWorker (moduleWire source out : String)
  /-- Any other arguments: an audit, with the plan of its arguments. -/
  | audit (plan : Plan)
  /-- An internal form that names one file as an input and as a file that it writes, refused with
  `reason` (`aliasRefusal`): it writes nothing. -/
  | aliased (reason : String)

/-- The invocation that `args` name, read once, before the check of its files (`Invocation.of`). -/
private def Invocation.read (args : List String) : BaseIO Invocation :=
  match args with
  | ["--validate-site", registry, artifact] => pure (.validateSite registry artifact)
  | ["--registry-out", output] => pure (.registryOut output)
  | ["--validate-registry", input] => pure (.validateRegistry input)
  | ["--module-graph-worker", input, out] => pure (.moduleGraphWorker input out)
  | ["--declaration-report-worker", input, out] => do
    let decoded ← (do
      let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
      let request : ReportWorkerRequest ← IO.ofExcept (fromJson? json)
      return (json, request) : IO (Json × ReportWorkerRequest)).toBaseIO
    return .declarationReportWorker input out (decoded.mapError toString)
  | ["--frontend-worker", input, out] => pure (.frontendWorker input out)
  | ["--compile-batch-worker", input, out] => pure (.compileBatchWorker input out)
  | ["--inspection-group-worker", input, out] => pure (.inspectionGroupWorker input out)
  | ["--diagnostic-worker", moduleWire, source, out] =>
    pure (.diagnosticWorker moduleWire source out)
  | ["--replacement-history-worker", moduleWire, source, out] =>
    pure (.replacementHistoryWorker moduleWire source out)
  | _ => .audit <$> Plan.of args

/-- The files that an internal form writes: its output, and for the declaration-report worker the
file `publish` of its decoded request too. A form that writes none and an audit, whose destinations
its plan gives, give none. -/
def Invocation.outputs : Invocation → List String
  | .validateSite .. | .validateRegistry _ | .audit _ | .aliased _ => []
  | .registryOut output => [output]
  | .declarationReportWorker _ out request =>
    out :: match request with
      | .ok (_, request) => [request.publish]
      | .error _ => []
  | .moduleGraphWorker _ out | .frontendWorker _ out | .compileBatchWorker _ out
  | .inspectionGroupWorker _ out | .diagnosticWorker _ _ out | .replacementHistoryWorker _ _ out =>
    [out]

/-- The files that an internal form reads by the names its arguments give. An audit gives none
here: its run marks its destinations before it reads its source and its manifest, whose names the
plan resolves. -/
def Invocation.inputs : Invocation → List String
  | .validateSite registry artifact => [registry, artifact]
  | .validateRegistry input | .moduleGraphWorker input _ | .declarationReportWorker input _ _
  | .frontendWorker input _ | .compileBatchWorker input _ | .inspectionGroupWorker input _ =>
    [input]
  | .diagnosticWorker _ source _ | .replacementHistoryWorker _ source _ => [source]
  | .registryOut _ | .audit _ | .aliased _ => []

/-- The invocation that `args` name, read once (`Invocation.read`), or `aliased` when one of its
input files is also one of the files it writes (`aliasRefusal`). The guard marks the files of this
reading before the run reads an input (`Regula.TaskManager.guard`), so such an invocation is
refused before anything is written. No caller in this repository names one file in both
places. -/
def Invocation.of (args : List String) : BaseIO Invocation := do
  let invocation ← Invocation.read args
  match ← aliasRefusal (invocation.inputs.map FilePath.mk) (invocation.outputs.map FilePath.mk) with
  | some reason => return .aliased reason
  | none => return invocation

/-- Each file that `invocation` marks and writes, as the run resolves it: the files of an internal
form (`outputs`), or each destination of an audit's plan that resolves (`Plan.targets`). -/
def Invocation.destinations : Invocation → List FilePath
  | .audit plan => plan.targets.filterMap fun (_, _, target) => target.toOption
  | other => other.outputs.map FilePath.mk

/-- Mark each file that `invocation` writes incomplete, each on its own, and return a line for each
that could not be marked: an audit's destinations (`markIncomplete`), with `reason` when given,
and each file of an internal form (`outputs`, `invalidateOutput`), with `reason` or else the reason
that the job has not completed. -/
def Invocation.markIncomplete (invocation : Invocation) (reason : Option String) :
    IO (List String) :=
  match invocation with
  | .audit plan => Regula.Checker.AxiomGate.markIncomplete plan reason
  | other => other.outputs.filterMapM fun (out : String) => do
    match ← (invalidateOutput ⟨out⟩ (reason.getD "the job has not completed")).toBaseIO with
    | .ok () => pure none
    | .error error => pure (some s!"{out}: {error}")

/-- The refusal of an invocation, which the guard of the executable runs before each run and, in a
process without Lean's task manager, in the run's place (`Regula.TaskManager.guard`): it reads the
arguments once (`Invocation.of`), as `run` does, marks each file of that reading incomplete with
`reason`, whether or not the invocation is admitted (`Invocation.markIncomplete`), and returns the
exit code of an incomplete audit. An invocation that names one file as an input and as a file it
writes (`Invocation.aliased`) has no file to mark, so the input stays as it was. No job runs. -/
def refuseWithoutTaskManager (reason : String) (args : List String) : IO UInt32 := do
  for line in ← (← Invocation.of args).markIncomplete (some reason) do
    IO.eprintln s!"axiom gate: could not mark the destination {line} incomplete"
  return Lint.Outcome.incomplete.exitCode

/-- Refuse an invalid invocation: the usage text and the problem, and the invalid-configuration
exit code, since no audit ran and no result was recorded. -/
private def refuseInvocation (message : String) : IO UInt32 := do
  IO.eprintln usage
  IO.eprintln s!"FAIL: invalid invocation: {message}"
  return Lint.Outcome.configuration.exitCode

/-- The audit of an invocation whose arguments are not an internal form, with their plan
(`Plan.of`): it refuses an invalid invocation, audits the single file or the manifested project
surfaces under the plan's root, and writes the result JSON and the acceptance link at the plan's
resolved destinations. It returns the exit code of the result it recorded (`Lint.gateExitCode`):
0 accepted or classified, 1 violation, 2 invalid configuration, 3 incomplete; an invalid
invocation returns 2. `failed` lists the destinations of the plan that could not be marked
incomplete (`Invocation.markIncomplete`); an admitted invocation stops with an error when it lists
any. -/
private unsafe def audit (plan : Plan) (failed : List String) : IO UInt32 := do
  resultTarget.set ((plan.target .result).bind (·.toOption))
  let options ← match plan.admitted with
    | .error reason => return ← refuseInvocation reason
    | .ok options => pure options
  unless failed.isEmpty do
    throw <| IO.userError "a destination could not be marked incomplete"
  if options.help then IO.println usage; return 0
  if options.verbose then timing.set true
  kernelTypes.set options.kernelTypes
  -- The root and destinations the plan resolved and marked.
  let repo ← IO.ofExcept plan.root
  let resultOut ← (plan.target .result).mapM IO.ofExcept
  let manifestPath := (options.manifest.map (resolve repo)).getD (Manifest.defaultPath repo)
  auditedTarget.set (some (repo, manifestPath))
  let acceptanceLink ← (plan.target .acceptanceLink).mapM IO.ofExcept
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
  let originalCopyInputs ← if options.file.isNone && !options.incremental && options.driverCopy.isNone then
      try pure (some (← Lake.captureConfigurationInputs repo)) catch _ => pure none
    else pure none
  let copyInputs ← IO.mkRef originalCopyInputs
  let composed ← IO.mkRef (none : Option Json)
  let observeConfiguration := fun (root : FilePath)
      (configuration : Array (FilePath × Option String))
      (inputs : Option Regula.CopyConfiguration.Inputs) => do
    unless inputs == originalCopyInputs do
      throw <| IO.userError "loaded copy configuration selections changed before construction"
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
      afterFailure error do
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
  -- A configuration-read failure still records the request, with its policy selection and no
  -- configuration read.
  let (configuration, readFailure) ← try
      pure (← SourceBinding.configuration repo manifestPath, none)
    catch error => pure (#[], some error)
  let request := ResultProtocol.requestJson
      (if options.file.isSome then "file" else if options.withDocs then "projectWithDocs" else
                                                                         "project")
    repo.toString ((options.file.map (fun path => (resolve repo path).toString)).getD repo.toString)
    (options.claim.map Profile.toString)
    (if options.file.isSome then some options.execution.toString else none) manifestPath
    configuration
  let (code, linked) ← withRetainedSources resultOut composed capturedSources <|
    match readFailure with
    | some error => return (← reportFailure error, none)
    | none => withSourceEvidenceOr (1, none) #[] configuration repo.toString mode composed
               resultOut action
  let request := request.setObjVal! "copyConfiguration" (toJson (← copyInputs.get))
  if let some account ← effective.get then
    let origins ← IO.ofExcept <| Lake.configurationOrigins repo.toString
      (configuration.map fun (path, source) => (path.toString, source)) (← copyInputs.get)
      (FilePath.mk (← IO.ofExcept (account.getObjValAs? String "root")))
    effective.set (some (account.setObjVal! "configurationOrigins" origins))
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

/-- Run one `axiomGate` invocation and return its exit code. It reads its arguments once
(`Invocation.of`) and marks each file of that reading incomplete, whether or not the invocation is
admitted (`Invocation.markIncomplete`), so a run that stops before its write leaves no earlier
completed output there. The internal forms then do only their job; any other invocation is an
audit of its plan (`audit`), which refuses an invalid invocation whatever marking failed. An
audit returns the exit code of the result it recorded (`Lint.gateExitCode`), and `--help` and the
internal forms 0 when they succeed. -/
unsafe def run (args : List String) : IO UInt32 := do
  terminalObservation.set none
  auditedTarget.set none
  resultTarget.set none
  RunFeedback.reset
  expectedStages.set ResultProtocol.allStages
  let invocation ← Invocation.of args
  let failed ← invocation.markIncomplete none
  for line in failed do
    IO.eprintln s!"axiom gate: could not mark the destination {line} incomplete"
  match invocation with
  | .validateSite registryPath artifactPath =>
    let registry ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile registryPath)
    let artifact ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile artifactPath)
    IO.ofExcept <| Regula.Website.validateArtifact ResultProtocol.producer registry artifact
    return 0
  | .registryOut output =>
    writeJson output (Regula.RegistryCodec.registryJson ResultProtocol.producer)
    return 0
  | .validateRegistry input =>
    let value ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    IO.ofExcept <| Regula.RegistryCodec.validateRegistry ResultProtocol.producer value
    return 0
  | .moduleGraphWorker input out =>
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request : ModuleGraphRequest ← IO.ofExcept (fromJson? json)
    let guarded ← SourceBinding.withUnchanged request.sourceBindings #[] <|
      Environment.loadModuleGraph request.modules (request.searchRoots.map FilePath.mk)
    let graph ← IO.ofExcept <| guarded.mapError (·.detail)
    writeJson out (workerPacket json (toJson graph))
    return 0
  | .declarationReportWorker _ out decoded =>
    let (json, request) ← IO.ofExcept decoded
    let guarded ← SourceBinding.withUnchanged
        (α := Except ProducerReport.Refusal ProducerReport.Environment)
        request.sourceBindings #[] do
      let outcome ← Environment.loadReportOutcome request.modules
        (request.searchRoots.map FilePath.mk) (request.sourceRoots.map FilePath.mk)
        (request.sourceBindings.map fun source => (source.moduleName, FilePath.mk source.path))
        request.ownership (validateReport := false)
        (historyMemo := some (FilePath.mk request.historyMemo)) (priors := request.priors)
        (publish := some (FilePath.mk request.publish)) (inspectDependencies := true)
      if let .ok report := outcome then
        if let .error failure := SourceBinding.validateAgainst request.sourceBindings report then
          return .error (.admission failure)
      return outcome
    writeJson out (workerPacket json (toJson (ProducerReport.Outcome.ofExcept
      ((guarded.mapError ProducerReport.Refusal.admission).bind id))))
    return 0
  | .frontendWorker input out =>
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request : Frontend.WorkerRequest ← IO.ofExcept (fromJson? json)
    let transcript ← Frontend.build request.moduleName request.source
      (request.searchRoots.map FilePath.mk)
    writeJson out (workerPacket json (toJson transcript))
    return 0
  | .compileBatchWorker input out =>
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request ← IO.ofExcept (fromJson? json)
    writeJson out
        (workerPacket json (indexedWorkerPayload (← SourceAudit.compileBatchWorker request)))
    return 0
  | .inspectionGroupWorker input out =>
    let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse (← IO.FS.readFile input)
    let request ← IO.ofExcept (fromJson? json)
    writeJson out (workerPacket json (toJson (← SourceAudit.inspectGroupWorker request)))
    return 0
  | .diagnosticWorker moduleWire source out =>
    let moduleName ← IO.ofExcept <| Regula.RegistryCodec.parseName
        (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse moduleWire)
    let before ← IO.FS.readFile source
    let errors ← Diagnostics.errors moduleName source
    unless (← IO.FS.readFile source) == before do throw <| IO.userError "diagnostic source changed"
    writeJson out
        (workerPacket (sourceWorkerRequest "diagnostic" moduleName source before) (toJson errors))
    return 0
  | .replacementHistoryWorker moduleWire source out =>
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
  | .audit plan => audit plan failed
  | .aliased reason => refuseInvocation reason

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
