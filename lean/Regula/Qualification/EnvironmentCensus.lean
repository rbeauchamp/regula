import Regula.Qualification.Support
import Regula.Checker.Acceptance
import Regula.Checker.Inspection

/-! # Environment census qualification

Native, source-bound environment composition qualification. Every environment's packet is
written before the census's own admission checks: its admitted report and transcripts, with a
refusal when frontend attribution failed, or only the refusal detail for an inspection that
`Inspection.inspect` refused (report admission, owned-package output outside every owned module,
source binding, admission reuse or transcript binding) or failed. Observed
process/filesystem/compiler behavior is not a universal proof; the separate shared-name theorem
establishes the pure collision class. -/
namespace Regula.Qualification.EnvironmentCensus
open Lean System Regula.Checker RegulaPolicy
open scoped Regula.Report

private def atomicWrite (path : FilePath) (value : Json) : IO Unit := do
  let temporary := path.addExtension "pending"
  IO.FS.writeFile temporary (value.compress ++ "\n")
  IO.FS.rename temporary path

private def save (attempt : String) (path : FilePath) (packets records : Array Json)
    (status : String) : IO Unit :=
  atomicWrite path <| Json.mkObj [
    ("attemptId", toJson attempt), ("schemaVersion", toJson (1 : Nat)), ("status", toJson status),
    ("packets", toJson packets), ("controls", toJson records)]

/-- Invalidate the destination before timeout discovery or process launch. -/
def beginAttempt (path : FilePath) (attempt : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  save attempt path #[] #[] "incomplete"

/-- Exercise actual native acquisition and the public freeze/finalization adapters.
Every report comes from the project audit's own acquisition (`Inspection.inspect`): one
`--declaration-report-worker` process per environment, so no environment's correspondence
checks run under a resource limit an earlier environment's process fixed (`Regula.Probe`).
The command owns one existing outer deadline, including its incremental build observation. -/
private unsafe def checkCore (attempt : String) (path : FilePath) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  save attempt path #[] #[] "incomplete"
  let root ← rootDirectory
  -- The same search-path initialization as the audit's coordinator (`AxiomGate.entry`); the
  -- report workers inherit it.
  initializeLeanSearchPath
  let configuration ← SourceBinding.configuration root (Manifest.defaultPath root)
  let inventory ← Lake.surfaceInventory root
  let sources ← SourceBinding.capture inventory.moduleSources
  let manifest ← Manifest.loadFor (Manifest.defaultPath root) inventory
  let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  let libraries ← Inspection.manifestedLibraries manifest inventory
  let environments ← Inspection.surfaceEnvironments manifest inventory assignments libraries
  let expected := environments.map (·.info.modules)
  let dependencies ← Snapshot.dependencies inventory
  -- The report workers run the `axiomGate` binary beside this one (`workerBinary`); build it
  -- from the same sources first, so the census never runs a stale worker.
  let worker ← Lake.buildTargets root #[.surface (.executable "axiomGate")]
  let mut records :=
    #[Json.mkObj [("case", toJson "worker-build"), ("observation", toJson worker)]]
  save attempt path #[] records "incomplete"
  requireChecks [⟨"report worker builds", worker.succeeded⟩]
  let targets := Lake.claimedTargets manifest
  let (build, failure) ← Lake.buildCheckedObservation root targets
      "incrementally for environment qualification"
  records := records.push <| Json.mkObj [("case", toJson "build"), ("observation", toJson build)]
  let mut packets : Array Json := #[]
  save attempt path packets records "incomplete"
  requireChecks [⟨"positive targets build warning-free", failure.isNone⟩]
  SourceBinding.unchanged sources
  SourceBinding.configurationUnchanged configuration
  let (frozenArtifacts, inspections) ←
    Inspection.inspect inventory sources assignments environments
  -- Write every environment's packet before the census's own admission checks (scope admission,
  -- freeze, finish, mutations): the admitted report, plus its refusal when frontend attribution
  -- failed, or only the refusal detail for an inspection `Inspection.inspect` refused or failed.
  let mut reports : Array Acceptance.RequestedInspection := #[]
  let mut refusals : Array String := #[]
  for (environment, outcome) in inspections do
    let packetPath := path.addExtension s!"packet-{packets.size}.json"
    let refused (detail : String) : Json × Except String Acceptance.RequestedInspection :=
      (Json.mkObj [("expectedModules", toJson environment.info.modules),
        ("refusal", toJson detail)], .error detail)
    let (packet, inspection) : Json × Except String Acceptance.RequestedInspection :=
      match outcome with
      | .ok (.ok inspected) =>
          let requested : Acceptance.RequestedInspection :=
            ⟨environment.info.modules, inspected.admitted, inspected.transcripts,
              environment.dependencies, environment.dependencySources⟩
          if inspected.frontendFailures.isEmpty then (toJson requested, .ok requested)
          else
            let detail := "; ".intercalate inspected.frontendFailures.toList
            ((toJson requested).setObjVal! "refusal" (toJson detail), .error detail)
      | .ok (.error failure) => refused failure.detail
      | .error error => refused error.toString
    atomicWrite packetPath packet
    match inspection with
    | .ok requested => reports := reports.push requested
    | .error detail => refusals := refusals.push s!"{environment.label}: {detail}"
    packets := packets.push (toJson packetPath.toString)
    save attempt path packets records "incomplete"
  unless refusals.isEmpty do
    throw <| IO.userError s!"environment inspection refused: {"; ".intercalate refusals.toList}"
  for requested in reports do
    let _ ← IO.ofExcept <| Policy.admitScope requested.report.compilerCapability
      requested.report.declarations requested.transcripts
  SourceBinding.unchanged sources
  SourceBinding.configurationUnchanged configuration
  if let some name ← Inspection.changedArtifact? frozenArtifacts then
    throw <| IO.userError
      s!"producer-artifact: the .olean files of {name} changed during the qualification"
  Snapshot.inputsUnchanged inventory dependencies
  -- Both environments own a `main`: the verification library's driver and the application
  -- executable's root, which is requested alone (`census_executable_alone`).
  let some verification := assignments.find? (·.target == "RegulaVerification")
    | throw <| IO.userError "verification surface absent"
  let some leftIndex := expected.toList.findIdx? (· == verification.library.map (·.name))
    | throw <| IO.userError "verification environment absent"
  let some application := inventory.executables.find? (·.executable == "auditApp")
    | throw <| IO.userError "application executable absent"
  let some rightIndex := expected.toList.findIdx? (· == #[application.root])
    | throw <| IO.userError "application environment absent"
  let some left := reports[leftIndex]? | throw <| IO.userError "verification packet absent"
  let some right := reports[rightIndex]? | throw <| IO.userError "application packet absent"
  let collisions := left.report.declarations.flatMap fun a =>
    (right.report.declarations.filter (·.name == a.name)).map fun b =>
      Json.mkObj
          [("name", toJson a.name), ("leftOwner", toJson a.module), ("rightOwner", toJson b.module)]
  let joined := Policy.admitScope left.report.compilerCapability
    (left.report.declarations ++ right.report.declarations)
    (left.transcripts ++ right.transcripts)
  records := records.push <| Json.mkObj [("case", toJson "concatenated-inventory"),
    ("collisions", toJson collisions), ("refusal", toJson (joined.toOption.isNone))]
  save attempt path packets records "incomplete"
  requireChecks [⟨"real cross-environment name collision retained", !collisions.isEmpty⟩,
    ⟨"concatenated unchanged inventories refused", joined.toOption.isNone⟩]
  let histories ← IO.ofExcept <| Acceptance.historyObservations reports
  let snapshotSources ← Acceptance.sourceSnapshots sources histories
  let snapshot ← IO.ofExcept <| Snapshot.make root configuration snapshotSources dependencies
  let claim ← IO.ofExcept <| admitClaim {
    scope := .project, mode := .incrementalProject, snapshot := snapshot.val, surfaces :=
        assignments }
  let freeze := fun input => Acceptance.freeze claim expected
    (Acceptance.configuredTargets manifest) (Acceptance.discoveredTargets inventory)
    sources inventory.leanLibDir input
  let frozen ← freeze reports
  let buildObservation := Acceptance.buildObservation build
  let _ ← Acceptance.finish frozen buildObservation
  records := records.push <| Json.mkObj
      [("case", toJson "complete-positive"), ("passed", toJson true)]
  save attempt path packets records "incomplete"
  -- A mutated report must pass the same `admit` that decoded reports pass, so a malformed
  -- report is refused before `freeze` exactly as the transport decoder refuses it.
  let omitted : Unit → IO (Array Acceptance.RequestedInspection) := fun _ => do
    let admitted ← IO.ofExcept <| ProducerReport.admit { left.report with sourceBindings := #[] }
    pure (reports.set! leftIndex { left with admitted })
  for (name, mutated, reason) in #[
      ("omitted-environment", fun _ => pure (reports.extract 0 (reports.size - 1)),
                                        "missing, duplicate or unrequested environment inspection"),
      ("duplicate-environment", fun _ => pure (reports.push left),
                                          "missing, duplicate or unrequested environment \
                                            inspection"),
      ("same-count-duplicate-environment", fun _ => pure (reports.set! rightIndex left),
                                                     "producer census differs from independently \
                                                       requested environment"),
      ("rebound-environment", fun _ => pure (reports.set! leftIndex right),
                                        "producer census differs from independently requested \
                                          environment"),
      ("source-binding-omission", omitted,
          "producer-source: source coverage or coordinates mismatch")] do
    let result ← (do freeze (← mutated ())).toBaseIO
    let refusal := match result with | .ok _ => "" | .error error => error.toString
    records := records.push <| Json.mkObj [("case", toJson name), ("refusal", toJson refusal)]
    save attempt path packets records "incomplete"
    requireChecks [⟨name, refusal.contains reason⟩]
  let inputs ← IO.ofExcept <| Acceptance.observations frozen buildObservation
  -- Mutate only raw supplied observations; retain the independently frozen plan/roles.
  let mut replayChanged := false
  let replayInputs := inputs.map fun (slot, observation) =>
    match observation.evidence with
    | .admission value =>
        (slot, { observation with evidence := .admission { value with admitted := #[] } })
    | _ => (slot, observation)
  for (_, observation) in inputs do
    if let .admission value := observation.evidence then
      if !value.admitted.isEmpty then replayChanged := true
  requireChecks [⟨"replay mutation has nonempty observed coverage", replayChanged⟩]
  let replayRefused := match finalize frozen.plan frozen.roles replayInputs with
    | .error (.acceptance .policyViolation) => true
    | _ => false
  records := records.push <| Json.mkObj
      [("case", toJson "replay-omission"), ("refused", toJson replayRefused)]
  save attempt path packets records "incomplete"
  requireChecks [⟨"replay-omission", replayRefused⟩]
  let some foreignRoot := right.report.execution.find? (·.name == `main)
    | throw <| IO.userError "application main execution observation absent"
  let some foreignDeclaration := right.report.declarations.find? (·.name == `main)
    | throw <| IO.userError "application main declaration absent"
  let substitutionInputs := inputs.map fun (slot, observation) =>
    match observation.evidence with
    | .declaration value =>
        if value.name == `main && value.module != foreignDeclaration.module then
          (slot, { observation with evidence := .declaration foreignDeclaration })
        else (slot, observation)
    | _ => (slot, observation)
  let rootInputs := inputs.map fun (slot, observation) =>
    match observation.evidence with
    | .execution value =>
        if value.name == `main && value.module != foreignRoot.module then
          (slot, { observation with evidence := .execution foreignRoot })
        else (slot, observation)
    | _ => (slot, observation)
  let unresolvedInputs := inputs.map fun (slot, observation) =>
    match observation.evidence with
    | .execution value =>
        (slot,
            { observation with evidence := .execution
                                 { value with unresolved :=
                                                #["qualification unresolved execution"] } })
    | _ => (slot, observation)
  -- No transcript substitution control runs: an accepted run plans no transcript job
  -- (`RegulaPolicy.accepted_no_transcript_subjects`), so the accepted positive above has no
  -- transcript observation to substitute. The record says so rather than omitting the case.
  records := records.push <| Json.mkObj [("case", toJson "cross-environment-role-transcript"),
    ("run", toJson false), ("reason", toJson
      "an accepted run plans no transcript job (RegulaPolicy.accepted_no_transcript_subjects)")]
  for (name, mutated) in #[
      ("cross-environment-declaration", substitutionInputs),
      ("cross-environment-root", rootInputs),
      ("incompatible-execution", unresolvedInputs)] do
    let result := finalize frozen.plan frozen.roles mutated
    let refusal := match result with | .ok _ => "" | .error failure => reprStr failure
    records := records.push <| Json.mkObj [("case", toJson name), ("refusal", toJson refusal)]
    save attempt path packets records "incomplete"
    requireChecks [⟨name, match result with
      | .error (.acceptance .policyViolation) => true
      | _ => false⟩]
  let changedSnapshot := { claim.val.snapshot with
    configuration := { claim.val.snapshot.configuration with
      source := claim.val.snapshot.configuration.source ++ "\n" } }
  let wrongSnapshot := inputs.map fun (slot, observation) =>
    (slot, { observation with snapshot := changedSnapshot })
  let checkedClaim ← IO.ofExcept <| admitClaim { claim.val with
    surfaces := claim.val.surfaces.map (fun surface => { surface with execution := .checked }) }
  let wrongRequest ← inputs.mapM fun (slot, observation) => do
    let key ← IO.ofExcept <| admitJobKey checkedClaim observation.key.stage observation.key.subject
    pure (slot, { observation with key })
  for (name, mutated) in #[
      ("wrong-snapshot", wrongSnapshot), ("incompatible-execution-request", wrongRequest)] do
    let result := finalize frozen.plan frozen.roles mutated
    let refusal := match result with | .ok _ => "" | .error failure => reprStr failure
    records := records.push <| Json.mkObj [("case", toJson name), ("refusal", toJson refusal)]
    save attempt path packets records "incomplete"
    requireChecks [⟨name, match result with
      | .error (.collection .invalidBinding) => true
      | _ => false⟩]
  let restored ← freeze reports
  let _ ← Acceptance.finish restored buildObservation
  SourceBinding.unchanged sources
  SourceBinding.configurationUnchanged configuration
  Snapshot.inputsUnchanged inventory dependencies
  records := records.push <| Json.mkObj
      [("case", toJson "restored-complete-positive"), ("passed", toJson true)]
  save attempt path packets records "complete"
  IO.println "environment census qualification: PASS (scoped native observations)"

/-- An ordinary failure keeps the packets already written (every environment's, once
`Inspection.inspect` has returned; see `checkCore`) and reports failure. Termination before
this handler runs leaves the initialized incomplete receipt; atomic rename is trusted IO. -/
unsafe def check (path : FilePath) (attempt : Option String := none) : IO Unit := do
  let attempt ← attempt.map pure |>.getD freshAttempt
  beginAttempt path attempt
  try checkCore attempt path
  catch error =>
    let evidence ← Regula.Qualification.readJson path
    atomicWrite path ((evidence.setObjVal! "status" (toJson "failed")).setObjVal!
      "failure" (toJson error.toString))
    throw error

end Regula.Qualification.EnvironmentCensus
