import Regula.Qualification.Support
import Regula.Checker.Acceptance

/-! # Environment census qualification

Native, source-bound environment composition qualification. Complete producer packets
are retained before admission controls. Observed process/filesystem/compiler behavior is
not a universal proof; the separate shared-name theorem establishes the pure collision class. -/
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
The command owns one existing outer deadline, including its incremental build observation. -/
private unsafe def checkCore (attempt : String) (path : FilePath) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  save attempt path #[] #[] "incomplete"
  let root ← rootDirectory
  let configuration ← SourceBinding.configuration root (Manifest.defaultPath root)
  let inventory ← Lake.surfaceInventory root
  let sources ← SourceBinding.capture inventory.moduleSources
  let manifest ← Manifest.load (Manifest.defaultPath root)
  let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  let expected := assignments.flatMap (·.environmentNames)
  let dependencies ← Snapshot.dependencies inventory
  let targets := manifest.surfaces.flatMap fun s => #[s.library] ++ s.executables
  let (build, failure) ← Lake.buildCheckedObservation root targets
      "incrementally for environment qualification"
  let mut records := #[Json.mkObj [("case", toJson "build"), ("observation", toJson build)]]
  let mut packets : Array Json := #[]
  save attempt path packets records "incomplete"
  requireChecks [⟨"positive targets build warning-free", failure.isNone⟩]
  SourceBinding.unchanged sources
  SourceBinding.configurationUnchanged configuration
  let mut reports : Array Acceptance.RequestedInspection := #[]
  for modules in expected do
    let report ← Environment.loadReport modules inventory.leanPath inventory.leanSrcPath
      inventory.moduleSources (some inventory.leanLibDir)
    -- Retain even a report whose subsequent frontend acquisition or validation fails.
    let packetPath := path.addExtension s!"packet-{reports.size}.json"
    atomicWrite packetPath (Json.mkObj [("expectedModules", toJson modules),
      ("report", toJson report),
      ("transcripts", toJson (#[] : Array RegulaPolicy.Frontend.Transcript)),
      ("frontendComplete", toJson false)])
    packets := packets.push (toJson packetPath.toString)
    save attempt path packets records "incomplete"
    let candidates := report.declarations.foldl (fun names d =>
      if Policy.needsFrontendTranscript #[d] && !names.contains d.module then names.push d.module
      else names) (#[] : Array Name)
    let mut transcripts : Array RegulaPolicy.Frontend.Transcript := #[]
    for name in candidates do
      let some source := sources.find? (·.moduleName == name)
        | throw <| IO.userError s!"missing captured frontend source: {name}"
      transcripts := transcripts.push
          (← Regula.Checker.Frontend.buildIsolated name ⟨source.path⟩ inventory.leanPath)
    let inspected : Acceptance.RequestedInspection :=
      ⟨modules, ← IO.ofExcept (ProducerReport.admit report), transcripts⟩
    reports := reports.push inspected
    atomicWrite packetPath (toJson inspected)
    save attempt path packets records "incomplete"
    IO.ofExcept ((SourceBinding.validateAgainst sources report).mapError (·.detail))
    IO.ofExcept ((SourceBinding.transcriptsMatch sources transcripts).mapError (·.detail))
    let _ ← IO.ofExcept <| Policy.admitScope report.declarations transcripts
  SourceBinding.unchanged sources
  SourceBinding.configurationUnchanged configuration
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
  let joined := Policy.admitScope (left.report.declarations ++ right.report.declarations)
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
  let transcripts := reports.flatMap (·.transcripts)
  let some foreignTranscript := transcripts[0]?
    | throw <| IO.userError "no real role transcript available for substitution"
  let roleInputs := inputs.map fun (slot, observation) =>
    match observation.evidence with
    | .transcript value =>
        if value.module != foreignTranscript.module then
          (slot, { observation with evidence := .transcript foreignTranscript })
        else (slot, observation)
    | _ => (slot, observation)
  for (name, mutated) in #[
      ("cross-environment-declaration", substitutionInputs),
      ("cross-environment-root", rootInputs),
      ("incompatible-execution", unresolvedInputs),
      ("cross-environment-role-transcript", roleInputs)] do
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

/-- Ordinary failures retain all captured packets and report failure. Termination before
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
