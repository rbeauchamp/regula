import Regula.Qualification.Project
import RegulaQualification.Producer

/-! # Producer qualification controls

Actual producer qualification: twelve documented-source controls (incremental and
build-lint, RG5001/RG5002, Fixed then Violation then restored Fixed) and two
standalone-executable controls. Each is kept for a genuinely external boundary: the
real `axiomGate` process, Lake build state and Lean elaboration of one source. Transport
admission of their reports is proved for every report (`ProducerReport.validate_sound`),
not sampled by mutation. Each invocation and rule shares one
workspace: the Violation audit runs over the prior Fixed build, so the incremental and
build-lint paths must detect the violation rather than accept stale artifacts. Because
that mutation shares its workspace, the Fixed control is re-established afterwards from a
cleared build (standard §7.8). The fresh-project
RG5001/RG5002 observations are the rule-example corpus records, which that campaign
validates with this same producer oracle. The source files remain authoritative; this
driver copies their bytes rather than maintaining another theorem fixture. -/
namespace Regula.Qualification.Producer
open Lean System

/-- One documented-source control's observation, which `check` validates after every workspace
has finished. -/
private structure Observation where
  /-- The rule whose example the control audited. -/
  rule : String
  /-- `Fixed` or `Violation`. -/
  kind : String
  /-- `incremental` or `build-lint`. -/
  invocation : String
  /-- The result mode the oracle requires. -/
  mode : String
  /-- The example's path below the repository. -/
  relative : String
  /-- The example's source text. -/
  source : String
  /-- The exit code of `axiomGate`. -/
  exitCode : Nat
  /-- The result document the reader rebuilt. -/
  report : Json
  /-- The path of the result file. -/
  output : FilePath
  /-- What `axiomGate` printed. -/
  transcript : String

/-- The rules whose documented examples the chains audit, one chain for each invocation. -/
private def rules : Array String := #["RG5001", "RG5002"]

/-- The examples a chain audits, in order: Fixed, then Violation over that Fixed build, then Fixed
again from a cleared build. -/
private def chainKinds : Array String := #["Fixed", "Violation", "Fixed"]

/-- The path below the repository of the example `kind` of `rule`. -/
private def examplePath (rule kind : String) : String := s!"examples/rules/{rule}/{kind}.lean"

/-- The examples the chains audit (`rules`, `chainKinds`), by their paths below the
repository. -/
private def examples : Array String :=
  rules.flatMap fun rule => chainKinds.map (examplePath rule)

/-- The workspace of `invocation` and `rule`: the examples of `chainKinds`, in order; `first`
numbers its result files. -/
private def chain (root : FilePath) (fresh : String → IO FilePath)
    (invocation : String) (flags : Array String) (mode rule : String) (first : Nat) :
    IO (Array Observation) := do
  let project ← fresh s!"{invocation}-{rule}"
  let mut observations := #[]
  for kind in chainKinds do
    let relative := examplePath rule kind
    let bytes ← Regula.Filesystem.readBytes (root / relative)
    let some source := String.fromUTF8? bytes | throw <|
                                                 IO.userError "fixture must be valid UTF-8"
    if observations.isEmpty then
      Regula.Filesystem.copyFile (root / relative) (project / "Example.lean")
    else
      -- Later phases deliberately mutate the file of the constructed private workspace.
      IO.FS.writeBinFile (project / "Example.lean") bytes
    -- Fixed runs from a cleared build; Violation keeps the prior Fixed build.
    if kind == "Fixed" then clearBuild project
    let output := project / s!"result-{first + observations.size}.json"
    -- The oracle compares the theorem's kernel type expression across the controls; a
    -- result carries it only on request.
    let (result, report) ← observeProject root project output (flags.push "--kernel-types")
    requireChecks
        [⟨"fixture bytes unchanged", (← IO.FS.readBinFile (project / "Example.lean")) == bytes⟩]
    observations := observations.push
      ⟨rule, kind, invocation, mode, relative, source, result.exitCode.toNat, report, output,
        result.stdout ++ result.stderr⟩
  return observations

/-- `decoded`, read from the result at `output` of an audit that printed `transcript`, or its
refusal: the result's path, the reason (`readMember`) and the last lines of the transcript, which
say why an audit that stopped early wrote no account. -/
private def fromResult {α : Type} (output : FilePath) (transcript : String)
    (decoded : Except String α) : IO α :=
  readMember output (decoded.mapError fun reason =>
    s!"{reason}\nthe audit's last lines:\n" ++
      "\n".intercalate (Regula.Checker.takeLast 40 (transcript.splitOn "\n").toArray).toList)

/-- The executable root of the standalone controls, before the axiom of phase `axiom`. -/
private def mainSource : String :=
  "/-! Standalone no-effect IO entrypoint. -/\n/-- Does nothing. -/\ndef main \
    : IO Unit := pure ()\n"

/-- The example that the library of a standalone control holds beside its executable root. -/
private def standaloneExample : String := examplePath "RG5002" "Fixed"

/-- The standalone executable control `phase` in a fresh workspace of its own. -/
private def standalone (root : FilePath) (fresh : String → IO FilePath) (phase : String) :
    IO Unit := do
  let project ← fresh s!"standalone-{phase}"
  Regula.Filesystem.copyFile (root / standaloneExample) (project / "Example.lean")
  let config := project / "lakefile.lean"
  -- The executable lists Regula's elaboration observer in `needs` (`observedTargetLean`), as
  -- `prepareProject`'s library does: the package loads it as a plugin, and an audit refuses a
  -- claimed module that it did not observe (RG2003, naming the missing `needs` as RG2006).
  IO.FS.writeFile config ((← IO.FS.readFile config) ++
    "\n" ++ Regula.Checker.observedTargetLean .executable "sampleTool" "  root := `SelftestMain\n")
  let manifestPath := project / "foundation_manifest.json"
  let manifest ← readJson manifestPath
  let surfaces ← readMember manifestPath (RegulaQualification.Member.array manifest "surfaces")
  let some surface := surfaces[0]? | throw <| IO.userError "missing scratch manifest surface"
  writeJson manifestPath (manifest.setObjVal! "surfaces"
    (toJson #[surface.setObjVal! "executables" (toJson #["sampleTool"])]))
  let source := mainSource ++
    (if phase == "axiom" then
        "/-- An owned axiom, which RG1001 rejects. -/\naxiom ownedAssumption : True\n" else "")
  IO.FS.writeFile (project / "SelftestMain.lean") source
  let output := project / s!"standalone-{phase}.json"
  let (result, report) ← observeProject root project output #[]
  fromResult output (result.stdout ++ result.stderr) (RegulaQualification.checked_decoded.run
    (RegulaQualification.Producer.standaloneRequirements report result.exitCode.toNat
        (phase == "axiom")))
  IO.println s!"standalone executable {phase}: PASS"

/-- Mark the export at `evidence` incomplete for the attempt `attempt`, before the campaign runs, so
an earlier completed export there cannot be mistaken for this attempt's: the record has no member
`examples`. With `reason`, it records why the attempt stops there. It stops with nothing written at
a file that the run may not replace (`writeEvidence`). -/
def beginAttempt (evidence : FilePath) (attempt : String) (reason : Option String := none) :
    IO Unit := do
  writeEvidence evidence (Json.mkObj ([("schemaVersion", toJson (1 : Nat)),
    ("status", .str "incomplete"), ("attempt", .str attempt)] ++
      (reason.map fun reason => [("reason", .str reason)]).getD []))

/-- Run all source-bound producer controls, optionally retaining emitted evidence. No workspace
reads another's, so the four documented-source workspaces and the two standalone ones run on
`jobs` workers (`mapWorkQueue`), beside the control of the guard (`rootImportsGuardControl`).
Before they start, the guard refuses when a module of the root package that their sources import
needs a build (`requireRootImportsBuilt`). `mapWorkQueue` joins every worker before it reports a
failure, and the error it reports is the first failing worker's. A worker that fails runs no
further item, so once `jobs` items have failed, the items still queued do not run. The
documented-source observations are then validated in the order of one workspace after another,
each against the theorem type of the first, as when the workspaces ran in turn. -/
private def checkControls (evidence : Option FilePath) (jobs : Nat) : IO Unit := do
  let root ← rootDirectory
  let sources := (← (examples.push standaloneExample).mapM fun (relative : String) =>
    Regula.Filesystem.readFile (root / relative)).push
    mainSource
  requireRootImportsBuilt root sources
  let records ← withScratch root "producer-controls" fun scratch => do
    let fresh (label : String) : IO FilePath := do
      let project := scratch / label
      IO.FS.createDir project
      prepareProject root project "producer_adopter" "kernel-only"
        "The unchanged reflexivity proposition and exact doc presence."
      return project
    let chains := #[("incremental", #["--incremental"], "incrementalProject"),
        ("build-lint", #["--build-lint"], "incrementalProject")].flatMap fun (invocation, flags,
          mode) => rules.map fun rule => (invocation, flags, mode, rule)
    let workspaces : Array (IO (Array Observation)) :=
      chains.mapIdx (fun index (invocation, flags, mode, rule) =>
        chain root fresh invocation flags mode rule (3 * index)) ++
      #["positive", "axiom"].map (fun phase => do standalone root fresh phase; pure #[]) |>.push
        (do rootImportsGuardControl root scratch sources; pure #[])
    let observed ← Regula.Checker.mapWorkQueue jobs workspaces id
    let mut records : Array Json := #[]
    let mut theoremType : Option Json := none
    for observation in observed.flatten do
      let report := observation.report
      let fromReport {α : Type} := fromResult (α := α) observation.output observation.transcript
      let account ← fromReport (RegulaQualification.Producer.account report)
      let declarations ← fromReport (RegulaQualification.Member.array account "declarations")
      let declaration ← fromReport do
        let some declaration := declarations[0]? | throw "missing theorem declaration"
        pure declaration
      let observedType ← fromReport (RegulaQualification.Member.value declaration "type")
      let expectedType := theoremType.getD observedType
      theoremType := some expectedType
      fromReport
          (RegulaQualification.Producer.checked_validation.run report observation.exitCode
        observation.rule observation.mode observation.source (observation.kind == "Fixed")
        expectedType)
      records := records.push (Json.mkObj [
        ("rule", .str observation.rule), ("case", .str observation.kind),
        ("invocation", .str observation.invocation), ("path", .str observation.relative),
        ("source", .str observation.source), ("result", report)])
      IO.println s!"{observation.invocation} project {observation.rule}/{observation.kind}: PASS"
    return records
  if let some path := evidence then
    writeEvidence path
      (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("examples", toJson records)])
  IO.println "producer qualification: PASS (scoped operational evidence)"

/-- Run all source-bound producer controls (`checkControls`), on `jobs` workers. With `evidence`,
the export there is first marked incomplete for the attempt `attempt`, or a fresh one
(`beginAttempt`), as the other campaigns begin theirs; a run that fails marks it again with the
error's text and then fails with that error. So no earlier completed export remains at `evidence`
after a run that does not complete, unless the writer refuses `evidence` (`writeEvidence`): a
symbolic link there, for one, keeps its target, which a reader that follows it still reads. -/
def check (evidence : Option FilePath) (attempt : Option String := none) (jobs : Nat := 4) :
    IO Unit := do
  let some path := evidence | checkControls none jobs
  let attempt ← attempt.getDM freshAttempt
  beginAttempt path attempt
  try checkControls (some path) jobs
  catch error =>
    discard <| (beginAttempt path attempt (some error.toString)).toBaseIO
    throw error

end Regula.Qualification.Producer
