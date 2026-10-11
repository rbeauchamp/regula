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

/-- The workspace of `invocation` and `rule`: Fixed, then Violation over that Fixed build, then
Fixed again from a cleared build, in order; `first` numbers its result files. -/
private def chain (root : FilePath) (fresh : String → IO FilePath)
    (invocation : String) (flags : Array String) (mode rule : String) (first : Nat) :
    IO (Array Observation) := do
  let project ← fresh s!"{invocation}-{rule}"
  let mut observations := #[]
  for kind in #["Fixed", "Violation", "Fixed"] do
    let relative := s!"examples/rules/{rule}/{kind}.lean"
    let bytes ← IO.FS.readBinFile (root / relative)
    let some source := String.fromUTF8? bytes | throw <|
                                                 IO.userError "fixture must be valid UTF-8"
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
      ⟨rule, kind, invocation, mode, relative, source, result.exitCode.toNat, report⟩
  return observations

/-- The executable root of the standalone controls, before the axiom of phase `axiom`. -/
private def mainSource : String :=
  "/-! Standalone no-effect IO entrypoint. -/\n/-- Does nothing. -/\ndef main \
    : IO Unit := pure ()\n"

/-- The documented-source examples the chains audit, by their paths below the repository. -/
private def examples : Array String :=
  #["RG5001", "RG5002"].flatMap fun rule =>
    #["Fixed", "Violation"].map fun kind => s!"examples/rules/{rule}/{kind}.lean"

/-- The standalone executable control `phase` in a fresh workspace of its own. -/
private def standalone (root : FilePath) (fresh : String → IO FilePath) (phase : String) :
    IO Unit := do
  let project ← fresh s!"standalone-{phase}"
  IO.FS.writeBinFile (project / "Example.lean")
      (← IO.FS.readBinFile (root / "examples/rules/RG5002/Fixed.lean"))
  let config := project / "lakefile.lean"
  IO.FS.writeFile config
      ((← IO.FS.readFile config) ++ "\nlean_exe sampleTool where\n  root := `SelftestMain\n")
  let manifestPath := project / "foundation_manifest.json"
  let manifest ← readJson manifestPath
  let surfaces ← IO.ofExcept (manifest.getObjValAs? (Array Json) "surfaces")
  let some surface := surfaces[0]? | throw <| IO.userError "missing scratch manifest surface"
  writeJson manifestPath (manifest.setObjVal! "surfaces"
    (toJson #[surface.setObjVal! "executables" (toJson #["sampleTool"])]))
  let source := mainSource ++
    (if phase == "axiom" then
        "/-- An owned axiom, which RG1001 rejects. -/\naxiom ownedAssumption : True\n" else "")
  IO.FS.writeFile (project / "SelftestMain.lean") source
  let (result, report) ← observeProject root project (project / s!"standalone-{phase}.json") #[]
  IO.ofExcept (RegulaQualification.checked_decoded.run
    (RegulaQualification.Producer.standaloneRequirements report result.exitCode.toNat
        (phase == "axiom")))
  IO.println s!"standalone executable {phase}: PASS"

/-- Run all source-bound producer controls, optionally retaining emitted evidence. No workspace
reads another's, so the four documented-source workspaces and the two standalone ones run on
`jobs` workers (`mapWorkQueue`), beside the control of the guard (`rootImportsGuardControl`).
Before they start, the guard refuses when a module of the root package that their sources import
needs a build (`requireRootImportsBuilt`). `mapWorkQueue` joins every worker before it reports a
failure, and the error it reports is the first failing worker's. A worker that fails runs no
further item, so once `jobs` items have failed, the items still queued do not run. The
documented-source observations are then validated in the order of one workspace after another,
each against the theorem type of the first, as when the workspaces ran in turn. -/
def check (evidence : Option FilePath) (jobs : Nat := 4) : IO Unit := do
  let root ← rootDirectory
  let sources := (← examples.mapM fun (relative : String) => IO.FS.readFile (root / relative)).push
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
          mode) => #["RG5001", "RG5002"].map fun rule => (invocation, flags, mode, rule)
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
      let account ← IO.ofExcept (RegulaQualification.Producer.account report)
      let declarations ← IO.ofExcept (account.getObjValAs? (Array Json) "declarations")
      let some declaration := declarations[0]? | throw <|
                                                  IO.userError "missing theorem declaration"
      let observedType ← IO.ofExcept (declaration.getObjVal? "type")
      let expectedType := theoremType.getD observedType
      theoremType := some expectedType
      IO.ofExcept
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
    if let some parent := path.parent then IO.FS.createDirAll parent
    writeJson path (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("examples", toJson records)])
  IO.println "producer qualification: PASS (scoped operational evidence)"

end Regula.Qualification.Producer
