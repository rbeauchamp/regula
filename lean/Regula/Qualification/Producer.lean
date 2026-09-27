import Regula.Qualification.Project
import RegulaQualification.Producer

/-! Actual producer qualification: twelve documented-source controls (incremental and
build-lint, RG5001/RG5002, Fixed then Violation then restored Fixed) and two
standalone-executable controls. Each is kept for a genuinely external boundary: the
real `axiomGate` process, Lake build state and Lean elaboration of one source. Transport
admission of their reports is proved for every report (`ProducerReport.validate_sound`),
not sampled by mutation. Each invocation and rule shares one
workspace: the Violation audit runs over the prior Fixed build, so the incremental and
build-lint paths must detect the violation rather than accept stale artifacts. Because
that mutation shares its workspace, the Fixed control is re-established afterwards from a
cleared build (standard §8.8). The fresh-project
RG5001/RG5002 observations are the rule-example corpus records, which that campaign
validates with this same producer oracle. The source files remain authoritative; this
driver copies their bytes rather than maintaining another theorem fixture. -/
namespace Regula.Qualification.Producer
open Lean System

/-- Run all source-bound producer controls, optionally retaining emitted evidence. -/
def check (evidence : Option FilePath) : IO Unit := do
  let root ← rootDirectory
  let records ← withScratch root "producer-controls" fun scratch => do
    let fresh (label : String) : IO FilePath := do
      let project := scratch / label
      IO.FS.createDir project
      prepareProject root project "producer_adopter" "kernel-only"
        "The unchanged reflexivity proposition and exact doc presence."
      return project
    let mut records : Array Json := #[]
    let mut theoremType : Option Json := none
    for (invocation, flags, mode) in #[
        ("incremental", #["--incremental"], "incrementalProject"),
        ("build-lint", #["--build-lint"], "incrementalProject")] do
      for rule in #["RG5001", "RG5002"] do
        let project ← fresh s!"{invocation}-{rule}"
        for kind in #["Fixed", "Violation", "Fixed"] do
          let relative := s!"examples/rules/{rule}/{kind}.lean"
          let bytes ← IO.FS.readBinFile (root / relative)
          let some source := String.fromUTF8? bytes | throw <| IO.userError "fixture must be valid UTF-8"
          IO.FS.writeBinFile (project / "Example.lean") bytes
          -- Fixed runs from a cleared build; Violation keeps the prior Fixed build.
          if kind == "Fixed" then clearBuild project
          let output := project / s!"result-{records.size}.json"
          let (result, report) ← observeProject root project output flags
          let account ← IO.ofExcept (RegulaQualification.Producer.account report)
          let declarations ← IO.ofExcept (account.getObjValAs? (Array Json) "declarations")
          let some declaration := declarations[0]? | throw <| IO.userError "missing theorem declaration"
          let observedType ← IO.ofExcept (declaration.getObjVal? "type")
          let expectedType := theoremType.getD observedType
          theoremType := some expectedType
          IO.ofExcept (RegulaQualification.Producer.checked_validation.run report result.exitCode.toNat
            rule mode source (kind == "Fixed") expectedType)
          requireChecks [⟨"fixture bytes unchanged", (← IO.FS.readBinFile (project / "Example.lean")) == bytes⟩]
          records := records.push (Json.mkObj [
            ("rule", .str rule), ("case", .str kind), ("invocation", .str invocation),
            ("path", .str relative), ("source", .str source), ("result", report)])
          IO.println s!"{invocation} project {rule}/{kind}: PASS"
    let mainSource := "/-! Standalone no-effect IO entrypoint. -/\ndef main : IO Unit := pure ()\n"
    for phase in #["positive", "axiom"] do
      let project ← fresh s!"standalone-{phase}"
      IO.FS.writeBinFile (project / "Example.lean") (← IO.FS.readBinFile (root / "examples/rules/RG5002/Fixed.lean"))
      let config := project / "lakefile.lean"
      IO.FS.writeFile config ((← IO.FS.readFile config) ++ "\nlean_exe sampleTool where\n  root := `SelftestMain\n")
      let manifestPath := project / "foundation_manifest.json"
      let manifest ← readJson manifestPath
      let surfaces ← IO.ofExcept (manifest.getObjValAs? (Array Json) "surfaces")
      let some surface := surfaces[0]? | throw <| IO.userError "missing scratch manifest surface"
      writeJson manifestPath (manifest.setObjVal! "surfaces"
        (toJson #[surface.setObjVal! "executables" (toJson #["sampleTool"])]))
      let source := mainSource ++ (if phase == "axiom" then "axiom ownedAssumption : True\n" else "")
      IO.FS.writeFile (project / "SelftestMain.lean") source
      let (result, report) ← observeProject root project (project / s!"standalone-{phase}.json") #[]
      IO.ofExcept (RegulaQualification.checked_decoded.run
        (RegulaQualification.Producer.standaloneRequirements report result.exitCode.toNat (phase == "axiom")))
      IO.println s!"standalone executable {phase}: PASS"
    return records
  if let some path := evidence then
    if let some parent := path.parent then IO.FS.createDirAll parent
    writeJson path (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("examples", toJson records)])
  IO.println "producer qualification: PASS (scoped operational evidence)"

end Regula.Qualification.Producer
