import Regula.Qualification.SourceEvidence
import Regula.Checker.Common

/-! # Documentation source-binding qualification

Frozen source/configuration controls through both documentation entrypoints and
through build/file boundaries. Mutating fixtures are never part of a positive library. -/
namespace Regula.Qualification.DocumentationSource
open Lean System RegulaQualification RegulaQualification.Evidence SourceEvidence

private def source :=
    "/-! The fixed dependency proposition. -/\ntheorem dependency : True := True.intro\n"
private def action (operation : String) : String :=
  if operation == "append" then "IO.FS.writeFile path ((← IO.FS.readFile path) ++ \"\\n\")"
  else if operation == "remove" then "IO.FS.removeFile path"
  else "IO.FS.removeFile path\n  IO.FS.createDirAll path"

/-- The adopter environment with timing output on: the transcript checks require the
`fence compilation` phase line (`documentationChecks`), which only timing output prints. -/
private def timedEnv : Array (String × Option String) :=
  cleanEnv.push (Regula.Checker.timingVariable, some "1")

/-- Full campaign or the upstream source-read subset; neither is advertised as ordinary
acceptance. Every refusal is checked for its intended reason and followed by restoration. -/
def check (sourceReadOnly : Bool) : IO Unit := do
  let root ← rootDirectory
  withScratch root "documentation-source" fun project => do
    prepareCoreProject root project "documentation_adopter" "kernel-only"
    IO.FS.writeFile (project / "Example.lean") source
    let manifest ← IO.FS.readFile (project / "foundation_manifest.json")
    -- What this runtime reports for reads that fail the two ways the controls cause: a file that
    -- does not exist, and a directory in a file's place.
    let missing ← readFailure (project / "Absent.lean")
    let directory ← readFailure (project / "docs")
    for (binary, flags) in
        #[("docFenceAudit", #["--jobs", "1", "--verbose"]), ("axiomGate", #["--with-docs"])] do
      if binary == "axiomGate" then
        IO.FS.removeFile (project / "Example.lean")
        let _ ← observe root project "setup-missing" binary flags {
          failure := true, status := "incomplete", ids := ["RG2001"] }
        IO.FS.writeFile (project / "Example.lean") source
        IO.println "documentation axiomGate/initial-source-missing: PASS"
      let mut phases := #[("positive", "", "")]
      for (label, path, operation, reason) in #[
          ("source-change", "Example.lean", "append",
              "producer-source: source snapshot changed: Example"),
          ("source-missing", "Example.lean", "remove",
              "producer-source: source snapshot unavailable: Example"),
          ("source-unreadable", "Example.lean", "directory",
              "producer-source: source snapshot unavailable: Example"),
          ("configuration-unreadable", "foundation_manifest.json", "directory",
              "producer-source: configuration snapshot unavailable:"),
          ("configuration-change", "foundation_manifest.json", "append",
              "producer-source: configuration snapshot changed"),
          ("configuration-missing", "foundation_manifest.json", "remove",
              "producer-source: configuration snapshot changed")] do
        if sourceReadOnly &&
            !#["source-missing", "source-unreadable", "configuration-unreadable"].contains
                label then continue
        let mutation :=
            s!"run_cmd do\n  let path := (← IO.currentDir) / \"{path}\"\n  {action operation}\n"
        phases := phases.push (label, mutation, reason) |>.push (label ++ "-restored", "", "")
      for (phase, mutation, reason) in phases do
        writeFence project
            ("import Lean\nimport Example\n" ++ mutation ++
                "theorem fenceClaim : True := dependency\n")
        let bad := !mutation.isEmpty
        -- Documentation's top-level result contains the project refusal only; the
        -- transcript additionally contains its distinct fence/compilation refusals.
        let (process, _) ← observe root project s!"{binary}-{phase}" binary flags {
          failure := bad, status := if bad then "incomplete" else "completed",
          ids := if bad then ["RG2005"] else [], reason,
          positiveText := s!"{RegulaPolicy.Compiler.positiveSummary RegulaPolicy.Compiler.candidate}=1/1" } timedEnv
        if bad then
          let scope := if binary == "docFenceAudit" then project / "docs" else project
          IO.ofExcept
              (checked_documentation.run (process.stdout ++ process.stderr) scope.toString
                  reason phase missing directory)
        IO.println s!"documentation {binary}/{phase}: PASS"
    if sourceReadOnly then
      for stage in #["file", "build"] do
        let target := project / (if stage == "file" then "Standalone.lean" else "Example.lean")
        let phases := if stage == "file" then
          #["initial-missing", "positive", "source-missing", "restored", "source-unreadable",
              "restored"]
          else
              #["positive", "source-change", "restored", "source-missing", "restored",
                  "source-unreadable", "restored"]
        for index in [:phases.size] do
          let phase := phases[index]!
          if ← target.isDir then IO.FS.removeDir target
          if phase == "initial-missing" then
            if ← target.pathExists then IO.FS.removeFile target
          else
            let operation := if phase == "source-change" then "append" else if phase ==
                                                                             "source-missing" then
                                                                                 "remove" else
                                                                                     "directory"
            let location := if stage == "file" then
                s!"let path : System.FilePath := {toJson target.toString |>.compress}"
              else "let path ← Lean.getFileName"
            let mutation := if phase.startsWith "source-" then
                s!"run_cmd do\n  {location}\n  {action operation}\n" else ""
            IO.FS.writeFile target ("import Lean\n" ++ source ++ mutation)
          let flags := if stage == "file" then
              #["--file", target.fileName.getD "", "--claim", "kernel-only"] else #["--with-docs"]
          let bad := phase.startsWith "source-" || phase == "initial-missing"
          let reason := if !phase.startsWith "source-" then "" else
            "producer-source: source snapshot " ++
                (if phase == "source-change" then "changed" else "unavailable")
          let (_, some result) ← observe root project s!"{stage}-{index}" "axiomGate" flags {
              failure := bad, status := if bad then "incomplete" else "completed",
              ids := if bad then [if phase == "initial-missing" then "RG2001" else "RG2005"] else
                                  [], reason }
            | throw <| IO.userError "missing boundary result"
          if phase.startsWith "source-" && phase != "source-change" then
            let why ← IO.ofExcept do
              let ds ← array result "diagnostics"
              let some d := ds[0]? | throw "missing source refusal"
              detail d
            requireChecks [⟨"exact unavailable IO reason", why.contains
              (if phase == "source-missing" then missing else directory)⟩,
              ⟨"exact unavailable source", why.contains (target.fileName.getD "")⟩]
          IO.println s!"source boundary {stage}/{phase}: PASS"
    -- Original checked sources remain unchanged: mutations happened in owned audit
    -- copies. Assert this rather than silently repair an unexpected outer mutation.
    requireChecks
        [⟨"outer configuration unchanged", (← IO.FS.readFile (project / "foundation_manifest.json"))
            == manifest⟩]
end Regula.Qualification.DocumentationSource
