import Regula.Qualification.SourceEvidence

/-! # Frozen-input failure qualification

Import/failed-build/failed-compilation source-binding qualification. A failed
operation must not skip frozen-input checks or misclassify an ordinary compiler error. -/
namespace Regula.Qualification.FrozenExit
open Lean System RegulaQualification RegulaQualification.Evidence SourceEvidence

private def importSource (enabled : Bool) (action : String) : String :=
  "import Lean\nopen Lean Elab Command in\nrun_cmd do\n  let path ← getFileName\n  elabCommand (← `(initialize do\n    if " ++
    (if enabled then "true" else "false") ++ " && (← IO.appPath).fileName == some \"axiomGate\" then\n      let path : System.FilePath := $(quote path)\n      " ++ action ++
    "))\ntheorem valid : True := True.intro\n"

private def lost := "open Lean Elab Command in\nrun_cmd do\n  let path ← getFileName\n  IO.FS.removeFile path\n  let _ ← IO.FS.readFile path\n  pure ()\n"

private structure Case where
  label : String
  source : String := good
  fence : String := good
  fileSource : String := good
  flags : Array String := #[]
  binary : String := "axiomGate"
  ids : List String := []
  reason : String := ""
  grouped : Bool := false

private def runCase (root project : FilePath) (manifest : String) (case : Case) : IO Unit := do
  IO.FS.writeFile (project / "foundation_manifest.json") manifest
  IO.FS.writeFile (project / "Example.lean") case.source
  IO.FS.writeFile (project / "Standalone.lean") case.fileSource
  writeFence project case.fence
  clearBuild project
  let _ ← observe root project (case.label.replace "/" "-") case.binary case.flags {
    failure := !case.ids.isEmpty, status := if case.ids.isEmpty then "completed" else "incomplete",
    ids := case.ids, reason := case.reason, grouped := case.grouped, impact := some "incomplete" }
  IO.println s!"frozen exits {case.label}: PASS"

/-- Preserve all upstream operation/exit controls, with disjoint outputs and fresh
artifacts on every positive, single-defect negative and restored invocation. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "frozen-exits" fun project => do
    prepareCoreProject root project "frozen_adopter" "standard-logical"
    let manifest ← IO.FS.readFile (project / "foundation_manifest.json")
    let check := runCase root project manifest
    for (binary, flags) in #[("docFenceAudit", #["--jobs", "1", "--verbose"]), ("axiomGate", #["--with-docs"])] do
      let action := "IO.FS.writeFile path ((← IO.FS.readFile path) ++ \"\\n\")"
      for phase in #["positive", "changed", "restored"] do
        let bad := phase == "changed"
        check {
          label := s!"import/{binary}/{phase}", binary, flags, grouped := true,
          fence := importSource bad action, ids := if bad then ["RG4002", "RG2005"] else [],
          reason := if bad then "producer-source: source snapshot changed: DocFence_1" else "" }
      let action := "IO.FS.removeFile path\n      let _ ← IO.FS.readFile path\n      pure ()"
      check {
        label := s!"import/{binary}/missing-and-throw", binary, flags, grouped := true,
        fence := importSource true action, ids := ["RG4002", "RG2005"],
        reason := "producer-source: source snapshot unavailable: DocFence_1" }
      check { label := s!"import/{binary}/throw-restored", binary, flags, grouped := true, fence := importSource false action }
      let action := "let _ := path\n      throw <| IO.userError \"producer-source: deliberate unchanged initializer failure\""
      check {
        label := s!"import/{binary}/unchanged-exception", binary, flags, grouped := true,
        fence := importSource true action, ids := ["RG4002"], reason := "checker inspection failed" }
      check { label := s!"import/{binary}/exception-restored", binary, flags, grouped := true, fence := importSource false action }
    for (label, binary, flags) in #[
        ("fresh", "axiomGate", #[]), ("incremental", "axiomGate", #["--incremental"]),
        ("file-dependency", "axiomGate", #["--file", "Standalone.lean", "--claim", "standard-logical"]),
        ("documentation-build", "docFenceAudit", #["--jobs", "1"])] do
      for phase in #["positive", "missing", "restored", "ordinary-error", "ordinary-restored"] do
        let missing := phase == "missing"
        let ordinary := phase == "ordinary-error"
        check {
          label := s!"build/{label}/{phase}", binary, flags,
          source := good ++ (if missing then lost else if ordinary then "\ndef bad : Nat := \"wrong\"\n" else ""),
          ids := if missing then ["RG2005"] else if ordinary then [if binary == "axiomGate" then "RG2003" else "error"] else [],
          reason := if missing then "producer-source: source snapshot unavailable: Example" else "" }
    for (binary, flags) in #[("docFenceAudit", #["--jobs", "1"]), ("axiomGate", #["--with-docs"])] do
      check {
        label := s!"compile/{binary}/missing", binary, flags, fence := good ++ lost,
        ids := ["RG4002", "RG2005"], reason := "producer-source: source snapshot unavailable: DocFence_1" }
      check { label := s!"compile/{binary}/restored", binary, flags }
    let flags := #["--file", "Standalone.lean", "--claim", "standard-logical"]
    let mutation := "open Lean Elab Command in\nrun_cmd do\n  let path := (← IO.currentDir) / \"Standalone.lean\"\n  IO.FS.removeFile path\n  let _ ← IO.FS.readFile path\n  pure ()\n"
    check {
      label := "build/original-file-missing", flags, source := good ++ mutation,
      ids := ["RG2005"], reason := "producer-source: source snapshot unavailable: AuditFile_" }
    check { label := "build/original-file-restored", flags }
    check {
      label := "compile/file/missing", flags, fileSource := good ++ lost,
      ids := ["RG2005"], reason := "producer-source: source snapshot unavailable: AuditFile_" }
    check { label := "compile/file/restored", flags }
    let mutation := "run_cmd do\n  let path := (← IO.currentDir) / \"foundation_manifest.json\"\n  IO.FS.removeFile path\n  let _ ← IO.FS.readFile path\n  pure ()\n"
    check {
      label := "build/configuration-missing", source := good ++ mutation,
      ids := ["RG2005"], reason := "producer-source: configuration snapshot changed:" }
    check { label := "build/configuration-restored" }
end Regula.Qualification.FrozenExit
