import Regula.Qualification.DependencySnapshot

/-! # Input inventory fault injection

Native Lake-boundary fault injection retaining root and Markdown inventory
controls. The copied qualification executable is a test-only argv proxy. -/
namespace Regula.Qualification.InputInventory
open Lean System DependencySnapshot

def requiredEnv (name : String) : IO String := do
  let some value ← IO.getEnv name | throw <| IO.userError s!"missing {name}"
  return value

/-- Copy the native dispatcher, without generating an interpreter or shell program. -/
def copyExecutable (source target : FilePath) : IO Unit := do
  IO.FS.writeBinFile target (← IO.FS.readBinFile source)
  success (← run (target.parent.getD ".") "chmod" #["755", target.toString])

/-- Called only when the executable has been installed as the isolated Lake proxy. -/
def worker (args : List String) : IO UInt32 := do
  let record : FilePath := ← requiredEnv "INVENTORY_RECORD"
  let mode ← requiredEnv "INVENTORY_FAULT"
  let active := args.head? == some "build" && !(← record.pathExists)
  if active then
    if mode == "root-add" then
      IO.FS.createDirAll "Example"
      IO.FS.writeFile "Example/New.lean" "/-! Added after root discovery. -/\naxiom escaped : False\n"
    else if mode.startsWith "docs-" then
      let target : FilePath := ← requiredEnv "INVENTORY_DOC"
      if mode == "docs-remove" then IO.FS.removeFile target
      else IO.FS.writeFile target "```lean\nexample : True := True.intro\n```\n"
  let command ← requiredEnv "INVENTORY_LAKE"
  let child ← IO.Process.spawn {
    cmd := command, args := args.toArray,
    stdin := .inherit, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  if active then
    writeJson record (Json.mkObj [("buildExit", toJson code.toNat),
      ("addedBuilt", toJson (← (FilePath.mk ".lake/build/lib/lean/Example/New.olean").pathExists))])
  return code

def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "input-inventory" fun scratch => do
    let project := scratch / "project"
    IO.FS.createDirAll (project / "Example")
    toolchain root project
    IO.FS.writeFile (project / "Example.lean") "/-! Empty declared surface. -/\n"
    IO.FS.writeFile (project / "lakefile.lean")
      "import Lake\nopen Lake DSL\npackage inventory_control\nlean_lib Example where\n  globs := #[.andSubmodules `Example]\n"
    manifest project "kernel-only"
    success (← run project "lake" #["update"] cleanEnv)
    let tools := scratch / "tools"
    IO.FS.createDirAll tools
    copyExecutable (← IO.appPath) (tools / "lake")
    let resolved ← run root "/usr/bin/which" #["lake"]
    success resolved
    let record := scratch / "build.json"
    let path ← requiredEnv "PATH"
    let env := cleanEnv ++ #[("REGULA_QUALIFICATION_WRAPPER", some "inventory"),
      ("INVENTORY_LAKE", some resolved.stdout.trimAscii.toString), ("INVENTORY_RECORD", some record.toString),
      ("PATH", some (tools.toString ++ ":" ++ path))]
    for (mode, flag) in #[("incremental", "--incremental"), ("build-lint", "--build-lint")] do
      for phase in #["positive", "root-add", "restored"] do
        removeFile (project / "Example/New.lean")
        if phase != "root-add" then clearBuild project
        requireChecks [⟨"added module starts absent",
          !(← (project / ".lake/build/lib/lean/Example/New.olean").pathExists)⟩]
        removeFile record
        let output := scratch / s!"{mode}-{phase}.json"
        let result ← run project (root / ".lake/build/bin/axiomGate").toString
          #["--project", project.toString, flag, "--json-out", output.toString]
          (env.push ("INVENTORY_FAULT", some phase))
        let packet ← readJson output
        let log := result.stdout ++ result.stderr
        if phase == "root-add" then
          let observation ← readJson record
          requireChecks [⟨"added root actually built", observation == Json.mkObj [
            ("buildExit", toJson (0 : Nat)), ("addedBuilt", toJson true)]⟩,
            ⟨s!"root inventory refusal: {log}\n{packet.compress}", result.exitCode != 0 && log.contains "root inventory changed:" &&
              !log.contains "accepted " &&
              (packet.getObjValAs? String "status").toOption == some "incomplete" &&
              (packet.getObjVal? "acceptance").toOption.isNone⟩]
        else
          success result
          requireChecks [⟨"root positive", accepted packet⟩]
        IO.println s!"root inventory {mode}/{phase}: PASS"
    let docs := project / "docs"
    IO.FS.createDirAll docs
    IO.FS.writeFile (docs / "control.md") "```lean\nexample : True := True.intro\n```\n"
    let target := docs / "target.md"
    for route in #["docFenceAudit", "ruleExamples"] do
      let phases := #["positive", "docs-edit", "restored", "docs-remove", "restored"]
      for index in [:phases.size] do
        let phase := phases[index]!
        removeFile record
        let bad := phase.startsWith "docs-"
        IO.FS.writeFile target (if bad then "```lean\nexample : False := True.intro\n```\n"
          else "```lean\nexample : True := True.intro\n```\n")
        clearBuild project
        let output := scratch / s!"{route}-{index}.json"
        let args := if route == "docFenceAudit" then #["--project", project.toString, "--jobs", "1"]
          else #["--documentation", project.toString, docs.toString, output.toString]
        let result ← run project (root / ".lake/build/bin" / route).toString args
          (env ++ #[("INVENTORY_FAULT", some phase), ("INVENTORY_DOC", some target.toString)])
        let log := result.stdout ++ result.stderr
        if bad then
          let observation ← readJson record
          let reason := if phase == "docs-remove" then "documentation inventory changed" else "documentation source changed"
          requireChecks [⟨"prerequisite build succeeded", (observation.getObjValAs? Nat "buildExit").toOption == some 0⟩,
            ⟨s!"Markdown inventory refused: {log}", result.exitCode != 0 && log.contains reason &&
              !log.contains "accepted "⟩]
          if ← output.pathExists then
            requireChecks [⟨"no documentation acceptance", ((← readJson output).getObjVal? "acceptance").toOption.isNone⟩]
        else success result
        IO.println s!"Markdown inventory {route}/{phase}: PASS"
end Regula.Qualification.InputInventory
