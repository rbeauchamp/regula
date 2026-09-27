import Regula.Qualification.Support

/-! # Diagnostic receipt boundary qualification

Execute the public diagnostic boundary with stale completed evidence and actual
timeout discovery/spawn failures. These are operational observations, not OS proofs. -/
namespace Regula.Qualification.ReceiptBoundary
open Lean System

/-- Test-only timeout substitute: discovery succeeds, then the selected executable
disappears before spawn. No production timeout selection hook is needed. -/
def worker (args : List String) : IO UInt32 := do
  requireChecks [⟨"timeout version probe", args == ["--version"]⟩]
  IO.FS.removeFile (← IO.appPath)
  IO.println "GNU coreutils qualification substitute"
  return 0

/-- Preserve existing completed evidence only until the next public invocation starts. -/
def check : IO Unit := do
  let root ← rootDirectory
  let executable ← IO.appPath
  withScratch root "receipt-boundary" fun scratch => do
    for route in #[#["acceptance", "fences"], #["environments"]] do
      let evidence := scratch / "evidence.json"
      for fault in #["missing", "unusable", "spawn"] do
        let bin := scratch / s!"{route[0]!}-{fault}"
        IO.FS.createDir bin
        if fault == "unusable" then
          IO.FS.writeFile (bin / "gtimeout") "not an executable\n"
        if fault == "spawn" then
          IO.FS.writeBinFile (bin / "gtimeout") (← IO.FS.readBinFile executable)
          let mode ← IO.Process.output
              {cmd := "/bin/chmod", args := #["+x", (bin / "gtimeout").toString]}
          requireChecks [⟨"executable fixture", mode.exitCode == 0⟩]
        writeJson evidence
            (Json.mkObj [("status", toJson "completed"), ("attemptId", toJson "old")])
        let result ← IO.Process.output {
          cmd := executable.toString, args := route ++ #["--evidence", evidence.toString],
          env := #[("PATH", some bin.toString),
            ("REGULA_QUALIFICATION_WRAPPER", none),
            ("REGULA_RECEIPT_TIMER", if fault == "spawn" then some "1" else none)] }
        let current ← readJson evidence
        let status ← IO.ofExcept (current.getObjValAs? String "status")
        let attempt ← IO.ofExcept (current.getObjValAs? String "attemptId")
        let log := result.stdout ++ result.stderr
        requireChecks [⟨"failure really occurred", result.exitCode != 0⟩,
          ⟨"old completion invalidated", status == "incomplete" && attempt != "old" &&
              !attempt.isEmpty⟩,
          ⟨"intended timeout discovery refusal", fault == "spawn" ||
              log.contains "requires GNU coreutils timeout"⟩,
          ⟨"selected timer disappeared before spawn", fault != "spawn" ||
            (!(← (bin / "gtimeout").pathExists) && !log.contains "requires GNU coreutils timeout")⟩]
        IO.println s!"receipt boundary {route[0]!}/{fault}: PASS"
end Regula.Qualification.ReceiptBoundary
