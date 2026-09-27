import Regula.Qualification.Support
import RegulaQualification.Registry

/-! Actual malformed-invocation qualification. All seven former Python cases remain;
each invocation starts with a seeded stale file in a unique scratch directory.
The pure output oracle is `RegulaQualification.Registry.checked_validation`.
This is operational evidence for the CLI, not a universal proof of `axiomGate`. -/

namespace Regula.Qualification.RegistryCli
open Lean System

/-- Seven public CLI paths whose recognizable destination must be invalidated. -/
def cases (root scratch output : FilePath) : Array (Array String) := #[
  #["--claim", "unknown"], #["--unknown"],
  #["--file", "x.lean", "--incremental"],
  #["--project", (scratch / "missing-project").toString],
  #["--project", root.toString, "--project", root.toString],
  #["--json-out", output.toString],
  #["--legacy-json-out", (scratch / "legacy.json").toString]]

/-- Observe every case through the real executable; the oracle consumes the actual
exit code and reparsed destination, with no fallback for missing or malformed files. -/
def check : IO Unit := do
  let root ← rootDirectory
  withScratch root "registry-cli" fun scratch => do
    let output := scratch / "result.json"
    for arguments in cases root scratch output do
      writeJson output (Json.mkObj [("status", .str "completed"), ("old", .bool true)])
      let result ← run root (root / ".lake/build/bin/axiomGate").toString
        (#["--json-out", output.toString] ++ arguments)
      let report ← readJson output
      match RegulaQualification.Registry.checked_validation.run result.exitCode.toNat report with
      | .ok () => pure ()
      | .error detail => throw <| IO.userError s!"{arguments}: {detail}\n{result.stdout}{result.stderr}\n{report}"
  IO.println "registry CLI qualification: PASS (7 configuration failures invalidate current output)"

end Regula.Qualification.RegistryCli
