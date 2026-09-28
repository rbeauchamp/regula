import Regula.Qualification.Support
import Regula.RegistryCodec
import RegulaQualification.Registry

/-! # Registry CLI qualification

Actual malformed-invocation qualification of six configuration failures; each invocation
starts with a seeded stale file in a unique scratch directory. The pure output oracle is
`RegulaQualification.Registry.checked_validation`. Then the registry and site validators
(`--validate-registry`, `--validate-site`) through the same executable: the exported registry
and a complete page inventory are accepted, and each intended-reason mutation (a rule record
with a field the registry no longer has, the previous schema version, a page with a field the
site inventory no longer has, a missing page) is refused. This is operational evidence for the
CLI, not a universal proof of `axiomGate`. -/

namespace Regula.Qualification.RegistryCli
open Lean System

/-- Six public CLI paths whose recognizable destination must be invalidated. -/
def cases (root scratch output : FilePath) : Array (Array String) := #[
  #["--claim", "unknown"], #["--unknown"],
  #["--file", "x.lean", "--incremental"],
  #["--project", (scratch / "missing-project").toString],
  #["--project", root.toString, "--project", root.toString],
  #["--json-out", output.toString]]

/-- Run the registry and site validators of the real executable on each candidate and require
acceptance exactly for the exported registry and the complete page inventory. -/
def checkValidators (root : FilePath) : IO Unit := do
  let gate := (root / ".lake/build/bin/axiomGate").toString
  withScratch root "registry-validators" fun scratch => do
    let registry := scratch / "registry.json"
    let exported ← run root gate #["--registry-out", registry.toString]
    unless exported.exitCode == 0 do
      throw <| IO.userError s!"--registry-out failed\n{exported.stdout}{exported.stderr}"
    let manifest ← readJson registry
    let rules ← IO.ofExcept (manifest.getObjValAs? (Array Json) "rules")
    let firstRule (f : Json → Json) : Json :=
      manifest.setObjVal! "rules" (toJson (rules.modify 0 f))
    let candidate := scratch / "candidate.json"
    let registryCases : List (String × Json × Bool) := [
      ("the exported registry", manifest, true),
      ("a rule record with availability",
        firstRule (·.setObjVal! "availability" (.str "existingChecker")), false),
      ("a rule record with attribution", firstRule (·.setObjVal! "attribution" (Json.mkObj [])),
        false),
      ("the previous schema version", manifest.setObjVal! "schemaVersion"
        (toJson (RegistryCodec.registrySchemaVersion - 1)), false)]
    for (label, value, accepted) in registryCases do
      writeJson candidate value
      let result ← run root gate #["--validate-registry", candidate.toString]
      unless (result.exitCode == 0) == accepted do
        throw <| IO.userError s!"--validate-registry on {label}: exit {result.exitCode}\n\
          {result.stderr}"
    let page (id : RuleId) : Json := Json.mkObj [("id", RegistryCodec.ruleJson id),
      ("route", toJson id.route), ("checkedExample", toJson true)]
    let pages := RuleId.all.map page
    let artifact (pages : List Json) : Json := Json.mkObj [
      ("required", toJson (RuleId.all.map RegistryCodec.ruleJson)),
      ("emitted", toJson ([] : List Json)), ("pages", toJson pages)]
    let siteCases : List (String × Json × Bool) := [
      ("the complete page inventory", artifact pages, true),
      ("a page with advertisedEnforced",
        artifact (pages.map fun p => p.setObjVal! "advertisedEnforced" (.bool true)), false),
      ("an inventory without its first page", artifact pages.tail, false)]
    for (label, value, accepted) in siteCases do
      writeJson candidate value
      let result ← run root gate #["--validate-site", registry.toString, candidate.toString]
      unless (result.exitCode == 0) == accepted do
        throw <| IO.userError s!"--validate-site on {label}: exit {result.exitCode}\n\
          {result.stderr}"
  IO.println "registry validator qualification: PASS (the exported registry and a complete page \
    inventory accepted; 3 registry and 2 site mutations refused)"

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
      | .error detail =>
          throw <| IO.userError s!"{arguments}: {detail}\n{result.stdout}{result.stderr}\n{report}"
  IO.println "registry CLI qualification: PASS (6 configuration failures invalidate current output)"
  checkValidators root

end Regula.Qualification.RegistryCli
