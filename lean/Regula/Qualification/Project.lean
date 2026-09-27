import Regula.Qualification.Support
import RegulaQualification.Json

/-! # Disposable adopter project setup

Shared disposable-adopter setup for producer and history controls. Lake's pinned
manifest is reused, not resolved against moving branches. All subprocesses scrub the
calling checkout's Lean paths. This adapter performs trusted IO, not policy inference. -/
namespace Regula.Qualification
open Lean System RegulaQualification

/-- Remove inherited paths for commands running in isolated adopters. -/
def cleanEnv : Array (String × Option String) := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)]

/-- A structural Lean name represented with the public tagged-name transport. -/
def nameJson (name : String) : Json := toJson (name.splitOn "." |>.map fun part => #["str", part])

/-- Fresh source-bound adopter sharing only pinned dependency artifacts. -/
def prepareProject (root project : FilePath) (packageName claim rationale : String) : IO Unit := do
  IO.FS.writeBinFile (project / "lean-toolchain") (← IO.FS.readBinFile (root / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.lean")
    s!"import Lake\nopen Lake DSL\npackage {packageName} where\n  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]\nrequire regula from {toJson root.toString |>.compress}\n@[default_target] lean_lib Example\n"
  writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim), ("execution", .str "checked"),
      ("rationale", .str rationale)]]),
    ("excluded-libraries", toJson (#[] : Array Json)), ("excluded-executables", toJson (#[] : Array Json))])
  let manifest ← readJson (root / "lake-manifest.json")
  let packages ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
  let packages := packages.map (·.setObjVal! "inherited" (.bool true)) |>.push (Json.mkObj [
    ("name", .str "regula"), ("scope", .str ""), ("type", .str "path"),
    ("dir", .str root.toString), ("configFile", .str "lakefile.lean"),
    ("manifestFile", .str "lake-manifest.json"), ("inherited", .bool false)])
  writeJson (project / "lake-manifest.json") (manifest.setObjVal! "packages" (toJson packages))
  IO.FS.createDirAll (project / ".lake")
  let result ← run root "ln" #["-s", (root / ".lake/packages").toString, (project / ".lake/packages").toString]
  requireChecks [⟨"pinned dependency link", result.exitCode == 0⟩]

/-- Core-only adopter for source/evidence controls. No checker dependency is imported
into the observed surface, matching the original standalone qualification path. -/
def prepareCoreProject (root project : FilePath) (packageName claim : String) : IO Unit := do
  IO.FS.writeBinFile (project / "lean-toolchain") (← IO.FS.readBinFile (root / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") s!"name = \"{packageName}\"\n[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\n[[lean_lib]]\nname = \"Example\"\n"
  let manifest ← readJson (root / "lake-manifest.json")
  writeJson (project / "lake-manifest.json")
    ((manifest.setObjVal! "packages" (toJson (#[] : Array Json))).setObjVal! "name" (.str packageName))
  writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim),
      ("rationale", .str "The same fixed mathematical claim in positive and restored phases.")]]),
    ("excluded-libraries", toJson (#[] : Array Json)), ("excluded-executables", toJson (#[] : Array Json))])
  IO.FS.createDirAll (project / "docs")

/-- Delete only this owned scratch project's build output before a restored control. -/
def clearBuild (project : FilePath) : IO Unit := do
  if ← (project / ".lake/build").pathExists then IO.FS.removeDirAll (project / ".lake/build")

/-- Require a new result path and run the actual public checker. -/
def observeProject (root project output : FilePath) (flags : Array String) : IO (IO.Process.Output × Json) := do
  requireChecks [⟨"result path must be fresh", !(← output.pathExists)⟩]
  let result ← run project (root / ".lake/build/bin/axiomGate").toString
    (#["--project", project.toString] ++ flags ++ #["--json-out", output.toString]) cleanEnv
  return (result, ← readJson output)

end Regula.Qualification
