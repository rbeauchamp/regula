import Regula.CompilerProbe
import Regula.Qualification.Support

/-! # Isolated compiler adaptation

Prepare an immutable candidate revision and exercise existing qualification campaigns with
an installed Elan toolchain. Receipts describe development observations, never admission
authority. Git, Elan, GNU timeout, compiler identity, and filesystem stability are trusted. -/

namespace Regula.Toolchain
open Lean System

private def checked (root : FilePath) (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args, cwd := some root }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"{cmd} {args} failed ({out.exitCode}):\n{out.stdout}{out.stderr}"
  return out.stdout.trimAscii.toString

private def cleanHead (root : FilePath) : IO String := do
  unless (← checked root "git" #["status", "--porcelain", "--untracked-files=normal"]).isEmpty do
    throw <| IO.userError s!"commit or preserve changes before qualification: {root}"
  checked root "git" #["rev-parse", "HEAD"]

private def identityJson (i : Identity) : Json := Json.mkObj [
  ("version", .str i.version), ("commit", .str i.commit),
  ("legacyCompilerTrust", .str i.legacyCompilerTrust.spelling)]

private def metadataDir (root : FilePath) : FilePath := root / ".lake/regula-toolchain"

private def prepare (root : FilePath) (selector : String) (destination : FilePath) : IO Unit := do
  let base ← cleanHead root
  let template := include_str "../RegulaPolicy/Compiler.lean"
  unless (← IO.FS.readFile (root / "lean/RegulaPolicy/Compiler.lean")) == template do
    throw <| IO.userError "compiler policy differs from this driver build; rebuild the driver"
  let identity ← probe root selector
  if ← destination.pathExists then
    throw <| IO.userError s!"candidate destination already exists: {destination}"
  let _ ← checked root "git" #["worktree", "add", "--detach", destination.toString, base]
  let candidate ← IO.FS.realPath destination
  -- The imported policy is also a build dependency of this executable. Replacing escaped
  -- Lean string literals specializes the same policy; the candidate recompiles its proofs.
  let policy := template.replace (reprStr RegulaPolicy.Compiler.version) (reprStr identity.version)
    |>.replace (reprStr RegulaPolicy.Compiler.commit) (reprStr identity.commit)
    |>.replace
      s!"def legacyCompilerTrust : LegacyCompilerTrust := .{RegulaPolicy.Compiler.legacyCompilerTrust.spelling}"
      s!"def legacyCompilerTrust : LegacyCompilerTrust := .{identity.legacyCompilerTrust.spelling}"
    |>.replace "def candidate : Bool := false" "def candidate : Bool := true"
  IO.FS.writeFile (candidate / "lean/RegulaPolicy/Compiler.lean") policy
  IO.FS.writeFile (candidate / "lean-toolchain") (selector ++ "\n")
  let _ ← checked candidate "git" #["add", "lean-toolchain", "lean/RegulaPolicy/Compiler.lean"]
  let _ ← checked candidate "git" #["commit", "--allow-empty", "-m",
    s!"chore(toolchain): prepare Lean {identity.version} at {identity.commit}"]
  let revision ← cleanHead candidate
  IO.FS.createDirAll (metadataDir candidate)
  Qualification.writeJson (metadataDir candidate / "prepared.json") (Json.mkObj [
    ("baseRevision", .str base), ("candidateRevision", .str revision),
    ("selector", .str selector), ("compiler", identityJson identity)])
  IO.println s!"Prepared unqualified candidate {revision} at {candidate}."
  IO.println s!"Run: lake exe toolchain qualify {candidate}"

private def qualify (root candidate : FilePath) : IO UInt32 := do
  let candidate ← IO.FS.realPath candidate
  let metadata := metadataDir candidate
  let receipt := metadata / "qualification.json"
  Qualification.writeJson receipt (Json.mkObj [
    ("purpose", .str "development compiler qualification observations"),
    ("status", .str "incomplete"), ("grantsSupport", .bool false)])
  let prepared ← Qualification.readJson (metadata / "prepared.json")
  let selector ← IO.ofExcept (prepared.getObjValAs? String "selector")
  let revision ← IO.ofExcept (prepared.getObjValAs? String "candidateRevision")
  let compiler ← IO.ofExcept (prepared.getObjVal? "compiler")
  let capability ← IO.ofExcept (compiler.getObjValAs? String "legacyCompilerTrust")
  let some legacyCompilerTrust := RegulaPolicy.Compiler.LegacyCompilerTrust.parse? capability
    | throw <| IO.userError "prepared compiler capability is unknown"
  let identity : Identity := {
    version := ← IO.ofExcept (compiler.getObjValAs? String "version")
    commit := ← IO.ofExcept (compiler.getObjValAs? String "commit")
    legacyCompilerTrust }
  let mut results : List Observation := []
  let writeReceipt (results : List Observation) (unchanged : Bool) : IO Unit :=
    Qualification.writeJson receipt (Json.mkObj [
      ("purpose", .str "development compiler qualification observations"),
      ("status", .str (if unchanged && complete results then "complete" else "incomplete")),
      ("grantsSupport", .bool false), ("prepared", prepared),
      ("campaigns", toJson (results.map fun r => Json.mkObj [
        ("name", .str r.campaign.name), ("lakeArguments", toJson r.campaign.args),
        ("expectedExit", toJson r.campaign.expectedExit.toNat),
        ("exitCode", toJson r.exitCode.toNat), ("observationMet", .bool r.meets)]))])
  -- Invalidate prior success before probing identity, finding a timer, or starting a process.
  writeReceipt [] false
  let unchanged : IO Unit := do
    unless (← cleanHead candidate) == revision do
      throw <| IO.userError "candidate revision changed; prepare a new candidate"
    unless (← probe root selector) == identity do
      throw <| IO.userError "selected compiler identity changed"
  unchanged
  let timer ← Qualification.timeoutCommand
  let lean ← selectedLean root selector
  let some bin := lean.parent | throw <| IO.userError "compiler has no binary directory"
  let baseEnv ← selectedEnv selector lean
  for campaign in campaigns do
    unchanged
    IO.println s!"{identity.version}: {campaign.name} (420-second limit)"
    (← IO.getStdout).flush
    let env := baseEnv ++ #[("REGULA_COMPILER_QUALIFICATION",
      if campaign.diagnostic then some "1" else none)]
    let out ← IO.Process.output {
      cmd := timer
      args := #["--signal=KILL", "420s", (bin / "lake").toString] ++ campaign.args.toArray
      cwd := some candidate, env }
    IO.FS.writeFile (metadata / s!"{campaign.name}.log") (out.stdout ++ out.stderr)
    results := results ++ [⟨campaign, out.exitCode, out.stdout ++ out.stderr⟩]
    writeReceipt results false
    unchanged
    IO.println s!"  exit {out.exitCode}; {metadata / s!"{campaign.name}.log"}"
    (← IO.getStdout).flush
    if campaign.name == "build" && out.exitCode != 0 then break
  unchanged
  writeReceipt results true
  IO.println s!"Development qualification receipt: {receipt}"
  return if complete results then 0 else 1

end Regula.Toolchain

/-- Prepare or qualify a candidate; invalid syntax never starts a campaign. -/
def main (args : List String) : IO UInt32 := do
  let root ← Regula.Qualification.rootDirectory
  return ← match args with
  | ["prepare", selector, destination] => do
    Regula.Toolchain.prepare root selector ⟨destination⟩
    return 0
  | ["qualify", candidate] => Regula.Toolchain.qualify root ⟨candidate⟩
  | _ => throw <| IO.userError "usage: lake exe toolchain prepare \
      INSTALLED_ELAN_TOOLCHAIN NEW_DIRECTORY | qualify DIRECTORY"
