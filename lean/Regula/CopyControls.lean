import Regula.Filesystem
import Lean.Elab.Command

/-! # Construction boundary controls

These controls exercise the native filesystem boundary that the construction theorem takes as
hypotheses. They are counterexample aids, not proofs of that external mechanism. The acceptance
build elaborates the refusal controls. No executable runs the deliberate link/FIFO fixtures.
-/

namespace Regula.CopyControls

open Lean System
open Regula.Filesystem

/-- Require an external fixture-maker to succeed. The link and FIFO creation below is deliberate
negative input, never the implementation of an accepted copy. Git fixture writers disable
automatic maintenance so no detached writer can race the subsequent source capture. -/
private def fixture (command : String) (args : Array String) : IO Unit := do
  let args := if command == "git" then #["-c", "maintenance.auto=false"] ++ args else args
  let out ← IO.Process.output (← Construction.gitProcessArgs {cmd := command, args})
  unless out.exitCode == 0 do throw <| IO.userError s!"fixture failed: {out.stderr}"

/-- Refuse an operation for its construction reason. A failure elsewhere does not qualify it. -/
private def refused (label needle : String) (action : IO Unit) : IO Unit := do
  match ← action.toBaseIO with
  | .ok _ => throw <| IO.userError s!"{label}: construction unexpectedly succeeded"
  | .error error =>
    unless error.toString.contains needle do
      throw <| IO.userError s!"{label}: wrong refusal: {error}"

-- POSIX no-follow and exclusive-creation boundary controls. Windows has no supported observer.
run_cmd do
  unless System.Platform.isWindows do
    withOwnTempDir fun base => do
      IO.eprintln "construction controls: source refusals"
      let source := base / "source"
      construct source [⟨["plain"], .file "source bytes".toUTF8⟩]
      let positive ← copy source (base / "positive")
      unless positive.length == 2 &&
          (← IO.FS.readFile (base / "positive/plain")) == "source bytes" do
        throw <| IO.userError "plain copy lost its source receipt or bytes"
      let policies := base / "policies"
      let selected := [".lake/policy.json", "tmp/policy.json", ".cache/policy.json", "policy.olean"]
      construct policies (Construction.layout (
        selected.map (fun path => ⟨(FilePath.mk path).components, .file "policy".toUTF8⟩) ++
        [⟨[".lake", "stale"], .file "stale".toUTF8⟩,
         ⟨[".cache", "stale"], .file "stale".toUTF8⟩,
         ⟨["tmp", "stale"], .file "stale".toUTF8⟩,
         ⟨["plain"], .file "ordinary".toUTF8⟩]))
      let selectedCopy := base / "selected-copy"
      discard <| Construction.sourceMain (["project", policies.toString, selectedCopy.toString] ++ selected)
      for path in selected do
        unless (← readFile (selectedCopy / path)) == "policy" do
          throw <| IO.userError "cold project copy lost selected policy bytes"
      unless (← readFile (selectedCopy / "plain")) == "ordinary" do
        throw <| IO.userError "cold project copy lost ordinary source bytes"
      for directory in [".lake", ".cache", "tmp"] do
        unless !(← Regula.Filesystem.isPresent (selectedCopy / directory / "stale")) do
          throw <| IO.userError "cold project selection included an unselected pruned sibling"
      fixture "ln" #["-s", "../plain", (policies / ".cache/link").toString]
      refused "selected policy link" "selected entry is not a regular file" <|
        discard <| Construction.sourceMain
          ["project", policies.toString, (base / "selected-link-output").toString, ".cache/link"]
      fixture "ln" #["-s", "..", (policies / ".cache/ancestor").toString]
      refused "selected policy ancestor link" "selected ancestor is not a directory" <|
        discard <| Construction.sourceMain
          ["project", policies.toString, (base / "selected-ancestor-output").toString, ".cache/ancestor/plain"]
      if ← Regula.Filesystem.isPresent (policies / ".CACHE/POLICY.json") then
        let foldedCopy := base / "folded-policy-copy"
        discard <| Construction.sourceMain
          ["project", policies.toString, foldedCopy.toString, ".CACHE/POLICY.json"]
        unless (← readFile (foldedCopy / ".CACHE/POLICY.json")) == "policy" do
          throw <| IO.userError "cold project copy lost a selected policy's stored spelling"
      refused "removed all domain" "unknown construction domain" <|
        discard <| Construction.sourceMain ["all", source.toString, (base / "all-output").toString]
      fixture "ln" #["-s", "plain", (source / "link").toString]
      refused "source link" "not a directory or" (discard <| copy source (base / "link-output"))
      removeOwn .link (source / "link")
      IO.eprintln "construction controls: FIFO"
      fixture "mkfifo" #[(source / "pipe").toString]
      refused "source FIFO" "not a directory or" (discard <| copy source (base / "pipe-output"))
      -- The observer intentionally has no removal kind for a FIFO. It stays in this fixture's
      -- private root, which withOwnTempDir removes as a whole after the control.
      let occupied := base / "occupied"
      IO.eprintln "construction controls: occupied destination"
      construct occupied [⟨["vendor"], .directory⟩]
      refused "occupied packages place" "occupied" (discard <| copy (base / "positive") occupied)
      let parent := base / "exclusive"
      IO.eprintln "construction controls: exclusive final link"
      construct parent []
      fixture "ln" #["-s", (base / "absent").toString, (parent / "vendor").toString]
      let output ← (Construction.emitWith Construction.observer parent
        [⟨["vendor"], .file "never follows the link".toUTF8⟩]).toBaseIO
      unless output matches .error _ do
        throw <| IO.userError "exclusive creation followed an occupied final link"
      unless !(← Regula.Filesystem.isPresent (base / "absent")) do
        throw <| IO.userError "exclusive creation wrote through a dangling link"
      -- Case aliases must collide at exclusive creation on a folding filesystem. Distinct
      -- spellings remain valid distinct entries on a case-sensitive filesystem.
      let probe := base / "case-probe"
      IO.eprintln "construction controls: case aliases"
      construct probe [⟨[".LaKe"], .directory⟩]
      if (← Construction.kindWith Construction.observer (probe / ".lake")) == some .dir then
        let result ← (construct (base / "case-output")
          [⟨[".LaKe"], .directory⟩, ⟨[".lake"], .directory⟩]).toBaseIO
        unless result matches .error _ do
          throw <| IO.userError "case-folded destination alias was not refused exclusively"

end Regula.CopyControls
