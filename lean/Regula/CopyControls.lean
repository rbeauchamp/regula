import Regula.Checker.Lake
import Regula.Qualification.Slot
import Lean.Elab.Command

/-! # Construction boundary controls

These controls exercise the native filesystem and Lake boundaries that the construction theorem
takes as hypotheses. They are counterexample aids, not proofs of those external mechanisms.
The acceptance build elaborates the refusal controls. `qualify combined` runs the loaded-workspace
control natively, as the product loads workspaces. No executable runs the deliberate link/FIFO
fixtures, and no workspace containing such a fixture is passed to Lake after a successful copy.
-/

namespace Regula.CopyControls

open Lean System
open Regula.Filesystem

/-- Require an external fixture-maker to succeed. The link and FIFO creation below is deliberate
negative input, never the implementation of an accepted copy. -/
private def fixture (command : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output {cmd := command, args}
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
      let slot := base / "conflicting-slot"
      construct slot []
      refused "conflicting source occurrences" "conflicting captured bytes" <|
        discard <| Regula.Qualification.Slot.prepareSlot source ⟨slot⟩
          #[(source / "plain", "source bytes".toUTF8), (source / "plain", "different".toUTF8)] #[] #[]
      let alias := base / "source-alias"
      fixture "ln" #["-s", source.toString, alias.toString]
      refused "slot linked source" "not a directory or" <|
        discard <| Regula.Qualification.Slot.copyTree alias (base / "slot-link-output")
      let gitAlias := base / "git-alias"
      fixture "ln" #["-s", (source / "plain").toString, gitAlias.toString]
      refused "slot linked Git pointer" "not a directory or" <|
        Regula.Qualification.Slot.materializeGit (base / "git-output") gitAlias
      fixture "ln" #["-s", "plain", (source / "link").toString]
      refused "source link" "not a directory or" (discard <| copy source (base / "link-output"))
      removeOwn .link (source / "link")
      IO.eprintln "construction controls: FIFO"
      fixture "mkfifo" #[(source / "pipe").toString]
      refused "source FIFO" "not a directory or" (discard <| copy source (base / "pipe-output"))
      refused "slot Git FIFO" "not a directory or" <|
        Regula.Qualification.Slot.materializeGit (base / "fifo-git-output") (source / "pipe")
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
      unless !(← (base / "absent").pathExists) do
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

-- Git's external index/blob/config boundary: the copy has the complete indexed worktree,
-- and every tracked link is the native Git target-text regular-file representation.
run_cmd do
  unless System.Platform.isWindows do
    withOwnTempDir fun base => do
      IO.eprintln "construction controls: Git target-text representation"
      let source := base / "git-source"
      construct source [⟨["plain"], .file "tracked file\n".toUTF8⟩]
      fixture "git" #["-C", source.toString, "init", "--quiet"]
      fixture "ln" #["-s", "plain", (source / "tracked-link").toString]
      fixture "git" #["-C", source.toString, "-c", "core.symlinks=true", "add", "plain", "tracked-link"]
      fixture "git" #["-C", source.toString, "-c", "user.name=Construction Control",
        "-c", "user.email=construction@example.invalid", "-c", "commit.gpgsign=false",
        "commit", "--quiet", "-m", "controlled index"]
      let target := base / "git-target"
      discard <| Construction.copyGit source target
      unless (← observeMetadata (target / "tracked-link")).type == .file &&
          (← readBytes (target / "tracked-link")) == "plain".toUTF8 do
        throw <| IO.userError "tracked Git link was not its target-text regular representation"
      let status ← IO.Process.output {
        cmd := "git", cwd := some target
        args := #["-c", "core.fileMode=true", "status", "--porcelain", "--untracked-files=all"]}
      unless status.exitCode == 0 && status.stdout.isEmpty do
        throw <| IO.userError s!"target-text Git checkout is not clean: {status.stdout}{status.stderr}"
      fixture "ln" #["-s", "plain", (source / "untracked-link").toString]
      refused "untracked Git source link" "not a directory or" <|
        discard <| Construction.copyGit source (base / "untracked-output")
      IO.eprintln "construction controls: tracked Git link regular and clean; untracked link refused"

/-- Loaded-workspace control: the lakefile sets packagesDir, while its loaded default manifest
omits that field. The source vendor entry is build state, not a directory to copy or link into.
Run in the native qualification executable because Lake's loader needs its initialized native
state; source elaboration tests the independent directory/file refusals above. -/
def checkWorkspace : IO Unit := do
  unless System.Platform.isWindows do
    withOwnTempDir fun base => do
      IO.eprintln "construction controls: loaded packages directory"
      let source := base / "project"
      let toolchain ← Construction.capture "lean-toolchain" ["lean-toolchain"]
      let lakefile := "import Lake\nopen Lake DSL\npackage construction_control where\n" ++
        "  packagesDir := \"vendor\"\n" ++
        "lean_lib Solo\n"
      let manifest := "{\"version\":\"1.1.0\",\"name\":\"construction_control\"," ++
        "\"lakeDir\":\".lake\",\"packages\":[]}\n"
      construct source (Construction.layout (toolchain ++ [
        ⟨["lakefile.lean"], .file lakefile.toUTF8⟩,
        ⟨["Solo.lean"], .file "/-! Plain source control. -/\n".toUTF8⟩,
        ⟨["lake-manifest.json"], .file manifest.toUTF8⟩,
        ⟨["vendor", "stale"], .file "must not be copied as project source".toUTF8⟩]))
      let target := base / "copied"
      let result ← Regula.Checker.Lake.copyProject source target target
      unless !(← (result.project / "vendor/stale").pathExists) &&
          (← IO.FS.readFile (result.project / "lake-manifest.json")) == manifest do
        throw <| IO.userError "copy used a manifest/default packages directory instead of Lake's workspace"
      unless !(← (result.project / ".lake/package-overrides.json").pathExists) do
        throw <| IO.userError "empty dependency graph changed captured configuration presence"
      Regula.Checker.Workspace.withRootWorkspace result.project fun ws => do
        unless ws.relPkgsDir == "vendor" &&
            ws.manifestFile == result.project / "lake-manifest.json" do
          throw <| IO.userError "ordinary copied load lost the loaded workspace configuration"
      if ← (source / "VENDOR").isDir then
        -- A deliberate configuration mutation exercises Lake's stored-spelling boundary.
        IO.FS.writeFile (source / "lakefile.lean") (lakefile.replace "vendor" "VENDOR")
        -- Two admitted moves change the stored spelling without treating the case alias as
        -- an independently occupied destination of the observer's replacement operation.
        replacePath (source / "lake-manifest.json") (source / "manifest-renaming")
        replacePath (source / "manifest-renaming") (source / "LAKE-MANIFEST.JSON")
        let folded ← Regula.Checker.Lake.copyProject source (base / "folded") (base / "folded")
        unless !(← (folded.project / "vendor/stale").pathExists) &&
            (← Regula.Filesystem.readFile (folded.project / "lake-manifest.json")) == manifest do
          throw <| IO.userError "case-folded packages or manifest location was not retained correctly"
      IO.println "construction workspace: configured packagesDir and captured manifest PASS"

end Regula.CopyControls
