import Regula.Checker.AcceptanceLink
import Regula.Checker.Inspection
import Regula.Cli.Setup
import Lean.Elab.Command

/-! # Controls of the reads of whether a path is present

A path that cannot be read, `locked/child` where `locked` is a directory without search
permission, which Lean's `System.FilePath.pathExists` and `System.FilePath.isDir` read as absent
(https://github.com/rbeauchamp/regula/issues/430). The first acceptance step builds this module, and
its build fails when a control does not give the expected result. These controls are about the
file system, a trusted boundary: they observe the reads on the toolchain's file system calls, and
they prove nothing.

- The setup: Lean's `System.FilePath.metadata` of the path fails with `permissionDenied`, not
  `noFileOrDirectory`. The committed fixture
  `examples/fixtures/absence-reads/AbsenceReads/Refused.lean`, which `lean --run` runs on the path,
  prints that `pathExists` and `isDir` give `false` for it. So the path is one that the defect takes
  for an absent one. The fixture is outside every library of the package, so no module that the
  self-audit inspects names the two readers. A run that cannot make such a path, such as one with
  the permissions of the superuser, fails here rather than passing without observing it.
- The observer: `Regula.Filesystem.isPresent`, `isDirectory`, `metadataIfPresent`,
  `readFileIfPresent` and `entryIfPresent` each fail with the read's `permissionDenied`. The
  theorems of `Regula.Filesystem` (`isPresent_error` and the others) state this for every error
  that is not `noFileOrDirectory`; this control observes that the toolchain's read gives such an
  error here.
- Sites that read through the observer, one for each outcome that `false` used to give: a refusal
  with another reason (`AcceptanceLink.require`, `Construction.markdownPaths`), an absent record
  (`Inspection.freezeArtifact`) and a walk past the path to its parent (`Setup.guidanceDirs`). Each
  fails with the read's `permissionDenied` instead. Each other changed site binds the observer's
  result in `IO` in the same way, so the error propagates there too, unless a caller catches it;
  this control does not run them.

The permissions of `locked` are given back before the temporary directory is removed. -/

namespace Regula.AbsenceControls

open Lean System

/-- The source of the committed fixture that runs Lean's two readers on the path that is its one
argument and prints what they give. -/
def refusedSource : String :=
  include_str "../../examples/fixtures/absence-reads/AbsenceReads/Refused.lean"

/-- Whether `result` is the failure of a read that the permissions of a directory denied. -/
def denied {α : Type} : Except IO.Error α → Bool
  | .error (.permissionDenied ..) => true
  | _ => false

/-- Run the controls in a new temporary directory, and fail with the first control that does not
give the expected result. -/
def check : IO Unit :=
  Regula.Filesystem.withOwnTempDir fun base => do
    let fail {α : Type} (message : String) : IO α := throw <| IO.userError message
    let locked := base / "locked"
    let path := locked / "child"
    IO.FS.createDirAll path
    IO.FS.writeFile (path / "AGENTS.md") "control"
    IO.Prim.setAccessRights locked 0
    try
      -- The setup: the read fails with `permissionDenied`, which Lean's two readers take for
      -- absence.
      unless denied (← path.metadata.toBaseIO) do
        fail s!"the control could not make an unreadable path: reading {path} did not fail \
          with permissionDenied"
      let source := base / "Refused.lean"
      IO.FS.writeFile source refusedSource
      let run ← IO.Process.output {
        cmd := ((← Lean.getBuildDir) / "bin/lean").toString
        args := #["--run", source.toString, path.toString]
        env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
      unless run.exitCode == 0 && run.stdout == "false false\n" do
        fail s!"Lean's pathExists and isDir did not both read the unreadable path {path} as \
          absent: exit {run.exitCode}, {run.stdout}{run.stderr}"
      -- The observer.
      let observed : List (String × Bool) := [
        ("isPresent", denied (← (Regula.Filesystem.isPresent path).toBaseIO)),
        ("isDirectory", denied (← (Regula.Filesystem.isDirectory path).toBaseIO)),
        ("metadataIfPresent", denied (← (Regula.Filesystem.metadataIfPresent path).toBaseIO)),
        ("readFileIfPresent", denied (← (Regula.Filesystem.readFileIfPresent path).toBaseIO)),
        ("entryIfPresent", denied (← (Regula.Filesystem.entryIfPresent path).toBaseIO))]
      -- Sites that read through it.
      let sites : List (String × Bool) := [
        ("Regula.Checker.AcceptanceLink.require",
          denied (← (Regula.Checker.AcceptanceLink.require path "control").toBaseIO)),
        ("Regula.Filesystem.Construction.markdownPaths",
          denied (← (Regula.Filesystem.Construction.markdownPaths path).toBaseIO)),
        ("Regula.Checker.Inspection.freezeArtifact",
          denied (← (Regula.Checker.Inspection.freezeArtifact `Control
            (path / "Control.olean")).toBaseIO)),
        ("Regula.Cli.Setup.guidanceDirs",
          denied (← (Regula.Cli.Setup.guidanceDirs path).toBaseIO))]
      for (name, refused) in observed ++ sites do
        unless refused do
          fail s!"{name} did not fail with the read's permissionDenied for the unreadable path \
            {path}"
    finally
      IO.Prim.setAccessRights locked 448

run_cmd check

end Regula.AbsenceControls
