import RegulaProvision
import Regula.Filesystem
import Lean.Elab.Command

/-! # Controls of the provisioning link installation

These controls run the link installation of provisioning, `RegulaProvision.installLinkWith` at the
driver's operations `RegulaProvision.linkOps`, on the native filesystem that
`RegulaProvision.RefusesOccupied` and `Regula.Filesystem.ReadsEntry` describe. They observe that
boundary once on the toolchain's system calls and the installed `ln`; they prove nothing, and
`RegulaProvision.Link` states the theorems. The first acceptance step builds this module, and its
build fails when a control does not give the expected result. No program imports it.

- An ordinary installation: with nothing at the place of the directory in which the link is made,
  the run puts a link that resolves to the target at the path, where nothing was or where a stale
  link was, and leaves nothing at that place and no other new entry beside the path.
- An occupied place: a directory with an entry in it, a symbolic link to a directory, a symbolic
  link that resolves to nothing, a regular file and a FIFO at the directory's place each make the
  run fail with the error of `mkdir(2)` for an existing entry. Afterwards the entry has its type
  and its bytes, its entries or the file its link resolves to, nothing is at the path, nothing new
  is beside it, no link is in the target directory, and nothing was made at the place a dangling
  link names. -/

namespace Regula.ProvisionControls

open System

/-- Run a fixture maker, which must succeed. The links and the FIFO it makes are deliberate
occupants of the place where an installation makes its directory, never an installation's
output. -/
private def fixture (command : String) (args : Array String) : IO Unit := do
  let out ← IO.Process.output { cmd := command, args, stdin := .null }
  unless out.exitCode == 0 do throw <| IO.userError s!"fixture {command} failed: {out.stderr}"

/-- The type of the entry at `path`, read without following a link there, or `none` when nothing
is there. -/
private def kind (path : FilePath) : IO (Option IO.FS.FileType) := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => return some metadata.type
  | .error (.noFileOrDirectory ..) => return none
  | .error error => throw error

/-- The names in the directory `path`, sorted. -/
private def names (path : FilePath) : IO (List String) := do
  return ((← path.readDir).map (·.fileName)).toList.mergeSort (· ≤ ·)

/-- Fail with `label` and `what` unless `holds`. -/
private def require (label what : String) (holds : Bool) : IO Unit :=
  unless holds do throw <| IO.userError s!"provisioning link control {label}: {what}"

/-- One occupant of the place where the installation makes its directory: its label, how to plant
it at that place, and the check, after the refused run, that it is as it was. -/
private structure Occupant where
  /-- The control's name. -/
  label : String
  /-- Plant the occupant at the place (the argument). -/
  plant : FilePath → IO Unit
  /-- Check, after the run, that the occupant at the place (the argument) is unchanged. -/
  unchanged : FilePath → IO Bool

run_cmd do
  unless System.Platform.isWindows do
    Regula.Filesystem.withOwnTempDir fun base => do
      let nonce := "control"
      let target := base / "target"
      IO.FS.createDir target
      IO.FS.writeFile (target / "kept") "target bytes"
      let targetReal ← IO.FS.realPath target
      let targetIntact : IO Bool := do
        return (← names target) == ["kept"] && (← IO.FS.readFile (target / "kept")) == "target bytes"
      -- The ordinary installation, where nothing is at the path and where a stale link is.
      for (label, stale) in [("ordinary", false), ("ordinary over a stale link", true)] do
        let dir := base / label.replace " " "-"
        IO.FS.createDir dir
        let path := dir / "mathlib"
        let some (stage, _) := RegulaProvision.linkStage path nonce
          | throw <| IO.userError "the control's path has no parent or no name"
        if stale then fixture "ln" #["-s", (base / "stale").toString, path.toString]
        RegulaProvision.installLinkWith RegulaProvision.linkOps path target.toString nonce
        require label "no link at the path" ((← kind path) == some .symlink)
        require label "the link does not resolve to the target"
          ((← IO.FS.realPath path) == targetReal)
        require label "the directory is still there" ((← kind stage) == none)
        require label "a new entry beside the path" ((← names dir) == ["mathlib"])
        require label "the target changed" (← targetIntact)
      -- Each occupied place.
      let dangling := base / "absent"
      let occupants : List Occupant := [
        { label := "directory"
          plant := fun place => do
            IO.FS.createDir place
            IO.FS.writeFile (place / "inner") "inner bytes"
          unchanged := fun place => do
            return (← kind place) == some .dir && (← names place) == ["inner"] &&
              (← IO.FS.readFile (place / "inner")) == "inner bytes" },
        { label := "link to a directory"
          plant := fun place => fixture "ln" #["-s", target.toString, place.toString]
          unchanged := fun place => do
            return (← kind place) == some .symlink && (← IO.FS.realPath place) == targetReal },
        { label := "dangling link"
          plant := fun place => fixture "ln" #["-s", dangling.toString, place.toString]
          unchanged := fun place => do
            return (← kind place) == some .symlink && (← kind dangling) == none },
        { label := "regular file"
          plant := fun place => IO.FS.writeFile place "file bytes"
          unchanged := fun place => do
            return (← kind place) == some .file && (← IO.FS.readFile place) == "file bytes" },
        { label := "FIFO"
          plant := fun place => fixture "mkfifo" #[place.toString]
          unchanged := fun place => do return (← kind place) == some .other }]
      for occupant in occupants do
        let label := s!"occupied by a {occupant.label}"
        let dir := base / s!"occupied-{occupant.label.replace " " "-"}"
        IO.FS.createDir dir
        let path := dir / "mathlib"
        let some (stage, _) := RegulaProvision.linkStage path nonce
          | throw <| IO.userError "the control's path has no parent or no name"
        occupant.plant stage
        let before ← names dir
        match ← (RegulaProvision.installLinkWith RegulaProvision.linkOps path target.toString
            nonce).toBaseIO with
        | .ok () => throw <| IO.userError s!"provisioning link control {label}: installed"
        | .error (.alreadyExists ..) => pure ()
        | .error error =>
          throw <| IO.userError s!"provisioning link control {label}: wrong refusal: {error}"
        require label "the occupant changed" (← occupant.unchanged stage)
        require label "something is at the path" ((← kind path) == none)
        require label "a new entry beside the path" ((← names dir) == before)
        require label "the target changed" (← targetIntact)

end Regula.ProvisionControls
