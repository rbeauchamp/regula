import RegulaProvision
import Regula.Filesystem
import Lean.Elab.Command

/-! # Controls of the provisioning link installation and of its selection of the pinned packages

The selection controls run provisioning's read of the pins of the Mathlib integration package,
`RegulaProvision.readPins`, and of a pinned revision, `RegulaProvision.manifestRevision`, on
manifests and package overrides files that they write, which Lake's own readers decode. They
observe that boundary, Lake's decoding of the files and the absence of an overrides file, once;
`RegulaProvision.selectPins` and `Regula.ProgramCheck.Provision` state the theorems. Each control
reads no network and acquires no Mathlib:

- The positive control: a manifest that records its packages directory, with one entry for each
  name, among them a path entry of its own, and no overrides file, gives its packages directory,
  the Mathlib entry's source and commit, and each Git entry's checkout directory and commit.
- A second `mathlib` entry after the first: its source and commit are taken, by the pins and by
  the check of the checkouts (`RegulaProvision.checkoutPin`), as Lake takes the last entry of a name.
- An overrides file with a Git entry for `mathlib` and one for another package: its entries are
  taken. One with a path entry for `mathlib`: nothing is shared.
- A path entry for `batteries` in the overrides file, or one that the manifest records as
  inherited, is refused, and the refusal names the package and the file
  (`RegulaProvision.pathRefusal`).
- A manifest without `packagesDir`, or with a null one, is refused, and so is an absent manifest.
- After each of these, the positive control is restored and gives its answer again.

The link controls run the link installation of provisioning, `RegulaProvision.installLinkWith` at the
driver's operations `RegulaProvision.linkOps`, on the native filesystem that
`RegulaProvision.RefusesOccupied` and `Regula.Filesystem.ReadsEntry` describe. They observe that
boundary once on the toolchain's system calls and the installed `ln`, and they read the text of a
link with `readlink`. They prove nothing: `RegulaProvision.Link` states the theorems. The first
acceptance step builds this module, and its build fails when a control does not give the expected
result. No program imports it.

- An ordinary installation: with nothing at the place of the directory in which the link is made,
  the run puts a link whose text is the target at the path, where nothing was or where a stale
  link was, and leaves nothing at that place and no other new entry beside the path.
- An occupied place: a directory with an entry in it, a symbolic link to a directory, a symbolic
  link that resolves to nothing, a regular file and a FIFO at the directory's place each make the
  run fail with the error of `mkdir(2)` for an existing entry. Afterwards the entry has its type
  and its contents (the text of a link, the bytes of a file, the names and bytes in a directory),
  nothing is at the path, nothing new is beside it, no link is in the target directory, and
  nothing was made at the place a dangling link names. -/

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

/-- The text of the symbolic link at `path`, as `readlink -n` prints it: Lean v4.34.1 has no
operation that reads it. -/
private def linkText (path : FilePath) : IO String := do
  let out ← IO.Process.output
    { cmd := "readlink", args := #["-n", path.toString], stdin := .null }
  unless out.exitCode == 0 do throw <| IO.userError s!"readlink {path} failed: {out.stderr}"
  return out.stdout

/-- The names in the directory `path`, sorted, listed through the admitted enumerator
(`Regula.Filesystem.Construction.listNames`), so a failed read of the directory fails the control
instead of returning fewer names. -/
private def names (path : FilePath) : IO (List String) := do
  return (← Regula.Filesystem.Construction.listNames path).mergeSort (· ≤ ·)

/-- Fail with `label` and `what` unless `holds`. -/
private def require (label what : String) (holds : Bool) : IO Unit :=
  unless holds do throw <| IO.userError s!"provisioning link control {label}: {what}"

/-- One occupant of the place where the installation makes its directory: its label, its type,
how to plant it at that place, and what the control reads of its contents, before and after the
refused run. -/
private structure Occupant where
  /-- The control's name. -/
  label : String
  /-- The type of the entry that `plant` makes. -/
  type : IO.FS.FileType
  /-- Plant the occupant at the place (the argument). -/
  plant : FilePath → IO Unit
  /-- The contents of the occupant at the place (the argument), which the refused run must leave
  as they were. -/
  contents : FilePath → IO String

run_cmd do
  unless System.Platform.isWindows do
    Regula.Filesystem.withOwnTempDir fun base => do
      let nonce := "control"
      let target := base / "target"
      IO.FS.createDir target
      IO.FS.writeFile (target / "kept") "target bytes"
      let targetReal ← IO.FS.realPath target
      let targetIntact : IO Bool := do
        return (← names target) == ["kept"] &&
          (← IO.FS.readFile (target / "kept")) == "target bytes"
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
        require label "the link's text is not the target" ((← linkText path) == target.toString)
        require label "the link does not resolve to the target"
          ((← IO.FS.realPath path) == targetReal)
        require label "the directory is still there" ((← kind stage) == none)
        require label "a new entry beside the path" ((← names dir) == ["mathlib"])
        require label "the target changed" (← targetIntact)
      -- Each occupied place.
      let dangling := base / "absent"
      let occupants : List Occupant := [
        { label := "directory"
          type := .dir
          plant := fun place => do
            IO.FS.createDir place
            IO.FS.writeFile (place / "inner") "inner bytes"
          contents := fun place => do
            return s!"{← names place} {← IO.FS.readFile (place / "inner")}" },
        { label := "link to a directory"
          type := .symlink
          plant := fun place => fixture "ln" #["-s", target.toString, place.toString]
          contents := linkText },
        { label := "dangling link"
          type := .symlink
          plant := fun place => fixture "ln" #["-s", dangling.toString, place.toString]
          contents := linkText },
        { label := "regular file"
          type := .file
          plant := fun place => IO.FS.writeFile place "file bytes"
          contents := IO.FS.readFile },
        { label := "FIFO"
          type := .other
          plant := fun place => fixture "mkfifo" #[place.toString]
          contents := fun _ => pure "" }]
      for occupant in occupants do
        let label := s!"occupied by a {occupant.label}"
        let dir := base / s!"occupied-{occupant.label.replace " " "-"}"
        IO.FS.createDir dir
        let path := dir / "mathlib"
        let some (stage, _) := RegulaProvision.linkStage path nonce
          | throw <| IO.userError "the control's path has no parent or no name"
        occupant.plant stage
        require label "the planted entry has another type" ((← kind stage) == some occupant.type)
        let contentsBefore ← occupant.contents stage
        let before ← names dir
        match ← (RegulaProvision.installLinkWith RegulaProvision.linkOps path target.toString
            nonce).toBaseIO with
        | .ok () => throw <| IO.userError s!"provisioning link control {label}: installed"
        | .error (.alreadyExists ..) => pure ()
        | .error error =>
          throw <| IO.userError s!"provisioning link control {label}: wrong refusal: {error}"
        require label "the occupant's type changed" ((← kind stage) == some occupant.type)
        require label "the occupant's contents changed"
          ((← occupant.contents stage) == contentsBefore)
        require label "something is at the path" ((← kind path) == none)
        require label "a new entry beside the path" ((← names dir) == before)
        require label "the target changed" (← targetIntact)
        require label "something is at the place the dangling link names"
          ((← kind dangling) == none)

/-! ## The selection of the pinned packages -/

/-- A manifest entry of the Git package `name` at the commit `rev` from `url`, in the form that Lake
writes. -/
private def gitEntry (name url rev : String) : Lean.Json :=
  Lean.Json.mkObj [("url", url), ("type", "git"), ("subDir", Lean.Json.null), ("scope", ""),
    ("rev", rev), ("name", name), ("manifestFile", "lake-manifest.json"), ("inputRev", rev),
    ("inherited", false), ("configFile", "lakefile.lean")]

/-- A manifest entry of the package `name` in the directory `dir`, in the form that Lake writes,
inherited when `inherited` holds. -/
private def pathEntry (name dir : String) (inherited := false) : Lean.Json :=
  Lean.Json.mkObj [("type", "path"), ("scope", ""), ("name", name),
    ("manifestFile", "lake-manifest.json"), ("inherited", inherited), ("dir", dir),
    ("configFile", "lakefile.lean")]

/-- The text of a manifest with `entries` that records the packages directory `packagesDir`: the
member is left out for `none`, and is `null` for `some none`. -/
private def manifestText (packagesDir : Option (Option String)) (entries : List Lean.Json) :
    String :=
  let recorded := match packagesDir with
    | none => []
    | some dir => [("packagesDir", match dir with | some dir => Lean.Json.str dir | none => .null)]
  (Lean.Json.mkObj ([("version", Lean.Json.str "1.2.0")] ++ recorded ++
    [("packages", Lean.Json.arr entries.toArray), ("name", "regula_mathlib"),
      ("lakeDir", ".lake")])).pretty

/-- The text of a package overrides file with `entries`, in the form that Lake writes. -/
private def overridesText (entries : List Lean.Json) : String :=
  (Lean.Json.mkObj [("schemaVersion", "1.2.0"), ("packages", Lean.Json.arr entries.toArray)]).pretty

/-- Fail with `label` and `what` unless `holds`. -/
private def requireSelection (label what : String) (holds : Bool) : IO Unit :=
  unless holds do throw <| IO.userError s!"provisioning selection control {label}: {what}"

/-- The pins that `readPins` gives the copy at `repo`, which must give some. -/
private def pinsOf (label : String) (repo : FilePath) : IO RegulaProvision.Pins := do
  let some (_, pins) ← RegulaProvision.readPins repo
    | throw <| IO.userError s!"provisioning selection control {label}: no Mathlib is shared"
  return pins

/-- The checkout directory and commit of each Git pin. -/
private def pinned (pins : RegulaProvision.Pins) : Array (String × String) :=
  pins.git.map fun (_, pin) => (pin.name, pin.rev)

/-- Fail unless the run `action` fails with an error whose text contains `needle`. -/
private def requireRefused {α : Type} (label needle : String) (action : IO α) : IO Unit := do
  match ← action.toBaseIO with
  | .ok _ => throw <| IO.userError s!"provisioning selection control {label}: not refused"
  | .error error =>
    requireSelection label s!"refused with '{error}', not for '{needle}'"
      (((toString error).splitOn needle).length > 1)

run_cmd do
  Regula.Filesystem.withOwnTempDir fun base => do
    let repo := base / "repo"
    let package := repo / RegulaProvision.mathlibPackage
    let manifest := package / "lake-manifest.json"
    let overrides := package / ".lake" / "package-overrides.json"
    IO.FS.createDirAll (package / ".lake")
    let (first, second, third, fourth, fifth) :=
      ("1111111111111111111111111111111111111111", "2222222222222222222222222222222222222222",
        "3333333333333333333333333333333333333333", "4444444444444444444444444444444444444444",
        "5555555555555555555555555555555555555555")
    let (url, otherUrl) := ("https://example.invalid/mathlib4", "https://example.invalid/fork")
    let committed := [pathEntry "regula" "../..", gitEntry "mathlib" url first,
      gitEntry "batteries" "https://example.invalid/batteries" second]
    -- The positive control, run first and after each mutation is undone.
    let positive (label : String) : IO Unit := do
      let pins ← pinsOf label repo
      requireSelection label "another packages directory" (pins.packagesDir == ".lake/packages")
      requireSelection label "another Mathlib" (pins.mathlibUrl == url && pins.mathlibRev == first)
      requireSelection label s!"other pins {pinned pins}"
        (pinned pins == #[("mathlib", first), ("batteries", second)])
      requireSelection label "another checkout commit"
        ((RegulaProvision.checkoutPin pins.git "mathlib").map (·.rev) == some first)
      requireSelection label "another revision"
        ((← RegulaProvision.manifestRevision repo RegulaProvision.mathlibPackage.toString
          `mathlib) == first)
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
    positive "positive"
    -- A second `mathlib` entry: Lake takes the last entry of a name.
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages"))
      (committed ++ [gitEntry "mathlib" otherUrl third]))
    let label := "duplicate mathlib entry"
    let pins ← pinsOf label repo
    requireSelection label "not the last entry's Mathlib"
      (pins.mathlibUrl == otherUrl && pins.mathlibRev == third)
    requireSelection label s!"other pins {pinned pins}"
      (pinned pins == #[("mathlib", third), ("batteries", second)])
    requireSelection label "not the last entry's checkout commit"
      ((RegulaProvision.checkoutPin pins.git "mathlib").map (·.rev) == some third)
    requireSelection label "not the last entry's revision"
      ((← RegulaProvision.manifestRevision repo RegulaProvision.mathlibPackage.toString
        `mathlib) == third)
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
    positive "positive after the duplicate entry"
    -- An overrides file: Lake takes its entries after the manifest's.
    IO.FS.writeFile overrides (overridesText [gitEntry "mathlib" otherUrl fourth,
      gitEntry "batteries" "https://example.invalid/batteries" fifth])
    let label := "overrides file"
    let pins ← pinsOf label repo
    requireSelection label "not the override's Mathlib"
      (pins.mathlibUrl == otherUrl && pins.mathlibRev == fourth)
    requireSelection label s!"other pins {pinned pins}"
      (pinned pins == #[("mathlib", fourth), ("batteries", fifth)])
    requireSelection label "not the override's checkout commit"
      ((RegulaProvision.checkoutPin pins.git "batteries").map (·.rev) == some fifth)
    IO.FS.writeFile overrides (overridesText [pathEntry "mathlib" "../vendored"])
    let label := "path override of mathlib"
    requireSelection label "a Mathlib is shared" (← RegulaProvision.readPins repo).isNone
    requireRefused label "materializes no Git package"
      (RegulaProvision.manifestRevision repo RegulaProvision.mathlibPackage.toString `mathlib)
    -- A path entry of a package that Mathlib requires: the shared workspace could not pin it.
    IO.FS.writeFile overrides (overridesText [pathEntry "batteries" "../batteries"])
    requireRefused "path override of batteries" "batteries: the package overrides file gives a path"
      (RegulaProvision.readPins repo)
    Regula.Filesystem.removeFound overrides
    positive "positive after the overrides file"
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages"))
      (committed ++ [pathEntry "batteries" "../batteries" (inherited := true)]))
    requireRefused "inherited path entry" "batteries: the manifest records a path entry"
      (RegulaProvision.readPins repo)
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
    positive "positive after the inherited path entry"
    -- A manifest that records no packages directory, or a null one: Lake would take the
    -- configuration's.
    for (label, recorded) in [("no packagesDir", none), ("null packagesDir", some none)] do
      IO.FS.writeFile manifest (manifestText recorded committed)
      requireRefused label "records no packagesDir" (RegulaProvision.readPins repo)
      IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
      positive s!"positive after {label}"
    -- No manifest: Lake would resolve the requirements anew.
    Regula.Filesystem.removeFound manifest
    requireRefused "absent manifest" "is absent" (RegulaProvision.readPins repo)
    IO.FS.writeFile manifest (manifestText (some (some ".lake/packages")) committed)
    positive "positive after the absent manifest"

end Regula.ProvisionControls
