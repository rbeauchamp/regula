import RegulaVerification
import Regula.Removal
import Regula.Destination
import Regula.Checker.LakeSelection

/-! # The observer reach check of the verification driver

`scripts/verify.sh` runs the verification driver with `lean --run` before the package is built, so
it imports only the toolchain's libraries: it cannot import the observers, and it does not run the
check itself. This module imports it, and its build fails when the compiled code of the driver
reaches a primitive that the check refuses (`Regula.Removal.checkProgram`): a removal outside the
filesystem observer, a write of a file or a directory, or a process start or environment read
outside the process observer. It admits the calls that the check admits in every program
(`Regula.Removal.sharedPairs`), the bootstrap pairs of the driver's process source
(`Regula.Removal.bootstrap`) and the driver's own calls that it names, each as the pair of the
declaration of a source that makes it and the primitive that it calls:

- the removals of a directory, in `RegulaVerification.removeDecided`, which takes the proof that
  `RegulaVerification.removal` decided the removal, the decision that
  `RegulaVerification.removal_shared` relates to `Regula.Removal.removal`, and where the compiler
  placed its body, in `RegulaVerification.removeOwn` and in the loop of
  `RegulaVerification.reclaim`;
- the removals of the ownership marker of a scratch directory, a regular file by a read that
  follows no link, in the loop of `RegulaVerification.reclaim` and in
  `RegulaVerification.Copy.remove`;
- the opening and the removal of the cold constructor's wrapper in `RegulaVerification.copyTree`:
  this run creates it exclusively in its private scratch directory before interpreting it, and
  the constructor writes the copy of the project in a child process, which this check of the
  driver's compiled code does not reach;
- the moves of the copy's build output to an absent path in `RegulaVerification.Copy.adopt`, and
  of the pending acceptance record with its `build` field over the pending record in
  `RegulaVerification.Copy.recordBuild`, which writes that record first;
- the writes of the scratch area in `RegulaVerification.makeCopy`: its directory, its lock, the
  ownership marker and the directory of a scratch directory, and the pending acceptance record;
- the writes at a destination of the driver: the directory of the destination, the new file beside
  it, the rename of that file over the destination and the removal of that file when the write
  stops, in `RegulaVerification.writeDocument`, and the directory of the acceptance link and the
  rename of the pending record over it in `RegulaVerification.promote`. Each of these replaces
  only what `RegulaVerification.ownershipRefusal` admits, at the entry that
  `RegulaVerification.destinationAt` finds before anything is made, whose identification of a
  document of Regula `RegulaVerification.regulaDocument_shared` relates to
  `Regula.Destination.regulaDocument`.

So a new write or removal of the driver at another place, such as a direct `IO.FS.writeFile` at a
destination or an opening of a file to write it, fails this build. So does a pair of this list
that admits no call of the driver. No decision of `RegulaCore.Removal` decides the moves and the
writes. Issue 389 asks for a decision of each of the removals that a theorem relates to
`RegulaCore.Removal`.

The driver reads the root package's manifest and package overrides file with Lake's own readers
before the first acceptance step (`RegulaVerification.dependencyFree`). `rootFiles_eq` and
`readRoot_eq` prove that read the checker's (`Regula.Checker.Workspace.readRoot`), and
`dependencyFree_effective` proves that Lake's selection (`Regula.Checker.LakeSelection`) takes no
entry for any name from a read that the driver accepts. A control below runs that read and check on
files that Lake's own encoder writes. -/

run_cmd Regula.Removal.checkProgram (bootstrap := `RegulaVerification.Process) (named := [
  (``RegulaVerification.removeDecided, ``IO.FS.removeDirAll),
  (``RegulaVerification.removeOwn, ``IO.FS.removeDirAll),
  (``RegulaVerification.reclaim, ``IO.FS.removeDirAll),
  (``RegulaVerification.reclaim, ``IO.FS.removeFile),
  (``RegulaVerification.Copy.remove, ``IO.FS.removeFile),
  (``RegulaVerification.copyTree, ``IO.FS.Handle.mk),
  (``RegulaVerification.copyTree, ``IO.FS.removeFile),
  (``RegulaVerification.Copy.adopt, ``IO.FS.rename),
  (``RegulaVerification.Copy.recordBuild, ``IO.FS.writeFile),
  (``RegulaVerification.Copy.recordBuild, ``IO.FS.rename),
  (``RegulaVerification.makeCopy, ``IO.FS.createDirAll),
  (``RegulaVerification.makeCopy, ``IO.FS.Handle.mk),
  (``RegulaVerification.makeCopy, ``IO.FS.createDir),
  (``RegulaVerification.writeDocument, ``IO.FS.createDirAll),
  (``RegulaVerification.writeDocument, ``IO.FS.Handle.mk),
  (``RegulaVerification.writeDocument, ``IO.FS.rename),
  (``RegulaVerification.writeDocument, ``IO.FS.removeFile),
  (``RegulaVerification.promote, ``IO.FS.createDirAll),
  (``RegulaVerification.promote, ``IO.FS.rename)])

-- A destination whose last component names no file, `new/` or `new/.`, names a directory and not
-- a file in it: the driver (`RegulaVerification.destinationAt`) and the programs
-- (`Regula.Destination.place`) refuse it by its name, before they drop a `.` or an empty name. The
-- same destination with a file name is accepted, at the real path of its prefix. The driver's
-- library is claimed and imports no module of the excluded `Regula` library, so this control is
-- here, and the first acceptance step builds this module.
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  let outcome ← (do
    for named in [s!"{base / "new"}/", s!"{base / "new"}/."].map System.FilePath.mk do
      let place ← Regula.Destination.place named
      let driver ← (RegulaVerification.destinationAt named).toBaseIO
      unless (match place with | .error reason => reason.endsWith "names no file, so the run \
          writes nothing there" | .ok _ => false) &&
          (match driver with | .error error => (toString error).endsWith "names no file, so \
            the run writes nothing there" | .ok _ => false) do
        throw <| IO.userError s!"{named} is not refused by its name"
    let named : System.FilePath := base / "new" / "file.json"
    let expected := (← IO.FS.realPath base) / "new" / "file.json"
    let place ← Regula.Destination.place named
    let driver ← RegulaVerification.destinationAt named
    unless (place.toOption.map Regula.Destination.entryPath) == some expected &&
        driver == expected do
      throw <| IO.userError s!"{named} is not accepted at {expected}"
    ).toBaseIO
  Regula.Filesystem.removeOwn .directory base
  match outcome with
  | .ok () => pure ()
  | .error error => throwError "the control of a destination that names no file failed: {error}"

-- A file that is not a document of Regula at the corpus receipt and at the acceptance link: the
-- driver's writer (`RegulaVerification.writeDocument`) and its promotion of the pending record
-- (`RegulaVerification.promote`) each refuse it and keep its bytes, and the promotion keeps the
-- record. A mark of Regula there is replaced by each. The checker self-test runs the driver's
-- begin-attempt, which writes the marks, against the same files (`driverCopyControl`).
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  let outcome ← (do
    let foreign := "# Notes\n\nNot a document of Regula.\n"
    let receipt := base / "tmp" / "rule-examples.json"
    let link := base / "tmp" / "acceptance-link.json"
    let record := base / "acceptance-link.pending.json"
    IO.FS.createDirAll (base / "tmp")
    IO.FS.writeFile receipt foreign
    IO.FS.writeFile link foreign
    IO.FS.writeFile record RegulaVerification.incompleteLink
    let refused (attempt : Except IO.Error Unit) : Bool := match attempt with
      | .error error => (toString error).contains "is a file that is not a JSON document"
      | .ok () => false
    let written ← (RegulaVerification.writeDocument receipt RegulaVerification.setupMark).toBaseIO
    let promoted ← (RegulaVerification.promote record link).toBaseIO
    unless refused written && refused promoted && (← IO.FS.readFile receipt) == foreign &&
        (← IO.FS.readFile link) == foreign && (← Regula.Filesystem.isPresent record) do
      throw <| IO.userError "the driver replaced, or did not refuse, a file that is not a \
        document of Regula"
    IO.FS.writeFile receipt RegulaVerification.incompleteLink
    IO.FS.writeFile link RegulaVerification.setupMark
    RegulaVerification.writeDocument receipt RegulaVerification.setupMark
    RegulaVerification.promote record link
    unless (← IO.FS.readFile receipt) == RegulaVerification.setupMark &&
        (← IO.FS.readFile link) == RegulaVerification.incompleteLink &&
        !(← Regula.Filesystem.isPresent record) do
      throw <| IO.userError "the driver did not replace a mark of Regula"
    ).toBaseIO
  Regula.Filesystem.removeOwn .directory base
  match outcome with
  | .ok () => pure ()
  | .error error => throwError "the control of the driver's writes at a file that is not a \
      document of Regula failed: {error}"

-- The first acceptance step's check that the root package requires nothing, over the driver's read
-- of a root's manifest and package overrides file: a manifest that records no package is accepted,
-- and again after each refused case is undone; an overrides file that records an entry, a manifest
-- that records a package and an absent manifest are refused.
run_cmd do
  let outcome ← (Regula.Filesystem.withOwnTempDir fun root => do
    let manifest := root / "lake-manifest.json"
    let overrides := root / ".lake" / "package-overrides.json"
    IO.FS.createDirAll (root / ".lake")
    let entry : _root_.Lake.PackageEntry :=
      { name := `batteries, inherited := false
        src := .git "https://example.invalid/batteries" "9999999999999999999999999999999999999999"
          none none }
    let lock (packages : Array _root_.Lake.PackageEntry) : _root_.Lake.Manifest :=
      { name := `regula, lakeDir := ".lake", fixedToolchain := false
        packagesDir? := some ".lake/packages", packages }
    let free : IO Bool := do
      return RegulaVerification.dependencyFree
        (← RegulaVerification.readRoot (RegulaVerification.rootFiles root))
    let require (what : String) (holds : Bool) : IO Unit :=
      unless holds do throw <| IO.userError what
    (lock #[]).save manifest
    require "refused a root that requires nothing" (← free)
    (lock #[entry]).save overrides
    require "accepted an overrides file that records an entry" !(← free)
    Regula.Filesystem.removeFound overrides
    require "refused a root that requires nothing, after the overrides file" (← free)
    (lock #[entry]).save manifest
    require "accepted a manifest that records a package" !(← free)
    Regula.Filesystem.removeFound manifest
    require "accepted an absent manifest" !(← free)
    (lock #[]).save manifest
    require "refused a root that requires nothing, after the absent manifest" (← free)).toBaseIO
  match outcome with
  | .ok () => pure ()
  | .error error => throwError "the control of the driver's dependency check failed: {error}"

namespace Regula.ProgramCheck.Verification
open Regula.Checker

/-- The driver's manifest and package overrides file of a root are the checker's. -/
theorem rootFiles_eq : RegulaVerification.rootFiles = Workspace.rootFiles := rfl

/-- The driver's read of those two files is the checker's: the same two reads by Lake's readers, in
the same order. -/
theorem readRoot_eq : RegulaVerification.readRoot = Workspace.readRoot := rfl

/-- A read that `dependencyFree` accepts is a manifest and the entries of an overrides file from
which Lake's selection takes no entry for any name: `LakeSelection.effectiveEntry` of the entries
that `LakeSelection.rootEntries` gives for that read is `none`. -/
theorem dependencyFree_effective
    {read : Option (_root_.Lake.Manifest × Array _root_.Lake.PackageEntry)}
    (h : RegulaVerification.dependencyFree read = true) :
    ∃ manifest overrides, read = some (manifest, overrides) ∧
      ∀ name, LakeSelection.effectiveEntry (manifest.packages ++ overrides) name = none := by
  obtain ⟨manifest, rfl, hPackages⟩ := (RegulaVerification.dependencyFree_iff read).mp h
  exact ⟨manifest, #[], rfl, fun name => by
    simp [hPackages, LakeSelection.effectiveEntry, LakeSelection.lastEntry]⟩

end Regula.ProgramCheck.Verification
