import RegulaVerification
import Regula.Removal
import Regula.Destination

/-! # The removal and write check of the verification driver

`scripts/verify.sh` runs the verification driver with `lean --run` before the package is built, so
it imports only the toolchain's libraries: it cannot import the filesystem observer, and it does
not run the check itself. This module imports it, and its build fails when the compiled code of
the driver reaches a removal outside the observer, or a write of a file or a directory, except the
calls that the check admits in every program (`Regula.Removal.sharedPairs`) and the driver's own
calls that it names. It names each as the pair of the declaration of a source that makes it and
the primitive that it calls (`Regula.Removal.checkProgram`):

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
- the move of the copy's build output to an absent path in `RegulaVerification.Copy.adopt`, and
  the write of the accepted record (`RegulaVerification.acceptedRecord`) beside the pending record
  and its move over it in `RegulaVerification.Copy.record`, a record that a later run replaces at
  the acceptance link (`RegulaVerification.ownershipDecision_accepted`);
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
before the first acceptance step (`RegulaVerification.dependencyFree`). `dependencyFree_effective`
proves that a read that the driver accepts has no entry for any name. A control below runs that
read and check on files that Lake's own encoder writes. -/

run_cmd Regula.Removal.checkProgram (named := [
  (``RegulaVerification.removeDecided, ``IO.FS.removeDirAll),
  (``RegulaVerification.removeOwn, ``IO.FS.removeDirAll),
  (``RegulaVerification.reclaim, ``IO.FS.removeDirAll),
  (``RegulaVerification.reclaim, ``IO.FS.removeFile),
  (``RegulaVerification.Copy.remove, ``IO.FS.removeFile),
  (``RegulaVerification.copyTree, ``IO.FS.Handle.mk),
  (``RegulaVerification.copyTree, ``IO.FS.removeFile),
  (``RegulaVerification.Copy.adopt, ``IO.FS.rename),
  (``RegulaVerification.Copy.record, ``IO.FS.writeFile),
  (``RegulaVerification.Copy.record, ``IO.FS.rename),
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

/-- A read that `dependencyFree` accepts is a manifest and the entries of an overrides file among
which no entry has any name: Lake materializes no package from it. -/
theorem dependencyFree_effective
    {read : Option (_root_.Lake.Manifest × Array _root_.Lake.PackageEntry)}
    (h : RegulaVerification.dependencyFree read = true) :
    ∃ manifest overrides, read = some (manifest, overrides) ∧
      ∀ name, (manifest.packages ++ overrides).findRev? (·.name == name) = none := by
  obtain ⟨manifest, rfl, hPackages⟩ := (RegulaVerification.dependencyFree_iff read).mp h
  exact ⟨manifest, #[], rfl, fun name => by simp [hPackages]⟩

end Regula.ProgramCheck.Verification
