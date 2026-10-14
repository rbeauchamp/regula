import RegulaVerification
import Regula.Removal
import Regula.Destination

/-! # The removal and write check of the verification driver

`scripts/verify.sh` runs the verification driver with `lean --run` before the package is built, so
it imports only Lean's library: it cannot import the filesystem observer, and it does not run the
check itself. This module imports it, and its build fails when the compiled code of the driver
reaches a removal outside the observer, or a write of a file or a directory, except the calls that
the check admits in every program (`Regula.Removal.sharedPairs`) and the driver's own calls that
it names. It names each as the pair of the declaration of a source that makes it and the primitive
that it calls (`Regula.Removal.checkProgram`):

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
`RegulaCore.Removal`. -/

run_cmd Regula.Removal.checkProgram (named := [
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
