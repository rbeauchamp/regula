import RegulaVerification
import Regula.Removal

/-! # The removal and write check of the verification driver

`scripts/verify.sh` runs the verification driver with `lean --run` before the package is built, so
it imports only Lean's library: it cannot import the filesystem observer, and it does not run the
check itself. This module imports it, and its build fails when the compiled code of the driver
reaches a removal outside the observer, or a write of a file or a directory
(`Regula.Removal.writePrimitives`), except the driver's own calls that it names, each as the pair
of the declaration that makes it and the primitive that it calls (`Regula.Removal.checkProgram`):

- the removals of a directory, in `RegulaVerification.removeOwn` and in the loop of
  `RegulaVerification.reclaim`, each of which `RegulaVerification.removal` decides, the decision
  that `RegulaVerification.removal_shared` relates to `Regula.Removal.removal`;
- the removals of the ownership marker of a scratch directory, a regular file by a read that
  follows no link, in the loop of `RegulaVerification.reclaim` and in
  `RegulaVerification.Copy.remove`;
- the removal of the cold constructor's wrapper in `RegulaVerification.copyTree`: this run
  created it exclusively in its private scratch directory before interpreting it;
- the moves of the copy's build output to an absent path in `RegulaVerification.Copy.adopt`, and
  of the pending acceptance record with its `build` field over the pending record in
  `RegulaVerification.Copy.recordBuild`, which writes that record first;
- the writes of the copy of the project below its scratch directory, in the loop of
  `RegulaVerification.copyTree`, and of the directory of the scratch area in
  `RegulaVerification.makeCopy`;
- the writes at a destination of the driver: the directory of the destination in
  `RegulaVerification.destinationAt`, the rename of a new file over the destination and the
  removal of that file when the write stops, in `RegulaVerification.writeDocument`, and the rename
  of the pending record over the acceptance link in `RegulaVerification.promote`. Each of these
  replaces only what `RegulaVerification.ownershipRefusal` admits, whose identification of a
  document of Regula `RegulaVerification.regulaDocument_shared` relates to
  `Regula.Destination.regulaDocument`.

So a new write or removal of the driver at another place, such as a direct `IO.FS.writeFile` at a
destination, fails this build. A write through another call of Lean's library, such as
`IO.FS.Handle.mk` with a mode that writes, which the driver's reads share, is not found. No decision
of `RegulaCore.Removal` decides the moves and the writes. Issue 389 asks for a decision of each of
the removals that a theorem relates to `RegulaCore.Removal`. -/

namespace Regula.ProgramCheck.Verification

open Lean in
/-- The loop over an array, specialized at the reclamation of scratch directories. -/
def reclaimLoop : Name :=
  mkPrivateNameCore `Init.Data.Array.Basic `Array.forIn'Unsafe.loop ++ `_at_ ++
    `RegulaVerification.reclaim.spec_0

open Lean in
/-- The loop over an array, specialized at the copy of the project's files. -/
def copyLoop : Name :=
  mkPrivateNameCore `Init.Data.Array.Basic `Array.forIn'Unsafe.loop ++ `_at_ ++
    `RegulaVerification.copyTree.spec_0

end Regula.ProgramCheck.Verification

open Regula.ProgramCheck.Verification in
run_cmd Regula.Removal.checkProgram
    (watched := Regula.Removal.primitives ++ Regula.Removal.writePrimitives) (named := [
  (`RegulaVerification.removeOwn, ``IO.FS.removeDirAll),
  (reclaimLoop, ``IO.FS.removeDirAll),
  (reclaimLoop, ``IO.FS.removeFile),
  (`RegulaVerification.Copy.remove, ``IO.FS.removeFile),
  (`RegulaVerification.copyTree, ``IO.FS.removeFile),
  (`RegulaVerification.Copy.adopt, ``IO.FS.rename),
  (`RegulaVerification.Copy.recordBuild, ``IO.FS.writeFile),
  (`RegulaVerification.Copy.recordBuild, ``IO.FS.rename),
  (`RegulaVerification.copyTree, ``IO.FS.createDirAll),
  (copyLoop, ``IO.FS.createDirAll),
  (copyLoop, ``IO.FS.writeBinFile),
  (`RegulaVerification.makeCopy, ``IO.FS.createDirAll),
  (`RegulaVerification.destinationAt, ``IO.FS.createDirAll),
  (`RegulaVerification.writeDocument, ``IO.FS.rename),
  (`RegulaVerification.writeDocument, ``IO.FS.removeFile),
  (`RegulaVerification.promote, ``IO.FS.rename)])
