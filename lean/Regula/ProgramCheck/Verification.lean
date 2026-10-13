import RegulaVerification
import Regula.Removal

/-! # The observer reach check of the verification driver

`scripts/verify.sh` runs the verification driver with `lean --run` before the package is built, so
it imports only the toolchain: it cannot import the observers, and it does not run the check
itself. This module imports it, and its build fails when the compiled code of the driver reaches a
primitive that the check refuses (`Regula.Removal.checkProgram`). It admits the bootstrap pairs of
the driver's process source (`Regula.Removal.bootstrap`) and the driver's own removals that it
names, each as the pair of the declaration that makes it and the primitive that it calls:

- the removals of a directory, in `RegulaVerification.removeOwn` and in the loop of
  `RegulaVerification.reclaim`, each of which `RegulaVerification.removal` decides, the decision
  that `RegulaVerification.removal_shared` relates to `Regula.Removal.removal`;
- the removals of the ownership marker of a scratch directory, a regular file by a read that
  follows no link, in the loop of `RegulaVerification.reclaim` and in
  `RegulaVerification.Copy.remove`;
- the moves of the copy's build output to an absent path in `RegulaVerification.Copy.adopt`, of
  the pending acceptance record with its `build` field over the pending record in
  `RegulaVerification.Copy.recordBuild`, and of the pending record over the record in the body of
  the `try` of `RegulaVerification.run`, which the compiler makes the declaration
  `RegulaVerification.run._lam_0`; no decision of `RegulaCore.Removal` decides them.

Issue 389 asks for a decision of each of these removals that a theorem relates to
`RegulaCore.Removal`. -/

namespace Regula.ProgramCheck.Verification

open Lean in
/-- The loop over an array, specialized at the reclamation of scratch directories. -/
def reclaimLoop : Name :=
  mkPrivateNameCore `Init.Data.Array.Basic `Array.forIn'Unsafe.loop ++ `_at_ ++
    `RegulaVerification.reclaim.spec_0

end Regula.ProgramCheck.Verification

open Regula.ProgramCheck.Verification in
run_cmd Regula.Removal.checkProgram (named :=
  Regula.Removal.bootstrap `RegulaVerification.Process ++ [
  (`RegulaVerification.removeOwn, ``IO.FS.removeDirAll),
  (reclaimLoop, ``IO.FS.removeDirAll),
  (reclaimLoop, ``IO.FS.removeFile),
  (`RegulaVerification.Copy.remove, ``IO.FS.removeFile),
  (`RegulaVerification.Copy.adopt, ``IO.FS.rename),
  (`RegulaVerification.Copy.recordBuild, ``IO.FS.rename),
  (`RegulaVerification.run._lam_0, ``IO.FS.rename)])
