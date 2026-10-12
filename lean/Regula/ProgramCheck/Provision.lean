import RegulaProvision
import Regula.Removal

/-! # The removal check of the provisioning driver

`scripts/provision.sh` runs the provisioning driver with `lean --run` before the package is built,
so it imports only Lean's library: it cannot import the filesystem observer, and it does not run
the check itself. This module imports it, and its build fails when the compiled code of the driver
reaches a removal outside the observer, except the driver's own removals that it names, each as
the pair of the declaration that makes it and the primitive that it calls
(`Regula.Removal.checkProgram`). Each of them decides by the driver's own reads, which follow no
link at the path (`RegulaProvision.observe`, `RegulaProvision.kind?`), and no decision of
`RegulaCore.Removal` decides them:

- the removal of a symbolic link or of a directory that `observe` classified, in
  `removeObserved`;
- the removal of a shared directory, which may be read-only, in `removeReadOnly` and
  `removeShared`, and of the entries of a shared directory in the loop of `removeShared`;
- the removal of a staged link or clone that an installation did not move, and the moves of the
  staged link or clone over the path, in `installLink` and `installClone`;
- the move of a staged shared directory to its place, in `create`, and of a staged registry over
  the registry, in `writeRegistry`;
- the removal of a retired link of a copy and of a registry, and the move of a shared directory
  before its removal, in the loops of `prune`.

Issue 389 asks for a decision of each of these removals that a theorem relates to
`RegulaCore.Removal`. -/

namespace Regula.ProgramCheck.Provision

open Lean in
/-- The private declaration `name` of the provisioning driver. -/
def provisioning (name : Name) : Name :=
  mkPrivateNameCore `RegulaProvision (`RegulaProvision ++ name)

open Lean in
/-- The array function `function` of Lean's library, specialized as `spec` in the declaration
`name` of the provisioning driver. -/
def specialized (function : Name) (name : Name) (spec : Name) : Name :=
  mkPrivateNameCore `Init.Data.Array.Basic function ++ `_at_ ++ provisioning name ++ spec

end Regula.ProgramCheck.Provision

open Regula.ProgramCheck.Provision in
run_cmd Regula.Removal.checkProgram (named := [
  (provisioning `removeObserved, ``IO.FS.removeFile),
  (provisioning `removeObserved, ``IO.FS.removeDirAll),
  (provisioning `removeReadOnly, ``IO.FS.removeDirAll),
  (provisioning `removeShared, ``IO.FS.removeFile),
  (provisioning `removeShared, ``IO.FS.removeDir),
  (specialized `Array.forIn'Unsafe.loop `removeShared `spec_0, ``IO.FS.removeFile),
  (specialized `Array.forIn'Unsafe.loop `removeShared `spec_0, ``IO.FS.removeDirAll),
  (provisioning `installLink, ``IO.FS.rename),
  (provisioning `installLink, ``IO.FS.removeFile),
  (provisioning `installClone, ``IO.FS.rename),
  (provisioning `installClone, ``IO.FS.removeDirAll),
  (provisioning `create, ``IO.FS.rename),
  (provisioning `writeRegistry, ``IO.FS.rename),
  (specialized `Array.mapMUnsafe.map `prune `spec_0, ``IO.FS.removeFile),
  (specialized `Array.forIn'Unsafe.loop `prune `spec_2, ``IO.FS.removeFile),
  (specialized `Array.forIn'Unsafe.loop `prune `spec_2._lam_0, ``IO.FS.rename)])
