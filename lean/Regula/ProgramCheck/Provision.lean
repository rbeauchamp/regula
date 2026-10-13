import RegulaProvision
import Regula.Removal
import Regula.Filesystem

/-! # The removal check of the provisioning driver

`scripts/provision.sh` runs the provisioning driver with `lean --run` before the package is built,
so it imports only Lean's library: it cannot import the filesystem observer, and it does not run
the check itself. This module imports it, and its build fails when the compiled code of the driver
reaches a removal outside the observer, except the driver's own removals that it names, each as
the pair of the declaration that makes it and the primitive that it calls
(`Regula.Removal.checkProgram`). Each of them decides by the driver's own reads, which follow no
link at the path (`RegulaProvision.observe`, `RegulaProvision.kind?`,
`RegulaProvision.entryKindWith`), and no decision of `RegulaCore.Removal` decides them:

- the removal of a symbolic link or of a directory that `observe` classified, in
  `removeObserved`;
- the removal of a shared directory, which may be read-only, in `removeReadOnly` and
  `removeShared`, and of the entries of a shared directory in the loop of `removeShared`;
- the move of the link that `installLinkWith` made over the path, in `moveLink`; the removal of
  that link when the move failed, in `removeLink`; and the removal of the directory that
  `installLinkWith` made the link in, which `rmdir(2)` removes only when it is empty, in
  `removeStage`;
- the removal of a staged clone that an installation did not move, and the move of the staged
  clone over the path, in `installClone`;
- the removal in `runConstruction` of the constructor wrapper this run created exclusively before
  interpreting it, in the destination's privately owned staging parent;
- the move of a staged shared directory to its place, in `create`, and of a staged registry over
  the registry, in `writeRegistry`;
- the removal of a retired link of a copy and of a registry, and the move of a shared directory
  before its removal, in the loops of `prune`.

Issue 389 asks for a decision of each of these removals that a theorem relates to
`RegulaCore.Removal`.

It also proves the driver's own presence read, which the driver defines because it cannot import
`Regula.Filesystem`, equal to the filesystem observer's (`isPresent_eq`). -/

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
  (provisioning `moveLink, ``IO.FS.rename),
  (provisioning `removeLink, ``IO.FS.removeFile),
  (provisioning `removeStage, ``IO.FS.removeDir),
  (provisioning `installClone, ``IO.FS.rename),
  (provisioning `installClone, ``IO.FS.removeDirAll),
  (provisioning `runConstruction, ``IO.FS.removeFile),
  (provisioning `create, ``IO.FS.removeFile),
  (provisioning `create, ``IO.FS.rename),
  (provisioning `writeRegistry, ``IO.FS.rename),
  (specialized `Array.mapMUnsafe.map `prune `spec_0, ``IO.FS.removeFile),
  (specialized `Array.forIn'Unsafe.loop `prune `spec_2._lam_0, ``IO.FS.removeFile),
  (specialized `Array.forIn'Unsafe.loop `prune `spec_2._lam_0, ``IO.FS.rename)])

/-- The presence read of the driver is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.Provision.isPresent_eq :
    RegulaProvision.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm
