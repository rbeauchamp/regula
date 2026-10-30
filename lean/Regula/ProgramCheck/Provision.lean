import RegulaProvision.Driver
import Regula.Filesystem

/-! # The reads of the provisioning driver

`scripts/provision.sh` runs the provisioning driver with `lean --run` before the package is built,
so it imports only the toolchain's libraries. This module proves the driver's own presence read,
which the driver defines because it cannot import `Regula.Filesystem`, equal to the filesystem
observer's (`isPresent_eq`). -/

/-- The presence read of the driver is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.Provision.isPresent_eq :
    RegulaProvision.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm
