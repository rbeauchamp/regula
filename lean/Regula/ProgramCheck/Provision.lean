import RegulaProvision.Driver
import RegulaProvision.Ownership
import Regula.Filesystem

/-! # The reads of the provisioning driver

`scripts/provision.sh` runs the provisioning driver with `lean --run` before the package is built,
so it imports only the toolchain's libraries. This module proves the driver's own presence read,
which the driver defines because it cannot import `Regula.Filesystem`, equal to the filesystem
observer's (`isPresent_eq`), and its read of a real path the observer's (`observeRealPath_eq`), so
that the pins it admits leave out only Regula's own integration entry at the observer's model, under
`Regula.Filesystem.ReadsReal` (`observer_admitted`). -/

/-- The presence read of the driver is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.Provision.isPresent_eq :
    RegulaProvision.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm

/-- The driver's read of a real path is the filesystem observer's
(`Regula.Filesystem.observeRealPath`). -/
theorem Regula.ProgramCheck.Provision.observeRealPath_eq :
    RegulaProvision.observeRealPath = Regula.Filesystem.observeRealPath :=
  rfl

open System Regula.StateTriple in
/-- When the driver's `pinsWith`, at its read of a real path, admits pins, each path entry that Lake
selects is the one for `regula`, and it is Regula's own integration entry in the world the run
starts from (`RegulaProvision.PathsOwn`), at the filesystem observer's model whose read of a real
path satisfies `Regula.Filesystem.ReadsReal` (`RegulaProvision.pinsWith_admitted_io`). -/
theorem Regula.ProgramCheck.Provision.observer_admitted
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option Regula.Filesystem.FileId)
    (readsReal : Regula.Filesystem.ReadsReal (Regula.Filesystem.observed entry real ident))
    (repo : FilePath) (manifest : Lake.Manifest) (overrides : Array Lake.PackageEntry)
    (w : Void IO.RealWorld) :
    RunsTo id (RegulaProvision.pinsWith RegulaProvision.observeRealPath repo manifest overrides w)
      (fun result after => after = w ∧ ∀ pins, result = .ok (some pins) →
        RegulaProvision.PathsOwn (Regula.Filesystem.observed entry real ident) w repo
          (RegulaProvision.rootEntries manifest overrides))
      (fun _ _ => False) :=
  RegulaProvision.pinsWith_admitted_io
    (fun _ => Regula.ProgramCheck.Provision.observeRealPath_eq ▸ Regula.Filesystem.ofEIO_agrees _)
    readsReal repo manifest overrides w

