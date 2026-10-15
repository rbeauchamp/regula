import RegulaProvision
import Regula.Removal
import Regula.Filesystem
import Regula.Checker.LakeSelection

/-! # The removal and write check of the provisioning driver, and its Lake selection

`scripts/provision.sh` runs the provisioning driver with `lean --run` before the package is built,
so it imports only the toolchain's libraries: it cannot import the filesystem observer, and it
does not run the check itself. This module imports it, and its build fails when the compiled code
of the driver reaches a removal outside the observer, or a write outside the places that
`Regula.Removal.sharedPairs` lists, except the driver's own calls that it names, each as the pair
of the declaration of a source that makes it and the primitive that it calls
(`Regula.Removal.checkProgram`). Each of its removals decides by the driver's own reads, which
follow no link at the path (`RegulaProvision.observe`, `RegulaProvision.kind?`,
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

Its writes are below the directories that it provisions: the directory in which a link is made, in
`makeStage`; the wrapper of the shared constructor, in `runConstruction`; the constructor's
instructions and the receipt of the staged shared directory, in `create`; the staged registry, in
`writeRegistry`; the packages directory of a copy, in `packagesPath`; and the directory of the
shared packages and its lock, in `provision`. The constructor that `runConstruction` interprets in
a child process writes the entries of the staged directory, and `makeLink` makes a link with
`ln -s`; this check of the driver's compiled code reaches neither.

Issue 389 asks for a decision of each of these removals that a theorem relates to
`RegulaCore.Removal`.

It also proves the driver's own presence read, which the driver defines because it cannot import
`Regula.Filesystem`, equal to the filesystem observer's (`isPresent_eq`). For the same reason the
driver restates Lake's selection of the packages that the Mathlib integration package pins
(`RegulaProvision.selectPins`); the theorems at the end prove its read of the manifest and the
package overrides file the checker's (`rootFiles_eq`, `readRoot_eq`), its choice of an entry
`Regula.Checker.LakeSelection.effectiveEntry` (`selectedEntry_eq`), and its pins, packages
directory and checkout check those that this rule and `LakeSelection.packagesDir` give
(`packagesDir_eq`, `mathlib_effective`, `git_effective`, `checkoutPin_effective`). -/

namespace Regula.ProgramCheck.Provision

open Lean in
/-- The private declaration `name` of the provisioning driver. -/
def provisioning (name : Name) : Name :=
  mkPrivateNameCore `RegulaProvision (`RegulaProvision ++ name)

end Regula.ProgramCheck.Provision

open Regula.ProgramCheck.Provision in
run_cmd Regula.Removal.checkProgram (named := [
  (provisioning `removeObserved, ``IO.FS.removeFile),
  (provisioning `removeObserved, ``IO.FS.removeDirAll),
  (provisioning `removeReadOnly, ``IO.FS.removeDirAll),
  (provisioning `removeShared, ``IO.FS.removeFile),
  (provisioning `removeShared, ``IO.FS.removeDir),
  (provisioning `removeShared, ``IO.FS.removeDirAll),
  (provisioning `moveLink, ``IO.FS.rename),
  (provisioning `removeLink, ``IO.FS.removeFile),
  (provisioning `removeStage, ``IO.FS.removeDir),
  (provisioning `makeStage, ``IO.FS.createDir),
  (provisioning `installClone, ``IO.FS.rename),
  (provisioning `installClone, ``IO.FS.removeDirAll),
  (provisioning `runConstruction, ``IO.FS.removeFile),
  (provisioning `runConstruction, ``IO.FS.Handle.mk),
  (provisioning `create, ``IO.FS.removeFile),
  (provisioning `create, ``IO.FS.rename),
  (provisioning `create, ``IO.FS.Handle.mk),
  (provisioning `create, ``IO.FS.writeFile),
  (provisioning `writeRegistry, ``IO.FS.rename),
  (provisioning `writeRegistry, ``IO.FS.writeFile),
  (``RegulaProvision.prune, ``IO.FS.removeFile),
  (``RegulaProvision.prune, ``IO.FS.rename),
  (provisioning `packagesPath, ``IO.FS.createDirAll),
  (``RegulaProvision.provision, ``IO.FS.createDirAll),
  (``RegulaProvision.provision, ``IO.FS.Handle.mk)])

/-- The presence read of the driver is the filesystem observer's (`Regula.Filesystem.isPresent`,
whose match form `Regula.Filesystem.isPresent_eq_match` states). -/
theorem Regula.ProgramCheck.Provision.isPresent_eq :
    RegulaProvision.isPresent = Regula.Filesystem.isPresent :=
  Regula.Filesystem.isPresent_eq_match.symm

namespace Regula.ProgramCheck.Provision

open System Regula.Checker RegulaProvision

/-- The driver reads the manifest and package overrides file that the checker reads for a
workspace's root (`Workspace.rootFiles`), which `LakeSelection.ownRootFiles_lake` relates to the
files that Lake's load reads. -/
theorem rootFiles_eq : RegulaProvision.rootFiles = Workspace.rootFiles := rfl

/-- The driver's read of the manifest and the package overrides file is the checker's one read of
them (`Workspace.readRoot`). -/
theorem readRoot_eq : RegulaProvision.readRoot = Workspace.readRoot := rfl

/-- The checker's entries of a workspace (`Workspace.configRequests`) are those that the driver
selects among (`RegulaProvision.rootEntries`), of the same read. -/
theorem configRequests_eq (files : FilePath × FilePath) :
    Workspace.configRequests files = (do
      let some (manifest, overrides) ← RegulaProvision.readRoot files | return none
      return some (rootEntries manifest overrides)) := rfl

/-- The driver's entry for a name is the checker's (`LakeSelection.effectiveEntry`): the entry that
Lake materializes the package of that name from. -/
theorem selectedEntry_eq : selectedEntry = LakeSelection.effectiveEntry := rfl

/-- The packages directory of the pins that the driver admits is the one that Lake materializes the
Git entries in (`LakeSelection.packagesDir`), whatever packages directory the root configuration
gives. -/
theorem packagesDir_eq {manifest : _root_.Lake.Manifest}
    {overrides : Array _root_.Lake.PackageEntry} {ownRegula : Bool} {pins : Pins}
    (h : selectPins manifest overrides ownRegula = .ok (some pins)) (relPkgsDir : FilePath) :
    LakeSelection.packagesDir manifest.packagesDir? relPkgsDir = pins.packagesDir := by
  rw [(selectPins_sound h).1]
  rfl

/-- The Mathlib source and commit of the pins that the driver admits are those of the entry that
Lake materializes `mathlib` from (`LakeSelection.effectiveEntry`, `LakeSelection.gitPin`). -/
theorem mathlib_effective {manifest : _root_.Lake.Manifest}
    {overrides : Array _root_.Lake.PackageEntry} {ownRegula : Bool} {pins : Pins}
    (h : selectPins manifest overrides ownRegula = .ok (some pins)) :
    ∃ entry,
      LakeSelection.effectiveEntry (rootEntries manifest overrides) `mathlib = some entry ∧
        LakeSelection.gitPin entry = some (pins.mathlibUrl, pins.mathlibRev) := by
  obtain ⟨-, ⟨entry, _, _, hEntry, hSrc⟩, -⟩ := selectPins_sound h
  exact ⟨entry, hEntry, by simp [LakeSelection.gitPin, hSrc]⟩

/-- Each Git pin of the pins that the driver admits is the entry that Lake materializes its package
from (`LakeSelection.effectiveEntry`), at the pin's commit, and the pin names its checkout
directory. Conversely, each Git entry that Lake materializes a package from is a pin. -/
theorem git_effective {manifest : _root_.Lake.Manifest}
    {overrides : Array _root_.Lake.PackageEntry} {ownRegula : Bool} {pins : Pins}
    (h : selectPins manifest overrides ownRegula = .ok (some pins)) :
    (∀ entry pin, (entry, pin) ∈ pins.git →
      LakeSelection.effectiveEntry (rootEntries manifest overrides) entry.name = some entry ∧
        pin.name = entry.dirName ∧ (LakeSelection.gitPin entry).map Prod.snd = some pin.rev) ∧
      ∀ entry url rev,
        LakeSelection.effectiveEntry (rootEntries manifest overrides) entry.name = some entry →
          LakeSelection.gitPin entry = some (url, rev) →
            (entry, ⟨entry.dirName, rev⟩) ∈ pins.git := by
  rw [(selectPins_sound h).2.2.1]
  refine ⟨fun entry pin hMem => ?_, fun entry url rev hEntry hPin => ?_⟩
  · obtain ⟨hEntry, hName, _, _, _, hSrc⟩ := mem_gitPins hMem
    exact ⟨hEntry, hName, by simp [LakeSelection.gitPin, hSrc]⟩
  · simp only [LakeSelection.gitPin] at hPin
    split at hPin
    · next url' rev' inputRev subDir hSrc =>
      cases hPin
      exact gitPins_complete hEntry hSrc
    · cases hPin

/-- The check of the shared checkouts takes, for a checkout directory, the pin of the entry that
Lake materializes into that directory below the packages directory (`LakeSelection.checkoutDir`),
at that entry's commit. -/
theorem checkoutPin_effective {manifest : _root_.Lake.Manifest}
    {overrides : Array _root_.Lake.PackageEntry} {ownRegula : Bool} {pins : Pins} {dir : String}
    {pin : Pin}
    (h : selectPins manifest overrides ownRegula = .ok (some pins))
    (hPin : checkoutPin pins.git dir = some pin) :
    ∃ entry,
      LakeSelection.effectiveEntry (rootEntries manifest overrides) entry.name = some entry ∧
        LakeSelection.checkoutDir pins.packagesDir entry =
          _root_.Lake.joinRelative pins.packagesDir dir ∧
        (LakeSelection.gitPin entry).map Prod.snd = some pin.rev := by
  rw [(selectPins_sound h).2.2.1] at hPin
  obtain ⟨entry, hEntry, hDir, -, _, _, _, hSrc⟩ := checkoutPin_gitPins hPin
  exact ⟨entry, hEntry, by simp [LakeSelection.checkoutDir, hSrc, hDir],
    by simp [LakeSelection.gitPin, hSrc]⟩

end Regula.ProgramCheck.Provision
