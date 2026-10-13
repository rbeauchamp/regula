import RegulaVerification
import Regula.Contract
import Regula.Decision
import RegulaCore.Removal
import RegulaCore.Destination
import Regula.Destination

/-! # Decision contracts of the verification driver

The decision kind of each pure decision `RegulaVerification` registers with `@[regula_decision]`,
and the theorems that relate the driver's copy of the destination rules to `RegulaCore.Destination`.
The driver imports only the toolchain, because `scripts/verify.sh` runs it with `lean --run` before
the package is built. This second module of its library imports it together with the two checker
interfaces, the removal decision of the filesystem observer (`RegulaCore.Removal`) and the
identification of a document of Regula (`RegulaCore.Destination`), and nothing the driver runs
imports this module. Each kind restates theorems of the driver about the same definition and adds
the witnesses a kind requires. A control requires that the driver's reading of a destination
(`destinationAt`) and the programs' (`Regula.Destination.place`) refuse a path whose last component
names no file, and accept the same path with a file name. -/

namespace RegulaVerification

/-- `parseMode` accepts exactly the argument lists of the supported invocations
(`parseMode_sound`, `parseMode_roundtrip`): it accepts the empty list, which selects the first
acceptance step, and refuses an unsupported argument. -/
theorem checked_parseMode : Regula.ExecutableContract parseMode
    (Regula.Decides (·.isSome = true) (fun args => ∃ mode, args = arguments mode)) :=
  ⟨.of_roundtrip parseMode_roundtrip
    (fun args mode parsed => (parseMode_sound args mode parsed).symm) .ordinary
    (unwritten := ["unsupported"]) (by decide)⟩

/-- `dependencyFree` accepts only a lock manifest whose `packages` array is present and empty
(`dependencyFree_packages`), and it accepts the manifest with that one field. That it accepts
every such manifest is not claimed. -/
theorem checked_dependencyFree : Regula.ExecutableContract dependencyFree
    (Regula.DecidesSoundly (· = true)
      (fun manifest => manifest.getObjValAs? (Array Lean.Json) "packages" = .ok #[])) :=
  ⟨{ sound := dependencyFree_packages
     accepted := ⟨Lean.Json.mkObj [("packages", Lean.Json.arr #[])], by decide +kernel⟩ }⟩

/-- `select` accepts exactly the argument lists of the supported invocations, as `parseMode`
does (`select_exact`): it accepts the empty list and refuses an unsupported argument. Its result
type depends on the arguments, since the selected mode carries the proof that the arguments are
that mode's, so the decision is of whether a mode is selected (`Regula.Dependent.isSome`). -/
theorem checked_select : Regula.ExecutableContract select (fun selected =>
    Regula.Decides (· = true) (fun args => ∃ mode, args = arguments mode)
      (Regula.Dependent.isSome selected)) :=
  have isSome (args : List String) :
      Regula.Dependent.isSome select args = (parseMode args).isSome := by
    rw [Regula.Dependent.isSome, ← select_exact, Option.isSome_map]
  ⟨.of_iff (fun args => by rw [isSome]; exact checked_parseMode.evidence.iff args)
    ⟨[], by rw [isSome]; decide⟩ ⟨["unsupported"], by rw [isSome]; decide⟩⟩

/-- `passed` accepts exactly the ends in which every command ran to its end with exit status 0
(`passed_iff`). It accepts a step whose one command so ended, and refuses one whose command
ended with another status. The specification is stated with membership and equality alone; it
uses nothing `passed` is defined with. -/
theorem checked_passed : Regula.ExecutableContract passed
    (Regula.Decides (· = true)
      (fun ends : List (Option UInt32) => ∀ ended ∈ ends, ended = some 0)) :=
  ⟨.of_iff passed_iff ⟨[some 0], by decide⟩ ⟨[some 1], by decide⟩⟩

/-- `removal` decides to remove exactly when a directory is at the path and its real path is that
path (`removal_remove_iff`). It removes for a directory at its own place and does not remove when
nothing is there. With a symbolic link at the path the place is not a directory, so it does not
remove. -/
theorem checked_removal : Regula.ExecutableContract removal
    (Regula.Decides (· = .remove) (fun observed =>
      observed.place = .directory ∧ observed.sameLocation = true)) :=
  ⟨.of_iff removal_remove_iff ⟨⟨.directory, true⟩, rfl⟩ ⟨⟨.absent, false⟩, by decide⟩⟩

/-- The place of the filesystem observer's decision (`Regula.Removal.Place`) that a place of the
driver is. The driver does not tell a file or a symbolic link from another entry that is not a
directory, so its `other` is that decision's `other`; that decision refuses each of them for a
directory. -/
def Place.shared : Place → Regula.Removal.Place
  | .absent => .absent
  | .directory => .present .directory
  | .other => .other

/-- The result of the filesystem observer's decision (`Regula.Removal.Removal`) that a result of the
driver's decision is. -/
def Removal.shared : Removal → Regula.Removal.Removal
  | .nothing => .nothing
  | .remove => .remove
  | .refuse => .refuse

/-- The driver's decision is the decision of the filesystem observer for a directory,
`Regula.Removal.removal .directory`, on the same observation, whatever is observed of the parent of
the path, which that decision does not read for a directory. The driver cannot import that
decision, because `scripts/verify.sh` runs it with `lean --run` before the package is built, and
a program of the package cannot import the driver, because both declare `main`. So the
decision is written twice, and this theorem relates the two. -/
theorem removal_shared (observed : Observed) (parentOwn : Bool) :
    (removal observed).shared = Regula.Removal.removal .directory
      ⟨observed.place.shared, observed.sameLocation, parentOwn⟩ := by
  obtain ⟨place, sameLocation⟩ := observed
  cases place <;> cases sameLocation <;> cases parentOwn <;> decide

/-- `prebuildCovers` accepts exactly a surface manifest of the shape `claimedTargets` reads all of
whose claimed targets are targets of the prebuild (`prebuildCovers_iff`). It accepts a manifest
with no surface and refuses one with no `surfaces` field. That `claimedTargets` reads the claimed
targets as the checker's manifest reader does is not claimed. -/
theorem checked_prebuildCovers : Regula.ExecutableContract prebuildCovers
    (Regula.Decides (· = true) (fun manifest => ∃ targets,
      claimedTargets manifest = some targets ∧ ∀ target ∈ targets, target ∈ gateTargets)) :=
  ⟨.of_iff prebuildCovers_iff
    ⟨Lean.Json.mkObj [("surfaces", Lean.Json.arr #[])], by decide +kernel⟩
    ⟨Lean.Json.null, by decide +kernel⟩⟩

/-- The driver identifies a document of Regula (`regulaDocument`) exactly as the package's
programs do (`Regula.Destination.regulaDocument`), for every JSON value. The driver cannot import
that identification, because `scripts/verify.sh` runs it with `lean --run` before the package is
built, so it is written twice, and this theorem relates the two. -/
theorem regulaDocument_shared (value : Lean.Json) :
    regulaDocument value = Regula.Destination.regulaDocument value :=
  rfl

/-- The driver reads the names below the longest present prefix of a destination (`plainNames`)
exactly as the package's programs do (`Regula.Destination.plainNames`), for every list of names. -/
theorem plainNames_shared (names : List String) :
    plainNames names = Regula.Destination.plainNames names :=
  rfl

/-- The driver identifies the `build.json` of a site artifact (`identifiesSiteBuild`) exactly as
the site's build does (`Regula.Destination.identifiesSiteBuild`), for every JSON value. -/
theorem identifiesSiteBuild_shared (value : Lean.Json) :
    identifiesSiteBuild value = Regula.Destination.identifiesSiteBuild value :=
  rfl

/-- The driver reads the marker of an assembly of the site at the name that the site's build
writes it at (`Regula.Destination.siteAssemblingMarker`). -/
theorem siteAssemblingMarker_shared :
    siteAssemblingMarker = Regula.Destination.siteAssemblingMarker :=
  rfl

-- A destination whose last component names no file, `new/` or `new/.`, names a directory and not
-- a file in it: the driver and the programs refuse it by its name, before they drop a `.` or an
-- empty name. The same destination with a file name is accepted, at the real path of its prefix.
run_cmd do
  let base ← Regula.Filesystem.ownTempDir
  let outcome ← (do
    for named in [s!"{base / "new"}/", s!"{base / "new"}/."].map System.FilePath.mk do
      let place ← Regula.Destination.place named
      let driver ← (destinationAt named).toBaseIO
      unless (match place with | .error reason => reason.endsWith "names no file, so the run \
          writes nothing there" | .ok _ => false) &&
          (match driver with | .error error => (toString error).endsWith "names no file, so \
            the run writes nothing there" | .ok _ => false) do
        throw <| IO.userError s!"{named} is not refused by its name"
    let named : System.FilePath := base / "new" / "file.json"
    let expected := (← IO.FS.realPath base) / "new" / "file.json"
    let place ← Regula.Destination.place named
    let driver ← destinationAt named
    unless (place.toOption.map Regula.Destination.entryPath) == some expected &&
        driver == expected do
      throw <| IO.userError s!"{named} is not accepted at {expected}"
    ).toBaseIO
  Regula.Filesystem.removeOwn .directory base
  match outcome with
  | .ok () => pure ()
  | .error error => throwError "the control of a destination that names no file failed: {error}"

attribute [regula_decision] parseMode dependencyFree select passed removal prebuildCovers

end RegulaVerification
