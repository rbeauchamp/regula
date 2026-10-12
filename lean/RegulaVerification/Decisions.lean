import RegulaVerification
import Regula.Contract
import Regula.Decision
import RegulaCore.Removal

/-! # Decision contracts of the verification driver

The decision kind of each pure decision `RegulaVerification` runs, with its
`@[regula_decision]` registration. The driver imports only the toolchain, because
`scripts/verify.sh` runs it with `lean --run` before the package is built. This second module of
its library imports it together with the two checker interfaces and the removal decision of the
site executable (`RegulaCore.Removal`), and nothing the driver runs imports this module. Each
kind restates theorems of the driver about the same definition and adds the witnesses a kind
requires. -/
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

/-- `walked` accepts exactly the paths below the project root that the copy of the first
acceptance step holds (`walked_iff`): the path does not start with `tmp`, and none of its
components is a name that an isolated copy of a project leaves out. It accepts `lean` and
refuses `tmp`. That this is the rule of the checker's isolated copy is not claimed. -/
theorem checked_walked : Regula.ExecutableContract walked
    (Regula.Decides (· = true) (fun relative => relative.head? ≠ some "tmp" ∧
      ∀ component ∈ relative, component ≠ ".git" ∧ component ≠ ".lake" ∧ component ≠ ".cache" ∧
        component ≠ ".regula-scratch")) :=
  ⟨.of_iff walked_iff ⟨["lean"], by decide⟩ ⟨["tmp"], by decide⟩⟩

/-- `removal` decides to remove exactly when a directory is at the path and its real path is that
path (`removal_remove_iff`). It removes for a directory at its own place and does not remove when
nothing is there. With a symbolic link at the path the place is not a directory, so it does not
remove. -/
theorem checked_removal : Regula.ExecutableContract removal
    (Regula.Decides (· = .remove) (fun observed =>
      observed.place = .directory ∧ observed.sameLocation = true)) :=
  ⟨.of_iff removal_remove_iff ⟨⟨.directory, true⟩, rfl⟩ ⟨⟨.absent, false⟩, by decide⟩⟩

/-- The place of the site executable's decision (`Regula.Removal.Place`) that a place of the
driver is. The driver does not tell a file or a symbolic link from another entry that is not a
directory, so its `other` is that decision's `other`; that decision refuses each of them for a
directory. -/
def Place.shared : Place → Regula.Removal.Place
  | .absent => .absent
  | .directory => .present .directory
  | .other => .other

/-- The result of the site executable's decision (`Regula.Removal.Removal`) that a result of the
driver's decision is. -/
def Removal.shared : Removal → Regula.Removal.Removal
  | .nothing => .nothing
  | .remove => .remove
  | .refuse => .refuse

/-- The driver's decision is the decision of the site executable for a directory,
`Regula.Removal.removal .directory`, on the same observation, whatever is observed of the parent of
the path, which that decision does not read for a directory. The driver cannot import that
decision, because `scripts/verify.sh` runs it with `lean --run` before the package is built, and
the site executable cannot import the driver, because both programs declare `main`. So the
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


/-! ## The walk of the copy -/

section Walk

variable {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]

/-- The driver's read of an entry, at the read of operations, is `Regula.Filesystem.entryType`. -/
theorem entryTypeWith_eq (ops : Regula.Filesystem.Ops m) :
    entryTypeWith ops.symlinkMetadata = Regula.Filesystem.entryType ops := rfl

/-- The driver's sort, at the read of operations, is `Regula.Filesystem.sortEntries`. -/
theorem sortEntriesWith_eq (ops : Regula.Filesystem.Ops m) :
    ∀ (entries : List IO.FS.DirEntry) (directories others : List System.FilePath),
      sortEntriesWith ops.symlinkMetadata entries directories others =
        Regula.Filesystem.sortEntries ops entries directories others
  | [], _, _ => by simp only [sortEntriesWith, Regula.Filesystem.sortEntries]
  | entry :: rest, directories, others => by
    simp only [sortEntriesWith, Regula.Filesystem.sortEntries, entryTypeWith_eq,
      sortEntriesWith_eq ops rest]
    congr 1

/-- The driver's listing, at the reads of operations, is `Regula.Filesystem.otherEntriesIn`. -/
theorem otherEntriesInWith_eq (ops : Regula.Filesystem.Ops m) (root : System.FilePath) :
    ∀ (limit : Nat) (directories others : List System.FilePath),
      otherEntriesInWith ops.symlinkMetadata ops.readDir root limit directories others =
        Regula.Filesystem.otherEntriesIn ops root limit directories others
  | _, [], _ => by simp only [otherEntriesInWith, Regula.Filesystem.otherEntriesIn]
  | 0, _ :: _, _ => by simp only [otherEntriesInWith, Regula.Filesystem.otherEntriesIn]
  | limit + 1, directory :: rest, others => by
    simp only [otherEntriesInWith, Regula.Filesystem.otherEntriesIn, sortEntriesWith_eq,
      otherEntriesInWith_eq ops root limit]

/-- The driver's walk, at the reads of operations, is `Regula.Filesystem.otherEntries`. -/
theorem otherEntriesWith_eq (ops : Regula.Filesystem.Ops m) (limit : Nat)
    (root : System.FilePath) :
    otherEntriesWith ops.symlinkMetadata ops.readDir limit root =
      Regula.Filesystem.otherEntries ops limit root := by
  simp only [otherEntriesWith, Regula.Filesystem.otherEntries, entryTypeWith_eq,
    otherEntriesInWith_eq]
  congr 1

/-- The driver's check, at the reads of operations, is `Regula.Removal.requirePlacedWith`. -/
theorem requireLinksPlacedWith_eq (ops : Regula.Filesystem.Ops m) (limit : Nat)
    (root : System.FilePath) (placed : List System.FilePath) :
    requireLinksPlacedWith ops.symlinkMetadata ops.readDir limit root placed =
      Regula.Removal.requirePlacedWith ops limit root placed := by
  simp only [requireLinksPlacedWith, Regula.Removal.requirePlacedWith, otherEntriesWith_eq,
    Regula.Removal.linksPlaced]
  rfl

end Walk

/-- Operations whose two reads are the driver's: `System.FilePath.symlinkMetadata` and
`System.FilePath.readDir`, and `IO.FS.realPath`. The driver's walk uses no other, so the other
operations only fail. -/
def readsOnly : Regula.Filesystem.Ops IO where
  symlinkMetadata := System.FilePath.symlinkMetadata
  realPath := IO.FS.realPath
  removeDirAll := fun path => throw (IO.userError s!"{path}: the driver's walk removes nothing")
  removeFile := fun path => throw (IO.userError s!"{path}: the driver's walk removes nothing")
  rename := fun source _ => throw (IO.userError s!"{source}: the driver's walk moves nothing")
  readDir := System.FilePath.readDir

/-- `requireNoLinks` changes nothing, and when it succeeds from a world, no path of the listed tree
of the root at that world (`Regula.Filesystem.Model.Listed`) is a symbolic link or another kind of
entry than a directory and a file (`Regula.Filesystem.Model.NotPlain`), when the driver's reads
satisfy `ReadsEntry` and `ListsEntries` at the model of their runs: it is
`Regula.Removal.requirePlacedWith` at those reads (`requireLinksPlacedWith_eq`), and its contract
in `IO` (`Regula.Removal.requirePlacedWith_io`) gives the rest. -/
theorem requireNoLinks_io
    (entry : Void IO.RealWorld → System.FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → System.FilePath → Option System.FilePath)
    (ident : Void IO.RealWorld → System.FilePath → Option Regula.Filesystem.FileId)
    (names : Void IO.RealWorld → System.FilePath → List String)
    (reads : Regula.Filesystem.ReadsEntry (.ofIO readsOnly entry real ident names))
    (lists : Regula.Filesystem.ListsEntries (.ofIO readsOnly entry real ident names))
    (root : System.FilePath) (w : Void IO.RealWorld) :
    Regula.StateTriple.RunsTo id (requireNoLinks root w)
      (fun _ s => s = w ∧ ∀ path, (Regula.Filesystem.Model.ofIO readsOnly entry real ident
          names).Listed w root path →
        ¬ (Regula.Filesystem.Model.ofIO readsOnly entry real ident names).NotPlain w path)
      (fun _ s => s = w) := by
  have holds := Regula.Removal.requirePlacedWith_io
    (Regula.Filesystem.corresponds_ofIO readsOnly entry real ident names) reads lists
    maxDirectories root [] w
  rw [requireNoLinks, show requireLinksPlacedWith System.FilePath.symlinkMetadata
      System.FilePath.readDir maxDirectories root [] =
      requireLinksPlacedWith readsOnly.symlinkMetadata readsOnly.readDir maxDirectories root []
      from rfl, requireLinksPlacedWith_eq]
  revert holds
  cases Regula.Removal.requirePlacedWith readsOnly maxDirectories root [] w with
  | ok _ s => exact fun ⟨same, placed⟩ => ⟨same, fun path listed other =>
      nomatch placed path listed other⟩
  | error _ s => exact id
attribute [regula_decision] parseMode dependencyFree select passed walked removal prebuildCovers

end RegulaVerification
