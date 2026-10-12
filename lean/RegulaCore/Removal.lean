import Regula.Contract
import Regula.Decision
import RegulaCore.Filesystem

/-! # Removal of an entry at its own place, and the move of a file

The decisions by which Regula removes a directory, a file or a symbolic link (`removal`) and moves
a file over another (`replacement`), and the operations that observe a place, decide and act,
written once for the filesystem's operations in any monad (`Regula.Filesystem.Ops`). Regula runs
them at the observer (`Regula.Filesystem`), and no other code of Regula calls a removal primitive
(`Regula.Removal.rawRemovals`).

`IO.FS.removeDirAll` reads the entries of the path it is given, also when that path is a symbolic
link to a directory, and then removes the entries of the link's target. A removal that first asks
`System.FilePath.pathExists` or `System.FilePath.isDir`, which follow a link, can therefore remove
the content of a directory outside the place it names. The decision takes an observation that
follows no link at the place (`Place`) and the comparison of the place's real path with the place
itself, and it removes only the kind of entry the caller removes, found at its own place
(`removal_remove_iff`). A symbolic link is at its own place when it is a name in a directory at its
own place (`Regula.Filesystem.Model.InOwnDirectory`): its real path is the file that it points to,
and `IO.FS.removeFile` removes the link, not that file.

## The operations

`observe` reads the real path of a place and of its parent, and then its entry. `removeOwnWith` acts
on what `removal` decides for that observation: it does nothing when nothing is there, runs the
checked removal of `Regula.Filesystem` when an entry of the kind is there at its own place, and
refuses otherwise. `removeFoundWith` removes a directory or a file, whichever is there.
`replaceWith` moves a file at its own place to a destination where nothing is, or a file is at its
own place, in a directory at its own place (`replacement_iff`), and reads both paths again after
the move. `requirePlacedWith` lists the tree below a directory (`Regula.Filesystem.otherEntries`)
and stops unless each symbolic link or other kind of entry than a directory and a file that it
finds is one that the program placed there (`linksPlaced_iff`, `requirePlacedWith_run`), under
`ReadsEntry` and `ListsEntries`.

Their contracts are of two strengths. What a successful run leaves at the path rests only on
`ReadsEntry`, since each operation reads the path again before it succeeds (`removeOwnWith_gone`,
`removeFoundWith_gone`, `replaceWith_moved`): these are checked operations. That a run changes
nothing unless the decision held, and that it keeps the entries outside the removed or moved paths
(`Regula.Filesystem.Model.Kept`), rests on the assumptions that each theorem names
(`removeOwnWith_spec`, `removeFoundWith_spec`, `replaceWith_spec`).

The verification driver decides its own removals with `RegulaVerification.removal`, which it
cannot import from here: `scripts/verify.sh` runs it with `lean --run` before any module of the
package is built. `RegulaVerification.Decisions` proves that the driver's decision agrees with
this one for a directory.

**Outside these operations:** a process that changes a place between its observation and the
removal or move, and a process that replaces an entry below a directory with a link while
`IO.FS.removeDirAll` removes it: that function examines each entry and then opens it by its path,
so such a process can make it remove the entries of a different directory. -/

namespace Regula.Removal

open System Std.Do Regula.StateTriple Regula.Filesystem

/-- The kind of entry a caller removes. -/
inductive Kind where
  /-- A directory, which is removed with all its entries. -/
  | directory
  /-- A file. -/
  | file
  /-- A symbolic link, which is removed and not the file that it points to. -/
  | link
  deriving DecidableEq, Repr

/-- What is at a path, observed without following a symbolic link at the path itself. -/
inductive Place where
  /-- Nothing is there. -/
  | absent
  /-- A directory, a regular file or a symbolic link is there. -/
  | present (kind : Kind)
  /-- Something else is there: an entry that is neither a directory, a regular file nor a symbolic
  link. -/
  | other
  deriving DecidableEq, Repr

/-- What was observed of a path before a removal of it. -/
structure Observed where
  /-- What is at the path. -/
  place : Place
  /-- Whether the real path of what is there is the path itself. -/
  sameLocation : Bool
  /-- Whether the last component of the path is a name, not `.` or `..`, and the parent of the path
  is its own real path. -/
  parentOwn : Bool
  deriving DecidableEq, Repr

/-- What is done about an entry that is to be removed. -/
inductive Removal where
  /-- Nothing is there: there is nothing to remove. -/
  | nothing
  /-- An entry of the kind is there, at its own place: it is removed. -/
  | remove
  /-- Something else is there: nothing is removed, and the caller stops. -/
  | refuse
  deriving DecidableEq, Repr

/-- Whether an entry of `kind` at the observed path is at its own place: a symbolic link when the
path is a name in a directory at its own place, since its own real path is the file that it points
to, and a directory or a file when its real path is the path. -/
def Observed.ownFor (observed : Observed) : Kind → Bool
  | .link => observed.parentOwn
  | .directory | .file => observed.sameLocation

/-- Remove only an entry of `kind` at its own place; there is nothing to remove when nothing is
there; refuse in every other case, which is each case with an entry of another kind at the path,
among them a symbolic link when the caller removes a directory or a file, and a path through a
symbolic link. -/
@[regula_decision]
def removal (kind : Kind) (observed : Observed) : Removal :=
  match observed.place with
  | .absent => .nothing
  | .present found => if found = kind ∧ observed.ownFor kind then .remove else .refuse
  | .other => .refuse

/-- The decision removes exactly when an entry of `kind` is at the path, by a read that follows
no link, and it is at its own place: a symbolic link is a name in a directory that is its own real
path, and a directory or a file has the path as its real path. -/
theorem removal_remove_iff (kind : Kind) (observed : Observed) :
    removal kind observed = .remove ↔
      observed.place = .present kind ∧
        (kind = .link ∧ observed.parentOwn = true ∨
          kind ≠ .link ∧ observed.sameLocation = true) := by
  obtain ⟨place, sameLocation, parentOwn⟩ := observed
  cases kind <;> rcases place with _ | (_ | _ | _) | _ <;> cases sameLocation <;>
    cases parentOwn <;> decide

/-- The decision has nothing to remove exactly when nothing is at the path. -/
theorem removal_nothing_iff (kind : Kind) (observed : Observed) :
    removal kind observed = .nothing ↔ observed.place = .absent := by
  obtain ⟨place, sameLocation, parentOwn⟩ := observed
  cases kind <;> rcases place with _ | (_ | _ | _) | _ <;> cases sameLocation <;>
    cases parentOwn <;> decide

/-- `removal` removes exactly an entry of the caller's kind at its own place
(`removal_remove_iff`). It removes a directory at its own place, and it does not remove a
directory when the caller removes a file. -/
theorem checked_removal : Regula.ExecutableContract removal (fun decide =>
    Regula.Decides (· = .remove)
      (fun input : Kind × Observed =>
        input.2.place = .present input.1 ∧
          (input.1 = .link ∧ input.2.parentOwn = true ∨
            input.1 ≠ .link ∧ input.2.sameLocation = true))
      (Function.uncurry decide)) :=
  ⟨.of_iff (fun input => removal_remove_iff input.1 input.2)
    ⟨(.directory, ⟨.present .directory, true, false⟩), rfl⟩
    ⟨(.file, ⟨.present .directory, true, true⟩), by decide⟩⟩

/-! ## The move of a file -/

/-- What was observed before a file is moved from one path to another. -/
structure Move where
  /-- What was observed of the path that the file is moved from. -/
  source : Observed
  /-- What was observed of the path that the file is moved to. -/
  destination : Observed
  deriving DecidableEq, Repr

/-- Move only a file at its own place, which `removal` would remove as a file, to a destination
that `removal` would not refuse as a file, so nothing is there or a file is there at its own
place, which is a name in a directory at its own place. A move over a file removes that file, so
the destination is decided as a removal of a file is; an absent destination is in a directory at
its own place, so the moved file does not reach a directory through a symbolic link. -/
@[regula_decision]
def replacement (move : Move) : Bool :=
  removal .file move.source == .remove && removal .file move.destination != .refuse &&
    move.destination.parentOwn

/-- The decision moves exactly a regular file at its own real path, to a path where nothing is, or
a regular file is at its own real path, which is a name in a directory that is its own real
path. -/
theorem replacement_iff (move : Move) :
    replacement move = true ↔
      (move.source.place = .present .file ∧ move.source.sameLocation = true) ∧
        (move.destination.place = .absent ∨
          move.destination.place = .present .file ∧ move.destination.sameLocation = true) ∧
        move.destination.parentOwn = true := by
  obtain ⟨⟨sourcePlace, sourceSame, sourceParent⟩,
    ⟨destinationPlace, destinationSame, destinationParent⟩⟩ := move
  rcases sourcePlace with _ | (_ | _ | _) | _ <;>
    rcases destinationPlace with _ | (_ | _ | _) | _ <;>
    cases sourceSame <;> cases sourceParent <;> cases destinationSame <;>
    cases destinationParent <;> decide

/-- `replacement` moves exactly a file at its own place to an absent path or a file at its own
place, which is a name in a directory at its own place (`replacement_iff`). It moves a file to an
absent path, and it does not move a directory. -/
theorem checked_replacement : Regula.ExecutableContract replacement (fun decide =>
    Regula.Decides (· = true)
      (fun move : Move =>
        (move.source.place = .present .file ∧ move.source.sameLocation = true) ∧
          (move.destination.place = .absent ∨
            move.destination.place = .present .file ∧ move.destination.sameLocation = true) ∧
          move.destination.parentOwn = true)
      decide) :=
  ⟨.of_iff replacement_iff
    ⟨⟨⟨.present .file, true, true⟩, ⟨.absent, false, true⟩⟩, by decide⟩
    ⟨⟨⟨.present .directory, true, true⟩, ⟨.absent, false, true⟩⟩, by decide⟩⟩

/-! ## The links below a directory that a program made

A program that makes a directory and runs Lake there, such as a copy of a project, may hold no
symbolic link or other entry than a directory and a file below it except those it placed itself
(`requirePlacedWith`): Lake follows such an entry when it removes below the directory. -/

/-- The paths below a directory that are symbolic links or other entries than directories and
files (`Regula.Filesystem.otherEntries`), and the paths of the links that the program placed
there. -/
structure TreeLinks where
  /-- The paths that a walk found. -/
  found : List FilePath
  /-- The paths of the links that the program placed. -/
  placed : List FilePath
  deriving DecidableEq, Repr

/-- Whether each path that the walk found is a link that the program placed. -/
@[regula_decision]
def linksPlaced (links : TreeLinks) : Bool :=
  links.found.all (· ∈ links.placed)

/-- The decision admits exactly the walks whose paths are among the placed ones. -/
theorem linksPlaced_iff (links : TreeLinks) :
    linksPlaced links = true ↔ links.found ⊆ links.placed := by
  simp [linksPlaced, List.subset_def]

/-- The decision contract of `linksPlaced`. -/
theorem checked_linksPlaced : Regula.ExecutableContract linksPlaced (fun decide =>
    Regula.Decides (· = true) (fun links : TreeLinks => links.found ⊆ links.placed) decide) :=
  ⟨.of_iff linksPlaced_iff
    ⟨⟨["/w/.lake/packages"], ["/w/.lake/packages"]⟩, by decide⟩
    ⟨⟨["/w/src/link"], ["/w/.lake/packages"]⟩, by decide⟩⟩

/-! ## A symbolic link that a program placed

A program that places a symbolic link in such a directory, as a copy of a project places the link
to the packages directory of the original, admits it only when a symbolic link is there and it
resolves to the target that the program meant (`requireLinkWith`). -/

/-- What reads find at the path of a symbolic link that a program placed, and at the target that it
meant: what is at the path by a read that follows no link there (`Place.ofType`), and the real paths
of the path, which follows the link, and of the target. A real path is `none` when `realpath(3)`
fails. -/
structure PlacedLink where
  /-- What is at the path of the link. -/
  place : Place
  /-- The real path of the path of the link. -/
  real : Option FilePath
  /-- The real path of the target that the program meant. -/
  target : Option FilePath
  deriving DecidableEq, Repr

/-- Whether a symbolic link is at the path and resolves to the real path of the target. -/
@[regula_decision]
def linkPlaced (link : PlacedLink) : Bool :=
  link.place == .present .link && link.real.isSome && link.real == link.target

/-- The decision admits exactly a symbolic link whose real path is the target's. -/
theorem linkPlaced_iff (link : PlacedLink) :
    linkPlaced link = true ↔
      link.place = .present .link ∧ ∃ real, link.real = some real ∧ link.target = some real := by
  rcases link with ⟨place, _ | real, target⟩
  · simp [linkPlaced]
  · simp only [linkPlaced, Bool.and_eq_true, beq_iff_eq, Option.isSome_some, and_true,
      Option.some.injEq, exists_eq_left']
    exact ⟨fun ⟨h, e⟩ => ⟨h, e.symm⟩, fun ⟨h, e⟩ => ⟨h, e.symm⟩⟩

/-- The decision contract of `linkPlaced`. -/
theorem checked_linkPlaced : Regula.ExecutableContract linkPlaced (fun decide =>
    Regula.Decides (· = true) (fun link : PlacedLink => link.place = .present .link ∧
      ∃ real, link.real = some real ∧ link.target = some real) decide) :=
  ⟨.of_iff linkPlaced_iff
    ⟨⟨.present .link, some "/o/.lake/packages", some "/o/.lake/packages"⟩, by decide⟩
    ⟨⟨.present .link, some "/outside", some "/o/.lake/packages"⟩, by decide⟩⟩

/-! ## Observation -/

/-- The name of the kind in a message. -/
def Kind.noun : Kind → String
  | .directory => "directory"
  | .file => "file"
  | .link => "symbolic link"

/-- The type, as `lstat(2)` reports it, of an entry of the kind. -/
def Kind.type : Kind → IO.FS.FileType
  | .directory => .dir
  | .file => .file
  | .link => .symlink

/-- The kind to remove at a path where `lstat(2)` reports `found`: a file when a regular file is
there, and a directory otherwise. When a symbolic link, something else or nothing is there,
`removal` decides the same for either kind. -/
def Kind.found : Option IO.FS.FileType → Kind
  | some .file => .file
  | _ => .directory

/-- What is at a path, from the type of its entry as `lstat(2)` reports it, or `none` when nothing
is there: a directory, a regular file and a symbolic link are present, and anything else is another
entry. -/
def Place.ofType : Option IO.FS.FileType → Place
  | none => .absent
  | some .dir => .present .directory
  | some .file => .present .file
  | some .symlink => .present .link
  | some .other => .other

/-- A place is absent exactly when nothing is there. -/
theorem Place.ofType_absent (found : Option IO.FS.FileType) :
    Place.ofType found = .absent ↔ found = none := by
  rcases found with _ | (_ | _ | _ | _) <;> simp [Place.ofType]

/-- An entry of a kind is present exactly when `lstat(2)` reports the type of that kind. -/
theorem Place.ofType_present (found : Option IO.FS.FileType) (kind : Kind) :
    Place.ofType found = .present kind ↔ found = some kind.type := by
  cases kind <;> rcases found with _ | (_ | _ | _ | _) <;> simp [Place.ofType, Kind.type]

variable {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m]

/-- Whether the last component of `path` is a name, not `.` or `..`, and its parent is at its own
place (`atOwnPlace`): `false` when `path` has no parent or ends in `.` or `..`. -/
def ownParent (ops : Ops m) (path : FilePath) : m Bool :=
  match path.parent, path.fileName with
  | some parent, some _ => atOwnPlace ops parent
  | _, _ => pure false

/-- What is observed of `path`: whether its real path is the path, whether it is a name in a
directory at its own place, and then what is there, by a read that follows no symbolic link at the
path. The entry is read last, so what the decision sees of it is what is there in the state in
which the decision is made (`observe_place`). -/
def observe (ops : Ops m) (path : FilePath) : m Observed := do
  let sameLocation ← atOwnPlace ops path
  let parentOwn ← ownParent ops path
  let found ← entryType ops path
  return { place := Place.ofType found, sameLocation, parentOwn }

/-! ## Removal and move -/

/-- The error of a removal that `removal` refused. -/
def refusal (kind : Kind) (path : FilePath) : IO.Error :=
  IO.userError s!"nothing was removed: {path} is not a {kind.noun} at its own place (a symbolic \
    link, an entry of another kind, or a path through a symbolic link is there)"

/-- Remove the entry of `kind` at `path` when one is there at its own place, do nothing when
nothing is there, and stop with nothing removed in every other case (`removal_remove_iff`). A
directory or file is at its own place when its real path is `path`, so a relative path, a `.` or
`..` component and a symbolic link at any component make it refuse. It removes with the checked
removals of `Regula.Filesystem`, which read the path again afterwards. -/
def removeOwnWith (ops : Ops m) (kind : Kind) (path : FilePath) : m Unit := do
  match removal kind (← observe ops path) with
  | .nothing => pure ()
  | .remove =>
    match kind with
    | .directory => removeDirectory ops path
    | .file | .link => removeEntry ops path
  | .refuse => throw (refusal kind path)

/-- Remove the directory or file at `path`, whichever is there, at its own place; do nothing when
nothing is there; and stop with nothing removed when a symbolic link, another kind of entry or a
path through a symbolic link is there (`Kind.found`, `removeOwnWith`). -/
def removeFoundWith (ops : Ops m) (path : FilePath) : m Unit := do
  removeOwnWith ops (Kind.found (← entryType ops path)) path

/-- The error of a move that `replacement` refused. -/
def moveRefusal (source destination : FilePath) : IO.Error :=
  IO.userError s!"nothing was moved: {source} is not a file at its own place, or {destination} is \
    neither a file at its own place nor an absent path in a directory at its own place"

/-- Read both paths again after a move, and fail unless nothing is at the source and a regular
file is at the destination. -/
def confirmMoved (ops : Ops m) (source destination : FilePath) : m Unit := do
  let left ← entryType ops source
  let arrived ← entryType ops destination
  match left, arrived with
  | none, some .file => pure ()
  | _, _ => throw (IO.userError s!"{source} was not moved to {destination}")

/-- Move the file at `source` to `destination` when `replacement` decides to (`replacement_iff`),
then read both paths again (`confirmMoved`); otherwise stop with nothing moved. -/
def replaceWith (ops : Ops m) (source destination : FilePath) : m Unit := do
  let observedSource ← observe ops source
  let observedDestination ← observe ops destination
  if replacement { source := observedSource, destination := observedDestination } then
    ops.rename source destination
    confirmMoved ops source destination
  else throw (moveRefusal source destination)

/-- Stop unless each path of the listed tree of `root` that is a symbolic link or another kind of
entry than a directory and a file (`otherEntries`), listing at most `limit` directories, is one of
`placed`, as `linksPlaced` decides (`requirePlacedWith_run`). -/
def requirePlacedWith (ops : Ops m) (limit : Nat) (root : FilePath) (placed : List FilePath) :
    m Unit := do
  let found ← otherEntries ops limit root
  unless linksPlaced { found, placed } do
    let stray := (found.find? fun path => !placed.contains path).getD root
    throw (IO.userError s!"{stray} is a symbolic link or another kind of entry than a directory \
      and a file below {root}, and not one of the links placed there: {placed}")

/-- Stop unless a symbolic link is at `link`, by a read that follows no link there, and its real
path is the real path of `target`, as `linkPlaced` decides (`requireLinkWith_run`). -/
def requireLinkWith (ops : Ops m) (link target : FilePath) : m Unit := do
  let found ← entryType ops link
  let real ← realOf ops link
  let targetReal ← realOf ops target
  unless linkPlaced { place := Place.ofType found, real, target := targetReal } do
    throw (IO.userError s!"{link} is not a symbolic link to {target}")

/-! ## Contracts in a model -/

/-- In `before`, the entry of `kind` at `path` is at its own place: a symbolic link is a name in a
directory at its own place (`Model.InOwnDirectory`), and a directory or a file has `path` as its
real path. -/
def OwnPlace (M : Model) (kind : Kind) (path : FilePath) (before : M.World) : Prop :=
  match kind with
  | .link => M.InOwnDirectory before path
  | .directory | .file => M.real before path = some path

/-- From `before` to `after`, the state changed only when an entry of `kind` was at `path`, at its
own place (`OwnPlace`), in `before`. -/
def OnlyOwn (M : Model) (kind : Kind) (path : FilePath) (before after : M.World) : Prop :=
  after = before ∨ (M.entry before path = some kind.type ∧ OwnPlace M kind path before)

/-- In `before`, a regular file is at `source` at its own place, and at `destination` nothing is
or a regular file is at its own place, and `destination` is a name in a directory at its own place
(`Model.InOwnDirectory`): what `replacement` decides on. -/
def Movable (M : Model) (source destination : FilePath) (before : M.World) : Prop :=
  (M.entry before source = some .file ∧ M.real before source = some source) ∧
    (M.entry before destination = none ∨
      M.entry before destination = some .file ∧ M.real before destination = some destination) ∧
    M.InOwnDirectory before destination

/-- A run of `observe` reports the place that `lstat(2)` reports in the state it ends in. -/
theorem observe_place (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
    Satisfies ((observe M.ops path).run before)
      (fun observed w => observed.place = Place.ofType (M.entry w path)) (fun _ _ => True) := by
  unfold observe
  refine Satisfies.bind (P := fun _ _ => True) ?_ fun _ w _ => ?_
  · cases (atOwnPlace M.ops path).run before <;> trivial
  refine Satisfies.bind (P := fun _ _ => True) ?_ fun _ w' _ => ?_
  · cases (ownParent M.ops path).run w <;> trivial
  refine Satisfies.bind ((entryType_run M reads path w').mono (fun _ _ h => h)
    (fun _ _ _ => trivial)) ?_
  rintro found w'' ⟨rfl, rfl⟩
  exact rfl

/-- A run of `ownParent` changes nothing and does not fail, and it gives `true` only when the path
is a name in a directory at its own place (`Model.InOwnDirectory`). -/
theorem ownParent_run (M : Model) (reads : ReadsReal M) (path : FilePath) (before : M.World) :
    Satisfies ((ownParent M.ops path).run before)
      (fun own w => w = before ∧ (own = true → M.InOwnDirectory before path))
      (fun _ _ => False) := by
  unfold ownParent
  cases parentOf : path.parent with
  | none => cases path.fileName <;> exact ⟨rfl, fun refused => nomatch refused⟩
  | some parent =>
    cases nameOf : path.fileName with
    | none => exact ⟨rfl, fun refused => nomatch refused⟩
    | some _ =>
      exact (atOwnPlace_run M reads parent before).mono
        (fun _ _ read => ⟨read.1, fun own => ⟨by rw [nameOf]; rfl, parent, parentOf,
          read.2.mp own⟩⟩)
        (fun _ _ impossible => impossible)

/-- A run of `observe` changes nothing and reports the place, whether its real path is the path,
and, when it reports so, that the path is a name in a directory at its own place. -/
theorem observe_run (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (path : FilePath) (before : M.World) :
    Satisfies ((observe M.ops path).run before)
      (fun observed w => w = before ∧ observed.place = Place.ofType (M.entry before path) ∧
        (observed.sameLocation = true ↔ M.real before path = some path) ∧
        (observed.parentOwn = true → M.InOwnDirectory before path))
      (fun _ w => w = before) := by
  unfold observe
  refine Satisfies.bind ((atOwnPlace_run M readsReal path before).mono (fun _ _ h => h)
    (fun _ _ h => h.elim)) ?_
  rintro same w ⟨rfl, same_iff⟩
  refine Satisfies.bind ((ownParent_run M readsReal path w).mono (fun _ _ h => h)
    (fun _ _ h => h.elim)) ?_
  rintro parentOwn w' ⟨rfl, inDirectory⟩
  refine Satisfies.bind (entryType_run M readsEntry path w') ?_
  rintro found w'' ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, same_iff, inDirectory⟩

/-- **Checked:** when `removeOwnWith` succeeds, nothing is at the path. This rests only on
`ReadsEntry`, whatever the removal primitives do. -/
theorem removeOwnWith_gone (M : Model) (reads : ReadsEntry M) (kind : Kind) (path : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ removeOwnWith M.ops kind path
      ⦃post⟨fun _ w => ⌜M.entry w path = none⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    unfold removeOwnWith
    refine Satisfies.bind (observe_place M reads path before) ?_
    intro observed w place
    cases decided : removal kind observed with
    | nothing =>
      have absent := (removal_nothing_iff kind observed).mp decided
      rw [place, Place.ofType_absent] at absent
      exact absent
    | remove =>
      cases kind with
      | directory => exact (triple_iff _ _ _ _).mp (removeDirectory_gone M reads path) w trivial
      | file | link => exact (triple_iff _ _ _ _).mp (removeEntry_gone M reads path) w trivial
    | refuse => trivial

/-- A run of `removeOwnWith` that succeeds leaves nothing at the path. Whether it succeeds or
fails, it keeps the entry at each path of the frame of the path (`Model.Unchanged`), and it changes
the state only when an entry of `kind` was at the path at its own place (`OnlyOwn`). -/
theorem removeOwnWith_run (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (removesTree : RemovesTree M) (removesEntry : RemovesEntry M) (kind : Kind) (path : FilePath)
    (before : M.World) :
    Satisfies ((removeOwnWith M.ops kind path).run before)
      (fun _ w => M.entry w path = none ∧ M.Unchanged path before w ∧ OnlyOwn M kind path before w)
      (fun _ w => M.Unchanged path before w ∧ OnlyOwn M kind path before w) := by
  unfold removeOwnWith
  refine Satisfies.bind ((observe_run M readsEntry readsReal path before).mono (fun _ _ h => h)
    (fun _ _ same => by subst same; exact ⟨M.unchanged_refl path _, Or.inl rfl⟩)) ?_
  rintro observed w ⟨rfl, place, same, inDirectory⟩
  cases decided : removal kind observed with
  | nothing =>
    have absent := (removal_nothing_iff kind observed).mp decided
    rw [place, Place.ofType_absent] at absent
    exact ⟨absent, M.unchanged_refl path w, Or.inl rfl⟩
  | remove =>
    obtain ⟨present, own⟩ := (removal_remove_iff kind observed).mp decided
    rw [place, Place.ofType_present] at present
    cases kind with
    | directory =>
      have real := same.mp (own.resolve_left (fun link => Kind.noConfusion link.1)).2
      exact ((triple_iff _ _ _ _).mp
        (removeDirectory_spec M readsEntry removesTree path w present real) w rfl).mono
        (fun _ _ removed => ⟨removed.1, removed.2, Or.inr ⟨present, real⟩⟩)
        (fun _ _ kept => ⟨kept, Or.inr ⟨present, real⟩⟩)
    | file =>
      have real := same.mp (own.resolve_left (fun link => Kind.noConfusion link.1)).2
      exact ((triple_iff _ _ _ _).mp
        (removeEntry_spec M readsEntry removesEntry path w (Or.inl real)) w rfl).mono
        (fun _ _ removed => ⟨removed.1, removed.2, Or.inr ⟨present, real⟩⟩)
        (fun _ _ kept => ⟨kept, Or.inr ⟨present, real⟩⟩)
    | link =>
      have placed := inDirectory (own.resolve_right (fun notLink => notLink.1 rfl)).2
      exact ((triple_iff _ _ _ _).mp
        (removeEntry_spec M readsEntry removesEntry path w (Or.inr ⟨present, placed⟩)) w
        rfl).mono
        (fun _ _ removed => ⟨removed.1, removed.2, Or.inr ⟨present, placed⟩⟩)
        (fun _ _ kept => ⟨kept, Or.inr ⟨present, placed⟩⟩)
  | refuse => exact ⟨M.unchanged_refl path w, Or.inl rfl⟩

/-- `removeOwnWith` removes only an entry of `kind` at its own place: when it succeeds, nothing is
at the path; whether it succeeds or fails, it keeps the entry at each path of the frame of the path
(`Model.Unchanged`) and changes the state only when an entry of `kind` was at the path at its own
place (`OnlyOwn`). -/
theorem removeOwnWith_spec (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (removesTree : RemovesTree M) (removesEntry : RemovesEntry M) (kind : Kind) (path : FilePath)
    (before : M.World) :
    ⦃fun w => ⌜w = before⌝⦄ removeOwnWith M.ops kind path
      ⦃post⟨fun _ w => ⌜M.entry w path = none ∧ M.Unchanged path before w ∧
          OnlyOwn M kind path before w⌝,
        fun _ w => ⌜M.Unchanged path before w ∧ OnlyOwn M kind path before w⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun _ same => same ▸
    removeOwnWith_run M readsEntry readsReal removesTree removesEntry kind path before

/-- **Checked:** when `removeFoundWith` succeeds, nothing is at the path. This rests only on
`ReadsEntry`. -/
theorem removeFoundWith_gone (M : Model) (reads : ReadsEntry M) (path : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ removeFoundWith M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    unfold removeFoundWith
    refine Satisfies.bind ((entryType_run M reads path before).mono (fun _ _ _ => trivial)
      (fun _ _ _ => trivial)) fun found w _ => ?_
    exact (triple_iff _ _ _ _).mp (removeOwnWith_gone M reads (Kind.found found) path) w trivial

/-- `removeFoundWith` removes only a directory or a file at its own place: when it succeeds,
nothing is at the path; whether it succeeds or fails, it keeps the entry at each path of the frame
of the path (`Model.Unchanged`) and changes the state only when an entry of a kind was at the path
at its own place (`OnlyOwn`). -/
theorem removeFoundWith_spec (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (removesTree : RemovesTree M) (removesEntry : RemovesEntry M) (path : FilePath)
    (before : M.World) :
    ⦃fun w => ⌜w = before⌝⦄ removeFoundWith M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none ∧ M.Unchanged path before w ∧
          ∃ kind, OnlyOwn M kind path before w⌝,
        fun _ w => ⌜M.Unchanged path before w ∧ ∃ kind, OnlyOwn M kind path before w⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun _ same => by
    subst same
    unfold removeFoundWith
    refine Satisfies.bind ((entryType_run M readsEntry path _).mono (fun _ _ h => h)
      (fun _ _ same => by
        subst same
        exact ⟨M.unchanged_refl path _, Kind.directory, Or.inl rfl⟩)) ?_
    rintro found w ⟨rfl, -⟩
    exact (removeOwnWith_run M readsEntry readsReal removesTree removesEntry (Kind.found found)
      path w).mono (fun _ _ removed => ⟨removed.1, removed.2.1, _, removed.2.2⟩)
      (fun _ _ kept => ⟨kept.1, _, kept.2⟩)

/-- A run of `confirmMoved` changes nothing, and succeeds only when nothing is at the source and a
regular file is at the destination. -/
theorem confirmMoved_run (M : Model) (reads : ReadsEntry M) (source destination : FilePath)
    (before : M.World) :
    Satisfies ((confirmMoved M.ops source destination).run before)
      (fun _ w => w = before ∧ M.entry before source = none ∧
        M.entry before destination = some .file)
      (fun _ w => w = before) := by
  unfold confirmMoved
  refine Satisfies.bind (entryType_run M reads source before) ?_
  rintro left w ⟨rfl, rfl⟩
  refine Satisfies.bind ((entryType_run M reads destination w).mono (fun _ _ h => h)
    (fun _ _ h => h)) ?_
  rintro arrived w' ⟨rfl, rfl⟩
  rcases h₁ : M.entry w' source with _ | _ <;> rcases h₂ : M.entry w' destination with
    _ | (_ | _ | _ | _) <;> first | exact ⟨rfl, rfl, rfl⟩ | exact rfl

/-- **Checked:** when `replaceWith` succeeds, nothing is at the source and a regular file is at
the destination. This rests only on `ReadsEntry`, whatever the move primitive does. -/
theorem replaceWith_moved (M : Model) (reads : ReadsEntry M) (source destination : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ replaceWith M.ops source destination
      ⦃post⟨fun _ w => ⌜M.entry w source = none ∧ M.entry w destination = some .file⌝,
        fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    unfold replaceWith
    refine Satisfies.bind (P := fun _ _ => True)
      (by cases (observe M.ops source).run before <;> trivial) fun _ w _ => ?_
    refine Satisfies.bind (P := fun _ _ => True)
      (by cases (observe M.ops destination).run w <;> trivial) fun _ w' _ => ?_
    split
    · refine Satisfies.bind (P := fun _ _ => True)
        (by cases (M.ops.rename source destination).run w' <;> trivial) fun _ moved _ => ?_
      exact (confirmMoved_run M reads source destination moved).mono
        (fun _ _ confirmed => by obtain ⟨rfl, gone, arrived⟩ := confirmed; exact ⟨gone, arrived⟩)
        (fun _ _ _ => trivial)
    · trivial

/-- A run of `replaceWith` that succeeds leaves nothing at the source and a regular file at the
destination, and it ran only when the decision held (`Movable`). Whether it succeeds or fails, it
keeps the entry at each path of the frame of both paths (`Model.Kept`), and it changes the state
only when the decision held. -/
theorem replaceWith_run (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (renames : Renames M) (source destination : FilePath) (before : M.World) :
    Satisfies ((replaceWith M.ops source destination).run before)
      (fun _ w => M.entry w source = none ∧ M.entry w destination = some .file ∧
        M.Kept [source, destination] before w ∧ Movable M source destination before)
      (fun _ w => M.Kept [source, destination] before w ∧
        (w = before ∨ Movable M source destination before)) := by
  unfold replaceWith
  have unchanged : ∀ w, w = before →
      M.Kept [source, destination] before w ∧ (w = before ∨ Movable M source destination before) :=
    fun _ same => by subst same; exact ⟨M.kept_refl _ _, Or.inl rfl⟩
  refine Satisfies.bind ((observe_run M readsEntry readsReal source before).mono (fun _ _ h => h)
    (fun _ w same => unchanged w same)) ?_
  rintro observedSource w ⟨rfl, sourcePlace, sourceSame, -⟩
  refine Satisfies.bind ((observe_run M readsEntry readsReal destination w).mono (fun _ _ h => h)
    (fun _ w' same => unchanged w' same)) ?_
  rintro observedDestination w' ⟨rfl, destinationPlace, destinationSame, destinationParent⟩
  split
  · rename_i decided
    obtain ⟨⟨sourcePresent, sourceOwn⟩, destinationFree, parentHolds⟩ :=
      (replacement_iff _).mp decided
    dsimp only at sourcePresent sourceOwn destinationFree parentHolds
    rw [sourcePlace, Place.ofType_present] at sourcePresent
    have inDirectory := destinationParent parentHolds
    obtain ⟨parent, parentIs, parentOwnReal⟩ := inDirectory.2
    have movable : Movable M source destination w' := by
      refine ⟨⟨sourcePresent, sourceSame.mp sourceOwn⟩, ?_, inDirectory⟩
      rcases destinationFree with absent | ⟨present, own⟩
      · rw [destinationPlace, Place.ofType_absent] at absent
        exact Or.inl absent
      · rw [destinationPlace, Place.ofType_present] at present
        exact Or.inr ⟨present, destinationSame.mp own⟩
    refine Satisfies.bind ((triple_iff _ _ _ _).mp
      (renames source destination parent w' (sourceSame.mp sourceOwn) parentIs parentOwnReal)
      w' rfl |>.mono (fun _ _ kept => kept) (fun _ _ kept => ⟨kept, Or.inr movable⟩)) ?_
    intro _ moved kept
    exact (confirmMoved_run M readsEntry source destination moved).mono
      (fun _ _ confirmed => by
        obtain ⟨rfl, gone, arrived⟩ := confirmed
        exact ⟨gone, arrived, kept, movable⟩)
      (fun _ _ same => by subst same; exact ⟨kept, Or.inr movable⟩)
  · exact unchanged w' rfl

/-- `replaceWith` moves only a file at its own place to an absent path or a file at its own place,
in a parent at its own place: when it succeeds, nothing is at the source and a regular file is at
the destination; whether it succeeds or fails, it keeps the entry at each path of the frame of both
paths (`Model.Kept`), and it changes the state only when the decision held (`Movable`). -/
theorem replaceWith_spec (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (renames : Renames M) (source destination : FilePath) (before : M.World) :
    ⦃fun w => ⌜w = before⌝⦄ replaceWith M.ops source destination
      ⦃post⟨fun _ w => ⌜M.entry w source = none ∧ M.entry w destination = some .file ∧
          M.Kept [source, destination] before w ∧ Movable M source destination before⌝,
        fun _ w => ⌜M.Kept [source, destination] before w ∧
          (w = before ∨ Movable M source destination before)⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun _ same => same ▸
    replaceWith_run M readsEntry readsReal renames source destination before

attribute [regula_checked filesystem removeOwnWith_gone
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")] removeOwnWith

attribute [regula_checked filesystem removeFoundWith_gone
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")] removeFoundWith

attribute [regula_checked filesystem replaceWith_moved
  (lean "v4.34.1" "Init/System/IO.lean#L903-L909")] replaceWith

/-- A run of `requirePlacedWith` changes nothing. When it succeeds, each path of the listed tree of
the root (`Model.Listed`) that is a symbolic link or another kind of entry than a directory and a
file (`Model.NotPlain`) is one of the placed paths. -/
theorem requirePlacedWith_run (M : Model) (reads : ReadsEntry M) (lists : ListsEntries M)
    (limit : Nat) (root : FilePath) (placed : List FilePath) (before : M.World) :
    Satisfies ((requirePlacedWith M.ops limit root placed).run before)
      (fun _ w => w = before ∧
        ∀ path, M.Listed before root path → M.NotPlain before path → path ∈ placed)
      (fun _ w => w = before) := by
  simp only [requirePlacedWith]
  refine Satisfies.bind (otherEntries_run M reads lists limit root before) ?_
  rintro found w ⟨rfl, below⟩
  by_cases admitted : linksPlaced { found, placed } = true
  · simp only [admitted, ↓reduceIte]
    simp only [EStateM.run_pure, Satisfies]
    exact ⟨trivial, fun path listed notPlain =>
      (linksPlaced_iff _).mp admitted (below path listed notPlain)⟩
  · simp only [Bool.not_eq_true] at admitted
    simp only [admitted, Bool.false_eq_true, ↓reduceIte, run_throw, Satisfies]

/-- A run of `requireLinkWith` changes nothing. When it succeeds, a symbolic link is at the link's
path, and its real path is the real path of the target. -/
theorem requireLinkWith_run (M : Model) (readsEntry : ReadsEntry M) (readsReal : ReadsReal M)
    (link target : FilePath) (before : M.World) :
    Satisfies ((requireLinkWith M.ops link target).run before)
      (fun _ w => w = before ∧ M.entry before link = some .symlink ∧
        ∃ real, M.real before link = some real ∧ M.real before target = some real)
      (fun _ w => w = before) := by
  simp only [requireLinkWith]
  refine Satisfies.bind (entryType_run M readsEntry link before) ?_
  rintro found w ⟨rfl, rfl⟩
  refine Satisfies.bind ((realOf_run M readsReal link w).mono (fun _ _ h => h) nofun) ?_
  rintro real w' ⟨rfl, rfl⟩
  refine Satisfies.bind ((realOf_run M readsReal target w').mono (fun _ _ h => h) nofun) ?_
  rintro targetReal w'' ⟨rfl, rfl⟩
  by_cases admitted : linkPlaced
      { place := Place.ofType (M.entry w'' link), real := M.real w'' link,
        target := M.real w'' target } = true
  · simp only [admitted, ↓reduceIte]
    simp only [EStateM.run_pure, Satisfies]
    obtain ⟨place, real, linked, targeted⟩ := (linkPlaced_iff _).mp admitted
    exact ⟨trivial, (Place.ofType_present _ .link).mp place, real, linked, targeted⟩
  · simp only [Bool.not_eq_true] at admitted
    simp only [admitted, Bool.false_eq_true, ↓reduceIte, run_throw, Satisfies]

/-! ## The operations in `IO` -/

section IO

variable {ops : Ops IO} {M : Model} {view : Void IO.RealWorld → M.World}

/-- `ownParent` at operations that correspond to a model runs as `ownParent` in the model. -/
theorem ownParent_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (ownParent ops path) (ownParent M.ops path) := by
  unfold ownParent
  cases path.parent <;> cases path.fileName <;>
    first | exact Agrees.pure view false | exact atOwnPlace_agrees corresponds _

/-- `observe` at operations that correspond to a model runs as `observe` in the model. -/
theorem observe_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (observe ops path) (observe M.ops path) := by
  unfold observe
  exact Agrees.bind (atOwnPlace_agrees corresponds path) fun _ =>
    Agrees.bind (ownParent_agrees corresponds path) fun _ =>
      Agrees.bind (entryType_agrees corresponds path) fun _ => Agrees.pure view _

/-- `removeOwnWith` at operations that correspond to a model runs as `removeOwnWith` in the
model. -/
theorem removeOwnWith_agrees (corresponds : Corresponds ops M view) (kind : Kind)
    (path : FilePath) :
    Agrees view (removeOwnWith ops kind path) (removeOwnWith M.ops kind path) := by
  unfold removeOwnWith
  refine Agrees.bind (observe_agrees corresponds path) fun observed => ?_
  cases removal kind observed with
  | nothing => exact Agrees.pure view ()
  | remove =>
    cases kind with
    | directory => exact removeDirectory_agrees corresponds path
    | file | link => exact removeEntry_agrees corresponds path
  | refuse => exact Agrees.throw view _

/-- `removeFoundWith` at operations that correspond to a model runs as `removeFoundWith` in the
model. -/
theorem removeFoundWith_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (removeFoundWith ops path) (removeFoundWith M.ops path) := by
  unfold removeFoundWith
  exact Agrees.bind (entryType_agrees corresponds path) fun found =>
    removeOwnWith_agrees corresponds (Kind.found found) path

/-- `confirmMoved` at operations that correspond to a model runs as `confirmMoved` in the
model. -/
theorem confirmMoved_agrees (corresponds : Corresponds ops M view)
    (source destination : FilePath) :
    Agrees view (confirmMoved ops source destination) (confirmMoved M.ops source destination) := by
  unfold confirmMoved
  refine Agrees.bind (entryType_agrees corresponds source) fun left => ?_
  refine Agrees.bind (entryType_agrees corresponds destination) fun arrived => ?_
  rcases left with _ | _ <;> rcases arrived with _ | (_ | _ | _ | _) <;>
    first | exact Agrees.pure view () | exact Agrees.throw view _

/-- `replaceWith` at operations that correspond to a model runs as `replaceWith` in the model. -/
theorem replaceWith_agrees (corresponds : Corresponds ops M view)
    (source destination : FilePath) :
    Agrees view (replaceWith ops source destination) (replaceWith M.ops source destination) := by
  unfold replaceWith
  refine Agrees.bind (observe_agrees corresponds source) fun observedSource => ?_
  refine Agrees.bind (observe_agrees corresponds destination) fun observedDestination => ?_
  cases replacement { source := observedSource, destination := observedDestination } with
  | true =>
    exact Agrees.bind (corresponds.2.2.2.2.1 source destination) fun _ =>
      confirmMoved_agrees corresponds source destination
  | false => exact Agrees.throw view _

/-- **Checked, in `IO`:** when `removeOwnWith` succeeds at operations that correspond to a model,
nothing is at the path in the state that the world it ends in is read as
(`removeOwnWith_gone`). -/
theorem removeOwnWith_gone_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (kind : Kind) (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeOwnWith ops kind path w) (fun _ s => M.entry s path = none)
      (fun _ _ => True) :=
  (removeOwnWith_agrees corresponds kind path).transfer w
    ((triple_iff _ _ _ _).mp (removeOwnWith_gone M reads kind path) (view w) trivial)

/-- `removeOwnWith` in `IO`, at operations that correspond to a model, removes only an entry of
`kind` at its own place (`removeOwnWith_spec`). -/
theorem removeOwnWith_io (corresponds : Corresponds ops M view) (readsEntry : ReadsEntry M)
    (readsReal : ReadsReal M) (removesTree : RemovesTree M) (removesEntry : RemovesEntry M)
    (kind : Kind) (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeOwnWith ops kind path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s ∧
        OnlyOwn M kind path (view w) s)
      (fun _ s => M.Unchanged path (view w) s ∧ OnlyOwn M kind path (view w) s) :=
  (removeOwnWith_agrees corresponds kind path).transfer w
    (removeOwnWith_run M readsEntry readsReal removesTree removesEntry kind path (view w))

/-- **Checked, in `IO`:** when `removeFoundWith` succeeds at operations that correspond to a model,
nothing is at the path in the state that the world it ends in is read as
(`removeFoundWith_gone`). -/
theorem removeFoundWith_gone_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeFoundWith ops path w) (fun _ s => M.entry s path = none)
      (fun _ _ => True) :=
  (removeFoundWith_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp (removeFoundWith_gone M reads path) (view w) trivial)

/-- `removeFoundWith` in `IO`, at operations that correspond to a model, removes only a directory
or a file at its own place (`removeFoundWith_spec`). -/
theorem removeFoundWith_io (corresponds : Corresponds ops M view) (readsEntry : ReadsEntry M)
    (readsReal : ReadsReal M) (removesTree : RemovesTree M) (removesEntry : RemovesEntry M)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeFoundWith ops path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s ∧
        ∃ kind, OnlyOwn M kind path (view w) s)
      (fun _ s => M.Unchanged path (view w) s ∧ ∃ kind, OnlyOwn M kind path (view w) s) :=
  (removeFoundWith_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp
      (removeFoundWith_spec M readsEntry readsReal removesTree removesEntry path (view w))
      (view w) rfl)

/-- **Checked, in `IO`:** when `replaceWith` succeeds at operations that correspond to a model,
nothing is at the source and a regular file is at the destination in the state that the world it
ends in is read as (`replaceWith_moved`). -/
theorem replaceWith_moved_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (source destination : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (replaceWith ops source destination w)
      (fun _ s => M.entry s source = none ∧ M.entry s destination = some .file)
      (fun _ _ => True) :=
  (replaceWith_agrees corresponds source destination).transfer w
    ((triple_iff _ _ _ _).mp (replaceWith_moved M reads source destination) (view w) trivial)

/-- `replaceWith` in `IO`, at operations that correspond to a model, moves only a file at its own
place to an absent path or a file at its own place, in a parent at its own place
(`replaceWith_spec`). -/
theorem replaceWith_io (corresponds : Corresponds ops M view) (readsEntry : ReadsEntry M)
    (readsReal : ReadsReal M) (renames : Renames M) (source destination : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo view (replaceWith ops source destination w)
      (fun _ s => M.entry s source = none ∧ M.entry s destination = some .file ∧
        M.Kept [source, destination] (view w) s ∧ Movable M source destination (view w))
      (fun _ s => M.Kept [source, destination] (view w) s ∧
        (s = view w ∨ Movable M source destination (view w))) :=
  (replaceWith_agrees corresponds source destination).transfer w
    (replaceWith_run M readsEntry readsReal renames source destination (view w))

/-- `requirePlacedWith` at operations that correspond to a model runs as `requirePlacedWith` in
the model. -/
theorem requirePlacedWith_agrees (corresponds : Corresponds ops M view) (limit : Nat)
    (root : FilePath) (placed : List FilePath) :
    Agrees view (requirePlacedWith ops limit root placed)
      (requirePlacedWith M.ops limit root placed) := by
  refine Agrees.bind (otherEntries_agrees corresponds limit root) fun found => ?_
  by_cases admitted : linksPlaced { found, placed } = true
  · simp only [admitted, ↓reduceIte]
    exact Agrees.pure view _
  · simp only [Bool.not_eq_true] at admitted
    simp only [admitted, Bool.false_eq_true, ↓reduceIte]
    exact Agrees.throw view _

/-- `requirePlacedWith` in `IO`, at operations that correspond to a model, ends in a world read as
the same state, and when it succeeds, each path of the listed tree of the root (`Model.Listed`)
that is a symbolic link or another kind of entry than a directory and a file (`Model.NotPlain`) is
one of the placed paths (`requirePlacedWith_run`). -/
theorem requirePlacedWith_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (lists : ListsEntries M) (limit : Nat) (root : FilePath) (placed : List FilePath)
    (w : Void IO.RealWorld) :
    RunsTo view (requirePlacedWith ops limit root placed w)
      (fun _ s => s = view w ∧ ∀ path, M.Listed (view w) root path →
        M.NotPlain (view w) path → path ∈ placed)
      (fun _ s => s = view w) :=
  (requirePlacedWith_agrees corresponds limit root placed).transfer w
    (requirePlacedWith_run M reads lists limit root placed (view w))

/-- `requireLinkWith` at operations that correspond to a model runs as `requireLinkWith` in the
model. -/
theorem requireLinkWith_agrees (corresponds : Corresponds ops M view) (link target : FilePath) :
    Agrees view (requireLinkWith ops link target) (requireLinkWith M.ops link target) := by
  refine Agrees.bind (entryType_agrees corresponds link) fun found => ?_
  refine Agrees.bind (realOf_agrees corresponds link) fun real => ?_
  refine Agrees.bind (realOf_agrees corresponds target) fun targetReal => ?_
  by_cases admitted :
      linkPlaced { place := Place.ofType found, real, target := targetReal } = true
  · simp only [admitted, ↓reduceIte]
    exact Agrees.pure view _
  · simp only [Bool.not_eq_true] at admitted
    simp only [admitted, Bool.false_eq_true, ↓reduceIte]
    exact Agrees.throw view _

/-- `requireLinkWith` in `IO`, at operations that correspond to a model, ends in a world read as
the same state, and when it succeeds, a symbolic link is at the link's path, and its real path is
the real path of the target (`requireLinkWith_run`). -/
theorem requireLinkWith_io (corresponds : Corresponds ops M view) (readsEntry : ReadsEntry M)
    (readsReal : ReadsReal M) (link target : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (requireLinkWith ops link target w)
      (fun _ s => s = view w ∧ M.entry (view w) link = some .symlink ∧
        ∃ real, M.real (view w) link = some real ∧ M.real (view w) target = some real)
      (fun _ s => s = view w) :=
  (requireLinkWith_agrees corresponds link target).transfer w
    (requireLinkWith_run M readsEntry readsReal link target (view w))

end IO

end Regula.Removal
