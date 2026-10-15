import RegulaProvision
import RegulaCore.Filesystem

/-! # The link installation of provisioning, in the filesystem model

`RegulaProvision.installLinkWith` puts the shared Mathlib link at its place in a copy. The driver
runs it at `linkOps`. This module states its runs in a model of the filesystem of
`RegulaCore.Filesystem` (`LinkModel`), and carries them to the runs of the same definition in `IO`
(`installLink_refused_io`, `installLink_placed_io`) at operations that agree with the model
(`LinkCorresponds`), as every set of operations does at the model whose states are the worlds
(`LinkModel.ofIO`, `linkCorresponds_ofIO`). `linkOps_refused` and `linkOps_placed` state them for
the driver's operations. The driver imports only the toolchain's libraries, because
`scripts/provision.sh` runs it with `lean --run` before the package is built; so this module of its
library imports it with the model, and nothing that the driver runs imports this module.

* `installLink_refused`: when an entry of any type is at the place of the directory in which the
  link is made, a directory, a symbolic link, a regular file or a special file, the run fails and
  ends in the state it started from. So it follows no link there, makes no link, in that entry or
  elsewhere, and changes no entry. It rests on `RefusesOccupied` alone, the refusal of
  `mkdir(2)`; no read decides it before the creation.
* `installLink_placed`: when a run succeeds, a symbolic link is at the path and nothing is at the
  directory's place. It rests on `Regula.Filesystem.ReadsEntry` alone: the program reads both after
  the move.

They do not establish the text of the link at the path, that a run which succeeds changes no
other entry, or what a run that fails after the directory's creation leaves. `ln`, `rename(2)`
and `rmdir(2)` have no assumption here; each is trusted as its operation in
`RegulaProvision.linkOps` states. The decisions to remove or replace the entry at the path before
the installation are not decided here (issue 389). -/

namespace RegulaProvision

open System Regula.StateTriple Regula.Filesystem

/-- A model of the link installation: a filesystem model, and the installation's operations as
actions on its states. The installation reads an entry with the model's `lstat(2)` read. -/
structure LinkModel where
  /-- The filesystem model whose entries the theorems describe. -/
  filesystem : Model
  /-- The installation's operations, as actions on the model's states. -/
  ops : LinkOps (EStateM IO.Error filesystem.World)
  /-- The installation's read of an entry is the model's `symlinkMetadata`. -/
  metadata : ops.metadata = filesystem.ops.symlinkMetadata

/-- The creation of a directory fails and changes nothing when an entry is at the path, whatever
its type: a directory, a symbolic link, which it does not follow, a regular file or a special
file. Lean 4.34.1's `IO.FS.createDir` calls `mkdir` once and reports its error, and the driver
sets the directory's mode only after `mkdir` succeeds (`RegulaProvision.linkOps`). -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L895-L900")
  (lean "v4.34.1" "runtime/io.cpp#L1181-L1195")
  (document filesystem "POSIX.1-2024, mkdir(): [EEXIST] The named file exists; if the path \
    names a symbolic link, mkdir() fails with [EEXIST]")]
def RefusesOccupied (L : LinkModel) : Prop :=
  ∀ path before, L.filesystem.entry before path ≠ none →
    Satisfies ((L.ops.directory path).run before) (fun _ _ => False)
      (fun _ after => after = before)

/-- The installation's read of an entry is the filesystem model's (`entryType`). -/
theorem entryKind_eq (L : LinkModel) (path : FilePath) :
    entryKindWith L.ops path = entryType L.filesystem.ops path := by
  unfold entryKindWith entryType
  rw [L.metadata]
  rfl

/-- A run of `confirmLinkWith` changes nothing, and succeeds only when a symbolic link is at the
path and nothing is at the directory's place. -/
theorem confirmLink_run (L : LinkModel) (reads : ReadsEntry L.filesystem) (path stage : FilePath)
    (before : L.filesystem.World) :
    Satisfies ((confirmLinkWith L.ops path stage).run before)
      (fun _ after => after = before ∧ L.filesystem.entry before path = some .symlink ∧
        L.filesystem.entry before stage = none)
      (fun _ after => after = before) := by
  have read (place : FilePath) : Satisfies ((entryKindWith L.ops place).run before)
      (fun found after => after = before ∧ found = L.filesystem.entry before place)
      (fun _ after => after = before) := by
    rw [entryKind_eq]
    exact entryType_run L.filesystem reads place before
  unfold confirmLinkWith
  refine Satisfies.bind (read path) fun placed state placedRead => ?_
  obtain ⟨rfl, placedIs⟩ := placedRead
  refine Satisfies.bind (read stage) fun left state leftRead => ?_
  obtain ⟨rfl, leftIs⟩ := leftRead
  clear read
  rcases placed with _ | ⟨_ | _ | _ | _⟩ <;> rcases left with _ | ⟨_ | _ | _ | _⟩ <;>
    simp only [run_throw, EStateM.run_pure, Satisfies, true_and] <;>
    exact ⟨placedIs.symm, leftIs.symm⟩

/-- When an entry is at the place of the directory in which the link is made, whatever its type,
a run of `installLinkWith` fails and ends in the state it started from: `mkdir(2)` refuses the
entry, and nothing runs after it. So the run follows no link there, makes no link, in that entry
or elsewhere, and changes no entry. -/
theorem installLink_refused (L : LinkModel) (refuses : RefusesOccupied L) (path : FilePath)
    (target nonce : String) (stage staged : FilePath)
    (staging : linkStage path nonce = some (stage, staged)) (before : L.filesystem.World)
    (occupied : L.filesystem.entry before stage ≠ none) :
    Satisfies ((installLinkWith L.ops path target nonce).run before)
      (fun _ _ => False) (fun _ after => after = before) := by
  have refused := refuses stage before occupied
  simp only [installLinkWith, staging, placeLinkWith, EStateM.run_bind]
  revert refused
  cases (L.ops.directory stage).run before with
  | ok _ _ => exact False.elim
  | error _ _ => exact id

/-- When a run of `installLinkWith` succeeds, a symbolic link is at the path and nothing is at the
place of the directory in which it was made. This rests on `ReadsEntry` alone, whatever the
creation, the link, the move and the removal did: the program reads both after them. -/
theorem installLink_placed (L : LinkModel) (reads : ReadsEntry L.filesystem) (path : FilePath)
    (target nonce : String) (stage staged : FilePath)
    (staging : linkStage path nonce = some (stage, staged)) (before : L.filesystem.World) :
    Satisfies ((installLinkWith L.ops path target nonce).run before)
      (fun _ after => L.filesystem.entry after path = some .symlink ∧
        L.filesystem.entry after stage = none)
      (fun _ _ => True) := by
  simp only [installLinkWith, staging]
  refine Satisfies.bind (P := fun _ _ => True) ?_ fun _ state _ => ?_
  · unfold Satisfies; split <;> trivial
  · exact (confirmLink_run L reads path stage state).mono
      (fun _ _ confirmed => confirmed.1 ▸ confirmed.2) (fun _ _ _ => trivial)

/-! ## The runs in `IO` -/

/-- The operations `ops` in `IO` run as the operations of the model `L`, when `view` reads each
world of `IO` as a state of `L` (`Regula.StateTriple.Agrees`). As `Regula.Filesystem.Corresponds`,
this is agreement of runs, not a property of the filesystem: `linkCorresponds_ofIO` proves it for
every set of operations at the model whose states are the worlds. -/
def LinkCorresponds (ops : LinkOps IO) (L : LinkModel)
    (view : Void IO.RealWorld → L.filesystem.World) : Prop :=
  (∀ path, Agrees view (ops.metadata path) (L.ops.metadata path)) ∧
    (∀ path, Agrees view (ops.directory path) (L.ops.directory path)) ∧
    (∀ target path, Agrees view (ops.link target path) (L.ops.link target path)) ∧
    (∀ source destination,
      Agrees view (ops.rename source destination) (L.ops.rename source destination)) ∧
    (∀ path, Agrees view (ops.removeFile path) (L.ops.removeFile path)) ∧
    (∀ path, Agrees view (ops.removeDir path) (L.ops.removeDir path))

/-- The model whose states are the worlds of `IO`: the filesystem model of `filesystemOps` and the
reads `entry`, `real` and `ident` (`Regula.Filesystem.Model.ofIO`), with the installation's
operations `ops` run over the worlds. `metadata` states that the installation reads an entry with
the filesystem model's read. -/
def LinkModel.ofIO (filesystemOps : Ops IO) (ops : LinkOps IO)
    (metadata : ops.metadata = filesystemOps.symlinkMetadata)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId) : LinkModel where
  filesystem := Model.ofIO filesystemOps entry real ident
  ops := {
    metadata := fun path => ofEIO (ops.metadata path)
    directory := fun path => ofEIO (ops.directory path)
    link := fun target path => ofEIO (ops.link target path)
    rename := fun source destination => ofEIO (ops.rename source destination)
    removeFile := fun path => ofEIO (ops.removeFile path)
    removeDir := fun path => ofEIO (ops.removeDir path) }
  metadata := by
    funext path
    show ofEIO (ops.metadata path) = ofEIO (filesystemOps.symlinkMetadata path)
    rw [metadata]

/-- Every set of operations in `IO` corresponds to the model whose states are the worlds of `IO`,
each world read as itself. -/
theorem linkCorresponds_ofIO (filesystemOps : Ops IO) (ops : LinkOps IO)
    (metadata : ops.metadata = filesystemOps.symlinkMetadata)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId) :
    LinkCorresponds ops (LinkModel.ofIO filesystemOps ops metadata entry real ident) id :=
  ⟨fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _, fun _ _ => ofEIO_agrees _,
    fun _ _ => ofEIO_agrees _, fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _⟩

section IO

variable {ops : LinkOps IO} {L : LinkModel} {view : Void IO.RealWorld → L.filesystem.World}

/-- `entryKindWith` at corresponding operations runs as `entryKindWith` in the model. -/
theorem entryKind_agrees (corresponds : LinkCorresponds ops L view) (path : FilePath) :
    Agrees view (entryKindWith ops path) (entryKindWith L.ops path) := by
  unfold entryKindWith
  refine Agrees.tryCatch (Agrees.bind (corresponds.1 path) fun _ => Agrees.pure view _) ?_
  intro error
  cases error <;> first | exact Agrees.pure view none | exact Agrees.throw view _

/-- `placeLinkWith` at corresponding operations runs as `placeLinkWith` in the model. -/
theorem placeLink_agrees (corresponds : LinkCorresponds ops L view)
    (stage staged path : FilePath) (target : String) :
    Agrees view (placeLinkWith ops stage staged path target)
      (placeLinkWith L.ops stage staged path target) := by
  obtain ⟨_, directory, link, rename, removeFile, removeDir⟩ := id corresponds
  refine Agrees.bind (directory stage) fun _ => Agrees.bind ?_ fun _ => removeDir stage
  refine Agrees.tryCatch (Agrees.bind (link target staged) fun _ => rename staged path) ?_
  intro error
  refine Agrees.bind ?_ fun _ => Agrees.throw view error
  refine Agrees.tryCatch ?_ fun _ => Agrees.pure view ()
  refine Agrees.bind (entryKind_agrees corresponds staged) fun found => ?_
  by_cases linked : (found == some .symlink) = true
  · simp only [linked, ↓reduceIte]
    exact Agrees.bind (removeFile staged) fun _ => removeDir stage
  · simp only [linked, Bool.false_eq_true, ↓reduceIte]
    exact Agrees.bind (Agrees.pure view ()) fun _ => removeDir stage

/-- `confirmLinkWith` at corresponding operations runs as `confirmLinkWith` in the model. -/
theorem confirmLink_agrees (corresponds : LinkCorresponds ops L view) (path stage : FilePath) :
    Agrees view (confirmLinkWith ops path stage) (confirmLinkWith L.ops path stage) := by
  refine Agrees.bind (entryKind_agrees corresponds path) fun placed => ?_
  refine Agrees.bind (entryKind_agrees corresponds stage) fun left => ?_
  rcases placed with _ | ⟨_ | _ | _ | _⟩ <;> rcases left with _ | ⟨_ | _ | _ | _⟩ <;>
    first | exact Agrees.pure view () | exact Agrees.throw view _

/-- `installLinkWith` at corresponding operations runs as `installLinkWith` in the model. -/
theorem installLink_agrees (corresponds : LinkCorresponds ops L view) (path : FilePath)
    (target nonce : String) :
    Agrees view (installLinkWith ops path target nonce)
      (installLinkWith L.ops path target nonce) := by
  unfold installLinkWith
  cases linkStage path nonce with
  | none => exact Agrees.throw view _
  | some places =>
    exact Agrees.bind (placeLink_agrees corresponds places.1 places.2 path target)
      fun _ => confirmLink_agrees corresponds path places.1

/-- `installLinkWith` in `IO`, at operations that correspond to a model, from a world whose state
has an entry at the place of the directory in which the link is made, fails and ends in a world
read as that state (`installLink_refused`). -/
theorem installLink_refused_io (corresponds : LinkCorresponds ops L view)
    (refuses : RefusesOccupied L) (path : FilePath) (target nonce : String)
    (stage staged : FilePath) (staging : linkStage path nonce = some (stage, staged))
    (w : Void IO.RealWorld) (occupied : L.filesystem.entry (view w) stage ≠ none) :
    RunsTo view (installLinkWith ops path target nonce w)
      (fun _ _ => False) (fun _ after => after = view w) :=
  (installLink_agrees corresponds path target nonce).transfer w
    (installLink_refused L refuses path target nonce stage staged staging (view w) occupied)

/-- When `installLinkWith` in `IO` succeeds at operations that correspond to a model, a symbolic
link is at the path and nothing is at the directory's place, in the state that the world it ends
in is read as (`installLink_placed`). -/
theorem installLink_placed_io (corresponds : LinkCorresponds ops L view)
    (reads : ReadsEntry L.filesystem) (path : FilePath) (target nonce : String)
    (stage staged : FilePath) (staging : linkStage path nonce = some (stage, staged))
    (w : Void IO.RealWorld) :
    RunsTo view (installLinkWith ops path target nonce w)
      (fun _ after => L.filesystem.entry after path = some .symlink ∧
        L.filesystem.entry after stage = none)
      (fun _ _ => True) :=
  (installLink_agrees corresponds path target nonce).transfer w
    (installLink_placed L reads path target nonce stage staged staging (view w))

end IO

/-! ## The driver's operations -/

/-- The link installation that the driver runs (`linkOps`), from a world where an entry is at the
place of the directory in which the link is made, fails and ends in the world it started from,
at the model of the worlds whose `mkdir` satisfies `RefusesOccupied`. `filesystemOps` is any set
of filesystem operations whose read of an entry is the driver's; no other operation of it
appears in the hypotheses. -/
theorem linkOps_refused (filesystemOps : Ops IO)
    (metadata : linkOps.metadata = filesystemOps.symlinkMetadata)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (refuses : RefusesOccupied (LinkModel.ofIO filesystemOps linkOps metadata entry real ident))
    (path : FilePath) (target nonce : String) (stage staged : FilePath)
    (staging : linkStage path nonce = some (stage, staged)) (w : Void IO.RealWorld)
    (occupied : entry w stage ≠ none) :
    RunsTo id (installLinkWith linkOps path target nonce w)
      (fun _ _ => False) (fun _ after => after = w) :=
  installLink_refused_io (linkCorresponds_ofIO filesystemOps linkOps metadata entry real ident)
    refuses path target nonce stage staged staging w occupied

/-- When the link installation that the driver runs (`linkOps`) succeeds, a symbolic link is at
the path and nothing is at the place of the directory in which it was made, at the model of the
worlds whose read of an entry satisfies `ReadsEntry`. -/
theorem linkOps_placed (filesystemOps : Ops IO)
    (metadata : linkOps.metadata = filesystemOps.symlinkMetadata)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (reads : ReadsEntry (Model.ofIO filesystemOps entry real ident))
    (path : FilePath) (target nonce : String) (stage staged : FilePath)
    (staging : linkStage path nonce = some (stage, staged)) (w : Void IO.RealWorld) :
    RunsTo id (installLinkWith linkOps path target nonce w)
      (fun _ after => entry after path = some .symlink ∧ entry after stage = none)
      (fun _ _ => True) :=
  installLink_placed_io (linkCorresponds_ofIO filesystemOps linkOps metadata entry real ident)
    reads path target nonce stage staged staging w

end RegulaProvision
