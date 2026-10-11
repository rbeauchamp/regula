import RegulaCore.StateTriple
import Regula.Contract
import Regula.Assumption

/-! # The filesystem, as Regula's code acts on it

The operations by which Regula's code reads the filesystem and removes from it (`Ops`), and the
assumptions it makes about them, each a predicate over a model of the filesystem (`Model`). Code
that acts on the filesystem is written once, for the operations in any monad. It runs at the real
operations, which the observer supplies in `IO` (`Regula.Filesystem.observer`). Its theorems are
stated at the operations of every model that satisfies the assumptions they name, so the
hypotheses of a theorem are exactly the assumptions it rests on.

## The model

A model has a type of states, two reads that give the vocabulary of the assumptions, and the
operations as actions on the state:

* `Model.entry`: the type of the entry that a path names, as `lstat(2)` reports it, which does
  not follow a symbolic link at the path's last component;
* `Model.real`: the path that `realpath(3)` resolves a path to, which is absolute and has no `.`
  or `..` component and no symbolic link.

The model is sequential: its state changes only by its operations, so no other process changes
the filesystem between two of them. That premise is the trusted assumption on `Model` itself, so
every theorem stated over a model rests on it.

## The assumptions

Each assumption is the contract of one operation: a `Std.Do` triple whose postcondition is the
property, with the sources that state it (`Regula.Assumption`).

* `ReadsEntry`: `symlinkMetadata` reports the entry, changes nothing, and fails with
  `noFileOrDirectory` only when nothing is there.
* `ReadsReal`: `realPath` gives the real path, changes nothing, and fails exactly when there is
  none.
* `RemovesTree`: `removeDirAll` of a directory at its own place changes no entry outside the
  directory (`Model.Unchanged`), whether it succeeds or fails.
* `RemovesEntry`: `removeFile` of a path at its own place changes no entry outside the path.

That a removal removes the path is not assumed. `removeDirectory` and `removeEntry` read the path
again after the removal and fail when something is still there, so their contracts
(`removeDirectory_gone`, `removeEntry_gone`) rest, besides the model, only on `ReadsEntry`: each
is a checked operation.

## Boundaries

The assumptions are stated for a POSIX system, where `symlinkMetadata` calls `lstat` and
`removeDirAll` reads each entry without following a symbolic link. In Lean 4.34.1 on Windows,
`symlinkMetadata` follows a link, so the observer refuses that read and every directory removal
there. A process that changes the filesystem while Regula's code acts on it is outside the model,
as the trusted assumption on `Model` states. -/

namespace Regula.Filesystem

open System Std.Do Regula.StateTriple

/-- The operations of the filesystem that Regula's code uses, in a monad `m`. The observer
supplies each as the operation of Lean's library that the field names; a model supplies them as
actions on its state (`Model`). -/
structure Ops (m : Type → Type) where
  /-- What `lstat(2)` reports of a path: `System.FilePath.symlinkMetadata`. -/
  symlinkMetadata : FilePath → m IO.FS.Metadata
  /-- The path that `realpath(3)` resolves a path to: `IO.FS.realPath`. -/
  realPath : FilePath → m FilePath
  /-- Remove a directory with all its entries: `IO.FS.removeDirAll`. -/
  removeDirAll : FilePath → m Unit
  /-- Remove the entry that a path names, which is not a directory: `IO.FS.removeFile`. -/
  removeFile : FilePath → m Unit

/-- A model of the filesystem: its states, what the two reads report in each state, and the
operations as actions on the state that can fail with an `IO.Error`. The model is sequential: its
state changes only by its operations. -/
structure Model where
  /-- The states of the filesystem. -/
  World : Type
  /-- The type of the entry that a path names in a state, as `lstat(2)` reports it: a symbolic
  link at the path's last component is the entry, not followed. `none` when nothing is there. -/
  entry : World → FilePath → Option IO.FS.FileType
  /-- The path that `realpath(3)` resolves a path to in a state: absolute, with no `.` or `..`
  component and no symbolic link. `none` when `realpath(3)` fails, such as when nothing is there. -/
  real : World → FilePath → Option FilePath
  /-- The operations, as actions on the state. -/
  ops : Ops (EStateM IO.Error World)

attribute [regula_assumption filesystem
  (trusted "No other process changes the filesystem while the code under study runs. No source \
    states this, and it is not true of a computer as a whole: the theorems apply only while no \
    other process changes the entries that they name.")] Model

/-- `path` is `directory` or an entry below it: it is `directory`, or its parent
(`System.FilePath.parent`) is within `directory`. -/
inductive Within (directory : FilePath) : FilePath → Prop where
  /-- A directory is within itself. -/
  | self : Within directory directory
  /-- A path whose parent is within the directory is within it. -/
  | entry {path parent : FilePath} :
      Within directory parent → path.parent = some parent → Within directory path

/-- From the state `before` to the state `after`, no entry outside `directory` changed. A path
whose parent is its own real path and whose last component is a name, not `.` or `..`, is the one
name of an entry with no symbolic link and no `.` or `..` in it. Each such path that is not within
`directory` names the same type of entry in both states. -/
def Model.Unchanged (M : Model) (directory : FilePath) (before after : M.World) : Prop :=
  ∀ path parent, path.parent = some parent → path.fileName.isSome = true →
    M.real before parent = some parent → ¬ Within directory path →
      M.entry after path = M.entry before path

/-- Nothing changes from a state to itself. -/
theorem Model.unchanged_refl (M : Model) (directory : FilePath) (w : M.World) :
    M.Unchanged directory w w :=
  fun _ _ _ _ _ _ => rfl

/-- Whether an error is the one that Lean gives for `ENOENT`: nothing is at the path. -/
def Absent : IO.Error → Prop
  | .noFileOrDirectory .. => True
  | _ => False

/-- `symlinkMetadata` reports the type of the entry at the path and changes nothing. It fails with
`noFileOrDirectory` only when nothing is there. It can also fail in other ways when nothing is
there, for example with `ENOTDIR` when a component of the path is not a directory. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L1151-L1156")
  (lean "v4.34.1" "runtime/io.cpp#L1160-L1179")
  (lean "v4.34.1" "runtime/io.cpp#L276-L279")
  (document "POSIX.1-2024, lstat()")]
def ReadsEntry (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.symlinkMetadata path
    ⦃post⟨fun metadata w => ⌜w = before ∧ M.entry before path = some metadata.type⌝,
      fun error w => ⌜w = before ∧ (Absent error → M.entry before path = none)⌝⟩⦄

/-- `realPath` gives the real path of the path and changes nothing. It fails exactly when there is
none. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L873-L879")
  (lean "v4.34.1" "runtime/io.cpp#L1054-L1066")
  (document "POSIX.1-2024, realpath()")]
def ReadsReal (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.realPath path
    ⦃post⟨fun real w => ⌜w = before ∧ M.real before path = some real⌝,
      fun _ w => ⌜w = before ∧ M.real before path = none⌝⟩⦄

/-- `removeDirAll` of a directory at its own place, whose real path is the path, changes no entry
outside the directory (`Model.Unchanged`), whether it succeeds or fails. On a POSIX system it reads
each entry with `lstat`, so it removes a symbolic link below the directory and not the link's
target. That it removes the directory is not assumed (`removeDirectory_gone`). The assumption is
false for a directory below the path that is also mounted at another place, such as by a bind
mount: its entries also have names outside the path. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")
  (lean "v4.34.1" "runtime/io.cpp#L1160-L1179")
  (lean "v4.34.1" "runtime/io.cpp#L1197-L1207")
  (lean "v4.34.1" "runtime/io.cpp#L1351-L1364")
  (document "POSIX.1-2024, lstat(), unlink() and rmdir()")]
def RemovesTree (M : Model) : Prop :=
  ∀ path before, M.entry before path = some .dir → M.real before path = some path →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.removeDirAll path
      ⦃post⟨fun _ w => ⌜M.Unchanged path before w⌝, fun _ w => ⌜M.Unchanged path before w⌝⟩⦄

/-- `removeFile` of a path at its own place, whose real path is the path, changes no entry outside
the path (`Model.Unchanged`), whether it succeeds or fails. That it removes the entry is not
assumed (`removeEntry_gone`). -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")
  (lean "v4.34.1" "runtime/io.cpp#L1351-L1364")
  (document "POSIX.1-2024, unlink()")]
def RemovesEntry (M : Model) : Prop :=
  ∀ path before, M.real before path = some path →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.removeFile path
      ⦃post⟨fun _ w => ⌜M.Unchanged path before w⌝, fun _ w => ⌜M.Unchanged path before w⌝⟩⦄

/-! ## Reads -/

/-- The type of the entry at `path`, by a read that follows no symbolic link at `path` itself, or
`none` when nothing is there. Any other failure of the read is thrown. -/
def entryType {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m (Option IO.FS.FileType) :=
  tryCatchThe IO.Error (do return some (← ops.symlinkMetadata path).type) fun
    | .noFileOrDirectory .. => pure none
    | error => throw error

/-- Whether the real path of `path` is `path` itself: `false` when it is another path, and when
`path` has none. -/
def atOwnPlace {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Bool :=
  tryCatchThe IO.Error (do return (← ops.realPath path) == path) fun _ => pure false

/-- A run of `entryType` gives the model's entry at the path and changes nothing. When it fails,
nothing changed. -/
theorem entryType_run (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
    Satisfies (entryType M.ops path before)
      (fun found w => w = before ∧ found = M.entry before path)
      (fun _ w => w = before) := by
  have h := (triple_iff _ _ _ _).mp (reads path before) before rfl
  simp only [entryType, run_tryCatch, run_bind, run_pure]
  revert h
  cases M.ops.symlinkMetadata path before with
  | ok metadata w => intro h; exact ⟨h.1, h.2.symm⟩
  | error e w => intro h; cases e <;> simp_all [Satisfies, Absent, run_pure, run_throw]

/-- A run of `atOwnPlace` never fails, changes nothing, and gives `true` exactly when the real
path of the path is the path. -/
theorem atOwnPlace_run (M : Model) (reads : ReadsReal M) (path : FilePath) (before : M.World) :
    Satisfies (atOwnPlace M.ops path before)
      (fun same w => w = before ∧ (same = true ↔ M.real before path = some path))
      (fun _ _ => False) := by
  have h := (triple_iff _ _ _ _).mp (reads path before) before rfl
  simp only [atOwnPlace, run_tryCatch, run_bind, run_pure]
  revert h
  cases M.ops.realPath path before with
  | ok real w => intro h; refine ⟨h.1, ?_⟩; rw [h.2]; simp [beq_iff_eq]
  | error e w => intro h; simp_all [Satisfies]

/-- `entryType` gives the model's entry at the path and changes nothing. When it fails, nothing
changed. -/
theorem entryType_spec (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
    ⦃fun w => ⌜w = before⌝⦄ entryType M.ops path
      ⦃post⟨fun found w => ⌜w = before ∧ found = M.entry before path⌝,
        fun _ w => ⌜w = before⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun _ same => same ▸ entryType_run M reads path before

/-- `atOwnPlace` never fails, changes nothing, and gives `true` exactly when the real path of the
path is the path. -/
theorem atOwnPlace_spec (M : Model) (reads : ReadsReal M) (path : FilePath) (before : M.World) :
    ⦃fun w => ⌜w = before⌝⦄ atOwnPlace M.ops path
      ⦃post⟨fun same w => ⌜w = before ∧ (same = true ↔ M.real before path = some path)⌝,
        fun _ _ => ⌜False⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun _ same => same ▸ atOwnPlace_run M reads path before

/-! ## Checked removals -/

/-- Read `path` again after a removal, and fail when something is still there. -/
def confirmGone {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  if (← entryType ops path).isSome then
    throw (IO.userError s!"{path} is still there after its removal")

/-- Remove the directory at `path` with all its entries, then read `path` again, and fail when
something is still there. -/
def removeDirectory {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  ops.removeDirAll path
  confirmGone ops path

/-- Remove the entry at `path`, which is not a directory, then read `path` again, and fail when
something is still there. -/
def removeEntry {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  ops.removeFile path
  confirmGone ops path

/-- A run of an action `removal` followed by `confirmGone` ends with nothing at the path when it
succeeds. It ends in a state of `Q` when `removal` succeeds and of `E` when `removal` fails, as the
runs of `removal` do. -/
theorem confirmed_run (M : Model) (reads : ReadsEntry M) (path : FilePath)
    (removal : EStateM IO.Error M.World Unit) (before : M.World) (Q E : M.World → Prop)
    (removed : Satisfies (removal before) (fun _ w => Q w) (fun _ w => E w)) :
    Satisfies ((do removal; confirmGone M.ops path : EStateM IO.Error M.World Unit) before)
      (fun _ w => M.entry w path = none ∧ Q w) (fun _ w => Q w ∨ E w) := by
  simp only [run_bind]
  revert removed
  cases removal before with
  | ok _ w =>
    intro removed
    have h := confirmGone_run M reads path w
    revert h
    simp only [Satisfies] at removed ⊢
    cases confirmGone M.ops path w with
    | ok _ w' => intro h; rw [h.1]; exact ⟨h.2, removed⟩
    | error _ w' => intro h; rw [h]; exact .inl removed
  | error _ w => intro removed; exact .inr removed
where
  /-- A run of `confirmGone` changes nothing, and succeeds only when nothing is at the path. -/
  confirmGone_run (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
      Satisfies (confirmGone M.ops path before)
        (fun _ w => w = before ∧ M.entry before path = none) (fun _ w => w = before) := by
    have h := entryType_run M reads path before
    simp only [confirmGone, run_bind]
    revert h
    cases entryType M.ops path before with
    | ok found w =>
      intro h
      cases found with
      | none => exact ⟨h.1, h.2.symm⟩
      | some _ => exact h.1
    | error e w => intro h; exact h

/-- **Checked:** when `removeDirectory` succeeds, nothing is at the path. Besides the model, this
rests only on `ReadsEntry`, whatever `removeDirAll` does. -/
theorem removeDirectory_gone (M : Model) (reads : ReadsEntry M) (path : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ removeDirectory M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    have h := confirmed_run M reads path (M.ops.removeDirAll path) before (fun _ => True)
      (fun _ => True) (by unfold Satisfies; split <;> trivial)
    revert h
    show Satisfies (removeDirectory M.ops path before) _ _ → _
    unfold Satisfies
    split
    · exact fun h => h.1
    · exact fun _ => trivial

/-- **Checked:** when `removeEntry` succeeds, nothing is at the path. Besides the model, this rests
only on `ReadsEntry`, whatever `removeFile` does. -/
theorem removeEntry_gone (M : Model) (reads : ReadsEntry M) (path : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ removeEntry M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    have h := confirmed_run M reads path (M.ops.removeFile path) before (fun _ => True)
      (fun _ => True) (by unfold Satisfies; split <;> trivial)
    revert h
    show Satisfies (removeEntry M.ops path before) _ _ → _
    unfold Satisfies
    split
    · exact fun h => h.1
    · exact fun _ => trivial

attribute [regula_checked filesystem removeDirectory_gone
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")] removeDirectory

attribute [regula_checked filesystem removeEntry_gone
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")] removeEntry

/-- `removeDirectory` of a directory at its own place removes it and changes no entry outside it;
when it fails, it changed no entry outside it. -/
theorem removeDirectory_spec (M : Model) (reads : ReadsEntry M) (removes : RemovesTree M)
    (path : FilePath) (before : M.World) (directory : M.entry before path = some .dir)
    (own : M.real before path = some path) :
    ⦃fun w => ⌜w = before⌝⦄ removeDirectory M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none ∧ M.Unchanged path before w⌝,
        fun _ w => ⌜M.Unchanged path before w⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun s same => by
    subst same
    have h := confirmed_run M reads path (M.ops.removeDirAll path) s (M.Unchanged path s)
      (M.Unchanged path s) ((triple_iff _ _ _ _).mp (removes path s directory own) s rfl)
    revert h
    show Satisfies (removeDirectory M.ops path s) _ _ → _
    unfold Satisfies
    split
    · exact id
    · exact fun h => h.elim id id

/-- `removeEntry` of a path at its own place removes it and changes no entry outside it; when it
fails, it changed no entry outside it. -/
theorem removeEntry_spec (M : Model) (reads : ReadsEntry M) (removes : RemovesEntry M)
    (path : FilePath) (before : M.World) (own : M.real before path = some path) :
    ⦃fun w => ⌜w = before⌝⦄ removeEntry M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none ∧ M.Unchanged path before w⌝,
        fun _ w => ⌜M.Unchanged path before w⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun s same => by
    subst same
    have h := confirmed_run M reads path (M.ops.removeFile path) s (M.Unchanged path s)
      (M.Unchanged path s) ((triple_iff _ _ _ _).mp (removes path s own) s rfl)
    revert h
    show Satisfies (removeEntry M.ops path s) _ _ → _
    unfold Satisfies
    split
    · exact id
    · exact fun h => h.elim id id

end Regula.Filesystem
