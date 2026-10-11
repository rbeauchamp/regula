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
* `Model.real`: what `realpath(3)` resolves a path to, which is absolute and has no `.` or `..`
  component and no symbolic link.

## The assumptions

Each assumption is a predicate with the sources that state it (`Regula.Assumption`). The four are
the contracts of the operations, each a `Std.Do` triple whose postcondition is the property:

* `ReadsEntry`: `symlinkMetadata` reports the entry, changes nothing, and fails with
  `noFileOrDirectory` only when nothing is there.
* `ReadsReal`: `realPath` gives what `realpath(3)` gives, changes nothing, and fails exactly when
  `realpath(3)` fails.
* `RemovesTree`: `removeDirAll` of a directory at its own place keeps the type of each entry
  outside the directory (`Model.Unchanged`), whether it succeeds or fails.
* `RemovesEntry`: `removeFile` of a path at its own place keeps the type of each entry outside the
  path.

Each is a statement about every run from every state, so together they carry "no other process
changes the filesystem while the code runs", which none states alone. In `IO`, the world that one
operation ends in is the world that the next starts from, so a change that another process makes
between them is part of one of the two runs. A read changes nothing, and a removal keeps the type
of each entry outside its path. So the change makes one of the assumptions false, unless the first
operation is a removal and the change is within its path, and the theorems that rest on a false
assumption say nothing.

That a removal removes the path is not assumed. `removeDirectory` and `removeEntry` read the path
again after the removal and fail when something is still there, so their contracts
(`removeDirectory_gone`, `removeEntry_gone`) rest only on `ReadsEntry`: each is a checked
operation.

## From the model to `IO`

The theorems about a function's runs in a model (`removeDirectory_spec`, `removeDirectory_gone`,
`removeEntry_spec`, `removeEntry_gone`, `atOwnPlace_spec`) are carried to the runs of the same
function in `IO` (`removeDirectory_io`, `removeDirectory_gone_io`, `removeEntry_io`,
`removeEntry_gone_io`, `atOwnPlace_io`) at operations that correspond to the model
(`Corresponds`): each operation in `IO` runs as the model's operation when each world of `IO` is
read as a model state. That is agreement of runs, not an assumption about the filesystem:
`corresponds_ofIO` proves it for every set of operations at the model whose states are the worlds
(`Model.ofIO`). `Regula.Filesystem` states the theorems for the observer at that model, where they
rest on the four assumptions alone.

## Boundaries

The assumptions are stated for a POSIX system, where `symlinkMetadata` calls `lstat`,
`removeDirAll` reads each entry without following a symbolic link, and `realPath` calls
`realpath`. In Lean 4.34.1 on Windows, `symlinkMetadata` follows a link and `realPath` can give a
path it did not resolve, so the observer refuses those reads and every directory removal there.
The model reads the type of an entry, not which file it is or what it holds: an entry outside a
removed path that is replaced by another entry of the same type is not a change the frame sees.

The frame (`Model.Unchanged`) leaves out each path that names an entry but is not its own real
path. On a volume that ignores case or Unicode normalization, the removal assumptions rest on
`realpath(3)` giving the name the volume stores for each component, so that another spelling of a
removed name is not its own real path. Darwin's `realpath(3)` does this (`RemovesTree` and
`RemovesEntry` cite its source), and it was observed once on macOS 27.0.1 (APFS), where
`realpath dir/FILE` printed `.../Dir/file`. The removal assumptions are false where `realpath(3)` keeps a name as written:
Darwin's on a volume where `getattrlist(2)` is not supported, which falls back to `lstat(2)`
(`realpath.c#L238-L243`), and glibc's in a Linux directory that folds case. They are also false
when an ancestor of the removed path is also reached through a second mount, such as a bind mount,
which `realpath(3)` does not resolve: the entries below it then have a second name that is its own
real path. `RemovesTree` is false, too, for a directory below the path that is also mounted at
another place. -/

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
operations as actions on the state that can fail with an `IO.Error`. -/
structure Model where
  /-- The states of the filesystem. -/
  World : Type
  /-- The type of the entry that a path names in a state, as `lstat(2)` reports it: a symbolic
  link at the path's last component is the entry, not followed. `none` when nothing is there. -/
  entry : World → FilePath → Option IO.FS.FileType
  /-- What `realpath(3)` resolves a path to in a state: an absolute path with no `.` or `..`
  component and no symbolic link. `none` when `realpath(3)` fails, such as when nothing is
  there. -/
  real : World → FilePath → Option FilePath
  /-- The operations, as actions on the state. -/
  ops : Ops (EStateM IO.Error World)

/-- `path` is `directory` or an entry below it: it is `directory`, or its parent
(`System.FilePath.parent`) is within `directory`. -/
inductive Within (directory : FilePath) : FilePath → Prop where
  /-- A directory is within itself. -/
  | self : Within directory directory
  /-- A path whose parent is within the directory is within it. -/
  | entry {path parent : FilePath} :
      Within directory parent → path.parent = some parent → Within directory path

/-- From the state `before` to the state `after`, each entry outside `directory` kept its type. The
frame is each path that is not within `directory`, whose parent is its own real path in `before`,
whose last component is a name, not `.` or `..`, and that in `before` is its own real path or
names nothing. Each such path names an entry of the same type in both states, or nothing in both.

A path that names an entry but is not its own real path is outside the frame: a second spelling
of the entry's name, such as another case or another Unicode normalization of it on a volume that
ignores those, and a symbolic link, whose real path is not the link. A path that names nothing is
in the frame, so nothing appears outside `directory`. Which file the entry is, and what it holds,
is not part of the model. -/
def Model.Unchanged (M : Model) (directory : FilePath) (before after : M.World) : Prop :=
  ∀ path parent, path.parent = some parent → path.fileName.isSome = true →
    M.real before parent = some parent →
    (M.entry before path = none ∨ M.real before path = some path) → ¬ Within directory path →
      M.entry after path = M.entry before path

/-- Nothing changes from a state to itself. -/
theorem Model.unchanged_refl (M : Model) (directory : FilePath) (w : M.World) :
    M.Unchanged directory w w :=
  fun _ _ _ _ _ _ _ => rfl

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
  (document filesystem "POSIX.1-2024, lstat()")]
def ReadsEntry (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.symlinkMetadata path
    ⦃post⟨fun metadata w => ⌜w = before ∧ M.entry before path = some metadata.type⌝,
      fun error w => ⌜w = before ∧ (Absent error → M.entry before path = none)⌝⟩⦄

/-- `realPath` gives what `realpath(3)` resolves the path to and changes nothing. It fails exactly
when `realpath(3)` fails. On Windows, Lean 4.34.1's `realPath` gives the path itself when it cannot
resolve it (`runtime/io.cpp#L1032-L1033`), so the observer refuses it there. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L873-L879")
  (lean "v4.34.1" "runtime/io.cpp#L1054-L1066")
  (document filesystem "POSIX.1-2024, realpath()")]
def ReadsReal (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.realPath path
    ⦃post⟨fun real w => ⌜w = before ∧ M.real before path = some real⌝,
      fun _ w => ⌜w = before ∧ M.real before path = none⌝⟩⦄

/-- `removeDirAll` of a directory at its own place, whose real path is the path, keeps the type of
each entry outside the directory (`Model.Unchanged`), whether it succeeds or fails. On a POSIX
system it reads each entry with `lstat`, so it removes a symbolic link below the directory and not
the link's target. That it removes the directory is not assumed (`removeDirectory_gone`).

On a volume that ignores case or Unicode normalization, the assumption rests on `realpath(3)`
giving the name the volume stores for each component, so that another spelling of the directory's
name is not its own real path and is outside the frame. Darwin's libc does this, as its source
below states, and it was observed once on macOS 27.0.1 (APFS), where `realpath dir/FILE` printed
`.../Dir/file`. The assumption is false where `realpath(3)` keeps a name as written: Darwin's on a
volume where `getattrlist(2)` is not supported, which falls back to `lstat(2)`
(`realpath.c#L238-L243`), and glibc's in a Linux directory that folds case. It is also false for a
directory below the path that is also mounted at another place, such as by a bind mount, whose
entries also have names outside the path, and when an ancestor of the path is also reached through
a second mount, which `realpath(3)` does not resolve: the entries below it then have a second name
that is its own real path. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")
  (lean "v4.34.1" "runtime/io.cpp#L1160-L1179")
  (lean "v4.34.1" "runtime/io.cpp#L1197-L1207")
  (lean "v4.34.1" "runtime/io.cpp#L1351-L1364")
  (document filesystem "POSIX.1-2024, lstat(), unlink() and rmdir()")
  (document filesystem "Apple Libc-1752.120.2, stdlib/FreeBSD/realpath.c#L216-L243 and \
    #L348-L358: Darwin's realpath(3) replaces each path component with the name that \
    getattrlist(2) reads from the volume")]
def RemovesTree (M : Model) : Prop :=
  ∀ path before, M.entry before path = some .dir → M.real before path = some path →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.removeDirAll path
      ⦃post⟨fun _ w => ⌜M.Unchanged path before w⌝, fun _ w => ⌜M.Unchanged path before w⌝⟩⦄

/-- `removeFile` of a path at its own place, whose real path is the path, keeps the type of each
entry outside the path (`Model.Unchanged`), whether it succeeds or fails. That it removes the entry
is not assumed (`removeEntry_gone`).

On a volume that ignores case or Unicode normalization, the assumption rests on `realpath(3)`
giving the name the volume stores for each component, so that another spelling of the entry's name
is not its own real path and is outside the frame. Darwin's libc does this, as its source below
states, and it was observed once on macOS 27.0.1 (APFS), where `realpath dir/FILE` printed
`.../Dir/file`. The assumption is false where `realpath(3)` keeps a name as written: Darwin's on a
volume where `getattrlist(2)` is not supported, which falls back to `lstat(2)`
(`realpath.c#L238-L243`), and glibc's in a Linux directory that folds case. It is also false when
an ancestor of the path is also reached through a second mount, such as a bind mount, which
`realpath(3)` does not resolve: the entries below it then have a second name that is its own real
path. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")
  (lean "v4.34.1" "runtime/io.cpp#L1351-L1364")
  (document filesystem "POSIX.1-2024, unlink()")
  (document filesystem "Apple Libc-1752.120.2, stdlib/FreeBSD/realpath.c#L216-L243 and \
    #L348-L358: Darwin's realpath(3) replaces each path component with the name that \
    getattrlist(2) reads from the volume")]
def RemovesEntry (M : Model) : Prop :=
  ∀ path before, M.real before path = some path →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.removeFile path
      ⦃post⟨fun _ w => ⌜M.Unchanged path before w⌝, fun _ w => ⌜M.Unchanged path before w⌝⟩⦄

/-! ## Operations in `IO` that correspond to a model -/

/-- The operations `ops` in `IO` run as the operations of the model `M`, when `view` reads each
world of `IO` as a state of `M` (`Regula.StateTriple.Agrees`): from each world, an operation of
`ops` has the outcome of the model's operation from the view of that world, and the view of the
world it ends in is the state the model's operation ends in.

This is agreement of runs, not a property of the filesystem, so it has no role: `corresponds_ofIO`
proves it for every set of operations at the model whose states are the worlds. It does not say
that no other process changes the filesystem. At that model, the four assumptions say so (see the
module's documentation). -/
def Corresponds (ops : Ops IO) (M : Model) (view : Void IO.RealWorld → M.World) : Prop :=
  (∀ path, Agrees view (ops.symlinkMetadata path) (M.ops.symlinkMetadata path)) ∧
    (∀ path, Agrees view (ops.realPath path) (M.ops.realPath path)) ∧
    (∀ path, Agrees view (ops.removeDirAll path) (M.ops.removeDirAll path)) ∧
    (∀ path, Agrees view (ops.removeFile path) (M.ops.removeFile path))

/-- The model action over the worlds of `IO` that runs the `EIO` action `x`. -/
def ofEIO {ε α : Type} (x : EIO ε α) : EStateM ε (Void IO.RealWorld) α := fun w =>
  match x w with
  | .ok a w' => .ok a w'
  | .error e w' => .error e w'

/-- The model whose states are the worlds of `IO`, whose operations are those of `ops` run over
them, and whose reads are `entry` and `real`. -/
def Model.ofIO (ops : Ops IO) (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath) : Model where
  World := Void IO.RealWorld
  entry := entry
  real := real
  ops := {
    symlinkMetadata := fun path => ofEIO (ops.symlinkMetadata path)
    realPath := fun path => ofEIO (ops.realPath path)
    removeDirAll := fun path => ofEIO (ops.removeDirAll path)
    removeFile := fun path => ofEIO (ops.removeFile path) }

/-- An `EIO` action runs as itself over the worlds of `IO`, each world read as itself. -/
theorem ofEIO_agrees {ε α : Type} (x : EIO ε α) : Agrees id x (ofEIO x) := by
  intro w
  cases ran : x w with
  | ok a w' => simp only [ofEIO, EStateM.run, id, ran]
  | error e w' => simp only [ofEIO, EStateM.run, id, ran]

/-- Every set of operations in `IO` corresponds to the model whose states are the worlds of `IO`,
each world read as itself. So a theorem about the runs of operations in `IO` at this model rests
only on the assumptions it names at it: that the operations satisfy them is the part that is
trusted. -/
theorem corresponds_ofIO (ops : Ops IO)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath) :
    Corresponds ops (Model.ofIO ops entry real) id :=
  ⟨fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _,
    fun _ => ofEIO_agrees _⟩

/-! ## Reads -/

/-- The type of the entry at `path`, by a read that follows no symbolic link at `path` itself, or
`none` when nothing is there. Any other failure of the read is thrown. No code that Regula runs
calls it yet: the next stage of issue #362 replaces it by writing the operations of
`Regula.Removal` over `Ops`. -/
def entryType {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m (Option IO.FS.FileType) :=
  tryCatchThe IO.Error (do return some (← ops.symlinkMetadata path).type) fun
    | .noFileOrDirectory .. => pure none
    | error => throw error

/-- Whether the real path of `path` is `path` itself: `false` when it is another path, and when
`path` has none. No code that Regula runs calls it yet: the next stage of issue #362 replaces it by
writing the operations of `Regula.Removal` over `Ops`. -/
def atOwnPlace {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Bool :=
  tryCatchThe IO.Error (do return (← ops.realPath path) == path) fun _ => pure false

/-- A run of `entryType` gives the model's entry at the path and changes nothing. When it fails,
nothing changed. -/
theorem entryType_run (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
    Satisfies ((entryType M.ops path).run before)
      (fun found w => w = before ∧ found = M.entry before path)
      (fun _ w => w = before) := by
  have h := (triple_iff _ _ _ _).mp (reads path before) before rfl
  simp only [entryType, run_tryCatch, EStateM.run_bind, EStateM.run_pure]
  revert h
  cases (M.ops.symlinkMetadata path).run before with
  | ok metadata w => intro h; exact ⟨h.1, h.2.symm⟩
  | error e w => intro h; cases e <;> simp_all [Satisfies, Absent, EStateM.run_pure, run_throw]

/-- A run of `atOwnPlace` never fails, changes nothing, and gives `true` exactly when the real
path of the path is the path. -/
theorem atOwnPlace_run (M : Model) (reads : ReadsReal M) (path : FilePath) (before : M.World) :
    Satisfies ((atOwnPlace M.ops path).run before)
      (fun same w => w = before ∧ (same = true ↔ M.real before path = some path))
      (fun _ _ => False) := by
  have h := (triple_iff _ _ _ _).mp (reads path before) before rfl
  simp only [atOwnPlace, run_tryCatch, EStateM.run_bind, EStateM.run_pure]
  revert h
  cases (M.ops.realPath path).run before with
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
something is still there. No code that Regula runs calls it yet: the next stage of issue #362
replaces it by writing the operations of `Regula.Removal` over `Ops`. -/
def removeDirectory {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  ops.removeDirAll path
  confirmGone ops path

/-- Remove the entry at `path`, which is not a directory, then read `path` again, and fail when
something is still there. No code that Regula runs calls it yet: the next stage of issue #362
replaces it by writing the operations of `Regula.Removal` over `Ops`. -/
def removeEntry {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  ops.removeFile path
  confirmGone ops path

/-- A run of an action `removal` followed by `confirmGone` ends with nothing at the path when it
succeeds. It ends in a state of `Q` when `removal` succeeds and of `E` when `removal` fails, as the
runs of `removal` do. -/
theorem confirmed_run (M : Model) (reads : ReadsEntry M) (path : FilePath)
    (removal : EStateM IO.Error M.World Unit) (before : M.World) (Q E : M.World → Prop)
    (removed : Satisfies (removal.run before) (fun _ w => Q w) (fun _ w => E w)) :
    Satisfies ((do removal; confirmGone M.ops path : EStateM IO.Error M.World Unit).run before)
      (fun _ w => M.entry w path = none ∧ Q w) (fun _ w => Q w ∨ E w) := by
  simp only [EStateM.run_bind]
  revert removed
  cases removal.run before with
  | ok _ w =>
    intro removed
    have h := confirmGone_run M reads path w
    revert h
    simp only [Satisfies] at removed ⊢
    cases (confirmGone M.ops path).run w with
    | ok _ w' => intro h; rw [h.1]; exact ⟨h.2, removed⟩
    | error _ w' => intro h; rw [h]; exact .inl removed
  | error _ w => intro removed; exact .inr removed
where
  /-- A run of `confirmGone` changes nothing, and succeeds only when nothing is at the path. -/
  confirmGone_run (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
      Satisfies ((confirmGone M.ops path).run before)
        (fun _ w => w = before ∧ M.entry before path = none) (fun _ w => w = before) := by
    have h := entryType_run M reads path before
    simp only [confirmGone, EStateM.run_bind]
    revert h
    cases (entryType M.ops path).run before with
    | ok found w =>
      intro h
      cases found with
      | none => exact ⟨h.1, h.2.symm⟩
      | some _ => exact h.1
    | error e w => intro h; exact h

/-- **Checked:** when `removeDirectory` succeeds, nothing is at the path. This rests only on
`ReadsEntry`, whatever `removeDirAll` does. -/
theorem removeDirectory_gone (M : Model) (reads : ReadsEntry M) (path : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ removeDirectory M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    have h := confirmed_run M reads path (M.ops.removeDirAll path) before (fun _ => True)
      (fun _ => True) (by unfold Satisfies; split <;> trivial)
    revert h
    show Satisfies ((removeDirectory M.ops path).run before) _ _ → _
    unfold Satisfies
    split
    · exact fun h => h.1
    · exact fun _ => trivial

/-- **Checked:** when `removeEntry` succeeds, nothing is at the path. This rests only on
`ReadsEntry`, whatever `removeFile` does. -/
theorem removeEntry_gone (M : Model) (reads : ReadsEntry M) (path : FilePath) :
    ⦃fun _ => ⌜True⌝⦄ removeEntry M.ops path
      ⦃post⟨fun _ w => ⌜M.entry w path = none⌝, fun _ _ => ⌜True⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun before _ => by
    have h := confirmed_run M reads path (M.ops.removeFile path) before (fun _ => True)
      (fun _ => True) (by unfold Satisfies; split <;> trivial)
    revert h
    show Satisfies ((removeEntry M.ops path).run before) _ _ → _
    unfold Satisfies
    split
    · exact fun h => h.1
    · exact fun _ => trivial

attribute [regula_checked filesystem removeDirectory_gone
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")] removeDirectory

attribute [regula_checked filesystem removeEntry_gone
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")] removeEntry

/-- `removeDirectory` of a directory at its own place removes it and keeps the type of each entry
outside it; when it fails, it kept the type of each entry outside it. -/
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
    show Satisfies ((removeDirectory M.ops path).run s) _ _ → _
    unfold Satisfies
    split
    · exact id
    · exact fun h => h.elim id id

/-- `removeEntry` of a path at its own place removes it and keeps the type of each entry outside
it; when it fails, it kept the type of each entry outside it. -/
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
    show Satisfies ((removeEntry M.ops path).run s) _ _ → _
    unfold Satisfies
    split
    · exact id
    · exact fun h => h.elim id id

/-! ## The functions in `IO` -/

section IO

variable {ops : Ops IO} {M : Model} {view : Void IO.RealWorld → M.World}

/-- `entryType` at operations that correspond to a model runs as `entryType` in the model. -/
theorem entryType_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (entryType ops path) (entryType M.ops path) := by
  unfold entryType
  refine Agrees.tryCatch (Agrees.bind (corresponds.1 path) fun _ => Agrees.pure view _) ?_
  intro error
  cases error <;> first | exact Agrees.pure view none | exact Agrees.throw view _

/-- `atOwnPlace` at operations that correspond to a model runs as `atOwnPlace` in the model. -/
theorem atOwnPlace_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (atOwnPlace ops path) (atOwnPlace M.ops path) :=
  Agrees.tryCatch (Agrees.bind (corresponds.2.1 path) fun _ => Agrees.pure view _)
    fun _ => Agrees.pure view false

/-- `confirmGone` at operations that correspond to a model runs as `confirmGone` in the model. -/
theorem confirmGone_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (confirmGone ops path) (confirmGone M.ops path) := by
  refine Agrees.bind (entryType_agrees corresponds path) fun found => ?_
  cases found <;> first | exact Agrees.pure view _ | exact Agrees.throw view _

/-- `removeDirectory` at operations that correspond to a model runs as `removeDirectory` in the
model. -/
theorem removeDirectory_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (removeDirectory ops path) (removeDirectory M.ops path) :=
  Agrees.bind (corresponds.2.2.1 path) fun _ => confirmGone_agrees corresponds path

/-- `removeEntry` at operations that correspond to a model runs as `removeEntry` in the model. -/
theorem removeEntry_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (removeEntry ops path) (removeEntry M.ops path) :=
  Agrees.bind (corresponds.2.2.2 path) fun _ => confirmGone_agrees corresponds path

/-- **Checked, in `IO`:** when `removeDirectory` succeeds at operations that correspond to a model,
nothing is at the path in the state the world it ends in is read as (`removeDirectory_gone`). -/
theorem removeDirectory_gone_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeDirectory ops path w) (fun _ s => M.entry s path = none) (fun _ _ => True) :=
  (removeDirectory_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp (removeDirectory_gone M reads path) (view w) trivial)

/-- **Checked, in `IO`:** when `removeEntry` succeeds at operations that correspond to a model,
nothing is at the path in the state the world it ends in is read as (`removeEntry_gone`). -/
theorem removeEntry_gone_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeEntry ops path w) (fun _ s => M.entry s path = none) (fun _ _ => True) :=
  (removeEntry_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp (removeEntry_gone M reads path) (view w) trivial)

/-- `removeDirectory` in `IO`, at operations that correspond to a model, of a directory at its own
place removes it and keeps the type of each entry outside it; when it fails, it kept the type of
each entry outside it (`removeDirectory_spec`). -/
theorem removeDirectory_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (removes : RemovesTree M) (path : FilePath) (w : Void IO.RealWorld)
    (directory : M.entry (view w) path = some .dir) (own : M.real (view w) path = some path) :
    RunsTo view (removeDirectory ops path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s)
      (fun _ s => M.Unchanged path (view w) s) :=
  (removeDirectory_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp
      (removeDirectory_spec M reads removes path (view w) directory own) (view w) rfl)

/-- `removeEntry` in `IO`, at operations that correspond to a model, of a path at its own place
removes it and keeps the type of each entry outside it; when it fails, it kept the type of each
entry outside it (`removeEntry_spec`). -/
theorem removeEntry_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (removes : RemovesEntry M) (path : FilePath) (w : Void IO.RealWorld)
    (own : M.real (view w) path = some path) :
    RunsTo view (removeEntry ops path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s)
      (fun _ s => M.Unchanged path (view w) s) :=
  (removeEntry_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp (removeEntry_spec M reads removes path (view w) own) (view w) rfl)

/-- `atOwnPlace` in `IO`, at operations that correspond to a model, never fails, ends in a world
read as the same state, and gives `true` exactly when the real path of the path is the path
(`atOwnPlace_spec`). -/
theorem atOwnPlace_io (corresponds : Corresponds ops M view) (reads : ReadsReal M)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (atOwnPlace ops path w)
      (fun same s => s = view w ∧ (same = true ↔ M.real (view w) path = some path))
      (fun _ _ => False) :=
  (atOwnPlace_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp (atOwnPlace_spec M reads path (view w)) (view w) rfl)

end IO

end Regula.Filesystem
