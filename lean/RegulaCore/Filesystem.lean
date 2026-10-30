import RegulaCore.StateTriple
import Regula.Contract
import Regula.Assumption

/-! # The filesystem, as Regula's code acts on it

The operations by which the copy construction reads the filesystem (`Ops`), and the assumptions it
makes about them, each a predicate over a model of the filesystem (`Model`). Code that acts on the
filesystem is written once, for the operations in any monad. It runs at the real operations, which
the observer supplies in `IO` (`Regula.Filesystem.observer`). Its theorems are stated at the
operations of every model that satisfies the assumptions they name, so the hypotheses of a theorem
are exactly the assumptions it rests on.

## The model

A model has a type of states, three reads that give the vocabulary of the assumptions, and the
operations as actions on the state:

* `Model.entry`: the type of the entry that a path names, as `lstat(2)` reports it, which does
  not follow a symbolic link at the path's last component;
* `Model.real`: what `realpath(3)` resolves a path to, which is absolute and has no `.` or `..`
  component and no symbolic link;
* `Model.ident`: the file that a path names (`FileId`), its device and its number on the device,
  as `lstat(2)` reports them. Lean 4.35.0's `IO.FS.Metadata` has neither
  (`Init/System/IO.lean#L1115-L1129`), so no operation reads it and no decision depends on it.

## The assumptions

Each assumption is a predicate with the sources that state it (`Regula.Assumption`), a `Std.Do`
triple whose postcondition is the property:

* `ReadsEntry`: `symlinkMetadata` reports the entry, changes nothing, and fails with
  `noFileOrDirectory` only when nothing is there.
* `ReadsReal`: `realPath` gives what `realpath(3)` gives, changes nothing, and fails exactly when
  `realpath(3)` fails.

Each is a statement about every run from every state, so together they describe runs in which no
other process changes the filesystem, which none states alone. A read changes nothing, so a change
during a read makes its assumption false, and the theorems that rest on a false assumption say
nothing.

## From the model to `IO`

Each operation in `IO` runs as the model's operation when each world of `IO` is read as a model
state (`Corresponds`). That is agreement of runs, not an assumption about the filesystem:
`corresponds_ofIO` proves it for every set of operations at the model whose states are the worlds
(`Model.ofIO`).

## Boundaries

The assumptions are stated for a POSIX system, where `symlinkMetadata` calls `lstat` and `realPath`
calls `realpath`. In Lean 4.35.0 on Windows, `symlinkMetadata` follows a link and `realPath` can
give a path it did not resolve, so the observer refuses those reads there. -/

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

/-- The identity of a file: the device that holds it and its number on that device, the fields
`st_dev` and `st_ino` that `lstat(2)` reports. POSIX.1-2024 `<sys/stat.h>` states that the two
together identify the file within the system. -/
structure FileId where
  /-- The device that holds the file: `st_dev`. -/
  device : Nat
  /-- The number of the file on its device: `st_ino`. -/
  inode : Nat

/-- A model of the filesystem: its states, what the three reads report in each state, and the
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
  /-- The file that a path names in a state, as `lstat(2)` reports its device and number: a
  symbolic link at the path's last component is the file, not followed. `none` when nothing is
  there. Lean 4.35.0's `IO.FS.Metadata` has no device or inode field
  (`Init/System/IO.lean#L1115-L1129`), so no operation reads it and no decision depends on it: it
  is what a statement about a file names. -/
  ident : World → FilePath → Option FileId
  /-- The operations, as actions on the state. -/
  ops : Ops (EStateM IO.Error World)

/-- The tree of `directory` in the state `w`: `directory` itself, and each path whose last
component is a name, not `.` or `..`, and whose parent is in the tree and is a directory as
`lstat(2)` reports it. It includes each entry that a walk that follows no link visits
in a run where no other process changes the filesystem. It also
holds each name with no entry in a directory of the tree, and each other spelling of a visited
entry, such as another case of its name on a volume that ignores case. As `lstat(2)` reports them,
neither adds a file to the files of the tree: the first names no file, and the second names the
file of the entry it spells. The tree goes into no symbolic link, whose own entry is not a
directory, and has no `..` path. -/
inductive Model.Below (M : Model) (w : M.World) (directory : FilePath) : FilePath → Prop where
  /-- A directory is in its own tree. -/
  | self : Model.Below M w directory directory
  /-- A name in a directory of the tree is in the tree. -/
  | child {path parent : FilePath} : Model.Below M w directory parent →
      M.entry w parent = some .dir → path.parent = some parent → path.fileName.isSome = true →
      Model.Below M w directory path

/-- Whether an error is the one that Lean gives for `ENOENT`: nothing is at the path. -/
def Absent : IO.Error → Prop
  | .noFileOrDirectory .. => True
  | _ => False

/-- `symlinkMetadata` reports the type of the entry at the path and changes nothing. It fails with
`noFileOrDirectory` only when nothing is there. It can also fail in other ways when nothing is
there, for example with `ENOTDIR` when a component of the path is not a directory. -/
@[regula_assumption filesystem
  (lean "v4.35.0" "Init/System/IO.lean#L1151-L1156")
  (lean "v4.35.0" "runtime/io.cpp#L1160-L1179")
  (lean "v4.35.0" "runtime/io.cpp#L276-L279")
  (document filesystem "POSIX.1-2024, lstat()")]
def ReadsEntry (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.symlinkMetadata path
    ⦃post⟨fun metadata w => ⌜w = before ∧ M.entry before path = some metadata.type⌝,
      fun error w => ⌜w = before ∧ (Absent error → M.entry before path = none)⌝⟩⦄

/-- `realPath` gives what `realpath(3)` resolves the path to and changes nothing. It fails exactly
when `realpath(3)` fails. On Windows, Lean 4.35.0's `realPath` gives the path itself when it cannot
resolve it (`runtime/io.cpp#L1032-L1033`), so the observer refuses it there.

On a volume that ignores case or Unicode normalization, Darwin's `realpath(3)` gives the name that
the volume stores for each component, as its source below states, and it was observed once on
macOS 27.0.1 (APFS), where `realpath dir/FILE` printed `.../Dir/file`. It keeps a name as written
on a volume where `getattrlist(2)` is not supported, where it falls back to `lstat(2)`
(`realpath.c#L238-L243`), and glibc's keeps it in a Linux directory that folds case. -/
@[regula_assumption filesystem
  (lean "v4.35.0" "Init/System/IO.lean#L873-L879")
  (lean "v4.35.0" "runtime/io.cpp#L1054-L1066")
  (document filesystem "POSIX.1-2024, realpath()")
  (document filesystem "Apple Libc-1752.120.2, stdlib/FreeBSD/realpath.c#L216-L243 and \
    #L348-L358: Darwin's realpath(3) replaces each path component with the name that \
    getattrlist(2) reads from the volume")]
def ReadsReal (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.realPath path
    ⦃post⟨fun real w => ⌜w = before ∧ M.real before path = some real⌝,
      fun _ w => ⌜w = before ∧ M.real before path = none⌝⟩⦄

/-! ## Operations in `IO` that correspond to a model -/

/-- The operations `ops` in `IO` run as the operations of the model `M`, when `view` reads each
world of `IO` as a state of `M` (`Regula.StateTriple.Agrees`): from each world, an operation of
`ops` has the outcome of the model's operation from the view of that world, and the view of the
world it ends in is the state the model's operation ends in.

This is agreement of runs, not a property of the filesystem, so it has no role: `corresponds_ofIO`
proves it for every set of operations at the model whose states are the worlds. It does not say
that no other process changes the filesystem. At that model, the assumptions describe runs in
which no other process changes it (see the module's documentation). -/
def Corresponds (ops : Ops IO) (M : Model) (view : Void IO.RealWorld → M.World) : Prop :=
  (∀ path, Agrees view (ops.symlinkMetadata path) (M.ops.symlinkMetadata path)) ∧
    (∀ path, Agrees view (ops.realPath path) (M.ops.realPath path))

/-- The model action over the worlds of `IO` that runs the `EIO` action `x`. -/
def ofEIO {ε α : Type} (x : EIO ε α) : EStateM ε (Void IO.RealWorld) α := fun w =>
  match x w with
  | .ok a w' => .ok a w'
  | .error e w' => .error e w'

/-- The model whose states are the worlds of `IO`, whose operations are those of `ops` run over
them, and whose reads are `entry`, `real` and `ident`. -/
def Model.ofIO (ops : Ops IO) (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId) : Model where
  World := Void IO.RealWorld
  entry := entry
  real := real
  ident := ident
  ops := {
    symlinkMetadata := fun path => ofEIO (ops.symlinkMetadata path)
    realPath := fun path => ofEIO (ops.realPath path) }

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
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId) :
    Corresponds ops (Model.ofIO ops entry real ident) id :=
  ⟨fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _⟩

/-! ## Reads -/

/-- The type of the entry at `path`, by a read that follows no symbolic link at `path` itself, or
`none` when nothing is there. Any other failure of the read is thrown. -/
def entryType {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m (Option IO.FS.FileType) :=
  tryCatchThe IO.Error (do return some (← ops.symlinkMetadata path).type) fun
    | .noFileOrDirectory .. => pure none
    | error => throw error

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

/-- `entryType` gives the model's entry at the path and changes nothing. When it fails, nothing
changed. -/
theorem entryType_spec (M : Model) (reads : ReadsEntry M) (path : FilePath) (before : M.World) :
    ⦃fun w => ⌜w = before⌝⦄ entryType M.ops path
      ⦃post⟨fun found w => ⌜w = before ∧ found = M.entry before path⌝,
        fun _ w => ⌜w = before⌝⟩⦄ :=
  (triple_iff _ _ _ _).mpr fun _ same => same ▸ entryType_run M reads path before

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

/-- When the read of `path` that follows no link gives `metadata`, `entryType` gives its type and
ends where the read ends. -/
theorem entryType_ok {path : FilePath} {w s : Void IO.RealWorld} {metadata : IO.FS.Metadata}
    (read : ops.symlinkMetadata path w = .ok metadata s) :
    entryType ops path w = .ok (some metadata.type) s := by
  unfold entryType
  exact eio_tryCatch_ok (by rw [eio_bind_ok read]; exact eio_pure _ _) _

/-- When the read of `path` that follows no link fails with an error that does not say that
nothing is there, `entryType` fails with that same error and ends where the read ends. -/
theorem entryType_error {path : FilePath} {w s : Void IO.RealWorld} {error : IO.Error}
    (read : ops.symlinkMetadata path w = .error error s) (other : ¬Absent error) :
    entryType ops path w = .error error s := by
  unfold entryType
  rw [eio_tryCatch_error (eio_bind_error read _)]
  cases error <;> first | exact absurd trivial other | exact eio_throw _ _

end IO

end Regula.Filesystem
