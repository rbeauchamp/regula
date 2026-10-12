import RegulaCore.StateTriple
import Regula.Contract
import Regula.Assumption

/-! # The filesystem, as Regula's code acts on it

The operations by which Regula's code reads the filesystem, removes from it and moves an entry in
it (`Ops`), and the assumptions it makes about them, each a predicate over a model of the
filesystem (`Model`). Code that acts on the filesystem is written once, for the operations in any
monad. It runs at the real operations, which the observer supplies in `IO`
(`Regula.Filesystem.observer`). Its theorems are stated at the operations of every model that
satisfies the assumptions they name, so the hypotheses of a theorem are exactly the assumptions it
rests on. The operations that decide before they remove or move are in `RegulaCore.Removal`.

## The model

A model has a type of states, four reads that give the vocabulary of the assumptions, and the
operations as actions on the state:

* `Model.entry`: the type of the entry that a path names, as `lstat(2)` reports it, which does
  not follow a symbolic link at the path's last component;
* `Model.real`: what `realpath(3)` resolves a path to, which is absolute and has no `.` or `..`
  component and no symbolic link;
* `Model.ident`: the file that a path names (`FileId`), its device and its number on the device,
  as `lstat(2)` reports them. Lean 4.34.1's `IO.FS.Metadata` has neither
  (`Init/System/IO.lean#L1115-L1129`), so no operation reads it and no decision depends on it: it
  names the files that the frame of a removal speaks about (`Model.Unchanged`).
* `Model.names`: the names that a directory holds, as `readdir(3)` reports them, without `.` and
  `..`. They give the tree of a directory as a walk that lists each directory reads it
  (`Model.Listed`).

## The assumptions

Each assumption is a predicate with the sources that state it (`Regula.Assumption`). The six are
the contracts of the operations, each a `Std.Do` triple whose postcondition is the property:

* `ReadsEntry`: `symlinkMetadata` reports the entry, changes nothing, and fails with
  `noFileOrDirectory` only when nothing is there.
* `ReadsReal`: `realPath` gives what `realpath(3)` gives, changes nothing, and fails exactly when
  `realpath(3)` fails.
* `RemovesTree`: `removeDirAll` of a directory at its own place keeps the entry at each path of
  its frame (`Model.Unchanged`), each path not spelled within the directory, below a parent at its
  own real path, whose file before is not an entry of the directory's tree (`Model.Below`),
  whether it succeeds or fails.
* `RemovesEntry`: `removeFile` of a path at its own place, or of a symbolic link in a directory at
  its own place, keeps the entry at each path of its frame, each path not spelled within the
  removed path, below a parent at its own real path, whose file before is not the removed one.
* `Renames`: `rename` of a source at its own place to a destination whose parent is at its own
  place keeps the entry at each path of the frame of both (`Model.Kept`).
* `ListsEntries`: `readDir` of a directory lists each name that it holds and changes nothing.

Each is a statement about every run from every state, so together they describe runs in which no
other process changes the filesystem, which none states alone. In `IO`, the world that one
operation ends in is the world that the next starts from, so a change that another process makes
while the code runs is part of the run of one operation. A read changes nothing, so a change during
a read makes its assumption false. A removal keeps the entry at each path of its frame, so a change
during a removal to an entry that the frame keeps makes its assumption false. A change inside the
removed tree can make `RemovesTree` false too, since `removeDirAll` resolves each path again
(`RemovesTree`). The theorems that rest on a false assumption say nothing.

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
rest on the six assumptions alone.

## Boundaries

The assumptions are stated for a POSIX system, where `symlinkMetadata` calls `lstat`,
`removeDirAll` reads each entry without following a symbolic link, and `realPath` calls
`realpath`. In Lean 4.34.1 on Windows, `symlinkMetadata` follows a link and `realPath` can give a
path it did not resolve, so the observer refuses those reads and every directory removal there.

The frame of a removal (`Model.Unchanged`) leaves out each path that names, before the removal,
the file of an entry of the removed tree (`Model.Below`, which includes the entries that
`removeDirAll` visits):
the same device and file number, which together identify a file within the system (POSIX.1-2024
`<sys/stat.h>`). So it leaves out every second name of such a file, whatever gives it: another
case or Unicode normalization of a name on a volume that ignores those, an APFS firmlink, a bind
mount, or a second hard link. It also leaves out each path spelled within the removed path
(`Within`), and each path whose parent is not its own real path, such as one through a symbolic
link or with a `..` component, since such a path can pass through the removed path. The target of
a symbolic link in the tree is not an entry of the tree through the link, so its entry is in the
frame unless the tree holds it under another name. The removal assumptions are
false where two names of one file report different devices, such as two mounts of one network or
FUSE file system, and on a file system whose file numbers are not stable. `RemovesTree` is false
too when another process, during the removal, replaces a directory of the tree with a symbolic link
or otherwise changes what a path of the tree resolves to: `removeDirAll` resolves each path again
at each call, so the walk can leave the tree, the race of CVE-2022-21658. The frame compares the
type of an entry, not which file it is after the removal or what it holds: an entry outside a
removed path that is replaced by another entry of the same type is not a change the frame sees. -/

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
  /-- Move the entry at the first path to the second, replacing what is there: `IO.FS.rename`. -/
  rename : FilePath → FilePath → m Unit
  /-- The entries of a directory: `System.FilePath.readDir`. -/
  readDir : FilePath → m (Array IO.FS.DirEntry)

/-- The identity of a file: the device that holds it and its number on that device, the fields
`st_dev` and `st_ino` that `lstat(2)` reports. POSIX.1-2024 `<sys/stat.h>` states that the two
together identify the file within the system. -/
structure FileId where
  /-- The device that holds the file: `st_dev`. -/
  device : Nat
  /-- The number of the file on its device: `st_ino`. -/
  inode : Nat

/-- A model of the filesystem: its states, what the four reads report in each state, and the
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
  there. Lean 4.34.1's `IO.FS.Metadata` has no device or inode field
  (`Init/System/IO.lean#L1115-L1129`), so no operation reads it and no decision depends on it: it
  names the files that the frame of a removal speaks about (`Model.Unchanged`). -/
  ident : World → FilePath → Option FileId
  /-- The names of the entries that a directory holds in a state, as `readdir(3)` reports them,
  without `.` and `..`. It is read only for a path whose entry is a directory (`ListsEntries`). -/
  names : World → FilePath → List String
  /-- The operations, as actions on the state. -/
  ops : Ops (EStateM IO.Error World)

/-- `path` is spelled within `directory`: it is `directory`, or its parent
(`System.FilePath.parent`) is spelled within `directory`. This is a relation of spellings, not of
files: a path with a `..` component, such as `directory/..`, or one through a symbolic link below
`directory` is within it and can name a file outside it. The tree of `directory`, which includes
the entries that `removeDirAll` visits, is `Model.Below`. -/
inductive Within (directory : FilePath) : FilePath → Prop where
  /-- A directory is within itself. -/
  | self : Within directory directory
  /-- A path whose parent is within the directory is within it. -/
  | entry {path parent : FilePath} :
      Within directory parent → path.parent = some parent → Within directory path

/-- The tree of `directory` in the state `w`: `directory` itself, and each path whose last
component is a name, not `.` or `..`, and whose parent is in the tree and is a directory as
`lstat(2)` reports it. It includes each entry that Lean 4.34.1's `IO.FS.removeDirAll` visits
(`Init/System/IO.lean#L1335-L1342`) in a run where no other process changes the filesystem. It also
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

/-- The listed tree of `root` in the state `w`: `root` itself, and the path of each name that a
directory of the tree holds (`Model.names`), joined to it as `System.FilePath.readDir` joins it
(`IO.FS.DirEntry.path`). A directory of the tree is one whose entry `lstat(2)` reports as a
directory, so the tree goes into no symbolic link. It is the tree that a walk which lists each
directory that it reads finds (`otherEntries`). Unlike `Model.Below`, it holds each entry by the
one name that its directory holds, not by another spelling of it. -/
inductive Model.Listed (M : Model) (w : M.World) (root : FilePath) : FilePath → Prop where
  /-- A path is in its own listed tree. -/
  | self : Model.Listed M w root root
  /-- The path of a name that a directory of the tree holds is in the tree. -/
  | child {directory : FilePath} {name : String} : Model.Listed M w root directory →
      M.entry w directory = some .dir → name ∈ M.names w directory →
      Model.Listed M w root (directory / name)

/-- In the state `w`, the entry at `path` is a symbolic link or another kind of entry than a
directory and a regular file, such as a socket or a device, as `lstat(2)` reports it. -/
def Model.NotPlain (M : Model) (w : M.World) (path : FilePath) : Prop :=
  M.entry w path = some .symlink ∨ M.entry w path = some .other

/-- A path of the listed tree of `directory` is `directory`, or it is in the listed tree of the
path of a name that `directory` holds, when `directory` is a directory. -/
theorem Model.Listed.first {M : Model} {w : M.World} {directory path : FilePath}
    (listed : M.Listed w directory path) : path = directory ∨
      M.entry w directory = some .dir ∧
        ∃ name ∈ M.names w directory, M.Listed w (directory / name) path := by
  induction listed with
  | self => exact .inl rfl
  | @child parent name _ isDir held ih =>
    rcases ih with same | ⟨top, first, firstHeld, below⟩
    · subst same
      exact .inr ⟨isDir, name, held, .self⟩
    · exact .inr ⟨top, first, firstHeld, .child below isDir held⟩

/-- From the state `before` to the state `after`, the entry at each path of the frame of the paths
`changed` kept its type. The frame is each path that is not spelled within any of them (`Within`),
whose parent is its own real path in `before`, whose last component is a name, not `.` or `..`, and
that in `before` names nothing or names a file (`Model.ident`) that no entry of the tree of any of
them (`Model.Below`) is. Each such path names an entry of the same type in both states, or nothing
in both.

A path that names, in `before`, the file of an entry of a tree is outside the frame: a second name
of that file, such as another case or Unicode normalization of a name on a volume that ignores
those, a name through an APFS firmlink or a bind mount, or a second hard link. A path whose parent
is not its own real path is outside the frame too, since it can pass through a changed path: one
through a symbolic link, or with a `.` or `..` component. The target of a symbolic link below a
changed path is not an entry of its tree through the link, so unless a tree holds it under another
name, its entry is in the frame. A path that names nothing is in the frame, so nothing appears
outside the changed paths. The frame compares the type of each entry, not which file it is in
`after` or what it holds. -/
def Model.Kept (M : Model) (changed : List FilePath) (before after : M.World) : Prop :=
  ∀ path parent, path.parent = some parent → path.fileName.isSome = true →
    M.real before parent = some parent →
    (M.entry before path = none ∨ ∃ file, M.ident before path = some file ∧
      ∀ directory ∈ changed, ∀ inner, M.Below before directory inner →
        M.ident before inner ≠ some file) →
    (∀ directory ∈ changed, ¬ Within directory path) → M.entry after path = M.entry before path

/-- The frame of the removal of `directory` (`Model.Kept`): from `before` to `after`, the entry at
each path not spelled within `directory`, below a parent at its own real path, whose file before is
not an entry of the tree of `directory` (`Model.Below`), kept its type. -/
def Model.Unchanged (M : Model) (directory : FilePath) (before after : M.World) : Prop :=
  M.Kept [directory] before after

/-- Nothing changes from a state to itself. -/
theorem Model.kept_refl (M : Model) (changed : List FilePath) (w : M.World) :
    M.Kept changed w w :=
  fun _ _ _ _ _ _ _ => rfl

/-- Nothing changes from a state to itself. -/
theorem Model.unchanged_refl (M : Model) (directory : FilePath) (w : M.World) :
    M.Unchanged directory w w :=
  M.kept_refl [directory] w

/-- In the state `w`, the last component of `path` is a name, not `.` or `..`, and the parent of
`path` is its own real path: the entry that `path` names is the one of that name in a directory at
its own place, reached through no symbolic link. A symbolic link at `path` is in its own directory
in this sense whatever it points to, since `lstat(2)` and `unlink(2)` do not follow a link at the
last component of a path. -/
def Model.InOwnDirectory (M : Model) (w : M.World) (path : FilePath) : Prop :=
  path.fileName.isSome = true ∧ ∃ parent, path.parent = some parent ∧ M.real w parent = some parent

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
resolve it (`runtime/io.cpp#L1032-L1033`), so the observer refuses it there.

On a volume that ignores case or Unicode normalization, Darwin's `realpath(3)` gives the name that
the volume stores for each component, as its source below states, and it was observed once on
macOS 27.0.1 (APFS), where `realpath dir/FILE` printed `.../Dir/file`. It keeps a name as written
on a volume where `getattrlist(2)` is not supported, where it falls back to `lstat(2)`
(`realpath.c#L238-L243`), and glibc's keeps it in a Linux directory that folds case. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L873-L879")
  (lean "v4.34.1" "runtime/io.cpp#L1054-L1066")
  (document filesystem "POSIX.1-2024, realpath()")
  (document filesystem "Apple Libc-1752.120.2, stdlib/FreeBSD/realpath.c#L216-L243 and \
    #L348-L358: Darwin's realpath(3) replaces each path component with the name that \
    getattrlist(2) reads from the volume")]
def ReadsReal (M : Model) : Prop :=
  ∀ path before, ⦃fun w => ⌜w = before⌝⦄ M.ops.realPath path
    ⦃post⟨fun real w => ⌜w = before ∧ M.real before path = some real⌝,
      fun _ w => ⌜w = before ∧ M.real before path = none⌝⟩⦄

/-- `removeDirAll` of a directory at its own place, whose real path is the path, keeps the entry at
each path of its frame (`Model.Unchanged`), each path not spelled within the directory, below a
parent at its own real path, whose file before is not an entry of the directory's tree
(`Model.Below`), whether it succeeds or fails. That it removes the directory is not assumed
(`removeDirectory_gone`).

On a POSIX system it reads each entry with `lstat` and goes only into a directory, so the tree has
a symbolic link below the directory and not the link's target. So the target's entry is in the
frame, unless the tree holds it under another name, and in a run where no other process changes
the filesystem, the assumption gives that the removal removes the link, not its target.
The frame leaves out each second name of an entry of the tree, by the device and file number that
identify a file within the system (POSIX.1-2024 `<sys/stat.h>`): another spelling on a volume that
ignores case or Unicode normalization, a name through an APFS firmlink, a bind mount of the
directory or of a directory around it, and a second hard link to a file of the tree. A mount below
the directory is a directory of the tree, so the files below it are entries of the tree, and their
names at another mount of them are second names. The assumption is false where two names of one
file report different devices, such as two mounts of one network or FUSE file system, and on a file
system whose file numbers are not stable. It is false too when another process, during the
removal, replaces a directory of the tree with a symbolic link or otherwise changes what a path of
the tree resolves to: `removeDirAll` resolves each path again at each call
(`Init/System/IO.lean#L1335-L1342`), so the walk can leave the tree and remove entries outside it,
such as the target of the link (the race of CVE-2022-21658). -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L1330-L1342")
  (lean "v4.34.1" "runtime/io.cpp#L1160-L1179")
  (lean "v4.34.1" "runtime/io.cpp#L1197-L1207")
  (lean "v4.34.1" "runtime/io.cpp#L1351-L1364")
  (document filesystem "POSIX.1-2024, lstat(), unlink() and rmdir()")
  (document filesystem "POSIX.1-2024, <sys/stat.h>: st_ino and st_dev taken together uniquely \
    identify the file within the system")]
def RemovesTree (M : Model) : Prop :=
  ∀ path before, M.entry before path = some .dir → M.real before path = some path →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.removeDirAll path
      ⦃post⟨fun _ w => ⌜M.Unchanged path before w⌝, fun _ w => ⌜M.Unchanged path before w⌝⟩⦄

/-- `removeFile` of a path at its own place, whose real path is the path, or of a symbolic link in a
directory at its own place (`Model.InOwnDirectory`), keeps the entry at each path of its frame
(`Model.Unchanged`), each path not spelled within the removed path, below a parent at its own real
path, whose file before is not an entry of the path's tree (`Model.Below`), whether it succeeds or
fails. When the path is not a directory, its tree is the path alone. That it removes the entry is
not assumed (`removeEntry_gone`).

POSIX `unlink()` removes a symbolic link, not the file that its content names, so the target of a
removed link is in the frame unless it is a second name of the link itself.

The frame leaves out each second name of the removed file, by the device and file number that
identify a file within the system (POSIX.1-2024 `<sys/stat.h>`): another spelling on a volume that
ignores case or Unicode normalization, a name through an APFS firmlink or a bind mount, and a
second hard link. The assumption is false where two names of one file report different devices,
such as two mounts of one network or FUSE file system, and on a file system whose file numbers are
not stable. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L881-L886")
  (lean "v4.34.1" "runtime/io.cpp#L1351-L1364")
  (document filesystem "POSIX.1-2024, unlink()")
  (document filesystem "POSIX.1-2024, <sys/stat.h>: st_ino and st_dev taken together uniquely \
    identify the file within the system")]
def RemovesEntry (M : Model) : Prop :=
  ∀ path before, M.real before path = some path ∨
      M.entry before path = some .symlink ∧ M.InOwnDirectory before path →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.removeFile path
      ⦃post⟨fun _ w => ⌜M.Unchanged path before w⌝, fun _ w => ⌜M.Unchanged path before w⌝⟩⦄

/-- `rename` of a source at its own place, whose real path is the path, to a destination whose
parent is its own real path, keeps the entry at each path of the frame of both (`Model.Kept`): each
path spelled within neither, below a parent at its own real path, whose file before is not an entry
of the tree of either (`Model.Below`), whether it succeeds or fails. That it moves the entry is not
assumed (`Regula.Removal.replaceWith_moved`).

POSIX `rename()` follows no symbolic link at the last component of either path: a link at the
source is moved, and a link at the destination is replaced, not its target. The frame leaves out
each second name of the moved entry and of the replaced one, by the device and file number that
identify a file within the system (POSIX.1-2024 `<sys/stat.h>`), as for `RemovesEntry`. The
assumption is false where two names of one file report different devices, on a file system whose
file numbers are not stable, and when another process changes the parent of either path while the
rename runs. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L903-L909")
  (lean "v4.34.1" "runtime/io.cpp#L1209-L1238")
  (document filesystem "POSIX.1-2024, rename()")
  (document filesystem "POSIX.1-2024, <sys/stat.h>: st_ino and st_dev taken together uniquely \
    identify the file within the system")]
def Renames (M : Model) : Prop :=
  ∀ source destination parent before, M.real before source = some source →
    destination.parent = some parent → M.real before parent = some parent →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.rename source destination
      ⦃post⟨fun _ w => ⌜M.Kept [source, destination] before w⌝,
        fun _ w => ⌜M.Kept [source, destination] before w⌝⟩⦄

/-- `readDir` of a directory, as `lstat(2)` reports the entry at the path, lists each name that the
directory holds (`Model.names`), with the path as its directory, and changes nothing. When it
fails, it changed nothing. It may list more: a name that it lists and the directory does not hold
is read like any other.

Lean 4.34.1's `readDir` calls `opendir(3)` and then `readdir(3)` until it gives no entry, leaving
out `.` and `..` (`runtime/io.cpp#L1076-L1098`). It does not tell the end of the directory from an
error of `readdir(3)`, which also gives no entry, so a read that fails part way gives the names
read so far, and the assumption is false for it. POSIX leaves unspecified whether `readdir(3)`
gives a name added or removed after `opendir(3)`, so the assumption is false too when another
process changes the directory while it is read. -/
@[regula_assumption filesystem
  (lean "v4.34.1" "Init/System/IO.lean#L1068-L1079")
  (lean "v4.34.1" "Init/System/IO.lean#L1137-L1142")
  (lean "v4.34.1" "runtime/io.cpp#L1076-L1098")
  (document filesystem "POSIX.1-2024, opendir() and readdir()")]
def ListsEntries (M : Model) : Prop :=
  ∀ path before, M.entry before path = some .dir →
    ⦃fun w => ⌜w = before⌝⦄ M.ops.readDir path
      ⦃post⟨fun entries w => ⌜w = before ∧ ∀ name ∈ M.names before path,
          ∃ entry ∈ entries, entry.root = path ∧ entry.fileName = name⌝,
        fun _ w => ⌜w = before⌝⟩⦄

/-! ## Operations in `IO` that correspond to a model -/

/-- The operations `ops` in `IO` run as the operations of the model `M`, when `view` reads each
world of `IO` as a state of `M` (`Regula.StateTriple.Agrees`): from each world, an operation of
`ops` has the outcome of the model's operation from the view of that world, and the view of the
world it ends in is the state the model's operation ends in.

This is agreement of runs, not a property of the filesystem, so it has no role: `corresponds_ofIO`
proves it for every set of operations at the model whose states are the worlds. It does not say
that no other process changes the filesystem. At that model, the six assumptions describe runs in
which no other process changes it (see the module's documentation). -/
def Corresponds (ops : Ops IO) (M : Model) (view : Void IO.RealWorld → M.World) : Prop :=
  (∀ path, Agrees view (ops.symlinkMetadata path) (M.ops.symlinkMetadata path)) ∧
    (∀ path, Agrees view (ops.realPath path) (M.ops.realPath path)) ∧
    (∀ path, Agrees view (ops.removeDirAll path) (M.ops.removeDirAll path)) ∧
    (∀ path, Agrees view (ops.removeFile path) (M.ops.removeFile path)) ∧
    (∀ source destination,
      Agrees view (ops.rename source destination) (M.ops.rename source destination)) ∧
    (∀ path, Agrees view (ops.readDir path) (M.ops.readDir path))

/-- The model action over the worlds of `IO` that runs the `EIO` action `x`. -/
def ofEIO {ε α : Type} (x : EIO ε α) : EStateM ε (Void IO.RealWorld) α := fun w =>
  match x w with
  | .ok a w' => .ok a w'
  | .error e w' => .error e w'

/-- The model whose states are the worlds of `IO`, whose operations are those of `ops` run over
them, and whose reads are `entry`, `real`, `ident` and `names`. -/
def Model.ofIO (ops : Ops IO) (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) : Model where
  World := Void IO.RealWorld
  entry := entry
  real := real
  ident := ident
  names := names
  ops := {
    symlinkMetadata := fun path => ofEIO (ops.symlinkMetadata path)
    realPath := fun path => ofEIO (ops.realPath path)
    removeDirAll := fun path => ofEIO (ops.removeDirAll path)
    removeFile := fun path => ofEIO (ops.removeFile path)
    rename := fun source destination => ofEIO (ops.rename source destination)
    readDir := fun path => ofEIO (ops.readDir path) }

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
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) :
    Corresponds ops (Model.ofIO ops entry real ident names) id :=
  ⟨fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _, fun _ => ofEIO_agrees _,
    fun _ => ofEIO_agrees _, fun _ _ => ofEIO_agrees _, fun _ => ofEIO_agrees _⟩

/-! ## Reads -/

/-- The type of the entry at `path`, by a read that follows no symbolic link at `path` itself, or
`none` when nothing is there. Any other failure of the read is thrown. -/
def entryType {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m (Option IO.FS.FileType) :=
  tryCatchThe IO.Error (do return some (← ops.symlinkMetadata path).type) fun
    | .noFileOrDirectory .. => pure none
    | error => throw error

/-- Whether the real path of `path` is `path` itself: `false` when it is another path, and when
`path` has none. On a volume that ignores case or Unicode normalization, it is `false` for another
spelling of a stored name where `realpath(3)` gives the stored name, as Darwin's does, and `true`
where `realpath(3)` keeps the name as written (`ReadsReal`). -/
def atOwnPlace {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Bool :=
  tryCatchThe IO.Error (do return (← ops.realPath path) == path) fun _ => pure false

/-- The real path of `path`, or `none` when `realpath(3)` fails. -/
def realOf {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m (Option FilePath) :=
  tryCatchThe IO.Error (do return some (← ops.realPath path)) fun _ => pure none

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

/-- A run of `realOf` never fails, changes nothing, and gives the model's real path of the path. -/
theorem realOf_run (M : Model) (reads : ReadsReal M) (path : FilePath) (before : M.World) :
    Satisfies ((realOf M.ops path).run before)
      (fun found w => w = before ∧ found = M.real before path)
      (fun _ _ => False) := by
  have h := (triple_iff _ _ _ _).mp (reads path before) before rfl
  simp only [realOf, run_tryCatch, EStateM.run_bind, EStateM.run_pure]
  revert h
  cases (M.ops.realPath path).run before with
  | ok real w => intro h; exact ⟨h.1, h.2.symm⟩
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

/-! ## The entries of a tree other than directories and files -/

/-- Sort `entries` by what a read that follows no link finds at the path of each (`entryType`): a
directory is added to `directories`, a symbolic link or another kind of entry than a directory and
a file to `others`, and a file or nothing is left out. -/
def sortEntries {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m) :
    List IO.FS.DirEntry → List FilePath → List FilePath → m (List FilePath × List FilePath)
  | [], directories, others => pure (directories, others)
  | entry :: rest, directories, others => do
    match ← entryType ops entry.path with
    | some .dir => sortEntries ops rest (entry.path :: directories) others
    | some .symlink | some .other => sortEntries ops rest directories (entry.path :: others)
    | some .file | none => sortEntries ops rest directories others

/-- List each directory of `directories`, and each directory that a listing finds below them at any
depth, and add to `others` each path that a listing finds that is a symbolic link or another kind
of entry than a directory and a file (`sortEntries`). It lists at most `limit` directories, and
fails, naming `root`, when one more is left to list. -/
def otherEntriesIn {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (root : FilePath) : Nat → List FilePath → List FilePath → m (List FilePath)
  | _, [], others => pure others
  | 0, _ :: _, _ =>
    throw (IO.userError s!"{root} has more directories below it than the walk lists")
  | limit + 1, directory :: rest, others => do
    let (directories, others) ← sortEntries ops (← ops.readDir directory).toList rest others
    otherEntriesIn ops root limit directories others

/-- Each path of the listed tree of `root` (`Model.Listed`) that is a symbolic link or another kind
of entry than a directory and a file, by reads that follow no link: `root` itself when it is one,
and when it is a directory, each such path below it (`otherEntriesIn`), listing at most `limit`
directories. A walk that lists exactly `limit` directories gives its paths. -/
def otherEntries {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (limit : Nat) (root : FilePath) : m (List FilePath) := do
  match ← entryType ops root with
  | some .dir => otherEntriesIn ops root limit [root] []
  | some .symlink | some .other => pure [root]
  | some .file | none => pure []

/-- A run of `sortEntries` changes nothing. When it succeeds, it keeps `directories` and `others`,
adds the path of each entry that is a directory to the directories and of each that is a symbolic
link or another kind of entry (`Model.NotPlain`) to the others, and adds nothing else to the
directories. -/
theorem sortEntries_run (M : Model) (reads : ReadsEntry M) :
    ∀ (entries : List IO.FS.DirEntry) (before : M.World) (directories others : List FilePath),
      (∀ directory ∈ directories, M.entry before directory = some .dir) →
      Satisfies ((sortEntries M.ops entries directories others).run before)
        (fun sorted w => w = before ∧
          (∀ directory ∈ sorted.1, M.entry before directory = some .dir) ∧
          directories ⊆ sorted.1 ∧ others ⊆ sorted.2 ∧
          ∀ entry ∈ entries,
            (M.entry before entry.path = some .dir → entry.path ∈ sorted.1) ∧
            (M.NotPlain before entry.path → entry.path ∈ sorted.2))
        (fun _ w => w = before)
  | [], before, directories, others, kept => by
    simp only [sortEntries, EStateM.run_pure, Satisfies]
    exact ⟨trivial, kept, List.Subset.refl _, List.Subset.refl _, by simp⟩
  | entry :: rest, before, directories, others, kept => by
    simp only [sortEntries]
    refine Satisfies.bind (entryType_run M reads entry.path before) ?_
    rintro found w ⟨rfl, rfl⟩
    have step := fun directories' others' kept' =>
      sortEntries_run M reads rest w directories' others' kept'
    cases found_eq : M.entry w entry.path with
    | none =>
      refine (step directories others kept).mono ?_ (fun _ _ h => h)
      rintro sorted w' ⟨same, dirs, subDirs, subOthers, sortedRest⟩
      refine ⟨same, dirs, subDirs, subOthers, ?_⟩
      intro e inE
      rcases List.mem_cons.mp inE with rfl | inRest
      · simp [Model.NotPlain, found_eq]
      · exact sortedRest e inRest
    | some kind =>
      cases kind with
      | dir =>
        refine (step (entry.path :: directories) others ?_).mono ?_ (fun _ _ h => h)
        · intro directory inD
          rcases List.mem_cons.mp inD with rfl | inRest
          · exact found_eq
          · exact kept directory inRest
        · rintro sorted w' ⟨same, dirs, subDirs, subOthers, sortedRest⟩
          refine ⟨same, dirs, fun d inD => subDirs (List.mem_cons_of_mem _ inD), subOthers, ?_⟩
          intro e inE
          rcases List.mem_cons.mp inE with rfl | inRest
          · exact ⟨fun _ => subDirs (List.mem_cons_self ..),
              fun notPlain => by rcases notPlain with h | h <;> simp [found_eq] at h⟩
          · exact sortedRest e inRest
      | file =>
        refine (step directories others kept).mono ?_ (fun _ _ h => h)
        rintro sorted w' ⟨same, dirs, subDirs, subOthers, sortedRest⟩
        refine ⟨same, dirs, subDirs, subOthers, ?_⟩
        intro e inE
        rcases List.mem_cons.mp inE with rfl | inRest
        · simp [Model.NotPlain, found_eq]
        · exact sortedRest e inRest
      | symlink | other =>
        refine (step directories (entry.path :: others) kept).mono ?_ (fun _ _ h => h)
        rintro sorted w' ⟨same, dirs, subDirs, subOthers, sortedRest⟩
        refine ⟨same, dirs, subDirs, fun o inO => subOthers (List.mem_cons_of_mem _ inO), ?_⟩
        intro e inE
        rcases List.mem_cons.mp inE with rfl | inRest
        · exact ⟨fun isDir => by simp [found_eq] at isDir,
            fun _ => subOthers (List.mem_cons_self ..)⟩
        · exact sortedRest e inRest

/-- A run of `otherEntriesIn` changes nothing. When it succeeds, it keeps `others`, and it holds
each path of the listed tree of each of `directories` (`Model.Listed`) that is a symbolic link or
another kind of entry than a directory and a file (`Model.NotPlain`). -/
theorem otherEntriesIn_run (M : Model) (reads : ReadsEntry M) (lists : ListsEntries M)
    (root : FilePath) :
    ∀ (limit : Nat) (before : M.World) (directories others : List FilePath),
      (∀ directory ∈ directories, M.entry before directory = some .dir) →
      Satisfies ((otherEntriesIn M.ops root limit directories others).run before)
        (fun found w => w = before ∧ others ⊆ found ∧
          ∀ directory ∈ directories, ∀ path, M.Listed before directory path →
            M.NotPlain before path → path ∈ found)
        (fun _ w => w = before)
  | _, before, [], others, _ => by
    simp only [otherEntriesIn, EStateM.run_pure, Satisfies]
    exact ⟨trivial, List.Subset.refl _, by simp⟩
  | 0, before, _ :: _, _, _ => by
    simp only [otherEntriesIn, run_throw, Satisfies]
  | limit + 1, before, directory :: rest, others, kept => by
    simp only [otherEntriesIn]
    have isDir := kept directory (List.mem_cons_self ..)
    refine Satisfies.bind ((triple_iff _ _ _ _).mp (lists directory before isDir) before rfl) ?_
    rintro entries w ⟨rfl, complete⟩
    refine Satisfies.bind (sortEntries_run M reads entries.toList w rest others
      fun d inD => kept d (List.mem_cons_of_mem _ inD)) ?_
    rintro ⟨directories, others'⟩ w' ⟨rfl, dirs, subRest, subOthers, sorted⟩
    refine (otherEntriesIn_run M reads lists root limit w' directories others' dirs).mono ?_
      (fun _ _ h => h)
    rintro found w'' ⟨same, othersFound, below⟩
    refine ⟨same, fun o inO => othersFound (subOthers inO), ?_⟩
    intro d inD path listed notPlain
    rcases List.mem_cons.mp inD with rfl | inRest
    · rcases listed.first with rfl | ⟨_, name, held, belowChild⟩
      · rcases notPlain with h | h <;> simp [isDir] at h
      · obtain ⟨entry, inEntries, rootEq, nameEq⟩ := complete name held
        have pathEq : entry.path = d / name := by
          simp only [IO.FS.DirEntry.path, rootEq, nameEq]
        have sortedEntry := sorted entry (Array.mem_toList_iff.mpr inEntries)
        rw [pathEq] at sortedEntry
        by_cases childDir : M.entry w' (d / name) = some .dir
        · exact below _ (sortedEntry.1 childDir) path belowChild notPlain
        · rcases belowChild.first with rfl | ⟨isChildDir, _⟩
          · exact othersFound (sortedEntry.2 notPlain)
          · exact absurd isChildDir childDir
    · exact below d (subRest inRest) path listed notPlain

/-- A run of `otherEntries` changes nothing. When it succeeds, it gives each path of the listed tree
of the root (`Model.Listed`) that is a symbolic link or another kind of entry than a directory and
a file (`Model.NotPlain`). -/
theorem otherEntries_run (M : Model) (reads : ReadsEntry M) (lists : ListsEntries M) (limit : Nat)
    (root : FilePath) (before : M.World) :
    Satisfies ((otherEntries M.ops limit root).run before)
      (fun found w => w = before ∧
        ∀ path, M.Listed before root path → M.NotPlain before path → path ∈ found)
      (fun _ w => w = before) := by
  simp only [otherEntries]
  refine Satisfies.bind (entryType_run M reads root before) ?_
  rintro found w ⟨rfl, rfl⟩
  have alone : ∀ path, M.Listed w root path → M.entry w root ≠ some .dir → path = root :=
    fun path listed notDir => by
      rcases listed.first with same | ⟨isDir, _⟩
      · exact same
      · exact absurd isDir notDir
  cases found_eq : M.entry w root with
  | none =>
    simp only [EStateM.run_pure, Satisfies]
    refine ⟨trivial, fun path listed notPlain => ?_⟩
    rw [alone path listed (by simp [found_eq])] at notPlain
    rcases notPlain with h | h <;> simp [found_eq] at h
  | some kind =>
    cases kind with
    | dir =>
      exact (otherEntriesIn_run M reads lists root limit w [root] [] (by simp [found_eq])).mono
        (fun _ _ ⟨same, _, below⟩ => ⟨same, fun path listed notPlain =>
          below root (List.mem_singleton_self _) path listed notPlain⟩) (fun _ _ h => h)
    | file =>
      simp only [EStateM.run_pure, Satisfies]
      refine ⟨trivial, fun path listed notPlain => ?_⟩
      rw [alone path listed (by simp [found_eq])] at notPlain
      rcases notPlain with h | h <;> simp [found_eq] at h
    | symlink | other =>
      simp only [EStateM.run_pure, Satisfies]
      exact ⟨trivial, fun path listed _ => by
        rw [alone path listed (by simp [found_eq])]
        exact List.mem_singleton_self _⟩

/-! ## Checked removals -/

/-- Read `path` again after a removal, and fail when something is still there. -/
def confirmGone {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  if (← entryType ops path).isSome then
    throw (IO.userError s!"{path} is still there after its removal")

/-- Remove the directory at `path` with all its entries, then read `path` again, and fail when
something is still there. It reads neither the kind of the entry nor its place: a symbolic link to a
directory at `path` makes `IO.FS.removeDirAll` remove the entries of its target. So it runs only in
`Regula.Removal.removeOwnWith`, after the decision `Regula.Removal.removal` decided to remove a
directory at its own place, and at the observer no other code runs it (`Regula.Filesystem`). -/
def removeDirectory {m : Type → Type} [Monad m] [MonadExceptOf IO.Error m] (ops : Ops m)
    (path : FilePath) : m Unit := do
  ops.removeDirAll path
  confirmGone ops path

/-- Remove the entry at `path`, which is not a directory, then read `path` again, and fail when
something is still there. It reads neither the kind of the entry nor its place, so it runs only in
`Regula.Removal.removeOwnWith`, after the decision `Regula.Removal.removal` decided to remove a file
at its own place, and at the observer no other code runs it (`Regula.Filesystem`). -/
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

/-- `removeDirectory` of a directory at its own place removes it and keeps the entry at each path
of its frame (`Model.Unchanged`), each path not spelled within the directory, below a parent at its
own real path, whose file before is not an entry of the directory's tree (`Model.Below`); when it
fails, it kept them. -/
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

/-- `removeEntry` of a path at its own place, or of a symbolic link in a directory at its own place,
removes it and keeps the entry at each path of its frame (`Model.Unchanged`), each path not
spelled within the path, below a parent at its own real path, whose file before is not an entry of
the path's tree (`Model.Below`); when it fails, it kept them. -/
theorem removeEntry_spec (M : Model) (reads : ReadsEntry M) (removes : RemovesEntry M)
    (path : FilePath) (before : M.World)
    (own : M.real before path = some path ∨
      M.entry before path = some .symlink ∧ M.InOwnDirectory before path) :
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

/-- `realOf` at operations that correspond to a model runs as `realOf` in the model. -/
theorem realOf_agrees (corresponds : Corresponds ops M view) (path : FilePath) :
    Agrees view (realOf ops path) (realOf M.ops path) :=
  Agrees.tryCatch (Agrees.bind (corresponds.2.1 path) fun _ => Agrees.pure view _)
    fun _ => Agrees.pure view none

/-- `sortEntries` at operations that correspond to a model runs as `sortEntries` in the model. -/
theorem sortEntries_agrees (corresponds : Corresponds ops M view) :
    ∀ (entries : List IO.FS.DirEntry) (directories others : List FilePath),
      Agrees view (sortEntries ops entries directories others)
        (sortEntries M.ops entries directories others)
  | [], _, _ => Agrees.pure view _
  | entry :: rest, directories, others => by
    simp only [sortEntries]
    refine Agrees.bind (entryType_agrees corresponds entry.path) fun found => ?_
    rcases found with _ | (_ | _ | _ | _) <;> exact sortEntries_agrees corresponds rest _ _

/-- `otherEntriesIn` at operations that correspond to a model runs as `otherEntriesIn` in the
model. -/
theorem otherEntriesIn_agrees (corresponds : Corresponds ops M view) (root : FilePath) :
    ∀ (limit : Nat) (directories others : List FilePath),
      Agrees view (otherEntriesIn ops root limit directories others)
        (otherEntriesIn M.ops root limit directories others)
  | _, [], _ => by simp only [otherEntriesIn]; exact Agrees.pure view _
  | 0, _ :: _, _ => by simp only [otherEntriesIn]; exact Agrees.throw view _
  | limit + 1, directory :: rest, others => by
    simp only [otherEntriesIn]
    refine Agrees.bind (corresponds.2.2.2.2.2 directory) fun entries => ?_
    refine Agrees.bind (sortEntries_agrees corresponds _ _ _) fun sorted => ?_
    obtain ⟨directories, others'⟩ := sorted
    exact otherEntriesIn_agrees corresponds root limit directories others'

/-- `otherEntries` at operations that correspond to a model runs as `otherEntries` in the model. -/
theorem otherEntries_agrees (corresponds : Corresponds ops M view) (limit : Nat)
    (root : FilePath) :
    Agrees view (otherEntries ops limit root) (otherEntries M.ops limit root) := by
  refine Agrees.bind (entryType_agrees corresponds root) fun found => ?_
  rcases found with _ | (_ | _ | _ | _) <;>
    first | exact otherEntriesIn_agrees corresponds root limit _ _ | exact Agrees.pure view _

/-- `otherEntries` in `IO`, at operations that correspond to a model, ends in a world read as the
same state, and when it succeeds, it gives each path of the listed tree of the root
(`Model.Listed`) that is a symbolic link or another kind of entry than a directory and a file
(`Model.NotPlain`) (`otherEntries_run`). -/
theorem otherEntries_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (lists : ListsEntries M) (limit : Nat) (root : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (otherEntries ops limit root w)
      (fun found s => s = view w ∧ ∀ path, M.Listed (view w) root path →
        M.NotPlain (view w) path → path ∈ found)
      (fun _ s => s = view w) :=
  (otherEntries_agrees corresponds limit root).transfer w
    (otherEntries_run M reads lists limit root (view w))

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
  Agrees.bind (corresponds.2.2.2.1 path) fun _ => confirmGone_agrees corresponds path

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
place removes it and keeps the entry at each path of its frame (`Model.Unchanged`), each path not
spelled within the directory, below a parent at its own real path, whose file before is not an
entry of the directory's tree (`Model.Below`); when it fails, it kept them
(`removeDirectory_spec`). -/
theorem removeDirectory_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (removes : RemovesTree M) (path : FilePath) (w : Void IO.RealWorld)
    (directory : M.entry (view w) path = some .dir) (own : M.real (view w) path = some path) :
    RunsTo view (removeDirectory ops path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s)
      (fun _ s => M.Unchanged path (view w) s) :=
  (removeDirectory_agrees corresponds path).transfer w
    ((triple_iff _ _ _ _).mp
      (removeDirectory_spec M reads removes path (view w) directory own) (view w) rfl)

/-- `removeEntry` in `IO`, at operations that correspond to a model, of a path at its own place, or
of a symbolic link in a directory at its own place, removes it and keeps the entry at each path of
its frame (`Model.Unchanged`), each path not spelled within the path, below a parent at its own
real path, whose file before is not an entry of the path's tree (`Model.Below`); when it fails, it
kept them (`removeEntry_spec`). -/
theorem removeEntry_io (corresponds : Corresponds ops M view) (reads : ReadsEntry M)
    (removes : RemovesEntry M) (path : FilePath) (w : Void IO.RealWorld)
    (own : M.real (view w) path = some path ∨
      M.entry (view w) path = some .symlink ∧ M.InOwnDirectory (view w) path) :
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
