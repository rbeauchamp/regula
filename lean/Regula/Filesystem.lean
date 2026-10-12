import RegulaCore.Removal

/-! # The observer of the filesystem, and the removals and moves that Regula runs

The filesystem operations of Lean's library that `Regula.Filesystem.Ops` names, as code written
over `Ops` runs them: each operation of `observer` is a definition of this module that calls one of
them. The observer's runs are a model of the filesystem (`observed`), whose states are the worlds
of `IO`. That the observer satisfies the assumptions of `RegulaCore.Filesystem` at that model is the
trusted step.

The observer's operations that remove or move an entry, and `observer` itself, are private to this
module. The only way that other code removes or moves an entry is one of the operations below,
each of which observes the place and acts only on what the decisions of `RegulaCore.Removal`
decide: `removeOwn`, `removeFound`, `replace` and `withOwnTempDir`. The theorems at the end state,
under the assumptions they name, what each does. The reach check `Regula.Removal.rawRemovals`
refuses each call of a removal primitive outside a declaration with the observer's role, so no
code of Regula calls one other than through this module. A deliberate use of the private
declarations, with `open private` or a hand-written name, is outside that criterion, as for the
private observation of issue 261.

The observer's reads are public: `ownPath` checks a place before a program makes something there,
`requireOwnDirectory` and `requireNoLinkedEntries` check a place before a program loads something
there, and `requireLinksPlaced` checks that a directory that a program made holds no symbolic link
but those it placed.

Each operation is `@[noinline]`, so its call of the library's operation stays in its own compiled
code and is not copied into a caller's. On Windows, Lean 4.34.1's
`System.FilePath.symlinkMetadata` follows a symbolic link at the path, which `ReadsEntry` does not
allow, and `IO.FS.removeDirAll` uses it on each entry. Its `IO.FS.realPath` gives the path itself
when it cannot resolve it (`runtime/io.cpp#L1032-L1033`), which `ReadsReal` does not allow. So on
Windows the observer's read of an entry, its read of a real path and its removal of a directory
fail without acting, and every removal and move, which read the entry first, fails. -/

namespace Regula.Filesystem

open System Regula.StateTriple Regula.Removal

/-- The error of an operation that the observer does not run on Windows, with the reason. -/
def windowsRefusal (operation : String) (path : FilePath) (reason : String) : IO.Error :=
  IO.userError s!"{operation} {path}: refused on Windows, where Lean 4.34.1's {reason}"

/-- Why the observer refuses a read of an entry and a removal of a directory on Windows. -/
def linkFollowed : String :=
  "System.FilePath.symlinkMetadata follows a symbolic link at the path"

/-- `System.FilePath.symlinkMetadata`, which fails on Windows. -/
@[noinline, regula_observer filesystem]
def observeMetadata (path : FilePath) : IO IO.FS.Metadata :=
  if System.Platform.isWindows then throw (windowsRefusal "lstat" path linkFollowed)
  else path.symlinkMetadata

/-- `IO.FS.realPath`, which fails on Windows. -/
@[noinline, regula_observer filesystem]
def observeRealPath (path : FilePath) : IO FilePath :=
  if System.Platform.isWindows then
    throw (windowsRefusal "realpath" path "IO.FS.realPath gives a path it did not resolve")
  else IO.FS.realPath path

/-- `IO.FS.removeDirAll`, which fails on Windows. -/
@[noinline, regula_observer filesystem]
private def observeRemoveDirAll (path : FilePath) : IO Unit :=
  if System.Platform.isWindows then throw (windowsRefusal "removeDirAll" path linkFollowed)
  else IO.FS.removeDirAll path

/-- `IO.FS.removeFile`. -/
@[noinline, regula_observer filesystem]
private def observeRemoveFile (path : FilePath) : IO Unit :=
  IO.FS.removeFile path

/-- `IO.FS.rename`. -/
@[noinline, regula_observer filesystem]
private def observeRename (source destination : FilePath) : IO Unit :=
  IO.FS.rename source destination

/-- `System.FilePath.readDir`. -/
@[noinline, regula_observer filesystem]
def observeReadDir (path : FilePath) : IO (Array IO.FS.DirEntry) :=
  path.readDir

/-- The filesystem's operations in `IO`, which Regula's code runs. -/
@[regula_observer filesystem]
private def observer : Ops IO where
  symlinkMetadata := observeMetadata
  realPath := observeRealPath
  removeDirAll := observeRemoveDirAll
  removeFile := observeRemoveFile
  rename := observeRename
  readDir := observeReadDir

/-! ## Removal and move -/

/-- Remove the entry of `kind` at `path` when one is there at its own place, do nothing when
nothing is there, and stop with nothing removed in every other case: `Regula.Removal.removeOwnWith`
at the observer (`observer_removeOwn`). A directory or file is at its own place when its real path
is `path`, so a relative path, a `.` or `..` component and a symbolic link at any component make it
refuse; `ownPath` gives the absolute path below the real working directory. A symbolic link is at
its own place when it is a name in a directory at its own place, and it is removed, not the file
that it points to. -/
def removeOwn (kind : Kind) (path : FilePath) : IO Unit :=
  removeOwnWith observer kind path

/-- Remove the directory or file at `path`, whichever is there, at its own place; do nothing when
nothing is there; and stop with nothing removed when a symbolic link, another kind of entry or a
path through a symbolic link is there: `Regula.Removal.removeFoundWith` at the observer
(`observer_removeFound`). -/
def removeFound (path : FilePath) : IO Unit :=
  removeFoundWith observer path

/-- Move the file at `source`, at its own place, to `destination`, where nothing is or a file is at
its own place, in a directory at its own place; otherwise stop with nothing moved:
`Regula.Removal.replaceWith` at the observer (`observer_replace`). It is how a program makes a file
appear complete or not at all: it writes the file beside its destination and moves it there. -/
def replace (source destination : FilePath) : IO Unit :=
  replaceWith observer source destination

/-- A new directory that `IO.FS.createTempDir` makes, by its real path, so `removeOwn` removes it:
on macOS the temporary directory is below `/var`, a symbolic link to `/private/var`. On Windows,
where the observer reads no real path (`observeRealPath`), it stops before it makes the directory,
so it leaves none behind. -/
def ownTempDir : IO FilePath := do
  if System.Platform.isWindows then
    throw (windowsRefusal "createTempDir" "(nothing was made)"
      "IO.FS.realPath gives a path it did not resolve")
  observeRealPath (← IO.FS.createTempDir)

/-- Run `action` in a new temporary directory (`ownTempDir`), and remove the directory with
`removeOwn` afterwards, whether `action` succeeds or fails. -/
def withOwnTempDir {α : Type} (action : FilePath → IO α) : IO α := do
  let directory ← ownTempDir
  try action directory finally removeOwn .directory directory

/-! ## Places checked before a program makes or loads something there -/

/-- What is at `path`, by a read that follows no symbolic link at `path` itself. -/
private def place (path : FilePath) : IO Place := do
  return Place.ofType (← entryType observer path)

/-- `path` as an absolute path whose present ancestors are at their own place. The leading `.`
components of a relative path are dropped, since each names the working directory; any other `.`
or `..` component makes it refuse before it reads anything. A relative path is joined to the real
path of the working directory, and no component that `path` gives is resolved. It refuses when the
nearest ancestor of `path` that is present, by a read that follows no link, is not its own real
path: a symbolic link is among the components up to it. An absent ancestor is made later by
`IO.FS.createDirAll` as a directory, so no link is among them when no process makes one after this
check, which is trusted. It stops on Windows, where the observer reads no entry. -/
def ownPath (path : FilePath) : IO FilePath := do
  let components := path.components.dropWhile (· == ".")
  if components.any (fun component => component == "." || component == "..") then
    throw <| IO.userError s!"nothing was made or removed: {path} has a `.` or `..` component"
  let path ← if path.isAbsolute then pure path else do
    let directory ← observeRealPath (← IO.currentDir)
    pure (if components.isEmpty then directory else directory / System.mkFilePath components)
  let refuse {α : Type} (ancestor : FilePath) : IO α := throw <| IO.userError
    s!"nothing was made or removed: {ancestor}, an ancestor of {path}, is not at its own place \
      (a symbolic link is among its components)"
  let mut ancestor := path.parent
  for _ in [:path.components.length] do
    let some current := ancestor | break
    match ← place current with
    | .absent => ancestor := current.parent
    | _ => if ← atOwnPlace observer current then return path else refuse current
  return path

/-- `removeOwn` at `ownPath path`, so a relative path is read below the real working directory. -/
def removePath (kind : Kind) (path : FilePath) : IO Unit := do
  removeOwn kind (← ownPath path)

/-- `removeFound` at `ownPath path`. -/
def removeFoundPath (path : FilePath) : IO Unit := do
  removeFound (← ownPath path)

/-- `replace` at `ownPath source` and `ownPath destination`. -/
def replacePath (source destination : FilePath) : IO Unit := do
  replace (← ownPath source) (← ownPath destination)

/-! ## Symbolic links below a directory -/

/-- The bound on the number of directories that a walk below a directory lists
(`Regula.Filesystem.otherEntries`). -/
def maxDirectories : Nat := 10_000_000

/-- Stop unless each path below `root`, at any depth and `root` itself, that is a symbolic link or
another kind of entry than a directory and a file is one of `placed`:
`Regula.Removal.requirePlacedWith` at the observer, listing at most `limit` directories
(`observer_requireLinksPlaced`). The walk lists each directory that a read following no link finds
below `root`, and goes into no symbolic link. When nothing is at `root`, or a file, it passes. -/
def requireLinksPlaced (root : FilePath) (placed : List FilePath)
    (limit : Nat := maxDirectories) : IO Unit :=
  requirePlacedWith observer limit root placed

/-- Stop unless nothing is at `path` or a directory is there at its own place, by the observation
that `removeOwn` makes. These are the places on which `removal .directory` does not refuse
(`removal_remove_iff`, `removal_nothing_iff`), so a symbolic link, a file and a path through a
symbolic link at `path` make it stop. -/
def requireOwnDirectory (path : FilePath) : IO Unit := do
  if removal .directory (← observe observer path) == .refuse then
    throw <| IO.userError s!"{path} is not a directory at its own place (a symbolic link, a file, \
      or a path through a symbolic link is there)"

/-- Stop unless nothing is at `path`, or a directory is there at its own place
(`requireOwnDirectory`) and each entry below it, at any depth, is a directory or a file
(`requireLinksPlaced` with no placed link). A symbolic link below it, also one whose target is
absent, makes it stop, so a file that a later operation opens by its name in this directory is not
reached through a link, when no process makes one after this check, which is trusted. -/
def requireNoLinkedEntries (path : FilePath) : IO Unit := do
  requireOwnDirectory path
  requireLinksPlaced path []

/-! ## The operations at the observer -/

/-- The model of the filesystem that the observer's runs are: its states are the worlds of `IO`,
its operations are the observer's, and `entry`, `real`, `ident` and `names` give what `lstat(2)`,
`realpath(3)` and `readdir(3)` report at each world. No operation reads `ident` (`Model.ident`):
the theorems below hold for every `ident`. The observer corresponds to the model
(`corresponds_ofIO`), so the theorems below rest only on the assumptions they name at it. -/
abbrev observed (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) : Model :=
  Model.ofIO observer entry real ident names

section Observer

variable {entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType}
  {real : Void IO.RealWorld → FilePath → Option FilePath}
  {ident : Void IO.RealWorld → FilePath → Option FileId}
  {names : Void IO.RealWorld → FilePath → List String}

/-- **Checked, at the observer:** when `removeOwn` succeeds from a world, nothing is at the path at
the world it ends in, when the observer satisfies `ReadsEntry`. -/
theorem observer_removeOwn_gone (reads : ReadsEntry (observed entry real ident names)) (kind : Kind)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (removeOwn kind path w) (fun _ s => entry s path = none) (fun _ _ => True) :=
  removeOwnWith_gone_io (corresponds_ofIO observer entry real ident names) reads kind path w

/-- `removeOwn` removes only an entry of `kind` at its own place, when the observer satisfies
`ReadsEntry`, `ReadsReal`, `RemovesTree` and `RemovesEntry`: when it succeeds, nothing is at the
path; whether it succeeds or fails, it keeps the entry at each path of the frame of the path
(`Model.Unchanged`) and changes the world only when an entry of `kind` was at the path at its own
place (`Regula.Removal.OnlyOwn`). -/
theorem observer_removeOwn (readsEntry : ReadsEntry (observed entry real ident names))
    (readsReal : ReadsReal (observed entry real ident names))
    (removesTree : RemovesTree (observed entry real ident names))
    (removesEntry : RemovesEntry (observed entry real ident names)) (kind : Kind) (path : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo id (removeOwn kind path w)
      (fun _ s => entry s path = none ∧ (observed entry real ident names).Unchanged path w s ∧
        OnlyOwn (observed entry real ident names) kind path w s)
      (fun _ s => (observed entry real ident names).Unchanged path w s ∧
        OnlyOwn (observed entry real ident names) kind path w s) :=
  removeOwnWith_io (corresponds_ofIO observer entry real ident names) readsEntry readsReal
    removesTree removesEntry kind path w

/-- **Checked, at the observer:** when `removeFound` succeeds from a world, nothing is at the path
at the world it ends in, when the observer satisfies `ReadsEntry`. -/
theorem observer_removeFound_gone (reads : ReadsEntry (observed entry real ident names))
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (removeFound path w) (fun _ s => entry s path = none) (fun _ _ => True) :=
  removeFoundWith_gone_io (corresponds_ofIO observer entry real ident names) reads path w

/-- `removeFound` removes only a directory or a file at its own place, when the observer satisfies
`ReadsEntry`, `ReadsReal`, `RemovesTree` and `RemovesEntry` (`observer_removeOwn`). -/
theorem observer_removeFound (readsEntry : ReadsEntry (observed entry real ident names))
    (readsReal : ReadsReal (observed entry real ident names))
    (removesTree : RemovesTree (observed entry real ident names))
    (removesEntry : RemovesEntry (observed entry real ident names)) (path : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo id (removeFound path w)
      (fun _ s => entry s path = none ∧ (observed entry real ident names).Unchanged path w s ∧
        ∃ kind, OnlyOwn (observed entry real ident names) kind path w s)
      (fun _ s => (observed entry real ident names).Unchanged path w s ∧
        ∃ kind, OnlyOwn (observed entry real ident names) kind path w s) :=
  removeFoundWith_io (corresponds_ofIO observer entry real ident names) readsEntry readsReal
    removesTree removesEntry path w

/-- **Checked, at the observer:** when `replace` succeeds from a world, nothing is at the source
and a regular file is at the destination at the world it ends in, when the observer satisfies
`ReadsEntry`. -/
theorem observer_replace_moved (reads : ReadsEntry (observed entry real ident names))
    (source destination : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (replace source destination w)
      (fun _ s => entry s source = none ∧ entry s destination = some .file) (fun _ _ => True) :=
  replaceWith_moved_io (corresponds_ofIO observer entry real ident names) reads source destination w

/-- `replace` moves only a file at its own place to an absent path or a file at its own place, in
a directory at its own place, when the observer satisfies `ReadsEntry`, `ReadsReal` and `Renames`:
when it succeeds, nothing is at the source and a regular file is at the destination; whether it
succeeds or fails, it keeps the entry at each path of the frame of both paths (`Model.Kept`) and
changes the world only when the decision held (`Regula.Removal.Movable`). -/
theorem observer_replace (readsEntry : ReadsEntry (observed entry real ident names))
    (readsReal : ReadsReal (observed entry real ident names))
    (renames : Renames (observed entry real ident names)) (source destination : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo id (replace source destination w)
      (fun _ s => entry s source = none ∧ entry s destination = some .file ∧
        (observed entry real ident names).Kept [source, destination] w s ∧
        Movable (observed entry real ident names) source destination w)
      (fun _ s => (observed entry real ident names).Kept [source, destination] w s ∧
        (s = w ∨ Movable (observed entry real ident names) source destination w)) :=
  replaceWith_io (corresponds_ofIO observer entry real ident names) readsEntry readsReal renames
    source destination w

/-- `requireLinksPlaced` changes nothing, and when it succeeds from a world, each path of the listed
tree of the root at that world (`Model.Listed`) that is a symbolic link or another kind of entry
than a directory and a file (`Model.NotPlain`) is one of the placed paths, when the observer
satisfies `ReadsEntry` and `ListsEntries` (`Regula.Removal.requirePlacedWith_run`). -/
theorem observer_requireLinksPlaced (readsEntry : ReadsEntry (observed entry real ident names))
    (lists : ListsEntries (observed entry real ident names)) (root : FilePath)
    (placed : List FilePath) (limit : Nat) (w : Void IO.RealWorld) :
    RunsTo id (requireLinksPlaced root placed limit w)
      (fun _ s => s = w ∧ ∀ path, (observed entry real ident names).Listed w root path →
        (observed entry real ident names).NotPlain w path → path ∈ placed)
      (fun _ s => s = w) :=
  requirePlacedWith_io (corresponds_ofIO observer entry real ident names) readsEntry lists limit
    root placed w

end Observer

end Regula.Filesystem
