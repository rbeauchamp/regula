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
and `requireLakePlaces` checks the places where Lake removes or replaces entries before Lake runs
in the program's process.

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

/-- The filesystem's operations in `IO`, which Regula's code runs. -/
@[regula_observer filesystem]
private def observer : Ops IO where
  symlinkMetadata := observeMetadata
  realPath := observeRealPath
  removeDirAll := observeRemoveDirAll
  removeFile := observeRemoveFile
  rename := observeRename

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

/-! ## The places where Lake removes or replaces entries -/

/-- The bound on the number of directories that `entriesBelow` reads. -/
def maxDirectories : Nat := 10_000_000

/-- Each entry at any depth below the directory `directory`, with what is there by a read that
follows no link: the walk descends into each directory that it finds and into no symbolic link. It
stops with an error when it would read more than `maxDirectories` directories. -/
private def entriesBelow (directory : FilePath) : IO (List (FilePath × Place)) := do
  let mut found := #[]
  let mut work := #[directory]
  for _ in [:maxDirectories] do
    let some current := work.back? | return found.toList
    work := work.pop
    for entry in ← current.readDir do
      let seen ← place entry.path
      found := found.push (entry.path, seen)
      if seen matches .present .directory then work := work.push entry.path
  throw <| IO.userError s!"nothing was loaded or built: {directory} has more than \
    {maxDirectories} directories below it"

/-- Read `place` before Lake runs (`Regula.Removal.LakeObserved`): whether its base is its own real
path, what is at each path from where the place is read from down to the place, by a read that
follows no link, up to the first that is not a directory, and, with `walk`, each entry below the
place when a directory is there (`entriesBelow`). The base is read without its `.` and empty
components, which name no other directory, and the place is read from the base or the ancestor of
it that the place's leading `..` components name (`LakePlace.start`). -/
def observeLakePlace (place : LakePlace) (walk : Bool) : IO LakeObserved := do
  let baseOwn ← atOwnPlace observer (System.mkFilePath (cleanComponents place.base))
  let some (start, below) := place.start | return { baseOwn, components := none, inside := [] }
  let mut components := #[]
  let mut current := System.mkFilePath start
  let mut last ← Regula.Filesystem.place current
  for name in below do
    unless last matches .present .directory do break
    current := current / name
    last ← Regula.Filesystem.place current
    components := components.push (current, last)
  let inside ← if walk && place.tree && last matches .present .directory then
      entriesBelow current else pure []
  return { baseOwn, components := some components.toList, inside }

/-- Whether `place` is a tree place below another tree place of `places`, by the components of
each from where it is read from down to it (`LakePlace.start`): the walk of that other place reads
each entry of this one, so it is not walked again (`requireLakePlaces`). Of two such places at the
same path, the earlier one is walked. -/
def walkedElsewhere (places : List LakePlace) (index : Nat) (place : LakePlace) : Bool :=
  let full (place : LakePlace) : Option (List String) := place.start.map fun (start, below) =>
    start ++ below
  place.tree && (places.zipIdx.any fun (other, otherIndex) =>
    other.tree && otherIndex != index &&
      match full other, full place with
      | some outer, some inner =>
        outer.isPrefixOf inner && (outer.length < inner.length || otherIndex < index)
      | _, _ => false)

/-- Why `lakePlacesAdmitted` refuses the observation `seen` of `place`. -/
def lakeRefusal (place : LakePlace) (seen : LakeObserved) : String :=
  let linked := ((seen.components.getD []) ++ seen.inside).find? (·.2 == .present .link)
  if !seen.baseOwn then s!"{place.base} is not its own real path (a symbolic link is among its \
    components, or nothing is there)"
  else if seen.components.isNone then s!"{place.path} is not below {place.base} or one of its \
    ancestors (a `..` component after another component, or a path outside it)"
  else match linked with
    | some (path, _) => s!"{path} is a symbolic link"
    | none => s!"{place.path} was refused"

/-- Stop unless Lake may run at `places`: read each (`observeLakePlace`) and decide on all of them
at once (`lakePlacesAdmitted`, `lakePlacesAdmitted_iff`). It admits them exactly when each base is
its own real path, each place is below its base or one of its ancestors, and no path from there
down to a place, and no entry at any depth below a place with `tree`, is a symbolic link. A tree
place below another tree place is not walked again (`walkedElsewhere`): the walk of the other place
reads each of its entries, since the decision admits a `..` component only before every other
component of a place below its base. Each ancestor of a base that is its own real path is its own
real path too. The reads are trusted, and a process that makes a link at a place after this check
is outside it. -/
def requireLakePlaces (places : List LakePlace) : IO Unit := do
  let observed ← places.zipIdx.mapM fun (place, index) =>
    observeLakePlace place (!walkedElsewhere places index place)
  unless lakePlacesAdmitted observed do
    let refused := (places.zip observed).find? fun (_, seen) => !lakePlacesAdmitted [seen]
    let detail := match refused with
      | some (place, seen) => lakeRefusal place seen
      | none => "a place was refused"
    throw <| IO.userError s!"nothing was loaded or built: Lake removes or replaces entries \
      there, and {detail}"

/-! ## The operations at the observer -/

/-- The model of the filesystem that the observer's runs are: its states are the worlds of `IO`,
its operations are the observer's, and `entry`, `real` and `ident` give what `lstat(2)` and
`realpath(3)` report at each world. No operation reads `ident` (`Model.ident`): the theorems below
hold for every `ident`. The observer corresponds to the model (`corresponds_ofIO`), so the theorems
below rest only on the assumptions they name at it. -/
abbrev observed (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId) : Model :=
  Model.ofIO observer entry real ident

section Observer

variable {entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType}
  {real : Void IO.RealWorld → FilePath → Option FilePath}
  {ident : Void IO.RealWorld → FilePath → Option FileId}

/-- **Checked, at the observer:** when `removeOwn` succeeds from a world, nothing is at the path at
the world it ends in, when the observer satisfies `ReadsEntry`. -/
theorem observer_removeOwn_gone (reads : ReadsEntry (observed entry real ident)) (kind : Kind)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (removeOwn kind path w) (fun _ s => entry s path = none) (fun _ _ => True) :=
  removeOwnWith_gone_io (corresponds_ofIO observer entry real ident) reads kind path w

/-- `removeOwn` removes only an entry of `kind` at its own place, when the observer satisfies
`ReadsEntry`, `ReadsReal`, `RemovesTree` and `RemovesEntry`: when it succeeds, nothing is at the
path; whether it succeeds or fails, it keeps the entry at each path of the frame of the path
(`Model.Unchanged`) and changes the world only when an entry of `kind` was at the path at its own
place (`Regula.Removal.OnlyOwn`). -/
theorem observer_removeOwn (readsEntry : ReadsEntry (observed entry real ident))
    (readsReal : ReadsReal (observed entry real ident))
    (removesTree : RemovesTree (observed entry real ident))
    (removesEntry : RemovesEntry (observed entry real ident)) (kind : Kind) (path : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo id (removeOwn kind path w)
      (fun _ s => entry s path = none ∧ (observed entry real ident).Unchanged path w s ∧
        OnlyOwn (observed entry real ident) kind path w s)
      (fun _ s => (observed entry real ident).Unchanged path w s ∧
        OnlyOwn (observed entry real ident) kind path w s) :=
  removeOwnWith_io (corresponds_ofIO observer entry real ident) readsEntry readsReal removesTree
    removesEntry kind path w

/-- **Checked, at the observer:** when `removeFound` succeeds from a world, nothing is at the path
at the world it ends in, when the observer satisfies `ReadsEntry`. -/
theorem observer_removeFound_gone (reads : ReadsEntry (observed entry real ident))
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (removeFound path w) (fun _ s => entry s path = none) (fun _ _ => True) :=
  removeFoundWith_gone_io (corresponds_ofIO observer entry real ident) reads path w

/-- `removeFound` removes only a directory or a file at its own place, when the observer satisfies
`ReadsEntry`, `ReadsReal`, `RemovesTree` and `RemovesEntry` (`observer_removeOwn`). -/
theorem observer_removeFound (readsEntry : ReadsEntry (observed entry real ident))
    (readsReal : ReadsReal (observed entry real ident))
    (removesTree : RemovesTree (observed entry real ident))
    (removesEntry : RemovesEntry (observed entry real ident)) (path : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo id (removeFound path w)
      (fun _ s => entry s path = none ∧ (observed entry real ident).Unchanged path w s ∧
        ∃ kind, OnlyOwn (observed entry real ident) kind path w s)
      (fun _ s => (observed entry real ident).Unchanged path w s ∧
        ∃ kind, OnlyOwn (observed entry real ident) kind path w s) :=
  removeFoundWith_io (corresponds_ofIO observer entry real ident) readsEntry readsReal removesTree
    removesEntry path w

/-- **Checked, at the observer:** when `replace` succeeds from a world, nothing is at the source
and a regular file is at the destination at the world it ends in, when the observer satisfies
`ReadsEntry`. -/
theorem observer_replace_moved (reads : ReadsEntry (observed entry real ident))
    (source destination : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (replace source destination w)
      (fun _ s => entry s source = none ∧ entry s destination = some .file) (fun _ _ => True) :=
  replaceWith_moved_io (corresponds_ofIO observer entry real ident) reads source destination w

/-- `replace` moves only a file at its own place to an absent path or a file at its own place, in
a directory at its own place, when the observer satisfies `ReadsEntry`, `ReadsReal` and `Renames`:
when it succeeds, nothing is at the source and a regular file is at the destination; whether it
succeeds or fails, it keeps the entry at each path of the frame of both paths (`Model.Kept`) and
changes the world only when the decision held (`Regula.Removal.Movable`). -/
theorem observer_replace (readsEntry : ReadsEntry (observed entry real ident))
    (readsReal : ReadsReal (observed entry real ident))
    (renames : Renames (observed entry real ident)) (source destination : FilePath)
    (w : Void IO.RealWorld) :
    RunsTo id (replace source destination w)
      (fun _ s => entry s source = none ∧ entry s destination = some .file ∧
        (observed entry real ident).Kept [source, destination] w s ∧
        Movable (observed entry real ident) source destination w)
      (fun _ s => (observed entry real ident).Kept [source, destination] w s ∧
        (s = w ∨ Movable (observed entry real ident) source destination w)) :=
  replaceWith_io (corresponds_ofIO observer entry real ident) readsEntry readsReal renames source
    destination w

end Observer

end Regula.Filesystem
