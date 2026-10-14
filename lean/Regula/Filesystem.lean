import RegulaCore.Removal
import Regula.Process
import RegulaCore.CopyConstruction

/-! # The observer of the filesystem, and the removals and moves that Regula runs

The filesystem operations of Lean's library that `Regula.Filesystem.Ops` names, as code written
over `Ops` runs them: each operation of `observer` is a definition of this module that calls one of
them. The observer's runs are a model of the filesystem (`observed`), whose states are the worlds
of `IO`. That the observer satisfies the assumptions of `RegulaCore.Filesystem` at that model is the
trusted step.

The observer's operations that remove or move an entry, and `observer` itself, are private to this
module. The only way that other code removes or moves an entry is one of the operations below:
`removeOwn`, `removeFound`, `replace` and `withOwnTempDir`, each of which observes the place and
acts only on what the decisions of `RegulaCore.Removal` decide, and `moveAside`, which moves an
entry into a directory that it makes new, so it replaces and removes nothing. The theorems at the
end state, under the assumptions they name, what each does. The reach check
`Regula.Removal.rawRemovals` refuses each call of a removal primitive outside a declaration with
the observer's role, so no code of Regula calls one other than through this module, except the
calls of Lean's library that `Regula.Removal.libraryRemovals` lists and the removals and moves of
the two drivers that `Regula.ProgramCheck.Verification` and `Regula.ProgramCheck.Provision` name. A
deliberate use of the private declarations, with `open private` or a hand-written name, is outside
that criterion, as for the private observation of issue 261.

The observer's reads are public: `ownPath` and `ownRoot` give the path at which a removal is
decided, and `requireOwnDirectory` and `requireNoLinkedEntries` check a place before a program
makes or loads something there.

Each operation is `@[noinline]`, so its call of the library's operation stays in its own compiled
code and is not copied into a caller's. On Windows, Lean 4.34.1's
`System.FilePath.symlinkMetadata` follows a symbolic link at the path, which `ReadsEntry` does not
allow, and `IO.FS.removeDirAll` uses it on each entry. Its `IO.FS.realPath` gives the path itself
when it cannot resolve it (`runtime/io.cpp#L1032-L1033`), which `ReadsReal` does not allow. So on
Windows the observer's read of an entry, its read of a real path and its removal of a directory
fail without acting, and every removal and move, which read the entry first, fails.

`readFileIfPresent` is not an operation of the observer: it calls `IO.FS.readFile` directly, and
gives `none` only for the error that says that nothing is at the path (`present`). -/

namespace Regula.CopyProcess

-- The toolchain-only constructor supplies no process primitives. Both this compiled adapter
-- and the cold source interpreter elaborate these shared Git and listing routes to Regula.Process.
run_cmd do
  let origin ← Lean.getRef
  let before ← Lean.getEnv
  let input := Lean.Parser.mkInputContext (include_str "GitProcessSource.inc")
    "Regula/GitProcessSource.inc"
  let result ← Lean.Elab.IO.processCommands input {} (← get)
  set result.commandState
  for (name, _) in result.commandState.env.constants.toList do
    unless before.contains name do
      Lean.Elab.addDeclarationRangesFromSyntax name origin

end Regula.CopyProcess

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
  Construction.observeMetadata path

/-- `IO.FS.realPath`, which fails on Windows. -/
@[noinline, regula_observer filesystem]
def observeRealPath (path : FilePath) : IO FilePath :=
  Construction.observeRealPath path

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

/-! ## Construction -/

/-- Capture selected source directories and regular files through the no-follow observer and
construct them exclusively. Links and special entries are refused before they can be opened.
`observer_copy` describes the exact resulting tree, under native primitive hypotheses.

Assumes: Lean v4.34.1 lstat (`Init/System/IO.lean:1151-1156`, `runtime/io.cpp:1160-1179`), an
admitted listing program that exits nonzero after a failed read of a directory
(`Construction.ReadsNames` names each program `Construction.locate` admits, with its source),
exclusive mkdir (`runtime/io.cpp:1181-1195`), and exclusive file creation
(`Init/System/IO.lean:651-660`, `runtime/io.cpp:409`). The source and private destination have no
concurrent writer. Windows is refused. Modes are not preserved: copied regular files receive 0644;
callers explicitly set 0755 for a copied executable they run. Lake creates and sets modes on
programs it builds. -/
def copy (source target : FilePath) (selected : FilePath → Bool := fun _ => true) :
    IO (List Construction.Item) := Construction.copy source target selected

/-- Construct a generated workspace through the same exclusive directory/file writer as `copy`.
The root is absent or privately owned and empty; its parent is at its own real path. -/
def construct (target : FilePath) (items : List Construction.Item) : IO Unit :=
  Construction.construct target items

/-- Copy a regular file through no-follow source admission and exclusive destination creation.
The parent is admitted at its real path before the common instruction writer runs. -/
def copyFile (source target : FilePath) (rights : UInt32 := 420) : IO Unit :=
  Construction.copyFile source target rights

/-- Read a regular source through the shared no-follow capture program before transforming it
into a generated fixture. Neither links nor special entries are consumed as source bytes. -/
def readBytes (source : FilePath) : IO ByteArray := do
  let [⟨_, .file bytes _⟩] ← Construction.capture source
    | throw <| IO.userError s!"source text is not one regular file: {source}"
  return bytes

/-- Decode bytes captured by the shared no-follow source reader as UTF-8. -/
def readFile (source : FilePath) : IO String := do
  let bytes ← readBytes source
  let some text := String.fromUTF8? bytes
    | throw <| IO.userError s!"source text is not UTF-8: {source}"
  return text

/-- Create a generated regular file through the exclusive writer. The destination's parent is
admitted through primitive observations before writing; an existing entry is refused. -/
def writeFile (target : FilePath) (text : String) : IO Unit := do
  let some parent := target.parent | throw <| IO.userError "generated file has no parent"
  let some name := target.fileName | throw <| IO.userError "generated file has no name"
  Construction.appendFileWith Construction.observer parent name text.toUTF8

/-- Create generated JSON bytes through the same exclusive writer. -/
def writeJson (target : FilePath) (json : Lean.Json) : IO Unit :=
  writeFile target (json.pretty ++ "\n")

/-- Grant 0755 to a known copied program before executing it. Refuse any non-regular entry or
path through an alias. The private destination has no concurrent writer during chmod.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1650` sets the regular file's access rights. -/
def makeExecutable (path : FilePath) : IO Unit := do
  unless (← observeMetadata path).type == .file && (← observeRealPath path) == path do
    throw <| IO.userError s!"copied executable is not a regular file at its own place: {path}"
  IO.Prim.setAccessRights path 493

/-- The construction observer over precisely the existing filesystem model's IO worlds. -/
abbrev observedConstruction (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) : Construction.CopyModel :=
  Construction.CopyModel.ofIO observer Construction.observer rfl rfl entry real ident names

/-- The construction observer that lists through `enumerator`, over precisely the existing
filesystem model's IO worlds. -/
abbrev locatedConstruction (enumerator : Construction.Enumerator)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String) : Construction.CopyModel :=
  Construction.CopyModel.ofIO observer enumerator.observer rfl rfl entry real ident names

/-- `copy` locates its listing program once and runs the shared copy through it. -/
theorem copy_locates (source target : FilePath) (selected : FilePath → Bool) :
    copy source target selected =
      (do Construction.copyWith (← Construction.locate).observer source target selected 4096) :=
  rfl

/-- The exact plain destination and complete selected source receipt of the actual copy callers
run, from the world that `Construction.locate` leaves once it gives `enumerator` (`copy_locates`).
All hypotheses describe native reads and exclusive creations; none asserts copy correctness.
Errors may leave a partial private destination and are never accepted. -/
theorem observer_copy (enumerator : Construction.Enumerator)
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String)
    (readsEntry : ReadsEntry (locatedConstruction enumerator entry real ident names).filesystem)
    (readsReal : ReadsReal (locatedConstruction enumerator entry real ident names).filesystem)
    (readsNames : Construction.ReadsNames (locatedConstruction enumerator entry real ident names))
    (readsBytes : Construction.ReadsBytes (locatedConstruction enumerator entry real ident names))
    (directories :
      Construction.CreatesDirectories (locatedConstruction enumerator entry real ident names))
    (files : Construction.CreatesFiles (locatedConstruction enumerator entry real ident names))
    (source target : FilePath) (selected : FilePath → Bool) (w : Void IO.RealWorld) :
    RunsTo id (Construction.copyWith enumerator.observer source target selected 4096 w)
      (fun items after =>
        Construction.Captured (locatedConstruction enumerator entry real ident names) w selected
          source [] items ∧
        Construction.Holds (locatedConstruction enumerator entry real ident names).filesystem target
          items after)
      (fun _ _ => True) :=
  Construction.copy_io
    (Construction.copy_corresponds_ofIO observer enumerator.observer rfl rfl entry real ident names)
    readsEntry readsReal readsNames readsBytes directories files source target selected 4096 w

/-- The exact plain tree of the generated-workspace function callers run, under the same native
primitive hypotheses as `observer_copy`. -/
theorem observer_construct
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String)
    (readsEntry : ReadsEntry (observedConstruction entry real ident names).filesystem)
    (readsReal : ReadsReal (observedConstruction entry real ident names).filesystem)
    (readsNames : Construction.ReadsNames (observedConstruction entry real ident names))
    (directories : Construction.CreatesDirectories (observedConstruction entry real ident names))
    (files : Construction.CreatesFiles (observedConstruction entry real ident names))
    (target : FilePath) (items : List Construction.Item) (w : Void IO.RealWorld) :
    RunsTo id (construct target items w)
      (fun _ after => Construction.Holds
        (observedConstruction entry real ident names).filesystem target items after) (fun _ _ => True) :=
  Construction.construct_io
    (Construction.copy_corresponds_ofIO observer Construction.observer rfl rfl entry real ident names)
    readsEntry readsReal readsNames directories files target items w

/-- The actual writer that copyFile and writeFile run retains an established plain parent and
adds exactly its regular-file instruction. The initial tree is an explicit precondition;
an arbitrary pre-existing directory is not authenticated by this theorem. -/
theorem observer_appendFile
    (entry : Void IO.RealWorld → FilePath → Option IO.FS.FileType)
    (real : Void IO.RealWorld → FilePath → Option FilePath)
    (ident : Void IO.RealWorld → FilePath → Option FileId)
    (names : Void IO.RealWorld → FilePath → List String)
    (readsEntry : ReadsEntry (observedConstruction entry real ident names).filesystem)
    (readsReal : ReadsReal (observedConstruction entry real ident names).filesystem)
    (directories : Construction.CreatesDirectories (observedConstruction entry real ident names))
    (files : Construction.CreatesFiles (observedConstruction entry real ident names))
    (parent : FilePath) (name : String) (bytes : ByteArray) (rights : UInt32)
    (done : List Construction.Item) (w : Void IO.RealWorld)
    (initial : Construction.Holds (observedConstruction entry real ident names).filesystem parent done w) :
    RunsTo id (Construction.appendFileWith Construction.observer parent name bytes rights w)
      (fun _ after => Construction.Holds (observedConstruction entry real ident names).filesystem
        parent (done ++ [⟨[name], .file bytes rights⟩]) after) (fun _ _ => True) :=
  Construction.appendFile_io
    (Construction.copy_corresponds_ofIO observer Construction.observer rfl rfl entry real ident names)
    readsEntry readsReal directories files parent name bytes rights done w initial

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

/-- `name` is the name of one entry of a directory: not empty, `.` or `..`, and with no path
separator, so a path whose last component it is names that entry of the directory before it. -/
def IsEntryName (name : String) : Prop :=
  name ≠ "" ∧ name ≠ "." ∧ name ≠ ".." ∧
    ∀ c ∈ name.toList, c ∉ FilePath.pathSeparators

instance (name : String) : Decidable (IsEntryName name) := by
  unfold IsEntryName; infer_instance

/-- The name of one entry of a directory (`IsEntryName`). -/
structure EntryName where
  /-- The name. -/
  name : String
  /-- The name is the name of one entry. -/
  isEntry : IsEntryName name

/-- `name` as the name of one entry, or `none` when it is empty, `.` or `..`, or has a path
separator. -/
def EntryName.of? (name : String) : Option EntryName :=
  if h : IsEntryName name then some ⟨name, h⟩ else none

/-- The path that the names `names` give, from the root of the file system when `absolute` holds
and from the working directory otherwise: each name follows the one before it after a path
separator, with no use of `FilePath.join`, which gives its second path alone when that is
absolute. -/
def namesPath (absolute : Bool) (names : List String) : FilePath :=
  if absolute then
    if names.isEmpty then ⟨FilePath.pathSeparator.toString⟩
    else ⟨String.join (names.map (FilePath.pathSeparator.toString ++ ·))⟩
  else if names.isEmpty then "." else mkFilePath names

/-- The place of an entry that `moveAside` moves: the names of the directories above it, from the
root of the file system when `absolute` holds and from the working directory otherwise, and its own
name. -/
structure AsidePlace where
  /-- Whether the names are from the root of the file system. -/
  absolute : Bool
  /-- The names of the directories above the entry. -/
  above : List String
  /-- The entry's own name. -/
  name : EntryName

/-- The place of the entry at `path`, or why `moveAside` does not move it: an empty path, or one
whose last component is `.` or `..`, which `rename(2)` does not rename. The empty components of
`path` are dropped, so `out/` names `out`, and a symbolic link at `out` is moved itself. -/
def AsidePlace.ofPath (path : FilePath) : Except String AsidePlace :=
  let names := path.components.filter (!·.isEmpty)
  match names.getLast? with
  | none => .error "it is an empty path"
  | some last =>
    match EntryName.of? last with
    | some name => .ok { absolute := path.isAbsolute, above := names.dropLast, name }
    | none => .error "its last component is `.` or `..`"

/-- The path of the entry at `p`. -/
def AsidePlace.path (p : AsidePlace) : FilePath :=
  namesPath p.absolute (p.above ++ [p.name.name])

/-- The path of the new directory named `aside` beside the entry at `p`. -/
def AsidePlace.aside (p : AsidePlace) (aside : EntryName) : FilePath :=
  namesPath p.absolute (p.above ++ [aside.name])

/-- The path of the entry at `p` in its new directory named `aside`, under its own name. -/
def AsidePlace.moved (p : AsidePlace) (aside : EntryName) : FilePath :=
  namesPath p.absolute (p.above ++ [aside.name, p.name.name])

/-- The name of the new directory for an entry named `name`, with the suffix `suffix`, or `none`
when that is not the name of one entry. -/
def asideName (name : EntryName) (suffix : String) : Option EntryName :=
  EntryName.of? s!"{name.name}.regula-refused-{suffix}"

/-- An operation of a move aside (`AsidePlace.plan`). No operation removes an entry. -/
inductive AsideOperation where
  /-- Make a directory with `IO.FS.createDir`, which fails when anything is at the path. -/
  | makeDirectory (path : FilePath)
  /-- Rename the entry at the first path to the second with `IO.FS.rename`. -/
  | rename (source destination : FilePath)

/-- The operations that `moveAside` runs at `p`, where it observed whether something is
(`present`), with the name `aside` of its new directory: none when nothing is there, and otherwise
the making of the new directory beside the entry, then the rename of the entry into it under its
own name. -/
def AsidePlace.plan (p : AsidePlace) (present : Bool) (aside : EntryName) : List AsideOperation :=
  if present then [.makeDirectory (p.aside aside), .rename p.path (p.moved aside)] else []

/-- Run one operation of a move aside: `IO.FS.createDir` or `IO.FS.rename` (`observeRename`). -/
private def runAside : AsideOperation → IO Unit
  | .makeDirectory path => IO.FS.createDir path
  | .rename source destination => observeRename source destination

/-- Whether something is at `path`, by a read that follows no symbolic link there
(`observeMetadata`): a symbolic link is something, also one whose target is absent. A failure of
the read other than an absent path stops it. -/
private def observePresent (path : FilePath) : IO Bool :=
  tryCatch (do discard (observeMetadata path); pure true) fun
    | .noFileOrDirectory .. => pure false
    | error => throw error

/-- A suffix for the name of a new directory: 16 hexadecimal digits from `IO.getRandomBytes`. The
directory is new because `moveAside` makes it with `mkdir(2)`, which fails when anything is there;
the suffix only makes that failure unlikely. -/
private def freshSuffix : IO String := do
  let digit (byte : UInt8) : String := String.ofList ((Nat.toDigits 16 (byte.toNat + 256)).drop 1)
  return (← IO.getRandomBytes 8).foldl (fun suffix byte => suffix ++ digit byte) ""

/-- Move the entry at `path`, whatever it is, aside, and give where it is now, or `none` when
nothing is there. It takes the place of the entry from `path` (`AsidePlace.ofPath`), observes
whether something is there (`observePresent`), names a new directory beside it
(`asideName`, `freshSuffix`) and runs the operations of that observation (`AsidePlace.plan`) in
order, stopping at the first that fails. The entry's name and the new directory's name are each the
name of one entry (`EntryName`), so the new directory is beside the entry and the rename moves the
entry into it. When the directory is made, it is new and empty, so the rename replaces nothing. A
symbolic link at `path` is moved, not the file that it points to. It removes nothing, and a copy
that it moves aside stays there. It stops before it acts on Windows, where Lean 4.34.1 renames with
`MoveFileEx` and replaces what is there (`src/runtime/io.cpp#L1219-L1222`).

Assumes: POSIX.1-2024 (https://pubs.opengroup.org/onlinepubs/9799919799/functions/mkdir.html,
https://pubs.opengroup.org/onlinepubs/9799919799/functions/rename.html). `mkdir()` is exclusive:
it fails with `EEXIST` when anything is at the path, a symbolic link among them. `rename()` is
atomic within one file system, renames a symbolic link at its first path itself and does not follow
it, removes nothing when nothing is at its second path, and fails with `EXDEV` across file systems
and with `EBUSY` or `EXDEV` on a mount point. Lean 4.34.1's `IO.FS.createDir` calls `mkdir` and
`IO.FS.rename` calls `rename` on these systems (`src/runtime/io.cpp#L1181-L1195`, `#L1209-L1236`).
No process makes an entry in the new directory between the two operations, which is trusted. -/
def moveAside (path : FilePath) : IO (Option FilePath) := do
  if System.Platform.isWindows then
    throw (windowsRefusal "rename" path "IO.FS.rename replaces what is at its destination")
  let place ← match AsidePlace.ofPath path with
    | .ok place => pure place
    | .error reason => throw (IO.userError reason)
  let present ← observePresent place.path
  let some aside := asideName place.name (← freshSuffix)
    | throw (IO.userError s!"the name of a new directory beside {place.path} is not the name of \
        one entry")
  (place.plan present aside).forM runAside
  return if present then some (place.moved aside) else none

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
    let directory ← observeRealPath (← Regula.Process.currentDir)
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

/-- The real path of the directory `root`, which a program of Regula owns, after it makes the
directory and its absent ancestors (`IO.FS.createDirAll`): `observeRealPath` resolves it once.
The root and its ancestors may be symbolic links that the adopter placed, such as a `.lake` that is
a link to a different disk. Each removal below the root is decided at its real path, so
`removeOwn` there refuses a symbolic link below the root, not one at the root or above it. It stops
on Windows, where the observer reads no real path. -/
def ownRoot (root : FilePath) : IO FilePath := do
  IO.FS.createDirAll root
  observeRealPath root

/-- `removeOwn` at `ownPath path`, so a relative path is read below the real working directory. -/
def removePath (kind : Kind) (path : FilePath) : IO Unit := do
  removeOwn kind (← ownPath path)

/-- `replace` at `ownPath source` and `ownPath destination`. -/
def replacePath (source destination : FilePath) : IO Unit := do
  replace (← ownPath source) (← ownPath destination)

/-- Stop unless nothing is at `path` or a directory is there at its own place, by the observation
that `removeOwn` makes. These are the places on which `removal .directory` does not refuse
(`removal_remove_iff`, `removal_nothing_iff`), so a symbolic link, a file and a path through a
symbolic link at `path` make it stop. -/
def requireOwnDirectory (path : FilePath) : IO Unit := do
  if removal .directory (← observe observer path) == .refuse then
    throw <| IO.userError s!"{path} is not a directory at its own place (a symbolic link, a file, \
      or a path through a symbolic link is there)"

/-- Stop unless nothing is at `path`, or a directory is there at its own place
(`requireOwnDirectory`) and each of its entries is a directory or a file, by a read that follows no
link at the entry. A symbolic link among the entries, also one whose target is absent, makes it
stop, so a file that a later operation opens by its name in this directory is not reached through
a link, when no process makes one after this check, which is trusted. -/
def requireNoLinkedEntries (path : FilePath) : IO Unit := do
  requireOwnDirectory path
  unless (← place path) matches .present .directory do return
  for entry in ← Regula.Filesystem.Construction.listDirectory path do
    unless (← place entry.path) matches .present .directory | .present .file do
      throw <| IO.userError s!"{entry.path} is not a directory or a file (a symbolic link or \
        another kind of entry is there)"

/-! ## The text of a file that may be absent -/

/-- The outcome of a read as an optional value: `none` for Lean's `noFileOrDirectory` error, the
one it gives for `ENOENT` (`Absent`), and each other error kept (`present_eq_ok_none_iff`,
`present_error`). -/
def present {α : Type} : Except IO.Error α → Except IO.Error (Option α)
  | .ok value => .ok (some value)
  | .error (.noFileOrDirectory ..) => .ok none
  | .error error => .error error

/-- `present` gives `none` exactly for an error that says nothing is at the path. -/
theorem present_eq_ok_none_iff {α : Type} (read : Except IO.Error α) :
    present read = .ok none ↔ ∃ error, read = .error error ∧ Absent error := by
  cases read with
  | ok value => simp [present]
  | error error => cases error <;> simp [present, Absent]

/-- `present` keeps each error that does not say that nothing is at the path. -/
theorem present_error {α : Type} (error : IO.Error) (h : ¬Absent error) :
    present (.error error : Except IO.Error α) = .error error := by
  cases error <;> simp_all [present, Absent]

/-- The text of the file at `path`, read with `IO.FS.readFile`, which follows symbolic links, or
`none` when Lean reports that nothing is there (`present`). Each other failure, such as a
permission error or a directory in the file's place, is thrown. `System.FilePath.pathExists`
instead reports each failure of its metadata read as absence. -/
def readFileIfPresent (path : FilePath) : IO (Option String) := do
  MonadExcept.ofExcept (present (← (IO.FS.readFile path).toBaseIO))

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
