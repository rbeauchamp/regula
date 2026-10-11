import RegulaCore.Filesystem

/-! # The observer of the filesystem

The filesystem operations of Lean's library that `Regula.Filesystem.Ops` names, as code written
over `Ops` runs them: each operation of `observer` is a definition of this module that calls one of
them. The observer's runs are a model of the filesystem (`observed`), whose states are the worlds
of `IO`. That the observer satisfies the assumptions of `RegulaCore.Filesystem` at that model is the
trusted step. The theorems at the end of this module state, under those assumptions, what the code
of `RegulaCore.Filesystem` does when it runs at the observer. Other code of Regula still calls these
operations of Lean's library directly, and no check finds those calls yet.

Each operation is `@[noinline]`, so its call of the library's operation stays in its own compiled
code and is not copied into a caller's. On Windows, Lean 4.34.1's
`System.FilePath.symlinkMetadata` follows a symbolic link at the path, which `ReadsEntry` does not
allow, and `IO.FS.removeDirAll` uses it on each entry. Its `IO.FS.realPath` gives the path itself
when it cannot resolve it (`runtime/io.cpp#L1032-L1033`), which `ReadsReal` does not allow. So on
Windows the observer's read of an entry, its read of a real path and its removal of a directory
fail without acting, and every removal that reads the entry first fails. -/

namespace Regula.Filesystem

open System Regula.StateTriple

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
def observeRemoveDirAll (path : FilePath) : IO Unit :=
  if System.Platform.isWindows then throw (windowsRefusal "removeDirAll" path linkFollowed)
  else IO.FS.removeDirAll path

/-- `IO.FS.removeFile`. -/
@[noinline, regula_observer filesystem]
def observeRemoveFile (path : FilePath) : IO Unit :=
  IO.FS.removeFile path

/-- The filesystem's operations in `IO`, which Regula's code runs. -/
@[regula_observer filesystem]
def observer : Ops IO where
  symlinkMetadata := observeMetadata
  realPath := observeRealPath
  removeDirAll := observeRemoveDirAll
  removeFile := observeRemoveFile

/-! ## The removals at the observer -/

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

/-- **Checked, at the observer:** when `removeDirectory observer` succeeds from a world, nothing is
at the path at the world it ends in, when the observer satisfies `ReadsEntry`. -/
theorem observer_removeDirectory_gone (reads : ReadsEntry (observed entry real ident))
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (removeDirectory observer path w) (fun _ s => entry s path = none)
      (fun _ _ => True) :=
  removeDirectory_gone_io (corresponds_ofIO observer entry real ident) reads path w

/-- **Checked, at the observer:** when `removeEntry observer` succeeds from a world, nothing is at
the path at the world it ends in, when the observer satisfies `ReadsEntry`. -/
theorem observer_removeEntry_gone (reads : ReadsEntry (observed entry real ident))
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (removeEntry observer path w) (fun _ s => entry s path = none) (fun _ _ => True) :=
  removeEntry_gone_io (corresponds_ofIO observer entry real ident) reads path w

/-- `removeDirectory observer` of a directory at its own place removes it and keeps the entry at
each path of its frame (`Model.Unchanged`), each path not spelled within the directory, below a
parent at its own real path, whose file before is not an entry of the directory's tree
(`Model.Below`), and when it fails it kept them, when the observer satisfies `ReadsEntry` and
`RemovesTree`. -/
theorem observer_removeDirectory (reads : ReadsEntry (observed entry real ident))
    (removes : RemovesTree (observed entry real ident)) (path : FilePath) (w : Void IO.RealWorld)
    (directory : entry w path = some .dir) (own : real w path = some path) :
    RunsTo id (removeDirectory observer path w)
      (fun _ s => entry s path = none ∧ (observed entry real ident).Unchanged path w s)
      (fun _ s => (observed entry real ident).Unchanged path w s) :=
  removeDirectory_io (corresponds_ofIO observer entry real ident) reads removes path w directory own

/-- `removeEntry observer` of a path at its own place removes it and keeps the entry at each path of
its frame (`Model.Unchanged`), each path not spelled within the path, below a parent at its own
real path, whose file before is not an entry of the path's tree (`Model.Below`), and when it fails
it kept them, when the observer satisfies `ReadsEntry` and `RemovesEntry`. -/
theorem observer_removeEntry (reads : ReadsEntry (observed entry real ident))
    (removes : RemovesEntry (observed entry real ident)) (path : FilePath) (w : Void IO.RealWorld)
    (own : real w path = some path) :
    RunsTo id (removeEntry observer path w)
      (fun _ s => entry s path = none ∧ (observed entry real ident).Unchanged path w s)
      (fun _ s => (observed entry real ident).Unchanged path w s) :=
  removeEntry_io (corresponds_ofIO observer entry real ident) reads removes path w own

/-- `atOwnPlace observer` never fails, ends in the world it starts from, and gives `true` exactly
when the real path of the path is the path, when the observer satisfies `ReadsReal`. -/
theorem observer_atOwnPlace (reads : ReadsReal (observed entry real ident))
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (atOwnPlace observer path w)
      (fun same s => s = w ∧ (same = true ↔ real w path = some path)) (fun _ _ => False) :=
  atOwnPlace_io (corresponds_ofIO observer entry real ident) reads path w

end Observer

end Regula.Filesystem
