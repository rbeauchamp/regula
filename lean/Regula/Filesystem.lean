import RegulaCore.Filesystem

/-! # The observer of the filesystem

The filesystem operations of Lean's library that `Regula.Filesystem.Ops` names, as code written
over `Ops` runs them: each operation of `observer` is a definition of this module that calls one of
them. That they correspond to some model of the filesystem (`Corresponds`) that satisfies the other
assumptions (`RegulaCore.Filesystem`) is the trusted step. The theorems at the end of this module
state, under those hypotheses, what the code of `RegulaCore.Filesystem` does when it runs at the
observer. Other code of Regula still calls these operations of Lean's library directly, and no
check finds those calls yet.

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

section Observer

variable {M : Model} {view : Void IO.RealWorld → M.World}

/-- **Checked, at the observer:** when `removeDirectory observer` succeeds, nothing is at the path,
when the observer corresponds to a model that satisfies `ReadsEntry`. -/
theorem observer_removeDirectory_gone (corresponds : Corresponds observer M view)
    (reads : ReadsEntry M) (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeDirectory observer path w) (fun _ s => M.entry s path = none)
      (fun _ _ => True) :=
  removeDirectory_gone_io corresponds reads path w

/-- **Checked, at the observer:** when `removeEntry observer` succeeds, nothing is at the path,
when the observer corresponds to a model that satisfies `ReadsEntry`. -/
theorem observer_removeEntry_gone (corresponds : Corresponds observer M view)
    (reads : ReadsEntry M) (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (removeEntry observer path w) (fun _ s => M.entry s path = none)
      (fun _ _ => True) :=
  removeEntry_gone_io corresponds reads path w

/-- `removeDirectory observer` of a directory at its own place removes it and keeps the type of
each entry outside it, and when it fails it kept them, when the observer corresponds to a model
that satisfies `ReadsEntry` and `RemovesTree`. -/
theorem observer_removeDirectory (corresponds : Corresponds observer M view)
    (reads : ReadsEntry M) (removes : RemovesTree M) (path : FilePath) (w : Void IO.RealWorld)
    (directory : M.entry (view w) path = some .dir) (own : M.real (view w) path = some path) :
    RunsTo view (removeDirectory observer path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s)
      (fun _ s => M.Unchanged path (view w) s) :=
  removeDirectory_io corresponds reads removes path w directory own

/-- `removeEntry observer` of a path at its own place removes it and keeps the type of each entry
outside it, and when it fails it kept them, when the observer corresponds to a model that satisfies
`ReadsEntry` and `RemovesEntry`. -/
theorem observer_removeEntry (corresponds : Corresponds observer M view)
    (reads : ReadsEntry M) (removes : RemovesEntry M) (path : FilePath) (w : Void IO.RealWorld)
    (own : M.real (view w) path = some path) :
    RunsTo view (removeEntry observer path w)
      (fun _ s => M.entry s path = none ∧ M.Unchanged path (view w) s)
      (fun _ s => M.Unchanged path (view w) s) :=
  removeEntry_io corresponds reads removes path w own

/-- `atOwnPlace observer` never fails, ends in a world read as the same state, and gives `true`
exactly when the real path of the path is the path, when the observer corresponds to a model that
satisfies `ReadsReal`. -/
theorem observer_atOwnPlace (corresponds : Corresponds observer M view) (reads : ReadsReal M)
    (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo view (atOwnPlace observer path w)
      (fun same s => s = view w ∧ (same = true ↔ M.real (view w) path = some path))
      (fun _ _ => False) :=
  atOwnPlace_io corresponds reads path w

end Observer

end Regula.Filesystem
