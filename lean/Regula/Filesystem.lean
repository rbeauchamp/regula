import RegulaCore.Filesystem

/-! # The observer of the filesystem

The filesystem operations of Lean's library that `Regula.Filesystem.Ops` names, as code written
over `Ops` runs them: each operation of `observer` is a definition of this module that calls one of
them. That each one behaves as the operation of some model of the filesystem that satisfies the
assumptions (`RegulaCore.Filesystem`) is the trusted step. Other code of Regula still calls these
operations of Lean's library directly, and no check finds those calls yet.

Each operation is `@[noinline]`, so its call of the library's operation stays in its own compiled
code and is not copied into a caller's. On Windows, Lean 4.34.1's
`System.FilePath.symlinkMetadata` follows a symbolic link at the path, which `ReadsEntry` does not
allow, and `IO.FS.removeDirAll` uses it on each entry. So on Windows the observer's read of an entry
and its removal of a directory fail without acting, and every removal that reads the entry first
fails. -/

namespace Regula.Filesystem

open System

/-- The error of an operation that the observer does not run on Windows. -/
def windowsRefusal (operation : String) (path : FilePath) : IO.Error :=
  IO.userError s!"{operation} {path}: refused on Windows, where Lean 4.34.1's \
    System.FilePath.symlinkMetadata follows a symbolic link at the path"

/-- `System.FilePath.symlinkMetadata`, which fails on Windows. -/
@[noinline, regula_observer filesystem]
def observeMetadata (path : FilePath) : IO IO.FS.Metadata :=
  if System.Platform.isWindows then throw (windowsRefusal "lstat" path)
  else path.symlinkMetadata

/-- `IO.FS.realPath`. -/
@[noinline, regula_observer filesystem]
def observeRealPath (path : FilePath) : IO FilePath :=
  IO.FS.realPath path

/-- `IO.FS.removeDirAll`, which fails on Windows. -/
@[noinline, regula_observer filesystem]
def observeRemoveDirAll (path : FilePath) : IO Unit :=
  if System.Platform.isWindows then throw (windowsRefusal "removeDirAll" path)
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

end Regula.Filesystem
