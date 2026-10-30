module

/-! # Whether a path is present

Lean 4.35.0's `System.FilePath.pathExists` and `System.FilePath.isDir` give `false` for every error
of their `metadata` read, not only for a missing file (`Init/System/IO.lean:1162-1172`), so a
permission error, an I/O error or a path that is too long reads as absence. The reads of this
module give absence only for the error that says that nothing is at the path, and throw every other
error. `Regula.Filesystem.isPresent_runsTo` and `isDirectory_runsTo` state what each run gives. No
check refuses a use of the two predicates of Lean in Regula's code.

The module imports only the toolchain's prelude and is in the module system, so each module of
Regula, in it or not, can import it. Code that cannot import it defines its own copy, and a theorem
proves that copy equal to the read here (`Regula.Filesystem.isPresent_eq_match`,
`isDirectory_eq_match`): a program that runs before the package is built, and the copy program,
whose source cold drivers run. -/

@[expose] public section

namespace Regula.Filesystem

open System

/-- The outcome of a read as an optional value: `none` for Lean's `noFileOrDirectory` error, the
one it gives for `ENOENT` (`Absent`), and each other error kept (`present_eq_ok_none_iff`,
`present_error`). -/
def present {α : Type} : Except IO.Error α → Except IO.Error (Option α)
  | .ok value => .ok (some value)
  | .error (.noFileOrDirectory ..) => .ok none
  | .error error => .error error

/-- The metadata of the file at `path`, read with `System.FilePath.metadata`, which follows
symbolic links as `pathExists` does, or `none` when Lean reports that nothing is there (`present`).
Each other failure, such as a permission error, is thrown (`metadataIfPresent_ok`,
`metadataIfPresent_absent`, `metadataIfPresent_error`).

Assumes: Lean v4.35.0 `metadata` (`Init/System/IO.lean:1149`) is `lean_io_metadata`
(`runtime/io.cpp:1143-1158`), which calls `stat(2)` through libuv and gives `noFileOrDirectory` for
`ENOENT` and for no other error (`runtime/io.cpp:201`, `:276-279`). A dangling symbolic link is
therefore absent, and a path through a file (`ENOTDIR`) is an error. -/
def metadataIfPresent (path : FilePath) : IO (Option IO.FS.Metadata) := do
  MonadExcept.ofExcept (present (← path.metadata.toBaseIO))

/-- Whether a file is at `path`, following symbolic links: `false` only when Lean reports that
nothing is there, and every other failure of the read thrown (`metadataIfPresent`,
`isPresent_runsTo`). -/
def isPresent (path : FilePath) : IO Bool :=
  return (← metadataIfPresent path).isSome

/-- Whether a directory is at `path`, following symbolic links: `false` when another kind of file is
there or Lean reports that nothing is, and every other failure of the read thrown
(`metadataIfPresent`, `isDirectory_runsTo`). -/
def isDirectory (path : FilePath) : IO Bool :=
  return (← metadataIfPresent path).any (·.type == .dir)

/-- The real path of `path`, or `none` when Lean reports that nothing is there (`isPresent`), and
every other failure thrown (`realPathIfPresent_absent`, `realPathIfPresent_error`,
`realPathIfPresent_present`). Lean's `IO.FS.realPath` gives `noFileOrDirectory` for every failure
of `realpath(3)` on POSIX, a denied permission among them, so its error cannot say that nothing is
there: the read of `metadata` decides that, and a failure of the resolution after it is thrown.

Assumes: Lean v4.35.0 `realPath` (`Init/System/IO.lean:879`) is `lean_io_realpath`
(`runtime/io.cpp:1014-1067`), whose POSIX branch calls `realpath(3)` and gives
`noFileOrDirectory` with `ENOENT` for each of its failures (`runtime/io.cpp:86-91`, `:1054-1066`).
`realpath(3)`, like `stat(2)`, follows each symbolic link. -/
def realPathIfPresent (path : FilePath) : IO (Option FilePath) := do
  if ← isPresent path then return some (← IO.FS.realPath path) else return none

/-- The text of the file at `path`, or `none` when Lean reports that nothing is there (`present`);
each other failure is thrown. -/
def readFileIfPresent (path : FilePath) : IO (Option String) := do
  MonadExcept.ofExcept (present (← (IO.FS.readFile path).toBaseIO))

end Regula.Filesystem
