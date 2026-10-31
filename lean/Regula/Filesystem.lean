import RegulaCore.CopyConstruction
import RegulaCore.Presence

/-! # The reads of the filesystem, and the copy construction at the real operations

The filesystem operations of Lean's library that `Regula.Filesystem.Ops` names, as the copy
construction of the acceptance and provisioning drivers runs them (`observer`, `copy`, `construct`),
with the theorems that describe the tree it makes. The other programs of the repository read
through `isPresent`, `isDirectory`, `readFileIfPresent`, `entryIfPresent` and `realPathIfPresent`.

Neither `lint` nor `regula` imports this module (`Regula.Effects.check`). It offers no operation
that removes or moves an entry on a caller's behalf: `withOwnTempDir`, which the controls of the
copy construction and of the prose checks use, removes only the directory that it made.

On Windows, Lean 4.35.0's `System.FilePath.symlinkMetadata` follows a symbolic link at the path,
which `ReadsEntry` does not allow. Its
`IO.FS.realPath` gives the path itself when it cannot resolve it (`runtime/io.cpp#L1032-L1033`),
which `ReadsReal` does not allow. So on Windows the observer's read of an entry, its read of a real
path fail without acting.

`readFileIfPresent` is not an operation of the observer: it calls `IO.FS.readFile` directly, and
gives `none` only for the error that says that nothing is at the path (`present`). Neither are
`isPresent`, `isDirectory` and `metadataIfPresent` of `RegulaCore.Presence`, which Regula's code
reads in place of Lean's `System.FilePath.pathExists` and `System.FilePath.isDir`: they read
`System.FilePath.metadata`, which follows links, and give absence only for that error too
(`isPresent_runsTo`, `isDirectory_runsTo`). `entryIfPresent` is the same read of the entry itself,
by the observer. -/

namespace Regula.Filesystem

open System Regula.StateTriple

/-- `System.FilePath.symlinkMetadata`, which fails on Windows. -/
@[noinline]
def observeMetadata (path : FilePath) : IO IO.FS.Metadata :=
  Construction.observeMetadata path

/-- `IO.FS.realPath`, which fails on Windows. -/
@[noinline]
def observeRealPath (path : FilePath) : IO FilePath :=
  Construction.observeRealPath path

/-- The filesystem's operations in `IO`, which Regula's code runs. -/
private def observer : Ops IO where
  symlinkMetadata := observeMetadata
  realPath := observeRealPath

/-! ## Construction -/

/-- Capture selected source directories and regular files through the no-follow observer and
construct them exclusively. Links and special entries are refused before they can be opened.
`observer_copy` describes the exact resulting tree, under native primitive hypotheses.

Assumes: Lean v4.35.0 lstat (`Init/System/IO.lean:1151-1156`, `runtime/io.cpp:1160-1179`), an
admitted listing program that exits nonzero after a failed read of a directory
(`Construction.ReadsNames` names each program `Construction.locate` admits, with its source),
exclusive mkdir (`runtime/io.cpp:1181-1195`), and exclusive file creation
(`Init/System/IO.lean:651-660`, `runtime/io.cpp:409`). The source and private destination have no
concurrent writer. Windows is refused. Modes are not preserved: copied regular files receive 0644.
Lake creates and sets modes on programs it builds. -/
def copy (source target : FilePath) (selected : FilePath → Bool := fun _ => true) :
    IO (List Construction.Item) := Construction.copy source target selected

/-- Construct a generated workspace through the same exclusive directory/file writer as `copy`.
The root is absent or privately owned and empty; its parent is at its own real path. -/
def construct (target : FilePath) (items : List Construction.Item) : IO Unit :=
  Construction.construct target items

/-- Read a regular source through the shared no-follow capture program. Neither links nor special
entries are consumed as source bytes. -/
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

/-- Run `action` in a new temporary directory, by its real path (on macOS the temporary directory is
below `/var`, a symbolic link to `/private/var`), and remove the directory afterwards, whether
`action` succeeds or fails. The path is the one that `IO.FS.createTempDir` just made. -/
def withOwnTempDir {α : Type} (action : FilePath → IO α) : IO α := do
  let directory ← IO.FS.realPath (← IO.FS.createTempDir)
  try action directory finally IO.FS.removeDirAll directory

/-! ## Whether a path is present, and the text of a file that may be absent

`present`, `metadataIfPresent`, `isPresent` and `isDirectory` are in `RegulaCore.Presence`, so that
each module of Regula can import them. The programs that cannot import it define their own copies,
each proved equal to the read here: the copy program's `Construction.isDirectory`
(`Construction.isDirectory_eq`), and the `isPresent` of each program that `lean --run` runs, in its
module of `Regula.ProgramCheck` (`isPresent_eq_match`). -/

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

section Presence

variable {path : FilePath} {w s : Void IO.RealWorld}

/-- When Lean's `System.FilePath.metadata` reads `metadata` at `path`, `metadataIfPresent` gives it,
and ends where the read ends. -/
theorem metadataIfPresent_ok {metadata : IO.FS.Metadata} (read : path.metadata w = .ok metadata s) :
    metadataIfPresent path w = .ok (some metadata) s := by
  unfold metadataIfPresent
  rw [eio_bind_ok (io_toBaseIO_ok read), io_ofExcept]
  rfl

/-- When the read fails with an error that says that nothing is at `path` (`Absent`),
`metadataIfPresent` gives `none`. -/
theorem metadataIfPresent_absent {error : IO.Error} (read : path.metadata w = .error error s)
    (absent : Absent error) : metadataIfPresent path w = .ok none s := by
  unfold metadataIfPresent
  rw [eio_bind_ok (io_toBaseIO_error read), io_ofExcept]
  cases error <;> simp_all [present, Absent]

/-- When the read fails with any other error, `metadataIfPresent` fails with it. -/
theorem metadataIfPresent_error {error : IO.Error} (read : path.metadata w = .error error s)
    (other : ¬Absent error) : metadataIfPresent path w = .error error s := by
  unfold metadataIfPresent
  rw [eio_bind_ok (io_toBaseIO_error read), io_ofExcept, present_error error other]

/-- When the read gives metadata, `isPresent` gives `true`. -/
theorem isPresent_ok {metadata : IO.FS.Metadata} (read : path.metadata w = .ok metadata s) :
    isPresent path w = .ok true s := by
  unfold isPresent
  rw [eio_bind_ok (metadataIfPresent_ok read), eio_pure]
  rfl

/-- When the read fails with an error that says that nothing is at `path`, `isPresent` gives
`false`, as `System.FilePath.pathExists` does. -/
theorem isPresent_absent {error : IO.Error} (read : path.metadata w = .error error s)
    (absent : Absent error) : isPresent path w = .ok false s := by
  unfold isPresent
  rw [eio_bind_ok (metadataIfPresent_absent read absent), eio_pure]
  rfl

/-- When the read fails with any other error, `isPresent` fails with it, where
`System.FilePath.pathExists` gives `false`. -/
theorem isPresent_error {error : IO.Error} (read : path.metadata w = .error error s)
    (other : ¬Absent error) : isPresent path w = .error error s := by
  unfold isPresent
  rw [eio_bind_error (metadataIfPresent_error read other)]

/-- When the read gives metadata, `isDirectory` gives whether its type is a directory. -/
theorem isDirectory_ok {metadata : IO.FS.Metadata} (read : path.metadata w = .ok metadata s) :
    isDirectory path w = .ok (metadata.type == .dir) s := by
  unfold isDirectory
  rw [eio_bind_ok (metadataIfPresent_ok read), eio_pure]
  rfl

/-- When the read fails with an error that says that nothing is at `path`, `isDirectory` gives
`false`, as `System.FilePath.isDir` does. -/
theorem isDirectory_absent {error : IO.Error} (read : path.metadata w = .error error s)
    (absent : Absent error) : isDirectory path w = .ok false s := by
  unfold isDirectory
  rw [eio_bind_ok (metadataIfPresent_absent read absent), eio_pure]
  rfl

/-- When the read fails with any other error, `isDirectory` fails with it, where
`System.FilePath.isDir` gives `false`. -/
theorem isDirectory_error {error : IO.Error} (read : path.metadata w = .error error s)
    (other : ¬Absent error) : isDirectory path w = .error error s := by
  unfold isDirectory
  rw [eio_bind_error (metadataIfPresent_error read other)]

end Presence

/-- What `isPresent` gives, by the run of Lean's `System.FilePath.metadata` from the same world:
`true` exactly when the read succeeds, `false` exactly when it fails with an error that says that
nothing is at the path (`Absent`), and every other error of the read, thrown, from the world the
read ends in. -/
theorem isPresent_runsTo (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (isPresent path w)
      (fun found s => if found then ∃ metadata, path.metadata w = .ok metadata s
        else ∃ error, path.metadata w = .error error s ∧ Absent error)
      (fun error s => path.metadata w = .error error s ∧ ¬Absent error) := by
  cases read : path.metadata w with
  | ok metadata s => rw [isPresent_ok read]; exact ⟨metadata, rfl⟩
  | error error s =>
    by_cases absent : Absent error
    · rw [isPresent_absent read absent]; exact ⟨error, rfl, absent⟩
    · rw [isPresent_error read absent]; exact ⟨rfl, absent⟩

/-- What `isDirectory` gives, by the run of Lean's `System.FilePath.metadata` from the same world:
`true` exactly when the read gives a directory, `false` exactly when it gives another kind of file
or fails with an error that says that nothing is at the path (`Absent`), and every other error of
the read, thrown. -/
theorem isDirectory_runsTo (path : FilePath) (w : Void IO.RealWorld) :
    RunsTo id (isDirectory path w)
      (fun found s => if found then
          ∃ metadata, path.metadata w = .ok metadata s ∧ metadata.type = .dir
        else (∃ metadata, path.metadata w = .ok metadata s ∧ metadata.type ≠ .dir) ∨
          ∃ error, path.metadata w = .error error s ∧ Absent error)
      (fun error s => path.metadata w = .error error s ∧ ¬Absent error) := by
  cases read : path.metadata w with
  | ok metadata s =>
    rw [isDirectory_ok read]
    by_cases directory : metadata.type = .dir
    · simp only [RunsTo, directory]; exact ⟨metadata, rfl, directory⟩
    · have other : (metadata.type == .dir) = false := by
        cases type : metadata.type <;> first | rfl | exact absurd type directory
      simp only [RunsTo, other]; exact .inl ⟨metadata, rfl, directory⟩
  | error error s =>
    by_cases absent : Absent error
    · rw [isDirectory_absent read absent]; exact .inr ⟨error, rfl, absent⟩
    · rw [isDirectory_error read absent]; exact ⟨rfl, absent⟩

/-- When Lean reports that nothing is at `path`, `realPathIfPresent` gives `none` and resolves
nothing. -/
theorem realPathIfPresent_absent {path : FilePath} {w s : Void IO.RealWorld} {error : IO.Error}
    (read : path.metadata w = .error error s) (absent : Absent error) :
    realPathIfPresent path w = .ok none s := by
  unfold realPathIfPresent
  rw [eio_bind_ok (isPresent_absent read absent)]
  exact eio_pure _ _

/-- Any other failure of the read is the failure of `realPathIfPresent`, which resolves nothing. -/
theorem realPathIfPresent_error {path : FilePath} {w s : Void IO.RealWorld} {error : IO.Error}
    (read : path.metadata w = .error error s) (other : ¬Absent error) :
    realPathIfPresent path w = .error error s := by
  unfold realPathIfPresent
  rw [eio_bind_error (isPresent_error read other)]

/-- When the read finds an entry, `realPathIfPresent` is the resolution, its failure included. -/
theorem realPathIfPresent_present {path : FilePath} {w s : Void IO.RealWorld}
    {metadata : IO.FS.Metadata} (read : path.metadata w = .ok metadata s) :
    realPathIfPresent path w = (do return some (← IO.FS.realPath path)) s := by
  unfold realPathIfPresent
  rw [eio_bind_ok (isPresent_ok read)]
  rfl

/-- `isPresent` as one match on Lean's read: the form of its copies in the code that cannot import
it, the programs that run with `lean --run` before the package is built (`RegulaProvision`,
`Regula.Release`). A theorem proves each copy equal to `isPresent` through this one
(`Regula.ProgramCheck.Provision.isPresent_eq`, `Regula.ProgramCheck.Release.isPresent_eq`). -/
theorem isPresent_eq_match : isPresent = (fun path => do
    match ← path.metadata.toBaseIO with
    | .ok _ => return true
    | .error (.noFileOrDirectory ..) => return false
    | .error error => throw error) := by
  funext path w
  show _ = (liftM (m := BaseIO) (n := IO) (path.metadata.toBaseIO) >>= _) w
  cases read : path.metadata w with
  | ok metadata s =>
    rw [isPresent_ok read, eio_bind_ok (io_toBaseIO_ok read)]
    exact (eio_pure _ _).symm
  | error error s =>
    rw [eio_bind_ok (io_toBaseIO_error read)]
    cases error with
    | noFileOrDirectory =>
      rw [isPresent_absent read trivial]
      exact (eio_pure _ _).symm
    | _ =>
      rw [isPresent_error read id]
      exact (eio_throw _ _).symm

/-- `isDirectory` as one match on the outcome of the read, the form that a program which cannot
import `RegulaCore.Presence` writes. -/
theorem isDirectory_eq_match : isDirectory = (fun path => do
    match ← path.metadata.toBaseIO with
    | .ok metadata => return metadata.type == .dir
    | .error (.noFileOrDirectory ..) => return false
    | .error error => throw error) := by
  funext path w
  show _ = (liftM (m := BaseIO) (n := IO) (path.metadata.toBaseIO) >>= _) w
  cases read : path.metadata w with
  | ok metadata s =>
    rw [isDirectory_ok read, eio_bind_ok (io_toBaseIO_ok read)]
    exact (eio_pure _ _).symm
  | error error s =>
    rw [eio_bind_ok (io_toBaseIO_error read)]
    cases error with
    | noFileOrDirectory =>
      rw [isDirectory_absent read trivial]
      exact (eio_pure _ _).symm
    | _ =>
      rw [isDirectory_error read id]
      exact (eio_throw _ _).symm

/-- The copy program's read of whether a directory is present is `isDirectory`. -/
theorem Construction.isDirectory_eq :
    Construction.isDirectory = Regula.Filesystem.isDirectory :=
  isDirectory_eq_match.symm

/-- The kind of the entry at `path` itself, by the observer's read, which follows no symbolic link
at `path` (`observeMetadata`), or `none` when Lean reports that nothing is there; every other
failure of the read is thrown (`RegulaCore.Filesystem.entryType`). It fails on Windows, where the
observer reads no entry.

Assumes: Lean v4.35.0 `symlinkMetadata` (`Init/System/IO.lean:1155-1156`) is
`lean_io_symlink_metadata` (`runtime/io.cpp:1160-1179`), which calls `lstat(2)` through libuv and
gives `noFileOrDirectory` for `ENOENT` and for no other error (`runtime/io.cpp:201`, `:276-279`). -/
def entryIfPresent (path : FilePath) : IO (Option IO.FS.FileType) :=
  entryType observer path

end Regula.Filesystem
