import Lake.Config.Defaults

/-! # Owned scratch directories

Scratch directories in Regula's own `.lake/regula-scratch/` under a project, and reclamation
of those whose run died. `directory` is the only place that location is derived, and
`withScratch`, the only source of a scratch path, creates nothing outside it. The Lake
directory holds build output, so a project's own walks of its sources already skip it.

Each scratch directory `<name>` is created only after its ownership marker `<name>.owner` was
created exclusively beside it, and the marker is removed only after the directory. Every
scratch directory is created and removed while its process holds a shared lock on `.lock`
there. A process that dies, for example at `scripts/verify.sh`'s SIGKILL deadline, cannot
remove its directory, but the kernel releases its lock. So whenever the lock can be taken
exclusively, no scratch owner is alive and every marked directory is an orphan; the next
scratch user removes them, then their markers, before creating its own. Nothing else is
removed: no unmarked entry, and nothing outside Regula's directory.

Regula v0.3.0 and earlier kept the same layout in the project's source tree, at
`tmp/.regula-scratch/` (`legacyDirectory`). Nothing is created there any more. Its orphans are
reclaimed under the same condition on its own lock, which those versions hold while they run;
the directory and its lock file are left in place. File locking, exclusive creation, process
death and directory removal are trusted operating-system effects. -/
namespace Regula.Scratch
open System

/-- Regula's own scratch directory, directly under the project's Lake directory. -/
def dirName : String := "regula-scratch"

/-- Regula's scratch directory of the project at `root`: `.lake/regula-scratch`, inside the
directory Lake keeps its own output in (`Lake.defaultLakeDir`). -/
def directory (root : FilePath) : FilePath := root / Lake.defaultLakeDir / dirName

/-- The name of the scratch directory Regula v0.3.0 and earlier kept under `tmp/`. -/
def legacyDirName : String := ".regula-scratch"

/-- The scratch directory Regula v0.3.0 and earlier used for the project at `root`,
`tmp/.regula-scratch` in its source tree. It is only read and reclaimed, never created. -/
def legacyDirectory (root : FilePath) : FilePath := root / "tmp" / legacyDirName

/-- The lock file, directly under a scratch directory. -/
def lockName : String := ".lock"

/-- The extension of an ownership marker, beside the directory it marks. -/
def markerExtension : String := "owner"

private def suffix : IO String := do
  let bytes ← IO.getRandomBytes 8
  let random := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
  return s!"{← IO.Process.getPID}-{← IO.monoNanosNow}-{random}"

/-- Kind of the path itself, without following a final symbolic link. -/
private def kind? (path : FilePath) : IO (Option IO.FS.FileType) := do
  try return some (← path.symlinkMetadata).type catch _ => return none

/-- Remove every marked directory directly under `dir`, then its marker, never following a
link. The caller holds the scratch lock exclusively. A failed removal is reported, not fatal. -/
private def reclaim (dir : FilePath) : IO Unit := do
  let mut reclaimed := 0
  for entry in ← dir.readDir do
    unless entry.path.extension == some markerExtension do continue
    let some name := entry.path.fileStem | continue
    let path := dir / name
    try
      if (← kind? entry.path) == some .file then
        match ← kind? path with
        | some .dir =>
          IO.FS.removeDirAll path
          IO.FS.removeFile entry.path
          reclaimed := reclaimed + 1
        | none => IO.FS.removeFile entry.path
        | some _ => pure ()
    catch error =>
      IO.eprintln s!"scratch: could not reclaim {path}: {error}"
  if reclaimed > 0 then
    IO.eprintln s!"scratch: reclaimed {reclaimed} orphaned scratch directories under {dir}"

/-- Reclaim the orphans under `dir` when its `lock` can be taken exclusively, which is when no
scratch owner there is alive. -/
private def reclaimIfIdle (dir : FilePath) (lock : IO.FS.Handle) : IO Unit := do
  if ← lock.tryLock then
    try reclaim dir finally lock.unlock

/-- Reclaim the orphans an older Regula left in `legacyDirectory root`. A run of such a version
holds that directory's lock shared while it owns scratch there, so the condition of
`reclaimIfIdle` identifies its orphans too. The lock is opened for reading only, so nothing is
created: a directory without a lock file holds no marker, since the lock was created first. The
directory and its lock file stay, since removing a lock file that a running older version may
open would let two runs hold different locks. A failure here is reported, not fatal. -/
private def reclaimLegacy (root : FilePath) : IO Unit := do
  let dir := legacyDirectory root
  let lock? ← try some <$> IO.FS.Handle.mk (dir / lockName) .read catch _ => pure none
  let some lock := lock? | return
  try reclaimIfIdle dir lock
  catch error => IO.eprintln s!"scratch: could not reclaim under {dir}: {error}"

/-- Run `action` in a fresh, marked scratch directory under `directory root` and remove it,
then its marker, on normal or exceptional return, holding the scratch lock shared throughout.
When no scratch owner is alive, orphans are reclaimed first, those of an older Regula under
`legacyDirectory root` included. Returns the value and the removed directory's path; the path
is returned only after its removal returned. Random naming is not a logical freshness proof. -/
def withScratch {α : Type} (root : FilePath) (stem : String) (action : FilePath → IO α) :
    IO (α × FilePath) := do
  let dir := directory root
  IO.FS.createDirAll dir
  let lock ← IO.FS.Handle.mk (dir / lockName) .append
  reclaimIfIdle dir lock
  reclaimLegacy root
  lock.lock (exclusive := false)
  try
    let path := dir / s!"{stem}-{← suffix}"
    let marker := path.addExtension markerExtension
    if ← path.pathExists then
      throw <| IO.userError s!"refusing to reuse scratch path {path}"
    discard <| IO.FS.Handle.mk marker .writeNew
    IO.FS.createDir path
    let value ← try action path finally
      IO.FS.removeDirAll path
      IO.FS.removeFile marker
    return (value, path)
  finally
    lock.unlock

end Regula.Scratch
