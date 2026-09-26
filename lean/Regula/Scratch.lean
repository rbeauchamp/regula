/-! Scratch directories under a checkout's `tmp/`, and reclamation of those whose run died.

Every scratch directory is created and removed while its process holds a shared lock on
`tmp/.scratch.lock`. A process that dies, for example at `scripts/verify.sh`'s SIGKILL
deadline, cannot remove its directory, but the kernel releases its lock. So whenever the
lock can be taken exclusively, no scratch owner is alive and every scratch-named directory
is an orphan; the next scratch user removes them before creating its own. A name is
admitted at creation only if the recognizer that reclamation uses accepts it, so every
directory created here is reclaimable. File locking, process death and directory removal
are trusted operating-system effects; a directory that another program gives a
scratch-shaped name under `tmp/` is reclaimed too. -/
namespace Regula.Scratch
open System

/-- The lock file, directly under `tmp/`. -/
def lockName : String := ".scratch.lock"

/-- A nonempty decimal numeral. -/
def isNumeral (part : String) : Bool :=
  !part.isEmpty && part.all Char.isDigit

/-- A nonempty stem part of letters, digits, `_` or `.`, not starting with `.`. -/
def isStemPart (part : String) : Bool :=
  !part.isEmpty && !part.startsWith "." && part.all fun c => c.isAlphanum || c == '_' || c == '.'

/-- Names created here, `<stem>-<pid>-<nanos>-<random>`, and the earlier qualification form
`<stem>-<byte>-…-<byte>-` with sixteen bytes, whose orphans are reclaimed as well. Either is
one path component: parts contain no separator. -/
def isScratchName (name : String) : Bool :=
  let parts := name.splitOn "-"
  let stemOf (suffix : Nat) := parts.length > suffix && (parts.take (parts.length - suffix)).all isStemPart
  let current := stemOf 3 && (parts.drop (parts.length - 3)).all isNumeral
  let earlier := stemOf 17 && parts.getLast? == some "" &&
    ((parts.drop (parts.length - 17)).take 16).all isNumeral
  current || earlier

private def suffix : IO String := do
  let bytes ← IO.getRandomBytes 8
  let random := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
  return s!"{← IO.Process.getPID}-{← IO.monoNanosNow}-{random}"

/-- Remove every scratch-named directory directly under `tmp`, never following a link.
The caller holds the scratch lock exclusively. A failed removal is reported, not fatal. -/
private def reclaim (tmp : FilePath) : IO Unit := do
  let mut reclaimed := 0
  for entry in ← tmp.readDir do
    if isScratchName entry.fileName then
      try
        if (← entry.path.symlinkMetadata).type == .dir then
          IO.FS.removeDirAll entry.path
          reclaimed := reclaimed + 1
      catch error =>
        IO.eprintln s!"scratch: could not reclaim {entry.path}: {error}"
  if reclaimed > 0 then
    IO.eprintln s!"scratch: reclaimed {reclaimed} orphaned scratch directories under {tmp}"

/-- Run `action` in a fresh scratch directory under `root/tmp` and remove it on normal or
exceptional return, holding the scratch lock shared throughout. When no scratch owner is
alive, orphans are reclaimed first. Returns the value and the removed directory's path;
the path is returned only after its removal returned. Random naming is not a logical
freshness proof. -/
def withScratch (root : FilePath) (stem : String) (action : FilePath → IO α) :
    IO (α × FilePath) := do
  let tmp := root / "tmp"
  IO.FS.createDirAll tmp
  let lock ← IO.FS.Handle.mk (tmp / lockName) .append
  if ← lock.tryLock then
    try reclaim tmp finally lock.unlock
  lock.lock (exclusive := false)
  try
    let name := s!"{stem}-{← suffix}"
    unless isScratchName name do
      throw <| IO.userError s!"scratch name {name} would not be reclaimable"
    let path := tmp / name
    if ← path.pathExists then
      throw <| IO.userError s!"refusing to reuse scratch path {path}"
    IO.FS.createDir path
    let value ← try action path finally IO.FS.removeDirAll path
    return (value, path)
  finally
    lock.unlock

end Regula.Scratch
