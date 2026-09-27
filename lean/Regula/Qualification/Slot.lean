import Regula.Checker.Snapshot
import Regula.Qualification.Support
import RegulaQualification.Json

/-! # Corpus producer slot

Corpus slot preparation. A `ProducerSlot` holds one physically independent copy
of the ROOT package (real byte copies, never hardlinks), prepared before the corpus
producer window and shared by every producer, which must not write it (no permission
enforces this; the `sharedIdentity` check refuses a changed end state rather than
preventing a write, and a write restored to identical content is not detected);
each producer writes only its own fresh workspace. Lake dependency packages are not
copied: the slot manifest names the captured original dependency roots. The ROOT copy and those dependency roots are
shared and must have no writer during the window. `SharedIdentity` checks the end
state of that requirement fail-closed: a content-level identity of every entry under every shared
root is captured before any producer starts and must be equal after every producer
has been joined. Shared permissions are never changed, so no permission state can
outlive the campaign (a killed campaign's scratch directory remains until the next scratch user
reclaims it; see `Regula.Scratch`). Producer children are waited and stream holders closed before
return (source-verified joined-worker discipline; no universal detached-grandchild
termination is claimed); the consumer path — control admission and terminal
qualification — consumes captured data and the real ROOT checkout and never
dereferences the slot path.
Preparation materializes self-contained Git metadata (worktree pointers,
`commondir`, `objects/info/alternates`, `core.worktree`) so the ROOT copy's Git
stays inside the slot, points manifest dependencies only at captured shared
roots, compares captured source/config inputs byte-exactly, records relocation
truthfully, and refuses on any containment violation. Filesystem, Git and
process behavior remain trusted IO, as throughout. -/
namespace Regula.Qualification.Slot
open Lean System RegulaQualification

/-- Producer-only writable environment ownership. -/
structure ProducerSlot where
  root : FilePath
  deriving Inhabited

/-- One prepared-file provenance record. `identity` is `"byte-identical"` when
the prepared bytes were compared equal to the captured input bytes, and
`"relocated"` when preparation truthfully rewrote path-bearing configuration. -/
structure FileProvenance where
  relativePath : String
  kind : String
  identity : String

/-- Prepared-slot provenance: truthful relocation records and containment
observations. No claim equates relocated bytes or relocated top-level paths with
the original ROOT paths. -/
structure SlotProvenance where
  originalRoot : String
  slotRoot : String
  revision : String
  files : Array FileProvenance

/-- Lexical path suffix of `path` under `root`. -/
def relativeOf (root path : FilePath) : FilePath :=
  let stem := root.toString ++ "/"
  FilePath.mk (if path.toString.startsWith stem then
    (path.toString.drop stem.length).toString else path.toString)

/-- Excluded copy-walk roots: scratch, tmp, nested slot directories and the
shared package recursion. -/
def excluded (relative : String) : Bool :=
  (relative.splitOn "/" |>.any fun part => part == "tmp" || part == "scratch" || part.startsWith "slot-")
    || relative == ".lake/packages" || relative.startsWith ".lake/packages/"

/-- True when `path` resolves inside `root` (executed normalization check).
Unresolvable paths are refused (fail closed): there is no lexical prefix
fallback, so unresolved `..`/absolute joins cannot pass. -/
def contained (root path : FilePath) : IO Bool := do
  try
    let resolved ← IO.FS.realPath path
    let base ← IO.FS.realPath root
    return resolved.toString == base.toString ||
      resolved.toString.startsWith (base.toString ++ "/")
  catch _ => return false

/-- Copy one file as an independent real byte copy (never a hardlink). -/
def copyFile (source target : FilePath) : IO Unit := do
  if let some parent := target.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile target (← IO.FS.readBinFile source)

/-- Metadata-preserving subtree copy through the system `cp` (argv only; no
shell interpolation of paths): `-R` recursive and `-p` permission/time
preservation on POSIX/Linux. Clone/CoW (`-c`) is optional and attempted first;
the real-copy `-p` path is the mandatory fallback (Linux CI has no clonefile).
Failures throw (fail closed). Only used after the guarded enumeration proves
the subtree has no excluded roots and no symlinks. -/
def copySubtreeSystem (source target : FilePath) : IO Unit := do
  let cloned ← run source "cp" #["-R", "-c", "-p", ".", target.toString]
  if cloned.exitCode == 0 then return
  let copied ← run source "cp" #["-R", "-p", ".", target.toString]
  unless copied.exitCode == 0 do
    throw <| IO.userError s!"slot subtree copy failed: {source} -> {target}\n{copied.stderr}"

private def isDirSafe (path : FilePath) : IO Bool := do
  try
    path.isDir
  catch _ => return false

/-- Fail-closed resolution helper: `none` marks an unresolvable path (classified
for the materializing fallback and refused at copy). -/
private def resolveSafe (path : FilePath) : IO (Option FilePath) := do
  try
    pure (some (← IO.FS.realPath path))
  catch _ => return none

/-- Directory depth bound of the slot walks (`scanTree`, `sharedWalk`), which makes them
total. A walk that reaches it fails closed. Under the trusted OS path limit (`PATH_MAX`:
4096 bytes on Linux, 1024 on macOS) a descent through real directories cannot reach it,
since each level adds at least two bytes, a separator and a name. Only `scanTree`, which
follows symlinks, can reach it, through a chain of more than 4096 distinct directories. -/
def maxWalkDepth : Nat := 4096

/-- Explicit scan-boundary traversal. Each directory scan carries the resolved
locations of its descent chain; a directory whose resolved location is already
on the chain is a cycle and is refused **at the scan boundary** (its entry is
still enumerated by its parent). Scans and recursion happen **at resolved
paths**: alias entries are pushed by their parent exactly as the legacy walk
did, but never produce alias-form children; where an alias re-scans a real
subtree, duplicate pushes may remain — the preserved claim is the **unique
legacy path-set** on finite acyclic inputs (not exactly-once). Unresolvable
entries are classified for the materializing fallback and fail closed at
copy. The walk terminates on its chain length, bounded by `maxWalkDepth`; a
deeper chain fails closed. -/
def scanTree (root : FilePath) (dir : FilePath) (chain : Array String) :
    IO (Array (FilePath × String × Bool)) := do
  let resolved ← IO.FS.realPath dir
  if chain.contains resolved.toString then
    return #[]
  if _h : chain.size < maxWalkDepth then
    let chain := chain.push resolved.toString
    let mut entries := #[]
    for d in (← resolved.readDir) do
      let isDir ← isDirSafe d.path
      entries := entries.push (d.path, (relativeOf root d.path).toString, isDir)
      if isDir then
        match ← resolveSafe d.path with
        | some target => entries := entries ++ (← scanTree root target chain)
        | none => pure ()
    return entries
  else
    throw <| IO.userError s!"slot copy walk exceeds {maxWalkDepth} directory levels: {resolved}"
termination_by maxWalkDepth - chain.size
decreasing_by simp; omega

/-- Recursively copy `source` into `target`. The guarded enumeration is the
explicit scan-boundary traversal (`scanTree`) with unchanged semantics: the
exact copy set with exclusion skipping, fail-closed unresolved containment,
and symlink classification covering directories and files alike (any entry
whose resolved location differs from its walked path — including symlinked and
empty/directories-only subtrees — forces the materializing per-file fallback,
so `cp` never copies a link). When the tree is guarded-clean, one
metadata-preserving system `cp` performs the copy (`copySubtreeSystem`);
otherwise the per-file real byte copy fallback runs with identical
exclusion/containment semantics. Returns the relative file paths copied, in
scan order. -/
def copyTree (source target : FilePath) : IO (Array String) := do
  let sourceRoot ← IO.FS.realPath source
  IO.FS.createDirAll target
  let mut copied : Array String := #[]
  let mut files : Array (FilePath × String) := #[]
  let mut guarded := true
  for (path, relative, isDirectory) in (← scanTree sourceRoot sourceRoot #[]) do
    if excluded relative then
      guarded := false
      continue
    unless (← contained sourceRoot path) do
      throw <| IO.userError s!"slot copy walk crossed owned root: {path}"
    let resolved ← resolveSafe path
    match resolved with
    | some value => if value.toString != path.toString then guarded := false
    | none => guarded := false
    if isDirectory then
      IO.FS.createDirAll (target / relative)
    else
      files := files.push (path, relative)
      copied := copied.push relative
  if guarded then
    copySubtreeSystem source target
  else
    for (path, relative) in files do
      copyFile path (target / relative)
  return copied

/-- Materialize one Git metadata tree into `target` so that `git` operating on
the copy is self-contained: pointer-file gitdirs, `commondir`,
`objects/info/alternates` and `core.worktree` are copied and rewritten to
contained locations. Any indirection that cannot be materialized inside the
slot is refused. -/
def materializeGit (slotGit : FilePath) (sourceGit : FilePath) : IO Unit := do
  let mut directory := sourceGit
  if !(← sourceGit.isDir) then
    -- Worktree pointer file: `gitdir: <path>`.
    let text ← IO.FS.readFile sourceGit
    let target := FilePath.mk ((text.replace "gitdir:" "").trimAscii.toString)
    unless (← target.pathExists) do
      throw <| IO.userError s!"slot git pointer target missing: {target}"
    directory := target
  let _ ← copyTree directory slotGit
  -- Materialize the common directory for linked worktrees. Source indirections
  -- may point outside the source tree (that is their normal shape); they must
  -- resolve to existing metadata, which is then materialized inside the slot.
  if (← (slotGit / "commondir").pathExists) then
    let raw := ((← IO.FS.readFile (slotGit / "commondir")).trimAscii.toString)
    let candidate := FilePath.mk raw
    let resolved ←
      if (← (directory / raw).pathExists) then pure (directory / raw)
      else if (← candidate.pathExists) then pure candidate
      else throw <| IO.userError s!"slot git commondir unresolvable: {raw}"
    let _ ← copyTree resolved (slotGit / "common")
    IO.FS.writeFile (slotGit / "commondir") "common\n"
  -- Materialize alternates into contained object stores.
  let alternates := slotGit / "objects/info/alternates"
  if (← alternates.pathExists) then
    let mut rewritten : Array String := #[]
    let mut index := 0
    for line in (← IO.FS.readFile alternates).splitOn "\n" do
      let entry := line.replace "\r" ""
      if entry.isEmpty then continue
      let source ←
        if (← (directory / entry).pathExists) then pure (directory / entry)
        else if (← (directory / "objects" / entry).pathExists) then
          pure (directory / "objects" / entry)
        else if (← (FilePath.mk entry).pathExists) then pure (FilePath.mk entry)
        else throw <| IO.userError s!"slot git alternate unresolvable: {entry}"
      let target := slotGit / s!"objects-alternated-{index}"
      let _ ← copyTree source target
      rewritten := rewritten.push target.toString
      index := index + 1
    IO.FS.writeFile alternates (String.intercalate "\n" rewritten.toList ++ "\n")
  -- Refuse `core.worktree` bindings in worktree or common configuration rather
  -- than let them escape the slot (`config.worktree` extension included).
  for config in #[slotGit / "config", slotGit / "config.worktree",
      slotGit / "common" / "config", slotGit / "common" / "config.worktree"] do
    if (← config.pathExists) then
      if (← IO.FS.readFile config).contains "worktree =" then
        throw <| IO.userError s!"slot git config carries core.worktree: {config}"

/-- Executed containment checks over the prepared ROOT copy: Git identity
resolution must land inside the slot, and every manifest `dir` must resolve
inside the slot or exactly to one of the captured shared dependency roots
(`shared`, canonical paths). Refusal on any other target. -/
def checkContainment (slot : ProducerSlot) (copy : FilePath)
    (shared : Array FilePath) : IO Unit := do
  unless (← contained slot.root copy) do
    throw <| IO.userError s!"slot package copy escapes slot: {copy}"
  if (← (copy / ".git").pathExists) then
    let git ← run copy "git" #["rev-parse", "--git-dir", "--git-common-dir", "--show-toplevel"]
    unless git.exitCode == 0 do
      throw <| IO.userError s!"slot git identity unavailable: {copy}\n{git.stdout}{git.stderr}"
    for line in git.stdout.splitOn "\n" do
      let entry := line.replace "\r" ""
      if entry.isEmpty then continue
      let resolved := if FilePath.isAbsolute (FilePath.mk entry) then FilePath.mk entry
        else copy / entry
      unless (← contained slot.root resolved) do
        throw <| IO.userError s!"slot git resolution escapes slot: {entry}"
  if (← (copy / "lake-manifest.json").pathExists) then
    let manifest ← readJson (copy / "lake-manifest.json")
    let packages ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
    for entry in packages do
      match entry.getObjVal? "dir" with
      | .error _ => pure ()
      | .ok dir =>
        let relative ← IO.ofExcept dir.getStr?
        let resolved := if FilePath.isAbsolute (FilePath.mk relative) then FilePath.mk relative
          else copy / relative
        let sharedRoot ← try
            pure (shared.contains (← IO.FS.realPath resolved))
          catch _ => pure false
        unless sharedRoot || (← contained slot.root resolved) do
          throw <| IO.userError s!"slot manifest dir escapes slot: {relative}"

/-- Exact comparison of one prepared file against supplied input bytes. -/
def compareBytes (target : FilePath) (expected : ByteArray) : IO Unit := do
  unless (← IO.FS.readBinFile target) == expected do
    throw <| IO.userError s!"slot copy byte mismatch: {target}"

/-- One content-level entry under a shared dependency root: root-relative path,
`lstat` kind and, for regular files, the exact byte length and the pinned native
`ByteArray.hash` of the complete contents. Symlinks are never followed; their
resolution (or its failure) is recorded instead. The digest is a 64-bit
non-cryptographic hash: it detects accidental persisting content changes, not adversarial
collisions. -/
structure SharedEntry where
  relative : String
  kind : String
  bytes : Nat
  digest : UInt64
  target : String
  deriving BEq, Inhabited

/-- Content-level identity of the shared dependency roots: one entry array per
captured root, in capture order, each sorted by relative path so the value does
not depend on directory enumeration order. Any added, removed, retyped,
resized, rewritten or re-targeted entry changes the value. -/
structure SharedIdentity where
  roots : Array (String × Array SharedEntry)
  deriving BEq, Inhabited

/-- `lstat` walk of one shared root, threading one accumulator. Directories are
recursed without following symlinks; every entry is recorded. `depth` is the
number of directory levels still allowed below `dir` (structural fuel, started at
`maxWalkDepth`); a deeper tree fails closed. -/
private def sharedWalk (root dir : FilePath) (acc : Array SharedEntry) :
    (depth : Nat) → IO (Array SharedEntry)
  | 0 => throw <| IO.userError s!"shared-root walk exceeds {maxWalkDepth} directory levels: {dir}"
  | depth + 1 => do
    let mut acc := acc
    for d in (← dir.readDir) do
      let relative := (relativeOf root d.path).toString
      match (← d.path.symlinkMetadata).type with
      | .dir =>
        acc := acc.push ⟨relative, "dir", 0, 0, ""⟩
        acc ← sharedWalk root d.path acc depth
      | .file => acc := acc.push ⟨relative, "file", 0, 0, ""⟩
      | .symlink =>
        let target ← try pure (← IO.FS.realPath d.path).toString
          catch _ => pure "<unresolvable>"
        acc := acc.push ⟨relative, "symlink", 0, 0, target⟩
      | .other => acc := acc.push ⟨relative, "other", 0, 0, ""⟩
    return acc

/-- Complete content of one regular file: exact length and native hash. -/
private def fileDigest (root : FilePath) (entry : SharedEntry) : IO SharedEntry := do
  if entry.kind != "file" then return entry
  let bytes ← IO.FS.readBinFile (root / entry.relative)
  return { entry with bytes := bytes.size, digest := bytes.hash }

/-- Capture the content-level identity of every shared dependency root. Each
root is walked once, then its entries are read in `width` contiguous chunks on
dedicated tasks; every task is joined before the first (lowest-chunk) error is
rethrown verbatim. Read-only: nothing under a shared root is written. -/
def sharedIdentity (roots : Array FilePath) (width : Nat := 8) : IO SharedIdentity := do
  let width := max width 1
  let mut result := #[]
  for root in roots do
    let walked ← sharedWalk root root #[] maxWalkDepth
    let chunk := (walked.size + width - 1) / width
    let tasks ← (Array.range width).mapM fun k =>
      IO.asTask ((walked.extract (k * chunk) ((k + 1) * chunk)).mapM (fileDigest root))
        Task.Priority.dedicated
    let mut outcomes := #[]
    for task in tasks do
      outcomes := outcomes.push (← IO.wait task)
    let mut digested := #[]
    for outcome in outcomes do
      digested := digested ++ (← IO.ofExcept outcome)
    result := result.push (root.toString, digested.qsort (·.relative < ·.relative))
  return ⟨result⟩

/-- First differing root and relative path between two identities, for the
refusal diagnostic only; equality itself is decided by `BEq`. -/
def SharedIdentity.difference (before after : SharedIdentity) : String := Id.run do
  if before.roots.size != after.roots.size then return "shared root count"
  for (b, a) in before.roots.zip after.roots do
    if b.1 != a.1 then return s!"shared root {b.1} vs {a.1}"
    if b.2.size != a.2.size then return s!"{b.1}: entry count {b.2.size} vs {a.2.size}"
    for (x, y) in b.2.zip a.2 do
      if x != y then return s!"{b.1}/{x.relative} vs {y.relative}"
  return "no difference"

/-- Prepare one complete slot: the writable ROOT package copy. The ROOT copy's
`lake-manifest.json` is truthfully relocated so that every package entry names
its captured shared dependency root (a manifest package without a captured
dependency refuses), recorded as `relocated`; captured inputs are compared
byte-exactly; Git identity is preserved through self-contained materialization
while top-level path equivalence with the original ROOT is explicitly not
claimed. Dependencies are recorded as `shared`; their no-writer requirement is
decided by the caller's `sharedIdentity` equality around the producer window. -/
def prepareSlot (originalRoot : FilePath) (slot : ProducerSlot)
    (rootSources rootConfigs : Array (FilePath × ByteArray))
    (deps : Array Regula.Checker.Snapshot.DependencyObservation) :
    IO SlotProvenance := do
  let copy := slot.root / "root"
  IO.FS.createDirAll copy
  let mut provenance : Array FileProvenance := #[]
  for (path, bytes) in rootSources ++ rootConfigs do
    let relative := (relativeOf originalRoot path).toString
    copyFile path (copy / relative)
    compareBytes (copy / relative) bytes
    provenance := provenance.push ⟨s!"root/{relative}", "source", "byte-identical"⟩
  -- Truthful relocation of the copied ROOT manifest to the captured shared
  -- dependency roots (canonical paths from the frozen Lake discovery).
  let manifestPath := copy / "lake-manifest.json"
  if (← manifestPath.pathExists) then
    let manifest ← readJson manifestPath
    let packages ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
    let relocated ← packages.mapM fun entry => do
      match entry.getObjVal? "name" with
      | .error _ => pure entry
      | .ok _ =>
        let name ← IO.ofExcept (entry.getObjValAs? String "name")
        let some dep := deps.find? (·.package == name)
          | throw <| IO.userError s!"slot manifest package without captured dependency: {name}"
        pure (entry.setObjVal! "dir" (.str dep.root.toString))
    IO.FS.writeFile manifestPath
      ((manifest.setObjVal! "packages" (toJson relocated)).compress ++ "\n")
    provenance := provenance.push ⟨"root/lake-manifest.json", "config", "relocated"⟩
  if (← (originalRoot / ".lake/build").pathExists) then
    let _ ← copyTree (originalRoot / ".lake/build") (copy / ".lake/build")
    provenance := provenance.push ⟨"root/.lake/build", "build", "copy"⟩
  if (← (originalRoot / ".git").pathExists) then
    materializeGit (copy / ".git") (originalRoot / ".git")
    provenance := provenance.push ⟨"root/.git", "git", "copy"⟩
  for dep in deps do
    provenance := provenance.push ⟨dep.package, "dependency", "shared"⟩
  for dep in deps do
    if let some expected := dep.revision then
      let git ← run dep.root "git" #["rev-parse", "HEAD"]
      unless git.exitCode == 0 && git.stdout.replace "\n" "" == expected do
        throw <| IO.userError s!"shared dependency git revision mismatch: {dep.package}"
  -- Root revision equality against the captured original (refusal on mismatch).
  let originalGit ← run originalRoot "git" #["rev-parse", "HEAD"]
  unless originalGit.exitCode == 0 do
    throw <| IO.userError "original root git revision unavailable"
  let rootGit ← run copy "git" #["rev-parse", "HEAD"]
  unless rootGit.exitCode == 0 &&
      rootGit.stdout.replace "\n" "" == originalGit.stdout.replace "\n" "" do
    throw <| IO.userError "slot root git revision mismatch"
  -- Root containment runs last: Git resolution stays inside the slot and every
  -- relocated manifest dir resolves exactly to a captured shared root.
  checkContainment slot copy (deps.map (·.root))
  let record : SlotProvenance := {
    originalRoot := (← IO.FS.realPath originalRoot).toString,
    slotRoot := (← IO.FS.realPath slot.root).toString,
    revision := rootGit.stdout.replace "\n" "",
    files := provenance }
  IO.FS.writeFile (slot.root / "slot-provenance.json")
    ((toJson (record.files.map fun file => Json.mkObj [
      ("path", .str file.relativePath), ("kind", .str file.kind),
      ("identity", .str file.identity)])).compress ++ "\n")
  return record

/-- One producer's fresh workspace over the shared slot: like `prepareProject`, but
`regula` resolves to the slot-private ROOT copy (shared by every producer,
which must not write it; checked by `sharedIdentity`, not enforced), every other
manifest `dir` is a captured shared dependency root, and no `.lake/packages` symlink is
created. -/
def prepareSlotProject (slot : ProducerSlot) (project : FilePath)
    (packageName claim rationale : String) : IO Unit := do
  IO.FS.writeBinFile (project / "lean-toolchain")
    (← IO.FS.readBinFile (slot.root / "root" / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.lean")
    s!"import Lake\nopen Lake DSL\npackage {packageName} where\n  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]\nrequire regula from {toJson (slot.root / "root").toString |>.compress}\n@[default_target] lean_lib Example\n"
  writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim), ("execution", .str "checked"),
      ("rationale", .str rationale)]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])
  let manifest ← readJson (slot.root / "root" / "lake-manifest.json")
  let packages ← IO.ofExcept (manifest.getObjValAs? (Array Json) "packages")
  -- Genuine path-class entries: `regula` at the slot-private ROOT copy, and
  -- each inherited entry at the `dir` that `prepareSlot` relocated to its captured
  -- shared dependency root. Neither is copied per producer. Pinned Lake
  -- v4.34.0 (`Lake/Load/Manifest.lean`: `PackageEntry.fromJson?`,
  -- v4.34.0 :123-153) decodes `type: "path"` (requiring
  -- name/type/inherited/dir) to an in-place filesystem source and ignores
  -- unknown keys; `Lake/Load/Materialize.lean`'s `.path` branch
  -- (v4.34.0 :180) then materializes with no remote fetch (the `.git` branch
  -- is v4.34.0 :183). `Lake/Load/Resolve.lean` materializes every entry by
  -- class (v4.34.0 :310/:322/:613; `resolveDepsCore` at :625). Pin fields
  -- (url/rev/inputRev) are retained as inert provenance in the captured
  -- manifest bytes. Path entries replace the inherited `type: "git"` entries,
  -- which would materialize (clone/copy) into each fresh workspace's own
  -- `.lake/packages`.
  let packages := packages.map (fun entry =>
    (entry.setObjVal! "inherited" (.bool true)).setObjVal! "type" (.str "path")) |>.push (Json.mkObj [
    ("name", .str "regula"), ("scope", .str ""), ("type", .str "path"),
    ("dir", .str (slot.root / "root").toString), ("configFile", .str "lakefile.lean"),
    ("manifestFile", .str "lake-manifest.json"), ("inherited", .bool false)])
  writeJson (project / "lake-manifest.json") (manifest.setObjVal! "packages" (toJson packages))
  IO.FS.createDirAll (project / ".lake")

end Regula.Qualification.Slot
