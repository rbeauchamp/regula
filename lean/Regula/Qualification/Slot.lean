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
copied: the slot manifest names the captured original dependency roots. The ROOT copy and those
dependency roots are
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
Preparation asks Git to resolve its metadata and common directory, then constructs a
self-contained copy. Alternate object stores, configuration extensions/includes and
core.worktree redirects refuse. The ROOT copy's Git stays inside the slot, and preparation
points manifest dependencies only at captured shared
roots, compares captured source/config inputs byte-exactly, records relocation
truthfully, and refuses on any containment violation. A ROOT, original or copy, whose package
overrides file records an entry refuses, since the relocation covers the manifest's entries only
(`refuseOverrides`). Filesystem, Git and
process behavior remain trusted IO, as throughout. -/
namespace Regula.Qualification.Slot
open Lean System RegulaQualification

/-- Producer-only writable environment ownership. -/
structure ProducerSlot where
  /-- The slot's directory; preparation copies the ROOT package into `root/root`. -/
  root : FilePath
  deriving Inhabited

/-- One prepared-file provenance record. `identity` is `"captured-source-equal"` when
the source bytes read before construction equal the frozen input bytes; destination byte
writing remains trusted and is not compared by this record. The label is
`"relocated"` when preparation truthfully rewrote path-bearing configuration. -/
structure FileProvenance where
  /-- The prepared path relative to the slot (`root/...`), or a shared dependency's package
  name. -/
  relativePath : String
  /-- What was prepared: `source`, `config`, `build`, `git` or `dependency`. -/
  kind : String
  /-- Source comparison or preparation: `captured-source-equal`, `relocated`, `copy` (the
  build directory or Git metadata) or `shared` (a dependency used in place). -/
  identity : String

/-- Prepared-slot provenance: truthful relocation records and containment
observations. No claim equates relocated bytes or relocated top-level paths with
the original ROOT paths. -/
structure SlotProvenance where
  /-- The canonical (`realPath`) directory of the original ROOT package. -/
  originalRoot : String
  /-- The canonical directory of the slot. -/
  slotRoot : String
  /-- The Git `HEAD` of the slot's ROOT copy, checked equal to the original's. -/
  revision : String
  /-- One provenance record per prepared entry, in preparation order. -/
  files : Array FileProvenance

/-- Lexical path suffix of `path` under `root`. -/
def relativeOf (root path : FilePath) : FilePath :=
  let stem := root.toString ++ "/"
  FilePath.mk (if path.toString.startsWith stem then
    (path.toString.drop stem.length).toString else path.toString)

/-- Excluded copy-walk roots: scratch, tmp, nested slot directories and the
shared package recursion. -/
def excluded (relative : String) : Bool :=
  (relative.splitOn "/" |>.any fun part => part == "tmp" || part == "scratch" ||
                                            part.startsWith "slot-")
    || relative == ".lake/packages" || relative.startsWith ".lake/packages/"

/-- True when `path` resolves inside `root` (executed normalization check).
A path where nothing is (`Regula.Filesystem.realPathIfPresent`) is refused (fail closed): there is
no lexical prefix fallback, so unresolved `..`/absolute joins cannot pass. A failure to read or
resolve either path is thrown. -/
def contained (root path : FilePath) : IO Bool := do
  let some resolved ← Regula.Filesystem.realPathIfPresent path | return false
  let some base ← Regula.Filesystem.realPathIfPresent root | return false
  return resolved.toString == base.toString ||
    resolved.toString.startsWith (base.toString ++ "/")

/-- Copy one source file through the shared no-follow/exclusive constructor. -/
def copyFile (source target : FilePath) : IO Unit :=
  Regula.Filesystem.copyFile source target

/-- Recursively copy a subtree through the shared constructor. No source link or special entry
is followed or retained, including Git metadata and build-state subtrees. The slot's source and
destination have no concurrent writer. Copied executable programs are granted 0755 only at the
places that execute them; all other regular files use 0644. -/
def copyTree (source target : FilePath) : IO (Array String) := do
  -- Keep the supplied spelling: canonicalizing first would hide a final source link.
  let root := source.normalize
  let base := root.components.length
  let selected := fun (path : FilePath) =>
    !excluded ("/".intercalate (path.components.drop base))
  let some parent := target.parent | throw <| IO.userError "slot copy target has no parent"
  Regula.Filesystem.Construction.ensureDirectory 4096 parent
  let items ← Regula.Filesystem.copy root target selected
  return (items.filterMap fun item => match item.payload with
    | .directory => none
    | .file .. => some ("/".intercalate item.relative)).toArray

/-- Directory-depth bound for observation-only walks. Exhaustion fails closed. -/
def maxWalkDepth : Nat := 4096

/-- Construct self-contained plain metadata using Git's own pointer and common-directory
resolution. Linked-worktree common metadata is captured beneath `common`; the one generated
commondir file selects it. Alternates, extension/include settings and core.worktree redirects
are outside the closed case and refuse before any destination is written.

Assumes: Git 2.54.0 `builtin/rev-parse.c:723-731` uses resolve_gitdir for --resolve-git-dir;
`setup.c:303-324` resolves commondir. Construction's gitPath, admitGitConfig, admitGitObjects
and gitProcessArgs document their path/config/environment assumptions. All captured source
metadata is stable and has no concurrent writer. -/
def materializeGit (slotGit : FilePath) (sourceGit : FilePath) : IO Unit := do
  let initial ← Regula.Filesystem.Construction.capture sourceGit
  let some root := sourceGit.parent | throw <| IO.userError "slot Git source has no parent"
  let directory ← Regula.Filesystem.Construction.gitPath root
    #["rev-parse", "--resolve-git-dir", sourceGit.toString]
  let localItems ← if directory == sourceGit then pure initial
    else Regula.Filesystem.Construction.capture directory
  let gitOptions := #["--git-dir", directory.toString]
  let common ← Regula.Filesystem.Construction.gitPath root
    (gitOptions ++ #["rev-parse", "--path-format=absolute", "--git-common-dir"])
  let commonItems ← if common == directory then pure []
    else Regula.Filesystem.Construction.capture common ["common"]
  Regula.Filesystem.Construction.admitGitConfig root (common / "config")
  Regula.Filesystem.Construction.admitGitObjects root gitOptions
  let localItems := localItems.filter (·.relative != ["commondir"])
  let generated := if common == directory then [] else
    [⟨["commondir"], .file "common\n".toUTF8⟩]
  Regula.Filesystem.construct slotGit
    (Regula.Filesystem.Construction.layout (localItems ++ commonItems ++ generated))

/-- Refuse the workspace whose manifest and package overrides file are `files` when that overrides
file records an entry, each file read by Lake's own reader (`Regula.Checker.Workspace.readRoot`).
Lake applies the overrides file's entries after the manifest's
(`Regula.Checker.LakeSelection.rootEntries`), and the slot relocates and checks the manifest's
entries only. A workspace without a manifest is not refused here: Lake reads its overrides file only
with a manifest. -/
def refuseOverrides (files : FilePath × FilePath) : IO Unit := do
  let some (_, overrides) ← Regula.Checker.Workspace.readRoot files | return
  unless overrides.isEmpty do
    throw <| IO.userError s!"slot workspace has package overrides: {files.2} records \
      {overrides.map (·.name)}, which Lake applies after the manifest's entries that the slot \
      relocates"

/-- Executed containment checks over the prepared ROOT copy: Git identity
resolution must land inside the slot, and every manifest entry, read by Lake's own reader
(`Regula.Checker.Workspace.readRoot`), must be a path entry whose `dir` resolves
inside the slot or exactly to one of the captured shared dependency roots
(`shared`, canonical paths). A Git entry, which Lake would clone inside the slot, and a package
overrides file that records an entry (`refuseOverrides`) refuse, and so does any other target. -/
def checkContainment (slot : ProducerSlot) (copy : FilePath)
    (shared : Array FilePath) : IO Unit := do
  unless (← contained slot.root copy) do
    throw <| IO.userError s!"slot package copy escapes slot: {copy}"
  if (← Regula.Filesystem.isPresent (copy / ".git")) then
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
  let files := Regula.Checker.Workspace.rootFiles copy
  refuseOverrides files
  if let some (manifest, _) ← Regula.Checker.Workspace.readRoot files then
    for entry in manifest.packages do
      match entry.src with
      | .git .. =>
        throw <| IO.userError s!"slot manifest entry is a Git entry, which Lake would clone \
          inside the slot: {entry.name}"
      | .path dir =>
        let resolved := if dir.isAbsolute then dir else copy / dir
        let sharedRoot := match ← Regula.Filesystem.realPathIfPresent resolved with
          | some real => shared.contains real
          | none => false
        unless sharedRoot || (← contained slot.root resolved) do
          throw <| IO.userError s!"slot manifest dir escapes slot: {dir}"

/-- Exact comparison of one prepared file against supplied input bytes. -/
def compareBytes (target : FilePath) (expected : ByteArray) : IO Unit := do
  unless (← IO.FS.readBinFile target) == expected do
    throw <| IO.userError s!"slot copy byte mismatch: {target}"

/-- One content-level entry under a shared dependency root: root-relative path,
`lstat` kind and, for regular files, the exact byte length and the pinned native
`ByteArray.hash` of the complete contents. Symlinks are never followed; the resolved path of
each is recorded, and a link that cannot be resolved fails the walk. The digest is a 64-bit
non-cryptographic hash: it detects accidental persisting content changes, not adversarial
collisions. -/
structure SharedEntry where
  /-- The entry's path relative to its shared root. -/
  relative : String
  /-- The `lstat` type: `dir`, `file`, `symlink` or `other`. -/
  kind : String
  /-- The byte length of a regular file; 0 for any other kind. -/
  bytes : Nat
  /-- `ByteArray.hash` of a regular file's contents; 0 for any other kind. -/
  digest : UInt64
  /-- A symlink's resolved path; empty for any other kind. A link that cannot be resolved fails
  the walk. -/
  target : String
  deriving BEq, Inhabited

/-- Content-level identity of the shared dependency roots: one entry array per
captured root, in capture order, each sorted by relative path so the value does
not depend on directory enumeration order. Any added, removed, retyped,
resized, rewritten or re-targeted entry changes the value. -/
structure SharedIdentity where
  /-- Each captured root, as given, with its entries sorted by relative path. -/
  roots : Array (String × Array SharedEntry)
  deriving BEq, Inhabited

/-- `lstat` walk of one shared root, threading one accumulator. Directories are
recursed without following symlinks; every entry is recorded. `depth` is the
number of directory levels still allowed below `dir` (structural fuel, started at
`maxWalkDepth`); a deeper tree fails closed. Each directory is listed through `enumerator`, which
`sharedIdentity` locates once. -/
private def sharedWalk (enumerator : Regula.Filesystem.Construction.Enumerator)
    (root dir : FilePath) (acc : Array SharedEntry) : (depth : Nat) → IO (Array SharedEntry)
  | 0 => throw <| IO.userError s!"shared-root walk exceeds {maxWalkDepth} directory levels: {dir}"
  | depth + 1 => do
    let mut acc := acc
    for name in ← enumerator.names dir do
      let path := dir / name
      let relative := (relativeOf root path).toString
      match (← path.symlinkMetadata).type with
      | .dir =>
        acc := acc.push ⟨relative, "dir", 0, 0, ""⟩
        acc ← sharedWalk enumerator root path acc depth
      | .file => acc := acc.push ⟨relative, "file", 0, 0, ""⟩
      | .symlink =>
        -- A link whose target cannot be resolved fails the walk, so no placeholder stands for
        -- two different targets in the identity.
        let target := (← IO.FS.realPath path).toString
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
  let enumerator ← Regula.Filesystem.Construction.locate
  let mut result := #[]
  for root in roots do
    let walked ← sharedWalk enumerator root root #[] maxWalkDepth
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

/-- The files that the root package of the checkout at `root` declares as build inputs, from Lake's
load of that package alone (`Workspace.withRootPackage`): the path of each of its `input_file`
targets, then each file below the path of each of its `input_dir` targets that the target's
filter admits. A library of a ROOT copy that needs such a target reads those files in each build
there, so the copy holds them beside the module sources (`RuleExamples.check`), and a campaign
records them among its sources (`RuleExamples.sourcePaths`). Each directory is walked as
`System.FilePath.walkDir` walks it (`Construction.walkDirectory`), and each entry is observed
strictly (`Regula.Filesystem.isDirectory`): a failure of that read other than a missing file
throws, where Lake's filter reads it as no directory.

Assumes:
- Lake v4.34.1 gives an `input_file` target the file `pkg.dir / path`
  (`Lake/Config/InputFile.lean:21-22`), and an `input_dir` target each file that
  `System.FilePath.walkDir` finds below `pkg.dir / path`, other than a directory, whose path, as
  that walk gives it, its filter admits (`Lake/Config/InputFile.lean:35-36`, `:43-44`,
  `Lake/Build/InputFile.lean:42-44`, `Lake/Build/Common.lean:812-823`).
- `Package.configTargets` gives each target of the package of the kind it names
  (`Lake/Config/ConfigTarget.lean:36-42`), and the root package's directory is the directory that
  its load configuration names, the real path of `root` (`loadConfig`). -/
def rootInputs (root : FilePath) : IO (Array FilePath) :=
  Regula.Checker.Workspace.withRootPackage root fun ws => do
    let mut found :=
      (ws.root.configTargets _root_.Lake.InputFile.configKind).map _root_.Lake.InputFile.path
    for dir in ws.root.configTargets _root_.Lake.InputDir.configKind do
      for path in ← Regula.Filesystem.Construction.walkDirectory (_root_.Lake.InputDir.path dir) do
        if _root_.Lake.InputDir.filter dir path && !(← Regula.Filesystem.isDirectory path) then
          found := found.push path
    return found

/-- Prepare one complete slot: the writable ROOT package copy. The ROOT copy's
`lake-manifest.json` is truthfully relocated so that every package entry names
its captured shared dependency root (a manifest package without a captured
dependency refuses), recorded as `relocated`; an original ROOT whose package overrides file
records an entry refuses (`refuseOverrides`), since Lake would apply it after the relocated entries; source captures are compared
byte-exactly with frozen inputs, without comparing destination bytes; Git identity is preserved through self-contained materialization
while top-level path equivalence with the original ROOT is explicitly not
claimed. Dependencies are recorded as `shared`; their no-writer requirement is
decided by the caller's `sharedIdentity` equality around the producer window. -/
def prepareSlot (originalRoot : FilePath) (slot : ProducerSlot)
    (rootSources rootConfigs : Array (FilePath × ByteArray))
    (deps : Array Regula.Checker.Snapshot.DependencyObservation) :
    IO SlotProvenance := do
  let copy := slot.root / "root"
  let mut provenance : Array FileProvenance := #[]
  let mut instructions := []
  let mut inputs : Array (FilePath × ByteArray) := #[]
  for (path, bytes) in rootSources ++ rootConfigs do
    if let some (_, previous) := inputs.find? (fun input => input.1.normalize == path.normalize) then
      unless previous == bytes do
        throw <| IO.userError s!"slot duplicate input has conflicting captured bytes: {path}"
      continue
    inputs := inputs.push (path, bytes)
    let relative := (relativeOf originalRoot path).components
    let captured ← Regula.Filesystem.Construction.capture path relative
    let [⟨_, .file actual _⟩] := captured
      | throw <| IO.userError s!"slot input is not a regular file: {path}"
    unless actual == bytes do throw <| IO.userError s!"slot input changed before construction: {path}"
    instructions := instructions ++ captured
    let relative := "/".intercalate relative
    provenance := provenance.push ⟨s!"root/{relative}", "source", "captured-source-equal"⟩
  Regula.Filesystem.construct copy (Regula.Filesystem.Construction.layout instructions)
  -- Relocate every captured dependency as a typed path entry, so ordinary loads of the slot
  -- never materialize a Git clone at a packages directory inside the slot.
  let relocatedManifest ← Regula.Checker.Workspace.withRootWorkspace originalRoot fun ws => do
    -- The relocation rewrites the manifest's entries only, so an original root whose package
    -- overrides file records an entry, which Lake applies after them, is refused.
    refuseOverrides (ws.manifestFile, ws.packageOverridesFile)
    let relative := ws.manifestFile.normalize.components.drop originalRoot.normalize.components.length
    let manifestPath := Regula.Filesystem.Construction.location copy relative
    let manifest ← _root_.Lake.Manifest.load manifestPath
    let relocated ← manifest.packages.mapM fun entry => do
      let some dep := deps.find? (·.package == entry.name.toString)
        | throw <| IO.userError s!"slot manifest package without captured dependency: {entry.name}"
      pure {entry with src := .path dep.root}
    -- This is an explicit relocation of a file the constructor placed, in a private plain tree.
    _root_.Lake.Manifest.save {manifest with packages := relocated} manifestPath
    return "/".intercalate relative
  provenance := provenance.push ⟨s!"root/{relocatedManifest}", "config", "relocated"⟩
  if (← Regula.Filesystem.isPresent (originalRoot / ".lake/build")) then
    let _ ← copyTree (originalRoot / ".lake/build") (copy / ".lake/build")
    -- Slot producers run the copied axiomGate/ruleExamples dispatchers by path, and Lake can
    -- invoke any declared executable. Grant 0755 precisely to the root's Lake-declared binaries.
    Regula.Checker.Workspace.withRootWorkspace originalRoot fun ws => do
      for executable in ws.root.leanExes do
        -- Lake v4.34.1 Config/LeanExe.lean:68-73 supplies the executable's exact output path.
        let relative := executable.file.normalize.components.drop originalRoot.normalize.components.length
        let path := Regula.Filesystem.Construction.location copy relative
        match ← Regula.Filesystem.Construction.kindWith Regula.Filesystem.Construction.observer path with
        | some .file => Regula.Filesystem.makeExecutable path
        | none => pure ()
        | _ => throw <| IO.userError s!"slot executable is not regular: {path}"
    provenance := provenance.push ⟨"root/.lake/build", "build", "copy"⟩
  if (← Regula.Filesystem.isPresent (originalRoot / ".git")) then
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
  let toolchain ← Regula.Filesystem.Construction.capture
    (slot.root / "root" / "lean-toolchain") ["lean-toolchain"]
  Regula.Filesystem.construct project (Regula.Filesystem.Construction.layout toolchain)
  Regula.Filesystem.writeFile (project / "lakefile.lean")
    s!"import Lake\nopen Lake DSL\npackage {packageName} where\n  leanOptions := #[⟨`autoImplicit, \
      false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, true⟩]\n  \
      plugins := #[`@regula/RegulaObserver:shared]\nrequire regula from \
      {toJson (slot.root / "root").toString |>.compress}\n\
      @[default_target] {Regula.Checker.observedTargetLean .library "Example"}"
  Regula.Filesystem.writeJson (project / "foundation_manifest.json") (Json.mkObj [
    ("schema-version", toJson (2 : Nat)), ("surfaces", toJson #[Json.mkObj [
      ("library", .str "Example"), ("claim", .str claim), ("execution", .str "checked"),
      ("rationale", .str rationale)]]),
    ("excluded-libraries", toJson (#[] : Array Json)),
    ("excluded-executables", toJson (#[] : Array Json))])
  -- These producer templates require Regula at its prepared ROOT slot. Its default manifest
  -- was relocated before the frozen producer window. Decode those captured bytes with Lake;
  -- loading the shared ROOT here would create config/0 during that no-writer window.
  let manifest ← IO.ofExcept <| _root_.Lake.Manifest.parse
    (← Regula.Filesystem.readFile (slot.root / "root/lake-manifest.json"))
  let packages ← manifest.packages.mapM fun entry => do
    unless entry.src matches .path _ do
      throw <| IO.userError s!"slot dependency was not prepared as a path: {entry.name}"
    pure {entry with inherited := true}
  let rootEntry : _root_.Lake.PackageEntry :=
    {name := `regula, inherited := false, src := .path (slot.root / "root")}
  Regula.Filesystem.writeFile (project / "lake-manifest.json")
    ((toJson {manifest with name := packageName.toName, packages := packages.push rootEntry}).pretty ++ "\n")

end Regula.Qualification.Slot
