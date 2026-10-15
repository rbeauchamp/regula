import Regula.Checker.AcceptanceLink
import Regula.Checker.Inspection
import Regula.Checker.SourceBinding
import Regula.Checker.Workspace
import Regula.Cli.Setup
import Regula.Qualification.RuleExamples
import Regula.Qualification.Slot
import RegulaProvision
import Lean.Elab.Command

/-! # Controls of the reads of whether a path is present

A path that cannot be read, `locked/child` where `locked` is a directory without search
permission, which Lean's `System.FilePath.pathExists` and `System.FilePath.isDir` read as absent
(https://github.com/rbeauchamp/regula/issues/430). The first acceptance step builds this module, and
its build fails when a control does not give the expected result, naming each such control. The
controls load Lake workspaces, which Regula refuses in a process whose Git environment is not
isolated, so a build without that isolation elaborates the module again under it
(`checkIsolated`). These
controls are about the file system, a trusted boundary: they observe the reads on the toolchain's
file system calls, and they prove nothing.

- The setup: Lean's `System.FilePath.metadata` of the path fails with `permissionDenied`, not
  `noFileOrDirectory`. The committed fixture
  `examples/fixtures/absence-reads/AbsenceReads/Refused.lean`, which `lean --run` runs on the path,
  prints that `pathExists` and `isDir` give `false` for it. So the path is one that the defect takes
  for an absent one. The fixture is outside every library of the package, so no module that the
  self-audit inspects names the two readers. A run that cannot make such a path, such as one with
  the permissions of the superuser, fails here rather than passing without observing it.
- The observers (`observers`): `Regula.Filesystem.isPresent`, `isDirectory`, `metadataIfPresent`,
  `readFileIfPresent`, `entryIfPresent`, `realPathIfPresent` and `atOwnPlace` each fail with the
  read's `permissionDenied`. The theorems of `Regula.Filesystem` (`isPresent_error` and the others)
  state, for every error that is not `noFileOrDirectory`, that the observer fails with that error;
  for `atOwnPlace` they are `atOwnPlace_entry_error` (its entry read fails) and
  `atOwnPlace_real_error` (its resolution fails). This control observes that the toolchain's read
  gives such an error here.
- A caller of each observer (`callers`), which fails with the read's `permissionDenied` too. For
  `isPresent`, one for each outcome that `false` used to give: a refusal with another reason
  (`AcceptanceLink.require`), an absent record (`Inspection.freezeArtifact`) and a walk past the
  path to its parent (`Setup.guidanceDirs`). Then `Construction.markdownPaths` (`isDirectory`),
  `RuleExamples.configuration` (`metadataIfPresent`), `SourceBinding.configuration`
  (`readFileIfPresent`), `Regula.Filesystem.ownPath` (the entry read of `entryIfPresent`), and
  `Slot.contained` and `Checker.findRepoRoot?` (`realPathIfPresent`). `atOwnPlace` has three
  callers. `Removal.ownParent` gives its result, so it is controlled on `path / "new"`. `ownPath`
  reads the entry (`entryType`) before it, so its control fails at that read whatever `atOwnPlace`
  does. `Removal.observe` reads the same entry after it, so on this path its control would fail at
  that read too; it is controlled apart, at operations whose entry reads succeed (below). The two
  loaders of `Checker.Workspace` observe the root package's configuration candidates
  (`requireConfigCandidates`) in `configured`, whose `lakefile.lean` is a link to a file below the
  path and whose `lakefile.toml` can be read: Lake would pass over the first for the second.
  `withRootWorkspace` also loads `withdep`, whose root can be read and whose dependency `dep` has
  the shape of `configured`. Lake loads `dep` from its `lakefile.toml` and records that choice
  in the manifest, and the strict observation of each loaded package's candidates
  (`requireConfigChoice`) must fail at the link. Each other changed site binds an observer's
  result in `IO` in the same way, so the error propagates there too, unless a caller catches it;
  this control does not run them.
- The loaders once the path can be read again (`loaderControls`): `withRootWorkspace` must load
  `withdep` with `dep` from the `lakefile.toml` that its manifest records, as Lake reads a name
  with an extension alone, though the link `lakefile.lean` beside it now resolves. With the links
  removed, both loaders must load `configured`, and `withRootWorkspace` must load `withdep` with
  its dependency. With a `lakefile.lean` written after a load beside the `lakefile.toml` that Lake
  loaded, the check of the loaded workspace (`requireConfigChoices`) must refuse each package
  whose configuration name has no extension, the root's and a dependency's that a package
  overrides entry names `lakefile`, and accept a dependency whose recorded name is
  `lakefile.toml`.
- `Removal.observe` at operations (`resolving`) whose entry reads each give a directory and whose
  resolution of the path alone fails (`resolutionFailure`), which no control on the unreadable path
  can make: it must fail with that same error, not observe a directory at another place. At the same
  operations with no failure it must observe a directory at its own place in a parent at its own
  place.
- `Slot.sharedIdentity` of a directory that holds a symbolic link to the path (`shared`): Lean's
  `IO.FS.realPath` reports every failure as `noFileOrDirectory`, so the walk must fail with that
  error rather than record the link, and once the permissions are given back it records the link
  with its resolved path.
- Provisioning's removal of a shared store that no registered copy links
  (`RegulaProvision.prune`), the case that destroys data (`provisioning`): a store whose Mathlib
  cannot be read, and a store whose registered copy's link cannot be resolved
  (`RegulaProvision.links`). In each, the store and its registry are kept and the failure is
  reported.
- The work tree that `Checker.gitWorkTree` reads (`workTrees`,
  https://github.com/rbeauchamp/regula/issues/444): the top level of a repository whose name ends
  in a space, with the space kept; below a `.git` file that names a repository, its work tree while
  the file can be read and a failure while it cannot; and `none` for a directory that no
  repository holds. With a query that fails in place of Git's, the read gives `none` without
  running it where no repository can be, and fails in a repository.

The permissions of each directory that a control takes away are given back before the temporary
directory is removed. -/

namespace Regula.AbsenceControls

open Lean System

/-- The source of the committed fixture that runs Lean's two readers on the path that is its one
argument and prints what they give. -/
def refusedSource : String :=
  include_str "../../examples/fixtures/absence-reads/AbsenceReads/Refused.lean"

/-- Whether `result` is the failure of a read that the permissions of a directory denied. -/
def denied {α : Type} : Except IO.Error α → Bool
  | .error (.permissionDenied ..) => true
  | _ => false

/-- The two reads of `atOwnPlace`, by Lean's `symlinkMetadata` and `realPath` as the observer of
`Regula.Filesystem` makes them. The control removes and moves nothing, so the other operations
refuse. -/
def reads : Regula.Filesystem.Ops IO where
  symlinkMetadata path := path.symlinkMetadata
  realPath := IO.FS.realPath
  removeDirAll path := throw <| IO.userError s!"the control removes nothing: {path}"
  removeFile path := throw <| IO.userError s!"the control removes nothing: {path}"
  rename source _ := throw <| IO.userError s!"the control moves nothing: {source}"

/-- Each shared read of whether a path is present, run on the path that cannot be read `path`. -/
def observers (path : FilePath) : List (String × IO Unit) := [
  ("Regula.Filesystem.isPresent", discard <| Regula.Filesystem.isPresent path),
  ("Regula.Filesystem.isDirectory", discard <| Regula.Filesystem.isDirectory path),
  ("Regula.Filesystem.metadataIfPresent", discard <| Regula.Filesystem.metadataIfPresent path),
  ("Regula.Filesystem.readFileIfPresent", discard <| Regula.Filesystem.readFileIfPresent path),
  ("Regula.Filesystem.entryIfPresent", discard <| Regula.Filesystem.entryIfPresent path),
  ("Regula.Filesystem.realPathIfPresent", discard <| Regula.Filesystem.realPathIfPresent path),
  ("Regula.Filesystem.atOwnPlace", discard <| Regula.Filesystem.atOwnPlace reads path)]

/-- A caller of each shared read, run on the path that cannot be read `path` and, where it takes
a second, the readable directory `base`. -/
def callers (base path : FilePath) : List (String × IO Unit) := [
  ("Regula.Checker.AcceptanceLink.require", Regula.Checker.AcceptanceLink.require path "control"),
  ("Regula.Checker.Inspection.freezeArtifact",
    discard <| Regula.Checker.Inspection.freezeArtifact `Control (path / "Control.olean")),
  ("Regula.Cli.Setup.guidanceDirs", discard <| Regula.Cli.Setup.guidanceDirs path),
  ("Regula.Filesystem.Construction.markdownPaths",
    discard <| Regula.Filesystem.Construction.markdownPaths path),
  ("Regula.Qualification.RuleExamples.configuration",
    discard <| Regula.Qualification.RuleExamples.configuration #[path / "lakefile.lean"]),
  ("Regula.Checker.SourceBinding.configuration",
    discard <| Regula.Checker.SourceBinding.configuration path (path / "lake-manifest.json")),
  ("Regula.Filesystem.ownPath", discard <| Regula.Filesystem.ownPath (path / "new")),
  ("Regula.Removal.ownParent", discard <| Regula.Removal.ownParent reads (path / "new")),
  ("Regula.Checker.Workspace.withRootWorkspace",
    Regula.Checker.Workspace.withRootWorkspace (base / "configured") fun _ => pure ()),
  ("Regula.Checker.Workspace.withRootPackage",
    Regula.Checker.Workspace.withRootPackage (base / "configured") fun _ => pure ()),
  ("Regula.Checker.Workspace.withRootWorkspace with a dependency's candidate",
    Regula.Checker.Workspace.withRootWorkspace (base / "withdep") fun _ => pure ()),
  ("Regula.Qualification.Slot.contained", discard <| Regula.Qualification.Slot.contained base path),
  ("Regula.Checker.findRepoRoot?", discard <| Regula.Checker.findRepoRoot? path)]

/-- The failure of the resolution at `resolving`. -/
def resolutionFailure : IO.Error := .otherError 4242 "the control's resolution failed"

/-- Operations at which the entry read of each path gives a directory, and the resolution of each
path gives that path, except that the resolution of `path` fails with `failure` when one is given.
The control removes and moves nothing, so the other operations refuse. -/
def resolving (path : FilePath) (failure : Option IO.Error) : Regula.Filesystem.Ops IO where
  symlinkMetadata _ := pure {
    accessed := ⟨0, 0⟩, modified := ⟨0, 0⟩, byteSize := 0, type := .dir, numLinks := 1 }
  realPath target := match failure with
    | some error => if target == path then throw error else pure target
    | none => pure target
  removeDirAll target := throw <| IO.userError s!"the control removes nothing: {target}"
  removeFile target := throw <| IO.userError s!"the control removes nothing: {target}"
  rename source _ := throw <| IO.userError s!"the control moves nothing: {source}"

/-- `Removal.observe` at `resolving`, on an absolute path with a parent: whether it fails with
`resolutionFailure` when the resolution of the path alone fails, and observes a directory at its
own place in a parent at its own place when no resolution fails. -/
def observeResolution : IO (List (String × Bool)) := do
  let path : FilePath := "/control/observed"
  let failing := resolving path (some resolutionFailure)
  let failed := match ← (Regula.Removal.observe failing path).toBaseIO with
    | .error (.otherError 4242 details) => details == "the control's resolution failed"
    | _ => false
  let observed ← Regula.Removal.observe (resolving path none) path
  return [("Regula.Removal.observe with a resolution of the path alone that fails", failed),
    ("Regula.Removal.observe with no failure", observed ==
      { place := .present .directory, sameLocation := true, parentOwn := true })]

/-- Make a symbolic link at `place` to `target`, or fail. -/
def makeLink (target place : FilePath) : IO Unit := do
  let made ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, place.toString] }
  unless made.exitCode == 0 do
    throw <| IO.userError s!"the control could not make the link {place}: {made.stderr}"

/-- The loaders of `Checker.Workspace` once the path can be read again, each with whether it gave
the expected result. The refused load of `withdep` wrote its manifest with the configuration file
that Lake chose for `dep` while the link `dep/lakefile.lean` could not be resolved,
`lakefile.toml`. Lake reads that recorded name alone, so the next load must load `dep` from it,
though the link now resolves: Regula observes the choice that Lake's build makes. With the two
links removed, both loaders must load `configured`, and `withRootWorkspace` must load `withdep`
with its dependency. A `lakefile.lean` that Lake loads cannot stay for these loads: Lake
elaborates it, which needs the native initialization of Lake that the elaboration of this module
does not have.

Then the comparison of a choice that a load made, which no failed read here can make, since the
read that fails is Lake's own: each load below writes a readable `lakefile.lean` after Lake loaded
`lakefile.toml` beside it, and runs the check of the loaded workspace (`requireConfigChoices`)
with the entries that the load materialized from. It must refuse the root `configured`, whose name
is `lakefile`, naming the package; accept `withdep`, whose manifest names `dep`'s
`lakefile.toml`; and refuse `withdep` with a package overrides file whose entry for `dep` names
`lakefile`, naming `dep`. -/
def loaderControls (base : FilePath) : IO (List (String × Bool)) := do
  let configured := base / "configured"
  let withdep := base / "withdep"
  let loads (load : IO Nat) (count : Nat) : IO Bool := do
    return match ← load.toBaseIO with
      | .ok loaded => loaded == count
      | .error _ => false
  let size (ws : _root_.Lake.Workspace) : IO Nat := pure ws.packages.size
  -- The number of packages, or none when no dependency was loaded from `lakefile.toml`.
  let fromRecorded (ws : _root_.Lake.Workspace) : IO Nat := pure <|
    if ws.packages.any fun package =>
        !package.isRoot && package.relConfigFile == ("lakefile.toml" : FilePath)
    then ws.packages.size else 0
  let recorded ← loads (Regula.Checker.Workspace.withRootWorkspace withdep fromRecorded) 2
  Regula.Filesystem.removePath .link (withdep / "dep" / "lakefile.lean")
  Regula.Filesystem.removePath .link (configured / "lakefile.lean")
  let loaded := [
    ("Regula.Checker.Workspace.withRootWorkspace with a recorded choice of lakefile.toml",
      recorded),
    ("Regula.Checker.Workspace.withRootWorkspace with one configuration",
      ← loads (Regula.Checker.Workspace.withRootWorkspace configured size) 1),
    ("Regula.Checker.Workspace.withRootPackage with one configuration",
      ← loads (Regula.Checker.Workspace.withRootPackage configured size) 1),
    ("Regula.Checker.Workspace.withRootWorkspace with a dependency",
      ← loads (Regula.Checker.Workspace.withRootWorkspace withdep size) 2)]
  -- The check of a loaded workspace (`requireConfigChoices`), run on the load of `dir` after
  -- `written`, a `lakefile.lean`, is written beside the `lakefile.toml` that Lake loaded, with the
  -- entries that the load materialized from (`configRequests`).
  let afterLoad (dir written : FilePath) : IO (Except String Unit) := do
    let checked ← (Regula.Checker.Workspace.withRootWorkspace dir fun ws => do
      IO.FS.writeFile written "-- written after the load\n"
      try
        let files := Regula.Checker.Workspace.rootFiles ws.root.dir
        let entries ← Regula.Checker.Workspace.configRequests files
        (Regula.Checker.Workspace.requireConfigChoices entries ws).toBaseIO
      finally
        Regula.Filesystem.removePath .file written).toBaseIO
    return match checked with
      | .ok (.ok ()) => .ok ()
      | .ok (.error error) | .error error => .error (toString error)
  let refusedFor (name : String) : Except String Unit → Bool
    | .error text =>
        (text.splitOn s!"Lake loaded package '{name}' from lakefile.toml").length > 1 &&
          (text.splitOn "its candidates give lakefile.lean").length > 1
    | .ok () => false
  -- The root's name is `lakefile`, so Lake chose its file in the load.
  let root ← afterLoad configured (configured / "lakefile.lean")
  -- `dep`'s entry in the manifest names `lakefile.toml`, so Lake chose nothing for it.
  let named ← afterLoad withdep (withdep / "dep" / "lakefile.lean")
  -- With `dep`'s entry in the package overrides file naming `lakefile`, Lake chose its file.
  let overrides := withdep / ".lake" / "package-overrides.json"
  IO.FS.createDirAll (withdep / ".lake")
  IO.FS.writeFile overrides <| Json.pretty <| Json.mkObj [("version", "1.2.0"), ("packages",
    Json.arr #[Json.mkObj [("type", "path"), ("scope", ""), ("name", "dep"),
      ("manifestFile", "lake-manifest.json"), ("inherited", false), ("dir", "dep"),
      ("configFile", "lakefile")]])]
  let unnamed ← tryFinally (afterLoad withdep (withdep / "dep" / "lakefile.lean"))
    (Regula.Filesystem.removePath .file overrides)
  return loaded ++ [
    ("Regula.Checker.Workspace.requireConfigChoices with the root's lakefile.lean written after \
      the load", refusedFor "control" root),
    ("Regula.Checker.Workspace.requireConfigChoices with lakefile.lean written beside a \
      dependency's recorded lakefile.toml", named matches .ok ()),
    ("Regula.Checker.Workspace.requireConfigChoices with lakefile.lean written beside the \
      lakefile.toml of a dependency whose entry names lakefile", refusedFor "dep" unnamed)]

/-- `Slot.sharedIdentity` of `root`, which holds a symbolic link to the path `path`, run while
`path` cannot be read: whether it failed with the error of the resolution. -/
def sharedUnresolved (root : FilePath) : IO Bool := do
  return match ← (Regula.Qualification.Slot.sharedIdentity #[root]).toBaseIO with
    | .error (.noFileOrDirectory ..) => true
    | _ => false

/-- `Slot.sharedIdentity` of `root`, run once `path` can be read again: whether it recorded the
link to `path` with the real path of `path`. -/
def sharedResolved (root path : FilePath) : IO Bool := do
  let real := (← IO.FS.realPath path).toString
  let identity ← Regula.Qualification.Slot.sharedIdentity #[root]
  return identity.roots.any fun (_, entries) =>
    entries.any fun entry => entry.kind == "symlink" && entry.target == real

/-- A shared store in `parent` as `RegulaProvision.prune` identifies one: a directory named by
its receipt's key, holding that receipt and a Mathlib directory, with a registry beside it that
records `copy`. Gives the store and its registry. -/
def sharedStore (parent copy : FilePath) : IO (FilePath × FilePath) := do
  let receipt : RegulaProvision.Receipt := {
    schemaVersion := RegulaProvision.receiptSchema, mathlibRev := "control",
    leanGithash := "control", leanVersion := "control", packages := #[] }
  let store := parent / receipt.key
  IO.FS.createDirAll (RegulaProvision.sharedPackages store / "mathlib")
  IO.FS.writeFile (store / RegulaProvision.receiptName) (toJson receipt).compress
  let registry := parent / s!"{receipt.key}.copies.json"
  IO.FS.writeFile registry (toJson #[copy.toString]).compress
  return (store, registry)

/-- Run `RegulaProvision.prune` on `parent`, where no store is the current one, with the
directory `locked` without search permission, and give whether the store and its registry are
still there and the failure was reported. The permissions of `locked`, where it is still there,
and of the `.lake` of each directory in `parent`, where a moved store keeps its own, are given
back first. -/
def pruneKeeps (parent locked store registry : FilePath) : IO Bool := do
  IO.Prim.setAccessRights locked 0
  let (output, ()) ← try IO.FS.withIsolatedStreams (RegulaProvision.prune parent "current" "" "")
    finally
      if (← Regula.Filesystem.entryIfPresent locked).isSome then
        IO.Prim.setAccessRights locked 448
      for entry in ← Regula.Filesystem.Construction.listDirectory parent do
        if (← Regula.Filesystem.entryIfPresent entry.path) == some .dir then
          if (← Regula.Filesystem.entryIfPresent (entry.path / ".lake")) == some .dir then
            IO.Prim.setAccessRights (entry.path / ".lake") 448
  return (← Regula.Filesystem.isDirectory store) && (← Regula.Filesystem.isPresent registry) &&
    (output.splitOn "could not prune").length > 1

/-- Provisioning's removal of a store that no registered copy links, the case that destroys
data, each with whether it kept the store and its registry: a store whose Mathlib cannot be
read, and a store whose registered copy's link cannot be resolved (`RegulaProvision.links`). -/
def provisioning (base : FilePath) : IO (List (String × Bool)) := do
  let unreadable := base / "unreadable-mathlib"
  let (store, registry) ← sharedStore unreadable (base / "unregistered")
  let mathlibKept ← pruneKeeps unreadable (store / ".lake") store registry
  let unresolved := base / "unresolved-link"
  let locked := unresolved / "locked"
  IO.FS.createDirAll (locked / "mathlib")
  let copy := unresolved / "copy"
  let made ← IO.Process.output
    { cmd := "ln", args := #["-s", (locked / "mathlib").toString, copy.toString] }
  unless made.exitCode == 0 do
    throw <| IO.userError s!"the control could not make the link {copy}: {made.stderr}"
  let (store, registry) ← sharedStore (unresolved / "shared") copy
  let linkKept ← pruneKeeps (unresolved / "shared") locked store registry
  return [("RegulaProvision.prune of a store whose Mathlib cannot be read", mathlibKept),
    ("RegulaProvision.links of a registered copy whose link cannot be resolved", linkKept)]

/-- The work tree that `Checker.gitWorkTree` reads for a directory in three places below `base`,
each with whether it gave the expected result (https://github.com/rbeauchamp/regula/issues/444):

- `tree ` (its name ends in a space), the top level of a new repository, beside a directory
  `tree`: its own real path, with the space. Git prints that path and a newline, and the earlier
  read removed the space and gave `tree`.
- `linked/sub`, below the `.git` file of `linked` that names the repository `store`, as
  `git init --separate-git-dir` makes it and as a linked work tree has one: the real path of
  `linked` before the permissions of that file are taken away and after they are given back, and
  a failure while it cannot be read, where the earlier read gave `none`.
- `plain`, which no repository holds: `none`.

Each place is first observed with Git itself, and the control fails, naming its setup, when Git
does not do what the place needs: find `linked` from `linked/sub` while its `.git` file can be
read, fail there while it cannot, and fail in `plain`.

Then a query that fails as a process that `SIGTERM` ends does (exit 143) takes the place of Git's
(`Checker.gitWorkTreeBy`). The read of `plain` must give `none` without running that query, so no
failure of the query is read as no work tree, and the read of `tree ` must fail. -/
def workTrees (base : FilePath) : IO (List (String × Bool)) := do
  let fail {α : Type} (message : String) : IO α := throw <| IO.userError message
  let spaced := base / "tree "
  IO.FS.createDirAll spaced
  IO.FS.createDirAll (base / "tree")
  let initialized ← Regula.Checker.runProcess spaced "git" #["init", "-q"]
  unless initialized.succeeded do
    fail s!"the control could not make the repository {spaced}: {initialized.output}"
  let expected ← IO.FS.realPath spaced
  let spacedRead ← (Regula.Checker.gitWorkTree spaced).toBaseIO
  let linked := base / "linked"
  let below := linked / "sub"
  let pointer := linked / ".git"
  let made ← Regula.Checker.runProcess base "git"
    #["init", "-q", "--separate-git-dir", (base / "store").toString, linked.toString]
  unless made.succeeded do
    fail s!"the control could not make the work tree {linked}: {made.output}"
  IO.FS.createDirAll below
  let linkedTop ← IO.FS.realPath linked
  let readable (stage : String) : IO (Except IO.Error (Option FilePath)) := do
    let git ← Regula.Checker.showTopLevel below
    unless git.succeeded do
      fail s!"the control's setup: Git did not find the work tree {linked} from {below} {stage}: \
        {git.output}"
    (Regula.Checker.gitWorkTree below).toBaseIO
  let before ← readable "before the permissions of its .git file are taken away"
  IO.Prim.setAccessRights pointer 0
  let (deniedGit, deniedRead) ← try
      pure (← (Regula.Checker.showTopLevel below).toBaseIO,
        ← (Regula.Checker.gitWorkTree below).toBaseIO)
    finally
      IO.Prim.setAccessRights pointer 420
  unless (match deniedGit with | .ok result => !result.succeeded | .error _ => false) do
    fail s!"the control's setup: Git did not fail below the .git file that cannot be read"
  let after ← readable "after the permissions of its .git file are given back"
  let plain := base / "plain"
  IO.FS.createDirAll plain
  let plainGit ← Regula.Checker.showTopLevel plain
  if plainGit.succeeded then
    fail s!"the control's setup: the temporary directory {base} is in the Git work tree \
      {plainGit.stdout}"
  let plainRead ← (Regula.Checker.gitWorkTree plain).toBaseIO
  let launches ← IO.mkRef (0 : Nat)
  let terminated (_ : FilePath) : IO Regula.Checker.ProcessResult := do
    launches.modify (· + 1)
    return { exitCode := 143, stdout := "", stderr := "the control's query, ended by SIGTERM" }
  let plainTerminated ← (Regula.Checker.gitWorkTreeBy terminated plain).toBaseIO
  let plainLaunches ← launches.get
  let spacedTerminated ← (Regula.Checker.gitWorkTreeBy terminated spaced).toBaseIO
  let isLinked (read : Except IO.Error (Option FilePath)) : Bool :=
    match read with | .ok (some top) => top == linkedTop | _ => false
  return [
    ("Regula.Checker.gitWorkTree of a top level whose name ends in a space",
      match spacedRead with | .ok (some top) => top == expected | _ => false),
    ("Regula.Checker.gitWorkTree below a .git file before its permissions are taken away and \
      after they are given back", isLinked before && isLinked after),
    ("Regula.Checker.gitWorkTree below a .git file that cannot be read",
      deniedRead matches .error _),
    ("Regula.Checker.gitWorkTree of a directory that no repository holds",
      plainRead matches .ok none),
    ("Regula.Checker.gitWorkTreeBy with a query that fails, where no repository can be",
      (plainTerminated matches .ok none) && plainLaunches == 0),
    ("Regula.Checker.gitWorkTreeBy with a query that fails, in a repository",
      spacedTerminated matches .error _)]

/-- Run the controls in a new temporary directory, and fail, naming each control that does not
give the expected result. -/
def check : IO Unit :=
  Regula.Filesystem.withOwnTempDir fun base => do
    let fail {α : Type} (message : String) : IO α := throw <| IO.userError message
    let locked := base / "locked"
    let path := locked / "child"
    IO.FS.createDirAll path
    IO.FS.writeFile (path / "AGENTS.md") "control"
    let shared := base / "shared"
    IO.FS.createDirAll shared
    makeLink path (shared / "link")
    -- A project whose `lakefile.lean` is a link to a file below the path, beside a
    -- `lakefile.toml` that can be read, and a project with a dependency of that shape. Lake
    -- never reads the linked file's text: each load either fails at the link or takes the
    -- recorded `lakefile.toml`, and the link is removed before the other loads.
    IO.FS.writeFile (path / "lakefile.lean") "-- the control's configuration\n"
    let configured := base / "configured"
    IO.FS.createDirAll configured
    IO.FS.writeFile (configured / "lakefile.toml") "name = \"control\"\n"
    makeLink (path / "lakefile.lean") (configured / "lakefile.lean")
    let withdep := base / "withdep"
    IO.FS.createDirAll (withdep / "dep")
    IO.FS.writeFile (withdep / "lakefile.toml")
      "name = \"withdep\"\n\n[[require]]\nname = \"dep\"\npath = \"dep\"\n"
    IO.FS.writeFile (withdep / "dep" / "lakefile.toml") "name = \"dep\"\n"
    makeLink (path / "lakefile.lean") (withdep / "dep" / "lakefile.lean")
    let source := base / "Refused.lean"
    IO.FS.writeFile source refusedSource
    let mut failed : Array String := #[]
    IO.Prim.setAccessRights locked 0
    try
      -- The setup: the read fails with `permissionDenied`, which Lean's two readers take for
      -- absence.
      unless denied (← path.metadata.toBaseIO) do
        fail s!"the control could not make an unreadable path: reading {path} did not fail \
          with permissionDenied"
      let run ← IO.Process.output {
        cmd := ((← Lean.getBuildDir) / "bin/lean").toString
        args := #["--run", source.toString, path.toString]
        env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none)] }
      unless run.exitCode == 0 && run.stdout == "false false\n" do
        fail s!"Lean's pathExists and isDir did not both read the unreadable path {path} as \
          absent: exit {run.exitCode}, {run.stdout}{run.stderr}"
      for (name, read) in observers path ++ callers base path do
        unless denied (← read.toBaseIO) do
          failed := failed.push s!"{name} did not fail with the read's permissionDenied"
      unless ← sharedUnresolved shared do
        failed := failed.push "Regula.Qualification.Slot.sharedIdentity did not fail with the \
          resolution's noFileOrDirectory"
    finally
      IO.Prim.setAccessRights locked 448
    unless ← sharedResolved shared path do
      failed := failed.push "Regula.Qualification.Slot.sharedIdentity did not record the link once \
        its target could be read"
    unless (← (Regula.Checker.Workspace.requireConfigCandidates configured "lakefile").toBaseIO)
        matches .ok () do
      failed := failed.push "Regula.Checker.Workspace.requireConfigCandidates did not accept the \
        candidates once they could be read"
    for (name, held) in (← observeResolution) ++ (← loaderControls base) do
      unless held do failed := failed.push s!"{name} did not give the expected result"
    for (name, kept) in ← provisioning base do
      unless kept do
        failed := failed.push s!"{name} did not keep the store and its registry"
    for (name, held) in ← workTrees base do
      unless held do failed := failed.push s!"{name} did not give the expected result"
    unless failed.isEmpty do
      fail s!"controls of the unreadable path {path} failed: {failed.toList}"

/-- The variable that marks the elaboration of this module which `checkIsolated` starts under Git
isolation, so that one whose environment still lacks an entry fails rather than starting another.
Whether the environment is isolated is decided from the environment, never from this variable. -/
def restartedVariable : String := "REGULA_ABSENCE_CONTROLS_RESTARTED"

/-- Run `check` where Lake's in-process loader can load a workspace: in a process whose
environment has every entry of the Git isolation (`Regula.GitIsolation.requireIsolated`, which
`Checker.Workspace` runs before each load). When this process's environment has every entry, as
in the first acceptance step, whose compiled program isolates its environment before it starts
Lake, `check` runs here. Otherwise, as in a `lake build` started from a shell, the toolchain's
`lean` elaborates `file`, this module, again under the isolation and `restartedVariable`, with this
process's other variables, among them the `LEAN_PATH` that Lake gives the elaboration, and its
failure, with its output, is this one's. A restarted elaboration whose environment still lacks an
entry fails, naming what to set. So a control fails only on what it observes, never on the shell's
Git environment.

Assumes: Lean v4.34.1 `Init/System/IO.lean:1420-1450` inherits the environment and the working
directory by default and applies `env` left to right (`runtime/process.cpp:436-515`); Lake
v4.34.1 starts the elaboration of a module with its `LEAN_PATH` in the environment
(`Lake/Build/Actions.lean:59-65`, `compileLeanModule`). -/
def checkIsolated (file : FilePath) : IO Unit := do
  let (isolation, missing) ← Regula.GitIsolation.observe
  if missing.isEmpty then return ← check
  if (← IO.getEnv restartedVariable).isSome then
    throw <| IO.userError s!"Git isolation did not take effect in the restarted elaboration of \
      {file}; still to set: {Regula.GitIsolation.describe missing}"
  let run ← IO.Process.output {
    cmd := ((← Lean.getBuildDir) / "bin/lean").toString
    args := #[file.toString]
    env := isolation.push (restartedVariable, some "1") }
  unless run.exitCode == 0 do
    throw <| IO.userError s!"the controls, elaborated again under Git isolation, failed (exit \
      {run.exitCode}): {run.stdout}{run.stderr}"

open Lean in
run_cmd do checkIsolated (← getFileName)

end Regula.AbsenceControls
