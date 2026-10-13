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
its build fails when a control does not give the expected result, naming each such control. These
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
  in the manifest, and the check of each loaded package (`requireConfigChoice`) must fail at the
  link. Each other changed site binds an observer's result in `IO` in the same way, so the error
  propagates there too, unless a caller catches it; this control does not run them.
- The loaders once the path can be read again (`loaderControls`): `withRootWorkspace` must refuse
  `withdep`, whose manifest records the choice of `lakefile.toml` for `dep`, naming the package
  and `lake update`. With the links removed, both loaders must load `configured`, and
  `withRootWorkspace` must load `withdep` with its dependency.
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
`lakefile.toml`, so the next load must refuse that recorded choice, naming the package and
`lake update`. With the two links removed, both loaders must load `configured`, and
`withRootWorkspace` must load `withdep` with its dependency. A `lakefile.lean` cannot stay for
these loads: Lake elaborates it, which needs the native initialization of Lake that the
elaboration of this module does not have. -/
def loaderControls (base : FilePath) : IO (List (String × Bool)) := do
  let configured := base / "configured"
  let withdep := base / "withdep"
  let recorded := match ← (Regula.Checker.Workspace.withRootWorkspace withdep fun _ =>
      pure ()).toBaseIO with
    | .error error =>
        let text := toString error
        (text.splitOn "Lake loaded package 'dep' from lakefile.toml").length > 1 &&
          (text.splitOn "lake update").length > 1
    | .ok () => false
  Regula.Filesystem.removePath .link (withdep / "dep" / "lakefile.lean")
  Regula.Filesystem.removePath .link (configured / "lakefile.lean")
  let loads (load : IO Nat) (count : Nat) : IO Bool := do
    return match ← load.toBaseIO with
      | .ok loaded => loaded == count
      | .error _ => false
  let size (ws : _root_.Lake.Workspace) : IO Nat := pure ws.packages.size
  return [
    ("Regula.Checker.Workspace.withRootWorkspace with a recorded choice of lakefile.toml",
      recorded),
    ("Regula.Checker.Workspace.withRootWorkspace with one configuration",
      ← loads (Regula.Checker.Workspace.withRootWorkspace configured size) 1),
    ("Regula.Checker.Workspace.withRootPackage with one configuration",
      ← loads (Regula.Checker.Workspace.withRootPackage configured size) 1),
    ("Regula.Checker.Workspace.withRootWorkspace with a dependency",
      ← loads (Regula.Checker.Workspace.withRootWorkspace withdep size) 2)]

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
      for entry in ← parent.readDir do
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
    -- recorded `lakefile.toml`, and the link is removed before the loads that succeed.
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
    unless failed.isEmpty do
      fail s!"controls of the unreadable path {path} failed: {failed.toList}"

run_cmd check

end Regula.AbsenceControls
