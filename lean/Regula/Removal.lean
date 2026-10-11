import RegulaCore.Removal
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.InitAttr

/-! # Removals at their own place

The operations by which the site executable removes a directory or a file. The exported ones,
`removeOwn` and `removeEntry`, each observe the place themselves, without following a symbolic
link at it, and remove only when the decision `Regula.Removal.removal` decided to remove
(`removal_remove_iff`). `requireOwnDirectory` stops unless a directory is at its own place or
nothing is there, by the same observation; the site checks Lake's directories with it before Lake
loads the checkout's package. The observation (`Observation`) and every operation that takes an
observation or a decision are private to this module. `removeDecided` is the one operation of
the site executable that calls a removal primitive of Lean's library, an operation that removes or
replaces an entry (`primitives`, `removalSymbols`). `rawRemovals` finds each
call of a removal primitive that an executable reaches other than through it or
`libraryRemovals`.

## What the check guarantees

The criterion is honest code, as `SECURITY.md` and `CONTEXT.md` define it: code that does not
deliberately change Lean's environment, compiler or build to make a check pass. Honest code in the
site executable cannot reach a removal outside this module, except the library removals that
`libraryRemovals` lists with the assumption on which each one rests. Deliberate circumvention by
Regula's own authors is outside it (issue 286), for example a hand-written `extern` bound to a C
function of the runtime that removes other than `removalSymbols`, or an observation made with
the `constructor` tactic, which applies the private constructor.

## Boundaries

The two reads of the file system (`System.FilePath.symlinkMetadata`, `IO.FS.realPath`) and the
removal primitives are trusted. That no process changes the place between the observation and the
removal is trusted. A process that replaces an entry below a directory with a symbolic link while
`IO.FS.removeDirAll` removes the directory is outside this module: that function examines each
entry and then opens it by its path. A removal by another program that an executable starts, such
as `rm`, is not a call that `rawRemovals` finds. On Windows every operation of this module stops
before it reads or removes anything (`refuseOnWindows`): the runtime has no read there that
follows no link. -/

namespace Regula.Removal

open System

/-- The name of the kind in a message. -/
def Kind.noun : Kind → String
  | .directory => "directory"
  | .file => "file"

/-- Stop on Windows, where no read follows no link. Assumes: there, the runtime of Lean
4.34.1 reads `System.FilePath.symlinkMetadata` with the read that follows a link
(`src/runtime/io.cpp:1160`, where `lean_io_symlink_metadata` returns `lean_io_metadata` on
Windows). -/
private def refuseOnWindows (path : FilePath) : IO Unit := do
  if System.Platform.isWindows then
    throw <| IO.userError s!"nothing was made or removed: {path} cannot be read without following \
      a symbolic link on Windows, so no removal and no path of an output is accepted there"

/-- What is at `path`, by a read that does not follow a symbolic link at `path` itself. It stops
on Windows (`refuseOnWindows`). -/
private def place (path : FilePath) : IO Place := do
  refuseOnWindows path
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => return match metadata.type with
    | .dir => .present .directory
    | .file => .present .file
    | _ => .other
  | .error (.noFileOrDirectory ..) => return .absent
  | .error error => throw error

/-- An observation of `path` that `observe` made. The type and its constructor are private to this
module, so the exported operations act only on observations that they made themselves. -/
private structure Observation (path : FilePath) where
  mk ::
  /-- What was observed at `path`. -/
  observed : Observed

/-- What is observed of `path` before a removal: what is there, by a read that follows no link
at the path, and whether its real path is the path. -/
private def observe (path : FilePath) : IO (Observation path) := do
  return .mk {
    place := ← place path
    sameLocation := match ← (IO.FS.realPath path).toBaseIO with
      | .ok real => real == path
      | .error _ => false }

/-- Remove the entry of `kind` at `path`, given an observation of `path` and the proof that
`removal` decided to remove on it. It is not inlined, so a removal primitive is called only in its
own compiled code (`decidedVariants`). It stops on Windows (`refuseOnWindows`), where no
observation is made either. -/
@[noinline]
private def removeDecided (path : FilePath) (kind : Kind) (observation : Observation path)
    (_decided : removal kind observation.observed = .remove) : IO Unit := do
  refuseOnWindows path
  match kind with
  | .directory => IO.FS.removeDirAll path
  | .file => IO.FS.removeFile path

/-- Act on what `removal` decides for `observation`, an observation of `path`. -/
private def removeObserved (kind : Kind) (path : FilePath) (observation : Observation path) :
    IO Unit :=
  match decided : removal kind observation.observed with
  | .nothing => pure ()
  | .remove => removeDecided path kind observation decided
  | .refuse =>
      throw <| IO.userError s!"nothing was removed: {path} is not a {kind.noun} at its own place \
        (a symbolic link, an entry of another kind, or a path through a symbolic link is there)"

/-- Remove the entry of `kind` at `path` when one is there at its own place, do nothing when
nothing is there, and stop with nothing removed in every other case (`removal_remove_iff`). A
directory or file is at its own place when its real path is `path`, so a relative path, a `.` or
`..` component and a symbolic link at any component make it refuse. -/
def removeOwn (kind : Kind) (path : FilePath) : IO Unit := do
  removeObserved kind path (← observe path)

/-- Remove the directory or file at `path`, whichever is there, at its own place; do nothing
when nothing is there; and stop with nothing removed when a symbolic link, another kind of
entry or a path through a symbolic link is there. The kind given to `removal` is the kind
observed. -/
def removeEntry (path : FilePath) : IO Unit := do
  let observation ← observe path
  let kind := match observation.observed.place with
    | .present kind => kind
    | _ => .directory
  removeObserved kind path observation

/-- Stop unless nothing is at `path` or a directory is there at its own place, by the observation
that `removeOwn` makes. These are the places on which `removal .directory` does not refuse
(`removal_remove_iff`, `removal_nothing_iff`), so a symbolic link, a file and a path through a
symbolic link at `path` make it stop. -/
def requireOwnDirectory (path : FilePath) : IO Unit := do
  let observation ← observe path
  if removal .directory observation.observed == .refuse then
    throw <| IO.userError s!"{path} is not a directory at its own place (a symbolic link, a file, \
      or a path through a symbolic link is there)"

/-- Stop unless nothing is at `path`, or a directory is there at its own place
(`requireOwnDirectory`) and each of its entries is a directory or a file, by a read that follows no
link at the entry. A symbolic link among the entries, also one whose target is absent, makes it
stop, so a file that a later operation opens by its name in this directory is not reached through
a link, when no process makes one after this check, which is trusted. -/
def requireNoLinkedEntries (path : FilePath) : IO Unit := do
  requireOwnDirectory path
  unless (← place path) matches .present .directory do return
  for entry in ← path.readDir do
    unless (← place entry.path) matches .present _ do
      throw <| IO.userError s!"{entry.path} is not a directory or a file (a symbolic link or \
        another kind of entry is there)"

/-- `path` as an absolute path whose present ancestors are at their own place. It refuses a path
with a `.` or `..` component before it reads anything. A relative path is joined to the real path
of the working directory, and no component that `path` gives is resolved. It refuses when the
nearest ancestor of `path` that is present, by a read that follows no link, is not its own real
path: a symbolic link is among the components up to it. An absent ancestor is made later by
`IO.FS.createDirAll` as a directory, so no link is among them when no process makes one after this
check, which is trusted. It stops on Windows (`refuseOnWindows`). -/
def ownPath (path : FilePath) : IO FilePath := do
  refuseOnWindows path
  if path.components.any (fun component => component == "." || component == "..") then
    throw <| IO.userError s!"nothing was made or removed: {path} has a `.` or `..` component"
  let path ← if path.isAbsolute then pure path
    else pure ((← IO.FS.realPath (← IO.currentDir)) / path)
  let refuse {α : Type} (ancestor : FilePath) : IO α := throw <| IO.userError
    s!"nothing was made or removed: {ancestor}, an ancestor of {path}, is not at its own place \
      (a symbolic link is among its components)"
  let mut ancestor := path.parent
  for _ in [:path.components.length] do
    let some current := ancestor | break
    match ← place current with
    | .absent => ancestor := current.parent
    | _ =>
      match ← (IO.FS.realPath current).toBaseIO with
      | .ok real => if real == current then return path else refuse current
      | .error _ => refuse current
  return path

open Lean IR

/-- The bound on the number of declarations that `rawRemovalsFrom` reads. -/
def maxDeclarations : Nat := 10_000_000

/-- The removal primitives of Lean's library, each of which removes or replaces a file or a
directory: the three removals, `IO.FS.rename`, which replaces the entry at its destination, and the
three writers of a module. Each file of a module is written to a temporary file, renamed over the
file, and the temporary file is removed when the write fails (`src/library/module.cpp:403` and
`:408`). -/
def primitives : List Name :=
  [``IO.FS.removeFile, ``IO.FS.removeDir, ``IO.FS.removeDirAll, ``IO.FS.rename,
    ``Lean.writeModule, ``Lean.saveModuleData, ``Lean.saveModuleDataParts]

/-- The C functions of the Lean 4.34.1 runtime that remove or replace an entry, by a search of its
sources (`src/runtime`, `src/library`) for `unlink`, `rmdir`, `rename` and `remove`. They are the
functions that `IO.FS.removeFile`, `IO.FS.removeDir` and `IO.FS.rename` are bound to
(`Init/System/IO.lean`), and the one that `Lean.CompactedRegion.save` is bound to, which writes a
module. A declaration of any name that is bound to one of them is a removal primitive. A C function
that writes to a file or makes an entry, without removing or replacing one, is not on this list. -/
def removalSymbols : List String :=
  ["lean_io_remove_file", "lean_io_remove_dir", "lean_io_rename", "lean_compacted_region_save"]

/-- Whether the entry of an `extern` attribute calls the C function `symbol`: by its name, or in
the C text of an inline entry. -/
def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

/-- The C function of `removalSymbols` that `name` is bound to, when it is an `extern`
declaration bound to one. -/
def boundRemoval (env : Environment) (name : Name) : Option String :=
  match findEnvDecl env name with
  | some (.extern _ _ _ data) =>
    removalSymbols.find? fun symbol => data.entries.any (bindsTo symbol)
  | _ => none

/-- The suffixes that Lean's compiler appends to the name of a declaration for the compiled
variants it makes of it: one without its irrelevant arguments, and the boxed form of each. -/
def compilerSuffixes : List Name :=
  [.anonymous, `_redArg, `_boxed, `_redArg ++ `_boxed]

/-- The name of `removeDecided`, which is private, for the controls of `rawRemovals`
(`Regula.RemovalControls`). -/
def decidedName : Name := ``removeDecided

/-- Whether `name` is `removeDecided` or a compiled variant that the compiler made of it: a name
of `compilerSuffixes` after its name, which is not the name of a declaration that a source
defines. -/
def decidedVariants (env : Environment) (name : Name) : Bool :=
  compilerSuffixes.any fun suffix =>
    name == decidedName ++ suffix && (suffix.isAnonymous || !env.contains name)

/-- The calls of a removal primitive in Lean's library that the site executable reaches, each
with the declaration that makes it, for Lean 4.34.1. Each one calls `IO.FS.removeFile` on one file
that the library itself manages, or `Lean.writeModule`; a removal of a directory is never on this
list. Each rests on an assumption, which the check does not establish:

- `Lake.importConfigFile`, with `IO.FS.removeFile` and with `Lean.writeModule`. Assumes: these
  remove and write only files in the directory of the root package's compiled configuration,
  `.lake/config/0` below the checkout. It removes the stale `lakefile.olean` and its trace
  (`Lake/Load/Lean/Elab.lean:244` and `:262`). It writes the new `lakefile.olean` and its
  siblings (`:256`), each through a temporary file that it renames over the file and removes when
  the write fails (`src/library/module.cpp:311-314`, `:403` and `:408`). That directory and the
  files written in it are the checkout's own: before the loader runs, `Workspace.withRootPackage`
  refuses when `.lake` or `.lake/config` is there and is not a directory at its own place
  (`requireOwnDirectory`), and when `.lake/config/0` is not one or has an entry that is a symbolic
  link (`requireNoLinkedEntries`), so no open for writing there follows a link. That check is the
  loader's prerequisite. The site loads only the root package of the checkout.
- `Lake.removeFileIfExists`, `Lake.downloadArtifactCore`, `Lake.download`. Assumes: the site runs
  no Lake build and no download of Lake's artifact cache in its own process, so these, which the
  build functions of Lake's facets reach (`Lake/Util/IO.lean:23`, `Lake/Config/Cache.lean:558`,
  `Lake/Build/Actions.lean:178`), do not run; the site runs `lake` as a separate process.
- The three variants of `IO.FS.withTempFile` in `bv_decide`. Assumes: the site elaborates no
  `bv_decide` proof, so these, which the tactic's initializers reach, do not run; each removes the
  temporary file that `withTempFile` made (`Init/System/IO.lean:1353`). -/
def libraryRemovals : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.removeFile),
    (`Lake.importConfigFile, ``Lean.writeModule),
    (`Lake.removeFileIfExists, ``IO.FS.removeFile),
    (`Lake.downloadArtifactCore, ``IO.FS.removeFile),
    (`Lake.download, ``IO.FS.removeFile),
    (`IO.FS.withTempFile._at_.Lean.Meta.Tactic.BVDecide.runExternal.spec_3._redArg._lam_0,
      ``IO.FS.removeFile),
    ((`IO.FS.withTempFile._at_._private.Lean.Elab.Tactic.Grind.BVDecide).num 0 ++
        `Lean.Elab.Tactic.Grind.evalBvDecide.spec_1._redArg._lam_0, ``IO.FS.removeFile),
    (`IO.FS.withTempFile._at_.Lean.Elab.Tactic.BVDecide.evalBvDecide.spec_1._redArg._lam_0,
      ``IO.FS.removeFile)]

/-- Whether the call of `primitive` by `caller` is a removal that this module admits: a call by
`removeDecided` (`decidedVariants`), or one of `libraryRemovals`. -/
def admitted (env : Environment) (caller primitive : Name) : Bool :=
  decidedVariants env caller || libraryRemovals.contains (caller, primitive)

/-- The declarations that run when an executable built from `env` starts: each declaration of
each module of `env` with an `[init]` or `[builtin_init]` attribute when it is the action that
runs, and otherwise the function that computes its value. -/
def initializers (env : Environment) : Array Name := Id.run do
  let mut roots := #[]
  for attr in [regularInitAttr, builtinInitAttr] do
    let mut entries := (attr.ext.getState env).2.toList.toArray
    for index in [:env.header.moduleNames.size] do
      entries := entries ++ attr.ext.getModuleEntries env index
        ++ attr.ext.getModuleIREntries env index
    for (decl, initDecl) in entries do
      roots := roots.push (if initDecl.isAnonymous then decl else initDecl)
  return roots

/-- Each call of a removal primitive that the compiled code of `roots` reaches and that
`admitted` does not admit, with the declaration that makes it; and each reached declaration whose
compiled body `env` does not hold, so that what it calls is unknown. An `extern` declaration bound
to a C function of `removalSymbols` (`boundRemoval`) is a removal primitive, whatever its name: a
call of it is admitted or raw as a call of `primitives` is, and as a root it is raw. Every compiled
declaration is followed, of this package, of Lean's library and of each other package; a C function
of the runtime is not. -/
def rawRemovalsFrom (env : Environment) (roots : Array Name) :
    Array (Name × Name) × Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut raw := #[]
  let mut unknown := #[]
  -- Each declaration is added to `work` at most once. The bound is far above the number of
  -- compiled declarations that an executable of this toolchain reaches (about 200,000); a
  -- declaration left in `work` at the bound is unknown, so the check fails closed.
  for _ in [:maxDeclarations] do
    let some name := work.back? | break
    work := work.pop
    match findEnvDecl env name with
    | some decl@(.fdecl ..) =>
      for used in collectUsedDecls env [decl] do
        if used == name then continue
        if primitives.contains used || (boundRemoval env used).isSome then
          unless admitted env name used do raw := raw.push (name, used)
        else if !seen.contains used then
          seen := seen.insert used
          work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) then unknown := unknown.push name
      if let some symbol := boundRemoval env name then raw := raw.push (name, Name.mkSimple symbol)
    | none => unknown := unknown.push name
  return (raw, unknown ++ work)

/-- `rawRemovalsFrom` for an executable whose `main` is `root`: from `root` and from each
initializer of the modules it links (`initializers`). -/
def rawRemovals (env : Environment) (root : Name) : Array (Name × Name) × Array Name :=
  rawRemovalsFrom env ((initializers env).push root)

end Regula.Removal
