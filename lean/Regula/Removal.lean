import RegulaCore.Removal
import Lean.Compiler.IR.EmitUtil

/-! # Removals at their own place

The operations by which the site executable removes a directory or a file: each observes the
place without following a symbolic link at it, and removes only when the decision
`Regula.Removal.removal` decided to remove (`removal_remove_iff`). `removeDecided` is the one
operation that calls a removal primitive of Lean's library, and it takes the proof of that
decision. `rawRemovals` finds every call of such a primitive that an executable reaches other
than through `removeDecided`.

## Boundaries

The two reads of the file system (`System.FilePath.symlinkMetadata`, `IO.FS.realPath`) and the
removal primitives are trusted. That no process changes the place between the observation and the
removal is trusted. A process that replaces an entry below a directory with a symbolic link while
`IO.FS.removeDirAll` removes the directory is outside this module: that function examines each
entry and then opens it by its path. A removal by another program that an executable starts, such
as `rm`, is not a call that `rawRemovals` finds. -/

namespace Regula.Removal

open System

/-- The name of the kind in a message. -/
def Kind.noun : Kind → String
  | .directory => "directory"
  | .file => "file"

/-- What is at `path`, by a read that does not follow a symbolic link at `path` itself. -/
def place (path : FilePath) : IO Place := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => return match metadata.type with
    | .dir => .present .directory
    | .file => .present .file
    | _ => .other
  | .error (.noFileOrDirectory ..) => return .absent
  | .error error => throw error

/-- What is observed of `path` before a removal: what is there, by a read that follows no link
at the path, and whether its real path is the path. -/
def observe (path : FilePath) : IO Observed := do
  return {
    place := ← place path
    sameLocation := match ← (IO.FS.realPath path).toBaseIO with
      | .ok real => real == path
      | .error _ => false }

/-- Remove the entry of `kind` at `path`. A caller must give the proof that `removal` decided to
remove it, so no call exists for a path that `removal` refused or found empty. It is not inlined,
so a removal primitive is called only in its own compiled code (`rawRemovals`). -/
@[noinline]
def removeDecided (path : FilePath) (kind : Kind) (observed : Observed)
    (_decided : removal kind observed = .remove) : IO Unit :=
  match kind with
  | .directory => IO.FS.removeDirAll path
  | .file => IO.FS.removeFile path

/-- Act on what `removal` decides for `observed`, the observation of `path`. -/
def removeObserved (kind : Kind) (path : FilePath) (observed : Observed) : IO Unit :=
  match decided : removal kind observed with
  | .nothing => pure ()
  | .remove => removeDecided path kind observed decided
  | .refuse =>
      throw <| IO.userError s!"nothing was removed: {path} is not a {kind.noun} at its own place \
        (a symbolic link, an entry of another kind, or a path through a symbolic link is there)"

/-- Remove the entry of `kind` at `path` when one is there at its own place, do nothing when
nothing is there, and stop with nothing removed in every other case (`removal_remove_iff`). A
directory or file is at its own place when its real path is `path`, so `path` must be absolute
and have no `.`, `..` or symbolic link among its components (`ownPlace`). -/
def removeOwn (kind : Kind) (path : FilePath) : IO Unit := do
  removeObserved kind path (← observe path)

/-- Remove the directory or file at `path`, whichever is there, at its own place; do nothing
when nothing is there; and stop with nothing removed when a symbolic link, another kind of
entry or a path through a symbolic link is there. The kind given to `removal` is the kind
observed. -/
def removeEntry (path : FilePath) : IO Unit := do
  let observed ← observe path
  let kind := match observed.place with
    | .present kind => kind
    | _ => .directory
  removeObserved kind path observed

/-- The place that `path` names, written as the real path of its parent and its own name, so that
`removeOwn` removes a directory or file there whatever links its parent path goes through. The
parent is created when it is absent. It refuses a path whose last component is not a name (`.`,
`..`, a root, or a path that ends with a separator). -/
def ownPlace (path : FilePath) : IO FilePath := do
  let some name := path.fileName
    | throw <| IO.userError s!"{path} does not end in the name of a directory or file"
  let parent := path.parent.getD "."
  IO.FS.createDirAll parent
  return (← IO.FS.realPath parent) / name

open Lean IR

/-- The removal primitives of Lean's library: each removes a file or a directory. -/
def primitives : List Name :=
  [``IO.FS.removeFile, ``IO.FS.removeDir, ``IO.FS.removeDirAll, ``IO.FS.withTempFile,
    ``IO.FS.withTempDir]

/-- The compiled declarations of this package in `env`: those of each imported module whose
name's first component starts with `Regula`, and those of the module being elaborated. -/
def packageDecls (env : Environment) : Std.HashSet Name := Id.run do
  let mut names : Std.HashSet Name := {}
  for h : index in [:env.header.moduleNames.size] do
    if env.header.moduleNames[index].getRoot.toString.startsWith "Regula" then
      for decl in PersistentEnvExtension.getModuleEntries declMapExt env index do
        names := names.insert decl.name
  for decl in declMapExt.getEntries env do
    names := names.insert decl.name
  return names

/-- Every removal primitive that the compiled code of `root` reaches through the compiled
declarations of this package other than `removeDecided`, with the declaration that calls it; and
each such declaration whose compiled body `env` does not hold, so that what it calls is unknown.
A declaration of Lean's library or of another package is not followed: what it removes is
trusted. -/
def rawRemovals (env : Environment) (root : Name) : Array (Name × Name) × Array Name := Id.run do
  let package := packageDecls env
  let decided := ``removeDecided
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut work := #[root]
  let mut raw := #[]
  let mut unknown := #[]
  -- Each declaration of the package is added to `work` at most once.
  for _ in [:package.size + 1] do
    let some name := work.back? | break
    work := work.pop
    match findEnvDecl env name with
    | some decl@(.fdecl ..) =>
      for used in collectUsedDecls env [decl] do
        if used == name then continue
        if primitives.contains used then raw := raw.push (name, used)
        else if package.contains used && !decided.isPrefixOf used && !seen.contains used then
          seen := seen.insert used
          work := work.push used
    | _ => unknown := unknown.push name
  return (raw, unknown ++ work)

end Regula.Removal
