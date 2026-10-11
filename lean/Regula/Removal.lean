import RegulaCore.Removal
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.InitAttr

/-! # Removals at their own place

The operations by which the site executable removes a directory or a file. Each one observes the
place itself, without following a symbolic link at it, and removes only when the decision
`Regula.Removal.removal` decided to remove (`removal_remove_iff`). The observation is an
`Observation` of the path, whose constructor is private, and every operation that takes an
observation or a decision is private, so a caller outside this module cannot remove on an
observation it made up. `removeDecided` is the one operation of the site executable that calls a
removal primitive of Lean's library. `rawRemovals` finds each call of such a primitive that an
executable reaches other than through it or `libraryRemovals`.

## Boundaries

The two reads of the file system (`System.FilePath.symlinkMetadata`, `IO.FS.realPath`) and the
removal primitives are trusted. That no process changes the place between the observation and the
removal is trusted. A process that replaces an entry below a directory with a symbolic link while
`IO.FS.removeDirAll` removes the directory is outside this module: that function examines each
entry and then opens it by its path. A removal by another program that an executable starts, such
as `rm`, is not a call that `rawRemovals` finds, and neither is a removal in code that the
compiled code reaches only through a C function of the runtime other than the primitives. -/

namespace Regula.Removal

open System

/-- The name of the kind in a message. -/
def Kind.noun : Kind → String
  | .directory => "directory"
  | .file => "file"

/-- What is at `path`, by a read that does not follow a symbolic link at `path` itself. -/
private def place (path : FilePath) : IO Place := do
  match ← path.symlinkMetadata.toBaseIO with
  | .ok metadata => return match metadata.type with
    | .dir => .present .directory
    | .file => .present .file
    | _ => .other
  | .error (.noFileOrDirectory ..) => return .absent
  | .error error => throw error

/-- An observation of `path` that `observe` made. Its constructor is private, so no code outside
this module has an observation that was not read from the file system. -/
structure Observation (path : FilePath) where
  private mk ::
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
own compiled code (`decidedVariants`). -/
@[noinline]
private def removeDecided (path : FilePath) (kind : Kind) (observation : Observation path)
    (_decided : removal kind observation.observed = .remove) : IO Unit :=
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

/-- `path` as an absolute path: a relative path is joined to the real path of the working
directory. No component that `path` gives is resolved, so `removeOwn` refuses the place when one
of them is a symbolic link, `.` or `..`. -/
def absolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then return path
  return (← IO.FS.realPath (← IO.currentDir)) / path

open Lean IR

/-- The bound on the number of declarations that `rawRemovalsFrom` reads. -/
def maxDeclarations : Nat := 10_000_000

/-- The removal primitives of Lean's library: each removes a file or a directory. -/
def primitives : List Name :=
  [``IO.FS.removeFile, ``IO.FS.removeDir, ``IO.FS.removeDirAll]

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
with the declaration that makes it, for Lean 4.34.1. Each one calls `IO.FS.removeFile`, which
unlinks the entry the path names: it removes no directory, it removes a symbolic link at that
entry and not the link's target, and it reads no directory's entries. Lake removes a stale
compiled configuration (`importConfigFile`), an output it replaces (`removeFileIfExists`) and a
download that failed (`downloadArtifactCore`, `download`); the three `withTempFile` variants of
`bv_decide` remove the temporary file they made. A removal of a directory is never on this list. -/
def libraryRemovals : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.removeFile),
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
compiled body `env` does not hold, so that what it calls is unknown. Every compiled declaration is
followed, of this package, of Lean's library and of each other package; a C function of the
runtime other than the primitives is not. -/
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
        if primitives.contains used then
          unless admitted env name used do raw := raw.push (name, used)
        else if !seen.contains used then
          seen := seen.insert used
          work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) then unknown := unknown.push name
    | none => unknown := unknown.push name
  return (raw, unknown ++ work)

/-- `rawRemovalsFrom` for an executable whose `main` is `root`: from `root` and from each
initializer of the modules it links (`initializers`). -/
def rawRemovals (env : Environment) (root : Name) : Array (Name × Name) × Array Name :=
  rawRemovalsFrom env ((initializers env).push root)

end Regula.Removal
