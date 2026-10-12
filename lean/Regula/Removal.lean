import Regula.Filesystem
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.InitAttr
import Lean.Elab.Command

/-! # The check that every removal of a program goes through the observer

A removal primitive of Lean's library is an operation that removes or replaces an entry
(`primitives`, `removalSymbols`). `rawRemovalsFrom` follows the compiled code of a program from its
`main` and the initializers of the modules it links, and finds each call of a removal primitive
that a declaration makes other than a declaration with the filesystem observer's role
(`@[regula_observer filesystem]`, `Regula.Filesystem`) or a call of Lean's library that
`libraryRemovals` lists. The observer's removals and its move are private to `Regula.Filesystem`,
and the operations it exports observe the place and act only on what the decisions of
`RegulaCore.Removal` decide.

`checkProgram` runs the check for the program whose `main` the environment declares, fails the
build of the module that runs it when the check finds a call, and records the program in the
module (`reached`). Each program of the package runs it: at the end of the root module of each
`lean_exe`, or in a module of `Regula.ProgramCheck` that imports a program that `lean --run` runs
and that cannot import this module. `lake exe qualify observers` refuses a program of the package
that no module records, and checks itself the one root that no library module can import,
`auditApp`'s `Main` (`Regula.Qualification.Observers`).

The check also counts the calls of an operation that writes a file or makes an entry
(`writePrimitives`) that the program's own declarations make outside the observer: the writes are
not yet routed through the observer, and each count is recorded and reported, not refused.

## What the check guarantees

The criterion is honest code, as `SECURITY.md` and `CONTEXT.md` define it: code that does not
deliberately change Lean's environment, compiler or build to make a check pass. Honest code in a
checked program cannot reach a removal outside the observer, except the library removals that
`libraryRemovals` lists with the assumption on which each one rests, and the removals of the two
programs that `scripts/verify.sh` and `scripts/provision.sh` run, which are admitted by name where
they are checked (`Regula.ProgramCheck.Verification`, `Regula.ProgramCheck.Provision`, issue
389). Deliberate
circumvention by Regula's own authors is outside it (issue 286), for example a hand-written
`extern` bound to a C function of the runtime that removes other than `removalSymbols`, or a use of
the private declarations of `Regula.Filesystem`.

## Boundaries

The C functions of the runtime are not followed: `removalSymbols` lists the ones that remove or
replace an entry. A removal by another program that a program starts, such as `rm`, is not a call
that the check finds. The check reads the compiled code that the environment holds; a declaration
whose compiled code it does not hold is unknown, and the check fails. -/

namespace Regula.Removal

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

/-- The operations of Lean's library that write a file or make an entry, without removing or
replacing one: a call of one of them is counted, not refused. `IO.FS.Handle.mk` and
`IO.FS.withFile` open a file in a mode that the compiled code passes as a value, so each call of
them is counted, also one that only reads. -/
def writePrimitives : List Name :=
  [``IO.FS.writeFile, ``IO.FS.writeBinFile, ``IO.FS.Handle.mk, ``IO.FS.withFile,
    ``IO.FS.createDir, ``IO.FS.createDirAll, ``IO.FS.createTempFile, ``IO.FS.createTempDir]

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

/-- The declarations of `env` with the observer's role of the filesystem
(`@[regula_observer filesystem]`, `Regula.Assumption.roles`). -/
def filesystemObservers (env : Environment) : Array Name :=
  (Regula.Assumption.roles env).filterMap fun (name, role) =>
    if role == .observer .filesystem then some name else none

/-- Whether `name` is one of `observers` or a compiled variant that the compiler made of one: a
name of `compilerSuffixes` after its name, which is not the name of a declaration that a source
defines. -/
def observerVariant (env : Environment) (observers : Array Name) (name : Name) : Bool :=
  observers.any fun observer => compilerSuffixes.any fun suffix =>
    name == observer ++ suffix && (suffix.isAnonymous || !env.contains name)

/-- The calls of a removal primitive in Lean's library that a program of the package reaches, each
with the declaration that makes it, for Lean 4.34.1. Each one calls `IO.FS.removeFile` on one file
that the library itself manages, or `Lean.writeModule`, except Lake's removal of a dependency's
clone and its move of a packages directory. Each rests on an assumption, which the check does not
establish:

- `Lake.importConfigFile`, with `IO.FS.removeFile` and with `Lean.writeModule`. Assumes: these
  remove and write only files in the directory of the root package's compiled configuration,
  `.lake/config/0` below the checkout. It removes the stale `lakefile.olean` and its trace
  (`Lake/Load/Lean/Elab.lean:244` and `:262`). It writes the new `lakefile.olean` and its
  siblings (`:256`), each through a temporary file that it renames over the file and removes when
  the write fails (`src/library/module.cpp:311-314`, `:403` and `:408`). That directory and the
  files written in it are the checkout's own: before the loader runs,
  `Regula.Checker.Workspace.withRootPackage` and `Regula.Checker.Workspace.withRootWorkspace`
  refuse when `.lake` or `.lake/config` is there and is not a directory at its own place
  (`Regula.Filesystem.requireOwnDirectory`), and when `.lake/config/0` is not one or has an entry
  that is a symbolic link (`Regula.Filesystem.requireNoLinkedEntries`), so no open for writing
  there follows a link. They are the only callers of Lake's loaders in `lean/`, by a search for
  them.
- `Lake.removeFileIfExists`, `Lake.downloadArtifactCore`, `Lake.download`. Assumes: a program that
  runs no Lake build and no download of Lake's artifact cache in its own process does not run
  these, which the build functions of Lake's facets reach (`Lake/Util/IO.lean:23`,
  `Lake/Config/Cache.lean:558`, `Lake/Build/Actions.lean:178`).
- `Lake.updateGitRepo`, specialized at `Lake.materializeGitRepo`, with `IO.FS.removeDirAll`.
  Assumes: it removes the clone of a dependency, `<workspace>/<packages>/<name>`, only when a
  directory is there whose remote is not the dependency's URL (`Lake/Load/Materialize.lean:64-82`),
  and a program reaches it only through `Regula.Checker.Workspace.withRootWorkspace`, the only
  caller of Lake's loaders that resolve dependencies in `lean/` by a search for them. Before Lake
  materializes the dependencies that a manifest locks, that function refuses when the clone of one
  is not a directory at its own place and its `HEAD` is not the manifest's revision, at which Lake
  leaves it as it is (`Lake/Load/Materialize.lean:251-261`). Before Lake's update of a workspace
  without a manifest, it refuses when the packages directory is not a directory at its own place
  or has an entry that is a symbolic link. So the clone that Lake removes is a directory at its own
  place, when the name of each package is one path component and no process changes the places
  between the check and the removal.
- `Lake.reuseManifest`, specialized at `Lake.Workspace.updateAndMaterializeCore`, with
  `IO.FS.rename`. Assumes: it moves the packages directory that a loaded manifest names to the
  workspace's, only when a manifest loads (`Lake/Load/Resolve.lean:252-283`), and
  `Regula.Checker.Workspace.withRootWorkspace` runs Lake's update only when `Lake.Manifest.load?`
  finds no manifest, so it moves nothing when no process makes a manifest between the two reads.
- The three variants of `IO.FS.withTempFile` in `bv_decide`. Assumes: the program elaborates no
  `bv_decide` proof, so these, which the tactic's initializers reach, do not run; each removes the
  temporary file that `withTempFile` made (`Init/System/IO.lean:1353`). -/
def libraryRemovals : List (Name × Name) :=
  [(`Lake.importConfigFile, ``IO.FS.removeFile),
    (`Lake.importConfigFile, ``Lean.writeModule),
    (`Lake.removeFileIfExists, ``IO.FS.removeFile),
    (`Lake.downloadArtifactCore, ``IO.FS.removeFile),
    (`Lake.download, ``IO.FS.removeFile),
    (mkPrivateNameCore `Lake.Load.Materialize `Lake.updateGitRepo ++ `_at_ ++
        mkPrivateNameCore `Lake.Load.Materialize `Lake.materializeGitRepo ++ `spec_0,
      ``IO.FS.removeDirAll),
    (mkPrivateNameCore `Lake.Load.Resolve `Lake.reuseManifest ++ `_at_ ++
        mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateAndMaterializeCore ++ `spec_3,
      ``IO.FS.rename),
    (`IO.FS.withTempFile._at_.Lean.Meta.Tactic.BVDecide.runExternal.spec_3._redArg._lam_0,
      ``IO.FS.removeFile),
    ((`IO.FS.withTempFile._at_._private.Lean.Elab.Tactic.Grind.BVDecide).num 0 ++
        `Lean.Elab.Tactic.Grind.evalBvDecide.spec_1._redArg._lam_0, ``IO.FS.removeFile),
    (`IO.FS.withTempFile._at_.Lean.Elab.Tactic.BVDecide.evalBvDecide.spec_1._redArg._lam_0,
      ``IO.FS.removeFile)]

/-- Whether the call of `primitive` by `caller` is a removal that the check admits: a call by one of
`observers` or a compiled variant of one (`observerVariant`), or one of `libraryRemovals` or of
`named`, the removals that a program which cannot import `Regula.Filesystem` names, each as the
pair of its caller and the primitive that it calls. -/
def admitted (env : Environment) (observers : Array Name) (named : List (Name × Name))
    (caller primitive : Name) : Bool :=
  observerVariant env observers caller || (libraryRemovals ++ named).contains (caller, primitive)

/-- The modules that a program whose `main` is in the module `root` links: `root` and each module
that it imports, directly or through another. -/
def linked (env : Environment) (root : Name) : Std.HashSet Name := Id.run do
  let mut index : Std.HashMap Name Nat := {}
  for h : position in [:env.header.moduleNames.size] do
    index := index.insert env.header.moduleNames[position] position
  let importsOf (module : Name) : Array Name :=
    if module == env.mainModule then env.header.imports.map (·.module)
    else match index[module]? with
      | some position =>
        (env.header.moduleData[position]?.map (·.imports.map (·.module))).getD #[]
      | none => #[]
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert root
  let mut work := #[root]
  for _ in [:env.header.moduleNames.size + 1] do
    let some module := work.back? | break
    work := work.pop
    for imported in importsOf module do
      unless seen.contains imported do
        seen := seen.insert imported
        work := work.push imported
  return seen

/-- The declarations that run when a program that links the modules `modules` starts: each
declaration of each of them with an `[init]` or `[builtin_init]` attribute when it is the action
that runs, and otherwise the function that computes its value. -/
def initializersOf (env : Environment) (modules : Std.HashSet Name) : Array Name := Id.run do
  let mut roots := #[]
  for attr in [regularInitAttr, builtinInitAttr] do
    let mut entries := if modules.contains env.mainModule then
      (attr.ext.getState env).2.toList.toArray else #[]
    for h : index in [:env.header.moduleNames.size] do
      if modules.contains env.header.moduleNames[index] then
        entries := entries ++ attr.ext.getModuleEntries env index
          ++ attr.ext.getModuleIREntries env index
    for (decl, initDecl) in entries do
      roots := roots.push (if initDecl.isAnonymous then decl else initDecl)
  return roots

/-- The declarations that run when a program built from `env` starts, of every module of `env`
(`initializersOf`). -/
def initializers (env : Environment) : Array Name :=
  initializersOf env (env.header.moduleNames.foldl (·.insert ·)
    (({} : Std.HashSet Name).insert env.mainModule))

/-- What the compiled code of a set of roots reaches. -/
structure Reach where
  /-- Each call of a removal primitive that the check does not admit, with its caller. -/
  raw : Array (Name × Name)
  /-- Each reached declaration whose compiled code the environment does not hold. -/
  unknown : Array Name
  /-- Each call of a primitive of `writePrimitives`, with its caller. -/
  writes : Array (Name × Name)

/-- Each call of a removal primitive that the compiled code of `roots` reaches and that `admitted`
does not admit, with the declaration that makes it; each reached declaration whose compiled body
`env` does not hold, so that what it calls is unknown; and each call of a primitive of
`writePrimitives`. An `extern` declaration bound to a C function of `removalSymbols`
(`boundRemoval`) is a removal primitive, whatever its name: a call of it is admitted or raw as a
call of `primitives` is, and as a root it is raw. Every compiled declaration is followed, of this
package, of Lean's library and of each other package, the callees of a write primitive among them;
a C function of the runtime is not. -/
def rawRemovalsFrom (env : Environment) (observers : Array Name) (roots : Array Name)
    (named : List (Name × Name) := []) : Reach :=
  Id.run do
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut raw := #[]
  let mut unknown := #[]
  let mut writes := #[]
  -- Each declaration is added to `work` at most once. The bound is far above the number of
  -- compiled declarations that a program of this toolchain reaches (about 200,000); a declaration
  -- left in `work` at the bound is unknown, so the check fails closed.
  for _ in [:maxDeclarations] do
    let some name := work.back? | break
    work := work.pop
    match findEnvDecl env name with
    | some decl@(.fdecl ..) =>
      for used in collectUsedDecls env [decl] do
        if used == name then continue
        if primitives.contains used || (boundRemoval env used).isSome then
          unless admitted env observers named name used do raw := raw.push (name, used)
        else
          if writePrimitives.contains used then writes := writes.push (name, used)
          if !seen.contains used then
            seen := seen.insert used
            work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) then unknown := unknown.push name
      if let some symbol := boundRemoval env name then raw := raw.push (name, Name.mkSimple symbol)
    | none => unknown := unknown.push name
  return { raw, unknown := unknown ++ work, writes }

/-- `rawRemovalsFrom` for a program whose `main` is `main` in the module `root`: from `main` and
from each initializer of the modules that it links (`linked`, `initializersOf`), with the
filesystem observers of `env` and the removals `named`. -/
def rawRemovals (env : Environment) (root : Name) (named : List (Name × Name) := []) : Reach :=
  rawRemovalsFrom env (filesystemObservers env) ((initializersOf env (linked env root)).push `main)
    named

/-- The prefix of the marker that `checkProgram` adds for each program that it checked: the
definition `reached ++ root`, where `root` is the program's root module, is the number of calls of
a write primitive outside the observer that the program's own declarations make. `lake exe qualify
observers` reads the markers from the module data of the package's modules. -/
def reached : Name := `Regula.Removal.reached

/-- Whether `module` is a module of the toolchain: its object file is below `lib/lean` of the
toolchain's root (`Lean.findSysroot`). -/
def toolchainModule (sysroot : System.FilePath) (module : Name) : IO Bool := do
  let olean ← findOLean module
  return (sysroot / "lib" / "lean").components.isPrefixOf olean.components

/-- Why the check refuses the program whose root module is `root`, by what its compiled code
reaches (`rawRemovals`): each call of a removal primitive that the check does not admit, and each
reached declaration whose compiled code is unknown; `none` when there is neither. -/
def programRefusal (root : Name) (reach : Reach) : Option String :=
  if !reach.raw.isEmpty then
    some s!"the program of {root} removes without the observer `Regula.Filesystem`: \
      {reach.raw.toList.map fun (caller, primitive) => s!"{caller} calls {primitive}"}"
  else if !reach.unknown.isEmpty then
    some s!"the program of {root} reaches declarations whose compiled code is not available, so \
      their removals are unknown: {reach.unknown.toList}"
  else none

/-- The distinct calls of a write primitive in `reach` that declarations outside the toolchain
make (`toolchainModule`): the writes of the program that are not yet routed through the
observer. -/
def pendingWrites (env : Environment) (reach : Reach) : IO (Std.HashSet (Name × Name)) := do
  let sysroot ← Lean.findSysroot
  let mut toolchain : Std.HashMap Name Bool := {}
  let mut pending : Std.HashSet (Name × Name) := {}
  for (caller, primitive) in reach.writes do
    let module := match env.getModuleIdxFor? caller with
      | some index => env.header.moduleNames[index.toNat]!
      | none => env.mainModule
    let inToolchain ← match toolchain[module]? with
      | some known => pure known
      | none => do
        let known ← if module == env.mainModule then pure false
          else toolchainModule sysroot module
        toolchain := toolchain.insert module known
        pure known
    unless inToolchain do pending := pending.insert (caller, primitive)
  return pending

/-- Check the program whose `main` the environment declares: fail with the refusal of the
program (`programRefusal`) when there is one. Then record the program with the number of its writes that
are not routed through the observer (`pendingWrites`, `reached`). `named` admits the removals that
a program which cannot import `Regula.Filesystem` names, each as the pair of its caller and the
primitive that it calls (`admitted`). -/
def checkProgram (named : List (Name × Name) := []) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless env.contains `main do
    throwError "no `main` is declared here, so there is no program to check"
  let root := match env.getModuleIdxFor? `main with
    | some index => env.header.moduleNames[index.toNat]!
    | none => env.mainModule
  let reach := rawRemovals env root named
  if let some refused := programRefusal root reach then throwError refused
  let pending ← pendingWrites env reach
  Elab.Command.liftCoreM <| addDecl (.defnDecl {
    name := reached ++ root, levelParams := [], type := mkConst ``Nat,
    value := mkNatLit pending.size, hints := .abbrev, safety := .safe })

end Regula.Removal
