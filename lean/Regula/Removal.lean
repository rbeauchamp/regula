import Regula.Filesystem
import Regula.Process
import Lake.Build.Actions
import Lake.Util.Proc
import Lean.Compiler.IR.EmitUtil
import Lean.Compiler.InitAttr
import Lean.Elab.Command

/-! # Compiled reach to external-system primitives

The name of this module remains compatible with the filesystem check. Its single `boundaries`
table now gives filesystem replacements, process starts and environment observations. One reach
walk and one admission decision (`admitted`) serve every row. The walk starts at the program's
`main` and the initializers of its linked modules, and follows Lean's compiled IR. A primitive or
an extern bound to a listed native symbol stops the walk and checks its caller. Missing compiled
code or unfinished traversal fails closed.

The observer role is admitted only in its row's observer module: `Regula.Filesystem` or
`Regula.Process`. A role elsewhere admits nothing. Sourced library pairs, imported toolchain
environment observations and explicitly named bootstrap pairs are trusted exemptions. The cold
drivers elaborate the same process source as the compiled observer, with no second policy.

`checkProgram` refuses a program at build time and records every accepted program under `reached`.
The existing `qualify observers` campaign checks those records for each executable and standalone
source driver, and checks the executable root outside the package's libraries itself. It remains
in self-audit shard 4/4.

## Limits

This is the honest-code boundary of `SECURITY.md` and `CONTEXT.md`: deliberate compiler or
environment mutation, private-declaration access and arbitrary trusted plugins remain outside it.
Each named pair admits its whole caller/primitive pair, including a second call of that primitive
inside the same caller. Issue 389 owns the drivers' filesystem decisions. Lake's source
configuration, builds and dependent programs remain trusted library behavior.

The runtime's C bodies and child programs are not followed. The table identifies the pinned
runtime symbols at the Lean boundary. A new native binding outside that table needs a sourced
entry before this check can say anything about its effects. -/

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

/-- Whether the entry of an `extern` attribute calls the C function `symbol`: by its name, or in
the C text of an inline entry. -/
def bindsTo (symbol : String) : ExternEntry → Bool
  | .standard _ fn => fn == symbol
  | .inline _ pattern => (pattern.splitOn symbol).length > 1
  | _ => false

/-- The suffixes that Lean's compiler appends to the name of a declaration for the compiled
variants it makes of it: one without its irrelevant arguments, and the boxed form of each. -/
def compilerSuffixes : List Name :=
  [.anonymous, `_redArg, `_boxed, `_redArg ++ `_boxed]

/-- The module whose declarations may have the filesystem observer's role: `Regula.Filesystem`,
whose exported operations remove only what the decisions of `RegulaCore.Removal` decide. -/
def observerModule : Name := `Regula.Filesystem

/-- The module of `env` that declares `name`: the module of the environment's own commands when no
imported module declares it. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

/-- The declarations of `env` with the observer's role of the filesystem
(`@[regula_observer filesystem]`, `Regula.Assumption.roles`), split by whether `observerModule`
declares them: those it declares, and those of every other module. -/
def observerRoles (env : Environment) (system : RegulaPolicy.External.System := .filesystem)
    (owner : Name := observerModule) : Array Name × Array Name :=
  (Regula.Assumption.roles env).foldl (init := (#[], #[])) fun (own, foreign) (name, role) =>
    if role != .observer system then (own, foreign)
    else if moduleOf env name == owner then (own.push name, foreign)
    else (own, foreign.push name)

/-- The filesystem observers that the check admits: the declarations of `observerModule` with the
observer's role (`observerRoles`). A role given in another module admits nothing. -/
def filesystemObservers (env : Environment) : Array Name :=
  (observerRoles env).1

/-- The declarations of other modules than `observerModule` with the filesystem observer's role,
each of which the check of a program refuses (`programRefusal`). -/
def foreignObservers (env : Environment) : Array Name :=
  (observerRoles env).2

/-- Whether `name` is one of `observers` or a compiled variant that the compiler made of one: a
name of `compilerSuffixes` after its name, which is not the name of a declaration that a source
defines. -/
def observerVariant (env : Environment) (observers : Array Name) (name : Name) : Bool :=
  observers.any fun observer => compilerSuffixes.any fun suffix =>
    name == observer ++ suffix && (suffix.isAnonymous || !env.contains name)

/-- The calls of a removal primitive in Lean's library that a program of the package reaches, each
with the declaration that makes it, for Lean 4.34.1. The check admits each of them without
establishing what it removes.

Lake's entries are trusted exemptions. Lake makes these removals and moves itself when a program
loads a workspace or builds in its own process (`Regula.Checker.Workspace`). Each acts on the
workspace that the program asked Lake to load or build, as `lake build` or `lake update` would
there. Its safety rests on that workspace's own contents: its configuration and targets, the clones
of its dependencies and the release archives that it fetches, which its adopter trusts as Lake
does. The same reason holds where a program runs Lake in a copy of a project that it made, such as
`Regula.Checker.Lake.copyProject`'s or the verification driver's: Lake acts on the copy as it would
on the workspace it was given. The limit of this exemption: a copy that `cp -R` makes, as
`Regula.Qualification.Slot` and the provisioning driver make theirs, holds the symbolic links that
the original holds, and a relative one resolves against the copy's location, not the original's. A
copy that `copyProject` makes holds the link that Regula places to the original's packages
directory. Lake's removals in a copy can act through either. Issue 399 tracks making each copy by
construction, so that it holds only directories, files and that one link.

- `Lake.importConfigFile`, with `IO.FS.removeFile` and with `Lean.writeModule`. Trusted exemption,
  for the reason above: it removes the stale compiled configuration of a package and its trace in
  `.lake/config/<index>`, and writes the new one and its siblings, each through a temporary file
  that it renames over the file and removes when the write fails (`Lake/Load/Lean/Elab.lean:244`,
  `:256` and `:262`, `src/library/module.cpp:311-314`, `:403` and `:408`).
  `Regula.Checker.Workspace.withRootPackage` keeps its own check of `.lake/config/0` too
  (`Regula.Filesystem.requireNoLinkedEntries`).
- `Lake.removeFileIfExists`, `Lake.downloadArtifactCore`, `Lake.download`. Trusted exemption, for
  the reason above: in a build, they remove stale artifacts, their `.hash` files and no-build
  traces, and a downloaded archive before it is fetched again and unpacked into a package's build
  directory (`Lake/Util/IO.lean:23`, `Lake/Build/Common.lean:313-326`,
  `Lake/Build/Package.lean:140-150`, `Lake/Build/Actions.lean:178`, `Lake/Config/Cache.lean:558`).
  Regula's builds turn off Lake's artifact cache
  (`Regula.Checker.Workspace.uncachedWorkspace_unreadable`, `uncachedWorkspace_unwritable`), not
  the fetch of a release archive.
- `Lake.updateGitRepo`, specialized at `Lake.materializeGitRepo`, with `IO.FS.removeDirAll`.
  Trusted exemption, for the reason above: it removes the clone of a dependency,
  `<workspace>/<packages>/<name>`, when a directory is there whose remote is not the dependency's
  URL (`Lake/Load/Materialize.lean:64-82` and `:251-261`).
- `Lake.reuseManifest`, specialized at `Lake.Workspace.updateAndMaterializeCore`, with
  `IO.FS.rename`. Trusted exemption, for the reason above: it moves the packages directory that a
  loaded manifest names to the workspace's (`Lake/Load/Resolve.lean:252-283`).
- The three variants of `IO.FS.withTempFile` in `bv_decide`. Trusted library exemption: source
  configuration can elaborate this builtin tactic. Each removes the temporary file that Lean's
  `withTempFile` made (`Init/System/IO.lean:1348-1357`); its temp-file mechanism remains trusted. -/
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

/-- One system's primitive boundary. All systems use the same reach and admission decision. -/
structure Boundary where
  /-- The external system whose primitive calls are controlled. -/
  system : RegulaPolicy.External.System
  /-- Lean operations at which traversal stops and checks their caller. -/
  primitives : List Name
  /-- Runtime symbols that a differently named extern can bind. -/
  symbols : List String
  /-- The only module that can supply an observer for this boundary. -/
  observer : Name
  /-- Sourced library exemptions, each a caller and primitive pair. -/
  library : List (Name × Name) := []
  /-- Exported library launch entrypoints that project callers may not use directly. -/
  entrypoints : List Name := []
  /-- Imported library roots trusted to call these entrypoints within their own mechanisms. -/
  entrypointCallers : List Name := []
  /-- Imported library roots trusted to observe this system's primitives. -/
  libraryCallers : List Name := []

/-- Lake and Lean v4.34.1 start their own processes at these library boundaries.
Assumes: the caller constructs Lake's environment from the checked installation and refuses
nonabsolute compiler/archiver overrides before loading or building a workspace. Lake's Git,
download, extraction and build mechanisms remain trusted, as the workspace's own configuration
does. Sources: `Lake/Util/Proc.lean:29-91`, `Lake/Build/Actions.lean` and
`Lake/Config/InstallPath.lean:278-318`. The private updateToolchain specialization delegates an
alternative-toolchain restart to Elan (`Lake/Load/Resolve.lean:368-430`); Regula's in-process load
configuration supplies no lakeArgs for that restart. This whole library pair remains trusted.
Lean's builtin solver start is a trusted library boundary. Regula supplies its checked cadical
through the initial sat.solver before in-process source elaboration, covering the default solver
only while source leaves that option unset. A source setting it, including resetting it to empty,
selects its own program and remains uncovered (issue 411, after issue 279's observer). Sources:
`Lean/Meta/Tactic/BVDecide/TacticContext.lean:55-66`, `External.lean:98-122`. -/
def libraryStarts : List (Name × Name) :=
  [(`Lean.Meta.Tactic.BVDecide.External.runInterruptible, ``IO.Process.spawn),
    (`Lake.rawProc, ``IO.Process.output),
    (`Lake.proc, ``IO.Process.output),
    (`Lake.captureProc?, ``IO.Process.output),
    (`Lake.captureProc', ``IO.Process.output),
    (`Lake.compileLeanModule, ``IO.Process.output),
    (mkPrivateNameCore `Lake.Config.InstallPath `Lake.LeanInstall.get.getGithash, ``IO.Process.output),
    (mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateToolchain ++ `_at_ ++
      mkPrivateNameCore `Lake.Load.Resolve `Lake.Workspace.updateAndMaterializeCore ++ `spec_7,
      ``IO.Process.spawn),
    (`Lake.testProc, ``IO.Process.spawn)]

/-- Verso's renderer fetches remote cross-reference data with its fixed curl command. This is a
trusted library download mechanism, not a checked toolchain selection. Regula's renderers enter
through `Verso.Genre.Manual.manualMain`; their own audit code never calls this private fetcher.
Assumes: pinned Verso cad4b633e75ea769b851f12f9ca3b4f0dfcc625f
`src/multi-verso/MultiVerso.lean:398-408` fixes the program to curl and varies its URL and working
directory; `:580-674` selects remote sources from Verso's configuration.
`src/verso-manual/VersoManual.lean:750`, `:839` and `:1049-1075` connect rendering to that mechanism.
The imported library and its download behavior remain trusted. -/
def rendererStarts : List (Name × Name) :=
  [(mkPrivateNameCore `MultiVerso `Verso.Multi.fetchRemote, ``IO.Process.output)]

/-- Narrow environment exemptions used by the renderer's own libraries. They admit no arbitrary
environment key or tool selection. Their callers are also entrypoints in the same boundary row,
so a Regula call of one is refused before it can borrow the primitive exemption.
Assumes: Lean v4.34.1 `Std/Time/Zoned/Database/TZdb.lean:123-139` and `:153-158` read only TZ and
TZDIR to resolve timezone files. Pinned Verso cad4b633e75ea769b851f12f9ca3b4f0dfcc625f
`src/multi-verso/MultiVerso.lean:384-396` reads the current directory to find the project;
`:580-581` enters that search from its own `updateRemotes`. The imported library's filesystem
observations and configuration remain trusted. -/
def rendererEnvironment : List (Name × Name) :=
  [(`Std.Time.Database.TZdb.resolveLocalPath, ``IO.getEnv),
    (`Std.Time.Database.TZdb.resolveZonesPaths, ``IO.getEnv),
    (mkPrivateNameCore `MultiVerso `Verso.Multi.findProject, ``IO.currentDir)]

/-- Every launcher whose raw primitive pair is exempted is also an entrypoint boundary,
derived from that same source inventory. Additional exported forwarding APIs accept the same
unchecked native program argument. Project calls stop here instead of borrowing a library's
internal exemption. Assumes: Lean v4.34.1 `Lake/Util/Proc.lean:29-91`,
`Lake/Build/Actions.lean:29-170`, `Lean/Meta/Tactic/BVDecide/External.lean:147-166` and
`LRAT/Cert.lean:98-111` define these launchers. Imported Lean and Lake callers retain their
sourced library mechanisms; toolchain origin and deliberate private access remain trusted. -/
def libraryLaunchers : List Name :=
  (libraryStarts ++ rendererStarts).map Prod.fst ++
    [``Lake.captureProc, ``Lake.compileO, ``Lake.compileStaticLib, ``Lake.compileSharedLib,
      ``Lake.compileExe, ``Lean.Meta.Tactic.BVDecide.External.satQuery,
      ``Lean.Meta.Tactic.BVDecide.runExternal]

/-- The single primitive table: filesystem replacement, process starts and environment reads.
A wrapper around output or run is controlled at that operation, while an extern alias is
controlled by its runtime binding. Other systems have no entries yet. -/
def boundaries : List Boundary :=
  [⟨.filesystem, primitives, removalSymbols, observerModule, libraryRemovals, [], [], []⟩,
    ⟨.process, [``IO.Process.spawn, ``IO.Process.output, ``IO.Process.run],
      ["lean_io_process_spawn"], `Regula.Process, libraryStarts ++ rendererStarts, libraryLaunchers,
      [`Lean, `Lake, `MultiVerso], []⟩,
    ⟨.environment, [``IO.getEnv, ``IO.currentDir, ``IO.Process.getCurrentDir, ``IO.appPath, ``IO.Process.setCurrentDir],
      ["lean_io_getenv", "lean_io_current_dir", "lean_io_process_get_current_dir", "lean_io_app_path", "lean_io_process_set_current_dir"],
      `Regula.Process, rendererEnvironment, rendererEnvironment.map Prod.fst, [`Std, `MultiVerso],
      [`Init, `Lean, `Lake]⟩]

/-- The cold-start source's native boundaries, instantiated for the driver module and namespace.
Each driver elaborates the same `ProcessSource.inc`, uses its typed selection and override
decision, and imports no package artifact. These are named bootstrap exemptions, not a second
process policy. Their compiler identity reports, Elan resolution and process effects stay trusted. -/
def bootstrap (scope : Name) : List (Name × Name) :=
  [(scope ++ `identified, ``IO.Process.output),
    (scope ++ `spawn, ``IO.Process.spawn),
    (scope ++ `output, ``IO.Process.output),
    (scope ++ `readEnv, ``IO.getEnv),
    (scope ++ `currentDir, ``IO.currentDir),
    (scope ++ `appPath, ``IO.appPath),
    (scope ++ `setCurrentDir, ``IO.Process.setCurrentDir)]

/-- Whether an extern binds a runtime symbol of this system's boundary. -/
def boundPrimitive (env : Environment) (boundary : Boundary) (name : Name) : Option String :=
  match findEnvDecl env name with
  | some (.extern _ _ _ data) =>
    boundary.symbols.find? fun symbol => data.entries.any (bindsTo symbol)
  | _ => none

/-- Index the named primitives and their authenticated compiled variants from the same table.
No second primitive list or admission rule is written here. -/
def primitiveIndex (env : Environment) : Std.HashMap Name Boundary := Id.run do
  let mut index := {}
  for boundary in boundaries do
    for primitive in boundary.primitives ++ boundary.entrypoints do
      for suffix in compilerSuffixes do
        let variant := primitive ++ suffix
        if observerVariant env #[primitive] variant then index := index.insert variant boundary
  return index

/-- The boundary of a primitive or an extern alias. The compiled declaration is read once, and
the runtime symbol is compared against the same per-system table. -/
def boundaryOf (env : Environment) (index : Std.HashMap Name Boundary) (name : Name) : Option Boundary :=
  if let some boundary := index[name]? then some boundary
  else match findEnvDecl env name with
    | some (.extern _ _ _ data) => boundaries.find? fun boundary =>
      boundary.symbols.any fun symbol => data.entries.any (bindsTo symbol)
    | _ => none

/-- Whether this caller comes from an imported module under a stated library root. The local
module never gets a library exemption, even when its name has such a root. The environment row
trusts Init, Lean and Lake observations, including their search-path and environment decoders.
Assumes: the imported modules at the table's stated roots are the toolchain's modules; the
installed toolchain and import mechanism are trusted. Sources: Lean v4.34.1
`Lean/Util/Path.lean:85-144`, `Lake/Config/Env.lean`, `Lake/Config/InstallPath.lean`. -/
def libraryCaller (env : Environment) (roots : List Name) (caller : Name) : Bool :=
  match env.getModuleIdxFor? caller with
  | some index => roots.contains env.header.moduleNames[index.toNat]!.getRoot
  | none => false

/-- The one admission decision for a caller and primitive, parameterized by its system's row.
A named bootstrap exemption and a library pair admit that whole caller/primitive pair. -/
def admitted (env : Environment) (boundary : Boundary) (observers : Array Name)
    (named : List (Name × Name)) (caller primitive : Name) : Bool :=
  observerVariant env observers caller || (boundary.library ++ named).any (fun (source, operation) =>
    observerVariant env #[source] caller && observerVariant env #[operation] primitive) ||
    (libraryCaller env boundary.entrypointCallers caller &&
      observerVariant env boundary.entrypoints.toArray primitive) ||
    libraryCaller env boundary.libraryCallers caller

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

/-- A raw call retains its system with the caller and primitive by construction. -/
structure Call where
  /-- The system whose observer was bypassed. -/
  system : RegulaPolicy.External.System
  /-- The declaration that called the primitive. -/
  caller : Name
  /-- The primitive or runtime binding reached. -/
  primitive : Name

/-- What the compiled code of a set of roots reaches. -/
structure Reach where
  /-- Every primitive call the check refuses, with its system. -/
  calls : Array Call
  /-- Each reached declaration whose compiled code the environment does not hold. -/
  unknown : Array Name
  /-- Each observer role outside the module named by its system's row. -/
  foreign : Array (RegulaPolicy.External.System × Name) := #[]

/-- The caller/primitive projection retained for the filesystem controls. -/
def Reach.raw (reach : Reach) : Array (Name × Name) :=
  reach.calls.map fun call => (call.caller, call.primitive)

/-- Every primitive call reached from `roots` and refused by the single per-system decision,
plus missing compiled bodies. Runtime-bound aliases use the same table as named primitives.
The filesystem observers parameter retains the existing control API; other rows obtain their
observers from the same role mechanism. Native C bodies are not followed. -/
def rawRemovalsFrom (env : Environment) (observers : Array Name) (roots : Array Name)
    (named : List (Name × Name) := []) : Reach :=
  Id.run do
  let index := primitiveIndex env
  let mut classified : Std.HashMap Name (Option Boundary) := {}
  let own := boundaries.foldl (fun own boundary =>
    own.insert boundary.system (if boundary.system == .filesystem then observers
      else (observerRoles env boundary.system boundary.observer).1))
    ({} : Std.HashMap RegulaPolicy.External.System (Array Name))
  let mut seen : Std.HashSet Name := {}
  for root in roots do seen := seen.insert root
  let mut work := roots
  let mut calls := #[]
  let mut unknown := #[]
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
        let boundary := match classified[used]? with
          | some boundary => boundary
          | none => boundaryOf env index used
        classified := classified.insert used boundary
        if let some boundary := boundary then
          unless admitted env boundary (own[boundary.system]?.getD #[]) named name used do
            calls := calls.push ⟨boundary.system, name, used⟩
        else if !seen.contains used then
          seen := seen.insert used
          work := work.push used
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) then unknown := unknown.push name
      for boundary in boundaries do
        if let some symbol := boundPrimitive env boundary name then
          calls := calls.push ⟨boundary.system, name, Name.mkSimple symbol⟩
    | none => unknown := unknown.push name
  return { calls, unknown := unknown ++ work }

/-- `rawRemovalsFrom` for a program whose `main` is `main` in the module `root`: from `main` and
from each initializer of the modules that it links (`linked`, `initializersOf`). Each row supplies
its own observers and sourced exemptions; `named` supplies the cold driver's explicit pairs.
Roles outside each row's boundary module are retained as foreign declarations. -/
def rawRemovals (env : Environment) (root : Name) (named : List (Name × Name) := []) : Reach :=
  let roots := (initializersOf env (linked env root)).push `main
  { rawRemovalsFrom env (filesystemObservers env) roots named with
    foreign := boundaries.foldl (fun found boundary =>
      found ++ ((observerRoles env boundary.system boundary.observer).2.map
        fun name => (boundary.system, name))) #[] }

/-- The prefix of the marker that `checkProgram` adds for each program that it checked: the
definition `reached ++ root` of type `Unit`, where `root` is the program's root module. `lake exe
qualify observers` reads the markers from the module data of the package's modules. -/
def reached : Name := `Regula.Removal.reached

/-- Why the check refuses the program whose root module is `root`, by what its compiled code
reaches (`rawRemovals`): an unadmitted primitive call, missing compiled code, or an observer role
outside its system's boundary module; `none` when there is none of them. -/
def programRefusal (root : Name) (reach : Reach) : Option String :=
  if !reach.raw.isEmpty then
    some s!"the program of {root} acts without its observer: \
      {reach.calls.toList.map fun call =>
        s!"{call.system.spelling}: {call.caller} calls {call.primitive}"}"
  else if !reach.unknown.isEmpty then
    some s!"the program of {root} reaches declarations whose compiled code is not available, so \
      their primitive effects are unknown: {reach.unknown.toList}"
  else if !reach.foreign.isEmpty then
    some s!"an observer's role is given outside its boundary module: \
      {reach.foreign.toList.map fun (system, name) => s!"{system.spelling}: {name}"}"
  else none

/-- Check the program whose `main` the environment declares: fail with the refusal of the
program (`programRefusal`) when there is one, and otherwise record the program (`reached`).
`named` admits the explicit bootstrap pairs of a program that cannot import its observers,
each as its caller and the primitive that it calls (`admitted`). -/
def checkProgram (named : List (Name × Name) := []) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  unless env.contains `main do
    throwError "no `main` is declared here, so there is no program to check"
  let root := moduleOf env `main
  if let some refused := programRefusal root (rawRemovals env root named) then throwError refused
  Elab.Command.liftCoreM <| addDecl (.defnDecl {
    name := reached ++ root, levelParams := [], type := mkConst ``Unit,
    value := mkConst ``Unit.unit, hints := .abbrev, safety := .safe })

end Regula.Removal
