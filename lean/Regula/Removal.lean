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
`Regula.Process`. A role elsewhere admits nothing. The filesystem observer's removals and its move
are private to `Regula.Filesystem`. Its exported operations `removeOwn`, `removeFound`, `replace`
and `withOwnTempDir` observe the place and act only on what the decisions of `RegulaCore.Removal`
decide. `moveAside` moves an entry into a directory that it makes new, so it replaces and removes
nothing, with no `ownPath` resolution and no `Regula.Removal.replacement` decision: a symbolic link
or a `..` among the components above the entry is followed as the operating system resolves it, as
a run of Verso writes through it too. Sourced filesystem library pairs, listed public library
entries, the startup pairs of the toolchain's initializers and explicitly named bootstrap pairs are
trusted exemptions. A library's process start or environment read on any other path is refused,
whoever owns the module that makes it. The cold drivers elaborate the same process source as the
compiled observer, with no second policy.

`checkProgram` refuses a program at build time and records every accepted program under `reached`.
The existing `qualify observers` campaign checks those records for each executable and standalone
source driver, and checks the executable root outside the package's libraries itself. It remains
in self-audit shard 4/4.

## Limits

This is the honest-code boundary of `SECURITY.md` and `CONTEXT.md`: deliberate compiler or
environment mutation, private-declaration access and arbitrary trusted plugins remain outside it.
Each named pair admits its whole caller/primitive pair, including a second call of that primitive
inside the same caller. A listed entry admits its row's primitives on every path below its call.
Issue 389 owns the drivers' filesystem decisions. Lake's source configuration, builds and dependent
programs remain trusted library behavior.

Assumes: this check guards Regula's own executables built from its committed lakefile and
lake-manifest.json. The build configuration, package selection, module naming and artifact loading
are trusted input, not an adversarial authentication claim. Lean v4.34.1 ModuleData stores no
compiled-as module name (Lean/Environment.lean:109-129); imports record the requested name
(:2225-2228) and the environment flattens artifact regions (:2371). Renamed or substituted
artifacts are outside this boundary. Exempted external dependencies must retain the committed
manifest selection; the renderer refuses override selectors before Lake resolves them.

The runtime's C bodies and child programs are not followed. The table identifies the runtime
symbols of the pinned Lean and of its libuv bindings in `Std` at the Lean boundary, each with its
source (`removalSymbols`, `environmentSymbols`). A new native binding outside that table needs a
sourced entry before this check can say anything about its effects. -/

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
on the workspace it was given. Regula's shared constructor refuses source links and special entries
and creates only directories and regular files (`Regula.Filesystem.observer_copy`,
`observer_construct`, under their native primitive hypotheses). It places no packages link: an
ordinary load uses a retained manifest and typed dependency path overrides. Thus this exemption
no longer needs a limit for links preserved or placed by Regula's copies. Dependency originals,
Lake-generated entries and deliberately planted diagnostic aliases remain trusted inputs. The
provisioning registration link in the original integration workspace is separate from constructing
a copy. `RegulaProvision.installLinkWith` makes it in a directory that `mkdir` creates, which
refuses an entry already at its place (`RegulaProvision.installLink_refused`).

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
  /-- Sourced library exemptions admitted on every path, each a caller and primitive pair. -/
  library : List (Name × Name) := []
  /-- Imported module roots of the callers of `library`. Module naming and artifact loading are
  trusted build inputs; this is a policy domain, not authentication. -/
  libraryRoots : List Name := []
  /-- Listed public library entries, each a Regula declaration and the library declaration that it
  calls. A path through that call admits this row's primitives below it. -/
  entries : List (Name × Name) := []
  /-- Library caller and primitive pairs admitted only on a path from an initializer of a module of
  the toolchain (`toolchainRoots`). -/
  startup : List (Name × Name) := []

/-- The private declaration `name` of `Regula.Checker.Workspace`. -/
def workspace (name : Name) : Name :=
  mkPrivateNameCore `Regula.Checker.Workspace (`Regula.Checker.Workspace ++ name)

/-- The workspace loads of Lake that Regula runs in its own process, each with the private
declaration of `Regula.Checker.Workspace` that alone calls it, with a configuration of its
`loadConfig`, computed by `Regula.Process.lakeEnvironment`. Below them Lake starts Git to clone,
fetch and test a dependency's repository, `curl` (or the program that CURL names) and `tar` to
fetch and unpack a release archive, `lean` to compile a module, and Elan to restart in a
dependency's toolchain. It reads CURL and the variables of `Lake.Env`. Trusted exemption: each
acts on the workspace that the caller asked Lake to load, as `lake build` or `lake update` would
there, and rests on its own configuration and dependencies, which its adopter trusts as Lake does.
Regula's load supplies no lakeArgs for the toolchain restart.
Sources: Lean v4.34.1 `Lake/Load/Workspace.lean:31-67`, `Lake/Load/Resolve.lean:369-430` and
`:587-625`, `Lake/Util/Git.lean:95-100`, `Lake/Util/Proc.lean:29-72`, `Lake/Util/Url.lean:105-150`,
`Lake/Build/Actions.lean:29` and `:174-185`. -/
def workspaceEntries : List (Name × Name) :=
  [(workspace `loadWorkspace, `Lake.loadWorkspace),
    (workspace `loadWorkspaceRoot, `Lake.loadWorkspaceRoot),
    (workspace `materializeDeps, `Lake.Workspace.materializeDeps)]

/-- Lake's installation and environment detection, called by `Regula.Process.lakeEnvironment` with
the identity-checked installation (`Regula.Process.lakeSysroot`). Trusted exemption:
`Lake.LeanInstall.get` with `collocated := true` takes the commit from Lake's own build and does
not start the `lean --githash` that its compiled code holds
(`Lake/Config/InstallPath.lean:272-287`).
It reads LEAN_AR, AR, LEAN_CC and CC (`:289-310`), whose values `lakeSysroot` admits first.
`Lake.findElanInstall?` reads ELAN_HOME and ELAN (`:212-225`), and `Lake.Env.compute` reads the
variables of Lake's environment (`Lake/Config/Env.lean:90-215`), as the toolchain's `lake` does. -/
def installationEntries : List (Name × Name) :=
  [(`Regula.Process.lakeEnvironment, `Lake.LeanInstall.get),
    (`Regula.Process.lakeEnvironment, `Lake.findElanInstall?),
    (`Regula.Process.lakeEnvironment, `Lake.Env.compute)]

/-- Lean's search paths and Lake's build runner, each with the Regula declaration that alone calls
it. Trusted exemption, as the `lean` and `lake` commands read the same variables:
`Lean.initSearchPath` at the identity-checked installation reads LEAN_PATH
(`Lean/Util/Path.lean:98-110`). `Lean.getSrcSearchPath` reads LEAN_SRC_PATH and the directory of
the running executable (`:137-143`, `Init/System/IO.lean:1305-1309`). `Lake.Workspace.runBuild`
reads MACOSX_DEPLOYMENT_TARGET on macOS (`Lake/Build/Run.lean:335-349`, `:427-435`). The build
function is its caller's, so the reach check follows it from that caller. -/
def searchPathEntries : List (Name × Name) :=
  [(`Regula.Process.initSearchPath, `Lean.initSearchPath),
    (`Regula.Process.srcSearchPath, `Lean.getSrcSearchPath),
    (`Regula.Checker.Workspace.runBuild, `Lake.Workspace.runBuild)]

/-- Verso's renderer, `manualMain`, each with the declaration of a renderer's root module that alone
calls it. Below it Verso fetches remote cross-reference data with its fixed curl command, reads the
current directory to find the project, and Lean's `Std` reads TZ and TZDIR to resolve timezone
files. Trusted exemption: this is the imported library's download mechanism, not a checked
toolchain selection. The renderer refuses override selectors for Verso before Lake resolves them
(`Regula.ProgramCheck.Renderer.requireCommittedSelection`).
Assumes: pinned Verso cad4b633e75ea769b851f12f9ca3b4f0dfcc625f
`src/multi-verso/MultiVerso.lean:384-408` and `:580-674`, and
`src/verso-manual/VersoManual.lean:750`, `:839` and `:1049-1075`. Lean v4.34.1
`Std/Time/Zoned/Database/TZdb.lean:123-139` and `:153-158`. The imported library, its configuration and its download behavior remain trusted. -/
def rendererEntries : List (Name × Name) :=
  [(`renderSite, `Verso.Genre.Manual.manualMain), (`renderManual, `Verso.Genre.Manual.manualMain)]

/-- The module roots of the toolchain's libraries, whose initializers start a path with the
`startup` pairs of each row. A project module's initializer starts an ordinary path.
Assumes: Regula's committed build configuration selects the toolchain's libraries, and module
naming and artifact loading are trusted. -/
def toolchainRoots : List Name :=
  [`Init, `Lean, `Lake, `Std]

/-- The process start that a path from an initializer of the toolchain reaches: Lean's builtin
`bv_decide`, which the initializer that registers it reaches, starts its SAT solver
(`Lean/Meta/Tactic/BVDecide/External.lean:98-122`). Regula supplies its checked cadical through the
initial `sat.solver` before in-process source elaboration (`Regula.Process.leanOptions`), covering
the default solver only while source leaves that option unset. A source setting it, including
resetting it to empty, selects its own program and remains uncovered (issue 411, after issue 279's
observer). -/
def processStartup : List (Name × Name) :=
  [(`Lean.Meta.Tactic.BVDecide.External.runInterruptible, ``IO.Process.spawn)]

/-- The environment reads that a path from an initializer of the toolchain reaches. The initializer
of `Lean.manualRoot` reads LEAN_MANUAL_ROOT (`Lean/DocString/Links.lean:35-37`). Without a
`sat.solver`, `bv_decide` looks for cadical beside the running executable
(`Lean/Meta/Tactic/BVDecide/TacticContext.lean:55-66`). `Lean.getSrcSearchPath` reads
LEAN_SRC_PATH (`Lean/Util/Path.lean:137-143`), and `IO.appDir`, which it calls to find Lean's
sources, reads the path of the running executable (`Init/System/IO.lean:1305-1309`). -/
def environmentStartup : List (Name × Name) :=
  [(`Lean.manualRoot, ``IO.getEnv),
    (mkPrivateNameCore `Lean.Meta.Tactic.BVDecide.TacticContext
      `Lean.Meta.Tactic.BVDecide.TacticContext.new.determineSolver, ``IO.appPath),
    (`Lean.getSrcSearchPath, ``IO.getEnv),
    (`IO.appDir, ``IO.appPath)]

/-- The runtime symbols of Lean 4.34.1 that read or change the process environment: its variables,
working directory and executable path. Lean binds the first five in `Init/System/IO.lean` (`:951`,
`:955`, `:959`, `:1383` and `:1386`). `Std.Internal.UV.System` binds the others to libuv
(`Std/Internal/UV/System.lean:134-152`, `:170-188` and `:236`). Its only callers are the public
`@[inline]` wrappers of `Std.Async.System` (`Std/Async/System.lean:250-287`) and `Std.IO.Process`
(`Std/Async/Process.lean:156-164` and `:209-210`), so a project call of a wrapper reaches the
binding, inlined or through the wrapper.
Assumes: on POSIX, the toolchain's libuv reads HOME for the home directory and TMPDIR, TMP, TEMP or
TEMPDIR for the temporary directory before any other source, so those two bindings observe
variables. The C bodies are not followed: a variable that a different runtime function reads in C
is outside this list. -/
def environmentSymbols : List String :=
  ["lean_io_getenv", "lean_io_current_dir", "lean_io_process_get_current_dir", "lean_io_app_path",
    "lean_io_process_set_current_dir", "lean_uv_cwd", "lean_uv_chdir", "lean_uv_os_homedir",
    "lean_uv_os_tmpdir", "lean_uv_os_environ", "lean_uv_os_getenv", "lean_uv_os_setenv",
    "lean_uv_os_unsetenv", "lean_uv_exepath"]

/-- The single primitive table: filesystem replacement, process starts and environment
observations. A wrapper around output or run is controlled at that operation, while an extern
alias is controlled by its runtime binding, as are `Std`'s libuv environment bindings and their
public wrappers. A library's own process start or environment read is admitted only below a listed
entry or on a path from the toolchain's initializers. Other systems have no entries yet. -/
def boundaries : List Boundary :=
  [{ system := .filesystem, primitives, symbols := removalSymbols, observer := observerModule,
      library := libraryRemovals, libraryRoots := [`Lean, `Lake] },
    { system := .process, primitives := [``IO.Process.spawn, ``IO.Process.output, ``IO.Process.run],
      symbols := ["lean_io_process_spawn"], observer := `Regula.Process,
      entries := workspaceEntries ++ installationEntries ++ rendererEntries,
      startup := processStartup },
    { system := .environment,
      primitives := [``IO.getEnv, ``IO.currentDir, ``IO.Process.getCurrentDir, ``IO.appPath,
        ``IO.Process.setCurrentDir],
      symbols := environmentSymbols, observer := `Regula.Process,
      entries := workspaceEntries ++ installationEntries ++ searchPathEntries ++ rendererEntries,
      startup := environmentStartup }]

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
    for primitive in boundary.primitives do
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

/-- Whether an imported caller belongs to one of the module roots `roots`.
Assumes: Regula's committed build configuration selects the stated libraries, and module naming
and artifact loading are trusted. Lean v4.34.1 Environment.lean:2225-2228 records the requested
import name, not a certified compiled-as name. This predicate does not authenticate artifacts. -/
def libraryCaller (env : Environment) (roots : List Name) (caller : Name) : Bool :=
  match env.getModuleIdxFor? caller with
  | some index => roots.contains env.header.moduleNames[index.toNat]!.getRoot
  | none => false

/-- Whether the call of `callee` by `caller` is one of `pairs`, each up to the compiled variants of
its two declarations. A first component that has an initializer stands for that initializer. -/
def listed (env : Environment) (pairs : List (Name × Name)) (caller callee : Name) : Bool :=
  pairs.any fun (source, target) =>
    observerVariant env #[(getInitFnNameFor? env source).getD source] caller &&
      observerVariant env #[target] callee

/-- What a path from a root has entered: the systems whose listed entries it passed through
(`Boundary.entries`), and whether it starts at an initializer of the toolchain
(`toolchainRoots`). -/
structure PathContext where
  /-- The systems of the listed entries on the path. -/
  entered : List RegulaPolicy.External.System := []
  /-- Whether the path starts at an initializer of a module of the toolchain. -/
  startup : Bool := false
  deriving BEq, Hashable

/-- The declaration of which `name` is a compiled specialization: Lean's compiler names the
specialization of `f` that it makes in `g` `f._at_.g.spec_n`, and its variants after that. A name
without `_at_` is none. -/
def specializationOf? : Name → Option Name
  | .anonymous => none
  | .str parent component => (specializationOf? parent).orElse fun _ =>
    if component == "_at_" then some parent else none
  | .num parent _ => specializationOf? parent

/-- Index the listed entries by their library declaration and its compiled variants, each with its
row's system and the Regula declaration that calls it. No second entry list is written here. -/
def entryIndex (env : Environment) :
    Std.HashMap Name (List (RegulaPolicy.External.System × Name)) := Id.run do
  let mut index := {}
  for boundary in boundaries do
    for (source, entry) in boundary.entries do
      for suffix in compilerSuffixes do
        let variant := entry ++ suffix
        if observerVariant env #[entry] variant then
          index := index.insert variant ((boundary.system, source) :: index.getD variant [])
  return index

/-- The context of the call of `callee` by `caller` on a path in `context`: each row that lists the
call as an entry (`entryIndex`) adds its system. A compiled specialization of the entry or of its
caller (`specializationOf?`) is that declaration, made for the caller's arguments. -/
def PathContext.enter (env : Environment)
    (index : Std.HashMap Name (List (RegulaPolicy.External.System × Name))) (context : PathContext)
    (caller callee : Name) : PathContext :=
  (index.getD ((specializationOf? callee).getD callee) []).foldl (init := context)
    fun context (system, source) =>
      if !context.entered.contains system &&
          (observerVariant env #[source] caller || specializationOf? caller == some source) then
        { context with entered := context.entered ++ [system] }
      else context

/-- The one admission decision for a caller and primitive on a path in `context`, parameterized by
its system's row: the row's observers, a named bootstrap pair, a path below a listed entry of the
row, a startup pair on a path from the toolchain's initializers, or a sourced library pair. -/
def admitted (env : Environment) (boundary : Boundary) (observers : Array Name)
    (named : List (Name × Name)) (context : PathContext) (caller primitive : Name) : Bool :=
  observerVariant env observers caller || listed env named caller primitive ||
    context.entered.contains boundary.system ||
    (context.startup && listed env boundary.startup caller primitive) ||
    (libraryCaller env boundary.libraryRoots caller && listed env boundary.library caller primitive)

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

/-- The initializers `initializers`, split into those of the toolchain's modules (`toolchainRoots`),
which start paths with the rows' `startup` pairs, and the others, which start ordinary paths. -/
def splitInitializers (env : Environment) (initializers : Array Name) : Array Name × Array Name :=
  initializers.partition (libraryCaller env toolchainRoots)

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

/-- Every primitive call reached from `roots`, and from `startup` on paths from the toolchain's
initializers, and refused by the single per-system decision, plus missing compiled bodies. A
declaration is followed once in each context in which a path reaches it (`PathContext`), so a call
of a listed entry by another caller admits nothing below it. A constant with an initializer is not
followed where it is referenced: the reference reads the value that its initializer, a root of the
program, stored when the program started. Runtime-bound aliases use the same table as named
primitives. The filesystem observers parameter retains the existing control API; other rows obtain
their observers from the same role mechanism. Native C bodies are not followed. -/
def rawRemovalsFrom (env : Environment) (observers : Array Name) (roots : Array Name)
    (named : List (Name × Name) := []) (startup : Array Name := #[]) : Reach :=
  Id.run do
  let index := primitiveIndex env
  let entries := entryIndex env
  let mut classified : Std.HashMap Name (Option Boundary) := {}
  let own := boundaries.foldl (fun own boundary =>
    own.insert boundary.system (if boundary.system == .filesystem then observers
      else (observerRoles env boundary.system boundary.observer).1))
    ({} : Std.HashMap RegulaPolicy.External.System (Array Name))
  let mut work := roots.map ((·, ({} : PathContext))) ++ startup.map ((·, { startup := true }))
  let mut seen : Std.HashSet (Name × PathContext) := work.foldl (·.insert ·) {}
  let mut calls := #[]
  let mut unknown := #[]
  -- Each declaration is added to `work` at most once in each context. The bound is far above the
  -- number of compiled declarations that a program of this toolchain reaches (about 200,000) in its
  -- few contexts; a declaration left in `work` at the bound is unknown, so the check fails closed.
  for _ in [:maxDeclarations] do
    let some (name, context) := work.back? | break
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
          unless admitted env boundary (own[boundary.system]?.getD #[]) named context name used ||
              calls.any (fun call => call.caller == name && call.primitive == used) do
            calls := calls.push ⟨boundary.system, name, used⟩
        else if (getInitFnNameFor? env used).isNone then
          let next := (used, context.enter env entries name used)
          unless seen.contains next do
            seen := seen.insert next
            work := work.push next
    | some (.extern _ _ _ data) =>
      if data.entries.any (· matches .opaque) && !unknown.contains name then
        unknown := unknown.push name
      for boundary in boundaries do
        if let some symbol := boundPrimitive env boundary name then
          let primitive := Name.mkSimple symbol
          unless calls.any (fun call => call.caller == name && call.primitive == primitive) do
            calls := calls.push ⟨boundary.system, name, primitive⟩
    | none => unless unknown.contains name do unknown := unknown.push name
  return { calls, unknown := unknown ++ work.map (·.1) }

/-- `rawRemovalsFrom` for a program whose `main` is `main` in the module `root`: from `main` and
from each initializer of the modules that it links (`linked`, `initializersOf`), split by
`splitInitializers`. Each row supplies its own observers and sourced exemptions; `named` supplies
the cold driver's explicit pairs. Roles outside each row's boundary module are retained as foreign
declarations. -/
def rawRemovals (env : Environment) (root : Name) (named : List (Name × Name) := []) : Reach :=
  let (startup, roots) := splitInitializers env (initializersOf env (linked env root))
  { rawRemovalsFrom env (filesystemObservers env) (roots.push `main) named startup with
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
each as its caller and the primitive that it calls (`admitted`).
Assumes: Regula's own executables use its committed lakefile/manifest, with trusted package
selection, module naming and artifact loading. Lean v4.34.1 Environment.lean:109-129,2225-2228
stores requested import names without certified compiled-as identities. The renderer refuses
override selection for its exempted dependency; malicious build inputs are outside this check. -/
def checkProgram (named : List (Name × Name) := []) : Elab.Command.CommandElabM Unit :=
  withExporting (isExporting := false) do
    let env ← getEnv
    unless env.contains `main do
      throwError "no `main` is declared here, so there is no program to check"
    let root := moduleOf env `main
    if let some refused := programRefusal root (rawRemovals env root named) then throwError refused
    Elab.Command.liftCoreM <| addDecl (.defnDecl {
      name := reached ++ root, levelParams := [], type := mkConst ``Unit,
      value := mkConst ``Unit.unit, hints := .abbrev, safety := .safe })

end Regula.Removal
