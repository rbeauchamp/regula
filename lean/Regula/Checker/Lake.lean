import Regula.Checker.Common
import Regula.Checker.Manifest
import Regula.Checker.Workspace
import RegulaCore.EditorPolicy
import Lake.CLI.Build

/-! # Lake-semantic discovery

Lake-semantic module, source, dependency, and build discovery. -/

namespace Regula.Checker.Lake

open Lean System
open Regula.Checker

/-- The root package facts the audit checks module origins against: its Lean library names and
the directory its compiled modules are written to. -/
structure RootInventory where
  /-- The names of the root package's Lean libraries. -/
  libraries : Array String
  /-- The root package's compiled-module output directory (Lake's `leanLibDir`); a module
  whose `.olean` lies below it is root-package output. -/
  leanLibDir : FilePath
  deriving Repr, BEq

/-- The root package's source-bound modules with the exact source Lake resolves for each: every
module of its libraries and its executable roots. The audit binds these sources, and replays a
root-package module wherever an environment loads it. An owned dependency's sources stay with its
package (`DependencyInventory.sources`), since two packages can give one module name different
sources; a project audit binds those that each environment loads
(`Environment.dependencyBindings`). Reuse them for frontend history instead of a module-prefix
search. -/
def SurfaceInventory.moduleSources (inventory : SurfaceInventory) : Array (Name × FilePath) :=
  inventory.libraries.flatMap (fun library => library.sources.map fun source =>
    (source.«module», source.source)) ++
    inventory.executables.map (fun executable => (executable.root, executable.source))

/-- What the audit owns beyond the requested modules: the compiled-module output directories of
the owned packages (the root package's, then each owned dependency's), the root package and the
owned dependencies with the modules each provides by its own module resolution
(`TargetInventory.modules`) and, in a copy, the copy's directory. A module loaded from below one of
those directories is the project's own output, so an environment that loads such a module without
owning it is refused (`unownedModules`); a loaded module is attributed to an owned package only
when its `.olean` is exactly that package's artifact of it (`Environment.attributeLoaded`); and in
a copy an owned module that resolves elsewhere is refused (`outsideCopy`). -/
def SurfaceInventory.ownership (inventory : SurfaceInventory) : Ownership :=
  let owned := inventory.dependencies.filter (·.owned)
  let provided (targets : Array TargetInventory) : Array Name :=
    (targets.flatMap (·.modules)).foldl (fun names name =>
      if names.contains name then names else names.push name) #[]
  { outputs := #[inventory.leanLibDir] ++ owned.map (·.leanLibDir)
    root := some { package := inventory.package, output := inventory.leanLibDir
                   modules := provided inventory.targets }
    dependencies := owned.map fun dependency =>
      { package := dependency.package, output := dependency.leanLibDir
        modules := provided dependency.targets }
    copy := inventory.copy }

/-- The directory of the running checker's own package: the one whose Lake build holds the
library the running checker loads its infrastructure from (`checkerPackageLibDir`), under Lake's
default layout (`<package>/.lake/build/lib/lean`), on real paths. It is `none` when that library
is not found or does not lie at that place. The checker's own build is Lake's default layout. -/
def checkerPackageDir : IO (Option FilePath) := do
  let some lib ← checkerPackageLibDir | return none
  let lib ← try IO.FS.realPath lib catch _ => return none
  let components := lib.components
  let layout := [_root_.Lake.defaultLakeDir.toString, "build", "lib", "lean"]
  unless layout.isSuffixOf components do return none
  return some (System.mkFilePath (components.take (components.length - layout.length)))

/-- The source of module `name` in the running checker's own package at `checker`: its libraries
keep their sources below `lean` (`modulePath?`, so `none` for a name that is not safe). -/
def checkerSource (checker : FilePath) (name : Name) : Option FilePath :=
  modulePath? (checker / "lean") name "lean"

/-- The module names that the configuration of `package` gives: the roots and the glob names of
each library and the root of each executable, before any module is resolved or any path is built
from them. A glob keeps its kind: `.submodules` of the anonymous name selects the modules of the
source directory itself and names no module, so it gives no name; `.one` and `.andSubmodules` name
their module, and every other `.submodules` its prefix. -/
def configuredModuleNames (package : _root_.Lake.Package) : Array Name :=
  package.leanLibs.flatMap (fun library => library.roots ++ library.config.globs.filterMap fun
      | .one name | .andSubmodules name => some name
      | .submodules .anonymous => none
      | .submodules name => some name) ++
    package.leanExes.map (·.config.root)

/-- Refuse a module name of package `package` that `modulePath?` cannot place below a directory
(`safeModuleComponents?`): a component that is an absolute path or has an empty, `.` or `..`
segment between path separators, or a numeric component. `Lean.modToFilePath` joins each component with
`FilePath.join`, which discards its base for an absolute component, so such a name could resolve a
checker source or an owned artifact outside the directory it belongs to. -/
def checkModuleNames (package : String) (names : Array Name) : IO Unit := do
  if let some name := unsafeModuleName? names then
    throw <| IO.userError s!"lake-query-malformed: package '{package}' names module {name}, whose \
      name has a component that is an absolute path, has an empty, `.` or `..` segment between path \
      separators, or is a number"

/-- Refuse a workspace that Lake loaded when a package's configuration gives a module name that
`checkModuleNames` refuses: the entry of module names from Lake's load of a workspace, for every
package, which each reader of a workspace passes before it resolves a module or builds a path from
a name (`surfaceInventory`, `LintBuild.markerInputs`, the setup commands and the Verso readers). -/
def checkWorkspaceModuleNames (ws : _root_.Lake.Workspace) : IO Unit :=
  for package in ws.packages do
    checkModuleNames package.baseName.toString (configuredModuleNames package)

/-- Refuse a module that package `package` provides under a prefix reserved to the checker
(`reservedModule`) unless its source `source` holds exactly the text of the running checker's own
source of that module (`checkerSource` of `checker`). `modules` are the package's own library and
executable modules with their sources, as the package's configuration gives them, before Lake
resolves each name to one package of the workspace. A module that the package provides with that
text is compiled from the same text as the checker's own artifact of that name, which the reporter's
overlay loads in its place. -/
def checkReservedModules (checker : Option FilePath) (package : String)
    (modules : Array (Name × FilePath)) : IO Unit := do
  for (name, source) in modules do
    unless reservedModule name do continue
    let refuse {α : Type} (reason : String) : IO α :=
      throw <| IO.userError s!"lake-query-malformed: package '{package}' provides module {name} \
        under a prefix reserved to the checker ({", ".intercalate reservedPrefixes.toList}), \
        {reason}"
    let some checker := checker
      | refuse "and the running checker's own package cannot be located"
    let some own := checkerSource checker name
      | refuse "with a name that is not a safe module name"
    let same ← try
        pure ((← IO.FS.readBinFile source) == (← IO.FS.readBinFile own))
      catch _ => pure false
    unless same do
      refuse s!"with a source {source} that is not the text of the running checker's own source \
        {own}"

/-- Lake's default output directories of a package, by configuration field: `buildDir`,
`leanLibDir`, `nativeLibDir`, `binDir` and `irDir`, with Lake's own default values. -/
def defaultOutputDirectories : Array (String × FilePath) :=
  #[("buildDir", _root_.Lake.defaultBuildDir), ("leanLibDir", _root_.Lake.defaultLeanLibDir),
    ("nativeLibDir", _root_.Lake.defaultNativeLibDir), ("binDir", _root_.Lake.defaultBinDir),
    ("irDir", _root_.Lake.defaultIrDir)]

/-- The output directories of a package as its loaded configuration sets them, in the fields and
order of `defaultOutputDirectories`, with no path resolved. -/
def packageOutputDirectories (package : _root_.Lake.Package) : Array (String × FilePath) :=
  #[("buildDir", package.config.buildDir), ("leanLibDir", package.config.leanLibDir),
    ("nativeLibDir", package.config.nativeLibDir), ("binDir", package.config.binDir),
    ("irDir", package.config.irDir)]

private def checkSource (repo : FilePath) (what : String)
    (moduleName sourceRaw : String) : IO FilePath := do
  let source := FilePath.mk sourceRaw
  let mut invalidSource := moduleName.isEmpty || sourceRaw.isEmpty
    || source.extension != some "lean" || !(← source.pathExists)
  if !invalidSource then
    invalidSource := !(← pathWithin source repo)
  if invalidSource then
    throw <| IO.userError s!"lake-query-malformed: {what} has invalid source"
  return ← IO.FS.realPath source

/-- The options Lake builds a target's modules with, exactly as Lake resolves them for the
target (`leanOptions`: build type, package, then target), and the extra `lean` arguments it
passes (`weakLeanArgs`, then `leanArgs`, the order of Lake's module build). -/
def buildOptions (options : Lean.LeanOptions) (weakArgs args : Array String) :
    RegulaPolicy.Community.BuildOptions where
  options := options.values.toList.map fun (name, value) => (name, match value with
    | .ofString s => .string s | .ofBool b => .bool b | .ofNat n => .nat n)
  arguments := (weakArgs ++ args).toList

/-- The options and extra `lean` arguments Lake builds the modules of library `lib` with. -/
def libraryOptions (lib : _root_.Lake.LeanLib) : RegulaPolicy.Community.BuildOptions :=
  buildOptions lib.leanOptions lib.weakLeanArgs lib.leanArgs

/-- The options and extra `lean` arguments Lake builds the root of executable `exe` with. -/
def executableOptions (exe : _root_.Lake.LeanExe) : RegulaPolicy.Community.BuildOptions :=
  buildOptions exe.root.leanOptions exe.root.weakLeanArgs exe.root.leanArgs

/-- The modules Lake can build as part of `library`, found in its source directory with Lake's
glob reader: those its globs match, and the submodules of each root that a glob matches, which
is the set `LeanLibConfig.isBuildableModule` admits among the module files. A module may occur
twice. -/
def buildableModules (library : _root_.Lake.LeanLib) : IO (Array Name) := do
  let names ← IO.mkRef (#[] : Array Name)
  let mut globs := library.config.globs
  for root in library.roots do
    if library.config.globs.any (·.matches root) &&
        (← (Lean.modToFilePath library.srcDir root "").isDir) then
      globs := globs.push (.submodules root)
  for glob in globs do
    glob.forEachModuleIn library.srcDir fun name => names.modify (·.push name)
  names.get

/-- Each library and executable of `package`, with the modules it provides by the package's own
module resolution (`buildableModules`, each once in `Name.quickLt` order, and an executable's
root) and the options it builds them with (`libraryOptions`, `executableOptions`); and each of
those modules with its source path as the package's configuration gives it, before Lake resolves
each name to one package of the workspace. `checkOneProvider` counts a library's modules of each
package, and an executable's root only of the root package and an owned dependency.
-/
def packageModules (package : _root_.Lake.Package) :
    IO (Array TargetInventory × Array (Name × FilePath)) := do
  let mut targets : Array TargetInventory := #[]
  let mut sources : Array (Name × FilePath) := #[]
  for library in package.leanLibs do
    let modules := ((← buildableModules library).foldl NameSet.insert {}).toArray.qsort Name.quickLt
    targets := targets.push
      { target := s!"lean_lib {library.name}", modules, options := libraryOptions library }
    for name in modules do
      let some source := modulePath? library.srcDir name "lean"
        | throw <| IO.userError s!"lake-query-malformed: package '{package.baseName}' provides \
            module {name}, whose name is not a safe module name"
      sources := sources.push (name, source)
  for exe in package.leanExes do
    targets := targets.push
      { target := s!"lean_exe {exe.name}", modules := #[exe.root.name]
        options := executableOptions exe }
    let some source := modulePath? exe.root.lib.srcDir exe.root.name "lean"
      | throw <| IO.userError s!"lake-query-malformed: package '{package.baseName}' roots executable \
          {exe.name} at {exe.root.name}, which is not a safe module name"
    sources := sources.push (exe.root.name, source)
  return (targets, sources)

/-- Refuse a module name that more than one package of the workspace provides by its own module
resolution (`TargetInventory.modules`) when one of those packages is the root package or an owned
dependency, counting each package's library modules and the executable roots of the root package
and of each owned dependency. `packages` gives each package's name, whether the audit owns it, and
its targets, the root package first. An audit supports one provider for each name that an owned
package provides: Lake refuses an import of a name with two providers only when it finds their
definitions distinct, and which one's artifact an environment loads otherwise follows the search
path, not the package. Two trusted packages may provide one name, since the audit attributes and
owns no module of a trusted package. A trusted package's executable roots are not counted: Lake
resolves an import only to a library module (`Lake.Package.findModule?`), and a loaded module that
an owned package provides is attributed only to that package's own artifact
(`Environment.attributeLoaded`). -/
def checkOneProvider (packages : Array (String × Bool × Array TargetInventory)) : IO Unit := do
  let mut providers : Std.HashMap Name (String × Bool) := {}
  for (package, owned, targets) in packages do
    for target in targets do
      unless owned || target.target.startsWith "lean_lib " do continue
      for name in target.modules do
        match providers[name]? with
        | some (other, otherOwned) =>
          if other != package && (owned || otherOwned) then
            throw <| IO.userError s!"lake-query-malformed: module {name} is provided by package \
              '{other}' and by package '{package}'; an audit supports one provider for each \
              module name of the root package and of each owned dependency"
        | none => providers := providers.insert name (package, owned)

/-- Refuse the root package or an owned dependency of the inventory whose loaded configuration sets
an output directory other than Lake's default (`defaultOutputDirectories`), compared by value with
no path resolved. Every audit decides this from Lake's load of the workspace (`surfaceInventory`),
incremental or fresh, before it builds the project or a copy, and the `lake lint` driver before it
builds its audit worker (`Lint.lint`); Lake's build of the program that runs the audit, of the
checker's own package, comes first. An owned package's compiled modules are then exactly at
`.lake/build/lib/lean` below its directory, where each loaded artifact is attributed
(`Environment.attributeLoaded`), and no build of a copy reads or writes a directory that its
configuration puts elsewhere. -/
def checkDefaultLayout (inventory : SurfaceInventory) : IO Unit := do
  let packages := #[(inventory.package, inventory.outputDirectories)] ++
    (inventory.dependencies.filter (·.owned)).map fun dependency =>
      (dependency.package, dependency.outputDirectories)
  for (package, directories) in packages do
    for (field, value) in directories do
      unless defaultOutputDirectories.contains (field, value) do
        throw <| IO.userError s!"lake-workspace-load-failed: an audit requires Lake's default \
          output layout of the root package and each owned dependency, but package \
          '{package}' sets {field} = {value}"

/-- Obtain every root-package Lean library and executable, exact module, and
exact source from Lake's own elaborated package model. This loads the checked
project's workspace in-process, so `lakefile.lean` and `lakefile.toml`
projects share one discovery path and need no custom Lake facets. This is the inventory of the
loaded workspace `ws` of the project at `repo`. -/
def surfaceInventoryOf (repo : FilePath) (ws : _root_.Lake.Workspace) : IO SurfaceInventory := do
    let pkg := ws.root
    -- No path is built from a module name before each name that a package's configuration gives is
    -- a safe module name (`checkModuleNames`); a resolved module is placed by `modulePath?`.
    checkWorkspaceModuleNames ws
    -- Modules under the checker's reserved prefixes must hold the running checker's own source
    -- text, whatever package provides them (`checkReservedModules`).
    let checker ← checkerPackageDir
    let leanLibDir := pkg.leanLibDir
    if leanLibDir.toString.isEmpty then
      throw <| IO.userError "lake-query-malformed: root leanLibDir is empty"
    let mut libraries : Array LibraryInventory := #[]
    for lib in pkg.leanLibs do
      -- The recorded spelling a manifest's library names are compared with (`recordedName`).
      let library := Manifest.targetSpelling lib.name
      let libModules ← lib.getModuleArray
      let modules := libModules.map (·.name)
      let mut sources : Array SourceEntry := #[]
      for libModule in libModules do
        let moduleName := libModule.name
        let source ← checkSource repo s!"{library} module {moduleName}"
          moduleName.toString libModule.leanFile.toString
        sources := sources.push { «module» := moduleName, source }
      if library.isEmpty || modules.isEmpty || libraries.any (·.library == library)
          || modules.toList.eraseDups.length != modules.size then
        throw <| IO.userError s!"lake-query-malformed: invalid library {library}"
      libraries := libraries.push {
        library, modules, sources
        options := libraryOptions lib }
    if libraries.isEmpty then
      throw <| IO.userError "lake-query-malformed: no root Lean libraries"
    let mut executables : Array ExecutableInventory := #[]
    for exe in pkg.leanExes do
      -- The recorded spelling a manifest's executable names are compared with (`recordedName`).
      let executable := Manifest.targetSpelling exe.name
      let root := exe.root.name
      let source ← checkSource repo s!"executable {executable}"
        root.toString exe.root.leanFile.toString
      if executable.isEmpty || root.isAnonymous || executables.any (·.executable == executable)
          || executables.any (·.root == root) then
        throw <| IO.userError s!"lake-query-malformed: invalid executable {executable}"
      executables := executables.push {
        executable, root, source
        options := executableOptions exe }
    -- The root package's own library and executable modules, as each dependency's below.
    let (targets, own) ← packageModules pkg
    checkReservedModules checker pkg.baseName.toString own
    let leanPath := #[leanLibDir] ++ ws.leanPath.toArray
    let leanSrcPath := ws.leanSrcPath.toArray
    -- A dependency is owned when its directory is in the root package's Git work tree.
    let rootTree ← gitWorkTree repo
    let dependencies ← (ws.packages.extract 1 ws.packages.size).mapM fun package => do
      -- The package's own library and executable modules, before Lake resolves each name to one
      -- package of the workspace.
      let (targets, own) ← packageModules package
      checkReservedModules checker package.baseName.toString own
      let names := (targets.filter (·.target.startsWith "lean_lib ")).foldl
        (fun names target => target.modules.foldl NameSet.insert names) ({} : NameSet)
      let mut sources := #[]
      for name in names.toArray.qsort Name.quickLt do
        let some resolved := ws.findModule? name
          | throw <| IO.userError s!"lake-query-malformed: dependency module {name} is unresolved"
        if resolved.pkg.keyName != package.keyName then continue
        let source ← checkSource package.dir s!"dependency module {name}"
          name.toString resolved.leanFile.toString
        sources := sources.push { «module» := name, source }
      for exe in package.leanExes do
        if sources.any (·.module == exe.root.name) then continue
        -- Dependencies may declare unused executables without shipping their
        -- sources. Capture existing roots; terminal rediscovery still detects
        -- their addition/removal. Claimed root-package targets remain required.
        if !(← exe.root.leanFile.pathExists) then continue
        let source ← checkSource package.dir s!"dependency executable {exe.name}"
          exe.root.name.toString exe.root.leanFile.toString
        sources := sources.push { «module» := exe.root.name, source }
      let root ← IO.FS.realPath package.dir
      let configurationPaths := #[package.configFile, package.manifestFile,
        package.dir / "lean-toolchain", package.dir / "lakefile.lean",
            package.dir / "lakefile.toml"]
        |>.toList.eraseDups.toArray
      let owned ← ownedDirectory rootTree root
      if owned && package.leanLibDir.toString.isEmpty then
        throw <| IO.userError s!"lake-query-malformed: {package.baseName} leanLibDir is empty"
      pure
          ({ package := package.baseName.toString, root, sources, configurationPaths, owned
             leanLibDir := package.leanLibDir, scope := package.scope
             configFile := package.relConfigFile, manifestFile := package.relManifestFile
             configuration := ← IO.FS.readFile package.configFile
             outputDirectories := packageOutputDirectories package, targets } :
              DependencyInventory)
    -- One provider for each library module and executable root of an owned package, counting the
    -- library modules of every package, by each package's own resolution.
    checkOneProvider (#[(pkg.baseName.toString, true, targets)] ++
      dependencies.map fun dependency =>
        (dependency.package, dependency.owned, dependency.targets))
    let root ← IO.FS.realPath repo
    let inventory : SurfaceInventory := {
      root, package := pkg.baseName.toString, outputDirectories := packageOutputDirectories pkg
      leanLibDir, leanPath, leanSrcPath, libraries, executables, targets, dependencies }
    -- Every audit, incremental or fresh, requires Lake's default layout of each owned package.
    checkDefaultLayout inventory
    return inventory

/-- The inventory (`surfaceInventoryOf`) of the workspace that Lake loads, with its dependencies, for
the project at `repo`. -/
def surfaceInventory (repo : FilePath) : IO SurfaceInventory :=
  Workspace.withRootWorkspace repo (surfaceInventoryOf repo)

/-- The inventory (`surfaceInventoryOf`) of the root package of the project at `repo`, which must
declare no dependency (`Workspace.withRootPackage`). It is the inventory that `surfaceInventory`
gives for such a project, and no loader that removes a directory is in its compiled code. -/
def rootSurfaceInventory (repo : FilePath) : IO SurfaceInventory :=
  Workspace.withRootPackage repo (surfaceInventoryOf repo)

/-- What Lake's load of a workspace selects for one dependency package: its name, directory and
ownership, the configuration and manifest files it reads, the text of that configuration, the
output directories the configuration sets, each library and executable with the modules it
provides and the Lean options and arguments it builds them with, and the source of each module, by
its path components below the directory. A copy of the project must select the same for each
package, with an owned package's directory relocated into the copy (`checkCopiedWorkspace`). -/
structure PackageSelection where
  /-- The package's name. -/
  package : String
  /-- The package's real directory. -/
  dir : FilePath
  /-- Whether the audit owns the package. -/
  owned : Bool
  /-- The configuration file, relative to `dir`. -/
  configFile : FilePath
  /-- The manifest file, relative to `dir`. -/
  manifestFile : FilePath
  /-- The text of the configuration file. -/
  configuration : String
  /-- The output directories the configuration sets (`packageOutputDirectories`). -/
  outputDirectories : Array (String × FilePath)
  /-- Each library and executable of the package with the modules it provides and the Lean options
  and extra `lean` arguments it builds them with (`packageModules`). -/
  targets : Array TargetInventory
  /-- Each module with the path components of its source below `dir`. -/
  sources : Array (Name × List String)
  deriving BEq, Repr

/-- The selection that an inventory records for a dependency package. -/
def DependencyInventory.selection (dependency : DependencyInventory) : PackageSelection :=
  let base := dependency.root.normalize.components.length
  { package := dependency.package, dir := dependency.root, owned := dependency.owned
    configFile := dependency.configFile, manifestFile := dependency.manifestFile
    configuration := dependency.configuration, outputDirectories := dependency.outputDirectories
    targets := dependency.targets
    sources := dependency.sources.map fun source =>
      (source.«module», source.source.normalize.components.drop base) }

/-- What Lake's load of a copy of the project must select: for the root package, each library and
executable with its modules and options, and for each dependency package its selection, with an
owned package's directory relocated into the copy. -/
structure CopySelection where
  /-- The root package's targets (`SurfaceInventory.targets`). -/
  root : Array TargetInventory
  /-- Each dependency package's selection. -/
  dependencies : Array PackageSelection

/-- A copy of a project made by `copyProject`. -/
structure ProjectCopy where
  /-- The root of the copied project. -/
  project : FilePath
  /-- The real directory of the copy, which holds the copied project and each copied owned path
  dependency. -/
  root : FilePath
  /-- What the copy's Lake load must select: the original's selection, with an owned package's
  directory relocated into the copy. -/
  selection : CopySelection

/-- The real directory that Lake's load of the copy at `project` gives the manifest entry `entry`
when no override replaces it, as `Lake.PackageEntry.materialize` computes it (Lake
`Load/Materialize.lean`, v4.34.1): a `path` entry's directory from the workspace's, and a Git
entry's checkout in the packages directory `packagesDir`, below its subdirectory if it names one;
`none` when that directory does not exist. -/
def manifestDirectory (project packagesDir : FilePath) (entry : _root_.Lake.PackageEntry) :
    IO (Option FilePath) := do
  let dir := match entry.src with
    | .path dir => project / dir
    | .git (subDir? := subDir?) .. =>
      let checkout := project / packagesDir / entry.dirName
      match subDir? with
      | some subDir => checkout / subDir
      | none => checkout
  try some <$> IO.FS.realPath dir catch _ => pure none

/-- Lake reads `.lake/package-overrides.json` on every workspace load, and the copy at `project`
holds the project's manifest but no `.lake` (`copyProject`). Record there an override entry for
each pair of `dependencies` whose dependency the copy's manifest entry of its name would not load
as the pair requires: from the directory of the pair, through the same configuration file and
manifest file as the original's load. The entry is a `path` entry to that directory with those
files. So the copy's configuration stays the project's when no dependency needs one.
`checkCopiedWorkspace` compares Lake's load of the copy with the original's, so an entry that this
decides wrongly is refused there, not trusted. -/
def relocateDependencies (project : FilePath)
    (dependencies : Array (DependencyInventory × FilePath)) : IO Unit := do
  let manifest ← _root_.Lake.Manifest.load? (project / "lake-manifest.json")
  let packagesDir := (manifest.bind (·.packagesDir?)).getD _root_.Lake.defaultPackagesDir
  let entries := (manifest.map (·.packages)).getD #[]
  let mut overrides : Array _root_.Lake.PackageEntry := #[]
  for (dependency, dir) in dependencies do
    let entry := entries.find? (·.name.toString == dependency.package)
    let same ← match entry with
      | some entry =>
          pure ((← manifestDirectory project packagesDir entry) == some dir &&
            entry.configFile == dependency.configFile &&
            entry.manifestFile? == some dependency.manifestFile)
      | none => pure false
    unless same do
      overrides := overrides.push {
        name := (entry.map (·.name)).getD dependency.package.toName, scope := dependency.scope
        inherited := false
        configFile := dependency.configFile, manifestFile? := some dependency.manifestFile
        src := .path dir }
  if overrides.isEmpty then return
  IO.FS.createDirAll (project / ".lake")
  _root_.Lake.Manifest.saveEntries (project / ".lake" / "package-overrides.json") overrides

/-- Copy a checked project into `target`, skipping VCS data, Lake build state, machine artifact
caches, the checker's scratch areas, the `exclude` path that receives the copy, and every part of a
compiled module (`isModulePart`), so the copy holds no compiled module until it builds one. Each
dependency the audit owns, as Lake's own load of the project selects it (`surfaceInventory`), is
copied too, and the copy builds it: the project and those dependencies keep their places relative
to the deepest directory that holds them all, which `target` stands for, so the copy of a project
in `audit/` of a repository whose root its path dependency is holds the repository with the project
at `target/audit`. Dependency checkouts are shared through a link at the copy's packages directory,
so a fresh build in the copy does not refetch or rebuild dependencies, and each dependency that the
copy's manifest would not load as the original's load does is given an override
(`relocateDependencies`). The packages directory is the one the project's manifest records,
`.lake/packages` by default; a relative one outside the project, such as a nested package's
`../.lake/packages`, is linked at the same relative place from the copied project, which must lie
inside `exclude`. -/
def copyProject (repo target exclude : FilePath) : IO ProjectCopy := do
  IO.FS.createDirAll target
  let root ← IO.FS.realPath repo
  let original ← surfaceInventory repo
  let owned := (original.dependencies.filter (·.owned)).foldl (fun dirs dependency =>
    if dependency.root == root || dirs.contains dependency.root then dirs
    else dirs.push dependency.root) #[]
  let directories := #[root] ++ owned
  let base := directories.foldl (fun acc dir => commonPrefix acc dir.normalize.components)
    root.normalize.components
  let place := fun (dir : FilePath) =>
    (dir.normalize.components.drop base.length).foldl (· / FilePath.mk ·) target
  let excludeComponents := exclude.normalize.components
  let excludeReal := (← IO.FS.realPath exclude).normalize.components
  -- Exclusion is closed under descendants. Prune before traversal: filtering
  -- afterwards still visits dependency checkouts and every prior scratch copy.
  -- VCS data, Lake build state, artifact caches and the checker's scratch
  -- directories are pruned at every depth (a nested Lake workspace such as a
  -- committed example adopter carries its own `.lake` with full dependency
  -- checkouts, and a nested package audited on its own keeps its scratch under
  -- its own `.lake`, or under its own `tmp/` when an older Regula audited it);
  -- the rest of the `tmp/` directory is pruned only at the project root and at the root of each
  -- owned path dependency, where it lives.
  let prunedAnywhere := fun (component : String) =>
    component == ".git" || component == _root_.Lake.defaultLakeDir.toString ||
      component == ".cache" || component == Regula.Scratch.legacyDirName
  -- Each directory is walked on its own, and a walk skips the others below it: one of them can
  -- lie in a directory that the walk prunes, as a project in the scratch area of a repository
  -- that is its own path dependency does.
  for top in directories do
    let sourceComponents := top.normalize.components
    let tmpDirectory := sourceComponents ++ ["tmp"]
    let others := (directories.filter (· != top)).map (·.normalize.components)
    let includePath := fun (path : FilePath) =>
      let components := path.normalize.components
      !excludeComponents.isPrefixOf components && !excludeReal.isPrefixOf components &&
        !tmpDirectory.isPrefixOf components &&
        !others.any (fun other => other.length > sourceComponents.length &&
          other.isPrefixOf components) &&
        !(components.drop sourceComponents.length).any prunedAnywhere
    for path in ← top.walkDir (fun path => pure (includePath path)) do
      let components := path.normalize.components
      if components == sourceComponents || !includePath path then
        continue
      let relative := components.drop sourceComponents.length
      let destination := relative.foldl (· / FilePath.mk ·) (place top)
      if ← path.isDir then
        IO.FS.createDirAll destination
      else if !isModulePart (path.fileName.getD "") then
        if let some parent := destination.parent then IO.FS.createDirAll parent
        IO.FS.writeBinFile destination (← IO.FS.readBinFile path)
  let project := place root
  IO.FS.createDirAll project
  let packagesDir := ((← _root_.Lake.Manifest.load? (repo / "lake-manifest.json")).bind
    (·.packagesDir?)).getD _root_.Lake.defaultPackagesDir
  let packages := repo / packagesDir
  if ← packages.isDir then
    let projectComponents := project.normalize.components
    unless excludeComponents.isPrefixOf projectComponents do
      throw <| IO.userError s!"could not link pinned Lake packages: the copy {project} is not \
        inside {exclude}"
    -- `joinWithin_extends`: the link lies inside `exclude`, which the caller removes.
    let some linkComponents := if packagesDir.isAbsolute then none else
        joinWithin excludeComponents (projectComponents.drop excludeComponents.length ++
          packagesDir.normalize.components)
      | throw <| IO.userError s!"could not link pinned Lake packages: the packages directory \
          {packagesDir} is not a relative path that stays inside {exclude} from the copy"
    let link : FilePath := System.mkFilePath linkComponents
    if let some parent := link.parent then IO.FS.createDirAll parent
    let linked ← runProcess project "ln" #["-s", (← IO.FS.realPath packages).toString,
      link.toString]
    if !linked.succeeded then
      throw <| IO.userError s!"could not link pinned Lake packages: {linked.output}"
  let placeOf (dir : FilePath) : IO FilePath := do
    IO.FS.createDirAll (place dir)
    IO.FS.realPath (place dir)
  let dependencies ← original.dependencies.mapM fun dependency => do
    return (dependency, ← if dependency.owned then placeOf dependency.root else pure dependency.root)
  relocateDependencies project dependencies
  return { project, root := ← IO.FS.realPath target
           selection := {
             root := original.targets
             dependencies := dependencies.map fun (dependency, dir) =>
               { dependency.selection with dir } } }

/-- Admit the inventory of a copy whose real directory is `root` and mark it as that copy
(`SurfaceInventory.copy`), so that each environment refuses an owned module that the copy's own
build did not produce (`Environment.ModuleGraph.outsideCopy`). The copy's inventory already keeps
Lake's default output layout of each owned package and one provider for each module name of an
owned package (`surfaceInventory`). Lake's own load of the copy must select exactly what `expected`
gives (`ProjectCopy.selection`): for the root package the same targets, each with the same modules
and options, and the same dependency packages, each with the same selection. With no `expected`,
for a copy that the verification driver made, the copy must own no dependency. -/
def checkCopiedWorkspace (root : FilePath) (expected : Option CopySelection)
    (inventory : SurfaceInventory) : IO SurfaceInventory := do
  let refuse {α : Type} (detail : String) : IO α :=
    throw <| IO.userError s!"lake-workspace-load-failed: in the copy of the project, {detail}"
  match expected with
  | none =>
    for dependency in inventory.dependencies do
      if dependency.owned then
        refuse s!"path dependency '{dependency.package}' at {dependency.root} is owned there but \
          was not copied"
  | some expected =>
    unless inventory.targets == expected.root do
      refuse s!"Lake loads the root package '{inventory.package}' with libraries and executables, \
        their modules or their Lean options and arguments that differ from what it loads for the \
        project"
    for dependency in inventory.dependencies do
      let some wanted := expected.dependencies.find? (·.package == dependency.package)
        | refuse s!"dependency '{dependency.package}' at {dependency.root} is not one of the \
            project's"
      unless dependency.selection == wanted do
        refuse s!"Lake loads dependency '{dependency.package}' from {dependency.root} with \
          configuration {dependency.configFile} and manifest {dependency.manifestFile}, which \
          differs from what it loads for the project: from {wanted.dir} with configuration \
          {wanted.configFile} and manifest {wanted.manifestFile}, and the same configuration text, \
          output directories, libraries and executables with their modules, Lean options and \
          arguments, ownership and module sources"
    for wanted in expected.dependencies do
      unless inventory.dependencies.any (·.package == wanted.package) do
        refuse s!"the project's dependency '{wanted.package}' is missing"
  return { inventory with copy := some root }

/-- A target of the claimed surface that a checker build requests: a library or an executable of
the root package, by a spelling that names it, or the Lean artifacts of a module of the root
package or of a library of the workspace. `Build.run` finds each among the root package's own
targets, and a module otherwise among the workspace's library modules; it never reads a spelling
as Lake target syntax, in which a `/` would name a package. -/
inductive SurfaceTarget where
  /-- The library of the root package whose recorded spelling (`Manifest.targetSpelling` of its
  name) is that of `spelling` (`Manifest.recordedName`), the relation a manifest's library names
  are checked with. -/
  | library (spelling : String)
  /-- The executable of the root package that `spelling` names, as for `library`. -/
  | executable (spelling : String)
  /-- The Lean artifacts (`leanArts`) of the module `name` of a target of the root package, or else
  of the library module `name` of the workspace (`Lake.Workspace.findModule?`), of which
  `surfaceInventory` admits one provider, as a fresh audit builds an owned dependency's module. -/
  | moduleArtifacts (name : Name)
  deriving Inhabited, BEq, Repr

/-- A target of a checker build: one of the claimed surface, or Lake target syntax, with which a
build of the checker's own worker names an executable of a dependency. -/
inductive Target where
  /-- A target of the claimed surface. -/
  | surface (target : SurfaceTarget)
  /-- A target as the `lake build` command line reads it. It requests no module itself. -/
  | spec (text : String)
  deriving Inhabited

/-- The targets that build each claimed library and executable of `manifest`. -/
def claimedTargets (manifest : Manifest) : Array SurfaceTarget :=
  manifest.surfaces.foldl (fun targets surface =>
    targets.push (.library surface.library) ++ surface.executables.map .executable) #[]

/-- The build request for `target` in `ws`, and the modules whose Lean artifacts it requests
itself: for a library, its default facets, as `lake build` builds a library, and the artifacts of
each of its modules, as Lake's globs give them; for an executable, its default facet and the
artifacts of its root module; for a module, its artifacts. Each request is made of Lake's own
target and facet objects as Lake's target resolution makes it (`mkConfigBuildSpec`). A spelling
that names no library or executable of the root package, a module of none of its targets and of no
library of the workspace, and a library without a module refuse. -/
private def surfaceRequest (ws : _root_.Lake.Workspace) (target : SurfaceTarget) :
    IO (Array _root_.Lake.BuildSpec × Array _root_.Lake.Module) := do
  let artifacts (mod : _root_.Lake.Module) : IO _root_.Lake.BuildSpec := do
    let some config := ws.findModuleFacetConfig? (_root_.Lake.Module.facetKind ++ `leanArts)
      | throw <| IO.userError "the workspace has no module facet leanArts"
    return { info := mod.facetCore config.name, buildable := config.buildable }
  match target with
  | .library spelling =>
    let recorded := Manifest.recordedName spelling
    let some lib := ws.root.leanLibs.find? (Manifest.targetSpelling ·.name == recorded)
      | throw <| IO.userError s!"'{spelling}' names no library of the root package"
    let modules ← lib.getModuleArray
    if modules.isEmpty then
      throw <| IO.userError s!"the library '{spelling}' has no module"
    let some config := ws.findFacetConfig? (_root_.Lake.LeanLib.facetKind ++ `default)
      | throw <| IO.userError "the workspace has no library facet default"
    let library : _root_.Lake.BuildSpec :=
      { info := lib.facetCore config.name, buildable := config.buildable }
    return (#[library] ++ (← modules.mapM artifacts), modules)
  | .executable spelling =>
    let recorded := Manifest.recordedName spelling
    let some exe := ws.root.leanExes.find? (Manifest.targetSpelling ·.name == recorded)
      | throw <| IO.userError s!"'{spelling}' names no executable of the root package"
    let some config := ws.findFacetConfig? (_root_.Lake.LeanExe.facetKind ++ `default)
      | throw <| IO.userError "the workspace has no executable facet default"
    let executable : _root_.Lake.BuildSpec :=
      { info := exe.facetCore config.name, buildable := config.buildable }
    return (#[executable, ← artifacts exe.root], #[exe.root])
  | .moduleArtifacts name =>
    let some mod := ws.root.findTargetModule? name <|> ws.findModule? name
      | throw <| IO.userError s!"{name} is a module of no target of the root package and of no \
          library of the workspace"
    return (#[← artifacts mod], #[mod])

/-- A build the checker runs: the Lean options it sets on the root package, if any, and the lines
of its output it also shows as it runs. A `Build` holds no way to run it other than
`Build.runObserved`, whose process result is `Build.run`, so every checker build runs as
`Build.runObserved` describes. -/
structure Build where
  /-- The Lean options set on the root package, over its own, or none, chosen from the workspace as
  Lake loads it, before `Build.run` turns off its artifact cache. It runs before the build, and an
  exception fails the build. -/
  rootOptions : _root_.Lake.Workspace → IO (Option LeanOptions) := fun _ => pure none
  /-- Selects the output lines also printed to standard output as the build writes them. -/
  display : String → Bool := fun _ => false
  /-- The lowest level of a log entry that fails the build (Lake's `failLv`, which
  `lake build --wfail` sets to `warning`): Lake's build monitor counts a required job as failed
  when its log, or the log it replays from its trace, holds an entry of that level or above. -/
  failLv : _root_.Lake.LogLevel := .error
  deriving Inhabited

/-- The arguments Lake passes to `lean` weakly for each module of `library`: its `weakLeanArgs`,
the package's followed by the library's (Lake's `LeanLib.weakLeanArgs`), rendered as compressed
JSON. The root module of an executable belongs to the library that Lake makes from the
executable's configuration, so for it these are the package's and the executable's. -/
def weakArgsRecord (library : _root_.Lake.LeanLib) : String :=
  (toJson library.weakLeanArgs).compress

/-- The `extraDep` facet of a library that the workspace configures, `existing` (Lake's own,
`LeanLib.extraDepFacetConfig`, or one a package declares in its place), with the trace of the
library's `weakArgsRecord` mixed into its job's when the library belongs to the package `root`.
The job of `existing` runs for every library, so what it builds or writes is kept. Lake mixes the
trace of that facet's job into the dependency trace of each module of the library
(`Lake/Build/Module.lean`, line 591), which sets no option of the module's elaboration. -/
def weakArgsExtraDep (root : Name)
    (existing : _root_.Lake.LibraryFacetConfig _root_.Lake.LeanLib.extraDepFacet) :
    _root_.Lake.LibraryFacetConfig _root_.Lake.LeanLib.extraDepFacet :=
  _root_.Lake.mkFacetJobConfig (buildable := existing.buildable) (memoize := existing.memoize)
    fun (library : _root_.Lake.LeanLib) => do
      let job : _root_.Lake.Job Unit ← existing.run library
      if library.pkg.baseName != root then return job
      let record := weakArgsRecord library
      let trace := _root_.Lake.BuildTrace.ofHash (_root_.Lake.pureHash record)
        s!"weakLeanArgs {record}"
      return job.mix (_root_.Lake.Job.ofTask (.pure (.ok () { trace })))

/-- The log of one job of a build, as Lake's build monitor judges it: Lake counts a job that is not
optional as failed when its log holds an entry at the build's failure level or above
(`Monitor.reportJob`, `Lake/Build/Run.lean` lines 119 to 129). -/
structure JobLog where
  /-- The job's caption in Lake's build monitor. -/
  caption : String
  /-- Whether the job is optional, so that its log fails no build. -/
  optional : Bool
  /-- The job's log, with what it replayed from a trace. -/
  entries : Array _root_.Lake.LogEntry
  deriving Inhabited

/-- Each entry of a log in `jobs` of a job that is not optional which Lake can have made from
output of the Lean compiler that is not a Lean message (`Workspace.unparsedCompilerOutput`), after
its job's caption. -/
def unparsedOutput (jobs : Array JobLog) : Array String :=
  jobs.flatMap fun job =>
    if job.optional then #[]
    else (job.entries.filter Workspace.unparsedCompilerOutput).map (s!"{job.caption}: {·.message}")

/-- `unparsedOutput` is empty exactly when no job that is not optional logged an entry that
`Workspace.unparsedCompilerOutput` selects. -/
theorem unparsedOutput_eq_empty_iff (jobs : Array JobLog) :
    unparsedOutput jobs = #[] ↔ ∀ job ∈ jobs, job.optional = false →
      ∀ entry ∈ job.entries, Workspace.unparsedCompilerOutput entry = false := by
  simp only [unparsedOutput, Array.flatMap_eq_empty_iff]
  apply forall₂_congr
  intro job _
  cases job.optional <;> simp [Array.filter_eq_empty_iff]

/-- Move the jobs registered in `own` to `lake`, the queue Lake's build monitor reads, and wait for
each, until `own` is empty; returns `forwarded` with each job moved. A job can register more jobs
while it runs, so `own` is read again once the jobs it held have finished. -/
partial def forwardJobs (own lake : IO.Ref (Array _root_.Lake.OpaqueJob))
    (forwarded : Array _root_.Lake.OpaqueJob) : BaseIO (Array _root_.Lake.OpaqueJob) := do
  let new ← own.modifyGet fun jobs => (jobs, #[])
  if new.isEmpty then return forwarded
  lake.modify (· ++ new)
  for job in new do
    discard <| IO.wait job.task
  forwardJobs own lake (forwarded ++ new)

/-- `build`, with each job it registers kept in `record` as Lake's build monitor reads it. Lake's
monitor judges the jobs registered in the build's job queue and the job that runs the build itself
(`Workspace.runBuild`, `Lake/Build/Run.lean` lines 427 to 436). This runs `build` with a queue of
its own, moves each job registered there to Lake's queue once registered (`forwardJobs`), waits for
each and for the job `build` returns, and records the log of each and that of the job that runs it,
so `record` holds exactly the logs Lake's monitor judges. A module of the build whose message file
name has a line break (`Workspace.lineBreakSourcePaths`) is logged as an error of the job that runs
the build, which fails it. -/
def observedFetch (ws : _root_.Lake.Workspace) (record : IO.Ref (Array JobLog))
    (build : _root_.Lake.FetchM (_root_.Lake.Job Unit)) :
    _root_.Lake.FetchM (_root_.Lake.Job Unit) :=
  _root_.Lake.FetchM.ofFn fun fetch pkg? stack store context log => do
    let own ← IO.mkRef #[]
    let result ← build.toFn fetch pkg? stack store { context with registeredJobs := own } log
    let mut jobs ← forwardJobs own context.registeredJobs #[]
    if let .ok job _ := result then
      discard <| IO.wait job.task
      jobs ← forwardJobs own context.registeredJobs jobs
    let lineBreaks := Workspace.lineBreakSourcePaths ws (← store.get)
    let addErrors (log : _root_.Lake.Log) := lineBreaks.foldl (init := log) fun log path =>
      log.push (.error s!"the file name Lake gives each message of module {path} has a line \
        break, so its log cannot tell those messages from other output of the compiler")
    let result := match result with
      | .ok job log => .ok job (addErrors log)
      | .error position log => .error position (addErrors log)
    let ownLog := match result with
      | .ok _ log => log
      | .error _ log => log
    record.set <| (jobs.map fun job => {
        caption := job.caption, optional := job.optional,
        entries := job.task.get.state.log.entries : JobLog }).push
      { caption := "the build's computation", optional := false, entries := ownLog.entries }
    return result

/-- Build `targets` of the workspace at `repo` as `build` describes, in this process through
Lake's build API, as `lake build` does: its build monitor's text is the output, and a failed build
exits 1. The inherited `LEAN_PATH` and `LEAN_SRC_PATH` are ignored, so the build resolves modules
only through that workspace. No package reads or writes Lake's artifact cache
(`Workspace.uncachedWorkspace`), and no module of the root package keeps a trace that records a
restore from it (`Workspace.dropRestoredTraces`). A target of the claimed surface is found among
the root package's own libraries, executables and modules, or a module among the workspace's
library modules (`surfaceRequest`), or the build fails.
For each, the build also requests the Lean artifacts of each of its modules, whatever the
library's default facets, so Lake elaborates each such module or replays the log of the
elaboration that wrote its trace, and its warnings are in the output. Afterwards each such
module's trace must record an elaboration (`Workspace.elaborationTrace`), or the build fails: a
module restored from the cache has no log of its elaboration, so its warnings would be missing
from the output. The build fails when a required job logs an entry at `build.failLv` or above.
With root-package options (`Build.rootOptions`), the build's libraries also take their `extraDep`
facet from `weakArgsExtraDep`, around the one the workspace configures. Lake's module trace
records a module's Lean options but not the `weakLeanArgs` Lake passes to `lean`, so without it a
module elaborated under weak arguments since changed would stay up to date and replay the log of
that elaboration. With it, a change to a weak
argument of the root package or of one of its targets changes the dependency trace of each module
that the arguments reach, and Lake elaborates each such module again; that Lake mixes that facet's
trace into the module's is read from Lake's source. The modules of other packages keep Lake's own
traces. The build runs through `observedFetch`, so the run returns beside the process result the
log of each job that Lake's build monitor judged. The `lean` processes Lake starts inherit this
process's working directory, which a module's elaboration can read (`IO.currentDir`), and Lake
reads a target spec that names a path from it, so the build runs with the root package's directory
as the working directory, as a `lake build` run there does. Lake's loader sets this process's Lean search
path (`Lean.searchPathRef`), which the checker's workers inherit. The run restores both, so like a
child `lake build` it leaves the checker's own state as it was. Both are process-wide, so no other
task of the process may build or read them while it runs; the checker runs its builds one at a
time. -/
def Build.runObserved (build : Build) (repo : FilePath) (targets : Array Target) :
    IO (ProcessResult × Array JobLog) := do
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← showingStream (IO.FS.Stream.ofBuffer buffer) build.display
  let searchPath ← Lean.searchPathRef.get
  let workingDirectory ← IO.currentDir
  let jobLogs ← IO.mkRef (#[] : Array JobLog)
  let exitCode ← try
      Workspace.withRootWorkspace repo (scrubSearchPath := true) fun loaded => do
        let ws := Workspace.uncachedWorkspace loaded
        IO.Process.setCurrentDir ws.root.dir
        let mut specs := #[]
        let mut modules := #[]
        for target in targets do
          match target with
          | .surface target =>
            let (requested, named) ← surfaceRequest ws target
            specs := specs ++ requested
            modules := modules ++ named
          | .spec text =>
            match ← (_root_.Lake.parseTargetSpecs ws [text]).toBaseIO with
            | .ok parsed => specs := specs ++ parsed
            | .error error => throw <| IO.userError (toString error)
        if let some spec := specs.find? (!·.buildable) then
          throw <| IO.userError s!"'{spec.info.key.toSimpleString}' is not a buildable target"
        let rootOptions ← build.rootOptions loaded
        Workspace.dropRestoredTraces ws
        let (ws, leanOptOverrides) ← match rootOptions with
          | some options =>
            let some existing := ws.findLibraryFacetConfig? _root_.Lake.LeanLib.extraDepFacet
              | throw <| IO.userError "the workspace configures no `extraDep` facet of a library"
            pure (ws.addLibraryFacetConfig (weakArgsExtraDep ws.root.baseName existing),
              ({} : NameMap LeanOptions).insert ws.root.baseName options)
          | none => pure (ws, {})
        ws.runBuild (observedFetch ws jobLogs (_root_.Lake.buildSpecs specs)) {
          out := .stream out, ansiMode := .noAnsi, showSuccess := true, leanOptOverrides,
          failLv := build.failLv }
        for mod in modules do
          let text ← match ← (IO.FS.readFile mod.traceFile).toBaseIO with
            | .ok text => pure (some text)
            | .error _ => pure none
          unless text.any Workspace.elaborationTrace do
            throw <| IO.userError s!"the build left no trace of an elaboration of {mod.name}, \
              so its messages were not observed"
      pure (0 : UInt32)
    catch error =>
      out.putStrLn s!"error: {error}"
      pure 1
    finally
      Lean.searchPathRef.set searchPath
      IO.Process.setCurrentDir workingDirectory
  let some stdout := String.fromUTF8? (← buffer.get).data
    | return ({ exitCode := 1, stdout := "", stderr := "error: build output is not UTF-8" },
        ← jobLogs.get)
  return ({ exitCode, stdout, stderr := "" }, ← jobLogs.get)

/-- The process result of `Build.runObserved`. -/
def Build.run (build : Build) (repo : FilePath) (targets : Array Target) : IO ProcessResult :=
  (·.1) <$> build.runObserved repo targets

instance : CoeFun Build (fun _ => FilePath → Array Target → IO ProcessResult) := ⟨Build.run⟩

/-- Run the executable of the root package of the workspace at `repo` that `spelling` names (as
for `SurfaceTarget.executable`) with `args`, as `lake exe` runs it once it is built: in `repo`,
with the environment Lake gives the programs it starts (`Workspace.augmentedEnvVars`), here that
of `Workspace.uncachedWorkspace`, without the inherited `LEAN_PATH` and `LEAN_SRC_PATH`. Unlike
`lake exe` it builds nothing, so no build that ignores `uncachedWorkspace` precedes it: the caller
builds the executable first with `Build.run`, and a missing executable fails. -/
def runBuiltExecutable (repo : FilePath) (spelling : String) (args : Array String) :
    IO ProcessResult := do
  let (file, env) ← Workspace.withRootWorkspace repo (scrubSearchPath := true) fun loaded => do
    let ws := Workspace.uncachedWorkspace loaded
    let recorded := Manifest.recordedName spelling
    let some exe := ws.root.leanExes.find? (Manifest.targetSpelling ·.name == recorded)
      | throw <| IO.userError s!"'{spelling}' names no executable of the root package"
    pure (exe.file, ws.augmentedEnvVars)
  unless ← file.pathExists do
    throw <| IO.userError s!"executable {spelling} was not built: {file}"
  runProcess repo file.toString args env

/-- Build the targets with the root package's own options, printing nothing as it runs. -/
def buildTargets : Build := {}

/-- `buildTargets`, also showing Lake's own progress line for each job (`isLakeProgressLine`) as
the build runs; the captured output is the same. -/
def buildTargetsShowing : Build := { display := isLakeProgressLine }

/-- Root-package Lean options of the `lint` driver's audit build: the audit-build marker
(`Regula.Linter.auditBuildOption`), which turns Regula's local feedback off in every module that
imports `Regula.Linter` whatever its source sets `linter.regula` to (`liveFeedback_auditBuild`).
The marker is unregistered and `weak.`, so every module's command scopes ignore it and
elaborate exactly as without it. The audit's own policy stages report Regula findings; the
warning-free check then measures only other warnings. The option enters Lake's module trace,
so with it a module built with local feedback, for example by an ordinary `lake build`, is
rebuilt: its replayed log can neither add Regula warnings nor stand in for this configuration's
warnings. Lake scopes Lean options by package and library, not by module, so the trace change
reaches every root-package module that the claimed build compiles. `buildAuditTargets`
therefore omits it only for a workspace of the plain shape in which each module of the root
package resolves to its one source and none imports the marker's reader
(`auditMarkerNeeded`); `axiomGate` and the build-lint target keep ordinary options
(`AxiomGate.claimedBuild`). -/
def auditLeanOptions : LeanOptions := .ofArray #[⟨Regula.Linter.auditBuildOption, .ofBool true⟩]

/-- The result of a build that `buildCheckedObservation` ran with Lake's failure level at
`warning`. -/
structure CheckedBuild where
  /-- The build's exit code and output. Lake's build monitor failed the build, and
  `Build.runObserved` exited 1, when a required job logged an entry of level `warning` or above. -/
  process : ProcessResult
  /-- The log of each job that Lake's build monitor judged (`observedFetch`). -/
  jobs : Array JobLog

/-- Each entry of a job of `build` that is not optional which Lake can have made from compiler
output that is not a Lean message (`unparsedOutput`), such as a warning whose line other output
corrupted, which Lake logs as information. -/
def CheckedBuild.unparsed (build : CheckedBuild) : Array String :=
  unparsedOutput build.jobs

/-- Build the claimed Lake targets and require success with no warnings: the build runs with
Lake's failure level at `warning`, so it succeeds only when no required job logged a warning or an
error. Lake gives each message of a module's elaboration the level of its Lean severity
(`LogLevel.ofMessageSeverity`), so an information message, whatever its text, never fails the
build. The build is also refused when a job that Lake's build monitor judged holds an entry Lake
can have made from compiler output that is not a Lean message (`CheckedBuild.unparsed`), since Lake
logs it as information whatever it held. The output is read only to report a failure. Returns the
diagnostic lines to report on failure. -/
def buildCheckedObservation (repo : FilePath) (targets : Array SurfaceTarget)
    (mode : String) (build : Build := buildTargets) :
    IO (CheckedBuild × Option (Array String)) := do
  let (process, jobs) ← Build.runObserved { build with failLv := .warning } repo
    (targets.map .surface)
  let build : CheckedBuild := { process, jobs }
  if process.succeeded && build.unparsed.isEmpty then return (build, none)
  let diagnostics :=
    if !build.unparsed.isEmpty then
      #["the compiler printed output that is not a Lean message, which Lake logs as \
        information whatever it held:"] ++ build.unparsed
    -- A warning's payload (the unused simp argument, the hint) sits on the
    -- continuation lines after its head; report the whole block.
    else if !(warningLines process.output).isEmpty then
      diagnosticBlocks process.output isWarningLine
    -- Lean's expected type and supplied proof are continuation lines. Keep
    -- that context so public-gate qualification can identify the obligation.
    else if !(errorLines process.output).isEmpty then outputLines process.output
    else takeLast 20 (outputLines process.output)
  return (build, some
      (#[s!"FAIL[build-failed]: positive surface did not build {mode} and warning-free"]
    ++ diagnostics))

/-- Compatibility diagnostic projection. Acceptance callers retain the process observation. -/
def buildChecked (repo : FilePath) (targets : Array SurfaceTarget)
    (mode : String) : IO (Option (Array String)) := do
  return (← buildCheckedObservation repo targets mode).2

/-- A project either builds its original targets before scope inspection, or first builds
artifacts and owes those exact original targets after the refusal-only scope check. -/
inductive ClaimedBuildPlan (original : Array SurfaceTarget) where
  /-- The initial build already requests every original target. -/
  | full
  /-- Scope inspection precedes the still-required complete target build. -/
  | deferred (artifacts : Array SurfaceTarget)

/-- Targets needed before the module-scope preflight. -/
def ClaimedBuildPlan.initialTargets {original : Array SurfaceTarget} :
    ClaimedBuildPlan original → Array SurfaceTarget
  | .full => original
  | .deferred artifacts => artifacts

/-- A deferred plan still owes the complete original target build. -/
def ClaimedBuildPlan.completionTargets {original : Array SurfaceTarget} :
    ClaimedBuildPlan original → Option (Array SurfaceTarget)
  | .full => none
  | .deferred _ => some original

/-- No deferred plan can substitute a smaller target set for the final build. -/
theorem ClaimedBuildPlan.completionTargets_exact {original targets : Array SurfaceTarget}
    (plan : ClaimedBuildPlan original) (h : plan.completionTargets = some targets) :
    targets = original := by
  cases plan <;> simp_all [completionTargets]

/-- Stages completed after the initial warning-free build, before scope inspection. -/
def ClaimedBuildPlan.completedBeforeScope {original : Array SurfaceTarget} :
    ClaimedBuildPlan original → List RegulaPolicy.Stage
  | .full => [.configuration, .discovery, .build]
  | .deferred _ => [.configuration, .discovery]

/-- The build stage is complete before preflight exactly when no final build remains. -/
theorem ClaimedBuildPlan.build_completed_iff {original : Array SurfaceTarget}
    (plan : ClaimedBuildPlan original) :
    RegulaPolicy.Stage.build ∈ plan.completedBeforeScope ↔ plan.completionTargets = none := by
  cases plan <;> simp [completedBeforeScope, completionTargets]

private def artifactTargets? (manifest : Manifest) (inventory : SurfaceInventory) :
    Option (Array SurfaceTarget) := do
  if !(manifest.surfaces.any fun surface => !surface.executables.isEmpty) then none else do
    let mut targets := #[]
    for surface in manifest.surfaces do
      targets := targets.push (.library surface.library)
      for executable in surface.executables do
        let found ← inventory.executables.find? (·.executable == executable)
        targets := targets.push (.moduleArtifacts found.root)
    return targets

/-- Keep library targets, including their custom facets, and use each claimed executable's
actual root `leanArts` facet before scope inspection, named by its module (`moduleArtifacts`).
An executable the inventory does not list keeps the original full build for the whole plan. -/
def claimedBuildPlan (manifest : Manifest) (inventory : SurfaceInventory) :
    ClaimedBuildPlan (claimedTargets manifest) :=
  match artifactTargets? manifest inventory with
  | some artifacts => .deferred artifacts
  | none => .full

/-- A library-only claim keeps the original one-build plan. -/
theorem claimedBuildPlan_without_executables (manifest : Manifest)
    (inventory : SurfaceInventory)
    (h : manifest.surfaces.any (fun surface => !surface.executables.isEmpty) = false) :
    claimedBuildPlan manifest inventory = .full := by
  simp [claimedBuildPlan, artifactTargets?, h]

/-- The modules `moduleName` imports transitively, as `lake query +MODULE:transImports`
reports them in `repo`. -/
def transitiveImports (repo : FilePath) (moduleName : String) : IO (Array String) := do
  jsonStringArray s!"transitive imports for {moduleName}" <|
    ← lakeQuery repo s!"+{moduleName}:transImports"

end Regula.Checker.Lake
