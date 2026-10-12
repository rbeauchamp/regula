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

/-- A component of a name as `nameJson` writes it: a string component is its text, and a numeric
one is an array that holds its digits, so neither form is the other. The expression matches on no
value, so the `extraDep` facet of Regula's `lakefile.lean`, whose admission by identity allows no
matcher, writes the same one. -/
def componentJson (component : Name) : Json :=
  if component.isNum then .arr #[.str (component.toString (escape := false))]
  else .str component.getString!

/-- A name by its components (`Name.components`), each as `componentJson` writes it. Unlike `toJson`
of a name, which writes its text and gives the distinct names `` `«?a.b» `` and `` `«?a».b `` the
same one, `nameOfJson?` inverts it (`nameOfJson?_eq_some_iff`), so distinct names have distinct
values. -/
def nameJson (name : Name) : Json :=
  .arr (name.components.map componentJson).toArray

/-- The name `name` followed by the component that `json` gives as `componentJson` writes it, or
none for any other value. A numeric component's digits must be those `Nat.repr` writes, so each
value read is one that `componentJson` writes. -/
def nameStep (name : Name) : Json → Option Name
  | .str text => some (.str name text)
  | .arr items =>
    if h : items.size = 1 then
      match items[0] with
      | .str digits => digits.toNat?.bind fun n =>
          if Nat.repr n = digits then some (.num name n) else none
      | _ => none
    else none
  | _ => none

/-- The name whose `nameJson` is `json`, or none when `json` is no such value. -/
def nameOfJson? : Json → Option Name
  | .arr items => items.toList.foldlM nameStep .anonymous
  | _ => none

/-- The components of `name.str text`: those of `name`, then `text`. -/
theorem components_str (name : Name) (text : String) :
    (Name.str name text).components = name.components ++ [.str .anonymous text] := by
  simp [Name.components, Name.componentsRev, Name.mkStr]

/-- The components of `name.num n`: those of `name`, then `n`. -/
theorem components_num (name : Name) (n : Nat) :
    (Name.num name n).components = name.components ++ [.num .anonymous n] := by
  simp [Name.components, Name.componentsRev, Name.mkNum]

/-- A string component is written as its text. -/
theorem componentJson_str (text : String) : componentJson (.str .anonymous text) = .str text := by
  simp [componentJson, Name.isNum, Name.getString!]

/-- A numeric component is written as the array of its digits, as `Nat.repr` writes them. -/
theorem componentJson_num (n : Nat) :
    componentJson (.num .anonymous n) = .arr #[.str (Nat.repr n)] := by
  simp only [componentJson, Name.isNum, ite_true]
  rfl

/-- A step that `nameStep` reads extends the written components by the value it read. -/
theorem nameStep_eq_some {name next : Name} {json : Json} (h : nameStep name json = some next) :
    next.components.map componentJson = name.components.map componentJson ++ [json] := by
  unfold nameStep at h
  split at h
  · cases h; simp [components_str, componentJson_str]
  · rename_i items
    split at h
    · rename_i hSize
      split at h
      · rename_i digits hDigits
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨n, -, hNext⟩ := h
        split at hNext
        · rename_i hRepr
          cases hNext
          have hItems : items = #[.str digits] := by
            apply Array.ext (by simp [hSize])
            intro i hi _
            have : i = 0 := by omega
            subst this; simp [hDigits]
          simp [components_num, componentJson_num, hItems, hRepr]
        · cases hNext
      · cases h
    · cases h
  · cases h

/-- What `nameStep` reads from `items`, starting at `start`, has the written components of `start`
followed by `items`. -/
theorem foldlM_nameStep_eq_some : ∀ (items : List Json) (start name : Name),
    items.foldlM nameStep start = some name →
      name.components.map componentJson = start.components.map componentJson ++ items
  | [], start, name, h => by cases h; simp
  | item :: rest, start, name, h => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨next, hNext, hRest⟩ := h
    rw [foldlM_nameStep_eq_some rest next name hRest, nameStep_eq_some hNext]
    simp

/-- `nameStep` reads the written components of `name` back to `name`. -/
theorem foldlM_nameStep_components (name : Name) :
    (name.components.map componentJson).foldlM nameStep .anonymous = some name := by
  induction name with
  | anonymous => rfl
  | str prefix_ text ih =>
    simp [components_str, List.foldlM_append, ih, componentJson_str, nameStep]
  | num prefix_ n ih =>
    simp [components_num, List.foldlM_append, ih, componentJson_num, nameStep, Nat.toNat?_repr]

/-- `nameOfJson?` reads `name` from `json` exactly when `json` is `nameJson name`: it inverts
`nameJson`, so distinct names have distinct values, whatever their components. -/
theorem nameOfJson?_eq_some_iff (json : Json) (name : Name) :
    nameOfJson? json = some name ↔ json = nameJson name := by
  constructor
  · intro h
    cases json <;> simp only [nameOfJson?, reduceCtorEq] at h
    rename_i items
    have hItems : name.components.map componentJson = items.toList := by
      have := foldlM_nameStep_eq_some items.toList .anonymous name h
      rwa [show Name.anonymous.components = [] from rfl, List.map_nil, List.nil_append] at this
    simp [nameJson, hItems]
  · rintro rfl
    simp [nameOfJson?, nameJson, foldlM_nameStep_components]

/-- `List.mapM Json.getStr?`, the traversal of Lean's `fromJson?` for an array of strings, reads
`texts` exactly from the list of their JSON strings. -/
theorem mapM_getStr?_eq_ok_iff : ∀ (items : List Json) (texts : List String),
    items.mapM Json.getStr? = .ok texts ↔ items = texts.map .str
  | [], texts => by cases texts <;> simp [pure, Except.pure]
  | .str text :: rest, texts => by
    have ih := mapM_getStr?_eq_ok_iff rest
    rw [List.mapM_cons]
    cases hRest : rest.mapM Json.getStr? with
    | error _ =>
      simp only [Json.getStr?, bind, Except.bind, pure, Except.pure, reduceCtorEq, false_iff]
      rintro hEq
      cases texts with
      | nil => cases hEq
      | cons _ tail =>
        simp only [List.map_cons, List.cons.injEq] at hEq
        have := (ih tail).mpr hEq.2
        rw [hRest] at this; cases this
    | ok values =>
      simp only [Json.getStr?, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      have hValues := (ih values).mp hRest
      cases texts with
      | nil => simp
      | cons _ tail =>
        simp only [List.cons.injEq, List.map_cons, Json.str.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨rfl, hValues⟩
        · rintro ⟨rfl, hTail⟩
          refine ⟨rfl, ?_⟩
          have := (ih tail).mpr hTail
          rw [hRest] at this
          cases this; rfl
  | .null :: _, texts | .bool _ :: _, texts | .num _ :: _, texts | .arr _ :: _, texts
  | .obj _ :: _, texts => by
    cases texts <;> simp [List.mapM_cons, Json.getStr?, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]

/-- Lean's `fromJson?` for an array of strings reads `strings` exactly from the array of their
JSON strings. -/
theorem fromJson?_strings_eq_ok_iff (json : Json) (strings : Array String) :
    fromJson? (α := Array String) json = .ok strings ↔ json = .arr (strings.map .str) := by
  cases json with
  | arr items =>
    cases items with
    | mk items =>
      cases strings with
      | mk texts =>
        simp only [fromJson?, Lean.Array.fromJson?, List.mapM_toArray, List.map_toArray]
        cases hItems : items.mapM Json.getStr? with
        | error _ =>
          simp only [Functor.map, Except.map, reduceCtorEq, false_iff]
          intro hEq
          have := (mapM_getStr?_eq_ok_iff items texts).mpr
            (by simpa using congrArg Array.toList (Json.arr.inj hEq))
          rw [hItems] at this; cases this
        | ok values =>
          simp only [Functor.map, Except.map, Except.ok.injEq, Json.arr.injEq]
          have := (mapM_getStr?_eq_ok_iff items values).mp hItems
          constructor
          · intro h; cases h; simp [this]
          · intro h
            have hTexts : items = texts.map .str := by simpa using congrArg Array.toList h
            have := (mapM_getStr?_eq_ok_iff items texts).mpr hTexts
            rw [hItems] at this; cases this; rfl
  | _ => simp [fromJson?, Lean.Array.fromJson?, throw, throwThe, MonadExceptOf.throw]

/-- The record of the weak arguments of the library `library` of the package `package`: the word
`weakLeanArgs`, the package's `baseName` (unique in a workspace) and the library's name as
`nameJson` writes them, and `args`, the arguments Lake passes to `lean` weakly for each module of
the library. -/
def weakArgsRecordJson (package library : Name) (args : Array String) : Json :=
  .arr #[.str "weakLeanArgs", nameJson package, nameJson library, .arr (args.map .str)]

/-- The package, library and weak arguments that `json` records as `weakArgsRecordJson` writes it,
or none when it is no such record. -/
def weakArgsRecordOf? : Json → Option (Name × Name × Array String)
  | .arr items =>
    match items.toList with
    | [.str "weakLeanArgs", package, library, args] =>
      match nameOfJson? package, nameOfJson? library, fromJson? (α := Array String) args with
      | some package, some library, .ok args => some (package, library, args)
      | _, _, _ => none
    | _ => none
  | _ => none

/-- `weakArgsRecordOf?` reads a package, a library and weak arguments from `json` exactly when
`json` is their record: it inverts `weakArgsRecordJson`, whatever the names. -/
theorem weakArgsRecordOf?_eq_some_iff (json : Json) (package library : Name)
    (args : Array String) :
    weakArgsRecordOf? json = some (package, library, args) ↔
      json = weakArgsRecordJson package library args := by
  constructor
  · intro h
    unfold weakArgsRecordOf? at h
    split at h
    · rename_i items
      split at h
      · rename_i packageJson libraryJson argsJson hItems
        split at h
        · rename_i hPackage hLibrary hArgs
          cases h
          have hArray : items = #[.str "weakLeanArgs", packageJson, libraryJson, argsJson] := by
            cases items; simp_all
          rw [hArray, (nameOfJson?_eq_some_iff _ _).mp hPackage,
            (nameOfJson?_eq_some_iff _ _).mp hLibrary, (fromJson?_strings_eq_ok_iff _ _).mp hArgs]
          rfl
        · cases h
      · cases h
    · cases h
  · rintro rfl
    have hPackage := (nameOfJson?_eq_some_iff (nameJson package) package).mpr rfl
    have hLibrary := (nameOfJson?_eq_some_iff (nameJson library) library).mpr rfl
    have hArgs := (fromJson?_strings_eq_ok_iff (.arr (args.map .str)) args).mpr rfl
    simp [weakArgsRecordOf?, weakArgsRecordJson, hPackage, hLibrary, hArgs]

/-- The record is injective in the library's identity and its weak arguments: records of two
libraries that differ in the package or in the library's name are different values. -/
theorem weakArgsRecordJson_injective {package library package' library' : Name}
    {args args' : Array String}
    (h : weakArgsRecordJson package library args = weakArgsRecordJson package' library' args') :
    package = package' ∧ library = library' ∧ args = args' := by
  have hRead := (weakArgsRecordOf?_eq_some_iff _ package library args).mpr rfl
  rw [h, (weakArgsRecordOf?_eq_some_iff _ package' library' args').mpr rfl] at hRead
  simp only [Option.some.injEq, Prod.mk.injEq] at hRead
  exact ⟨hRead.1.symm, hRead.2.1.symm, hRead.2.2.symm⟩

/-- The record of `library`: its package's `baseName`, its name and its `weakLeanArgs`, the
package's followed by the library's (Lake's `LeanLib.weakLeanArgs`), in `weakArgsRecordJson`. The
root module of an executable belongs to the library that Lake makes from the executable's
configuration, so for it these are the package's and the executable's. -/
def weakArgsRecord (library : _root_.Lake.LeanLib) : Json :=
  weakArgsRecordJson library.pkg.baseName library.name library.weakLeanArgs

/-- The caption of the trace input that records `library`'s `weakArgsRecord`, as both
`weakArgsExtraDep` and the `extraDep` facet that Regula's `lakefile.lean` declares write it: the
record rendered as compressed JSON. -/
def weakArgsCaption (library : _root_.Lake.LeanLib) : String :=
  (weakArgsRecord library).compress

/-- Whether the trace input caption `caption` is a current record of `library`: it reads as JSON
whose record (`weakArgsRecordOf?`) names `library`'s package and `library` and gives its current
weak arguments. -/
def ownRecord (library : _root_.Lake.LeanLib) (caption : String) : Bool :=
  match Json.parse caption with
  | .ok json =>
    decide (weakArgsRecordOf? json =
      some (library.pkg.baseName, library.name, library.weakLeanArgs))
  | .error _ => false

/-- A caption is a current record of `library` exactly when Lean's JSON parser reads it as
`library`'s record (`weakArgsRecord`), by `weakArgsRecordOf?_eq_some_iff`. -/
theorem ownRecord_iff (library : _root_.Lake.LeanLib) (caption : String) :
    ownRecord library caption = true ↔ Json.parse caption = .ok (weakArgsRecord library) := by
  unfold ownRecord
  split
  · rename_i json hParse
    rw [hParse, decide_eq_true_iff, weakArgsRecordOf?_eq_some_iff]
    simp [weakArgsRecord]
  · rename_i hParse
    simp [hParse]

/-- A module's trace file records the weak arguments of the module's own library, `library`,
exactly when Lake reads it as a trace whose inputs hold, at some depth, an input whose caption is
a current record of `library` (`ownRecord_iff`). A record that the trace holds for a different
library, nested through that library's `extraDep` job, names that library or its package, so it
is a different record (`weakArgsRecordJson_injective`), whatever the names. That the record
`weakArgsExtraDep` writes, rendered as text, reads back as itself is Lean's JSON rendering, not
proved here; the build-policy controls observe it.

Assumes: Regula's facet (`weakArgsExtraDep`, or the `extraDep` facet of Regula's `lakefile.lean`)
wrote the record when Lake built the module. This is the trust in the build traces that Lake
recorded in the checkout, which standard §7.11 states for the incremental gate. A facet that wrote
a forged record when the module was built is outside this evidence; `--fresh` rests on no recorded
trace. For Regula's shipped `lakefile.lean`, acceptance checks only that its encoder's elaborated
value is equal to `weakArgsRecordJson` (`lakefileEncoderAgrees`), nothing about a configuration
that an adopter or a dependency changes. -/
theorem traceRecords_ownRecord_iff (library : _root_.Lake.LeanLib) (text : String) :
    Workspace.traceRecords (ownRecord library) text = true ↔
      ∃ data, _root_.Lake.BuildMetadata.parse text = .ok data ∧
        Workspace.Records (ownRecord library) (toJson data.inputs) :=
  Workspace.traceRecords_iff _ _

/-- The name of the `extraDep` facet declaration that Regula's own `lakefile.lean` ships, which
mixes each root library's `weakArgsCaption` into its job's trace. -/
def regulaFacetName : Name := `weakLeanArgsTrace

/-- The name of the encoder that the facet of Regula's `lakefile.lean` runs to write its record: a
copy of `weakArgsRecordJson`. The file cannot import Regula's modules, since Lake loads the
configuration of a fresh dependency before it builds any of that dependency's modules.
`lakefileEncoderAgrees` checks the copy. -/
def lakefileEncoderName : Name := `weakLeanArgsRecord

/-- Whether the kernel admits `value`, of type `type`, as equal to `weakArgsRecordJson` by
`Eq.refl`: it adds `value` to `env` as a definition, then that theorem, and discards the result. A
value of another type, or one that uses a constant `env` lacks or unfolds to another term, is
refused. -/
def agreesWithRecordJson (env : Environment) (type value : Expr) : Bool :=
  let copy := `_regula_lakefile_encoder
  let definition : DefinitionVal :=
    { name := copy, levelParams := [], type, value, hints := ReducibilityHints.abbrev
      safety := .safe }
  let equality : TheoremVal :=
    { name := copy ++ `agrees, levelParams := []
      type := mkApp3 (mkConst ``Eq [.one]) type (mkConst copy) (mkConst ``weakArgsRecordJson)
      value := mkApp2 (mkConst ``Eq.refl [.one]) type (mkConst copy) }
  let checked := do
    let env ← env.addDeclCore 0 defaultMaxRecDepth.toUSize (.defnDecl definition) none
    env.addDeclCore 0 defaultMaxRecDepth.toUSize (.thmDecl equality) none
  checked matches .ok _

/-- Whether the compiled configuration `config` of Regula's `lakefile.lean` has an encoder equal to
`weakArgsRecordJson`: its declaration `lakefileEncoderName` has no universe parameters and is
equal to `weakArgsRecordJson` by `Eq.refl` in `env` (`agreesWithRecordJson`), and the value of
its facet declaration (`regulaFacetName`) mentions that declaration. This checks the elaborated
declarations that Lake compiles, not their source text.

Acceptance runs it on the configuration of Regula's own checkout (`Regula.RegistryChecks`), to
catch a drift between the encoder of Regula's shipped `lakefile.lean` and `weakArgsRecordJson`.
It establishes that this encoder's elaborated value is equal to `weakArgsRecordJson` by
`Eq.refl`, and that the facet's value mentions it. It establishes nothing about a configuration
that an adopter or a dependency changes, which is the case of a forged facet outside the
incremental gate's evidence (`traceRecords_ownRecord_iff`). Nor does it show that the facet
runs the encoder, how the facet forms the record's arguments or the caption (the build-lint
qualification exercises these), or that no runtime replacement such as `implemented_by` changes
the code Lean's compiler emits for it. -/
def lakefileEncoderAgrees (env : Environment) (config : ModuleData) : Except String Unit := do
  let find (name : Name) : Except String (Expr × Expr) :=
    match config.constants.find? (·.name == name) with
    | some (.defnInfo info) =>
      if info.levelParams.isEmpty then .ok (info.type, info.value)
      else .error s!"the declaration {name} of Regula's lakefile has universe parameters"
    | _ => .error s!"Regula's lakefile has no definition {name}"
  let (type, value) ← find lakefileEncoderName
  unless agreesWithRecordJson env type value do
    throw s!"the kernel does not admit {lakefileEncoderName} of Regula's lakefile as equal to \
      {``weakArgsRecordJson}"
  let (_, facet) ← find regulaFacetName
  unless facet.getUsedConstants.contains lakefileEncoderName do
    throw s!"the facet {regulaFacetName} of Regula's lakefile does not use {lakefileEncoderName}"

/-- Whether a package's compiled configuration holds exactly Regula's own `extraDep` facet
declaration: the text of its configuration file (`text`) is the text of the `lakefile.lean` of the
Regula that runs this decision (`running`, `runningLakefile`), that file declares exactly one library
facet itself (`ownLibraryFacets`), and `regulaFacetName` is among its constants. -/
def regulaFacetAdmitted (text running : Option String) (ownLibraryFacets : Nat)
    (constants : Array Name) : Bool :=
  match text, running with
  | some text, some running =>
    text == running && ownLibraryFacets == 1 && constants.contains regulaFacetName
  | _, _ => false

/-- Regula's facet is admitted exactly when both configuration texts are read and equal, the file
declares one library facet of its own, and it has a constant named `regulaFacetName`. -/
theorem regulaFacetAdmitted_iff (text running : Option String) (ownLibraryFacets : Nat)
    (constants : Array Name) :
    regulaFacetAdmitted text running ownLibraryFacets constants = true ↔
      ∃ source, text = some source ∧ running = some source ∧ ownLibraryFacets = 1 ∧
        regulaFacetName ∈ constants := by
  cases text with
  | none => simp [regulaFacetAdmitted]
  | some source =>
    cases running with
    | none => simp [regulaFacetAdmitted]
    | some other =>
      simp only [regulaFacetAdmitted, Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem,
        Option.some.injEq]
      constructor
      · rintro ⟨⟨rfl, h1⟩, h2⟩; exact ⟨_, rfl, rfl, h1, h2⟩
      · rintro ⟨_, rfl, rfl, h1, h2⟩; exact ⟨⟨rfl, h1⟩, h2⟩

/-- The text of the `lakefile.lean` of the package whose build directory holds the running
executable, `<package>/.lake/build/bin/<executable>`, or none when it cannot be read. -/
def runningLakefile : IO (Option String) := do
  let app ← IO.FS.realPath (← IO.appPath)
  let some package := (app.parent.bind (·.parent)).bind (·.parent) |>.bind (·.parent)
    | return none
  match ← (IO.FS.readFile (package / "lakefile.lean")).toBaseIO with
  | .ok text => return some text
  | .error _ => return none

/-- The number of library facets that the compiled configuration of `package` declares, itself or
through its imports, other than Regula's own `extraDep` facet when the file is the running Regula's
`lakefile.lean` (`regulaFacetAdmitted`, with `running` its text). Lake inserts each into the
workspace's facets in turn (`Workspace.addFacetDecls`), so one named `extraDep` replaces the facet
that Regula's `lakefile.lean` declares when its package is resolved later. A `lakefile.toml`
declares none. A configuration file that cannot be read fails. -/
def otherLibraryFacets (ws : _root_.Lake.Workspace) (running : Option String)
    (package : _root_.Lake.Package) : IO Nat := do
  if package.configFile.extension == some "toml" then return 0
  let some file := package.configFile.fileName
    | throw <| IO.userError s!"the configuration {package.configFile} names no file"
  let compiled := ws.root.dir / _root_.Lake.defaultLakeDir / "config" / toString package.wsIdx /
    (FilePath.mk file).withExtension "olean"
  let (config, _) ← readModuleData compiled
  -- An entry of module names: the import lines of a Lean configuration.
  requireSafeModuleNames s!"the configuration {package.configFile}" (config.imports.map (·.module))
  let imported ← _root_.Lake.importModulesUsingCache config.imports {} 1024
  let own := ((config.entries.find? (·.1 == _root_.Lake.libraryFacetAttr.ext.name)).map
    (·.2.size)).getD 0
  let text ← match ← (IO.FS.readFile package.configFile).toBaseIO with
    | .ok text => pure (some text)
    | .error _ => pure none
  let admitted := regulaFacetAdmitted text running own (config.constants.map (·.name))
  return (_root_.Lake.libraryFacetAttr.getAllEntries imported).size + own -
    if admitted then 1 else 0

/-- Whether no dependency can have replaced the `extraDep` facet of Regula's `lakefile.lean`: no
package other than the root declares a library facet other than Regula's own
(`otherLibraryFacets`). Lake inserts the root's facets before those of its dependencies
(`Lake/Load/Workspace.lean`, line 39), so a facet of the root replaces none that a dependency
declares. It is in effect only where no dependency declares one, and a record that it writes is
then the root configuration's own, which the incremental gate trusts as it trusts the traces Lake
recorded (`traceRecords_ownRecord_iff`). The unmarked build counts no record otherwise
(`Build.runObserved`). A failure to read a configuration counts as another facet. -/
def onlyRegulaFacets (ws : _root_.Lake.Workspace) : IO Bool := do
  try
    let running ← runningLakefile
    let dependencies := ws.packages.filter (!·.isRoot)
    return (← dependencies.mapM (otherLibraryFacets ws running)).all (· == 0)
  catch _ => return false

/-- The `extraDep` facet of a library that the workspace configures, `existing` (Lake's own,
`LeanLib.extraDepFacetConfig`, or one a package declares in its place), with the trace of the
library's `weakArgsRecord` mixed into its job's when the library belongs to the root package
(`Package.isRoot`). The job of `existing` runs for every library, so what it builds or writes is
kept. Lake mixes the trace of that facet's job into the dependency trace of each module of the
library (`Lake/Build/Module.lean`, line 591), which sets no option of the module's elaboration. -/
def weakArgsExtraDep
    (existing : _root_.Lake.LibraryFacetConfig _root_.Lake.LeanLib.extraDepFacet) :
    _root_.Lake.LibraryFacetConfig _root_.Lake.LeanLib.extraDepFacet :=
  _root_.Lake.mkFacetJobConfig (buildable := existing.buildable) (memoize := existing.memoize)
    fun (library : _root_.Lake.LeanLib) => do
      let job : _root_.Lake.Job Unit ← existing.run library
      if !library.pkg.isRoot then return job
      let caption := weakArgsCaption library
      let trace := _root_.Lake.BuildTrace.ofHash (_root_.Lake.pureHash caption) caption
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
  /-- The most significant action Lake recorded for the job (`JobState.action`): `build` when it
  ran a build action, such as a module's elaboration, and `replay` when it replayed the log of an
  earlier one from a trace. -/
  action : _root_.Lake.JobAction := .unknown
  deriving Inhabited

/-- Whether `jobs` show that Lake elaborated `module` in this build: some job has the caption Lake
gives a module's job, its name (`Module.recBuildLean`, `Lake/Build/Module.lean` line 1005), and
each such job ran a build action. Lake resets a job's action when it registers the job
(`JobState.renew`, `Lake/Build/Job/Register.lean` lines 20 and 44), so the action of a module's job
is that of its own work, and that job runs a build action only to elaborate the module
(`Module.buildLean`).

Assumes: in Lake v4.34.1 a module's job is the only job captioned with its name that records a
build action, and records one exactly when the build elaborated the module. -/
def elaboratedIn (jobs : Array JobLog) (module : Name) : Bool :=
  let named := jobs.filter (·.caption == module.toString)
  !named.isEmpty && named.all (·.action == .build)

/-- The modules of `claimed` whose result in a build that does not settle replayed logs (`settled`
false) rests on the log of an elaboration from before this audit invocation whose weak arguments
are not known: Lake elaborated none of them in this build (`elaboratedIn`), nor did an earlier
build of the same audit invocation (`earlier`), and the trace whose log the build replayed does not
record a current record of the module's own library (`recorded`, `traceRecords_ownRecord_iff`).
Lake's module trace records the `weakLeanArgs` an elaboration ran under only through an `extraDep`
facet that mixes them in, such as the one Regula's `lakefile.lean` declares, so without that record
a clean log can come from weak arguments since removed, and its RG2003 result is not established.
A build under the audit-build marker settles them, since its own facet records them
(`weakArgsExtraDep`). A record counts only as written by Regula's facet when the module was built,
the trust in recorded traces that `traceRecords_ownRecord_iff` assumes.
-/
def reusedModules (settled : Bool) (earlier recorded : Array Name) (jobs : Array JobLog)
    (claimed : Array Name) : Array Name :=
  if settled then #[] else claimed.filter fun module => !earlier.contains module &&
    !recorded.contains module && !elaboratedIn jobs module

/-- A module is reused exactly when the build does not settle replayed logs, the module is
claimed, no earlier build of this audit invocation elaborated it, its replayed trace does not
record its weak arguments, and either no job of the build is captioned with its name or one such
job ran no build action. -/
theorem mem_reusedModules_iff (settled : Bool) (earlier recorded : Array Name)
    (jobs : Array JobLog) (claimed : Array Name) (module : Name) :
    module ∈ reusedModules settled earlier recorded jobs claimed ↔
      settled = false ∧ module ∈ claimed ∧ module ∉ earlier ∧ module ∉ recorded ∧
        ((∀ job ∈ jobs, job.caption ≠ module.toString) ∨
          ∃ job ∈ jobs, job.caption = module.toString ∧ job.action ≠ .build) := by
  cases settled
  · have hAll : ((jobs.filter (·.caption == module.toString)).all
        (·.action == .build)) = false ↔
        ∃ job ∈ jobs, job.caption = module.toString ∧ job.action ≠ .build := by
      rw [← Bool.not_eq_true, Array.all_eq_true_iff_forall_mem]
      simp [Array.mem_filter]
    simp only [reusedModules, elaboratedIn, Bool.false_eq_true, ite_false, Array.mem_filter,
      Bool.and_eq_true, Bool.not_eq_true', true_and, Bool.and_eq_false_iff, Bool.not_eq_false',
      Array.isEmpty_iff, Array.filter_eq_empty_iff, hAll, beq_iff_eq, ne_eq]
    rw [Bool.eq_false_iff, ne_eq, Array.contains_iff_mem, and_assoc, Bool.eq_false_iff, ne_eq,
      Array.contains_iff_mem]
  · simp [reusedModules]

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
so `record` holds exactly the logs Lake's monitor judges. A registered job's log is read from its
completed task, after Lake's own capture of its standard output and error (`Job.async`,
`Lake/Build/Job/Monad.lean` line 173) has added its entry. The job that runs the build is also
captured that way (`Workspace.startBuild`, `Lake/Build/Run.lean` line 363), but only after this
returns, so this runs `build` under the same capture (`withLoggedIO`, `Lake/Util/Log.lean` line
437) and records that job's log afterwards: the rest of this writes nothing to standard output or
error, so Lake's capture adds no entry. A module of the build whose messages
`unparsedCompilerOutput_ofSerialMessage` does not cover (`Workspace.lineBreakSourcePaths`) is
logged as an error of the job that runs the build, which fails it. -/
def observedFetch (ws : _root_.Lake.Workspace) (record : IO.Ref (Array JobLog))
    (build : _root_.Lake.FetchM (_root_.Lake.Job Unit)) :
    _root_.Lake.FetchM (_root_.Lake.Job Unit) :=
  _root_.Lake.FetchM.ofFn fun fetch pkg? stack store context log => do
    let own ← IO.mkRef #[]
    let result ← (_root_.Lake.withLoggedIO build).toFn fetch pkg? stack store
      { context with registeredJobs := own } log
    let mut jobs ← forwardJobs own context.registeredJobs #[]
    if let .ok job _ := result then
      discard <| IO.wait job.task
      jobs ← forwardJobs own context.registeredJobs jobs
    let lineBreaks := Workspace.lineBreakSourcePaths ws (← store.get)
    let addErrors (log : _root_.Lake.Log) := lineBreaks.foldl (init := log) fun log reason =>
      log.push (.error s!"{reason}, so its log cannot tell those messages from other output of \
        the compiler")
    let result := match result with
      | .ok job log => .ok job (addErrors log)
      | .error position log => .error position (addErrors log)
    let ownLog := match result with
      | .ok _ log => log
      | .error _ log => log
    record.set <| (jobs.map fun job => {
        caption := job.caption, optional := job.optional,
        entries := job.task.get.state.log.entries,
        action := job.task.get.state.action : JobLog }).push
      { caption := "the build's computation", optional := false, entries := ownLog.entries }
    return result

/-- The result of a build that `Build.runObserved` ran. -/
structure CheckedBuild where
  /-- The build's exit code and output. Lake's build monitor failed the build, and
  `Build.runObserved` exited 1, when a required job logged an entry at the build's failure level
  or above. -/
  process : ProcessResult
  /-- The failure level the build ran at (`Build.failLv`). -/
  failLv : _root_.Lake.LogLevel
  /-- The log of each job that Lake's build monitor judged (`observedFetch`). -/
  jobs : Array JobLog
  /-- Whether the build set Lean options on the root package (`Build.rootOptions`), the audit
  build's marker among them, so that its libraries take their `extraDep` facet from
  `weakArgsExtraDep`. -/
  marked : Bool
  /-- The modules of the build's claimed targets (`surfaceRequest`). -/
  claimed : Array Name
  /-- The modules that an earlier build of the same audit invocation elaborated (`Elaborated`). -/
  earlier : Array Name
  /-- The claimed modules whose trace file, read after the build, records a current record of the
  module's own library among its inputs (`traceRecords_ownRecord_iff`), when no dependency
  declares a library facet other than Regula's (`onlyRegulaFacets`); none otherwise. -/
  recorded : Array Name := #[]

/-- Each entry of a job of `build` that is not optional which Lake can have made from compiler
output that is not a Lean message (`unparsedOutput`), such as a warning whose line other output
corrupted, which Lake logs as information. -/
def CheckedBuild.unparsed (build : CheckedBuild) : Array String :=
  unparsedOutput build.jobs

/-- The claimed modules of `build` whose RG2003 result is not established: the build has no
audit-build marker, and it replayed their clean log from an elaboration before the audit whose
trace does not record the current weak arguments of the module's own library (`reusedModules`),
or a dependency declares a library facet other than Regula's (`onlyRegulaFacets`). Every
checked build decides this, whatever reads its output. A build in a fresh copy elaborates each
claimed module itself, so it has none. -/
def CheckedBuild.reused (build : CheckedBuild) : Array Name :=
  reusedModules build.marked build.earlier build.recorded build.jobs build.claimed

/-- The claimed modules that the builds of one audit invocation elaborated (`elaboratedIn`). The
audit creates it at its entry and passes it to each of its builds, so a later build of the same
audit that replays their logs rests on that elaboration. No other audit reads it. -/
abbrev Elaborated := IO.Ref (Array Name)

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
def Build.runObserved (build : Build) (repo : FilePath) (targets : Array Target)
    (elaborated : Option Elaborated := none) : IO CheckedBuild := do
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← showingStream (IO.FS.Stream.ofBuffer buffer) build.display
  let searchPath ← Lean.searchPathRef.get
  let workingDirectory ← IO.currentDir
  let jobLogs ← IO.mkRef (#[] : Array JobLog)
  let marked ← IO.mkRef false
  let claimed ← IO.mkRef (#[] : Array Name)
  let earlier ← IO.mkRef (#[] : Array Name)
  let recorded ← IO.mkRef (#[] : Array Name)
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
        marked.set rootOptions.isSome
        claimed.set (modules.map (·.name))
        if let some elaborated := elaborated then earlier.set (← elaborated.get)
        Workspace.dropRestoredTraces ws
        -- A record counts only when no dependency declares a library facet that can replace
        -- Regula's `extraDep` facet; the marked build settles replayed logs without one.
        let recordsOwn ← if rootOptions.isSome then pure false else onlyRegulaFacets ws
        let (ws, leanOptOverrides) ← match rootOptions with
          | some options =>
            let some existing := ws.findLibraryFacetConfig? _root_.Lake.LeanLib.extraDepFacet
              | throw <| IO.userError "the workspace configures no `extraDep` facet of a library"
            pure (ws.addLibraryFacetConfig (weakArgsExtraDep existing),
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
          if recordsOwn && text.any (Workspace.traceRecords (ownRecord mod.lib)) then
            recorded.modify (·.push mod.name)
        let jobs ← jobLogs.get
        if let some elaborated := elaborated then
          elaborated.modify (· ++ (modules.map (·.name)).filter (elaboratedIn jobs))
      pure (0 : UInt32)
    catch error =>
      out.putStrLn s!"error: {error}"
      pure 1
    finally
      Lean.searchPathRef.set searchPath
      IO.Process.setCurrentDir workingDirectory
  let observed (process : ProcessResult) : IO CheckedBuild := do
    let jobs ← jobLogs.get
    let marked ← marked.get
    let claimed ← claimed.get
    let earlier ← earlier.get
    let recorded ← recorded.get
    return { process, failLv := build.failLv, jobs, marked, claimed, earlier, recorded }
  let some stdout := String.fromUTF8? (← buffer.get).data
    | observed { exitCode := 1, stdout := "", stderr := "error: build output is not UTF-8" }
  observed { exitCode, stdout, stderr := "" }

/-- The process result of `Build.runObserved`. -/
def Build.run (build : Build) (repo : FilePath) (targets : Array Target) : IO ProcessResult :=
  (·.process) <$> build.runObserved repo targets

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

/-- Build the claimed Lake targets and require success with no warnings: the build runs with
Lake's failure level at `warning`, so it succeeds only when no required job logged a warning or an
error. Lake gives each message of a module's elaboration the level of its Lean severity
(`LogLevel.ofMessageSeverity`), so an information message, whatever its text, never fails the
build. The build is also refused when a job that Lake's build monitor judged holds an entry Lake
can have made from compiler output that is not a Lean message (`CheckedBuild.unparsed`), since Lake
logs it as information whatever it held. When the build has no audit-build marker, a claimed
module whose log it replayed from an elaboration before the audit, under weak arguments that its
trace does not record (`CheckedBuild.reused`), has no established result, and each such module is
reported. `elaborated` holds the modules that earlier builds of the same audit elaborated, and
the build adds its own. The output is read only to report a failure. Returns the diagnostic lines
to report on failure. -/
def buildCheckedObservation (repo : FilePath) (targets : Array SurfaceTarget)
    (mode : String) (build : Build := buildTargets) (elaborated : Option Elaborated := none) :
    IO (CheckedBuild × Option (Array String)) := do
  let build ← Build.runObserved { build with failLv := .warning } repo (targets.map .surface)
    elaborated
  let process := build.process
  if process.succeeded && build.unparsed.isEmpty && build.reused.isEmpty then
    return (build, none)
  if process.succeeded && build.unparsed.isEmpty then
    return (build, some (#[s!"FAIL[build-reused]: the claimed build {mode} without Regula's \
        audit-build marker reused the log of an elaboration from before this run for each \
        module below, and its trace does not record the current `weakLeanArgs` of the module's \
        library. Lake's own module trace omits them, and only the `extraDep` facet of Regula's \
        `lakefile.lean` records them, so that log can come from weak arguments since removed, \
        and the module's result is not established. A record counts only when no dependency \
        declares a library facet other than Regula's, since one can replace Regula's. A build \
        with the marker (`lake lint` without REGULA_ORDINARY_LAKEFILES=1) or a fresh audit \
        elaborates it again."] ++
      build.reused.map (s!"not established: {·}")))
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
