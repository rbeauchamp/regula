import Regula.Checker.Common
import Regula.Checker.Manifest
import Regula.Checker.Workspace
import RegulaCore.EditorPolicy
import Regula.Contract
import Regula.Decision
import Lake.CLI.Build
import Lake.Load.Lean.Elab

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

/-- Exact source locations already discovered through Lake for root-package
modules. Reuse these for frontend history instead of a module-prefix search. -/
def SurfaceInventory.moduleSources (inventory : SurfaceInventory) : Array (Name × FilePath) :=
  inventory.libraries.flatMap (fun library => library.sources.map fun source =>
    (source.«module», source.source)) ++
    inventory.executables.map (fun executable => (executable.root, executable.source))

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

/-- Obtain every root-package Lean library and executable, exact module, and
exact source from Lake's own elaborated package model. This loads the checked
project's workspace in-process, so `lakefile.lean` and `lakefile.toml`
projects share one discovery path and need no custom Lake facets. -/
def surfaceInventory (repo : FilePath) : IO SurfaceInventory :=
  Workspace.withRootWorkspace repo fun ws => do
    let pkg := ws.root
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
    let leanPath := #[leanLibDir] ++ ws.leanPath.toArray
    let leanSrcPath := ws.leanSrcPath.toArray
    let dependencies ← (ws.packages.extract 1 ws.packages.size).mapM fun package => do
      let names ← IO.mkRef ({} : NameSet)
      for library in package.leanLibs do
        for name in ← buildableModules library do
          names.modify (·.insert name)
      let mut sources := #[]
      for name in (← names.get).toArray.qsort Name.quickLt do
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
      pure
          ({ package := package.baseName.toString, root, sources, configurationPaths } :
              DependencyInventory)
    let root ← IO.FS.realPath repo
    return { root, leanLibDir, leanPath, leanSrcPath, libraries, executables, dependencies }

/-- Build the targets with the inherited Lean search paths removed, so the
build resolves modules only through the workspace being built. -/
def buildTargets (repo : FilePath) (targets : Array String) : IO ProcessResult :=
  runProcess repo "lake" (#["build"] ++ targets) scrubbedLeanPathEnv

/-- `buildTargets`, also showing Lake's own progress line for each job (`isLakeProgressLine`) as
the build runs; the captured output is the same. -/
def buildTargetsShowing (repo : FilePath) (targets : Array String) : IO ProcessResult :=
  runProcessShowing repo "lake" (#["build"] ++ targets) scrubbedLeanPathEnv isLakeProgressLine

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

/-- The module whose import loads Regula's local feedback: it registers the linter and the module
hook with `initialize`, and it is the only module of Regula that reads the marker of
`auditLeanOptions`. That it is Regula's only reader is checked by inspection. A project module that
reads the option from its own import-time options would read the marker too; the equal verdicts of
the plain shape assume that none does. -/
def linterModule : Name := `Regula.Linter

/-- The kind of a target that a package declares, or of the target that a `needs` entry names,
as the plain shape reads it. -/
inductive TargetKind where
  /-- A `lean_lib`. -/
  | leanLib
  /-- A `lean_exe`. -/
  | leanExe
  /-- An `input_file`, which Lake only reads and hashes. -/
  | inputFile
  /-- An `input_dir`, which Lake only reads and hashes. -/
  | inputDir
  /-- Any other declaration (a custom `target`, an `extern_lib`, an unknown kind), or a `needs`
  entry that names no target of its own package. -/
  | other
  deriving DecidableEq, Repr

/-- The fields of a target's configuration that the plain shape lets differ from Lake's default:
the source directory, roots and globs of a library, the root, file name and interpreter support
of an executable, `needs` and Lean options of both, and the path and text mode of an input target.
Lake's build runs no code from any of them. -/
def TargetKind.fields : TargetKind → List Name
  | .leanLib => [`srcDir, `roots, `globs, `needs, `leanOptions]
  | .leanExe => [`srcDir, `root, `exeName, `needs, `supportInterpreter, `leanOptions]
  | .inputFile | .inputDir => [`path, `text]
  | .other => []

/-- The fields of a package's configuration that the plain shape lets differ from Lake's default:
the source directory, Lean options, the lint and test drivers, and the package's metadata. Lake's
build runs no code from any of them. -/
def packageFields : List Name :=
  [`srcDir, `leanOptions, `lintDriver, `lintDriverArgs, `testDriver, `testDriverArgs, `version,
    `versionTags, `description, `keywords, `homepage, `license, `licenseFiles, `readmeFile,
    `reservoir]

/-- What the plain shape reads of one target of a package. -/
structure TargetShape where
  /-- The kind of the target. -/
  kind : TargetKind
  /-- Each field of the target's configuration that Regula does not show to have Lake's default
  value. -/
  unknown : Array Name
  /-- The kind of the target that each `needs` entry of a library or an executable names. -/
  needs : Array TargetKind

/-- A target of the plain shape: a `lean_lib`, `lean_exe`, `input_file` or `input_dir` that has
Lake's default value in each field outside `TargetKind.fields`, and whose `needs` entries each
name an `input_file` or an `input_dir` of its package. -/
def TargetShape.Plain (target : TargetShape) : Prop :=
  target.kind ≠ .other ∧ (∀ field ∈ target.unknown, field ∈ target.kind.fields) ∧
    ∀ kind ∈ target.needs, kind = .inputFile ∨ kind = .inputDir

/-- A declaration of a package's compiled configuration file, as the plain shape reads it. -/
inductive ConfigDeclaration where
  /-- A definition whose type is one of Lake's configuration types (`configurationTypes`). -/
  | configuration
  /-- A theorem or an axiom whose statement is a `Lake.FamilyDef` or an equation between types, as
  Lake's commands generate. A compiler replacement (`csimp`) is an equation between functions, so
  it is not one. -/
  | typeFact
  /-- Any other declaration. -/
  | other
  deriving DecidableEq, Repr

/-- The environment extensions whose entries a compiled configuration file of the plain shape may
have: those that Lake's commands and the compilation of their declarations fill, as in Regula's own
configuration files at the pinned Lean. Any other extension, such as that of `csimp`,
`implemented_by`, `extern`, `init` or a documentation comment, is not plain. -/
def configExtensions : List String :=
  ["Lean.declRangeExt", "_private.Lean.Namespace.0.Lean.namespacesExt", "reducibilityCore",
    "Lean.Compiler.inlineAttrs", "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
    "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt", "Lean.Meta.instanceExtension",
    "Lean.IR.declMapExt", "_private.Lean.ExtraModUses.0.Lean.extraModUses",
    "Lean.Compiler.LCNF.baseExt", "Lean.Compiler.LCNF.monoExt", "Lean.Compiler.LCNF.impureSigExt",
    "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "Lean.deprecatedModuleExt",
    "Lean.Meta.simpExtension", "Lean.Linter.deprecatedAttr", "symbolFrequency", "sineQueNon",
    "Lake.packageAttr", "Lake.packageDepAttr", "Lake.leanLibAttr", "Lake.leanExeAttr",
    "Lake.inputFileAttr", "Lake.inputDirAttr", "Lake.targetAttr", "Lake.defaultTargetAttr"]

/-- What the plain shape reads of one package of the workspace. -/
structure PackageShape where
  /-- Each field of the package's configuration that Regula does not show to have Lake's default
  value. -/
  unknown : Array Name
  /-- Each target that the package declares. -/
  targets : Array TargetShape
  /-- The number of facets that the package's configuration file declares, new or in place of
  one of Lake's; `none` when Regula cannot read it. -/
  facets : Option Nat
  /-- Each declaration of the package's compiled configuration file; none for a `lakefile.toml`. -/
  declarations : Array ConfigDeclaration
  /-- Each environment extension with entries of the compiled configuration file itself; none for
  a `lakefile.toml`. -/
  extensions : Array String

/-- A package of the plain shape: it has Lake's default value in each field outside
`packageFields`, each of its targets is of the plain shape, its configuration file declares no
facet, each declaration of its compiled configuration file is a `configuration` or a `typeFact`,
and each extension with entries of that file is one of `configExtensions`. In a workspace of such
packages, a build of `lean_lib` and `lean_exe` targets runs no custom build step: it compiles
modules and reads and hashes input files. -/
def PackageShape.Plain (shape : PackageShape) : Prop :=
  (∀ field ∈ shape.unknown, field ∈ packageFields) ∧ (∀ target ∈ shape.targets, target.Plain) ∧
    shape.facets = some 0 ∧ (∀ declaration ∈ shape.declarations, declaration ≠ .other) ∧
    ∀ extension ∈ shape.extensions, extension ∈ configExtensions

/-- Whether `kind` is one of the two input kinds. -/
def TargetKind.input : TargetKind → Bool
  | .inputFile | .inputDir => true
  | _ => false

/-- `TargetKind.input` holds exactly for the two input kinds. -/
theorem TargetKind.input_iff (kind : TargetKind) :
    kind.input = true ↔ kind = .inputFile ∨ kind = .inputDir := by
  cases kind <;> simp [input]

/-- The test of `TargetShape.Plain` (`TargetShape.plain_iff`). -/
def TargetShape.plain (target : TargetShape) : Bool :=
  target.kind != .other && target.unknown.all (target.kind.fields.contains ·) &&
    target.needs.all TargetKind.input

/-- `TargetShape.plain` decides `TargetShape.Plain`. -/
theorem TargetShape.plain_iff (target : TargetShape) : target.plain = true ↔ target.Plain := by
  simp only [plain, Plain, Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true',
    List.contains_iff_mem, TargetKind.input_iff, and_assoc]

/-- The test of `PackageShape.Plain` (`PackageShape.plain_iff`). -/
def PackageShape.plain (shape : PackageShape) : Bool :=
  shape.unknown.all (packageFields.contains ·) && shape.targets.all TargetShape.plain &&
    shape.facets == some 0 && shape.declarations.all (· != .other) &&
    shape.extensions.all (configExtensions.contains ·)

/-- `PackageShape.plain` decides `PackageShape.Plain`. -/
theorem PackageShape.plain_iff (shape : PackageShape) : shape.plain = true ↔ shape.Plain := by
  simp only [plain, Plain, Bool.and_eq_true, Array.all_eq_true', List.contains_iff_mem,
    TargetShape.plain_iff, beq_iff_eq, bne_iff_ne, ne_eq, and_assoc]

/-- A module of the root package as the driver reads it: the source file that each of the
package's libraries and executables gives the name, the source file of the module that Lake
resolves the name to, and the modules that Lake reports it imports transitively. -/
structure ModuleEntry where
  /-- The module's name. -/
  name : Name
  /-- The real path of the source file that each library and each executable of the root package
  gives the name. -/
  sources : Array String
  /-- The real path of the source file of the module that Lake resolves the name to, if that
  module is of the root package. -/
  resolved : Option String
  /-- The modules that Lake's `transImports` facet reports for the name. -/
  imports : Array Name

/-- A module that Lake resolves to the one source file that the root package gives it. -/
def ModuleEntry.Resolved (entry : ModuleEntry) : Prop :=
  ∀ source ∈ entry.sources, entry.resolved = some source

/-- The test of `ModuleEntry.Resolved` (`ModuleEntry.resolvedTest_iff`). -/
def ModuleEntry.resolvedTest (entry : ModuleEntry) : Bool :=
  entry.sources.all (entry.resolved == some ·)

/-- `ModuleEntry.resolvedTest` decides `ModuleEntry.Resolved`. -/
theorem ModuleEntry.resolvedTest_iff (entry : ModuleEntry) :
    entry.resolvedTest = true ↔ entry.Resolved := by
  simp only [resolvedTest, Resolved, Array.all_eq_true', beq_iff_eq]

/-- What the `lint` driver reads of the workspace before its claimed build: the shape of each
package, and each module that the root package owns. Lake applies the root package's Lean options
to the modules that package owns: the buildable modules of its libraries and the roots of its
executables. -/
structure MarkerInputs where
  /-- The shape of each package of the workspace (`packageShape`). -/
  packages : Array PackageShape
  /-- Each buildable module of the root package's libraries (`buildableModules`) and each root of
  its executables (`moduleEntries`). -/
  modules : Array ModuleEntry

/-- Whether the `lint` driver's claimed build passes `auditLeanOptions`: a package is not
`PackageShape.Plain`, or a module of the root package is not `ModuleEntry.Resolved` or imports
`linterModule`, directly or transitively (`auditMarkerNeeded_iff`). -/
@[regula_decision]
def auditMarkerNeeded (inputs : MarkerInputs) : Bool :=
  !(inputs.packages.all PackageShape.plain) ||
    inputs.modules.any fun entry => !entry.resolvedTest || entry.imports.contains linterModule

/-- `auditMarkerNeeded` asks for the marker exactly when a package is not of the plain shape, or
a module of the root package is not resolved to its one source or has the linter's module among
its imports. -/
theorem auditMarkerNeeded_iff (inputs : MarkerInputs) :
    auditMarkerNeeded inputs = true ↔
      ¬ (∀ shape ∈ inputs.packages, shape.Plain) ∨
        ∃ entry ∈ inputs.modules, ¬ entry.Resolved ∨ linterModule ∈ entry.imports := by
  have plain : inputs.packages.all PackageShape.plain = true ↔
      ∀ shape ∈ inputs.packages, shape.Plain := by
    simp only [Array.all_eq_true', PackageShape.plain_iff]
  have modules : (inputs.modules.any fun entry =>
        !entry.resolvedTest || entry.imports.contains linterModule) = true ↔
      ∃ entry ∈ inputs.modules, ¬ entry.Resolved ∨ linterModule ∈ entry.imports := by
    simp only [Array.any_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      ModuleEntry.resolvedTest_iff, Array.contains_iff_mem]
    constructor
    · rintro ⟨i, bound, holds⟩
      exact ⟨inputs.modules[i], Array.getElem_mem bound, holds⟩
    · rintro ⟨entry, entered, holds⟩
      obtain ⟨i, bound, rfl⟩ := Array.getElem_of_mem entered
      exact ⟨i, bound, holds⟩
  rw [auditMarkerNeeded, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, plain,
    modules]

/-- `auditMarkerNeeded` is a sound and complete decision of "a package is not of the plain shape,
or a module of the root package is not resolved to its one source or imports the linter's module"
(`auditMarkerNeeded_iff`): it asks for the marker for a package whose facets it cannot read, and
not for an empty workspace. The specification is a statement about fields, kinds and membership;
it names no test of the implementation. It does not establish that `linterModule` is the only
reader of the marker, nor that the inputs describe the workspace: the first is checked by
inspection, and the second rests on `markerInputs`, Lake's configuration, its compiled
configuration files and its `transImports` facet. -/
theorem checked_auditMarkerNeeded : Regula.ExecutableContract auditMarkerNeeded
    (Regula.Decides (· = true) fun inputs : MarkerInputs =>
      ¬ (∀ shape ∈ inputs.packages, shape.Plain) ∨
        ∃ entry ∈ inputs.modules, ¬ entry.Resolved ∨ linterModule ∈ entry.imports) :=
  ⟨Regula.Decides.of_iff auditMarkerNeeded_iff
    ⟨⟨#[⟨#[], #[], none, #[], #[]⟩], #[]⟩, (auditMarkerNeeded_iff _).mpr
      (.inl fun plain => by
        have facets := (plain ⟨#[], #[], none, #[], #[]⟩ (by simp)).2.2.1
        simp at facets)⟩
    ⟨⟨#[], #[]⟩, fun accepted => by
      rcases (auditMarkerNeeded_iff _).mp accepted with notPlain | ⟨_, member, _⟩
      · exact notPlain fun _ member => by simp at member
      · simp at member⟩⟩

/-- Lake reads an explicit `+module` with `String.toName` and splits facets at `:`.
Use that spelling, with `facet`, only when it retains the exact discovered root name, as for
`moduleArtifactsTarget?`. -/
def moduleFacetTarget? (root : Name) (facet : String) : Option String :=
  let spelling := root.toString (escape := false)
  if spelling.toName = root ∧ spelling.contains ':' = false then
    some s!"+{spelling}:{facet}"
  else none

/-- Each of `modules`, in that order, with the modules that it imports transitively in `ws`, as
Lake's `transImports` facet reports them through its query API (`Lake.querySpecs`, the form of
`lake query --json`): the modules of the workspace's packages, not those of the toolchain. The
facet reads module headers and builds nothing. `none` when a module has no query target, Lake
does not resolve one, Lake cannot read the imports, or a result is not an array of module
names. -/
def moduleImports (ws : _root_.Lake.Workspace) (modules : Array Name) :
    IO (Option (Array (Name × Array Name))) := do
  let some targets := modules.mapM (moduleFacetTarget? · "transImports") | return none
  let .ok specs ← (_root_.Lake.parseTargetSpecs ws targets.toList).toBaseIO | return none
  -- Lake's own report of a header it cannot read is the build's to show: the build that follows
  -- reads the same headers.
  let discarded ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let answers ← try
      ws.runBuild (_root_.Lake.querySpecs specs .json)
        { out := .stream (IO.FS.Stream.ofBuffer discarded), ansiMode := .noAnsi }
    catch _ => return none
  unless answers.size == modules.size do return none
  return (modules.zip answers).mapM fun (name, answer) => do
    let imports ← (Json.parse answer >>= fromJson? (α := Array Name)).toOption
    pure (name, imports)

/-- The kind of a declaration from its Lake kind name. -/
def declarationKind (kind : Name) : TargetKind :=
  if kind == _root_.Lake.LeanLib.configKind then .leanLib
  else if kind == _root_.Lake.LeanExe.configKind then .leanExe
  else if kind == _root_.Lake.InputFile.configKind then .inputFile
  else if kind == _root_.Lake.InputDir.configKind then .inputDir
  else .other

/-- The kind of the target that the `needs` entry `key` of a library or an executable of
`package` names: a target of `package` written `@/NAME` or `@PACKAGE/NAME`, with no facet. Every
other entry, such as a module, a facet or a target of another package, is `other`. -/
def needKind (package : _root_.Lake.Package) (key : _root_.Lake.PartialBuildKey) : TargetKind :=
  match key with
  | .packageTarget owner target =>
      if owner.isAnonymous || owner == package.baseName || owner == package.keyName then
        match package.targetDecls.find? (·.name == target) with
        | some declaration => declarationKind declaration.kind
        | none => .other
      else .other
  | _ => .other

/-- The canonical fields that Lake lists for a configuration type (`Lake.ConfigFields`) that
`checks` does not show to have Lake's default value: each field with no test in `checks`, and each
whose test is `false`. A field that Lake adds in another release has no test, so it is listed. -/
def unknownFields (fields : Array _root_.Lake.ConfigFieldInfo) (checks : List (Name × Bool)) :
    Array Name :=
  fields.filterMap fun field =>
    if field.canonical && checks.lookup field.name != some true then some field.name else none

/-- The tests against Lake's defaults of the fields of `LeanConfig`, which a package, a library and
an executable share. `leanOptions` has no test. -/
def leanConfigChecks (config : _root_.Lake.LeanConfig) : List (Name × Bool) :=
  [(`buildType, config.buildType == .release), (`moreLeanArgs, config.moreLeanArgs.isEmpty),
    (`weakLeanArgs, config.weakLeanArgs.isEmpty), (`moreLeancArgs, config.moreLeancArgs.isEmpty),
    (`moreServerOptions, config.moreServerOptions.isEmpty),
    (`weakLeancArgs, config.weakLeancArgs.isEmpty), (`moreLinkObjs, config.moreLinkObjs.isEmpty),
    (`moreLinkLibs, config.moreLinkLibs.isEmpty), (`moreLinkArgs, config.moreLinkArgs.isEmpty),
    (`weakLinkArgs, config.weakLinkArgs.isEmpty), (`backend, config.backend == .default),
    (`platformIndependent, config.platformIndependent.isNone),
    (`dynlibs, config.dynlibs.isEmpty), (`plugins, config.plugins.isEmpty),
    (`requiresModuleSystem, !config.requiresModuleSystem),
    (`allowNonModules, !config.allowNonModules)]

/-- The tests against Lake's defaults of the fields of a package's configuration. The fields of
`packageFields` have no test. -/
def packageChecks {key origin : Name} (config : _root_.Lake.PackageConfig key origin) :
    List (Name × Bool) :=
  leanConfigChecks config.toLeanConfig ++
    [(`bootstrap, !config.bootstrap), (`extraDepTargets, config.extraDepTargets.isEmpty),
      (`precompileModules, !config.precompileModules),
      (`moreGlobalServerArgs, config.moreGlobalServerArgs.isEmpty),
      (`buildDir, decide (config.buildDir = _root_.Lake.defaultBuildDir)),
      (`leanLibDir, decide (config.leanLibDir = _root_.Lake.defaultLeanLibDir)),
      (`nativeLibDir, decide (config.nativeLibDir = _root_.Lake.defaultNativeLibDir)),
      (`binDir, decide (config.binDir = _root_.Lake.defaultBinDir)),
      (`irDir, decide (config.irDir = _root_.Lake.defaultIrDir)),
      (`releaseRepo, config.releaseRepo.isNone), (`buildArchive, config.buildArchive.isNone),
      (`preferReleaseBuild, !config.preferReleaseBuild),
      (`enableArtifactCache?, config.enableArtifactCache?.isNone),
      (`restoreAllArtifacts?, config.restoreAllArtifacts?.isNone),
      (`libPrefixOnWindows, !config.libPrefixOnWindows),
      (`allowImportAll, !config.allowImportAll), (`builtinLint?, config.builtinLint?.isNone),
      (`fixedToolchain, !config.fixedToolchain),
      (`packagesDir, decide (config.packagesDir = _root_.Lake.defaultPackagesDir))]

/-- The tests against Lake's defaults of the fields of a library's configuration;
`nativeFacets` is the given reading of the compiled configuration (`leanConfigReading`). The
fields of `TargetKind.fields` have no test. -/
def libraryChecks {name : Name} (config : _root_.Lake.LeanLibConfig name) (nativeFacets : Bool) :
    List (Name × Bool) :=
  leanConfigChecks config.toLeanConfig ++
    [(`libName, config.libName.isEmpty), (`libPrefixOnWindows, !config.libPrefixOnWindows),
      (`extraDepTargets, config.extraDepTargets.isEmpty),
      (`precompileModules, !config.precompileModules),
      (`defaultFacets, config.defaultFacets == #[_root_.Lake.LeanLib.leanArtsFacet]),
      (`nativeFacets, nativeFacets), (`allowImportAll, !config.allowImportAll)]

/-- The tests against Lake's defaults of the fields of an executable's configuration;
`nativeFacets` is the given reading of the compiled configuration (`leanConfigReading`). The
fields of `TargetKind.fields` have no test. -/
def executableChecks {name : Name} (config : _root_.Lake.LeanExeConfig name)
    (nativeFacets : Bool) : List (Name × Bool) :=
  leanConfigChecks config.toLeanConfig ++
    [(`extraDepTargets, config.extraDepTargets.isEmpty), (`nativeFacets, nativeFacets)]

/-- Lake's default `nativeFacets` as a configuration file elaborates it at the pinned Lake,
`fun shouldExport => #[if shouldExport then Module.oExportFacet else Module.oFacet]`, with a
metavariable in place of each of its two proofs that the facet's output is a file path. -/
def defaultNativeFacetsTerm : Expr :=
  let facetType := mkApp (.const ``_root_.Lake.ModuleFacet []) (.const ``System.FilePath [])
  let one : Level := .succ .zero
  let facet (name : Name) (proof : Nat) : Expr :=
    mkApp3 (.const ``_root_.Lake.ModuleFacet.mk []) (.const ``System.FilePath []) (.const name [])
      (.mvar ⟨.num `proof proof⟩)
  let choice := mkAppN (.const ``ite [one]) #[facetType,
    mkApp3 (.const ``Eq [one]) (.const ``Bool []) (.bvar 0) (.const ``Bool.true []),
    mkApp2 (.const ``instDecidableEqBool []) (.bvar 0) (.const ``Bool.true []),
    facet ``_root_.Lake.Module.oExportFacet 1, facet ``_root_.Lake.Module.oFacet 2]
  .lam `shouldExport (.const ``Bool []) (mkApp2 (.const ``List.toArray [.zero]) facetType
    (mkApp3 (.const ``List.cons [.zero]) facetType choice
      (mkApp (.const ``List.nil [.zero]) facetType))) .default

/-- Lake's `Pattern.star` for paths, the default filter of an `input_dir`, as a configuration file
elaborates it at the pinned Lake. -/
def starPatternTerm : Expr :=
  mkApp2 (.const ``_root_.Lake.Pattern.star [.zero, .zero]) (.const ``System.FilePath [])
    (.const ``_root_.Lake.PathPatDescr [])

/-- Whether `term` is the whole term `expected`, except that each metavariable of `expected`
stands for a constant that `theorems` names: a proof, which the compiler erases. Binder names are
not compared; everything else is. -/
def sameUpToProofs (theorems : NameSet) : Expr → Expr → Bool
  | .mvar _, term => match term with
    | .const name _ => theorems.contains name
    | _ => false
  | .app function argument, term => match term with
    | .app function' argument' =>
        sameUpToProofs theorems function function' && sameUpToProofs theorems argument argument'
    | _ => false
  | .lam _ type body info, term => match term with
    | .lam _ type' body' info' =>
        info == info' && sameUpToProofs theorems type type' && sameUpToProofs theorems body body'
    | _ => false
  | expected, term => expected == term

/-- Whether every target that the compiled configuration `config` declares is Lake's DSL form whose
function fields are Lake's defaults. Each tagged target is a constant of type `ConfigDecl` whose
value is `KConfigDecl.toConfigDecl` of a constant of the file, whose value is
`DSL.mkConfigDecl` of a configuration constant of the file. That constant is a `LeanLibConfig.mk`
or `LeanExeConfig.mk` whose `nativeFacets` is the whole term `defaultNativeFacetsTerm`, its proofs
aside (`sameUpToProofs` with the theorems of the file), an `InputDirConfig.mk` whose filter is the
whole term `starPatternTerm`, or an `InputFileConfig`. Any other term gives `false`; the positions
are those of Lake's constructors, and a term at another position is not one of these terms. -/
def defaultFunctionFields (config : ModuleData) : Bool :=
  let value? (name : Name) := (config.constants.find? (·.name == name)).bind (·.value?)
  let theorems : NameSet := config.constants.foldl (init := {}) fun names constant =>
    match constant with
    | .thmInfo _ => names.insert constant.name
    | _ => names
  config.constants.all fun constant =>
    constant.type != .const ``_root_.Lake.ConfigDecl [] || Option.isSome do
      let tagged ← constant.value?
      guard (tagged.isAppOfArity ``_root_.Lake.KConfigDecl.toConfigDecl 2)
      let declaration ← value? (← tagged.appArg!.constName?)
      guard (declaration.isAppOfArity ``_root_.Lake.DSL.mkConfigDecl 6)
      let name ← (declaration.getArg! 3).constName?
      let some configuration := config.constants.find? (·.name == name) | none
      let value ← configuration.value?
      match configuration.type.getAppFn.constName? with
      | some ``_root_.Lake.LeanLibConfig =>
          guard (value.isAppOfArity ``_root_.Lake.LeanLibConfig.mk 13 &&
            sameUpToProofs theorems defaultNativeFacetsTerm (value.getArg! 11))
      | some ``_root_.Lake.LeanExeConfig =>
          guard (value.isAppOfArity ``_root_.Lake.LeanExeConfig.mk 9 &&
            sameUpToProofs theorems defaultNativeFacetsTerm (value.getArg! 8))
      | some ``_root_.Lake.InputDirConfig =>
          guard (value.isAppOfArity ``_root_.Lake.InputDirConfig.mk 4 &&
            sameUpToProofs theorems starPatternTerm (value.getArg! 3))
      | some ``_root_.Lake.InputFileConfig => pure ()
      | _ => none

/-- Lake's configuration types: the types of the definitions that Lake's `package`, `require`,
`lean_lib`, `lean_exe`, `input_file` and `input_dir` commands generate, and that of the package's
name. -/
def configurationTypes : List Name :=
  [``_root_.Lake.PackageDecl, ``_root_.Lake.PackageConfig, ``_root_.Lake.Dependency,
    ``_root_.Lake.ConfigDecl, ``_root_.Lake.LeanLibDecl, ``_root_.Lake.LeanExeDecl,
    ``_root_.Lake.InputFileDecl, ``_root_.Lake.InputDirDecl, ``_root_.Lake.LeanLibConfig,
    ``_root_.Lake.LeanExeConfig, ``_root_.Lake.InputFileConfig, ``_root_.Lake.InputDirConfig,
    ``Lean.Name]

/-- The `ConfigDeclaration` of a declaration of a compiled configuration file: a definition whose
type's head is one of `configurationTypes`, a theorem or an axiom whose statement is a
`Lake.FamilyDef` or an equation in `Type`, or any other declaration. -/
def configDeclaration (constant : ConstantInfo) : ConfigDeclaration :=
  let typeFact := constant.type.isAppOf ``_root_.Lake.FamilyDef ||
    (constant.type.isAppOfArity ``Eq 3 && constant.type.getArg! 0 == .sort (.succ .zero))
  match constant with
  | .defnInfo _ =>
      if constant.type.getAppFn.constName?.any (configurationTypes.contains ·) then .configuration
      else .other
  | .thmInfo _ | .axiomInfo _ => if typeFact then .typeFact else .other
  | _ => .other

/-- What Regula reads of the compiled configuration file of a package. -/
structure ConfigReading where
  /-- The number of facets that the file declares; `none` when an import declares a target. -/
  facets : Option Nat
  /-- Whether its targets have Lake's default function fields (`defaultFunctionFields`). -/
  functions : Bool
  /-- The `ConfigDeclaration` of each declaration of the file. -/
  declarations : Array ConfigDeclaration
  /-- Each environment extension with entries of the file itself. -/
  extensions : Array String

/-- What Regula reads of the compiled configuration of a package whose configuration file is
`lakefile.lean` (`ConfigReading`). Lake keeps the compiled file at `.lake/config/<index>/` of the
workspace and imports its imports through `importModulesUsingCache`, which this reads again. The
facets are the entries of Lake's three facet attributes in the file and in its imports, which are
what Lake loaded. The declarations and the extensions are the file's own, so a registration of an
attribute whose scope ends in the file, which leaves no entry, still shows as its declaration. -/
def leanConfigReading (ws : _root_.Lake.Workspace) (package : _root_.Lake.Package) :
    IO ConfigReading := do
  let some file := package.configFile.fileName |
    return { facets := none, functions := false, declarations := #[], extensions := #[] }
  let compiled := ws.root.dir / _root_.Lake.defaultLakeDir / "config" / toString package.wsIdx /
    (FilePath.mk file).withExtension "olean"
  let (config, _) ← readModuleData compiled
  let imported ← _root_.Lake.importModulesUsingCache config.imports {} 1024
  let own (extension : Name) : Nat :=
    ((config.entries.find? (·.1 == extension)).map (·.2.size)).getD 0
  let facets := [_root_.Lake.moduleFacetAttr, _root_.Lake.packageFacetAttr,
    _root_.Lake.libraryFacetAttr].foldl (init := 0) fun count facetAttribute =>
      count + (facetAttribute.getAllEntries imported).size + own facetAttribute.ext.name
  return {
    facets := if (_root_.Lake.targetAttr.getAllEntries imported).isEmpty then some facets else none
    functions := defaultFunctionFields config
    declarations := config.constants.map configDeclaration
    extensions := config.entries.filterMap fun (extension, entries) =>
      if entries.isEmpty then none else some extension.toString }

/-- What the plain shape reads of a target of `package` (`TargetShape`). For a `lakefile.lean`,
`functions` is the reading of its compiled configuration (`leanConfigReading`). For a
`lakefile.toml` (`toml`), Lake's TOML loader never sets `nativeFacets`, and it gives an `input_dir`
Lake's `Pattern.star`, which is named `star`, only for an omitted filter or `"*"`; it gives every
other filter `Pattern.ofDescr`, which has no name. -/
def targetShape (package : _root_.Lake.Package)
    (declaration : _root_.Lake.PConfigDecl package.keyName) (toml functions : Bool) :
    TargetShape :=
  let kind := declarationKind declaration.kind
  let nativeFacets := toml || functions
  if let some config := declaration.config? _root_.Lake.LeanLib.configKind then
    { kind, needs := config.needs.map (needKind package)
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.LeanLibConfig declaration.name)) (libraryChecks config nativeFacets) }
  else if let some config := declaration.config? _root_.Lake.LeanExe.configKind then
    { kind, needs := config.needs.map (needKind package)
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.LeanExeConfig declaration.name)) (executableChecks config nativeFacets) }
  else if let some config := declaration.config? _root_.Lake.InputDir.configKind then
    { kind, needs := #[]
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.InputDirConfig declaration.name))
        [(`filter, if toml then config.filter.name == `star else functions)] }
  else if kind == .inputFile then
    { kind, needs := #[]
      unknown := unknownFields (_root_.Lake.ConfigFields.fields
        (σ := _root_.Lake.InputFileConfig declaration.name)) [] }
  else { kind := .other, unknown := #[], needs := #[] }

/-- What the plain shape reads of `package`: Lake's configuration of the package and of each
target, and for `lakefile.lean` its compiled configuration (`leanConfigReading`). A `lakefile.toml`
declares no facet and has no compiled configuration file: Lake's TOML loader gives it no facet. -/
def packageShape (ws : _root_.Lake.Workspace) (package : _root_.Lake.Package) :
    IO PackageShape := do
  let toml := package.configFile.extension == some "toml"
  let reading ← if toml then
      pure { facets := some 0, functions := false, declarations := #[], extensions := #[] }
    else leanConfigReading ws package
  return {
    unknown := unknownFields (_root_.Lake.ConfigFields.fields
      (σ := _root_.Lake.PackageConfig package.keyName package.origName))
      (packageChecks package.config)
    targets := package.targetDecls.map (targetShape package · toml reading.functions)
    facets := reading.facets, declarations := reading.declarations
    extensions := reading.extensions }

/-- Each buildable module of the root package's libraries and each root of its executables, with
the real path of each source file that a library or an executable gives it, the source file of the
module that Lake resolves the name to (`Workspace.findTargetModule?`, which the `+NAME` targets of
`moduleImports` also use) when that module is of the root package, and its imports. `none` when
`moduleImports` reads none. -/
def moduleEntries (ws : _root_.Lake.Workspace) : IO (Option (Array ModuleEntry)) := do
  let root := ws.root
  let mut sources : Array (Name × FilePath) := #[]
  for library in root.leanLibs do
    for name in ← buildableModules library do
      sources := sources.push (name, Lean.modToFilePath library.srcDir name "lean")
  for exe in root.leanExes do
    sources := sources.push (exe.root.name, exe.root.leanFile)
  let mut names : Array Name := #[]
  let mut seen : NameSet := {}
  for (name, _) in sources do
    unless seen.contains name do
      names := names.push name
      seen := seen.insert name
  let some closure ← moduleImports ws names | return none
  let real (path : FilePath) : IO String := return (← IO.FS.realPath path).toString
  some <$> closure.mapM fun (name, imports) => do
    let mut paths : Array String := #[]
    for (other, source) in sources do
      if other == name then
        let path ← real source
        unless paths.contains path do paths := paths.push path
    let resolved ← match ws.findTargetModule? name with
      | some found =>
          if found.pkg.keyName == root.keyName then some <$> real found.leanFile else pure none
      | none => pure none
    return { name, sources := paths, resolved, imports }

/-- The `MarkerInputs` of `ws`. `none` when Lake cannot read the imports of a module of the root
package; the caller also keeps the marker when this raises. -/
def markerInputs (ws : _root_.Lake.Workspace) : IO (Option MarkerInputs) := do
  let packages ← ws.packages.mapM (packageShape ws)
  let some modules ← moduleEntries ws | return none
  return some { packages, modules }

/-- `buildTargets`, run in-process through Lake's build API because the `lake build` command line
sets no Lean options, with `auditLeanOptions` on the root package unless `auditMarkerNeeded`
decides that the workspace is of the plain shape and that each module of the root package resolves
to its one source and does not import `linterModule`. Each failure to read the workspace, by an
exception or by an unknown, keeps the marker. The marked build and the unmarked one give the same
verdict for that shape only: a build of `lean_lib` and `lean_exe` targets in it runs no custom
build step, so it compiles only modules that the root package owns, whose imports the decision
read (or modules of other packages, which the root package's options do not reach), and Regula's
only reader of the marker is loaded in none of them. That no project module reads the marker
itself is assumed. Without the marker the ordinary build output is reused as it is. The inherited
search paths are ignored as in `buildTargets`; the build monitor's text is the output, and a
failed build exits 1. Lake's progress line for each job is also shown as the build runs, as by
`buildTargetsShowing`. -/
def buildAuditTargets (repo : FilePath) (targets : Array String) : IO ProcessResult := do
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← showingStream (IO.FS.Stream.ofBuffer buffer) isLakeProgressLine
  let exitCode ← try
      Workspace.withRootWorkspace repo (scrubSearchPath := true) fun ws => do
        let specs ← match ← (_root_.Lake.parseTargetSpecs ws targets.toList).toBaseIO with
          | .ok specs => pure specs
          | .error error => throw <| IO.userError (toString error)
        let marked ← try
            pure <| match ← markerInputs ws with
              | some inputs => checked_auditMarkerNeeded.run inputs
              | none => true
          catch _ => pure true
        let overrides : NameMap LeanOptions :=
          if marked then ({} : NameMap LeanOptions).insert ws.root.baseName auditLeanOptions else {}
        ws.runBuild (_root_.Lake.buildSpecs specs) {
          out := .stream out, ansiMode := .noAnsi, showSuccess := true,
          leanOptOverrides := overrides }
      pure (0 : UInt32)
    catch error =>
      out.putStrLn s!"error: {error}"
      pure 1
  let some stdout := String.fromUTF8? (← buffer.get).data
    | return { exitCode := 1, stdout := "", stderr := "error: build output is not UTF-8" }
  return { exitCode, stdout, stderr := "" }

/-- Build the claimed Lake targets and require success with no warnings.
Returns the diagnostic lines to report on failure. -/
def buildCheckedObservation (repo : FilePath) (targets : Array String)
    (mode : String) (build : FilePath → Array String → IO ProcessResult := buildTargets) :
    IO (ProcessResult × Option (Array String)) := do
  let build ← build repo targets
  if build.succeeded && (warningLines build.output).isEmpty then return (build, none)
  let diagnostics :=
    -- A warning's payload (the unused simp argument, the hint) sits on the
    -- continuation lines after its head; report the whole block.
    if !(warningLines build.output).isEmpty then diagnosticBlocks build.output isWarningLine
    -- Lean's expected type and supplied proof are continuation lines. Keep
    -- that context so public-gate qualification can identify the obligation.
    else if !(errorLines build.output).isEmpty then outputLines build.output
    else takeLast 20 (outputLines build.output)
  return (build, some
      (#[s!"FAIL[build-failed]: positive surface did not build {mode} and warning-free"]
    ++ diagnostics))

/-- Compatibility diagnostic projection. Acceptance callers retain the process observation. -/
def buildChecked (repo : FilePath) (targets : Array String)
    (mode : String) : IO (Option (Array String)) := do
  return (← buildCheckedObservation repo targets mode).2

/-- A project either builds its original targets before scope inspection, or first builds
artifacts and owes those exact original targets after the refusal-only scope check. -/
inductive ClaimedBuildPlan (original : Array String) where
  /-- The initial build already requests every original target. -/
  | full
  /-- Scope inspection precedes the still-required complete target build. -/
  | deferred (artifacts : Array String)

/-- Targets needed before the module-scope preflight. -/
def ClaimedBuildPlan.initialTargets {original : Array String} :
    ClaimedBuildPlan original → Array String
  | .full => original
  | .deferred artifacts => artifacts

/-- A deferred plan still owes the complete original target build. -/
def ClaimedBuildPlan.completionTargets {original : Array String} :
    ClaimedBuildPlan original → Option (Array String)
  | .full => none
  | .deferred _ => some original

/-- No deferred plan can substitute a smaller target set for the final build. -/
theorem ClaimedBuildPlan.completionTargets_exact {original targets : Array String}
    (plan : ClaimedBuildPlan original) (h : plan.completionTargets = some targets) :
    targets = original := by
  cases plan <;> simp_all [completionTargets]

/-- Stages completed after the initial warning-free build, before scope inspection. -/
def ClaimedBuildPlan.completedBeforeScope {original : Array String} :
    ClaimedBuildPlan original → List RegulaPolicy.Stage
  | .full => [.configuration, .discovery, .build]
  | .deferred _ => [.configuration, .discovery]

/-- The build stage is complete before preflight exactly when no final build remains. -/
theorem ClaimedBuildPlan.build_completed_iff {original : Array String}
    (plan : ClaimedBuildPlan original) :
    RegulaPolicy.Stage.build ∈ plan.completedBeforeScope ↔ plan.completionTargets = none := by
  cases plan <;> simp [completedBeforeScope, completionTargets]

/-- Lake reads an explicit `+module` with `String.toName` and splits facets at `:`.
Use that spelling only when it retains the exact discovered root name. -/
def moduleArtifactsTarget? (root : Name) : Option String :=
  let spelling := root.toString (escape := false)
  if spelling.toName = root ∧ spelling.contains ':' = false then
    some s!"+{spelling}:leanArts"
  else none

/-- A selected module spelling preserves the discovered root and has no facet separator. -/
theorem moduleArtifactsTarget?_sound {root : Name} {target : String}
    (h : moduleArtifactsTarget? root = some target) :
    ∃ spelling : String, target = s!"+{spelling}:leanArts" ∧
      spelling.toName = root ∧ spelling.contains ':' = false := by
  dsimp only [moduleArtifactsTarget?] at h
  split at h
  · rename_i valid
    exact ⟨root.toString (escape := false), (Option.some.inj h).symm, valid⟩
  · simp at h

private def artifactTargets? (manifest : Manifest) (inventory : SurfaceInventory) :
    Option (Array String) := do
  if !(manifest.surfaces.any fun surface => !surface.executables.isEmpty) then none else do
    let mut targets := #[]
    for surface in manifest.surfaces do
      targets := targets.push surface.library
      for executable in surface.executables do
        let found ← inventory.executables.find? (·.executable == executable)
        let target ← moduleArtifactsTarget? found.root
        targets := targets.push target
    return targets

/-- Keep library targets, including their custom facets, and use each claimed executable's
actual root `leanArts` facet before scope inspection. A root that cannot be expressed faithfully
through Lake's module-target syntax retains the original full build for the whole plan. -/
def claimedBuildPlan (manifest : Manifest) (inventory : SurfaceInventory) :
    ClaimedBuildPlan (Manifest.positiveTargets manifest) :=
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
