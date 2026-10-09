import Regula.Checker.Common
import Regula.Checker.Manifest
import Regula.Checker.Workspace
import RegulaCore.EditorPolicy
import Regula.Contract
import Regula.Decision
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
therefore omits it only for a workspace of the plain shape in which no module of the root
package imports the marker's reader (`auditMarkerNeeded`); `axiomGate` and the build-lint target
keep ordinary options (`AxiomGate.claimedBuild`). -/
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

/-- What the plain shape reads of one package of the workspace. -/
structure PackageShape where
  /-- The kind of each target the package declares. -/
  targets : Array TargetKind
  /-- The kind of the target that each `needs` entry of its libraries and executables names. -/
  needs : Array TargetKind
  /-- The number of `extraDepTargets` entries of the package, its libraries and its
  executables. -/
  extraDeps : Nat
  /-- The number of plugins, dynamic libraries, and extra `lean`, `leanc` and link arguments,
  objects and libraries that the package, its libraries and its executables configure. -/
  extras : Nat

/-- The plain shape of a package: it declares only `lean_lib`, `lean_exe`, `input_file` and
`input_dir` targets, each `needs` entry names an `input_file` or an `input_dir` of the package,
and it has no extra-dependency target and no plugin, dynamic library or extra argument, object or
library. In a workspace of such packages that declares no facet, new or of Lake's name, a build
of `lean_lib` and `lean_exe` targets runs no custom build step: it compiles modules and reads and
hashes input files. -/
def PackageShape.Plain (shape : PackageShape) : Prop :=
  (∀ kind ∈ shape.targets,
      kind = .leanLib ∨ kind = .leanExe ∨ kind = .inputFile ∨ kind = .inputDir) ∧
    (∀ kind ∈ shape.needs, kind = .inputFile ∨ kind = .inputDir) ∧
    shape.extraDeps = 0 ∧ shape.extras = 0

/-- Whether `kind` is one of the four kinds the plain shape admits. -/
def TargetKind.admitted : TargetKind → Bool
  | .other => false
  | _ => true

/-- Whether `kind` is one of the two input kinds. -/
def TargetKind.input : TargetKind → Bool
  | .inputFile | .inputDir => true
  | _ => false

/-- The test of `PackageShape.Plain` (`plain_iff`). -/
def PackageShape.plain (shape : PackageShape) : Bool :=
  shape.targets.all TargetKind.admitted && shape.needs.all TargetKind.input &&
    shape.extraDeps == 0 && shape.extras == 0

/-- `TargetKind.admitted` holds exactly for the four admitted kinds. -/
theorem TargetKind.admitted_iff (kind : TargetKind) :
    kind.admitted = true ↔
      kind = .leanLib ∨ kind = .leanExe ∨ kind = .inputFile ∨ kind = .inputDir := by
  cases kind <;> simp [admitted]

/-- `TargetKind.input` holds exactly for the two input kinds. -/
theorem TargetKind.input_iff (kind : TargetKind) :
    kind.input = true ↔ kind = .inputFile ∨ kind = .inputDir := by
  cases kind <;> simp [input]

/-- `PackageShape.plain` decides `PackageShape.Plain`. -/
theorem PackageShape.plain_iff (shape : PackageShape) : shape.plain = true ↔ shape.Plain := by
  simp only [plain, Plain, Bool.and_eq_true, Array.all_eq_true', beq_iff_eq,
    TargetKind.admitted_iff, TargetKind.input_iff, and_assoc]

/-- What the `lint` driver reads of the workspace before its claimed build: the shape of each
package, the facets it declares, and each module that the root package owns with its
transitive imports. Lake applies the root package's Lean options to the modules that package
owns: the buildable modules of its libraries and the roots of its executables. -/
structure MarkerInputs where
  /-- The shape of each package of the workspace (`packageShape`). -/
  packages : Array PackageShape
  /-- The number of facets that the workspace declares, new or in place of Lake's own
  (`customFacets`). -/
  customFacets : Nat
  /-- Each buildable module of the root package's libraries (`buildableModules`) and each root of
  its executables, with the modules that Lake reports it imports transitively
  (`moduleImports`). -/
  closure : Array (Name × Array Name)

/-- Whether the `lint` driver's claimed build passes `auditLeanOptions`: the workspace is not of
the plain shape (a package that is not `PackageShape.Plain`, or a custom facet), or a module of
the root package imports `linterModule`, directly or transitively (`auditMarkerNeeded_iff`). -/
@[regula_decision]
def auditMarkerNeeded (inputs : MarkerInputs) : Bool :=
  !(inputs.packages.all PackageShape.plain && inputs.customFacets == 0) ||
    inputs.closure.any fun entry => entry.2.contains linterModule

/-- `auditMarkerNeeded` asks for the marker exactly when the workspace is not of the plain shape
or some entry's imports have the linter's module among them. -/
theorem auditMarkerNeeded_iff (inputs : MarkerInputs) :
    auditMarkerNeeded inputs = true ↔
      ¬ ((∀ shape ∈ inputs.packages, shape.Plain) ∧ inputs.customFacets = 0) ∨
        ∃ entry ∈ inputs.closure, linterModule ∈ entry.2 := by
  have plain : (inputs.packages.all PackageShape.plain && inputs.customFacets == 0) = true ↔
      (∀ shape ∈ inputs.packages, shape.Plain) ∧ inputs.customFacets = 0 := by
    simp only [Bool.and_eq_true, Array.all_eq_true', PackageShape.plain_iff, beq_iff_eq]
  have imports : (inputs.closure.any fun entry => entry.2.contains linterModule) = true ↔
      ∃ entry ∈ inputs.closure, linterModule ∈ entry.2 := by
    simp only [Array.any_eq_true, Array.contains_iff_mem]
    constructor
    · rintro ⟨i, bound, member⟩
      exact ⟨inputs.closure[i], Array.getElem_mem bound, member⟩
    · rintro ⟨entry, entered, member⟩
      obtain ⟨i, bound, rfl⟩ := Array.getElem_of_mem entered
      exact ⟨i, bound, member⟩
  rw [auditMarkerNeeded, Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, plain,
    imports]

/-- `auditMarkerNeeded` is a sound and complete decision of "the workspace is not of the plain
shape, or a module of the root package imports the linter's module" (`auditMarkerNeeded_iff`):
it asks for the marker for a workspace with a custom facet and not for an empty one. The
specification is a statement about fields, kinds and membership; it names no test of the
implementation. It does not establish that `linterModule` is the only reader of the marker, nor
that the inputs describe the workspace: the first is checked by inspection, and the second rests
on `markerInputs`, Lake's configuration and its `transImports` facet. -/
theorem checked_auditMarkerNeeded : Regula.ExecutableContract auditMarkerNeeded
    (Regula.Decides (· = true) fun inputs : MarkerInputs =>
      ¬ ((∀ shape ∈ inputs.packages, shape.Plain) ∧ inputs.customFacets = 0) ∨
        ∃ entry ∈ inputs.closure, linterModule ∈ entry.2) :=
  ⟨Regula.Decides.of_iff auditMarkerNeeded_iff
    ⟨⟨#[], 1, #[]⟩, (auditMarkerNeeded_iff _).mpr (.inl fun ⟨_, zero⟩ => absurd zero (by decide))⟩
    ⟨⟨#[], 0, #[]⟩, fun accepted => by
      rcases (auditMarkerNeeded_iff _).mp accepted with notPlain | ⟨_, member, _⟩
      · exact notPlain ⟨(fun _ member => by simp at member), rfl⟩
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

/-- The number of plugins, dynamic libraries, and extra `lean`, `leanc` and link arguments,
objects and libraries that `config` sets. -/
def configExtras (config : _root_.Lake.LeanConfig) : Nat :=
  config.moreLeanArgs.size + config.weakLeanArgs.size + config.moreLeancArgs.size +
    config.weakLeancArgs.size + config.moreLinkArgs.size + config.weakLinkArgs.size +
    config.moreLinkObjs.size + config.moreLinkLibs.size + config.dynlibs.size +
    config.plugins.size

/-- What the plain shape reads of `package`: Lake's configuration of the package, its libraries
and its executables. -/
def packageShape (package : _root_.Lake.Package) : PackageShape where
  targets := package.targetDecls.map (declarationKind ·.kind)
  needs := (package.leanLibs.flatMap (·.config.needs) ++
      package.leanExes.flatMap (·.config.needs)).map (needKind package)
  extraDeps := package.config.extraDepTargets.size +
    (package.leanLibs.map (·.config.extraDepTargets.size)).sum +
    (package.leanExes.map (·.config.extraDepTargets.size)).sum
  extras := configExtras package.config.toLeanConfig +
    (package.leanLibs.map (configExtras ·.config.toLeanConfig)).sum +
    (package.leanExes.map (configExtras ·.config.toLeanConfig)).sum

/-- The number of facets of `ws` that are not Lake's own: each name outside `initFacetConfigs`, and
each name of Lake's that a configuration declares again. Lake puts a declared facet in place of
its own facet of that name (`FacetConfigMap.insert`) and keeps no record of the declaration, so a
facet counts as Lake's own only when its configuration is the very object of `initFacetConfigs`
that the workspace was loaded from; a declared facet is a new object. Comparing addresses is
`unsafe`. An object of Lake's that is not shared only counts as declared, which keeps the
marker. -/
unsafe def customFacets (ws : _root_.Lake.Workspace) : Nat :=
  ws.facetConfigs.foldl (init := 0) fun count name config =>
    match _root_.Lake.FacetConfigMap.get? name _root_.Lake.initFacetConfigs with
    | some lake => if ptrEq config lake then count else count + 1
    | none => count + 1

/-- The `MarkerInputs` of `ws`. `none` when Lake cannot read the imports of a module of the root
package; the caller also keeps the marker when this raises. -/
unsafe def markerInputs (ws : _root_.Lake.Workspace) : IO (Option MarkerInputs) := do
  let root := ws.root
  let mut modules : Array Name := #[]
  for library in root.leanLibs do
    modules := modules ++ (← buildableModules library)
  modules := modules ++ root.leanExes.map (·.root.name)
  let some closure ← moduleImports ws modules | return none
  return some
    { packages := ws.packages.map packageShape, customFacets := customFacets ws, closure }

/-- `buildTargets`, run in-process through Lake's build API because the `lake build` command line
sets no Lean options, with `auditLeanOptions` on the root package unless `auditMarkerNeeded`
decides that the workspace is of the plain shape and that no module of the root package imports
`linterModule`. Each failure to read the workspace, by an exception or by an unknown, keeps the
marker. The marked build and the unmarked one give the same verdict for that shape only: a build
of `lean_lib` and `lean_exe` targets in it runs no custom build step, so it compiles only modules
that the root package owns, whose imports the decision read (or modules of other packages, which
the root package's options do not reach), and Regula's only reader of the marker is loaded in none
of them. That no project module reads the marker itself is assumed.
Without the marker the ordinary build output is reused as it is. The inherited search paths are
ignored as in `buildTargets`; the build monitor's text is the output, and a failed build exits 1.
Lake's progress line for each job is also shown as the build runs, as by `buildTargetsShowing`. -/
unsafe def buildAuditTargets (repo : FilePath) (targets : Array String) : IO ProcessResult := do
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
