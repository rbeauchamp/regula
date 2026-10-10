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
        let mut globs := library.config.globs
        for root in library.roots do
          if library.config.globs.any (·.matches root) &&
              (← (Lean.modToFilePath library.srcDir root "").isDir) then
            globs := globs.push (.submodules root)
        for glob in globs do
          glob.forEachModuleIn library.srcDir fun name => do
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

/-- A target of the claimed surface that a checker build requests: a library or an executable of
the root package, by a spelling that names it, or the Lean artifacts of a module of the root
package. `Build.run` finds each among the root package's own targets; it never reads a spelling
as Lake target syntax, in which a `/` would name a package. -/
inductive SurfaceTarget where
  /-- The library of the root package whose recorded spelling (`Manifest.targetSpelling` of its
  name) is that of `spelling` (`Manifest.recordedName`), the relation a manifest's library names
  are checked with. -/
  | library (spelling : String)
  /-- The executable of the root package that `spelling` names, as for `library`. -/
  | executable (spelling : String)
  /-- The Lean artifacts (`leanArts`) of the module `name` of a target of the root package. -/
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
that names no library or executable of the root package, a module of none of its targets, and a
library without a module refuse. -/
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
    let some mod := ws.root.findTargetModule? name
      | throw <| IO.userError s!"{name} is a module of no target of the root package"
    return (#[← artifacts mod], #[mod])

/-- A build the checker runs: the Lean options it sets on the root package, if any, and the lines
of its output it also shows as it runs. A `Build` holds no way to run it other than `Build.run`,
so every checker build runs as `Build.run` describes. -/
structure Build where
  /-- The Lean options set on the root package, over its own, or none. -/
  rootOptions : Option LeanOptions := none
  /-- Selects the output lines also printed to standard output as the build writes them. -/
  display : String → Bool := fun _ => false
  deriving Inhabited

/-- Build `targets` of the workspace at `repo` as `build` describes, in this process through
Lake's build API, as `lake build` does: its build monitor's text is the output, and a failed build
exits 1. The inherited `LEAN_PATH` and `LEAN_SRC_PATH` are ignored, so the build resolves modules
only through that workspace. No package reads or writes Lake's artifact cache
(`Workspace.uncachedWorkspace`), and no module of the root package keeps a trace that records a
restore from it (`Workspace.dropRestoredTraces`). A target of the claimed surface is found among
the root package's own libraries, executables and modules (`surfaceRequest`), or the build fails.
For each, the build also requests the Lean artifacts of each of its modules, whatever the
library's default facets, so Lake elaborates each such module or replays the log of the
elaboration that wrote its trace, and its warnings are in the output. Afterwards each such
module's trace must record an elaboration (`Workspace.elaborationTrace`), or the build fails: a
module restored from the cache has no log of its elaboration, so its warnings would be missing
from the output. The `lean` processes Lake starts inherit this process's working directory, which
a module's elaboration can read (`IO.currentDir`), and Lake reads a target spec that names a path
from it, so the build runs with the root package's directory as the working directory, as a
`lake build` run there does. Lake's loader sets this process's Lean search path
(`Lean.searchPathRef`), which the checker's workers inherit. The run restores both, so like a
child `lake build` it leaves the checker's own state as it was. Both are process-wide, so no other
task of the process may build or read them while it runs; the checker runs its builds one at a
time. -/
def Build.run (build : Build) (repo : FilePath) (targets : Array Target) : IO ProcessResult := do
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← showingStream (IO.FS.Stream.ofBuffer buffer) build.display
  let searchPath ← Lean.searchPathRef.get
  let workingDirectory ← IO.currentDir
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
        Workspace.dropRestoredTraces ws
        let leanOptOverrides := match build.rootOptions with
          | some options => ({} : NameMap LeanOptions).insert ws.root.baseName options
          | none => {}
        ws.runBuild (_root_.Lake.buildSpecs specs) {
          out := .stream out, ansiMode := .noAnsi, showSuccess := true, leanOptOverrides }
        for mod in modules do
          let recorded ← match ← (IO.FS.readFile mod.traceFile).toBaseIO with
            | .ok text => pure (Workspace.elaborationTrace text)
            | .error _ => pure false
          unless recorded do
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
    | return { exitCode := 1, stdout := "", stderr := "error: build output is not UTF-8" }
  return { exitCode, stdout, stderr := "" }

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
so a module built with local feedback, for example by an ordinary `lake build`, is rebuilt:
its replayed log can neither add Regula warnings nor stand in for this configuration's
warnings. Lake scopes Lean options by package and library, not by module, so the trace change
reaches every root-package module; `axiomGate` and the build-lint target therefore keep
ordinary options (`AxiomGate.claimedBuild`). -/
def auditLeanOptions : LeanOptions := .ofArray #[⟨Regula.Linter.auditBuildOption, .ofBool true⟩]

/-- `buildTargetsShowing` with `auditLeanOptions` on the root package, which the `lake build`
command line cannot set. -/
def buildAuditTargets : Build :=
  { rootOptions := some auditLeanOptions, display := isLakeProgressLine }

/-- Build the claimed Lake targets and require success with no warnings.
Returns the diagnostic lines to report on failure. -/
def buildCheckedObservation (repo : FilePath) (targets : Array SurfaceTarget)
    (mode : String) (build : Build := buildTargets) :
    IO (ProcessResult × Option (Array String)) := do
  let build ← build repo (targets.map .surface)
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
