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
      let library := lib.name.toString
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
      let executable := exe.name.toString
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
so a module built with local feedback, for example by an ordinary `lake build`, is rebuilt:
its replayed log can neither add Regula warnings nor stand in for this configuration's
warnings. Lake scopes Lean options by package and library, not by module, so the trace change
reaches every root-package module; `axiomGate` and the build-lint target therefore keep
ordinary options (`AxiomGate.claimedBuild`). -/
def auditLeanOptions : LeanOptions := .ofArray #[⟨Regula.Linter.auditBuildOption, .ofBool true⟩]

/-- `buildTargets` with `auditLeanOptions` on the root package, run in-process through Lake's
build API because the `lake build` command line sets no Lean options. The inherited search
paths are ignored as in `buildTargets`; the build monitor's text is the output, and a failed
build exits 1. Lake's progress line for each job is also shown as the build runs, as by
`buildTargetsShowing`. -/
def buildAuditTargets (repo : FilePath) (targets : Array String) : IO ProcessResult := do
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let out ← showingStream (IO.FS.Stream.ofBuffer buffer) isLakeProgressLine
  let exitCode ← try
      Workspace.withRootWorkspace repo (scrubSearchPath := true) fun ws => do
        let specs ← match ← (_root_.Lake.parseTargetSpecs ws targets.toList).toBaseIO with
          | .ok specs => pure specs
          | .error error => throw <| IO.userError (toString error)
        ws.runBuild (_root_.Lake.buildSpecs specs) {
          out := .stream out, ansiMode := .noAnsi, showSuccess := true,
          leanOptOverrides := ({} : NameMap LeanOptions).insert ws.root.baseName auditLeanOptions }
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

/-- The modules `moduleName` imports transitively, as `lake query +MODULE:transImports`
reports them in `repo`. -/
def transitiveImports (repo : FilePath) (moduleName : String) : IO (Array String) := do
  jsonStringArray s!"transitive imports for {moduleName}" <|
    ← lakeQuery repo s!"+{moduleName}:transImports"

end Regula.Checker.Lake
