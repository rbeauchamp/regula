import Regula.Qualification.Support
import Regula.Process
import Regula.Cli.Setup
import Regula.Checker.Workspace
import Regula.Removal
import Regula.Checker.Frontend
import Regula.Checker.Diagnostics
import Regula.ProgramCheck.Renderer

/-! # Qualification of the process and bootstrap boundaries

These controls observe the irreducibly external compiler, process, Elan and script mechanisms.
Each planted native executable first proves it ran by writing its own marker and returning 73.
Every shadow is in the bin of a workspace constructed by Lake, with Lake's computed environment.
No control constructs PATH itself. A second record identifies the image that ran, so a different
planted tool cannot satisfy the intended-action check. The original marker stays unchanged.
The protected route must then run the expected tool or refuse the stated override, with no marker.
The native-build baselines are intentionally unprotected Lean fixtures, outside program surfaces.
Script controls run exact wrapper copies against Lean stub drivers and establish wrapper selection,
not acceptance of the stub or of the real driver's verification workload. Every child is joined. -/

namespace Regula.Qualification.Process

open Lean System

namespace Sources

/-- The committed Lake configuration; no run-time values are embedded in source. -/
def lakefile : String := include_str "../../../examples/process-controls/lakefile.lean"

/-- The committed native build input. -/
def native : String := include_str "../../../examples/process-controls/ProcessFixture.lean"

/-- The approved provisioning wrapper's controlled driver. -/
def setup : String := include_str "../../../examples/process-controls/Setup.lean"

/-- The approved verification wrapper's controlled driver. -/
def driver : String := include_str "../../../examples/process-controls/Driver.lean"

/-- The unchanged solver goal for raw and checked routes. -/
def solver : String := include_str "../../../examples/process-controls/Solver.lean"

/-- The raw native-build counterexample, parameterized by its command arguments. -/
def baseline : String := include_str "../../../examples/process-controls/Baseline.lean"

/-- Ordinary imported project callers, with trusted module naming and artifact loading. -/
def projectCaller : String := include_str "../../../examples/process-controls/ProjectCaller.lean"

/-- Lake's actual native fallback, without a copied selection rule. -/
def nativeFallback : String := include_str "../../../examples/process-controls/NativeFallback.lean"

/-- The local manifest-selection workspace; paths are fixed fixture-relative names. -/
def selection : String := include_str "../../../examples/process-controls/Selection.lean"

/-- Each tiny local dependency declares only its package, not a private Verso copy. -/
def selectedDependency : String := include_str "../../../examples/process-controls/SelectedDependency.lean"

/-- Copy the campaign's exact committed sources for separate sequential compiler checks.
Called by the compiled qualifier; it executes no fixture main. The solver compiler check
does elaborate its tactic. No printer, source generator or interpreted Lake cache is used. -/
def writePreflight (directory : FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.createDirAll (directory / "Regula")
  for (name, source) in [("lakefile.lean", lakefile), ("ProcessFixture.lean", native),
      ("Setup.lean", setup), ("Driver.lean", driver), ("Solver.lean", solver),
      ("Baseline.lean", baseline), ("Regula/ProjectCaller.lean", projectCaller),
      ("NativeFallback.lean", nativeFallback), ("Selection.lean", selection),
      ("SelectedDependency.lean", selectedDependency)] do
    IO.FS.writeFile (directory / name) source

end Sources

/-- Compile and import ordinary project callers through Lean's actual artifact loader.
The controls inspect compiled calls, and never execute their planted native actions.
Assumes: Lean v4.34.1 `Lean/Setup.lean:69-87` and `Lean/Environment.lean:2228-2249` load the
supplied artifact and retain its path. `Lean/Environment.lean:2427-2431` requires initializer
execution before loading extensions; this serialized control enables it and retains the imported
regions as `Lean/ImportingFlag.lean:18-28` requires. Compiler and imports remain trusted. -/
private def importedProjectControl (directory : FilePath) : IO Unit := do
  let source := directory / "Regula" / "ProjectCaller.lean"
  let artifact := source.withExtension "olean"
  IO.FS.createDirAll (directory / "Regula")
  IO.FS.writeFile source Sources.projectCaller
  let compiled ← run directory (.toolchain .lean)
    #["-R", directory.toString, "-o", artifact.toString, source.toString]
  requireChecks [⟨"imported project control: actual source compiled", compiled.exitCode == 0⟩]
  let artifacts : ImportArtifacts := .ofArrays #[#[artifact]]
  unsafe Lean.enableInitializersExecution
  let env ← Lean.importModules #[{ module := `Regula.ProjectCaller, importAll := true }] {} 0
    (loadExts := true) (level := .private)
    (arts := ({} : NameMap ImportArtifacts).insert `Regula.ProjectCaller artifacts)
  let caller := `Regula.ProjectCaller.read
  let some index := env.getModuleIdxFor? caller
    | throw <| IO.userError "imported project control: caller was not imported"
  requireChecks [⟨"imported project control: actual caller module is recorded",
      env.header.moduleNames[index.toNat]! == `Regula.ProjectCaller⟩,
    ⟨"imported project control: genuine named Lake library remains admitted",
      Regula.Removal.libraryCaller env [`Lake] `Lake.captureProc'⟩,
    ⟨"imported project control: project module is outside library policy domains",
      !Regula.Removal.libraryCaller env [`Init, `Lean, `Lake, `Std, `MultiVerso] caller⟩]
  for (root, primitive) in [(caller, ``IO.getEnv), (`Regula.ProjectCaller.start, ``Lake.captureProc'),
      (`Std.Time.Database.TZdb.resolveLocalPath, ``IO.getEnv)] do
    let reach := Regula.Removal.rawRemovalsFrom env #[] #[root]
    requireChecks [⟨"imported project control: intended compiled action is refused",
      reach.unknown.isEmpty && reach.calls.any fun call =>
        call.caller == root && Regula.Removal.observerVariant env #[primitive] call.primitive⟩]

/-- Exercise Lake's actual override resolution before testing the renderer's shared refusal.
The baseline must select the stated local package; a failed load cannot satisfy it. The guarded
route must name the overridden dependency and never enter its action. The positive action
inspects the package Lake actually resolved. This observes an external loader, not artifact
authentication or a proof of arbitrary package contents. Assumes: Lake v4.34.1
`Load/Resolve.lean:603-607` overlays Manifest entries with the workspace override file, and
`Load/Manifest.lean:300-317` supplies that file's decoder and encoder. No dependency is copied. -/
private def manifestSelectionControl (directory : FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "lean-toolchain") s!"leanprover/lean4:v{Lean.versionString}\n"
  IO.FS.writeFile (directory / "lakefile.lean") Sources.selection
  for name in ["committed", "overridden"] do
    let dependency := directory / name
    IO.FS.createDirAll dependency
    IO.FS.writeFile (dependency / "lakefile.lean") Sources.selectedDependency
  let committed : _root_.Lake.PackageEntry := {
    name := `verso, inherited := false, src := .path "committed" }
  let manifest : _root_.Lake.Manifest := {
    name := `regula_selection_fixture, lakeDir := ".lake", fixedToolchain := false,
    packagesDir? := some ".lake/packages", packages := #[committed] }
  let manifestFile := directory / _root_.Lake.defaultManifestFile
  discard <| manifest.save manifestFile
  let before ← IO.FS.readFile manifestFile
  let selectedPath (workspace : _root_.Lake.Workspace) : IO FilePath := do
    let some package := workspace.findPackageByName? `verso
      | throw <| IO.userError "selection control: actual resolver omitted verso"
    IO.FS.realPath package.dir
  let overridesFile ← Regula.Checker.Workspace.withRootWorkspace directory
    (fun workspace => pure workspace.packageOverridesFile) (resolveDependencies := false)
  for (label, entry, expected) in [
      ("changed entry", { committed with src := .path "overridden" }, "overridden"),
      ("identical entry", committed, "committed")] do
    discard <| _root_.Lake.Manifest.saveEntries overridesFile #[entry]
    let selected ← Regula.Checker.Workspace.withRootWorkspace directory selectedPath
    requireChecks [⟨s!"{label}: Lake's override baseline actually resolved its package",
      selected == (← IO.FS.realPath (directory / expected))⟩]
    let entered ← IO.mkRef false
    let refused ← (Regula.ProgramCheck.Renderer.requireCommittedSelection directory
      (fun _ => entered.set true)).toBaseIO
    requireChecks [⟨s!"{label}: intended selector refusal", match refused with
      | .error error => (toString error).contains "observer reach check incomplete: exempted dependency verso has an overridden selection"
      | .ok _ => false⟩,
      ⟨s!"{label}: guarded action was not entered", !(← entered.get)⟩,
      ⟨s!"{label}: committed manifest remained unchanged", (← IO.FS.readFile manifestFile) == before⟩]
    Regula.Filesystem.removePath .file overridesFile
  let entered ← IO.mkRef false
  Regula.ProgramCheck.Renderer.requireCommittedSelection directory fun workspace => do
    requireChecks [⟨"committed selection: actual dependency resolved",
      (← selectedPath workspace) == (← IO.FS.realPath (directory / "committed"))⟩]
    entered.set true
  requireChecks [⟨"committed selection: guarded positive action really entered", ← entered.get⟩]

/-- The native shadow's early entry, before any command parsing or deadline dispatch.
Only the control supplies its marker path; it changes no project file. -/
def worker (args : List String := []) : IO UInt32 := do
  -- This owned identity-reply control is not a copied Lean installation. It exercises the
  -- observer's self-report protocol; the native cc/ar actions still prove their own image ran.
  if args == ["--stdin"] && (← Regula.Process.readEnv "REGULA_PROCESS_IDENTITY") == some "1" then
    IO.println Lean.versionString
    IO.println Lean.githash
    return 0
  let some marker ← Regula.Process.readEnv "REGULA_PROCESS_MARKER"
    | throw <| IO.userError "process control has no marker"
  IO.FS.writeFile marker "shadow ran\n"
  IO.FS.writeFile (System.FilePath.mk marker |>.addExtension "program")
    (← IO.FS.realPath (← Regula.Process.appPath)).toString
  IO.println "regula process shadow ran"
  return 73

/-- Exercise the actual process preparation or workspace load in a fresh worker. The positive
boundary mode admits an absolute override without starting a native tool. A returned path is
boundary admission, not a successful native build or a claim that the identity reply is Lean. -/
def nativeFallbackWorker (mode : String) (directory : FilePath) : IO UInt32 := do
  try
    match mode with
    | "prepare" => discard <| Regula.Process.prepare (.toolchain .lake) {cmd := ""}
    | "workspace" => Regula.Checker.Workspace.withRootWorkspace directory fun _ => pure ()
    | "boundary" => discard <| Regula.Process.lakeSysroot
    | _ => throw <| IO.userError "unknown native fallback worker"
    IO.println "native boundary admitted"
    return 0
  catch error =>
    IO.eprintln error
    return 2

/-- Elaborate one solver-using source in this Regula executable. The raw branch is an external
boundary counterexample: no process policy is duplicated, only the unprotected initial options.
The protected branches call the actual setup, fresh frontend and diagnostic source readers.
The caller selects this worker by its own single argument, so solver children with native SAT
arguments inherit only the marker-worker environment mode. Assumes: Lean v4.34.1
External.lean:147-166 supplies its solver arguments, and Init/System/IO.lean:1434-1450 inherits
the parent's environment. Imported tactic code and its native solver remain trusted. -/
def cadicalWorker (checked : Bool) (route : String := "setup") : IO UInt32 := do
  let some file ← Regula.Process.readEnv "REGULA_CADICAL_SOURCE"
    | throw <| IO.userError "cadical control has no owned source"
  let source ← IO.FS.readFile file
  let errors ← if checked then do
    if route == "setup" then
      let (_, errors) ← Regula.Cli.Setup.lakefileCommands file source
      pure errors
    else do
      Regula.Checker.initializeLeanSearchPath
      match route with
      | "frontend" =>
        discard <| unsafe Regula.Checker.Frontend.buildCurrentSearchPath `processCadical file
        pure []
      | "diagnostics" =>
        (← unsafe Regula.Checker.Diagnostics.errors `processCadical file).toList |> pure
      | _ => throw <| IO.userError "unknown checked solver reader"
  else do
    Regula.Checker.initializeLeanSearchPath
    unsafe Lean.enableInitializersExecution
    let input := Parser.mkInputContext source file
    let (header, parser, messages) ← Parser.parseHeader input
    let (env, messages) ← Elab.processHeader header {} messages input (mainModule := `processCadical)
    let result ← Elab.IO.processCommands input parser (Elab.Command.mkState env messages {})
    (result.commandState.messages.toList.filter (·.severity == .error)).mapM (·.toString)
  for error in errors do IO.eprintln error
  return if errors.isEmpty then 0 else 1

/-- Make one owned native shadow from the current qualification executable.
This is a filesystem/process control, not a proof that copying or chmod is correct. -/
private def shadow (executable path : FilePath) : IO Unit := do
  IO.FS.writeBinFile path (← IO.FS.readBinFile executable)
  let mode ← run (path.parent.getD ".")
    (.stated "/bin/chmod" "Make this owned native process fixture executable")
    #["755", path.toString]
  requireChecks [⟨"shadow chmod completed", mode.exitCode == 0⟩]

/-- Read a boundary marker without turning its absence into an unlabeled IO failure. -/
private def marked (marker : FilePath) (expected : String) : IO Bool := do
  match ← (IO.FS.readFile marker).toBaseIO with
  | .ok contents => return contents == expected
  | .error _ => return false

/-- One tiny native-build workspace, with no dependency or copied toolchain. -/
private def nativeProject (project : FilePath) : IO Unit := do
  IO.FS.createDirAll project
  IO.FS.writeFile (project / "lean-toolchain") s!"leanprover/lean4:v{Lean.versionString}\n"
  IO.FS.writeFile (project / "lakefile.lean") Sources.lakefile
  IO.FS.writeFile (project / "ProcessFixture.lean") Sources.native

/-- One owned workspace's planted route, selected by Lake's package model and environment. -/
private structure Fixture where
  root : FilePath
  bin : FilePath
  marker : FilePath
  env : Array (String × Option String)

/-- Construct every shadow in the root package's actual bin directory. Assumes: Lean v4.34.1
Lake/Config/Workspace.lean:351-353, 375-386, 412-431 puts package bins before the toolchain,
whose own path precedes the inherited PATH (Lake/Config/Env.lean:237-241). Thus an unprotected
bare tool under lake env selects this planted image. The control uses those Lake APIs, not a
manually edited PATH or an assumed build-directory spelling. -/
private def plant (root executable marker : FilePath) : IO Fixture := do
  nativeProject root
  let (bin, env) ← Regula.Checker.Workspace.withRootWorkspace root
    (fun workspace => pure (workspace.root.binDir, workspace.augmentedEnvVars))
    (resolveDependencies := false)
  IO.FS.createDirAll bin
  for tool in #[Regula.Process.Tool.lean, .lake, .leanchecker, .clang, .llvmAr, .cadical] do
    shadow executable (bin / tool.basename)
  return ⟨root, bin, marker, env ++ #[
    ("REGULA_QUALIFICATION_WRAPPER", some "process"),
    ("REGULA_PROCESS_MARKER", some marker.toString)]⟩

/-- The original marker plus the OS-reported image establish the specific planted action.
Assumes: Lean v4.34.1 Init/System/IO.lean:952-955 reports the executing image; realPath and the
owned fixture files remain trusted. A different shadow's failure cannot satisfy this check. -/
private def Fixture.actionRan (fixture : Fixture) (tool : Regula.Process.Tool) : IO Bool := do
  let image ← IO.FS.realPath (fixture.bin / tool.basename)
  return (← marked fixture.marker "shadow ran\n") &&
    (← marked (fixture.marker.addExtension "program") image.toString)

/-- Remove the owned action records only after the required action was established. -/
private def Fixture.clear (fixture : Fixture) : IO Unit := do
  Regula.Filesystem.removePath .file fixture.marker
  Regula.Filesystem.removePath .file (fixture.marker.addExtension "program")

/-- Require the bare-name route's live selection of the intended workspace image through Lake.
Assumes: Lake v4.34.1 Workspace.augmentedEnvVars and augmentedPath (Config/Workspace.lean:375-386,
412-431) precede the installation's path (Config/Env.lean:237-241) with this package's bin.
This intentionally unprotected child is an external-boundary control, outside claimed source. -/
private def baseline (fixture : Fixture) (tool : Regula.Process.Tool) : IO Unit := do
  let result ← run fixture.root (.toolchain .lake) #["env", tool.basename] fixture.env
  requireChecks [⟨s!"workspace {tool.basename}: action ran (exit {result.exitCode}, stdout {result.stdout}, stderr {result.stderr})",
    result.exitCode == 73 && result.stdout == "regula process shadow ran\n" &&
      (← fixture.actionRan tool)⟩]
  fixture.clear
  IO.println s!"process control: workspace {tool.basename}: live baseline completed"

/-- Lake itself selects bare cc/ar when the candidate lacks its bundled tools. The baseline
must record that exact native image, then both protected public paths must refuse for the native
fallback reason. The owned candidate contains an identity-reply control, not a cloned compiler;
it qualifies installation admission and Lake's actual native action, not a whole alternate build.
Successful absolute-override preparation restores the boundary positive. -/
private def missingNativeControl (fixture : Fixture) (executable : FilePath)
    (tool : Regula.Process.Tool) : IO Unit := do
  let installation := fixture.root / "candidate"
  IO.FS.createDirAll (installation / "bin")
  shadow executable (installation / "bin" / "lean")
  -- The positive prepares this path but does not execute it.
  IO.FS.writeFile (installation / "bin" / "lake") ""
  let operation := if tool == .clang then "cc" else "ar"
  let image := fixture.bin / operation
  shadow executable image
  let source := fixture.root / "NativeFallback.lean"
  IO.FS.writeFile source Sources.nativeFallback
  IO.FS.writeFile (fixture.root / "control.c") "int control(void) { return 0; }\n"
  let cleared := fixture.env ++ Regula.Process.overrideVariables.map fun name => (name, none)
  let raw ← run fixture.root (.toolchain .lean)
    #["--run", source.toString, installation.toString, operation, fixture.root.toString] cleared
  requireChecks [⟨"missing native bundle: Lake's exact fallback action ran",
    raw.exitCode == 1 && (← marked fixture.marker "shadow ran\n") &&
      (← marked (fixture.marker.addExtension "program") (← IO.FS.realPath image).toString)⟩]
  fixture.clear
  let otherOverride := if tool == .clang then "LEAN_AR" else "LEAN_CC"
  let otherTool := if tool == .clang then Regula.Process.Tool.llvmAr else .clang
  let env := cleared.filter (fun entry => entry.1 != otherOverride) ++
    #[(otherOverride, some (← Regula.Process.toolPath otherTool).toString),
    ("LEAN_SYSROOT", some installation.toString),
    ("REGULA_PROCESS_IDENTITY", some "1")]
  for mode in ["prepare", "workspace"] do
    let result ← run fixture.root (.stated executable "The native worker exercises the guarded installation boundary")
      #["--process-native-fallback", mode, fixture.root.toString] env
    requireChecks [⟨"missing native bundle: intended installation refusal",
      result.exitCode == 2 && result.stderr.contains s!"installation has no bundled {tool.basename} and no stable absolute override; Lake's bare native-tool fallback is refused"⟩,
      ⟨"missing native bundle: no workspace native tool started", !(← fixture.marker.pathExists)⟩]
  let absoluteEnv := env ++ #[("LEAN_CC", some (← Regula.Process.toolPath .clang).toString),
    ("LEAN_AR", some (← Regula.Process.toolPath .llvmAr).toString)]
  for mode in ["prepare", "boundary"] do
    let result ← run fixture.root (.stated executable "The native worker restores absolute-override boundary admission")
      #["--process-native-fallback", mode, fixture.root.toString] absoluteEnv
    requireChecks [⟨"missing native bundle: restored boundary admits absolute overrides",
      result.exitCode == 0 && result.stdout == "native boundary admitted\n"⟩]

/-- Run the actual approved wrapper's bytes in an isolated workspace with a Lean stub driver.
The real Lean must elaborate the stub and return its exact 37; a PATH shadow writes another marker.
No acceptance campaign runs here and no shell program is generated. -/
private def scriptRoute (root scratch executable marker : FilePath) (script driver : String) : IO Unit := do
  let planted ← plant (scratch / script) executable marker
  let fixture := planted.root
  IO.FS.createDirAll (fixture / "scripts")
  IO.FS.createDirAll (fixture / "lean")
  IO.FS.writeFile (fixture / "lean-toolchain") (← IO.FS.readFile (root / "lean-toolchain"))
  IO.FS.writeFile (fixture / "scripts" / script) (← IO.FS.readFile (root / "scripts" / script))
  let driverMarker := fixture / "driver-ran"
  let beginMarker := fixture / "begin-ran"
  let setupMarker := fixture / "setup-ran"
  if script == "verify.sh" then
    IO.FS.writeFile (fixture / "scripts" / "provision.sh") (← IO.FS.readFile (root / "scripts" / "provision.sh"))
    let mode ← run fixture (.stated "/bin/chmod" "Preserve the approved provisioning wrapper's executable mode in its control")
      #["755", (fixture / "scripts" / "provision.sh").toString]
    requireChecks [⟨"copied provisioning wrapper is executable", mode.exitCode == 0⟩]
    IO.FS.writeFile (fixture / "lean" / "RegulaProvision.lean") Sources.setup
  IO.FS.writeFile (fixture / "lean" / driver) Sources.driver
  baseline planted .lean
  let result ← run fixture (.stated "/bin/bash" "Invoke the exact operator-approved wrapper copied for this control")
    #[(fixture / "scripts" / script).toString] (planted.env ++ #[
      ("REGULA_PROCESS_SETUP_MARKER", some setupMarker.toString),
      ("REGULA_PROCESS_BEGIN_MARKER", some beginMarker.toString),
      ("REGULA_PROCESS_DRIVER_MARKER", some driverMarker.toString)])
  requireChecks [⟨s!"{script}: real Lean elaborated the stub", result.exitCode == 37 &&
      (← IO.FS.readFile driverMarker) == "driver ran\n"⟩,
    ⟨s!"{script}: workspace Lean was bypassed", !(← marker.pathExists)⟩]
  if script == "verify.sh" then
    requireChecks [⟨"verification wrapper really ran begin-attempt", (← IO.FS.readFile beginMarker) == "begin ran\n"⟩,
      ⟨"verification wrapper really completed setup before its timed driver", (← IO.FS.readFile setupMarker) == "setup ran\n"⟩]

/-- Qualify every substitution route with a Lake-constructed workspace and a specific action.
Assumes: Lean v4.34.1 Lake/Config/Workspace.lean:375-386, 412-431 and Config/Env.lean:237-241
make each package-bin shadow win an unprotected bare-name lookup. Solver siblings and missing
siblings are constructed explicitly; TacticContext.lean:55-66 gives those two default routes.
The loop covers tools, both approved scripts and compiler/archiver overrides. Every observation
inherits the public deadline. Windows extension construction is covered by Tool, but these live
POSIX controls do not run there. Explicit source solver choices remain uncovered (issue 411). -/
def check : IO Unit := do
  if System.Platform.isWindows then
    throw <| IO.userError "process qualification: POSIX script and native-build controls unsupported on Windows"
  let root ← rootDirectory
  let executable ← Regula.Process.appPath
  withScratch root "process-observers" fun scratch => do
    importedProjectControl (scratch / "imported-project")
    manifestSelectionControl (scratch / "manifest-selection")
    let marker := scratch / "shadow-ran"
    let fixture ← plant (scratch / "tools") executable marker
    for (tool, args) in [(Regula.Process.Tool.lean, #["--version"]),
        (.lake, #["--version"]),
        (.leanchecker, #["--fresh", "--verbose", "Init.Data.Nat.Basic"])] do
      baseline fixture tool
      let selected ← Regula.Process.toolPath tool
      for (label, program, arguments) in [
          ("direct", Regula.Process.Program.toolchain tool, args),
          ("lake env", .toolchain .lake, #["env", selected.toString] ++ args)] do
        let result ← run fixture.root program arguments fixture.env
        requireChecks [⟨s!"{tool.basename}/{label}: tool actually ran", result.exitCode == 0 &&
            !result.stdout.isEmpty && !result.stdout.contains "regula process shadow ran"⟩,
          ⟨s!"{tool.basename}/{label}: workspace program was bypassed", !(← marker.pathExists)⟩]
    scriptRoute root scratch executable marker "verify.sh" "RegulaVerification.lean"
    scriptRoute root scratch executable marker "provision.sh" "RegulaProvision.lean"
    let solver ← plant (scratch / "solver") executable marker
    let solverSource := solver.root / "Solver.lean"
    IO.FS.writeFile solverSource Sources.solver
    let solverEnv := solver.env ++ #[("REGULA_CADICAL_SOURCE", some solverSource.toString)]
    let missingSibling := solver.root / "driver"
    IO.FS.createDirAll missingSibling
    for (label, directory) in [("sibling", solver.bin), ("PATH fallback", missingSibling)] do
      let parent := directory / "solver-driver"
      shadow executable parent
      baseline solver .cadical
      let raw ← run solver.root (.stated parent "The owned qualifier elaborates the raw solver control in-process")
        #["--process-cadical-raw"] solverEnv
      requireChecks [⟨s!"raw solver/{label}: workspace cadical action ran (exit {raw.exitCode}, stdout {raw.stdout}, stderr {raw.stderr})",
        raw.exitCode == 1 && (← solver.actionRan .cadical)⟩]
      solver.clear
      for route in ["setup", "frontend", "diagnostics"] do
        let checked ← run solver.root (.stated parent "The owned qualifier exercises the actual source reader's checked solver")
          #["--process-cadical-reader", route] solverEnv
        requireChecks [⟨s!"checked solver/{label}/{route}: same source really elaborated", checked.exitCode == 0⟩,
          ⟨s!"checked solver/{label}/{route}: workspace cadical was bypassed", !(← marker.pathExists)⟩]
    let lake ← Regula.Process.toolPath .lake
    for (overrideName, tool) in [("LEAN_CC", Regula.Process.Tool.clang), ("CC", .clang),
        ("LEAN_AR", .llvmAr), ("AR", .llvmAr)] do
      let native ← plant (scratch / overrideName) executable marker
      baseline native tool
      if overrideName == "CC" || overrideName == "AR" then
        missingNativeControl native executable tool
      let name := tool.basename
      let overrides := native.env.filter (fun entry => !Regula.Process.overrideVariables.contains entry.1) ++
        (Regula.Process.overrideVariables.filter (· != overrideName)).map (fun key => (key, none)) ++
        #[(overrideName, some name)]
      -- LEAN_* always overrides the bundled tool. CC/AR are also refused, even where this
      -- released installation's bundled compiler means Lake would ignore them today.
      if overrideName == "LEAN_CC" || overrideName == "LEAN_AR" then
        let project := native.root
        let source := project / "Baseline.lean"
        IO.FS.writeFile source Sources.baseline
        let attempted ← run project (.toolchain .lean)
          #["--run", source.toString, lake.toString, project.toString, overrideName, name] native.env
        requireChecks [⟨s!"{overrideName}: Lake really invoked the workspace native tool (exit {attempted.exitCode}, stdout {attempted.stdout}, stderr {attempted.stderr})",
          attempted.exitCode != 0 && (← native.actionRan tool)⟩]
        native.clear
      let refused ← (Regula.Process.output (.toolchain .lake)
        {cmd := "", args := #["--version"], cwd := some native.root, env := overrides}).toBaseIO
      requireChecks [⟨s!"{overrideName}: intended absolute-override refusal", match refused with
          | .error error => (toString error).contains s!"invalid {overrideName} override" &&
              (toString error).contains s!"process selection requires an absolute path: {name}"
          | .ok _ => false⟩,
        ⟨s!"{overrideName}: no workspace native tool started", !(← marker.pathExists)⟩]
    IO.println "process observers: PASS (live tool, wrapper and native-override controls; Windows unqualified)"

end Regula.Qualification.Process
