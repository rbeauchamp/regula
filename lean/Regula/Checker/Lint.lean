import Regula.Checker.AxiomGate
import Regula.Checker.LintBuild

/-!
# Lake lint driver

`lint`: the Lake lint driver (`lintDriver = "regula/lint"`).

It runs the same project audit body as `axiomGate` (incremental by default, fresh with
`--fresh`) and maps that audit's own recorded terminal status to four exit classes through the
claimed `RegulaCore.Lint.classify`. It adds no detector, policy or acceptance path: its
success line is `Account.pass` of the accepted account the audit recorded. `--explain-config` is a
read-only
account of the configuration an audit would use; it runs no audit and, like `--help`, exits
with the non-success configuration class, so a `lintDriverArgs` entry cannot make every
`lake lint` succeed.
-/

namespace Regula.Checker.Lint

open Lean System

/-- The command-line options of one `lake lint` run of this driver, as `parseArgs` reads them. -/
structure Options where
  /-- `--project DIR`: the project to audit instead of the current one. -/
  project : Option String := none
  /-- `--manifest PATH`: the surface manifest instead of `foundation_manifest.json`. -/
  manifest : Option String := none
  /-- `--json-out PATH`: where the audit writes its versioned result JSON. -/
  jsonOut : Option String := none
  /-- `--fresh`: audit an isolated copy built from empty output instead of incrementally. -/
  fresh : Bool := false
  /-- `--verbose`: pass `--verbose` to the audit, which then also prints every classified
  declaration, the execution roots and toolchain trusted-base entries it lists on request, and
  its timing spans. -/
  verbose : Bool := false
  /-- `--ordinary-lakefiles`: the workspace owner asserts that the workspace's lakefiles are
  ordinary configuration. The claimed build then omits the audit-build marker when the plain-shape
  guard `Lake.auditMarkerNeeded` admits the workspace, and prints whether it omits the marker or
  keeps it and why (`Lake.buildAuditTargets`); without it the build always has the marker. -/
  ordinaryLakefiles : Bool := false
  /-- `--explain-config`: print the configuration an audit would use, run no audit and exit
  with the configuration class. -/
  explain : Bool := false
  /-- `--help` or `-h`: print the usage text, run no audit and exit with the configuration
  class. -/
  help : Bool := false

/-- The usage text: the accepted arguments and the meaning of each exit code. -/
def usage : String :=
  "usage: lake lint [-- [--fresh] [--project DIR] [--manifest PATH] [--json-out PATH] \
    [--verbose] [--ordinary-lakefiles]]\n" ++
  "       lake lint -- --explain-config [--fresh] [--project DIR] [--manifest PATH]\n" ++
  "Checks every manifested Lake surface: incremental elaboration with current policy\n" ++
  "inspection by default, or an isolated fresh build with --fresh.\n" ++
  "--verbose also prints every classified declaration, timing spans, each execution root with a \
    boundary the toolchain does not own or an unresolved path and every entry of the toolchain \
    trusted base.\n" ++
  "--ordinary-lakefiles asserts that the workspace's lakefiles are ordinary configuration: the \
    claimed build then omits the audit-build marker when a conservative guard admits the \
    workspace, and reuses the ordinary build output; the driver prints whether it omits the \
    marker or keeps it and why.\n" ++
  "exit codes: 0 accepted, 1 violation, 2 invalid configuration or invocation, 3 incomplete\n" ++
  "--explain-config and --help run no audit, establish no result and exit 2."

private def setOnce (flag : String) (current : Option String) (value : String) :
    Except String (Option String) :=
  if current.isSome then .error s!"duplicate {flag} option" else .ok (some value)

private def setFlag (flag : String) (current : Bool) : Except String Bool :=
  if current then .error s!"duplicate {flag} option" else .ok true

/-- Unknown, duplicate and incomplete arguments are refused; none narrows the claim. -/
def parseArgs : List String → Options → Except String Options
  | [], options => .ok options
  | "--" :: rest, options => parseArgs rest options
  | "--project" :: value :: rest, options => do
      parseArgs rest { options with project := ← setOnce "--project" options.project value }
  | "--manifest" :: value :: rest, options => do
      parseArgs rest { options with manifest := ← setOnce "--manifest" options.manifest value }
  | "--json-out" :: value :: rest, options => do
      parseArgs rest { options with jsonOut := ← setOnce "--json-out" options.jsonOut value }
  | "--fresh" :: rest, options => do
      parseArgs rest { options with fresh := ← setFlag "--fresh" options.fresh }
  | "--verbose" :: rest, options => do
      parseArgs rest { options with verbose := ← setFlag "--verbose" options.verbose }
  | "--ordinary-lakefiles" :: rest, options => do
      parseArgs rest { options with
        ordinaryLakefiles := ← setFlag "--ordinary-lakefiles" options.ordinaryLakefiles }
  | "--explain-config" :: rest, options => do
      parseArgs rest { options with explain := ← setFlag "--explain-config" options.explain }
  | "--help" :: rest, options | "-h" :: rest, options =>
      parseArgs rest { options with help := true }
  | flag :: _, _ => .error s!"unknown or incomplete argument: {flag}"

/-- The audit invocation: the same `axiomGate` project body and options. -/
def gateArgs (options : Options) : List String :=
  (if options.fresh then [] else ["--incremental"]) ++
  (options.project.map (["--project", ·])).getD [] ++
  (options.manifest.map (["--manifest", ·])).getD [] ++
  (options.jsonOut.map (["--json-out", ·])).getD [] ++
  (if options.verbose then ["--verbose"] else [])

/-- The evidence mode an audit of this invocation must report. -/
def requestedMode (fresh : Bool) : EvidenceMode :=
  if fresh then .freshProject else .incrementalProject

private def modeText (fresh : Bool) : String :=
  if fresh then "freshProject (isolated copy built from empty output)"
  else "incrementalProject (incremental elaboration; current policy on cached modules)"

/-- Read-only: validates the manifest and Lake scope with the audit's own functions and
prints what an audit would check. It never constructs or reports a result. -/
private def explain (options : Options) : IO Outcome := do
  Regula.Checker.initializeLeanSearchPath
  let repo ← match options.project with
    | some dir => findRepoRoot dir
    | none => repoRoot
  let manifestPath := match options.manifest with
    | some path => if (FilePath.mk path).isAbsolute then FilePath.mk path else repo / path
    | none => Manifest.defaultPath repo
  IO.println "regula lint configuration (read-only; no audit was run)"
  IO.println s!"project: {repo}"
  IO.println
      s!"manifest: {manifestPath} \
        ({if options.manifest.isSome then "--manifest" else "project-root default"})"
  let inventory ← Lake.surfaceInventory repo
  let manifest ← Manifest.loadFor manifestPath inventory
  discard <| IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  AxiomGate.checkClassification manifest inventory
  IO.println s!"mode: {modeText options.fresh}"
  IO.println s!"required stages: {", ".intercalate (projectStages.map ResultProtocol.stageName)}"
  for surface in manifest.surfaces do
    let modules := ((inventory.libraries.find? (·.library == surface.library)).map (·.modules)).getD
        #[]
    IO.println s!"surface {surface.library}: claim {surface.claim}, execution {surface.execution}"
    unless surface.decides.isEmpty do
      IO.println s!"  its decision registrations count toward: \
        {", ".intercalate surface.decides.toList}"
    IO.println s!"  modules: {", ".intercalate (modules.map toString).toList}"
    unless surface.executables.isEmpty do
      IO.println s!"  executables: {", ".intercalate surface.executables.toList}"
  for excluded in manifest.excludedLibraries do
    IO.println s!"excluded library {excluded.library}: {excluded.rationale}"
  for excluded in manifest.excludedExecutables do
    IO.println s!"excluded executable {excluded.executable}: {excluded.rationale}"
  IO.println
      ("not run by this command: documentation fences (`lake exe axiomGate --with-docs`); " ++
    "editor options such as linter.regula affect only local feedback")
  return .configuration

private def refuse (message : String) : IO Outcome := do
  IO.eprintln usage
  IO.eprintln s!"regula lint: {Outcome.configuration.label}: {message}"
  return .configuration

/-- The Lake target of `workerBinary`, which the audit spawns as its worker. Lake's lint
dispatch builds only the driver, so the driver builds this sibling target before the audit,
in the workspace `lake lint` was dispatched from (`repoRoot`, never `--project`). That
workspace built the running driver, whether `regula` is a path dependency, a git dependency
under `.lake/packages`, any custom `packagesDir` or the root, so it resolves `regula` to the
same package, dependencies and toolchain, and its `regula/axiomGate` is `workerBinary`. -/
def workerTarget : String := "regula/axiomGate"

/-- Refuses unless the workspace at the working directory (`repoRoot`, which builds the worker
and is the default audited project) is the one `lake lint` was dispatched from. Lake v4.34.0
runs the driver without changing its working directory, so `lake -d DIR lint` from another
project would otherwise build and audit that project. `Package.lint` spawns it through `env`
with `Workspace.augmentedEnvVars`: `LEAN_PATH` is the dispatching workspace's `leanPath`, then
the library directory of the toolchain-collocated Lake (`LakeInstall.ofLean`, so
`LEAN_SYSROOT/lib/lean`), then any inherited `LEAN_PATH`. `dispatchedFrom_iff` shows the check
holds exactly when the working-directory workspace, loaded by the same Lake, has the same
package library directories, whatever was inherited. Any other Lake layout, or a driver run
outside Lake, fails the check and is refused. -/
private def dispatchRefusal : IO (Option String) := do
  let message := "the working directory is not the workspace `lake lint` was dispatched from; " ++
    "run lake lint from the project root without -d/--dir"
  let some sysroot ← IO.getEnv "LEAN_SYSROOT" | return some message
  let received := (((← IO.getEnv "LEAN_PATH").map SearchPath.parse).getD []).map toString
  let workspace ← Workspace.withRootWorkspace (← repoRoot) fun ws =>
    pure (ws.leanPath.map toString)
  if dispatchedFrom workspace (FilePath.mk sysroot / "lib" / "lean").toString received then
    return none
  return some message

/-- The banner's note of the workspace owner's assertion. -/
private def ownerAssertion : String :=
  "; the workspace owner asserts ordinary lakefiles (--ordinary-lakefiles)"

/-- A refusal when the package that `lake lint` was dispatched from gives `--ordinary-lakefiles`
in its `lintDriverArgs`, which Lake places before the command line's arguments: the option is
the workspace owner's assertion on the command line, not the audited project's. A workspace that
does not load is left to `dispatchRefusal`, which refuses it. -/
private def configuredOptInRefusal : IO (Option String) := do
  let configured ← try
      Workspace.withRootWorkspace (← repoRoot) fun ws => pure ws.root.lintDriverArgs
    catch _ => return none
  return if configured.contains "--ordinary-lakefiles" then
      some "--ordinary-lakefiles is the workspace owner's assertion on the lake lint command \
        line; the package's lintDriverArgs cannot give it"
    else none

/-- Every path but the audit's `classify` returns a non-accepted class. -/
private unsafe def lint (args : List String) : IO Outcome := do
  let parsed := parseArgs args {}
  try AxiomGate.invalidateResults [.result] args
  catch error => if let .error message := parsed then return ← refuse message else throw error
  match parsed with
  | .error message => refuse message
  | .ok options =>
    if options.ordinaryLakefiles then
      if let some message ← configuredOptInRefusal then return ← refuse message
    if options.help || options.explain then
      if options.jsonOut.isSome || options.verbose || options.ordinaryLakefiles then
        return ← refuse "--json-out, --verbose and --ordinary-lakefiles apply only to an audit"
      if options.help then
        IO.println usage
        return .configuration
    if let some message ← dispatchRefusal then return ← refuse message
    if options.explain then return ← explain options
    IO.println
        s!"regula lint: enforcing all manifested Lake surfaces; mode {modeText options.fresh}\
          {if options.ordinaryLakefiles then ownerAssertion else ""}"
    (← IO.getStdout).flush
    -- The supported scope (`Lake.surfaceInventory`: Lake's default output layout of each owned
    -- package and one provider for each module name of an owned package) of the dispatching
    -- workspace, which builds the audit worker, is decided before this driver builds it. Outside
    -- it the worker is not built. When that workspace is the audited project, the audit, which
    -- decides the same scope from Lake's load before its first build and needs no worker for
    -- that, reports the refusal; when `--project` names another project, whose audit would need
    -- the worker, the driver refuses here with the dispatching workspace's refusal.
    let dispatching ← repoRoot
    match ← (Lake.surfaceInventory dispatching).toBaseIO with
    | .ok _ =>
      let worker ← Lake.buildTargetsShowing dispatching #[.spec workerTarget]
      unless worker.succeeded && (← (← workerBinary).pathExists) do
        IO.eprintln worker.output
        IO.eprintln s!"regula lint: {Outcome.incomplete.label}: audit worker {workerTarget} did \
          not build"
        return .incomplete
    | .error refusal =>
      let audited ← match options.project with
        | some dir => try some <$> findRepoRoot dir catch _ => pure none
        | none => pure (some dispatching)
      unless audited == some dispatching do
        IO.eprintln s!"regula lint: the workspace {dispatching} that lake lint was dispatched \
          from, which builds the audit worker, is outside the supported scope: {refusal}"
        IO.println s!"regula lint: {Outcome.incomplete.label} (exit {Outcome.incomplete.exitCode})"
        return .incomplete
      IO.println "regula lint: the workspace is outside the supported scope, so the audit worker \
        is not built"
    AxiomGate.claimedBuild.set (Lake.buildAuditTargets options.ordinaryLakefiles)
    AxiomGate.ordinaryLakefiles.set options.ordinaryLakefiles
    let code ← AxiomGate.entry (gateArgs options)
    let observed ← AxiomGate.terminalObservation.get
    let outcome := classify (requestedMode options.fresh) code observed
    -- The only success line projects the accepted account the audit recorded.
    match outcome, observed with
    | .accepted, some (.accepted account) => IO.println (account.pass "regula lint")
    | _, _ => IO.println s!"regula lint: {outcome.label} (exit {outcome.exitCode})"
    return outcome

/-- Driver body. An error escaping `lint` is configuration for a `manifest-` refusal and
incomplete otherwise, never the violation class. -/
unsafe def run (args : List String) : IO UInt32 := do
  let outcome ← try lint args catch error =>
    let outcome := if error.toString.startsWith "manifest-" then Outcome.configuration else
                                                                  .incomplete
    IO.eprintln s!"regula lint: {outcome.label}: {error}"
    pure outcome
  return outcome.exitCode

end Regula.Checker.Lint
