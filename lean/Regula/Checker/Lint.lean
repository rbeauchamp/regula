import Regula.Checker.AxiomGate
import Regula.Checker.LintBuild

/-!
# Lake lint driver

`lint`: the Lake lint driver (`lintDriver = "regula/lint"`).

It runs the same project audit body as `axiomGate` (incremental by default, fresh with
`--fresh`) and maps that audit's own recorded terminal status to four exit classes through the
claimed `RegulaCore.Lint.classify`. It adds no detector, policy or acceptance path: its
success line is `Account.pass` of the accepted account the audit recorded, followed by the
project and manifest the audit resolved. `--explain-config` is a read-only account of the
configuration an audit would use; it runs no audit and, like `--help`, exits with the non-success
configuration class.

What the driver audits and where its result goes do not depend on which configuration Lake
loaded, which Lake does not tell the driver (`configuredRefusal`). The audited project is always
the workspace `lake lint` was dispatched from: a `--project` naming another one is refused with
the configuration class. A relative `--json-out` names a path in that workspace, and the success
line and the result name the manifest. The workspace owner's assertion of ordinary lakefiles
comes from the caller's environment (`ownerAssertion`), not from an argument. In addition,
`configuredRefusal` refuses `lintDriverArgs` of the default configuration that give an option
outside `Options.packageConfigurable`.
-/

namespace Regula.Checker.Lint

open Lean System

/-- The usage text: the accepted arguments and the meaning of each exit code. -/
def usage : String :=
  "usage: lake lint [-- [--fresh] [--manifest PATH] [--json-out PATH] [--verbose]]\n" ++
  "       lake lint -- --explain-config [--fresh] [--manifest PATH]\n" ++
  "Checks every manifested Lake surface of the project lake lint runs in: incremental \
    elaboration with current policy\n" ++
  "inspection by default, or an isolated fresh build with --fresh.\n" ++
  "--verbose also prints every classified declaration, timing spans, each execution root with a \
    boundary the toolchain does not own or an unresolved path and every entry of the toolchain \
    trusted base.\n" ++
  s!"{ordinaryLakefilesVariable}=1 in the environment asserts that the workspace's lakefiles are \
    ordinary configuration: the claimed build then omits the audit-build marker when a \
    conservative guard admits the workspace, and reuses the ordinary build output; the driver \
    prints whether it omits the marker or keeps it and why.\n" ++
  "A relative --json-out names a path in the project lake lint runs in. --project, if given, \
    must name that project; `lake exe axiomGate --project DIR` audits another one. The \
    package's lintDriverArgs may give only --fresh, --verbose, --explain-config and --help.\n" ++
  "exit codes: 0 accepted, 1 violation, 2 invalid configuration or invocation, 3 incomplete\n" ++
  "--explain-config and --help run no audit, establish no result and exit 2."

/-- The audit invocation: the same `axiomGate` project body and options. It passes no
`--project`, so the audit's project is the working directory's, the dispatching workspace. -/
def gateArgs (options : Options) : List String :=
  (if options.fresh then [] else ["--incremental"]) ++
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
  let repo ← repoRoot
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
in the workspace `lake lint` was dispatched from (`repoRoot`), which is also the audited project.
That workspace built the running driver, whether `regula` is a path dependency, a git dependency
under `.lake/packages`, any custom `packagesDir` or the root, so it resolves `regula` to the
same package, dependencies and toolchain, and its `regula/axiomGate` is `workerBinary`. -/
def workerTarget : String := "regula/axiomGate"

/-- Refuses unless the workspace at the working directory (`repoRoot`, which builds the worker
and is the audited project) is the one `lake lint` was dispatched from, and, as an extra refusal,
unless the `lintDriverArgs` of that workspace's default configuration are admitted for `args`
(`configuredRefusal`). Lake v4.34.0 runs the driver without changing its working directory, so
`lake -d DIR lint` from another project would otherwise build and audit that project.
`Package.lint` spawns it through `env` with `Workspace.augmentedEnvVars`: `LEAN_PATH` is the
dispatching workspace's `leanPath`, then the library directory of the toolchain-collocated Lake
(`LakeInstall.ofLean`, so `LEAN_SYSROOT/lib/lean`), then any inherited `LEAN_PATH`.
`dispatchedFrom_iff` shows the check holds exactly when the working-directory workspace, loaded by
the same Lake, has the same package library directories, whatever was inherited. Any other Lake
layout, or a driver run outside Lake, fails the check and is refused. -/
private def dispatchRefusal (args : List String) : IO (Option String) := do
  let message := "the working directory is not the workspace `lake lint` was dispatched from; " ++
    "run lake lint from the project root without -d/--dir"
  let some sysroot ← IO.getEnv "LEAN_SYSROOT" | return some message
  let received := (((← IO.getEnv "LEAN_PATH").map SearchPath.parse).getD []).map toString
  let (workspace, configured) ← Workspace.withRootWorkspace (← repoRoot) fun ws =>
    pure (ws.leanPath.map toString, ws.root.lintDriverArgs.toList)
  unless dispatchedFrom workspace (FilePath.mk sysroot / "lib" / "lean").toString received do
    return some message
  return configuredRefusal configured args

/-- The refusal, if any, of a `--project`: whatever gave it, it must name the project root of the
dispatching workspace `dispatching`, which the driver audits. -/
private def projectRefusal (dispatching : FilePath) (project : Option String) :
    IO (Option String) := do
  let some dir := project | return none
  let named ← try some <$> findRepoRoot dir catch _ => pure none
  if named == some dispatching then return none
  return some s!"--project {dir} is not the project lake lint runs in ({dispatching}); lake lint \
    audits only that project, and `lake exe axiomGate --project DIR` audits another one"

/-- The banner's note of the workspace owner's assertion. -/
private def ownerAssertionNote : String :=
  s!"; the workspace owner asserts ordinary lakefiles ({ordinaryLakefilesVariable}=1)"

/-- A destination as the driver resolves it: a relative path names a path in the dispatching
workspace `root`. -/
private def inWorkspace (root : FilePath) (path : String) : FilePath :=
  if (FilePath.mk path).isAbsolute then path else root / path

/-- Mark every result destination of `args` incomplete (`resultDestinations`, the parsed
`--json-out` when the arguments parse), each where the audit would write it. An absolute one is
marked even when the working directory is outside any Lean project. -/
private def invalidateDestinations (args : List String) : IO Unit := do
  let destinations := (resultDestinations args).eraseDups
  for path in destinations.filter (FilePath.mk · |>.isAbsolute) do
    AxiomGate.invalidateResult path
  let relative := destinations.filter fun path => !(FilePath.mk path).isAbsolute
  unless relative.isEmpty do
    let root ← repoRoot
    for path in relative do AxiomGate.invalidateResult (inWorkspace root path)

/-- Every path but the audit's `classify` returns a non-accepted class. Before any other check
the driver decides the dispatch refusal, which includes the package's `lintDriverArgs`, and marks
every result destination incomplete. A failed mark is reported as such only when neither the
arguments nor the dispatch is refused, so a refused option keeps the configuration class. -/
private unsafe def lint (args : List String) : IO Outcome := do
  let parsed := parseArgs args {}
  let dispatch ← (dispatchRefusal args).toBaseIO
  if let .error error ← (invalidateDestinations args).toBaseIO then
    if let .error message := parsed then return ← refuse message
    if let .ok (some message) := dispatch then return ← refuse message
    throw error
  match parsed with
  | .error message =>
    refuse <| if args.contains "--ordinary-lakefiles" then
        s!"{message}; the workspace owner gives that assertion as {ordinaryLakefilesVariable}=1 \
          in the environment of lake lint"
      else message
  | .ok options =>
    if options.help || options.explain then
      if options.jsonOut.isSome || options.verbose then
        return ← refuse "--json-out and --verbose apply only to an audit"
      if options.help then
        IO.println usage
        return .configuration
    if let some message ← IO.ofExcept dispatch then return ← refuse message
    let dispatching ← repoRoot
    if let some message ← projectRefusal dispatching options.project then
      return ← refuse message
    if options.explain then return ← explain options
    let ordinary ← match ownerAssertion (← IO.getEnv ordinaryLakefilesVariable) with
      | .ok asserted => pure asserted
      | .error message => return ← refuse message
    IO.println
        s!"regula lint: enforcing all manifested Lake surfaces; mode {modeText options.fresh}\
          {if ordinary then ownerAssertionNote else ""}"
    (← IO.getStdout).flush
    -- The supported scope (`Lake.surfaceInventory`: Lake's default output layout of each owned
    -- package and one provider for each module name of an owned package) of the dispatching
    -- workspace, which builds the audit worker and is the audited project, is decided before
    -- this driver builds the worker. Outside it the worker is not built, and the audit, which
    -- decides the same scope from Lake's load before its first build and needs no worker for
    -- that, reports the refusal.
    match ← (Lake.surfaceInventory dispatching).toBaseIO with
    | .ok _ =>
      let worker ← Lake.buildTargetsShowing dispatching #[.spec workerTarget]
      unless worker.succeeded && (← (← workerBinary).pathExists) do
        IO.eprintln worker.output
        IO.eprintln s!"regula lint: {Outcome.incomplete.label}: audit worker {workerTarget} did \
          not build"
        return .incomplete
    | .error _ =>
      IO.println "regula lint: the workspace is outside the supported scope, so the audit worker \
        is not built"
    AxiomGate.claimedBuild.set (Lake.buildAuditTargets ordinary)
    AxiomGate.ordinaryLakefiles.set ordinary
    -- The destination invalidated above: a relative path is resolved in the dispatching workspace.
    let jsonOut := options.jsonOut.map fun path => (inWorkspace dispatching path).toString
    let code ← AxiomGate.entry (gateArgs { options with jsonOut })
    let observed ← AxiomGate.terminalObservation.get
    let audited ← AxiomGate.auditedTarget.get
    let outcome := classify (requestedMode options.fresh) code observed
    -- The only success line projects the accepted account the audit recorded and names the
    -- project and manifest that audit resolved; without them the run is incomplete.
    match outcome, observed, audited with
    | .accepted, some (.accepted account), some (project, manifest) =>
      IO.println s!"{account.pass "regula lint"} — project {project}, manifest {manifest}"
      return outcome
    | .accepted, _, _ =>
      IO.println s!"regula lint: {Outcome.incomplete.label} (exit {Outcome.incomplete.exitCode})"
      return .incomplete
    | _, _, _ =>
      IO.println s!"regula lint: {outcome.label} (exit {outcome.exitCode})"
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
