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

The driver reads its arguments once (`read`), observes, and decides (`decision`) before it
writes any result destination or audited artifact; then it marks every result destination of that
one reading incomplete, each on its own, and a refusal keeps the configuration class whatever
marking failed (`Decision.settled`). What it audits and where its result goes do not depend on which
configuration Lake loaded, which Lake does not tell the driver. The audited project is always the
workspace `lake lint` was dispatched from: a `--project` naming another one is refused with the
configuration class. A relative `--json-out` names a path in that workspace, and the success line
and the result name the manifest. The workspace owner's assertion of ordinary lakefiles comes
from the caller's environment (`ownerAssertion`), not from an argument. In addition,
`configuredRefusal` refuses `lintDriverArgs` of the default configuration that give an option
outside `Options.packageConfigurable`; none of the guarantees above rests on it.
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
prints what an audit of the dispatching root `repo` would check, with the facet report and its
census (`FacetReport.Output.census`). It never constructs or reports a result. -/
private def explain (repo : FilePath) (options : Options) : IO Outcome := do
  Regula.Checker.initializeLeanSearchPath
  let manifestPath := match options.manifest with
    | some path => if (FilePath.mk path).isAbsolute then FilePath.mk path else repo / path
    | none => Manifest.defaultPath repo
  IO.println "regula lint configuration (read-only; no audit was run)"
  IO.println s!"project: {repo}"
  IO.println
      s!"manifest: {manifestPath} \
        ({if options.manifest.isSome then "--manifest" else "project-root default"})"
  let inventory ← Lake.surfaceInventory repo (facets := .census)
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

/-- The Lake target of `workerBinary`, which the audit spawns as its worker. Lake's lint
dispatch builds only the driver, so the driver builds this sibling target before the audit,
in the workspace `lake lint` was dispatched from (`repoRoot`), which is also the audited project.
That workspace built the running driver, whether `regula` is a path dependency, a git dependency
under `.lake/packages`, any custom `packagesDir` or the root, so it resolves `regula` to the
same package, dependencies and toolchain, and its `regula/axiomGate` is `workerBinary`.

The spelling starts with `@`, which Lake reads as a package and a target and never as a path
(`Lake/CLI/Build.lean:175-177`). A spelling without it is first resolved as a path in the
workspace (`:184-192`): there a resolved path that is a module's source names that module, and a
failure of `realPath` gives the target by name. -/
def workerTarget : String := "@regula/axiomGate"

/-- What the driver reads before it decides (`Observed`), from the working directory's project
root `dispatching`. It loads only that root's configuration (`resolveDependencies := false`), so it
resolves, updates and materializes no dependency and writes no manifest; it writes no result
destination and no audited artifact, and the writes of that load are the assumption of `Observed`.
That workspace (`repoRoot`, which builds the worker and is the audited project) is the
dispatching one when its root library directory ends the dispatching part of the `LEAN_PATH` the
driver received: Lake v4.35.0 runs the driver without changing its working directory, so
`lake -d DIR lint` from another project would otherwise build and audit that project.
`Package.lint` spawns it through `env` with `Workspace.augmentedEnvVars`: `LEAN_PATH` is the
dispatching workspace's `leanPath`, then the library directory of the toolchain-collocated Lake
(`LakeInstall.ofLean`, so `LEAN_SYSROOT/lib/lean`), then any inherited `LEAN_PATH`.
`dispatchedFrom_iff` shows the check holds exactly when the root library directory is the last of
the dispatching workspace's, whatever was inherited, under the assumption of `dispatchedFrom`.
Any other Lake layout, or a driver run outside Lake, fails the check. It also reads the
`lintDriverArgs` of that workspace's default configuration,
the project root of `project` (the parsed `--project`, `findRepoRoot?`), `none` where that gives
a reason that it names none, such as an ancestor with both configuration files, and the owner's
assertion. A failure to read a path is the failure of the observation. -/
private def observe (dispatching : FilePath) (project : Option String) : IO Observed := do
  let sysroot ← IO.getEnv "LEAN_SYSROOT"
  let received := (((← IO.getEnv "LEAN_PATH").map SearchPath.parse).getD []).map toString
  let (root, configured) ← Workspace.withRootWorkspace dispatching (resolveDependencies := false)
    fun ws => pure (ws.root.leanLibDir.toString, ws.root.lintDriverArgs.toList)
  let dispatched := match sysroot with
    | some sysroot =>
      dispatchedFrom root (FilePath.mk sysroot / "lib" / "lean").toString received
    | none => false
  let named ← match project with
    | some dir => (·.toOption.map toString) <$> findRepoRoot? dir
    | none => pure none
  return { dispatching := dispatching.toString, dispatched, configured, named,
           owner := ← IO.getEnv ordinaryLakefilesVariable }

/-- The banner's note of the workspace owner's assertion. -/
private def ownerAssertionNote : String :=
  s!"; the workspace owner asserts ordinary lakefiles ({ordinaryLakefilesVariable}=1)"

/-- A destination as the driver resolves it: a relative path names a path in the dispatching
workspace `root`. -/
private def inWorkspace (root : FilePath) (path : String) : FilePath :=
  if (FilePath.mk path).isAbsolute then path else root / path

/-- Each destination of a reading, resolved where the audit writes it: a relative one in the
working directory's project root `root`, which it needs. -/
private def targets (reading : Reading) (root : Except IO.Error FilePath) :
    List (String × Except IO.Error FilePath) :=
  reading.destinations.eraseDups.map fun path =>
    (path, if (FilePath.mk path).isAbsolute then .ok (FilePath.mk path)
      else root.map (inWorkspace · path))

/-- Mark each resolved destination incomplete, one at a time, and return a line for each that
could not be marked, so one failure leaves no other unmarked. With `reason`, each records it as the
reason that the run stops there. -/
private def markIncomplete (targets : List (String × Except IO.Error FilePath))
    (reason : Option String := none) : IO (List String) := do
  let mut failed := []
  for (path, target) in targets do
    let marked ← match target with
      | .ok target =>
        let mark : IO Unit := match reason with
          | some reason => AxiomGate.invalidateResult target reason
          | none => AxiomGate.invalidateResult target
        mark.toBaseIO
      | .error error => pure (.error error)
    if let .error error := marked then failed := failed ++ [s!"{path}: {error}"]
  return failed

/-- The refusal of a run, which the guard of the executable runs before each run and, in a process
without Lean's task manager, in the run's place (`Regula.TaskManager.guard`): it reads the
arguments once (`read`) and finds the working directory's project root once, as `lint` does, marks
each result destination of the reading incomplete with `reason`, and returns the incomplete class.
A mark stops with nothing written at a file that is not empty or a document of Regula
(`AxiomGate.invalidateResult`). No audit runs. -/
def refuseWithoutTaskManager (reason : String) (args : List String) : IO UInt32 := do
  for line in ← markIncomplete (targets (read args) (← repoRoot.toBaseIO)) reason do
    IO.eprintln s!"regula lint: could not mark the result destination {line} incomplete"
  return Outcome.incomplete.exitCode

/-- Every path but the audit's `classify` returns a non-accepted class. The driver reads its
arguments once (`read`) and finds the working directory's project root once; observation
(`observe`), decision (`decision`), marking and the run all use that reading and that root. It
decides before it writes any result destination or audited artifact. Then it marks every result
destination of the reading incomplete, refused or not, and settles the exit class from the
decision and the marks that failed (`Decision.settled`): a refusal keeps the configuration class
whatever failed. -/
private unsafe def lint (args : List String) : IO Outcome := do
  let reading := read args
  let root ← repoRoot.toBaseIO
  let observed ← (do
    observe (← IO.ofExcept root) (reading.parsed.toOption.bind (·.project))).toBaseIO
  let decided := decision reading (observed.mapError toString)
  let resolved := targets reading root
  let failed ← markIncomplete resolved
  for line in failed do
    IO.eprintln s!"regula lint: could not mark the result destination {line} incomplete"
  match decided.settled failed with
  | .error outcome =>
    match decided with
    | .refuse reason =>
      IO.eprintln usage
      IO.eprintln s!"regula lint: {outcome.label}: {reason}"
    | .help => IO.println usage
    | .incomplete reason => IO.eprintln s!"regula lint: {outcome.label}: {reason}"
    | .explain _ | .run _ _ =>
      IO.eprintln s!"regula lint: {outcome.label}: a result destination could not be marked \
        incomplete"
    return outcome
  | .ok (.explain options) => explain (← IO.ofExcept root) options
  | .ok (.run options ordinary) =>
    let dispatching ← IO.ofExcept root
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
      unless worker.succeeded && (← Regula.Filesystem.isPresent (← workerBinary)) do
        IO.eprintln worker.output
        IO.eprintln s!"regula lint: {Outcome.incomplete.label}: audit worker {workerTarget} did \
          not build"
        return .incomplete
    | .error _ =>
      IO.println "regula lint: the workspace is outside the supported scope, so the audit worker \
        is not built"
    AxiomGate.claimedBuild.set (Lake.buildAuditTargets ordinary)
    AxiomGate.ordinaryLakefiles.set ordinary
    -- The destination marked above, where it was resolved: the run's destinations are exactly
    -- its `--json-out` (`decision_run`), and each was marked (`settled_run`).
    let jsonOut ← resolved.head?.mapM fun (_, target) => IO.ofExcept target
    let code ← AxiomGate.entry (gateArgs { options with jsonOut := jsonOut.map toString })
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
