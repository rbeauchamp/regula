import Regula.Checker.BuildLintQualification
import Regula.Checker.LintBuild
import RegulaCore.Lint

/-!
# Lake lint driver qualification

Qualification of the `lake lint` driver path. Each control copies a shipped adopter
(`examples/build-lint` in `lakefile.lean` format, `examples/lake-lint-toml` in
`lakefile.toml` format), establishes a green `lake lint`, applies one intended
mutation, and re-establishes the green control after removing all build output.
The artifact-cache controls (`cachedWarning`, `dependencyCachedWarning`, `emptyFacetsWarning`)
and `escapedNameWarning` start from their mutation and end with their green control. The driver
reuses the build-policy audit body, whose detectors the build-policy partition qualifies; these
controls establish Lake's dispatch, the exit classes, and the editor/builtin boundaries of this
invocation path. Decision probes load a changed adopter's workspace in-process, as the driver
does, and check the decision of its claimed build under the owner's assertion of ordinary
lakefiles (`REGULA_ORDINARY_LAKEFILES=1` in the environment of `lake lint`) without running an
audit. They are diagnostics, not proofs of the driver or of Lake.
-/

namespace Regula.Checker.LintQualification

open Lean System

private def acceptanceLabel := "PASS"

/-- Whether a manifest package entry is the support package `build_lint_support`: its name, a
received value, conforms to that string (`JsonAgreement.conforms`). -/
private def isSupportEntry (entry : Json) : Bool :=
  JsonAgreement.conforms (entry.getObjValD "name") (toJson "build_lint_support")

/-- `lake lint` in `cwd` with `args` after `lake lint`, and the environment changes `env` after an
inherited owner's assertion is removed. -/
private def lint (cwd : FilePath) (args : Array String := #[])
    (env : Array (String × Option String) := #[]) : IO ProcessResult :=
  runProcess cwd "lake" (#["lint"] ++ args)
    (scrubbedLeanPathEnv ++ #[(Lint.ordinaryLakefilesVariable, none)] ++ env)

/-- One invocation's required exit code and required/forbidden output fragments. -/
private structure Expectation where
  label : String
  exitCode : UInt32
  contains : Array String := #[]
  excludes : Array String := #[]

/-- The failures of one observed invocation against its expectation, with its output. -/
private def assess (e : Expectation) (result : ProcessResult) : IO (Array String) := do
  let mut failures := #[]
  if result.exitCode != e.exitCode then
    failures := failures.push s!"lake-lint/{e.label}: exit {result.exitCode}, expected {e.exitCode}"
  if let some missing := e.contains.find? (!result.output.contains ·) then
    failures := failures.push s!"lake-lint/{e.label}: missing {missing}"
  if let some present := e.excludes.find? (result.output.contains ·) then
    failures := failures.push s!"lake-lint/{e.label}: unexpected {present}"
  if !failures.isEmpty then failures := failures.push result.output
  IO.println s!"lake-lint control {e.label}: {if failures.isEmpty then "completed" else "FAILED"}"
  (← IO.getStdout).flush
  return failures

private def expect (cwd : FilePath) (e : Expectation) (args : Array String := #[])
    (env : Array (String × Option String) := #[]) : IO (Array String) := do
  assess e (← lint cwd args env)

/-- The adopter's `axiomGate --file` audit of `file` against kernel-only, run through Lake. -/
private def fileAudit (cwd : FilePath) (file : String) (args : Array String := #[]) :
    IO ProcessResult :=
  runProcess cwd "lake" (#["exe", "axiomGate", "--file", file, "--claim", "kernel-only"] ++ args)
    scrubbedLeanPathEnv

/-- An accepted run prints its account's `Account.pass` line, which names the coverage, and no
timing span, which only `--verbose` prints. -/
private def accepted (label : String) (fresh : Bool := false) : Expectation :=
  { label, exitCode := 0, contains := #[if fresh then
      s!"regula lint: {acceptanceLabel} — fresh whole-project acceptance"
    else s!"regula lint: {acceptanceLabel} — incremental project acceptance"],
    excludes := #["verification phase", "diagnostic span"] }

/-- Replace one exact anchor; a missing or repeated anchor is a harness failure. -/
private def mutate (path : FilePath) (before after : String) : IO Unit := do
  let original ← IO.FS.readFile path
  if (original.splitOn before).length != 2 then
    throw <| IO.userError s!"lake-lint: expected exactly one anchor {before} in {path}"
  IO.FS.writeFile path (original.replace before after)

private def restore (adopter : FilePath) (files : Array (FilePath × String)) : IO Unit := do
  for (path, text) in files do IO.FS.writeFile path text
  if ← (adopter / ".lake" / "build").pathExists then
    Regula.Filesystem.removePath .directory (adopter / ".lake" / "build")

/-- A decision probe: after an ordinary `lake build` of `targets`, which leaves the compiled
lakefile under `.lake/config`, the workspace at `adopter` is loaded in-process as the driver loads
it, and the decision of the driver's claimed build under the owner's assertion
(`Lake.markerInputs`, `Lake.checked_auditMarkerNeeded`) must be `expected`: `none` omits the
audit-build marker, and `some cause` keeps it with a reason (`Lake.markerReason`) that contains
`cause`, so a probe whose change does not decide fails. The loads share the process's search
path, so they run one at a time under `probes`. -/
private def probe (probes : Std.Mutex Unit) (adopter : FilePath) (label : String)
    (targets : Array String) (expected : Option String) : IO (Array String) := do
  let build ← runProcess adopter "lake" (#["build"] ++ targets) scrubbedLeanPathEnv
  let failures ← if !build.succeeded then
      pure #[s!"lake-lint/{label}: the ordinary build failed", build.output]
    else do
      let decision : Except String (Bool × Option String) ← try
          probes.atomically do
            Workspace.withRootWorkspace adopter (scrubSearchPath := true) fun ws => do
              let some inputs ← Lake.markerInputs ws
                | return .error "Lake did not report the imports of a module of the root package"
              return .ok (Lake.checked_auditMarkerNeeded.run inputs, Lake.markerReason inputs)
        catch error => pure (.error (toString error))
      pure <| match decision with
        | .error error => #[s!"lake-lint/{label}: the workspace could not be read: {error}"]
        | .ok (decided, reason) =>
            if decided == expected.isSome &&
                expected.all (fun cause => reason.any (·.contains cause)) then #[]
            else #[s!"lake-lint/{label}: the claimed build \
              {if decided then "keeps" else "omits"} the marker \
              ({reason.getD "the plain shape"}), expected \
              {expected.elim "the plain shape" (s!"a reason with '{·}'")}"]
  IO.println s!"lake-lint control {label}: {if failures.isEmpty then "completed" else "FAILED"}"
  (← IO.getStdout).flush
  return failures

/-- The environment of the workspace owner's assertion that the lakefiles are ordinary
configuration. -/
private def optIn : Array (String × Option String) :=
  #[(Lint.ordinaryLakefilesVariable, some "1")]

/-- The line of the driver's claimed build under the owner's assertion that omits the
audit-build marker, and the start of the line that keeps it (`Lake.buildAuditTargets`). -/
private def markerOmitted := "the claimed build omits the audit-build marker"
private def markerKept := "the claimed build keeps the audit-build marker: "

/-- The files of the `lakefile.lean` adopter that its controls change, each with its text as
`BuildLintQualification.setup` wrote it, for `restore`. -/
private def leanOriginals (adopter : FilePath) : IO (Array (FilePath × String)) :=
  #[adopter / "Widget" / "Additional.lean", adopter / "foundation_manifest.json",
      adopter / "Widget.lean", adopter / "lakefile.lean"].mapM fun path => do
    return (path, ← IO.FS.readFile path)

/-! The controls of the `lakefile.lean` adopter (`examples/build-lint`) are one chain in its
order, cut into five parts (`leanAudit`, `leanDecisions`, `leanArguments`, `leanViolation`,
`leanRefusals`) at points where the chain has restored every file it changed, or changed none, or
left only the plain shape of the lakefile, which `leanArguments` writes first. Each part starts
from the adopter as `BuildLintQualification.setup` writes it, in a workspace of its own, so each
control reads the files it read in the chain. The first control of a later part starts from no
build output, as it did in the chain after a `restore`, apart from the first probe of
`leanDecisions` and the first controls of `leanArguments`, which in the chain started from the
output of the controls before them. That probe builds the library itself, and so does the first
audit of `leanArguments`, `lean/option-like-manifest-read`. -/

/-- `lakefile.lean` adopter, the first part: an accepted run whose default output shows Lake's
build progress and no timing span, the read-only configuration explanation, and the file audit,
which lists every classified declaration only with `--verbose`. An information message whose text
reads as a warning line fails neither the claimed build nor the file audit. -/
private def leanAudit (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  -- The first run builds every module, showing Lake's progress line for each. Until the file
  -- audits end, Widget also prints an information message whose text reads as a warning line,
  -- which is no warning: the claimed build is checked by Lake's log levels and the file audit by
  -- the compiler's message severities, not by the text of their output.
  let widget := adopter / "Widget.lean"
  let widgetSource ← IO.FS.readFile widget
  mutate widget "namespace Widget" "#print \"Widget.lean:1:0: warning: an information message\"\n\n\
    namespace Widget"
  let positive := accepted "lean/positive"
  let mut failures ← expect adopter
    { positive with contains := positive.contains.push "] Built Widget" }
  if !failures.isEmpty then return failures
  failures := failures ++ (← expect adopter {
      label := "lean/explain-config", exitCode := 2,
      contains := #["no audit was run", "Widget.Additional", "kernel-only"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["--", "--explain-config"])
  -- The file audit lists only declarations with a finding, and timing spans are verbose output.
  failures := failures ++ (← assess {
      label := "lean/file-positive", exitCode := 0, contains := #[s!"file audit: {acceptanceLabel}"],
      excludes := #["[OK]", "verification phase", "diagnostic span"] }
    (← fileAudit adopter "Widget.lean"))
  failures := failures ++ (← assess {
      label := "lean/file-verbose", exitCode := 0,
      contains := #[s!"file audit: {acceptanceLabel}", "[OK]", "diagnostic span"] }
    (← fileAudit adopter "Widget.lean" #["--verbose"]))
  IO.FS.writeFile widget widgetSource
  return failures

/-- The plain shape of the `lakefile.lean` adopter's `lakefile`: without the `policy` target the
workspace declares only `lean_lib` and `lean_exe` targets and Regula's input targets, and no
module of the package imports `Regula.Linter`. -/
private def leanPlain (lakefile : FilePath) : IO String := do
  match (← IO.FS.readFile lakefile).splitOn "\n/-- The sole default target" with
  | [declarations, _] => pure declarations
  | _ => throw <| IO.userError "lake-lint: expected one policy target in the adopter's lakefile"

/-- The lakefile `plain` with `field` added to the declaration of the library `Widget`. -/
private def widgetLibraryIn (plain field : String) : String :=
  plain.replace "globs := #[.andSubmodules `Widget]"
    s!"globs := #[.andSubmodules `Widget]\n  {field}"

/-- `lakefile.lean` adopter, the second part. Without the custom `policy` target the workspace has
the plain shape: without the owner's assertion the driver keeps the audit-build marker and prints
no decision, so an ordinary build after it rebuilds; with it the driver prints that it omits the
marker, and an ordinary `lake build` and the driver reuse each other's build output. The banner
names the assertion and the result records it as `scope.ordinaryLakefiles`; the success line and
the result (`scope.project`, `scope.manifestPath`) name the audited project and manifest. Decision
probes of the guard (`probe`), each with one change to the plain shape and the reason that
decides: a custom target and a library in `needs` each keep the marker. After a marked build, a
weak argument added to the claimed library makes the driver elaborate it again
(`Lake.weakArgsRecord`), and a warning whose line another process's output corrupted fails both the
claimed build and the file audit, and fails the claimed build also in a library outside the claim
that the claimed library needs. A module of such a library whose source directory has a line break
fails the build, and a target of the claimed library's `extraDepTargets` still runs in the audit
build. -/
private def leanDecisions (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  BuildLintQualification.setup repo adopter
  let positive := accepted "lean/positive"
  let manifest := adopter / "foundation_manifest.json"
  let widget := adopter / "Widget.lean"
  let widgetSource ← IO.FS.readFile widget
  let lakefile := adopter / "lakefile.lean"
  let mut failures : Array String := #[]
  let plain ← leanPlain lakefile
  let widgetLibrary := widgetLibraryIn plain
  -- A custom target beside the targets of the plain shape.
  IO.FS.writeFile lakefile (plain ++ "\ntarget extra : Unit := pure (pure ())\n")
  failures := failures ++ (← probe probes adopter "lean/custom-target-marked" #["Widget"]
    (some "target extra is not a lean_lib"))
  -- A library outside the claim that the claimed library has built first (`needs`).
  let tooling := adopter / "Tooling.lean"
  IO.FS.writeFile tooling "/-! Tooling outside the claim. -/\n"
  IO.FS.writeFile lakefile <| widgetLibrary "needs := #[`@/Tooling]\n\nlean_lib Tooling where\n  \
    globs := #[.one `Tooling]"
  failures := failures ++ (← probe probes adopter "lean/needed-library-marked" #["Widget"]
    (some "target Widget needs a target of kind lean_lib"))
  Regula.Filesystem.removePath .file tooling
  -- Without the owner's assertion the driver keeps the marker, as before the plain
  -- shape existed, and prints no decision, so an ordinary build after it rebuilds. With it the
  -- driver builds without the marker and says so, and an ordinary build and the driver reuse each
  -- other's output.
  IO.FS.writeFile lakefile plain
  failures := failures ++ (← expect adopter { positive with
    label := "lean/plain-default-marked", excludes := positive.excludes.push "the claimed build" })
  -- After that marked build, a weak argument added to the claimed library is the only change.
  -- Lake's module trace omits `weakLeanArgs`, so only the audit build's record of them
  -- (`Lake.weakArgsRecord`) changes Widget's trace, and the driver elaborates it again.
  IO.FS.writeFile lakefile (widgetLibrary "weakLeanArgs := #[\"-DmaxHeartbeats=400000\"]")
  failures := failures ++ (← expect adopter { positive with
    label := "lean/weak-args-rebuilt", contains := positive.contains.push "] Built Widget" })
  IO.FS.writeFile lakefile plain
  -- A child process that inherits the compiler's standard output prints text without a line
  -- break before a warning's JSON line, so the line is no Lean message and Lake logs it as
  -- information. The claimed build refuses it, and so does the file audit at its build of the
  -- project, before its own compile of the file.
  mutate widget "import Regula.Contract" "import Regula.Contract\nimport Lean"
  mutate widget "namespace Widget" "run_cmd do\n  let child ← IO.Process.spawn \
    { cmd := \"printf\", args := #[\"x\"] }\n  discard child.wait\n  \
    Lean.logWarning \"a corrupted warning\"\n\nnamespace Widget"
  failures := failures ++ (← expect adopter {
      label := "lean/corrupted-warning", exitCode := 3,
      contains := #["the compiler printed output that is not a Lean message",
        "a corrupted warning"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  failures := failures ++ (← assess {
      label := "lean/file-corrupted-warning", exitCode := 3,
      contains := #["the compiler printed output that is not a Lean message",
        "a corrupted warning"],
      excludes := #[s!"file audit: {acceptanceLabel}"] }
    (← fileAudit adopter "Widget.lean"))
  IO.FS.writeFile widget widgetSource
  -- The same corrupted warning in a library outside the claim that the claimed library needs:
  -- Lake's build monitor judges that library's job, and so does the audit's check of the output.
  -- The manifest excludes that library.
  let manifestText ← IO.FS.readFile manifest
  let some manifestJson := (Json.parse manifestText).toOption
    | throw <| IO.userError "lake-lint: the adopter's manifest is not JSON"
  IO.FS.writeFile manifest (manifestJson.setObjVal! "excluded-libraries" (Json.arr #[
    Json.mkObj [("library", "Tooling"), ("rationale", "Tooling outside the claim.")]])).pretty
  IO.FS.writeFile tooling "import Lean\n\nrun_cmd do\n  let child ← IO.Process.spawn \
    { cmd := \"printf\", args := #[\"x\"] }\n  discard child.wait\n  \
    Lean.logWarning \"a corrupted tooling warning\"\n"
  IO.FS.writeFile lakefile <| widgetLibrary "needs := #[`@/Tooling]\n\nlean_lib Tooling where\n  \
    globs := #[.one `Tooling]"
  failures := failures ++ (← expect adopter {
      label := "lean/needed-corrupted-warning", exitCode := 3,
      contains := #["the compiler printed output that is not a Lean message",
        "a corrupted tooling warning"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  Regula.Filesystem.removePath .file tooling
  -- A library outside the claim whose source directory has a line break: the file name of its
  -- messages could then read as Lake's entry for other output, so the build refuses the module.
  let breakDirectory := adopter / "line\nbreak"
  IO.FS.createDirAll breakDirectory
  IO.FS.writeFile (breakDirectory / "Tooling.lean") "/-! Tooling outside the claim. -/\n"
  IO.FS.writeFile lakefile <| widgetLibrary "needs := #[`@/Tooling]\n\nlean_lib Tooling where\n  \
    srcDir := \"line\\nbreak\"\n  globs := #[.one `Tooling]"
  failures := failures ++ (← expect adopter {
      label := "lean/line-break-source-path", exitCode := 3,
      contains := #["Tooling", "has a line break, so its log cannot tell"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  Regula.Filesystem.removePath .directory breakDirectory
  IO.FS.writeFile manifest manifestText
  -- A module facet `input` the package declares in place of Lake's returns, for Widget, a copy of
  -- its source in a directory whose name has a line break. Lake compiles a module from that result
  -- and names its messages by it, not by `Module.leanFile`, so the build refuses the module.
  IO.FS.writeFile lakefile (plain ++ "\n@[«module_facet»] def copiedInput : ModuleFacetDecl :=\n  \
    .mk Module.inputFacet <| mkFacetJobConfig (buildable := false) fun (mod : Module) => do\n    \
    let job ← Module.inputFacetConfig.run mod\n    \
    if mod.name != `Widget then return job\n    \
    job.mapM fun input => do\n      \
    let directory := mod.pkg.dir / \"line\\nbreak\"\n      \
    IO.FS.createDirAll directory\n      \
    IO.FS.writeFile (directory / \"Widget.lean\") (← IO.FS.readFile input.path)\n      \
    return {input with path := directory / \"Widget.lean\"}\n")
  failures := failures ++ (← expect adopter {
      label := "lean/line-break-input-copy", exitCode := 3,
      contains := #["module Widget", "has a line break, so its log cannot tell"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  IO.FS.writeFile lakefile plain
  Regula.Filesystem.removePath .directory breakDirectory
  -- A target in the claimed library's `extraDepTargets` writes a file that the claimed module's
  -- elaboration reads. Regula's `extraDep` facet replaces one that the root package declares, and
  -- runs Lake's own, which builds those targets, so the audit build runs it.
  let generated := adopter / "generated.txt"
  IO.FS.writeFile lakefile (widgetLibrary "extraDepTargets := #[`generate]" ++
    "\ntarget generate pkg : Unit := do\n  \
    IO.FS.writeFile (pkg.dir / \"generated.txt\") \"ready\"\n  return Job.nil\n")
  mutate widget "namespace Widget" "namespace Widget\n\n\
    /-- Text that a target of the library's `extraDepTargets` writes. -/\n\
    def generated : String := include_str \"generated.txt\"\n"
  Regula.Filesystem.removePath .file generated
  failures := failures ++ (← expect adopter { positive with
    label := "lean/extra-dep-target", contains := positive.contains.push "] Built Widget" })
  IO.FS.writeFile widget widgetSource
  IO.FS.writeFile lakefile plain
  Regula.Filesystem.removePath .file generated
  let ordinary ← runProcess adopter "lake" #["build", "Widget"] scrubbedLeanPathEnv
  unless ordinary.succeeded && ordinary.output.contains "] Built Widget" do
    failures := failures.push s!"lake-lint/lean/plain-default-marked: the ordinary build reused \
      the driver's build: {ordinary.output}"
  failures := failures ++ (← expect adopter { positive with
    label := "lean/plain-reused", contains := positive.contains.push markerOmitted }
    (env := optIn))
  let ordinary ← runProcess adopter "lake" #["build", "Widget"] scrubbedLeanPathEnv
  unless ordinary.succeeded && !ordinary.output.contains "] Built Widget" do
    failures := failures.push s!"lake-lint/lean/plain-reused: the ordinary build rebuilt a module: \
      {ordinary.output}"
  failures := failures ++ (← expect adopter { positive with
    label := "lean/plain-reused-again", excludes := positive.excludes.push "] Built" }
    (env := optIn))
  -- The banner names the owner's assertion, and the result records it as
  -- `scope.ordinaryLakefiles`. The success line and the result name the audited project and
  -- manifest.
  let project ← IO.FS.realPath adopter
  let projectManifest := project / "foundation_manifest.json"
  failures := failures ++ (← expect adopter { positive with
      label := "lean/opt-in-reported"
      contains := positive.contains ++ #["the workspace owner asserts ordinary lakefiles",
        s!"— project {project}, manifest {projectManifest}"] }
    #["--", "--json-out", "opt-in.json"] optIn)
  let scope := (← readJson (adopter / "opt-in.json")).getObjValD "scope"
  let recorded := scope.getObjValD "ordinaryLakefiles"
  unless JsonAgreement.conforms recorded (toJson true) do
    failures := failures.push s!"lake-lint/lean/opt-in-reported: scope.ordinaryLakefiles is \
      {recorded.compress}"
  unless JsonAgreement.conforms (scope.getObjValD "project") (toJson project.toString) &&
      JsonAgreement.conforms (scope.getObjValD "manifestPath")
        (toJson projectManifest.toString) do
    failures := failures.push s!"lake-lint/lean/opt-in-reported: scope.project is \
      {(scope.getObjValD "project").compress} and scope.manifestPath is \
      {(scope.getObjValD "manifestPath").compress}"
  Regula.Filesystem.removePath .file (adopter / "opt-in.json")
  return failures

/-- `lakefile.lean` adopter, the third part, which starts from the plain shape. The assertion as a
driver argument or with a value other than `1` is refused, and so is a `--project` for another
project on the command line. A `lintDriverArgs` entry that gives `--project`, an unwritable
`--json-out` or a `--manifest` whose value looks like an option is refused by the extra check of
the default configuration, the last after the command line's destination is marked incomplete. A
refusal keeps the configuration class though a destination cannot be written, each destination is
marked on its own, and a manifest named `--json-out` is read as the manifest, not written. The
corpus producer marks the result where the audit's own plan resolved it. Decision probes of the
guard (`probe`), each with one change to the plain shape and the reason that decides: an
`input_file` in `needs` keeps the plain shape, and each of these keeps the marker: Lake's `ilean`
facet declared again with Lake's own configuration, a library field outside the plain shape's list
(`libName`), a `nativeFacets` that is not Lake's whole default term, a lakefile declaration beside
Lake's configuration declarations, and a theorem that equates two functions. -/
private def leanArguments (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  BuildLintQualification.setup repo adopter
  let positive := accepted "lean/positive"
  let lakefile := adopter / "lakefile.lean"
  let plain ← leanPlain lakefile
  let widgetLibrary := widgetLibraryIn plain
  let project ← IO.FS.realPath adopter
  let mut failures : Array String := #[]
  IO.FS.writeFile lakefile plain
  -- The owner's assertion comes only from the caller's environment, which no package
  -- configuration sets: as a driver argument it is refused, and so is a value other than `1`.
  failures := failures ++ (← expect adopter {
      label := "lean/opt-in-argument-refused", exitCode := 2,
      contains := #["unknown or incomplete argument: --ordinary-lakefiles",
        s!"{Lint.ordinaryLakefilesVariable}=1", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["--", "--ordinary-lakefiles"])
  failures := failures ++ (← expect adopter {
      label := "lean/opt-in-value-refused", exitCode := 2,
      contains := #[s!"{Lint.ordinaryLakefilesVariable} must be 1 or unset",
        "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] }
    (env := #[(Lint.ordinaryLakefilesVariable, some "yes")]))
  -- The audited project is the dispatching workspace whatever gives `--project` (#292): another
  -- project on the command line is refused, and so, by the extra check of the default
  -- configuration, is a `--project` in the package's `lintDriverArgs`.
  failures := failures ++ (← expect adopter {
      label := "lean/other-project-refused", exitCode := 2,
      contains := #["is not the project lake lint runs in", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["--", "--project", repo.toString])
  IO.FS.writeFile lakefile (plain.replace "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  lintDriverArgs := #[\"--project\", \"vendor/clean\"]")
  failures := failures ++ (← expect adopter {
      label := "lean/project-configured-refused", exitCode := 2,
      contains := #["the package's lintDriverArgs give --project",
        "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  -- A configured destination that cannot be written is still a configuration refusal, not an
  -- incomplete run.
  IO.FS.writeFile lakefile (plain.replace "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  lintDriverArgs := #[\"--json-out\", \"/\"]")
  failures := failures ++ (← expect adopter {
      label := "lean/unwritable-destination-configured-refused", exitCode := 2,
      contains := #["the package's lintDriverArgs give --json-out",
        "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  -- A configured value that looks like an option is not a destination: the command line's
  -- `--json-out` is the one marked incomplete before the refusal.
  IO.FS.writeFile lakefile (plain.replace "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  lintDriverArgs := #[\"--manifest\", \"--json-out\"]")
  IO.FS.writeFile (adopter / "stale.json") "{\"status\":\"completed\"}\n"
  failures := failures ++ (← expect adopter {
      label := "lean/option-like-value-refused", exitCode := 2,
      contains := #["the package's lintDriverArgs give --manifest",
        "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["--", "--json-out", "stale.json"])
  let stale := (← readJson (adopter / "stale.json")).getObjValD "status"
  unless JsonAgreement.conforms stale (toJson "incomplete") do
    failures := failures.push s!"lake-lint/lean/option-like-value-refused: stale.json has status \
      {stale.compress}"
  if ← (adopter / "--json-out").pathExists then
    failures := failures.push "lake-lint/lean/option-like-value-refused: the configured value \
      --json-out was written as a destination"
  Regula.Filesystem.removePath .file (adopter / "stale.json")
  -- The driver decides before it marks a destination, and a refusal keeps the configuration
  -- class though a destination cannot be written: for another project, for `--help`, and for a
  -- configured destination beside the command line's, each of which is marked on its own.
  IO.FS.writeFile lakefile plain
  failures := failures ++ (← expect adopter {
      label := "lean/other-project-unwritable-refused", exitCode := 2,
      contains := #["is not the project lake lint runs in",
        "could not mark the result destination /", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] }
    #["--", "--project", repo.toString, "--json-out", "/"])
  failures := failures ++ (← expect adopter {
      label := "lean/help-unwritable-refused", exitCode := 2,
      contains := #["--json-out and --verbose apply only to an audit",
        "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["--", "--help", "--json-out", "/"])
  IO.FS.writeFile lakefile (plain.replace "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  lintDriverArgs := #[\"--json-out\", \"/\"]")
  IO.FS.writeFile (adopter / "stale.json") "{\"status\":\"completed\"}\n"
  failures := failures ++ (← expect adopter {
      label := "lean/each-destination-marked", exitCode := 2,
      contains := #["duplicate --json-out option", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["--", "--json-out", "stale.json"])
  let stale := (← readJson (adopter / "stale.json")).getObjValD "status"
  unless JsonAgreement.conforms stale (toJson "incomplete") do
    failures := failures.push s!"lake-lint/lean/each-destination-marked: stale.json has status \
      {stale.compress}"
  Regula.Filesystem.removePath .file (adopter / "stale.json")
  -- The audit reads its arguments once too: a manifest named `--json-out` is the manifest, not
  -- a destination, so the run reads it and writes only the command line's `--json-out`.
  IO.FS.writeFile lakefile plain
  let manifestText ← IO.FS.readFile (adopter / "foundation_manifest.json")
  IO.FS.writeFile (adopter / "--json-out") manifestText
  failures := failures ++ (← expect adopter { positive with
      label := "lean/option-like-manifest-read"
      contains := positive.contains.push s!"manifest {project / "--json-out"}" }
    #["--", "--manifest", "--json-out", "--json-out", "named.json"] optIn)
  unless (← IO.FS.readFile (adopter / "--json-out")) == manifestText do
    failures := failures.push "lake-lint/lean/option-like-manifest-read: the manifest named \
      --json-out was overwritten"
  let named := (← readJson (adopter / "named.json")).getObjValD "status"
  unless JsonAgreement.conforms named (toJson "completed") do
    failures := failures.push s!"lake-lint/lean/option-like-manifest-read: named.json has status \
      {named.compress}"
  Regula.Filesystem.removePath .file (adopter / "--json-out")
  Regula.Filesystem.removePath .file (adopter / "named.json")
  -- The corpus producer marks the result where the audit's own plan resolved it: from another
  -- directory, a relative `--json-out` with `--project` is the project's file, and a stale file of
  -- the same name in the working directory is left as it was.
  let elsewhere := adopter / "elsewhere"
  IO.FS.createDirAll elsewhere
  IO.FS.writeFile (elsewhere / "facts.json") "[]\n"
  IO.FS.writeFile (elsewhere / "result.json") "{\"status\":\"completed\"}\n"
  failures := failures ++
    (← assess { label := "lean/rule-examples-project-marked", exitCode := 0 }
    (← runProcess elsewhere (repo / ".lake" / "build" / "bin" / "ruleExamples").toString
      #["--injected-git-facts", "facts.json", "axiomGate", "--project", adopter.toString,
        "--json-out", "result.json", "--help"]))
  unless (← IO.FS.readFile (elsewhere / "result.json")) == "{\"status\":\"completed\"}\n" do
    failures := failures.push "lake-lint/lean/rule-examples-project-marked: the working \
      directory's result.json was changed"
  match Json.parse (← IO.FS.readFile (adopter / "result.json")) with
  | .ok marked =>
    unless JsonAgreement.conforms (marked.getObjValD "status") (toJson "incomplete") &&
        JsonAgreement.conforms (marked.getObjValD "gitFacts") (toJson "injected") do
      failures := failures.push s!"lake-lint/lean/rule-examples-project-marked: the project's \
        result.json has status {(marked.getObjValD "status").compress} and gitFacts \
        {(marked.getObjValD "gitFacts").compress}"
  | .error error =>
    failures := failures.push s!"lake-lint/lean/rule-examples-project-marked: the project's \
      result.json: {error}"
  Regula.Filesystem.removePath .directory elsewhere
  Regula.Filesystem.removePath .file (adopter / "result.json")
  -- An `input_file` in `needs` keeps the plain shape.
  let notes := adopter / "notes.txt"
  IO.FS.writeFile notes "Widget notes.\n"
  IO.FS.writeFile lakefile <| widgetLibrary "needs := #[`@/widgetNotes]\n\ninput_file widgetNotes \
    where\n  path := \"notes.txt\""
  failures := failures ++ (← probe probes adopter "lean/input-needs-plain" #["Widget"] none)
  Regula.Filesystem.removePath .file notes
  -- Each of these keeps the marker, for the reason its change gives: Lake's `ilean` facet
  -- declared again with Lake's own configuration, which the compiled configuration file records
  -- as a facet declaration; a field outside the plain shape's list with another value than Lake's
  -- default; a `nativeFacets` that differs from Lake's default only in the `Decidable` instance of
  -- its `if`, which adds code; a declaration of the lakefile beside Lake's configuration
  -- declarations; and a theorem that equates two functions, the form of a compiler replacement
  -- (`csimp`).
  let marked (label cause text : String) : IO (Array String) := do
    IO.FS.writeFile lakefile text
    probe probes adopter label #["Widget"] (some cause)
  failures := failures ++ (← marked "lean/lake-facet-marked" "1 facet declaration" (plain ++
    "\n@[«module_facet»] def ileanAgain : ModuleFacetDecl :=\n  \
      ⟨Module.ileanFacet, Module.ileanFacetConfig⟩\n"))
  failures := failures ++ (← marked "lean/field-marked" "target Widget sets the field libName"
    (widgetLibrary "libName := \"widget\""))
  failures := failures ++ (← marked "lean/native-facets-marked"
    "target Widget sets the field nativeFacets"
    (widgetLibrary "nativeFacets := fun b => #[@ite (ModuleFacet System.FilePath) (b = true)\n    \
      (dbgTrace \"extra\" (fun _ => inferInstance)) Module.oExportFacet Module.oFacet]"))
  failures := failures ++ (← marked "lean/declaration-marked" "the declaration helperVersion"
    (plain ++ "\ndef helperVersion : Nat := 1\n"))
  failures := failures ++ (← marked "lean/theorem-marked" "the declaration identityFact"
    (plain ++ "\ntheorem identityFact : @id Nat = @id Nat := rfl\n"))
  return failures

/-- `lakefile.lean` adopter, the fourth part: a violation with its summary counts, a repeated cached
failure, and Lake's builtin-only and combined dispatch. -/
private def leanViolation (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  let additional := adopter / "Widget" / "Additional.lean"
  let mut failures : Array String := #[]
  -- An unimported glob module; the second run has every module cached.
  mutate additional "namespace Widget.Additional"
    "/-- A control assumption. -/\naxiom lintAssumption : True\nnamespace Widget.Additional"
  -- The summary counts no incomplete finding, and the rebuilt module shows its progress line.
  let violation : Expectation := {
    label := "lean/violation", exitCode := 1,
    contains := #["RG1001", "lintAssumption", "violation(s), 0 incomplete finding(s)",
      "regula lint: VIOLATION (exit 1)"],
    excludes := #["verification phase", "diagnostic span"] }
  failures := failures ++ (← expect adopter
    { violation with contains := violation.contains.push "] Built Widget.Additional" })
  failures := failures ++ (← expect adopter { violation with label := "lean/cached-violation" })
  -- Builtin linting needs explicit modules here (the default target is `policy`).
  -- Lake skips the driver: exit 0 despite the violation is not Regula enforcement.
  failures := failures ++ (← expect adopter {
      label := "lean/builtin-only", exitCode := 0,
      excludes := #["regula lint:"] } #["--builtin-only", "Widget"])
  failures := failures ++ (← expect adopter { violation with label := "lean/builtin-and-driver" }
    #["--builtin-lint", "Widget"])
  return failures

/-- `lakefile.lean` adopter, the fifth part: the configuration and invocation exit classes, an
incomplete build, a claimed import outside every library (RG2004) in the driver and the file
audit, a failed audit worker reported with its own error, and the restored positive. -/
private def leanRefusals (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  let originals ← leanOriginals adopter
  let manifest := adopter / "foundation_manifest.json"
  let widget := adopter / "Widget.lean"
  let lakefile := adopter / "lakefile.lean"
  let mut failures : Array String := #[]
  mutate manifest "\"kernel-only\"" "\"unknown\""
  failures := failures ++ (← expect adopter {
      label := "lean/configuration", exitCode := 2,
      contains := #["manifest-schema", "regula lint: INVALID CONFIGURATION (exit 2)"] })
  failures := failures ++ (← expect adopter {
      label := "lean/invocation", exitCode := 2,
      contains := #["unknown or incomplete argument: --bogus"] } #["--", "--bogus"])
  restore adopter originals
  mutate widget "namespace Widget" "/-- A control that does not elaborate. -/\ndef lintBroken : \
    Nat := \"text\"\nnamespace Widget"
  failures := failures ++ (← expect adopter {
      label := "lean/incomplete", exitCode := 3,
      contains := #["build-failed", "FAIL: 0 violation(s), 1 incomplete finding(s)",
        "regula lint: INCOMPLETE (exit 3)"] })
  restore adopter originals
  -- A claimed module imports a module of the package outside every library: the coverage
  -- violation RG2004 naming both (#129), not a failed worker.
  mutate lakefile "globs := #[.andSubmodules `Widget]" "globs := #[.one `Widget]"
  mutate widget "import Regula.Contract\n" "import Regula.Contract\nimport Widget.Additional\n"
  failures := failures ++ (← expect adopter {
      label := "lean/unowned-module", exitCode := 1,
      contains := #["RG2004", "unexpected-project-module", "Widget.Additional is outside every",
        "imported by Widget", "FAIL: 1 violation(s), 0 incomplete finding(s)",
        "regula lint: VIOLATION (exit 1)"],
      excludes := #["RG2001", "declaration-report-worker"] })
  -- The file audit reports the same import as the same violation, not as a compiler failure,
  -- naming the audited file, not the module it compiles the file as, as the importer.
  failures := failures ++ (← assess {
      label := "lean/file-unowned-module", exitCode := 1,
      contains := #["RG2004", "Widget.Additional is outside every",
        s!"imported by {(← IO.FS.realPath adopter) / "Widget.lean"}",
        "FAIL: 1 violation(s), 0 incomplete finding(s)"],
      excludes := #["does not elaborate", "RG2003", "RG2001", "AuditFile_"] }
    (← fileAudit adopter "Widget.lean"))
  restore adopter originals
  -- Two library modules that both declare `main` cannot share one environment, so the audit
  -- worker fails: its error is the RG2001 finding's detail, and the report lists the stages that
  -- completed before inspection (#130).
  let entryPoints := #[adopter / "Widget" / "One.lean", adopter / "Widget" / "Two.lean"]
  for file in entryPoints do
    IO.FS.writeFile file "/-! A root-namespace entry point. -/\n\n/-- Does nothing. -/\n\
      def main : IO Unit := pure ()\n"
  failures := failures ++ (← expect adopter {
      label := "lean/worker-failure", exitCode := 3,
      contains := #["RG2001", "declaration inspection of Widget failed", "already contains 'main'",
        "FAIL: 0 violation(s), 1 incomplete finding(s)", "regula lint: INCOMPLETE (exit 3)"] }
    #["--", "--json-out", "worker-failure.json"])
  let stages := (← readJson (adopter / "worker-failure.json")).getObjValD "stagesCompleted"
  unless JsonAgreement.conforms stages (toJson #["configuration", "discovery", "build"]) do
    failures := failures.push s!"lake-lint/lean/worker-failure: stagesCompleted {stages.compress}"
  for file in entryPoints do Regula.Filesystem.removePath .file file
  restore adopter originals
  failures := failures ++ (← expect adopter (accepted "lean/fresh-restored"))
  return failures

/-- The `lakefile.toml` adopter (`examples/lake-lint-toml`) as `BuildLintQualification.setup`
writes it, and the text of its module `Gadget.Double`, which its controls change, for
`restore`. -/
private def tomlSetup (repo adopter : FilePath) : IO (Array (FilePath × String)) := do
  BuildLintQualification.setup repo adopter "lake-lint-toml" #["Gadget.lean", "Gadget/Double.lean"]
    "lakefile.toml"
  let double := adopter / "Gadget" / "Double.lean"
  return #[(double, ← IO.FS.readFile double)]

/-! The controls of the `lakefile.toml` adopter importing `Regula.Linter` are one chain in its
order, cut into four parts (`tomlAudit`, `tomlLive`, `tomlTargets`, `tomlPlain`) at points where
the chain has restored every file it changed. Each part starts from the adopter as `tomlSetup`
writes it, in a workspace of its own, so each control reads the files it read in the chain, and
its first control starts from no build output, as it did in the chain after a `restore`. -/

/-- `lakefile.toml` adopter, the first part: an accepted run, a dispatch from another project
root, and disabling live feedback, which cannot waive the project predicate. -/
private def tomlAudit (repo adopter : FilePath) : IO (Array String) := do
  discard <| tomlSetup repo adopter
  let mut failures ← expect adopter (accepted "toml/positive")
  if !failures.isEmpty then return failures
  let double := adopter / "Gadget" / "Double.lean"
  -- Dispatched for the adopter from another project root, which the audit would accept.
  failures := failures ++ (← expect repo {
      label := "toml/foreign-dir", exitCode := 2,
      contains := #["without -d/--dir", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["-d", adopter.toString])
  -- The same from a project with no manifest and a refused argument: the driver loads only that
  -- project's root configuration, so it writes no manifest there and, for a `lakefile.toml`,
  -- nothing at all.
  let foreign := adopter / "foreign"
  IO.FS.createDirAll foreign
  IO.FS.writeFile (foreign / "lakefile.toml") "name = \"foreign\"\n"
  IO.FS.writeFile (foreign / "lean-toolchain") (← IO.FS.readFile (adopter / "lean-toolchain"))
  failures := failures ++ (← expect foreign {
      label := "toml/foreign-dir-unwritten", exitCode := 2,
      contains := #["unknown or incomplete argument: --bogus",
        "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] }
    #["-d", adopter.toString, "--", "--bogus"])
  let written := (← foreign.readDir).map (·.fileName) |>.filter
    (· ∉ ["lakefile.toml", "lean-toolchain"])
  unless written.isEmpty do
    failures := failures.push s!"lake-lint/toml/foreign-dir-unwritten: the driver wrote {written} \
      in the working directory's project"
  Regula.Filesystem.removePath .directory foreign
  mutate double "end Gadget" <|
    "set_option linter.regula false in\n/-- A control assumption. -/\n" ++
      "axiom optedOut : True\nend Gadget"
  failures := failures ++ (← expect adopter {
      label := "toml/editor-opt-out", exitCode := 1,
      contains := #["RG1001", "optedOut", "regula lint: VIOLATION (exit 1)"] })
  return failures

/-- `lakefile.toml` adopter, the second part: a live finding, also re-enabled by the source or
replayed from an ordinary `lake build` with live feedback, is the audit's violation rather than a
failed build. Under the owner's assertion the driver keeps the audit-build marker for
the live finding, whose module imports `Regula.Linter`, and prints why. -/
private def tomlLive (repo adopter : FilePath) : IO (Array String) := do
  let originals ← tomlSetup repo adopter
  let double := adopter / "Gadget" / "Double.lean"
  let mut failures : Array String := #[]
  -- A source re-enable cannot bring live feedback back into the audit build (#69).
  mutate double "end Gadget" <|
    "set_option linter.regula true\n/-- A control assumption. -/\n" ++
      "axiom reenabled : True\nend Gadget"
  failures := failures ++ (← expect adopter {
      label := "toml/source-reenabled", exitCode := 1,
      contains := #["RG1001", "reenabled", "regula lint: VIOLATION (exit 1)"],
      excludes := #["build-failed", "editorSnapshot"] })
  restore adopter originals
  mutate double "end Gadget" "/-- A control assumption. -/\naxiom liveFinding : True\nend Gadget"
  let ordinary ← runProcess adopter "lake" #["build"] scrubbedLeanPathEnv
  unless ordinary.succeeded && ordinary.output.contains "RG1001 [violation; editorSnapshot" do
    failures := failures.push s!"lake-lint/toml/live-build: {ordinary.output}"
  -- `Gadget.Double` imports `Regula.Linter`, so even under the owner's assertion the
  -- driver builds with the audit-build marker (`Lake.auditMarkerNeeded`), says why, and rebuilds
  -- the module that the ordinary build made.
  failures := failures ++ (← expect adopter {
      label := "toml/live-finding", exitCode := 1,
      contains := #["RG1001", "liveFinding", "regula lint: VIOLATION (exit 1)",
        "] Built Gadget.Double", markerKept, "imports Regula.Linter"],
      excludes := #["build-failed", "editorSnapshot"] } (env := optIn))
  return failures

/-- `lakefile.toml` adopter, the third part: a claimed `lean_lib` and a claimed `lean_exe` whose
Lake target names are not Lean identifiers are accepted under those names and classified alike
under the names as Lean prints them; naming one target under both is a configuration refusal, and
so is a library or executable entry, claimed or excluded, that names no root target of its kind:
one refusal that quotes the entry as the manifest writes it and lists the root targets of that kind
by Lake target name, in the driver and, for an executable entry, in the adopter's
`axiomGate --file` audit, which reads the manifest through the same loader. -/
private def tomlTargets (repo adopter : FilePath) : IO (Array String) := do
  discard <| tomlSetup repo adopter
  let mut failures : Array String := #[]
  -- A `lean_lib` and a `lean_exe` whose Lake target names are not Lean identifiers (#163, #166).
  -- The manifest names each by that name or as Lean prints it; both are one claim, naming both
  -- is a duplicate, and an entry, claimed or excluded, that names no target of its kind is one
  -- manifest refusal that quotes it as written and lists the root targets of that kind by Lake
  -- target name. These observe Lake's reading of a `lakefile.toml` name and of a `lake build`
  -- argument, which the manifest theorems take as given.
  let lakefile := adopter / "lakefile.toml"
  let manifest := adopter / "foundation_manifest.json"
  let cli := adopter / "Gadget" / "Cli.lean"
  let extra := adopter / "Extra.lean"
  let claiming (executables : Array String) (excluded : Array String := #[])
      (library : String := "gadget-extra") (excludedLibraries : Array String := #[]) : String :=
    Json.compress <| Json.mkObj [
      ("schema-version", toJson (2 : Nat)),
      ("surfaces", toJson #[
        Json.mkObj [
          ("library", toJson "Gadget"), ("executables", toJson executables),
          ("claim", toJson "choice-free"), ("execution", toJson "report"),
          ("rationale", toJson "target-name control")],
        Json.mkObj [
          ("library", toJson library), ("claim", toJson "choice-free"),
          ("execution", toJson "report"), ("rationale", toJson "target-name control")]]),
      ("excluded-libraries", toJson <| excludedLibraries.map fun excludedLibrary => Json.mkObj [
        ("library", toJson excludedLibrary), ("rationale", toJson "target-name control")]),
      ("excluded-executables", toJson <| excluded.map fun executable => Json.mkObj [
        ("executable", toJson executable), ("rationale", toJson "target-name control")])]
  let explained (label : String) : Expectation := {
    label, exitCode := 2,
    contains := #["no audit was run", "executables: «gadget-tool»",
      "surface «gadget-extra»: claim"],
    excludes := #[s!"regula lint: {acceptanceLabel}", "manifest-"] }
  IO.FS.writeFile lakefile <| (← IO.FS.readFile lakefile) ++
    "\n[[lean_lib]]\nname = \"gadget-extra\"\nroots = [\"Extra\"]\n" ++
    "\n[[lean_exe]]\nname = \"gadget-tool\"\nroot = \"Gadget.Cli\"\n"
  IO.FS.writeFile cli
    "/-! The adopter's command. -/\n\n/-- Does nothing. -/\ndef main : IO Unit := pure ()\n"
  IO.FS.writeFile extra
    "/-! The adopter's second library. -/\n\n/-- A constant. -/\ndef Extra.answer : Nat := 42\n"
  IO.FS.writeFile manifest (claiming #["gadget-tool"])
  failures := failures ++ (← expect adopter (accepted "toml/target-name"))
  failures := failures ++
    (← expect adopter (explained "toml/target-name-config") #["--", "--explain-config"])
  IO.FS.writeFile manifest (claiming #["«gadget-tool»"] (library := "«gadget-extra»"))
  failures := failures ++
    (← expect adopter (explained "toml/printed-name-config") #["--", "--explain-config"])
  let duplicate (label noun name : String) : Expectation := {
    label, exitCode := 2,
    contains := #["RG2002", s!"manifest-schema: duplicate {noun} '{name}'",
      "regula lint: INVALID CONFIGURATION (exit 2)"] }
  IO.FS.writeFile manifest (claiming #["gadget-tool", "«gadget-tool»"])
  failures := failures ++
    (← expect adopter (duplicate "toml/both-spellings" "executable" "«gadget-tool»"))
  IO.FS.writeFile manifest (claiming #["gadget-tool"] (excludedLibraries := #["«gadget-extra»"]))
  failures := failures ++
    (← expect adopter (duplicate "toml/library-both-spellings" "library" "«gadget-extra»"))
  -- The refusal names the entry as written and lists the root targets of its kind unescaped.
  let unknown (label noun entry roots : String) : Expectation := {
    label, exitCode := 2,
    contains := #["RG2002",
      s!"manifest-incomplete: {noun} '{entry}' is not a root Lean {noun}", roots,
      "regula lint: INVALID CONFIGURATION (exit 2)"],
    excludes := #["RG2001", s!"«{entry}»", "«gadget-tool»", "«gadget-extra»"] }
  let rootExecutables := "the root Lean executables are [\"gadget-tool\"]"
  let rootLibraries := "the root Lean libraries are [\"Gadget\", \"gadget-extra\"]"
  IO.FS.writeFile manifest (claiming #["gadget-tol"])
  failures := failures ++ (← expect adopter
    (unknown "toml/unknown-executable" "executable" "gadget-tol" rootExecutables))
  IO.FS.writeFile manifest (claiming #["gadget-tool"] #["old-tool"])
  failures := failures ++ (← expect adopter
    (unknown "toml/unknown-excluded" "executable" "old-tool" rootExecutables))
  -- The adopter's `axiomGate --file` audit reads the same manifest for the same inventory.
  failures := failures ++ (← assess {
      label := "toml/file-unknown-excluded", exitCode := 2,
      contains := #["RG2002",
        "manifest-incomplete: executable 'old-tool' is not a root Lean executable",
        rootExecutables],
      excludes := #["RG2001", "RG2003", "build-failed", s!"file audit: {acceptanceLabel}"] }
    (← fileAudit adopter "Gadget.lean"))
  IO.FS.writeFile manifest (claiming #["gadget-tool"] (library := "gadget-extr"))
  failures := failures ++ (← expect adopter
    (unknown "toml/unknown-library" "library" "gadget-extr" rootLibraries))
  IO.FS.writeFile manifest (claiming #["gadget-tool"] (excludedLibraries := #["old-lib"]))
  failures := failures ++ (← expect adopter
    (unknown "toml/unknown-excluded-library" "library" "old-lib" rootLibraries))
  return failures

/-- `lakefile.toml` adopter, the fourth part: without the `Regula.Linter` import, an `input_dir`
filter `"*"` keeps the plain shape: the driver prints that it omits the marker, and an ordinary
build reuses its output. Decision probes of the guard (`probe`), each with one change to the
adopter and the reason that decides: the filter `"*"` keeps the plain shape, and a filter by
extension and the `Regula.Linter` import each keep the marker. Then the restored adopter is
accepted by a fresh audit. -/
private def tomlPlain (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  let originals ← tomlSetup repo adopter
  let double := adopter / "Gadget" / "Double.lean"
  let lakefile := adopter / "lakefile.toml"
  let targetOriginals := #[(lakefile, ← IO.FS.readFile lakefile)]
  let mut failures : Array String := #[]
  -- Without the `Regula.Linter` import the workspace can have the plain shape. A `lakefile.toml`
  -- `input_dir` filter is Lake's default only when it is omitted or `"*"`: then the driver omits
  -- the marker under the owner's assertion, and an ordinary build reuses its output.
  -- With any other filter, or with the import, the driver keeps the marker.
  let doubleSource ← IO.FS.readFile double
  mutate double "import Regula.Linter\n\n" ""
  let inputs := adopter / "inputs"
  IO.FS.createDirAll inputs
  IO.FS.writeFile (inputs / "notes.lean") "-- An input file.\n"
  let base ← IO.FS.readFile lakefile
  let withFilter (filter : String) : IO Unit :=
    IO.FS.writeFile lakefile (base.replace "globs = [\"Gadget\", \"Gadget.+\"]"
      s!"globs = [\"Gadget\", \"Gadget.+\"]\nneeds = [\"@/notes\"]\n\n[[input_dir]]\n\
        name = \"notes\"\npath = \"inputs\"\n{filter}")
  withFilter "filter = \"*\""
  failures := failures ++ (← expect adopter
    { accepted "toml/star-reused" with
      contains := (accepted "toml/star-reused").contains.push markerOmitted } (env := optIn))
  let ordinary ← runProcess adopter "lake" #["build"] scrubbedLeanPathEnv
  unless ordinary.succeeded && !ordinary.output.contains "] Built Gadget" do
    failures := failures.push s!"lake-lint/toml/star-reused: the ordinary build rebuilt a module: \
      {ordinary.output}"
  failures := failures ++ (← probe probes adopter "toml/star-plain" #[] none)
  withFilter "filter = { extension = [\"lean\"] }"
  failures := failures ++ (← probe probes adopter "toml/filter-marked" #[]
    (some "target notes sets the field filter"))
  withFilter "filter = \"*\""
  IO.FS.writeFile double doubleSource
  failures := failures ++ (← probe probes adopter "toml/linter-import-marked" #[]
    (some "imports Regula.Linter"))
  Regula.Filesystem.removePath .directory inputs
  restore adopter (originals ++ targetOriginals)
  failures := failures ++
      (← expect adopter (accepted "toml/fresh-restored" (fresh := true)) #["--", "--fresh"])
  return failures

/-! Controls of the weak-arguments record (`Lake.weakArgsCaption`) that the `extraDep` facet of
Regula's `lakefile.lean` mixes into each root module's trace, in the three modes whose build reads
the checkout's existing output without the audit-build marker: `lake lint` under the owner's
assertion on the plain shape, `axiomGate --incremental`, and the build-lint `policy` target. A
claimed theorem leaves an unused `have`, which the weak argument `-Dlinter.unusedVariables=false`
hides. The controls were one chain, cut into four groups (`weakArgsModes`, `weakArgsOverrides`,
`weakArgsDeclared`, `weakArgsProbes`) at the points where the chain restored the files it changed.
Each group starts from the adopter as `BuildLintQualification.setup` writes it, in a workspace of
its own (`WeakArgsAdopter`), and recreates what it reads: the override package and its
`lake update override` where it uses them. The first run of a later group starts from no build
output, where in the chain it started from the output of the controls before it. -/

/-- The weak argument of the weak-arguments controls, added to the library `Widget` of `text`. -/
private def withWeak (text : String) : String :=
  text.replace "globs := #[.andSubmodules `Widget]"
    "globs := #[.andSubmodules `Widget]\n  weakLeanArgs := #[\"-Dlinter.unusedVariables=false\"]"

/-- The lakefile `text` with the path dependency `override` required above Regula. Lake resolves a
package's `require` lines from the last to the first, so a `require` above Regula's is resolved
after it, and its facet declarations replace Regula's. -/
private def withOverride (text : String) : String :=
  text.replace "\nrequire regula " "\nrequire override from \"override\"\n\nrequire regula "

/-- The warning of the claimed theorem whose proof leaves an unused `have`. -/
private def weakArgsWarning := "Variable name `unused` is not explicitly referenced"

/-- The `lakefile.lean` adopter of the weak-arguments controls as `BuildLintQualification.setup`
writes it: its lakefile with the `policy` target (`full`) and in the plain shape (`plain`), the
module `Widget.Additional` as written (`original`) and with a claimed theorem whose proof leaves an
unused `have` (`warned`), and the three modes. -/
private structure WeakArgsAdopter where
  adopter : FilePath
  lakefile : FilePath
  full : String
  plain : String
  additional : FilePath
  original : String
  warned : String
  /-- Each mode: its label, its run, the lakefile it runs under, and its exit code on an
  incomplete result (`lake build` fails the `policy` target with exit 1). -/
  modes : Array (String × IO ProcessResult × String × UInt32)

/-- `BuildLintQualification.setup` in `adopter`, read as the adopter of the weak-arguments
controls. -/
private def weakArgsSetup (repo adopter : FilePath) : IO WeakArgsAdopter := do
  BuildLintQualification.setup repo adopter
  let lakefile := adopter / "lakefile.lean"
  let full ← IO.FS.readFile lakefile
  let plain ← leanPlain lakefile
  let additional := adopter / "Widget" / "Additional.lean"
  let original ← IO.FS.readFile additional
  let warned := original.replace "end Widget.Additional" <|
    "/-- A claimed theorem whose proof leaves an unused `have`. -/\n" ++
      "theorem withUnused (n : Nat) : n = n :=\n  have unused : 0 = 0 := rfl\n  rfl\n\n" ++
      "end Widget.Additional"
  let env := scrubbedLeanPathEnv
  let lint : IO ProcessResult := runProcess adopter "lake" #["lint"] (env ++ optIn)
  let gate : IO ProcessResult := runProcess adopter "lake" #["exe", "axiomGate", "--incremental"] env
  let policy : IO ProcessResult := runProcess adopter "lake" #["build"] env
  return {
    adopter := adopter, lakefile := lakefile, full := full, plain := plain
    additional := additional, original := original, warned := warned
    modes := #[("lint", lint, plain, 3), ("incremental", gate, plain, 3),
      ("policy", policy, full, 1)] }

/-- An ordinary build of Widget under the weak argument, which hides the warning, after which the
lakefile is `text` again. -/
private def WeakArgsAdopter.hidden (w : WeakArgsAdopter) (label text : String) :
    IO (Array String) := do
  IO.FS.writeFile w.additional w.warned
  IO.FS.writeFile w.lakefile (withWeak text)
  let ordinary ← runProcess w.adopter "lake" #["build", "Widget"] scrubbedLeanPathEnv
  IO.FS.writeFile w.lakefile text
  if ordinary.succeeded && !ordinary.output.contains weakArgsWarning then return #[]
  return #[s!"lake-lint/weak-args/{label}: the ordinary build under the weak argument did not \
    hide the warning:\n{ordinary.output}", ordinary.output]

/-- The lakefile of the path dependency `override`, which declares `facet`. -/
private def overrideLakefile (facet : String) : String :=
  "import Lake\nopen Lake DSL\n\npackage override\n\n" ++ facet

/-- The path dependency `override`, whose lakefile declares `facet`, required above Regula in the
plain shape of the adopter's lakefile and resolved by `lake update override`, which adds it to the
adopter's manifest. Returns the failures. -/
private def WeakArgsAdopter.requireOverride (w : WeakArgsAdopter) (facet : String) :
    IO (Array String) := do
  let override := w.adopter / "override"
  IO.FS.createDirAll override
  IO.FS.writeFile (override / "lean-toolchain") (← IO.FS.readFile (w.adopter / "lean-toolchain"))
  IO.FS.writeFile (override / "lakefile.lean") (overrideLakefile facet)
  let mut failures := #[]
  if withOverride w.plain == w.plain then
    failures := failures.push "lake-lint/weak-args: the adopter's lakefile has no `require regula`"
  IO.FS.writeFile w.lakefile (withOverride w.plain)
  let updated ← runProcess w.adopter "lake" #["update", "override"] scrubbedLeanPathEnv
  unless updated.succeeded do
    failures := failures.push s!"lake-lint/weak-args: `lake update override` failed:\n\
      {updated.output}"
  return failures

/-- Weak-arguments controls, the first group: in each mode, after an ordinary build under the weak
argument, removing it changes the record in Widget's trace, so the mode elaborates the module again
and reports the warning; without the theorem, a second run with nothing changed replays the modules
and is accepted. -/
private def weakArgsModes (repo adopter : FilePath) : IO (Array String) := do
  let w ← weakArgsSetup repo adopter
  let mut failures := #[]
  for (mode, run, text, incomplete) in w.modes do
    failures := failures ++ (← w.hidden s!"{mode}-hidden" text)
    failures := failures ++ (← assess {
        label := s!"weak-args/{mode}-rebuilt", exitCode := incomplete,
        contains := if mode == "lint" then #[weakArgsWarning, "RG2003", markerOmitted]
          else #[weakArgsWarning],
        excludes := #["not established"] } (← run))
    IO.FS.writeFile w.additional w.original
    let passed : Expectation :=
      { label := s!"weak-args/{mode}-accepted", exitCode := 0
        excludes := #["not established", weakArgsWarning] }
    failures := failures ++ (← assess passed (← run))
    failures := failures ++ (← assess { passed with label := s!"weak-args/{mode}-reused" } (← run))
  return failures

/-- Weak-arguments controls, the second group: a path dependency resolved after Regula that declares
Lake's own `extraDep` facet replaces Regula's, so the trace records no weak arguments; one that also
writes a record of a different library, `Helper`, in every trace stands for another facet that
writes records. After the same ordinary build and removal, `axiomGate --incremental` and the
`policy` target replay the modules and report them not established in both cases, since a
dependency declares a library facet other than Regula's (`Lake.onlyRegulaFacets`), and `lake lint`
keeps the marker, since a package declares a facet, and reports the warning. For the libraries of
Regula's package, each facet writes exactly the record Regula's own facet writes, with the encoder
taken from Regula's shipped `lakefile.lean`, so Regula's modules keep their traces and no build of
the group rebuilds them in the repository's build directory, which other groups read as it runs. -/
private def weakArgsOverrides (repo adopter : FilePath) : IO (Array String) := do
  let w ← weakArgsSetup repo adopter
  let shipped ← IO.FS.readFile (repo / "lakefile.lean")
  let recordMarker := "/-- The record of the weak arguments "
  let missing := #["lake-lint/weak-args: Regula's lakefile has no weak-arguments record"]
  let [_, rest] := shipped.splitOn s!"\n{recordMarker}" | return missing
  let body :: _ :: _ := rest.splitOn "\n@[«library_facet»]" | return missing
  let encoder := recordMarker ++ body ++ "\n"
  -- A dependency resolved after Regula declares an `extraDep` facet in place of Regula's: Lake's
  -- own (`override`), and one that also writes a record of a library `Helper` of the adopter in
  -- the trace of each library (`forged`). A package that declares a library facet other than
  -- Regula's leaves every replayed module not established, whatever the traces record. Each writes
  -- Regula's own record for Regula's libraries, so the shared build of Regula stays up to date.
  let facet (name other : String) : String :=
    encoder ++ "\n@[«library_facet»] def " ++ name ++ " : LibraryFacetDecl :=\n  \
      .mk LeanLib.extraDepFacet <| mkFacetJobConfig fun library => do\n    \
      let job ← LeanLib.extraDepFacetConfig.run library\n    \
      let record? : Option String := if library.pkg.baseName == `regula then\n        \
        some (weakLeanArgsRecord library.pkg.baseName library.name\n          \
        library.weakLeanArgs).compress\n      \
      else " ++ other ++ "\n    \
      let some record := record? | return job\n    \
      return job.mix <| Job.ofTask <| .pure <| .ok () {\n      \
      trace := BuildTrace.ofHash (pureHash record) record }\n"
  let variants : Array (String × String) := #[
    ("override", facet "lakeExtraDep" "none"),
    ("forged", facet "forgedExtraDep" "\n        \
      let name := fun (name : Lean.Name) => Lean.Json.arr \
        (name.components.map (Lean.Json.str ·.getString!)).toArray\n        \
      some (Lean.Json.arr #[.str \"weakLeanArgs\", name library.pkg.baseName,\n          \
      name `Helper, .arr #[]]).compress")]
  let mut failures ← w.requireOverride variants[0]!.2
  for (variant, facet) in variants do
    IO.FS.writeFile (adopter / "override" / "lakefile.lean") (overrideLakefile facet)
    for (mode, run, text, incomplete) in w.modes do
      failures := failures ++ (← w.hidden s!"{mode}-{variant}-hidden" (withOverride text))
      let expectation : Expectation := if mode == "lint" then
          { label := s!"weak-args/{mode}-{variant}-marked", exitCode := 3,
            contains := #[weakArgsWarning, "RG2003", markerKept, "facet declaration"],
            excludes := #["not established"] }
        else
          { label := s!"weak-args/{mode}-{variant}-unestablished", exitCode := incomplete,
            contains := #["not established: Widget"], excludes := #[weakArgsWarning] }
      failures := failures ++ (← assess expectation (← run))
  return failures

/-- Weak-arguments controls, the third group: a dependency that declares a library facet of another
name leaves Regula's facet in effect, so Widget's trace holds its own record. The two unmarked
modes accept a run that elaborates Widget again and still report Widget not established when it
replays. -/
private def weakArgsDeclared (repo adopter : FilePath) : IO (Array String) := do
  let w ← weakArgsSetup repo adopter
  -- A dependency that declares a library facet of another name leaves Regula's `extraDep` facet in
  -- effect, so Widget's trace holds its own library's record. The unmarked builds still count no
  -- record (`Lake.onlyRegulaFacets`): a first run without Widget's trace elaborates Widget and
  -- the changed module again, and a second run replays Widget and reports it not established.
  let mut failures ← w.requireOverride "library_facet other : Unit := pure Job.nil\n"
  let record := "[\\\"weakLeanArgs\\\",[\\\"build_lint_adopter\\\"],[\\\"Widget\\\"],[]]"
  let widgetTrace := adopter / ".lake" / "build" / "lib" / "lean" / "Widget.trace"
  for (mode, run, text, incomplete) in w.modes do
    if mode == "lint" then continue
    IO.FS.writeFile w.additional (w.original ++ s!"\n-- declared {mode}\n")
    IO.FS.writeFile w.lakefile (withOverride text)
    -- Without this, Widget replays from the previous mode's build.
    Regula.Filesystem.removePath .file widgetTrace
    let rebuilt : Expectation :=
      { label := s!"weak-args/{mode}-declared-rebuilt", exitCode := 0
        excludes := #["not established"] }
    failures := failures ++ (← assess rebuilt (← run))
    let trace ← match ← (IO.FS.readFile widgetTrace).toBaseIO with
      | .ok text => pure text
      | .error _ => pure ""
    unless trace.contains record do
      failures := failures.push s!"lake-lint/weak-args/{mode}-declared: Widget's trace has no \
        record of its own library:\n{trace}"
    let unestablished : Expectation :=
      { label := s!"weak-args/{mode}-declared-unestablished", exitCode := incomplete
        contains := #["not established: Widget"] }
    failures := failures ++ (← assess unestablished (← run))
  return failures

/-- Weak-arguments controls, the fourth group. Decision probes of the plain shape: Regula's own
facet is admitted (the lint mode's marker-free runs of `weakArgsModes`), while a root package named
`regula` that declares the same facet in another `lakefile.lean`, or a facet of that name with
another body, keeps the marker. A workspace that requires Regula as `checker` and an unrelated
package as `regula` records weak arguments for its root library and none for the unrelated
package's: Regula's facet decides by Lake's identity of its own package, not by name. -/
private def weakArgsProbes (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  BuildLintQualification.setup repo adopter
  let env := scrubbedLeanPathEnv
  let mut failures := #[]
  -- A root package named `regula` that declares the facet of Regula's `lakefile.lean`, verbatim,
  -- in another lakefile, and one whose facet of that name has another body: neither is the
  -- Regula that runs the probe, so each keeps the marker.
  let shipped ← IO.FS.readFile (repo / "lakefile.lean")
  let some facetText := Lake.weakArgsDeclarations shipped
    | return failures.push "lake-lint/weak-args: Regula's lakefile has no weak-arguments facet"
  let fake := adopter / "fake-regula"
  IO.FS.createDirAll fake
  IO.FS.writeFile (fake / "lean-toolchain") (← IO.FS.readFile (adopter / "lean-toolchain"))
  IO.FS.writeFile (fake / "Probe.lean") "/-! A module of the probe. -/\n"
  let fakeLakefile (facet : String) : String :=
    s!"import Lake\nopen Lake DSL\n\npackage «regula»\n\nlean_lib Probe\n\n{facet}"
  IO.FS.writeFile (fake / "lakefile.lean") (fakeLakefile facetText)
  failures := failures ++ (← probe probes fake "weak-args/regula-elsewhere" #["Probe"]
    (some "facet declaration"))
  let rewritten := facetText.replace "\"weakLeanArgs\"" "\"otherLeanArgs\""
  if rewritten == facetText then
    failures := failures.push "lake-lint/weak-args: the facet's body has no word `weakLeanArgs`"
  IO.FS.writeFile (fake / "lakefile.lean") (fakeLakefile rewritten)
  failures := failures ++ (← probe probes fake "weak-args/regula-other-body" #["Probe"]
    (some "facet declaration"))
  -- A workspace that requires Regula under the name `checker` and an unrelated package under the
  -- name `regula`: Regula's facet decides by Lake's identity of the package that declares it, not
  -- by the name `regula`, so the root's library gets a record and the unrelated package's none.
  IO.FS.writeFile (fake / "lakefile.lean") (fakeLakefile "")
  let renamed := adopter / "renamed"
  IO.FS.createDirAll renamed
  IO.FS.writeFile (renamed / "lean-toolchain") (← IO.FS.readFile (adopter / "lean-toolchain"))
  IO.FS.writeFile (renamed / "Root.lean") "/-! A module of the root. -/\n"
  IO.FS.writeFile (renamed / "lakefile.lean") s!"import Lake\nopen Lake DSL\n\npackage renamed\n\n\
    require checker from {repr repo.toString}\n\nrequire regula from {repr fake.toString}\n\n\
    lean_lib Root\n"
  let resolvedRenamed ← runProcess renamed "lake" #["update"] env
  let builtRenamed ← runProcess renamed "lake" #["build", "Root", "@regula/Probe"] env
  let traceText (path : FilePath) : IO String := do
    match ← (IO.FS.readFile path).toBaseIO with
    | .ok text => pure text
    | .error _ => pure ""
  let rootTrace ← traceText (renamed / ".lake" / "build" / "lib" / "lean" / "Root.trace")
  let probeTrace ← traceText (fake / ".lake" / "build" / "lib" / "lean" / "Probe.trace")
  if !resolvedRenamed.succeeded || !builtRenamed.succeeded then
    failures := failures.push s!"lake-lint/weak-args/renamed: the workspace did not build:\n\
      {resolvedRenamed.output}\n{builtRenamed.output}"
  else if !rootTrace.contains
      "[\\\"weakLeanArgs\\\",[\\\"renamed\\\"],[\\\"Root\\\"],[" then
    failures := failures.push s!"lake-lint/weak-args/renamed: the root library has no record:\n\
      {rootTrace}"
  else if probeTrace.isEmpty || probeTrace.contains "weakLeanArgs" then
    failures := failures.push s!"lake-lint/weak-args/renamed: the unrelated package named \
      `regula` has a record or no trace:\n{probeTrace}"
  else
    IO.println "lake-lint control weak-args/renamed: completed"
  Regula.Filesystem.removePath .directory renamed
  Regula.Filesystem.removePath .directory fake
  return failures

/-- Counterexample control for issue 291, at an external boundary: Lake's artifact cache, whose
restores the checker's proofs do not cover. A module that Lake restores from the cache gets a
trace with an empty log, so a build that restores a claimed module reports none of its warnings.
The `lakefile.lean` adopter enables the cache (`enableArtifactCache`, with every artifact copied
into the build directory) in a private `LAKE_CACHE_DIR` of the control's own workspace, and a
claimed module warns. Every `lake lint -- --fresh` must then be incomplete with RG2003: before the
checker's builds stopped using the cache, the second identical run was accepted, the module
restored from the cache the first run filled. The control then has Lake's ordinary `lake build`
restore that module from the cache into the adopter's own build output, observes the restored
trace, and requires the incremental `axiomGate` audit, whose build has the same Lean options and
so the same trace, to report the warning too. Without the warning, a fresh run is accepted. -/
private def cachedWarning (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  mutate (adopter / "lakefile.lean") "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  enableArtifactCache := true\n  restoreAllArtifacts := true"
  let additional := adopter / "Widget" / "Additional.lean"
  let original ← IO.FS.readFile additional
  mutate additional "end Widget.Additional" <|
    "/-- A claimed theorem whose proof leaves an unused `have`. -/\n" ++
      "theorem withUnused (n : Nat) : n = n :=\n  have unused : 0 = 0 := rfl\n  rfl\n\n" ++
      "end Widget.Additional"
  let env := scrubbedLeanPathEnv ++ #[("LAKE_CACHE_DIR", some (adopter / "lake-cache").toString)]
  let warning := "Variable name `unused` is not explicitly referenced"
  let incomplete (label : String) : Expectation := {
    label, exitCode := 3, contains := #["RG2003", warning, "regula lint: INCOMPLETE (exit 3)"],
    excludes := #[s!"regula lint: {acceptanceLabel}"] }
  let fresh := runProcess adopter "lake" #["lint", "--", "--fresh"] env
  let mut failures ← assess (incomplete "cache/fresh") (← fresh)
  failures := failures ++ (← assess (incomplete "cache/fresh-again") (← fresh))
  let build := runProcess adopter "lake" #["build", "Widget"] env
  let built ← build
  Regula.Filesystem.removePath .directory (adopter / ".lake" / "build")
  let restored ← build
  let trace := adopter / ".lake" / "build" / "lib" / "lean" / "Widget" / "Additional.trace"
  let synthetic := match ← (IO.FS.readFile trace).toBaseIO with
    | .ok text => (Json.parse text).toOption.bind fun json =>
        (json.getObjValAs? Bool "synthetic").toOption
    | .error _ => none
  unless built.succeeded && built.output.contains warning && restored.succeeded &&
      !restored.output.contains warning && synthetic == some true do
    failures := failures.push
      s!"lake-lint/cache/restore: no warning-free restore of the module:\n{built.output}\n\
        {restored.output}"
  failures := failures ++ (← assess {
      label := "cache/incremental-restored", exitCode := 3, contains := #["RG2003", warning],
      excludes := #["axiom gate: PASS"] }
    (← runProcess adopter "lake" #["exe", "axiomGate", "--incremental"] env))
  -- The positive control: without the warning, the cache-enabled adopter is accepted.
  IO.FS.writeFile additional original
  failures := failures ++ (← assess (accepted "cache/fresh-restored" (fresh := true)) (← fresh))
  return failures

/-- `cachedWarning` with the artifact cache enabled only in a dependency's own configuration,
which Lake reads before `LAKE_ARTIFACT_CACHE`: a path dependency inside the `lakefile.lean`
adopter, a Git repository of its own and so a trusted dependency that each audit builds in place,
enables the cache (`enableArtifactCache`, with every artifact copied into the build
directory) in a private `LAKE_CACHE_DIR` of the control's own workspace, and its module, which a
claimed module imports, warns. Lake's ordinary `lake build` fills the cache with that module,
and its build output is then removed, as in a new checkout. A `lake lint -- --fresh` must then
elaborate the module again and be incomplete with RG2003, where restoring it from the cache would
show no warning. Without the warning, a fresh run is accepted. -/
private def dependencyCachedWarning (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  let dependency := adopter / "dep"
  IO.FS.createDirAll dependency
  let initialized ← runProcess dependency "git" #["init", "-q"]
  unless initialized.succeeded do
    return #[s!"lake-lint/dependency-cache: git init failed: {initialized.output}"]
  IO.FS.writeFile (dependency / "lakefile.lean") <|
    "import Lake\nopen Lake DSL\n\npackage dep where\n  enableArtifactCache := true\n" ++
      "  restoreAllArtifacts := true\n\nlean_lib Dep\n"
  let module := dependency / "Dep.lean"
  let warned := "/-! A dependency module. -/\n\n" ++
    "/-- A theorem whose proof leaves an unused `have`. -/\n" ++
    "theorem depWithUnused (n : Nat) : n = n :=\n  have unused : 0 = 0 := rfl\n  rfl\n"
  IO.FS.writeFile module warned
  mutate (adopter / "lakefile.lean") "require regula from"
    "require dep from \"dep\"\n\nrequire regula from"
  let manifest ← readJson (adopter / "lake-manifest.json")
  let packages : Array Json ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  writeJson (adopter / "lake-manifest.json") <| manifest.setObjVal! "packages" <|
    toJson (#[Json.mkObj [
      ("name", toJson "dep"), ("scope", toJson ""), ("configFile", toJson "lakefile.lean"),
      ("manifestFile", toJson "lake-manifest.json"), ("inherited", toJson false),
      ("type", toJson "path"), ("dir", toJson "dep")]] ++ packages)
  let additional := adopter / "Widget" / "Additional.lean"
  IO.FS.writeFile additional ("import Dep\n" ++ (← IO.FS.readFile additional))
  let env := scrubbedLeanPathEnv ++ #[("LAKE_CACHE_DIR", some (adopter / "lake-cache").toString)]
  let warning := "Variable name `unused` is not explicitly referenced"
  let filled ← runProcess adopter "lake" #["build", "Dep"] env
  let mut failures : Array String := #[]
  unless filled.succeeded && filled.output.contains warning do
    failures := failures.push s!"lake-lint/dependency-cache/fill: {filled.output}"
  if ← (dependency / ".lake" / "build").pathExists then
    Regula.Filesystem.removePath .directory (dependency / ".lake" / "build")
  let fresh := runProcess adopter "lake" #["lint", "--", "--fresh"] env
  failures := failures ++ (← assess {
      label := "dependency-cache/fresh", exitCode := 3,
      contains := #["RG2003", warning, "regula lint: INCOMPLETE (exit 3)"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } (← fresh))
  -- The positive control: without the warning, the adopter is accepted.
  IO.FS.writeFile module <|
    "/-! A dependency module. -/\n\n/-- A theorem. -/\n" ++
      "theorem depReflexive (n : Nat) : n = n := rfl\n"
  failures := failures ++
    (← assess (accepted "dependency-cache/fresh-restored" (fresh := true)) (← fresh))
  return failures

/-- Counterexample control for the class the first review of issue 291 found: a claimed module
whose elaboration the audit's build neither performs nor replays. The `lakefile.lean` adopter's
claimed library builds no module by default (`defaultFacets := #[]`), the artifact cache is on as
in `cachedWarning`, and a claimed module warns. Lake's ordinary `lake build Widget:leanArts`
elaborates the modules and fills the cache, and the incremental `axiomGate` audit must replay the
module's warning and report RG2003: when the audit built only the library's default facets, it
built nothing, observed no warning and was accepted. Lake's build then restores the module from
the cache into a removed build output, and the incremental audit must elaborate it again and
report RG2003, as must a fresh `lake lint`. Without the warning, a fresh run is accepted. -/
private def emptyFacetsWarning (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  mutate (adopter / "lakefile.lean") "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  enableArtifactCache := true\n  restoreAllArtifacts := true"
  mutate (adopter / "lakefile.lean") "globs := #[.andSubmodules `Widget]"
    "globs := #[.andSubmodules `Widget]\n  defaultFacets := #[]"
  let additional := adopter / "Widget" / "Additional.lean"
  let original ← IO.FS.readFile additional
  mutate additional "end Widget.Additional" <|
    "/-- A claimed theorem whose proof leaves an unused `have`. -/\n" ++
      "theorem withUnused (n : Nat) : n = n :=\n  have unused : 0 = 0 := rfl\n  rfl\n\n" ++
      "end Widget.Additional"
  let env := scrubbedLeanPathEnv ++ #[("LAKE_CACHE_DIR", some (adopter / "lake-cache").toString)]
  let warning := "Variable name `unused` is not explicitly referenced"
  let reported (label : String) : Expectation := {
    label, exitCode := 3, contains := #["RG2003", warning], excludes := #["axiom gate: PASS"] }
  let incremental := runProcess adopter "lake" #["exe", "axiomGate", "--incremental"] env
  let build := runProcess adopter "lake" #["build", "Widget:leanArts"] env
  let built ← build
  let mut failures : Array String := #[]
  unless built.succeeded && built.output.contains warning do
    failures := failures.push s!"lake-lint/empty-facets/build: {built.output}"
  failures := failures ++ (← assess (reported "empty-facets/incremental") (← incremental))
  Regula.Filesystem.removePath .directory (adopter / ".lake" / "build")
  let restored ← build
  let trace := adopter / ".lake" / "build" / "lib" / "lean" / "Widget" / "Additional.trace"
  let synthetic := match ← (IO.FS.readFile trace).toBaseIO with
    | .ok text => (Json.parse text).toOption.bind fun json =>
        (json.getObjValAs? Bool "synthetic").toOption
    | .error _ => none
  unless restored.succeeded && !restored.output.contains warning && synthetic == some true do
    failures := failures.push
      s!"lake-lint/empty-facets/restore: no warning-free restore of the module:\n\
        {restored.output}"
  failures := failures ++
    (← assess (reported "empty-facets/incremental-restored") (← incremental))
  failures := failures ++ (← assess {
      label := "empty-facets/fresh", exitCode := 3,
      contains := #["RG2003", warning, "regula lint: INCOMPLETE (exit 3)"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] }
    (← runProcess adopter "lake" #["lint", "--", "--fresh"] env))
  -- The positive control: without the warning, the audit builds the modules itself.
  IO.FS.writeFile additional original
  failures := failures ++ (← assess (accepted "empty-facets/fresh-restored" (fresh := true))
    (← runProcess adopter "lake" #["lint", "--", "--fresh"] env))
  return failures

/-- Counterexample control for the class the second review of issue 291 found: a claimed name
that the audit's build read as Lake target syntax, in which a `/` names a package. The
`lakefile.toml` adopter's claimed library is named `foo/bar`, which the manifest records as
`«foo/bar»`, and a path dependency named `«foo` has a library named `bar»` that builds no module
by default: Lake's command line reads `«foo/bar»` as that library. Lake's ordinary
`lake build +Gadget:leanArts` elaborates the claimed root module, which warns, and the incremental
`axiomGate` audit must find the claimed library itself and report RG2003: when the audit's build
read the claimed name as target syntax, it built the dependency's empty library, observed no
warning and was accepted. Without the warning, a fresh run is accepted. -/
private def escapedNameWarning (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter "lake-lint-toml" #["Gadget.lean", "Gadget/Double.lean"]
    "lakefile.toml"
  let lakefile := adopter / "lakefile.toml"
  mutate lakefile "defaultTargets = [\"Gadget\"]\n" ""
  mutate lakefile "name = \"Gadget\"" "name = \"foo/bar\""
  mutate lakefile "[[require]]\nname = \"regula\""
    "[[require]]\nname = \"«foo\"\npath = \"dep\"\n\n[[require]]\nname = \"regula\""
  let dependency := adopter / "dep"
  IO.FS.createDirAll dependency
  IO.FS.writeFile (dependency / "lakefile.toml")
    "name = \"«foo\"\n\n[[lean_lib]]\nname = \"bar»\"\ndefaultFacets = []\n"
  IO.FS.writeFile (dependency / "bar».lean") "/-! A dependency module that no build needs. -/\n"
  let lakeManifest ← readJson (adopter / "lake-manifest.json")
  let packages : Array Json ← IO.ofExcept <| lakeManifest.getObjValAs? (Array Json) "packages"
  writeJson (adopter / "lake-manifest.json") <| lakeManifest.setObjVal! "packages" <|
    toJson (#[Json.mkObj [
      -- Lean writes the package name `«foo` escaped, as `««foo»`, and reads it back.
      ("name", toJson (Name.mkSimple "«foo")), ("scope", toJson ""),
      ("configFile", toJson "lakefile.toml"),
      ("manifestFile", toJson "lake-manifest.json"), ("inherited", toJson false),
      ("type", toJson "path"), ("dir", toJson "dep")]] ++ packages)
  mutate (adopter / "foundation_manifest.json") "\"library\": \"Gadget\""
    "\"library\": \"«foo/bar»\""
  let gadget := adopter / "Gadget.lean"
  let original ← IO.FS.readFile gadget
  IO.FS.writeFile gadget <| original ++
    "\n/-- A claimed theorem whose proof leaves an unused `have`. -/\n" ++
    "theorem withUnused (n : Nat) : n = n :=\n  have unused : 0 = 0 := rfl\n  rfl\n"
  let warning := "Variable name `unused` is not explicitly referenced"
  let built ← runProcess adopter "lake" #["build", "+Gadget:leanArts"] scrubbedLeanPathEnv
  let mut failures : Array String := #[]
  unless built.succeeded && built.output.contains warning do
    failures := failures.push s!"lake-lint/escaped-name/build: {built.output}"
  failures := failures ++ (← assess {
      label := "escaped-name/incremental", exitCode := 3, contains := #["RG2003", warning],
      excludes := #["axiom gate: PASS"] }
    (← runProcess adopter "lake" #["exe", "axiomGate", "--incremental"] scrubbedLeanPathEnv))
  -- The positive control: without the warning, the claimed library is found and accepted.
  IO.FS.writeFile gadget original
  failures := failures ++ (← assess (accepted "escaped-name/fresh-restored" (fresh := true))
    (← runProcess adopter "lake" #["lint", "--", "--fresh"] scrubbedLeanPathEnv))
  return failures

/-- The module of the adopter's path dependency `build_lint_support` for the path-dependency
controls: a reference computation, the replacement a `csimp` theorem makes the compiler run, and
a caller of the reference. Honest, the replacement equals the reference and the theorem is
proved. Forged, the replacement differs and the theorem is a declaration that the kernel does not
accept, added with `debug.skipKernelTC` as in `Fixtures.Mutations.ForgedAdmissionCorrespondence`. -/
private def supportSource (forged : Bool) : String :=
  let correspondence := if forged then [
      "open Lean Elab Command in",
      "set_option debug.skipKernelTC true in",
      "run_cmd liftCoreM do",
      "  let proposition := mkApp3 (mkConst ``Eq [.succ .zero])",
      "    (mkForall .anonymous .default (mkConst ``Nat) (mkConst ``Nat))",
      "    (mkConst `Support.reference) (mkConst `Support.replacement)",
      "  Lean.addDecl (.thmDecl {",
      "    name := `Support.correspondence",
      "    levelParams := []",
      "    type := proposition",
      "    value := mkConst ``True.intro })",
      "attribute [csimp] Support.correspondence"]
    else [
      "/-- The replacement is the reference. -/",
      "@[csimp] theorem Support.correspondence :",
      "    @Support.reference = @Support.replacement := rfl"]
  "\n".intercalate <| ["import Lean", "/-! A path dependency of the adopter. -/",
    "/-- The reference computation. -/", "def Support.reference (n : Nat) : Nat := n",
    "/-- The replacement the compiler runs. -/",
    s!"def Support.replacement (n : Nat) : Nat := {if forged then "n + 1" else "n"}"] ++
    correspondence ++ ["/-- A caller of the reference. -/",
      "def Support.caller (n : Nat) : Nat := Support.reference n", ""]

/-- The adopter of the path-dependency controls: `examples/build-lint` with the path dependency
`build_lint_support` in its Git work tree (`BuildLintQualification.addSupport`), whose honest
module a claimed module imports, under the claimed checked execution of the adopter. The eight
parts of these controls (`pathOwned`, `pathOwnedChecks`, `pathForged`, `pathConfig`,
`pathReserved`, `pathEscapes`, `pathOverrides`, `pathTrusted`) are one chain of controls in this
order, cut at points where the chain has restored every file it changed, apart from the
dependency's module, which the control after the cut writes again, from the copies of the
dependency that the override controls leave and that no later configuration names, and from build
output. Each part starts from this adopter in a workspace of its own, so each control reads the
files it read in the chain. The first control of a later part that builds starts from no build
output, where in the chain it started from the output of the controls before it. -/
private def pathSetup (repo adopter : FilePath) : IO Unit := do
  BuildLintQualification.setup repo adopter
  BuildLintQualification.addSupport adopter (supportSource false) (owned := true)
  mutate (adopter / "Widget.lean") "import Regula.Contract\n"
    "import Regula.Contract\nimport Support\n"
  mutate (adopter / "Widget.lean") "end Widget"
    "/-- Runs the dependency's caller. -/\ndef useCaller (n : Nat) : Nat := Support.caller n\n\
      \nend Widget"

/-- An accepted run of the path-dependency adopter whose account trusts `regula` alone and never
names the owned dependency. -/
private def ownedAccepted (label : String) (fresh : Bool := false) : Expectation :=
  let positive := accepted label fresh
  { positive with
      contains := positive.contains.push
        "trusted dependencies, not wholly replayed through Lean's kernel: regula\n",
      excludes := positive.excludes.push "build_lint_support" }

/-- The driver's own line when it refuses to build its audit worker for a workspace outside the
supported scope (`Lint.lint`). -/
private def unbuiltWorker :=
  "regula lint: the workspace is outside the supported scope, so the audit worker is not built"

/-- A workspace in which `name` has a second provider beside the owned dependency, which every
audit refuses before the driver builds its audit worker. -/
private def ambiguous (label name : String) : Expectation := {
  label, exitCode := 3,
  contains := #["lake-query-malformed", s!"module {name} is provided by package",
    "package 'build_lint_support'", "one provider for each module name", unbuiltWorker,
    "regula lint: INCOMPLETE (exit 3)"] }

/-- The path-dependency controls (`pathSetup`): a path dependency of an adopter that is a
repository of its own, which a claimed module imports, under the claimed checked execution of
`examples/build-lint`. In the adopter's Git work
tree the dependency is owned: the account trusts only `regula`; the fresh audit builds it in the
copy and writes nothing to the original's build output; an axiom it declares that nothing uses is
refused (RG1001); a theorem it declares that uses `Classical.choice` meets its own module's
Standard-Logical profile, not the kernel-only claim of the library importing it; its forged
correspondence theorem is refused by kernel replay as incomplete (RG2005) in the incremental and
the fresh audit. A build or library directory other than Lake's default that it configures is
refused from its loaded configuration before the driver builds its audit worker, under `--fresh`
and in an incremental audit, and so is a root `buildDir` that names the original checkout's own
build output; the fresh audit leaves the original's build output absent; these controls do not reach
the origin check that follows a build. An override that selects another configuration file is
loaded by the fresh copy too. A configuration that computes from its own directory a Lean option,
or which of its libraries provides a module, makes the fresh copy's Lake load differ, which is
refused. A package that provides `Regula.Contract` with a source other than the checker's own is
refused before any environment loads: a dependency required after the checker or before it, and a
vendored package that Lake loads under the name `regula`. An executable root `Main` of the root
package is accepted beside `regula`'s own, since a trusted package's executable roots are not
counted. A name that two trusted packages provide, and neither the root package nor an owned
dependency, is accepted too (`Lake.checkOneProvider`), though no control here builds such a
workspace. A module name that an owned package and a second package provide, an executable root
`Main` of the root package and of the dependency, or `Support` of the dependency and of a second
owned one, is refused before the driver builds its audit worker. So is a library root
`Regula.«<directory>/Payload»` that a claimed module imports, whose absolute component would put
its source and artifact outside the
dependency's directories, and so is the root `Regula.«../Payload»`, whose `..` segment would leave
them. A `lake lint -- --project` from such a workspace for another project is refused before any
audit, since the driver audits only the dispatching workspace (`Lint.lint`), though no control
here runs that case. A
claimed module's import of `Widget.«<adopter directory>/Payload»`, which Lake builds under
the claimed library's glob outside every output directory, is refused once the module is loaded.
An override in `.lake/package-overrides.json` that selects the dependency in place of one
elsewhere is owned in the fresh copy too, and of two override entries the fresh copy loads the
last, as Lake does. As a Git work tree of its own it is trusted: the forged theorem
supplies no correspondence, so the boundary it was to prove is rejected (RG3002), and with an
honest module the account names it. These observe Git's work-tree discovery, Lake's path
dependencies and overrides and the fresh copy, which the ownership theorems (`sameWorkTree_iff`,
`contains_ownedModuleSet`) take as given.

This first part holds the accepted owned dependency, incremental and fresh. -/
private def pathOwned (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let mut failures ← expect adopter (ownedAccepted "path/owned")
  if !failures.isEmpty then return failures
  -- The fresh audit builds the owned dependency in its copy: the original's output stays absent.
  Regula.Filesystem.removePath .directory (support / ".lake" / "build")
  failures := failures ++
    (← expect adopter (ownedAccepted "path/owned-fresh" (fresh := true)) #["--", "--fresh"])
  if ← (support / ".lake" / "build").pathExists then
    failures := failures.push "lake-lint/path/owned-fresh: the fresh audit wrote the original \
      dependency's build output"
  return failures

/-- The second part of the path-dependency controls (`pathSetup`, `pathOwned`): the owned
dependency's unused axiom and its Standard-Logical theorem. -/
private def pathOwnedChecks (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let mut failures : Array String := #[]
  IO.FS.writeFile (support / "Support.lean") <| supportSource false ++
    "/-- An axiom that nothing uses. -/\naxiom Support.unused : False\n"
  failures := failures ++ (← expect adopter {
      label := "path/owned-axiom", exitCode := 1,
      contains := #["RG1001", "Support.unused", "regula lint: VIOLATION (exit 1)"] })
  -- A declaration of an owned dependency meets its own module's profile, Standard-Logical, not
  -- the kernel-only profile of the library that imports it.
  IO.FS.writeFile (support / "Support.lean") <| supportSource false ++
    "/-- Excluded middle, which nothing uses. -/\ntheorem Support.excluded (p : Prop) : p ∨ ¬p := \
      Classical.em p\n"
  failures := failures ++ (← expect adopter (ownedAccepted "path/owned-standard-logical"))
  return failures

/-- The third part of the path-dependency controls (`pathSetup`, `pathOwned`): the owned
dependency's forged correspondence theorem, and its output directories and the root's. -/
private def pathForged (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  IO.FS.writeFile (support / "Support.lean") (supportSource true)
  let refused (label : String) : Expectation := {
    label, exitCode := 3,
    contains := #["RG2005", "kernel-admission", "regula lint: INCOMPLETE (exit 3)"] }
  let mut failures ← expect adopter (refused "path/owned-forged")
  failures := failures ++
    (← expect adopter (refused "path/owned-forged-fresh") #["--", "--fresh"])
  IO.FS.writeFile (support / "Support.lean") (supportSource false)
  -- Every audit refuses, before any build, an owned package that sets an output directory other
  -- than Lake's default: a build directory or a library directory in the original checkout, under
  -- `--fresh` and in an incremental audit. The fresh audit leaves the original's build output
  -- absent.
  let supportLakefile := support / "lakefile.toml"
  let supportConfiguration ← IO.FS.readFile supportLakefile
  let layout (label : String) : Expectation := {
    label, exitCode := 3,
    contains := #["lake-workspace-load-failed", "default output layout", unbuiltWorker,
      "regula lint: INCOMPLETE (exit 3)"] }
  IO.FS.writeFile supportLakefile <| supportConfiguration.replace "[[lean_lib]]"
    s!"buildDir = {toJson (support / ".lake" / "build").toString |>.compress}\n[[lean_lib]]"
  failures := failures ++ (← expect adopter (layout "path/owned-build-outside") #["--", "--fresh"])
  IO.FS.writeFile supportLakefile <| supportConfiguration.replace "[[lean_lib]]"
    s!"leanLibDir = {toJson (support / ".lake" / "build" / "lib" / "lean").toString |>.compress}\n\
      [[lean_lib]]"
  if ← (support / ".lake" / "build").pathExists then
    Regula.Filesystem.removePath .directory (support / ".lake" / "build")
  failures := failures ++ (← expect adopter (layout "path/owned-libdir-outside") #["--", "--fresh"])
  if ← (support / ".lake" / "build").pathExists then
    failures := failures.push "lake-lint/path/owned-libdir-outside: the fresh audit wrote the \
      original dependency's build output"
  failures := failures ++ (← expect adopter (layout "path/owned-libdir-incremental"))
  IO.FS.writeFile supportLakefile supportConfiguration
  -- The root package's `buildDir` as an absolute path to its own build output in the original
  -- checkout: the driver refuses before it builds its audit worker, and the fresh audit before it
  -- copies or builds.
  let rootLakefile := adopter / "lakefile.lean"
  let rootConfiguration ← IO.FS.readFile rootLakefile
  let rootBuild := (toJson (adopter / ".lake" / "build").toString).compress
  IO.FS.writeFile rootLakefile <| rootConfiguration.replace "  lintDriver := \"regula/lint\"\n"
    s!"  lintDriver := \"regula/lint\"\n  buildDir := {rootBuild}\n"
  failures := failures ++ (← expect adopter (layout "path/root-build-outside") #["--", "--fresh"])
  return failures

/-- The fourth part of the path-dependency controls (`pathSetup`, `pathOwned`): an override that
selects another configuration file. -/
private def pathConfig (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let mut failures : Array String := #[]
  -- An override that keeps the dependency's directory but selects another configuration file,
  -- whose source directory holds a module with an axiom that nothing uses: the fresh copy loads
  -- the configuration the original's Lake load selects, so both audits refuse the axiom.
  IO.FS.writeFile (support / "alt.toml")
    "name = \"build_lint_support\"\nsrcDir = \"actual\"\n[[lean_lib]]\nname = \"Support\"\n"
  IO.FS.createDirAll (support / "actual")
  IO.FS.writeFile (support / "actual" / "Support.lean") <| supportSource false ++
    "/-- An axiom that nothing uses. -/\naxiom Support.unused : False\n"
  let configManifestPath := adopter / "lake-manifest.json"
  let configManifest ← readJson configManifestPath
  let configEntries ← IO.ofExcept <| configManifest.getObjValAs? (Array Json) "packages"
  let some configEntry := configEntries.find? isSupportEntry
    | return failures.push "lake-lint/path: the manifest has no build_lint_support entry"
  let relative := configEntry.setObjVal! "dir" (toJson "support")
  writeJson configManifestPath <| configManifest.setObjVal! "packages" <| toJson <|
    configEntries.map fun item => if JsonAgreement.conforms item configEntry then relative else item
  let alternative ← IO.ofExcept <| _root_.Lake.PackageEntry.fromJson?
    (relative.setObjVal! "configFile" (toJson "alt.toml"))
  _root_.Lake.Manifest.saveEntries (adopter / ".lake" / "package-overrides.json") #[alternative]
  let configured (label : String) : Expectation := {
    label, exitCode := 1,
    contains := #["RG1001", "Support.unused", "regula lint: VIOLATION (exit 1)"] }
  failures := failures ++ (← expect adopter (configured "path/owned-config"))
  failures := failures ++
    (← expect adopter (configured "path/owned-config-fresh") #["--", "--fresh"])
  return failures

/-- The fifth part of the path-dependency controls (`pathSetup`, `pathOwned`): the names reserved
to the checker, and an executable root `Main` of the root package and of the dependency. -/
private def pathReserved (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let supportLakefile := support / "lakefile.toml"
  let supportConfiguration ← IO.FS.readFile supportLakefile
  let mut failures : Array String := #[]
  -- A package that provides a module under a prefix reserved to the checker with a source other
  -- than the checker's own, here `Regula.Contract` with an axiom that nothing uses, is refused
  -- before any environment loads, whichever package Lake resolves the name to. Lake itself refuses
  -- to build the checker in this workspace (it cannot disambiguate the two `Regula.Contract`), so
  -- these controls run the checker built in this repository.
  let gate (label : String) : IO (Array String) := do
    assess {
        label, exitCode := 3,
        contains := #["Regula.Contract", "reserved to the checker", "not the text"] }
      (← runProcess adopter (repo / ".lake" / "build" / "bin" / "axiomGate").toString
        #["--incremental", "--project", adopter.toString] scrubbedLeanPathEnv)
  let contract := (← IO.FS.readFile (repo / "lean" / "Regula" / "Contract.lean")) ++
    "\n/-- An axiom that nothing uses. -/\naxiom Regula.Contract.unused : False\n"
  IO.FS.createDirAll (support / "Regula")
  IO.FS.writeFile (support / "Regula" / "Contract.lean") contract
  IO.FS.writeFile supportLakefile <| supportConfiguration ++
    "[[lean_lib]]\nname = \"SupportContract\"\nroots = [\"Regula.Contract\"]\n"
  failures := failures ++ (← gate "path/owned-reserved-name")
  -- The same with the dependency required before the checker, so that Lake resolves the name to
  -- the checker: the dependency's own modules are still checked.
  let adopterLakefile := adopter / "lakefile.lean"
  let adopterConfiguration ← IO.FS.readFile adopterLakefile
  let supportRequire := "\nrequire build_lint_support from \"support\"\n"
  let some regulaRequire := (adopterConfiguration.splitOn "\n").find? (·.startsWith "require regula")
    | return failures.push "lake-lint/path: the adopter does not require regula"
  IO.FS.writeFile adopterLakefile <| (adopterConfiguration.replace supportRequire "\n").replace
    regulaRequire ("require build_lint_support from \"support\"\n" ++ regulaRequire)
  failures := failures ++ (← gate "path/owned-reserved-name-first")
  IO.FS.writeFile adopterLakefile adopterConfiguration
  IO.FS.writeFile supportLakefile supportConfiguration
  Regula.Filesystem.removePath .directory (support / "Regula")
  -- A vendored package in the adopter's work tree that Lake loads under the checker's package name
  -- `regula`, with the same modified `Regula.Contract`: the name grants nothing.
  let vendor := adopter / "vendor"
  IO.FS.createDirAll (vendor / "lean" / "Regula")
  IO.FS.writeFile (vendor / "lean" / "Regula" / "Contract.lean") contract
  IO.FS.writeFile (vendor / "lean-toolchain") (← IO.FS.readFile (adopter / "lean-toolchain"))
  IO.FS.writeFile (vendor / "lakefile.toml")
    "name = \"regula\"\n[[lean_lib]]\nname = \"Regula\"\nsrcDir = \"lean\"\nroots = [\"Regula.Contract\"]\n"
  let vendorManifestPath := adopter / "lake-manifest.json"
  let vendorManifest ← readJson vendorManifestPath
  let vendorEntries ← IO.ofExcept <| vendorManifest.getObjValAs? (Array Json) "packages"
  writeJson vendorManifestPath <| vendorManifest.setObjVal! "packages" <| toJson <|
    vendorEntries.map fun item =>
      if JsonAgreement.conforms (item.getObjValD "name") (toJson "regula") then
        (item.setObjVal! "dir" (toJson "vendor")).setObjVal! "configFile" (toJson "lakefile.toml")
      else item
  IO.FS.writeFile adopterLakefile <|
    adopterConfiguration.replace regulaRequire "require regula from \"vendor\""
  failures := failures ++ (← gate "path/vendored-regula-name")
  IO.FS.writeFile adopterLakefile adopterConfiguration
  writeJson vendorManifestPath vendorManifest
  Regula.Filesystem.removePath .directory vendor
  -- An executable of the root package with root module `Main`, which the executable `auditApp` of
  -- the trusted `regula` also has: a trusted package's executable roots are not counted, so the
  -- incremental audit accepts it. An unused executable of the owned dependency with root module
  -- `Main` of its own package is a second provider, which every audit refuses before any build,
  -- whichever environment would load either.
  let manifestFile := adopter / "foundation_manifest.json"
  let adopterManifest ← IO.FS.readFile manifestFile
  let mainSource := "/-! An entry point. -/\n\n/-- Runs nothing. -/\ndef main : IO Unit := pure ()\n"
  IO.FS.writeFile (adopter / "Main.lean") mainSource
  IO.FS.writeFile adopterLakefile <| adopterConfiguration ++
    "\nlean_exe widgetMain where\n  root := `Main\n"
  mutate manifestFile "\"excluded-executables\": []"
    "\"excluded-executables\": [{\"executable\": \"widgetMain\", \"rationale\": \"An entry point \
      outside the claimed surface.\"}]"
  failures := failures ++ (← expect adopter (ownedAccepted "path/root-executable-main"))
  IO.FS.writeFile (support / "Main.lean") mainSource
  IO.FS.writeFile supportLakefile <| supportConfiguration ++
    "[[lean_exe]]\nname = \"supportUtil\"\nroot = \"Main\"\n"
  failures := failures ++ (← expect adopter (ambiguous "path/owned-executable-names" "Main"))
  IO.FS.writeFile adopterLakefile adopterConfiguration
  IO.FS.writeFile manifestFile adopterManifest
  IO.FS.writeFile supportLakefile supportConfiguration
  Regula.Filesystem.removePath .file (adopter / "Main.lean")
  Regula.Filesystem.removePath .file (support / "Main.lean")
  return failures

/-- The sixth part of the path-dependency controls (`pathSetup`, `pathOwned`): a second owned
provider of `Support`, configurations computed from the dependency's own directory, module names
that would leave its directories, and a library of no module. -/
private def pathEscapes (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let supportLakefile := support / "lakefile.toml"
  let supportConfiguration ← IO.FS.readFile supportLakefile
  let adopterLakefile := adopter / "lakefile.lean"
  let adopterConfiguration ← IO.FS.readFile adopterLakefile
  let mut failures : Array String := #[]
  -- A second owned path dependency that provides `Support` with the same source: the audit refuses
  -- the name before any build, where Lake's build would refuse the import as ambiguous.
  let second := adopter / "support2"
  IO.FS.createDirAll second
  IO.FS.writeFile (second / "Support.lean") (← IO.FS.readFile (support / "Support.lean"))
  IO.FS.writeFile (second / "lean-toolchain") (← IO.FS.readFile (adopter / "lean-toolchain"))
  IO.FS.writeFile (second / "lakefile.toml")
    "name = \"build_lint_support_two\"\n[[lean_lib]]\nname = \"Support\"\n"
  let manifestPath := adopter / "lake-manifest.json"
  let projectManifest ← readJson manifestPath
  let entries ← IO.ofExcept <| projectManifest.getObjValAs? (Array Json) "packages"
  let some supportEntry := entries.find? isSupportEntry
    | return failures.push "lake-lint/path: the manifest has no build_lint_support entry"
  writeJson manifestPath <| projectManifest.setObjVal! "packages" <| toJson <| entries.push <|
    (supportEntry.setObjVal! "name" (toJson "build_lint_support_two")).setObjVal! "dir"
      (toJson second.toString)
  IO.FS.writeFile adopterLakefile <| adopterConfiguration ++
    "\nrequire build_lint_support_two from \"support2\"\n"
  failures := failures ++ (← expect adopter (ambiguous "path/owned-duplicate-provider" "Support"))
  IO.FS.writeFile adopterLakefile adopterConfiguration
  writeJson manifestPath projectManifest
  Regula.Filesystem.removePath .directory second
  -- The owned dependency's configuration as a `lakefile.lean`, for the two controls below.
  let asLean (configuration : String) : IO Unit := do
    writeJson manifestPath <| projectManifest.setObjVal! "packages" <| toJson <|
      entries.map fun item =>
        if isSupportEntry item then
          item.setObjVal! "configFile" (toJson "lakefile.lean")
        else item
    Regula.Filesystem.removePath .file supportLakefile
    IO.FS.writeFile (support / "lakefile.lean") configuration
  let restore : IO Unit := do
    Regula.Filesystem.removePath .file (support / "lakefile.lean")
    IO.FS.writeFile supportLakefile supportConfiguration
    writeJson manifestPath projectManifest
  let differs (label : String) : Expectation := {
    label, exitCode := 3,
    contains := #["lake-workspace-load-failed", "differs", "regula lint: INCOMPLETE (exit 3)"] }
  -- An owned dependency whose `lakefile.lean` computes a Lean option from its own directory: the
  -- fresh copy's Lake load resolves another option for it, and the copy is refused.
  asLean "import Lake\nopen Lake DSL\n\npackage build_lint_support where\n  leanOptions := \
    #[⟨`maxRecDepth, .ofNat (512 + (__dir__).toString.length)⟩]\n\nlean_lib Support\n"
  failures := failures ++ (← expect adopter (differs "path/owned-options-fresh") #["--", "--fresh"])
  restore
  -- An owned dependency whose `lakefile.lean` gives its modules `Support` and `Aux` to libraries
  -- `Low` and `High`, with fixed options, by the length of its own directory: the fresh copy's
  -- longer directory swaps them, so Lake builds `Support` there with the other option, although
  -- each library's name and options and each module's source stay the same. The copy is refused.
  IO.FS.writeFile (support / "Aux.lean") "/-! An auxiliary module. -/\n"
  asLean s!"import Lake\nopen Lake DSL\n\npackage build_lint_support\n\n\
    def swapped : Bool := (__dir__).toString.length > {support.toString.length + 20}\n\n\
    lean_lib Low where\n  roots := if swapped then #[`Aux] else #[`Support]\n  \
    leanOptions := #[⟨`maxRecDepth, .ofNat 512⟩]\n\n\
    lean_lib High where\n  roots := if swapped then #[`Support] else #[`Aux]\n  \
    leanOptions := #[⟨`maxRecDepth, .ofNat 1024⟩]\n"
  failures := failures ++
    (← expect adopter (differs "path/owned-target-swap-fresh") #["--", "--fresh"])
  restore
  Regula.Filesystem.removePath .file (support / "Aux.lean")
  -- An owned dependency whose library root is `Regula.«<its own directory>/Payload»`, which a
  -- claimed module imports, with an axiom that nothing uses. The second component is an absolute
  -- path, so `Lean.modToFilePath` places the module's source and artifact at
  -- `<its own directory>/Payload`, outside its source and output directories, and the checker's
  -- source of that name would be the dependency's own file. Every audit refuses the name before
  -- any path is built from it (`Lake.checkModuleNames`).
  IO.FS.writeFile (support / "Payload.lean")
    "/-! A payload. -/\n\n/-- An axiom that nothing uses. -/\naxiom Payload.bad : False\n"
  asLean "import Lake\nopen Lake DSL\n\npackage build_lint_support\n\nlean_lib Support\n\n\
    lean_lib Payload where\n  roots := #[.str `Regula ((__dir__) / \"Payload\").toString]\n"
  let claimed := adopter / "Widget.lean"
  let claimedSource ← IO.FS.readFile claimed
  mutate claimed "import Support\n" s!"import Support\nimport Regula.«{(support / "Payload").toString}»\n"
  failures := failures ++ (← expect adopter {
      label := "path/owned-escaping-name", exitCode := 3,
      contains := #["lake-query-malformed", "is an absolute path",
        "regula lint: INCOMPLETE (exit 3)"] })
  IO.FS.writeFile claimed claimedSource
  restore
  -- The same payload under the library root `Regula.«../Payload»`, whose `..` segment would leave
  -- the source directory below `Regula`: refused the same way.
  asLean "import Lake\nopen Lake DSL\n\npackage build_lint_support\n\nlean_lib Support\n\n\
    lean_lib Payload where\n  roots := #[.str `Regula \"../Payload\"]\n"
  mutate claimed "import Support\n" "import Support\nimport Regula.«../Payload»\n"
  failures := failures ++ (← expect adopter {
      label := "path/owned-traversing-name", exitCode := 3,
      contains := #["lake-query-malformed", "segment between path separators",
        "regula lint: INCOMPLETE (exit 3)"] })
  IO.FS.writeFile claimed claimedSource
  restore
  -- A claimed module that imports `Widget.«<adopter directory>/Payload»`, with an axiom that
  -- nothing uses. No configuration or file walk gives the name, but Lake builds it under the
  -- `Widget` library's glob, with its source and artifact at `<adopter directory>/Payload`, outside
  -- every output directory. Every audit refuses the loaded module's name
  -- (`Environment.attributeLoaded`).
  IO.FS.writeFile (adopter / "Payload.lean")
    "/-! A payload. -/\n\n/-- An axiom that nothing uses. -/\naxiom Payload.bad : False\n"
  mutate claimed "import Support\n" s!"import Support\nimport Widget.«{(adopter / "Payload").toString}»\n"
  failures := failures ++ (← expect adopter {
      label := "path/imported-escaping-name", exitCode := 3,
      contains := #["module-name-unsafe", "is an absolute path",
        "regula lint: INCOMPLETE (exit 3)"] })
  IO.FS.writeFile claimed claimedSource
  -- The payloads' sources, and any compiled part a build left beside them.
  for directory in #[support, adopter] do
    for entry in ← directory.readDir do
      if entry.fileName.startsWith "Payload." then Regula.Filesystem.removePath .file entry.path
  -- The owned dependency's library selects its modules with `.submodules` of the anonymous name,
  -- the modules of its source directory `src`, and has no root: the glob names no module, so the
  -- audit's admission does not refuse it. Lake itself then takes every module name for the
  -- library's own, `Init` included, so its build of the claimed library fails, and `lake lint`
  -- cannot build its driver; the checker built in this repository shows the admission alone.
  let supportFile := support / "Support.lean"
  let supportText ← IO.FS.readFile supportFile
  IO.FS.createDirAll (support / "src")
  IO.FS.writeFile (support / "src" / "Support.lean") supportText
  Regula.Filesystem.removePath .file supportFile
  asLean "import Lake\nopen Lake DSL\n\npackage build_lint_support\n\nlean_lib Support where\n  \
    srcDir := \"src\"\n  roots := #[]\n  globs := #[.submodules .anonymous]\n"
  failures := failures ++ (← assess {
      label := "path/owned-anonymous-submodules", exitCode := 3,
      contains := #["RG2003", "build-failed"],
      excludes := #["lake-query-malformed", "names module"] }
    (← runProcess adopter (repo / ".lake" / "build" / "bin" / "axiomGate").toString
      #["--incremental", "--project", adopter.toString] scrubbedLeanPathEnv))
  return failures

/-- The seventh part of the path-dependency controls (`pathSetup`, `pathOwned`): overrides of the
dependency. -/
private def pathOverrides (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let mut failures : Array String := #[]
  -- The manifest names a copy elsewhere, and an override selects the one in the work tree.
  let external := adopter / "external"
  IO.FS.createDirAll external
  for name in #["Support.lean", "lakefile.toml", "lean-toolchain"] do
    IO.FS.writeFile (external / name) (← IO.FS.readFile (support / name))
  let initialized ← runProcess external "git" #["init", "-q"]
  unless initialized.succeeded do
    return failures.push s!"lake-lint/path: git init failed: {initialized.output}"
  let manifestPath := adopter / "lake-manifest.json"
  let manifest ← readJson manifestPath
  let entries ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
  let some entry := entries.find? isSupportEntry
    | return failures.push "lake-lint/path: the manifest has no build_lint_support entry"
  writeJson manifestPath <| manifest.setObjVal! "packages" <| toJson <| entries.map fun item =>
    if JsonAgreement.conforms item entry then item.setObjVal! "dir" (toJson external.toString)
    else item
  let override ← IO.ofExcept <| _root_.Lake.PackageEntry.fromJson?
    (entry.setObjVal! "dir" (toJson "support"))
  _root_.Lake.Manifest.saveEntries (adopter / ".lake" / "package-overrides.json") #[override]
  failures := failures ++ (← expect adopter (ownedAccepted "path/owned-override"))
  failures := failures ++
    (← expect adopter (ownedAccepted "path/owned-override-fresh" (fresh := true))
      #["--", "--fresh"])
  -- Of two override entries of the dependency, Lake keeps the last, the honest repository
  -- elsewhere; the fresh copy loads that one too, not the first, whose correspondence is forged.
  let first := adopter / "external-first"
  IO.FS.createDirAll first
  for name in #["lakefile.toml", "lean-toolchain"] do
    IO.FS.writeFile (first / name) (← IO.FS.readFile (external / name))
  IO.FS.writeFile (first / "Support.lean") (supportSource true)
  let initializedFirst ← runProcess first "git" #["init", "-q"]
  unless initializedFirst.succeeded do
    return failures.push s!"lake-lint/path: git init failed: {initializedFirst.output}"
  let overrides ← [first, external].mapM fun dir => IO.ofExcept <|
    _root_.Lake.PackageEntry.fromJson? (entry.setObjVal! "dir" (toJson dir.toString))
  _root_.Lake.Manifest.saveEntries (adopter / ".lake" / "package-overrides.json")
    overrides.toArray
  let lastFresh := accepted "path/override-last-fresh" (fresh := true)
  failures := failures ++ (← expect adopter { lastFresh with
    contains := lastFresh.contains ++
      #["trusted dependencies, not wholly replayed through Lean's kernel:",
        "build_lint_support"] }
    #["--", "--fresh"])
  return failures

/-- The eighth part of the path-dependency controls (`pathSetup`, `pathOwned`): the dependency as a
Git work tree of its own. -/
private def pathTrusted (repo adopter : FilePath) : IO (Array String) := do
  pathSetup repo adopter
  let support := adopter / "support"
  let mut failures : Array String := #[]
  -- A repository of its own makes the dependency a Git work tree other than the adopter's.
  let initialized ← runProcess support "git" #["init", "-q"]
  unless initialized.succeeded do
    return failures.push s!"lake-lint/path: git init failed: {initialized.output}"
  IO.FS.writeFile (support / "Support.lean") (supportSource true)
  failures := failures ++ (← expect adopter {
      label := "path/trusted-forged", exitCode := 1,
      contains := #["RG3002", "Support.reference", "regula lint: VIOLATION (exit 1)"],
      excludes := #["kernel-admission"] })
  IO.FS.writeFile (support / "Support.lean") (supportSource false)
  let trustedPositive := accepted "path/trusted"
  failures := failures ++ (← expect adopter { trustedPositive with
    contains := trustedPositive.contains ++
      #["trusted dependencies, not wholly replayed through Lean's kernel:",
        "build_lint_support"] })
  return failures

/-- The `lakefile.lean` adopter in the checker's own Git work tree, so `regula` is an owned
dependency, with a claimed import of `Regula.Linter`, as the adoption guide recommends. Its closure
holds modules of `regula` under the checker's reserved prefixes, such as `RegulaPolicy.Identity`,
whose decision contract lies in `RegulaPolicy.Claim`, which no claimed module imports, and modules
outside them, such as `RegulaCore.EditorPolicy`. A module under those prefixes is the checker's own
code, which no environment owns (`Environment.projectModules`); the audit owns and replays the
others, and replays each reserved module that imports one of them, such as `Regula.Linter.Rules`
(`Admission.replaySet`). A `lake lint -- --fresh` must accept the adopter: when the audit owned the
reserved modules, it reported RG1008 for `admitIdentity`, and before that, the admission refused
`RegulaPolicy.Codec`, which the reporter loads under `--fresh`, as an unreplayed module that
imports a replayed one. Its account must name `regula` alone as a trusted dependency, as it names a
`regula` outside the work tree, since `regula` provides modules under those prefixes
(`RegulaPolicy.DependencyState.reserved`). That line does not tell an owned `regula` from a trusted
one, so the same run's result document must record `regula` in `snapshot.dependencies` with
`owned: true` and `RegulaCore.EditorPolicy` among the `dependencyModules` of an environment. -/
private def ownedChecker (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  Regula.Filesystem.removePath .directory (adopter / ".git")
  mutate (adopter / "Widget.lean") "import Regula.Contract\n"
    "import Regula.Contract\nimport Regula.Linter\n"
  let label := "owned-checker/fresh"
  let positive := accepted label (fresh := true)
  let onlyRegula := "trusted dependencies, not wholly replayed through Lean's kernel: regula\n"
  let resultFile := adopter / "owned-checker.json"
  let mut failures ← expect adopter
    { positive with contains := positive.contains.push onlyRegula }
    #["--", "--fresh", "--json-out", "owned-checker.json"]
  unless failures.isEmpty do return failures
  let acceptance := (← readJson resultFile).getObjValD "acceptance"
  Regula.Filesystem.removePath .file resultFile
  let entries (value : Json) : Array Json := value.getArr?.toOption.getD #[]
  let dependencies := entries ((acceptance.getObjValD "snapshot").getObjValD "dependencies")
  unless dependencies.any (fun dependency =>
      JsonAgreement.conforms (dependency.getObjValD "package") (toJson "regula") &&
      JsonAgreement.conforms (dependency.getObjValD "owned") (toJson true)) do
    failures := failures.push s!"lake-lint/{label}: snapshot.dependencies has no owned regula: \
      {(Json.arr dependencies).compress}"
  let inspected := Regula.RegistryCodec.printedNameJson `RegulaCore.EditorPolicy
  let environments := entries (acceptance.getObjValD "environments")
  let dependencyModules := environments.map (·.getObjValD "dependencyModules")
  unless dependencyModules.any (fun modules =>
      (entries modules).any (JsonAgreement.conforms · inspected)) do
    failures := failures.push s!"lake-lint/{label}: no environment's dependencyModules holds \
      {inspected.compress}: {(Json.arr dependencyModules).compress}"
  return failures

/-- With the checker's `axiomGate` worker binary removed, `lake lint` builds it and still
reaches the accepted result: Lake's lint dispatch itself builds only the driver. -/
private def absentWorker (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter "lake-lint-toml" #["Gadget.lean", "Gadget/Double.lean"]
    "lakefile.toml"
  Regula.Filesystem.removePath .file (repo / ".lake" / "build" / "bin" / "axiomGate")
  expect adopter (accepted "toml/absent-worker")

/-- The first commands of an adopter on Lake's own templates, external boundaries all: the
template of this toolchain's `lake new`, the lakefile edits of `regula init`, and `lake lint`.
In each format (`lakefile.toml`, and `lakefile.lean` with `.lean`, whose `lean_lib` has an empty
`where` block), a project from `lake new` that requires this checkout (`requireCheckout`) gets
from `lake exe regula init` the glob that includes the module its umbrella imports, then
`doctor` reports the setup complete, and a second `init` writes nothing. In the `lakefile.toml`
project, `lake lint` then reports only the docstrings the template lacks ([RG2003]); with them
written it accepts the project. That the plan of the result is empty in the model is
`Regula.Setup.plan_idempotent`; these runs observe that the written files realize it. -/
private def lakeNew (repo scratch : FilePath) : IO (Array String) := do
  let regula (project : FilePath) : IO ProcessResult :=
    runProcess project "lake" #["exe", "regula", "init"] scrubbedLeanPathEnv
  -- `lake new`, the `regula` requirement, then `init` twice: the first must report writing
  -- `setting`, after which the lakefile must contain `written`.
  let setUp (name format lakefile require setting written : String) : IO (Array String) := do
    let made ← runProcess scratch "lake" (#["new", name] ++ (if format.isEmpty then #[] else
      #[format])) scrubbedLeanPathEnv
    if !made.succeeded then return #[s!"lake-lint/new/{name}: lake new failed", made.output]
    let project := scratch / name
    IO.FS.writeFile (project / lakefile) ((← IO.FS.readFile (project / lakefile)) ++ require)
    BuildLintQualification.requireCheckout repo project
    let mut failures ← assess {
        label := s!"new/{name}/init", exitCode := 0,
        contains := #["regula init: wrote ", setting, "regula doctor: the setup is complete"] }
      (← regula project)
    unless (← IO.FS.readFile (project / lakefile)).contains written do
      failures := failures.push s!"lake-lint/new/{name}: {lakefile} lacks {written}"
    return failures ++ (← assess {
        label := s!"new/{name}/init-again", exitCode := 0,
        contains := #["regula init: nothing to write", "regula doctor: the setup is complete"] }
      (← regula project))
  let path := Json.compress (toJson repo.toString)
  let mut failures ← setUp "demo" "" "lakefile.toml"
    s!"\n[[require]]\nname = \"regula\"\npath = {path}\n" "globs = [\"Demo\", \"Demo.+\"]"
    "globs = [\"Demo\", \"Demo.+\"]"
  if !failures.isEmpty then return failures
  let demo := scratch / "demo"
  failures := failures ++ (← expect demo {
      label := "new/demo/lint", exitCode := 3,
      contains := #["RG2003", "hello", "main"], excludes := #["RG2002", "RG2004"] })
  IO.FS.writeFile (demo / "Demo.lean") "import Demo.Basic\n/-! The `Demo` library. -/\n"
  IO.FS.writeFile (demo / "Demo" / "Basic.lean")
    "/-! A greeting. -/\n/-- The subject of the greeting. -/\ndef hello := \"world\"\n"
  IO.FS.writeFile (demo / "Main.lean") <| "import Demo\n/-! The `demo` executable. -/\n" ++
    "/-- Print the greeting. -/\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n"
  failures := failures ++ (← expect demo (accepted "new/demo/documented"))
  return failures ++ (← setUp "legacy" ".lean" "lakefile.lean"
    s!"\nrequire regula from {path}\n" "globs := #[.andSubmodules `Legacy]"
    "lean_lib «Legacy» where\n  globs := #[.andSubmodules `Legacy]")

/-- The cold compiler guard of Regula's own `lakefile.lean`, through `lake` in a fresh package
holding only that file, its toolchain pin and the policy source it executes. An inherited
`LEAN_SYSROOT` whose `lean` is not the compiler running Lake is refused on each branch of the
guard, naming that `lean`, and the same package then loads with the inherited environment. Two
programs stand in for that `lean`, neither of them a compiler: this toolchain's `lake`, which
fails on the policy source, and the `true` utility, which exits successfully without printing
the running compiler's identity and so reaches the identity comparison. A compiler of another
identity as the child is not exercised here. -/
private def compilerGuard (repo project : FilePath) : IO (Array String) := do
  for name in #["lakefile.lean", "lean-toolchain", "lean/RegulaPolicy/Compiler.lean"] do
    if let some parent := (project / name).parent then IO.FS.createDirAll parent
    IO.FS.writeFile (project / name) (← IO.FS.readFile (repo / name))
  let path := System.SearchPath.parse ((← IO.getEnv "PATH").getD "")
  let some silent ← path.findM? fun dir => (dir / "true").pathExists
    | throw <| IO.userError "lake-lint: the compiler-guard control found no `true` on PATH"
  let load (env : Array (String × Option String)) : IO ProcessResult :=
    runProcess project "lake" #["check-lint"] (scrubbedLeanPathEnv ++ env)
  let refused (label : String) (program : FilePath) (branch : String) : IO (Array String) := do
    let sysroot := project / label
    let lean := sysroot / "bin" / "lean"
    IO.FS.createDirAll (sysroot / "bin")
    let linked ← runProcess project "ln" #["-s", program.toString, lean.toString]
    if !linked.succeeded then throw <| IO.userError linked.output
    assess { label := s!"guard/{label}", exitCode := 1, contains := #[lean.toString, branch] }
      (← load #[("LEAN_SYSROOT", some sysroot.toString)])
  let failing ← refused "failing-child" ((← Lean.findSysroot) / "bin" / "lake")
    "refused Regula's compiler policy or could not compile it"
  let unidentified ← refused "unidentified-child" (silent / "true") "is not the Lean running Lake"
  return failing ++ unidentified ++
    (← assess { label := "guard/restored", exitCode := 0 } (← load #[]))

/-- Run the control group `name` in its own disposable workspace, printing when it starts and how
long it took (`loggedPhase`), so that the job log shows the schedule. -/
private def runGroup (repo scratch : FilePath) (name : String)
    (control : FilePath → FilePath → IO (Array String)) : IO (Array String) :=
  loggedPhase s!"lake lint {name}" <|
    withScratch scratch s!"lake-lint-{name}" fun adopter => control repo adopter

/-- The number of shards of the controls: `checkerSelftest --partition lint-driver --shard i/5`
runs the controls of the `i`th (`qualify`), and the diagnostics workflow runs each shard as a job
of its own, under the deadline of its own invocation. -/
def shards : Nat := SelftestArguments.Partition.lintDriver.shards

/-- The shard numbered `index` from 0, which `--shard` numbers from 1. -/
private def numbered (index : Nat) (bound : index < shards := by decide) : Fin shards :=
  ⟨index, bound⟩

/-- Every control runs in exactly one shard: the selections of the five shards of a list of
controls, in their order, are together a rearrangement of the list, which an unsharded run executes
(`inShard_cover`). This is a statement about the selection; that the shards select from the same
list rests on their running the same sources, which it does not state. -/
theorem shards_cover {α : Type} (items : List (Fin shards × α)) :
    ((List.finRange shards).flatMap fun selected => inShard (some selected) items).Perm
      (inShard none items) :=
  inShard_cover _ (List.nodup_finRange shards) List.mem_finRange items

/-- One control group: its shard, its name in the job log, and the controls it runs in a workspace
of its own. -/
private abbrev Group := Fin shards × String × (FilePath → FilePath → IO (Array String))

/-- The groups of controls each run alone, one after another, before the other groups start: the
absent-worker control, since the adopters share the checker's binaries, and it removes one of
them. -/
private def aloneGroups : List Group :=
  [(numbered 0, "worker", absentWorker)]

/-- The other groups, which run on the workers of `mapWorkQueue`, each with the shard it is in.
They are listed longest first, so the shorter ones fill the workers that the longer ones free; in
a shard, its groups keep that order. Each shard's groups add up to a similar time, and its longest
group is a part of a chain: the chains of the two adopters, of the path dependency and of the
weak-arguments controls are cut into parts (`leanOriginals`, `tomlSetup`, `pathSetup`,
`WeakArgsAdopter`), so that no group is longer than about a quarter of a shard's time, apart from
the owned-checker control, one `lake lint -- --fresh`, which shares its shard only with the short
compiler-guard control `guard`. The order and the shards follow the times of the groups in the
slowest CI run of the campaign before the cut (`docs/guides/proofs-and-boundaries.md` names the
run). No CI run timed the weak-arguments groups: the chain they were cut from took about 163 s
locally, and each is placed by its share of the chain's Lake invocations, the two longest
(`weakArgsOverrides`, `weakArgsModes`) first, each of the four in a shard of its own other than
the owned-checker control's. -/
private def queuedGroups (probes : Std.Mutex Unit) : List Group :=
  [(numbered 2, "weak-args-overrides", weakArgsOverrides),
    (numbered 4, "weak-args-modes", weakArgsModes),
    (numbered 1, "owned-checker", ownedChecker),
    (numbered 2, "path-overrides", pathOverrides),
    (numbered 3, "lean-decisions", leanDecisions probes),
    (numbered 3, "lean-arguments", leanArguments probes),
    (numbered 4, "path-owned", pathOwned),
    (numbered 0, "lean-audit", leanAudit),
    (numbered 3, "weak-args-declared", weakArgsDeclared),
    (numbered 0, "weak-args-probes", weakArgsProbes probes),
    (numbered 0, "path-owned-checks", pathOwnedChecks),
    (numbered 4, "path-config", pathConfig),
    (numbered 3, "lake-new", lakeNew),
    (numbered 2, "path-forged", pathForged),
    (numbered 0, "path-trusted", pathTrusted),
    (numbered 3, "toml-audit", tomlAudit),
    (numbered 4, "toml-live", tomlLive),
    (numbered 2, "lean-refusals", leanRefusals),
    (numbered 0, "lean-violation", leanViolation),
    (numbered 4, "toml-targets", tomlTargets),
    (numbered 2, "cache", cachedWarning),
    (numbered 3, "toml-plain", tomlPlain probes),
    (numbered 4, "path-escapes", pathEscapes),
    (numbered 2, "empty-facets", emptyFacetsWarning),
    (numbered 0, "path-reserved", pathReserved),
    (numbered 3, "dependency-cache", dependencyCachedWarning),
    (numbered 3, "escaped-name", escapedNameWarning),
    (numbered 1, "guard", compilerGuard)]

/-- Run the control groups of `shard`, or every group without one (`inShard`, `shards_cover`): the
groups of `aloneGroups` first, one after another, and stop at the first that fails; then the other
groups on `jobs` workers, each of which takes the next waiting group as soon as it is free
(`mapWorkQueue`), so no worker idles while a group waits and no batch boundary holds a group back.
`mapWorkQueue` returns one result for each group, in this order (`checked_indexedResults`). The
adopters' decision probes load their workspaces one at a time (`probe`). Returns the names of the
groups run and the failures. -/
def qualify (repo scratch : FilePath) (jobs : Nat) (shard : Option (Fin shards) := none) :
    IO (Array String × Array String) := do
  let probes ← Std.Mutex.new ()
  let alone := (inShard shard aloneGroups).map (·.2)
  let queued := (inShard shard (queuedGroups probes)).map (·.2)
  let names := (alone ++ queued).map (·.1) |>.toArray
  for (name, control) in alone do
    let failures ← runGroup repo scratch name control
    if !failures.isEmpty then return (names, failures)
  let results ← mapWorkQueue jobs queued.toArray
    fun (name, control) => runGroup repo scratch name control
  return (names, results.foldl (· ++ ·) #[])

end Regula.Checker.LintQualification
