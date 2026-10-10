import Regula.Checker.BuildLintQualification
import Regula.Checker.LintBuild

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
does, and check the decision of its claimed build under the owner's `--ordinary-lakefiles` without
running an audit. They are diagnostics, not proofs of the driver or of Lake.
-/

namespace Regula.Checker.LintQualification

open Lean System

private def acceptanceLabel := "PASS"

private def lint (cwd : FilePath) (args : Array String := #[]) : IO ProcessResult :=
  runProcess cwd "lake" (#["lint"] ++ args) scrubbedLeanPathEnv

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

private def expect (cwd : FilePath) (e : Expectation) (args : Array String := #[]) :
    IO (Array String) := do
  assess e (← lint cwd args)

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
    IO.FS.removeDirAll (adopter / ".lake" / "build")

/-- A decision probe: after an ordinary `lake build` of `targets`, which leaves the compiled
lakefile under `.lake/config`, the workspace at `adopter` is loaded in-process as the driver loads
it, and the decision of the driver's claimed build under the owner's `--ordinary-lakefiles`
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

/-- The driver arguments of the workspace owner's assertion that the lakefiles are ordinary
configuration. -/
private def optIn : Array String := #["--", "--ordinary-lakefiles"]

/-- The line of the driver's claimed build under the owner's `--ordinary-lakefiles` that omits the
audit-build marker, and the start of the line that keeps it (`Lake.buildAuditTargets`). -/
private def markerOmitted := "the claimed build omits the audit-build marker"
private def markerKept := "the claimed build keeps the audit-build marker: "

/-- `lakefile.lean` adopter: every exit class with its summary counts, a repeated cached failure,
a claimed import outside every library (RG2004) in the driver and the file audit, a failed audit
worker reported with its own error, Lake's builtin-only and combined dispatch, and the read-only
configuration explanation. Default output shows Lake's build progress and no timing span; the
file audit lists every classified declaration only with `--verbose`. Without the custom `policy`
target the workspace has the plain shape: without the owner's `--ordinary-lakefiles` the driver
keeps the audit-build marker and prints no decision, so an ordinary build after it rebuilds; with
it the driver prints that it omits the marker, and an ordinary `lake build` and the driver reuse
each other's build output. The banner names the option and the result records it as
`scope.ordinaryLakefiles`; a `lintDriverArgs` entry that gives it is refused. Decision probes of
the guard (`probe`), each with one change to the plain shape and the reason that decides: an
`input_file` in `needs` keeps the plain shape, and each of these keeps the marker: a custom target,
a library in `needs`, Lake's `ilean` facet declared again with Lake's own configuration, a
library field outside the plain shape's list (`libName`), a `nativeFacets` that is not Lake's
whole default term, a lakefile declaration beside Lake's configuration declarations, and a theorem
that equates two functions. -/
private def leanAdopter (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  BuildLintQualification.setup repo adopter
  -- The first run builds every module, showing Lake's progress line for each.
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
  let additional := adopter / "Widget" / "Additional.lean"
  let manifest := adopter / "foundation_manifest.json"
  let widget := adopter / "Widget.lean"
  let lakefile := adopter / "lakefile.lean"
  let originals := #[(additional, ← IO.FS.readFile additional),
    (manifest, ← IO.FS.readFile manifest), (widget, ← IO.FS.readFile widget),
    (lakefile, ← IO.FS.readFile lakefile)]
  -- The plain shape: without the `policy` target the workspace declares only `lean_lib` and
  -- `lean_exe` targets and Regula's input targets, and no module of the package imports
  -- `Regula.Linter`.
  let plain ← match (← IO.FS.readFile lakefile).splitOn "\n/-- The sole default target" with
    | [declarations, _] => pure declarations
    | _ => throw <| IO.userError "lake-lint: expected one policy target in the adopter's lakefile"
  let widgetLibrary (field : String) : String :=
    plain.replace "globs := #[.andSubmodules `Widget]"
      s!"globs := #[.andSubmodules `Widget]\n  {field}"
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
  IO.FS.removeFile tooling
  -- Without the owner's `--ordinary-lakefiles` the driver keeps the marker, as before the plain
  -- shape existed, and prints no decision, so an ordinary build after it rebuilds. With it the
  -- driver builds without the marker and says so, and an ordinary build and the driver reuse each
  -- other's output.
  IO.FS.writeFile lakefile plain
  failures := failures ++ (← expect adopter { positive with
    label := "lean/plain-default-marked", excludes := positive.excludes.push "the claimed build" })
  let ordinary ← runProcess adopter "lake" #["build", "Widget"] scrubbedLeanPathEnv
  unless ordinary.succeeded && ordinary.output.contains "] Built Widget" do
    failures := failures.push s!"lake-lint/lean/plain-default-marked: the ordinary build reused \
      the driver's build: {ordinary.output}"
  failures := failures ++ (← expect adopter { positive with
    label := "lean/plain-reused", contains := positive.contains.push markerOmitted } optIn)
  let ordinary ← runProcess adopter "lake" #["build", "Widget"] scrubbedLeanPathEnv
  unless ordinary.succeeded && !ordinary.output.contains "] Built Widget" do
    failures := failures.push s!"lake-lint/lean/plain-reused: the ordinary build rebuilt a module: \
      {ordinary.output}"
  failures := failures ++ (← expect adopter { positive with
    label := "lean/plain-reused-again", excludes := positive.excludes.push "] Built" } optIn)
  -- The banner names the owner's assertion, and the result records it as
  -- `scope.ordinaryLakefiles`.
  failures := failures ++ (← expect adopter { positive with
      label := "lean/opt-in-reported"
      contains := positive.contains.push "the workspace owner asserts ordinary lakefiles" }
    (optIn ++ #["--json-out", "opt-in.json"]))
  let recorded := ((← readJson (adopter / "opt-in.json")).getObjValD "scope").getObjValD
    "ordinaryLakefiles"
  unless recorded == toJson true do
    failures := failures.push s!"lake-lint/lean/opt-in-reported: scope.ordinaryLakefiles is \
      {recorded.compress}"
  IO.FS.removeFile (adopter / "opt-in.json")
  -- A package's `lintDriverArgs` cannot give the owner's assertion: the driver refuses it.
  IO.FS.writeFile lakefile (plain.replace "lintDriver := \"regula/lint\""
    "lintDriver := \"regula/lint\"\n  lintDriverArgs := #[\"--ordinary-lakefiles\"]")
  failures := failures ++ (← expect adopter {
      label := "lean/opt-in-configured-refused", exitCode := 2,
      contains := #["lintDriverArgs cannot give it", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] })
  -- An `input_file` in `needs` keeps the plain shape.
  let notes := adopter / "notes.txt"
  IO.FS.writeFile notes "Widget notes.\n"
  IO.FS.writeFile lakefile <| widgetLibrary "needs := #[`@/widgetNotes]\n\ninput_file widgetNotes \
    where\n  path := \"notes.txt\""
  failures := failures ++ (← probe probes adopter "lean/input-needs-plain" #["Widget"] none)
  IO.FS.removeFile notes
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
  restore adopter originals
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
  restore adopter originals
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
  unless stages == toJson #["configuration", "discovery", "build"] do
    failures := failures.push s!"lake-lint/lean/worker-failure: stagesCompleted {stages.compress}"
  for file in entryPoints do IO.FS.removeFile file
  restore adopter originals
  failures := failures ++ (← expect adopter (accepted "lean/fresh-restored"))
  return failures

/-- `lakefile.toml` adopter importing `Regula.Linter`: disabling live feedback cannot waive
the project predicate, and a live finding, also re-enabled by the source or replayed from an
ordinary `lake build` with live feedback, is the audit's violation rather than a failed build.
A claimed `lean_lib` and a claimed `lean_exe` whose Lake target names are not Lean identifiers
are accepted under those names and classified alike under the names as Lean prints them; naming
one target under both is a configuration refusal, and so is a library or executable entry,
claimed or excluded, that names no root target of its kind: one refusal that quotes the entry as
the manifest writes it and lists the root targets of that kind by Lake target name, in the driver
and, for an executable entry, in the adopter's `axiomGate --file` audit, which reads the manifest
through the same loader. Under the owner's `--ordinary-lakefiles` the driver keeps the audit-build
marker for the live finding, whose module imports `Regula.Linter`, and prints why. Without that
import, an `input_dir` filter `"*"` keeps the plain shape: the driver prints that it omits the
marker, and an ordinary build reuses its output. Decision probes of the guard (`probe`), each with
one change to the adopter and the reason that decides: the filter `"*"` keeps the plain shape, and
a filter by extension and the `Regula.Linter` import each keep the marker. -/
private def tomlAdopter (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  BuildLintQualification.setup repo adopter "lake-lint-toml" #["Gadget.lean", "Gadget/Double.lean"]
    "lakefile.toml"
  let mut failures ← expect adopter (accepted "toml/positive")
  if !failures.isEmpty then return failures
  let double := adopter / "Gadget" / "Double.lean"
  let originals := #[(double, ← IO.FS.readFile double)]
  -- Dispatched for the adopter from another project root, which the audit would accept.
  failures := failures ++ (← expect repo {
      label := "toml/foreign-dir", exitCode := 2,
      contains := #["without -d/--dir", "regula lint: INVALID CONFIGURATION"],
      excludes := #[s!"regula lint: {acceptanceLabel}"] } #["-d", adopter.toString])
  mutate double "end Gadget" <|
    "set_option linter.regula false in\n/-- A control assumption. -/\n" ++
      "axiom optedOut : True\nend Gadget"
  failures := failures ++ (← expect adopter {
      label := "toml/editor-opt-out", exitCode := 1,
      contains := #["RG1001", "optedOut", "regula lint: VIOLATION (exit 1)"] })
  restore adopter originals
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
  -- `Gadget.Double` imports `Regula.Linter`, so even under the owner's `--ordinary-lakefiles` the
  -- driver builds with the audit-build marker (`Lake.auditMarkerNeeded`), says why, and rebuilds
  -- the module that the ordinary build made.
  failures := failures ++ (← expect adopter {
      label := "toml/live-finding", exitCode := 1,
      contains := #["RG1001", "liveFinding", "regula lint: VIOLATION (exit 1)",
        "] Built Gadget.Double", markerKept, "imports Regula.Linter"],
      excludes := #["build-failed", "editorSnapshot"] } optIn)
  restore adopter originals
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
  let targetOriginals := #[(lakefile, ← IO.FS.readFile lakefile),
    (manifest, ← IO.FS.readFile manifest)]
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
  IO.FS.removeFile cli
  IO.FS.removeFile extra
  restore adopter targetOriginals
  -- Without the `Regula.Linter` import the workspace can have the plain shape. A `lakefile.toml`
  -- `input_dir` filter is Lake's default only when it is omitted or `"*"`: then the driver omits
  -- the marker under the owner's `--ordinary-lakefiles`, and an ordinary build reuses its output.
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
      contains := (accepted "toml/star-reused").contains.push markerOmitted } optIn)
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
  IO.FS.removeDirAll inputs
  restore adopter (originals ++ targetOriginals)
  failures := failures ++
      (← expect adopter (accepted "toml/fresh-restored" (fresh := true)) #["--", "--fresh"])
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
  IO.FS.removeDirAll (adopter / ".lake" / "build")
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
    IO.FS.removeDirAll (dependency / ".lake" / "build")
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
  IO.FS.removeDirAll (adopter / ".lake" / "build")
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

/-- A path dependency of an adopter that is a repository of its own
(`BuildLintQualification.setup`, `BuildLintQualification.addSupport`), which a claimed module
imports, under the claimed checked execution of `examples/build-lint`. In the adopter's Git work
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
counted. A module name that two packages provide, an executable root `Main` of the root package and
of the dependency, or `Support` of the dependency and of a second owned one, is refused before the
driver builds its audit worker. So is a library root `Regula.«<directory>/Payload»` that a claimed
module imports, whose absolute component would put its source and artifact outside the
dependency's directories, and so is the root `Regula.«../Payload»`, whose `..` segment would leave
them. A claimed module's import of `Widget.«<adopter directory>/Payload»`, which Lake builds under
the claimed library's glob outside every output directory, is refused once the module is loaded.
An override in `.lake/package-overrides.json` that selects the dependency in place of one
elsewhere is owned in the fresh copy too, and of two override entries the fresh copy loads the
last, as Lake does. As a Git work tree of its own it is trusted: the forged theorem
supplies no correspondence, so the boundary it was to prove is rejected (RG3002), and with an
honest module the account names it. These observe Git's work-tree discovery, Lake's path
dependencies and overrides and the fresh copy, which the ownership theorems (`sameWorkTree_iff`,
`contains_ownedModuleSet`) take as given. -/
private def pathDependency (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  BuildLintQualification.addSupport adopter (supportSource false) (owned := true)
  let support := adopter / "support"
  mutate (adopter / "Widget.lean") "import Regula.Contract\n"
    "import Regula.Contract\nimport Support\n"
  mutate (adopter / "Widget.lean") "end Widget"
    "/-- Runs the dependency's caller. -/\ndef useCaller (n : Nat) : Nat := Support.caller n\n\
      \nend Widget"
  let onlyRegula := "trusted dependencies, not replayed through Lean's kernel: regula\n"
  let owned (label : String) (fresh : Bool := false) : Expectation :=
    let positive := accepted label fresh
    { positive with contains := positive.contains.push onlyRegula,
                    excludes := positive.excludes.push "build_lint_support" }
  let mut failures ← expect adopter (owned "path/owned")
  if !failures.isEmpty then return failures
  -- The fresh audit builds the owned dependency in its copy: the original's output stays absent.
  IO.FS.removeDirAll (support / ".lake" / "build")
  failures := failures ++
    (← expect adopter (owned "path/owned-fresh" (fresh := true)) #["--", "--fresh"])
  if ← (support / ".lake" / "build").pathExists then
    failures := failures.push "lake-lint/path/owned-fresh: the fresh audit wrote the original \
      dependency's build output"
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
  failures := failures ++ (← expect adopter (owned "path/owned-standard-logical"))
  IO.FS.writeFile (support / "Support.lean") (supportSource true)
  let refused (label : String) : Expectation := {
    label, exitCode := 3,
    contains := #["RG2005", "kernel-admission", "regula lint: INCOMPLETE (exit 3)"] }
  failures := failures ++ (← expect adopter (refused "path/owned-forged"))
  failures := failures ++
    (← expect adopter (refused "path/owned-forged-fresh") #["--", "--fresh"])
  IO.FS.writeFile (support / "Support.lean") (supportSource false)
  -- Every audit refuses, before any build, an owned package that sets an output directory other
  -- than Lake's default: a build directory or a library directory in the original checkout, under
  -- `--fresh` and in an incremental audit. The fresh audit leaves the original's build output
  -- absent.
  let supportLakefile := support / "lakefile.toml"
  let supportConfiguration ← IO.FS.readFile supportLakefile
  -- The driver's own line when it refuses to build its audit worker for a workspace outside the
  -- supported scope (`Lint.lint`).
  let unbuiltWorker :=
    "regula lint: the workspace is outside the supported scope, so the audit worker is not built"
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
    IO.FS.removeDirAll (support / ".lake" / "build")
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
  IO.FS.writeFile rootLakefile rootConfiguration
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
  let some configEntry := configEntries.find? (·.getObjValD "name" == toJson "build_lint_support")
    | return failures.push "lake-lint/path: the manifest has no build_lint_support entry"
  let relative := configEntry.setObjVal! "dir" (toJson "support")
  writeJson configManifestPath <| configManifest.setObjVal! "packages" <| toJson <|
    configEntries.map fun item => if item == configEntry then relative else item
  let alternative ← IO.ofExcept <| _root_.Lake.PackageEntry.fromJson?
    (relative.setObjVal! "configFile" (toJson "alt.toml"))
  _root_.Lake.Manifest.saveEntries (adopter / ".lake" / "package-overrides.json") #[alternative]
  let configured (label : String) : Expectation := {
    label, exitCode := 1,
    contains := #["RG1001", "Support.unused", "regula lint: VIOLATION (exit 1)"] }
  failures := failures ++ (← expect adopter (configured "path/owned-config"))
  failures := failures ++
    (← expect adopter (configured "path/owned-config-fresh") #["--", "--fresh"])
  IO.FS.removeFile (adopter / ".lake" / "package-overrides.json")
  writeJson configManifestPath configManifest
  IO.FS.removeFile (support / "alt.toml")
  IO.FS.removeDirAll (support / "actual")
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
  IO.FS.removeDirAll (support / "Regula")
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
      if item.getObjValD "name" == toJson "regula" then
        (item.setObjVal! "dir" (toJson "vendor")).setObjVal! "configFile" (toJson "lakefile.toml")
      else item
  IO.FS.writeFile adopterLakefile <|
    adopterConfiguration.replace regulaRequire "require regula from \"vendor\""
  failures := failures ++ (← gate "path/vendored-regula-name")
  IO.FS.writeFile adopterLakefile adopterConfiguration
  writeJson vendorManifestPath vendorManifest
  IO.FS.removeDirAll vendor
  -- An executable of the root package with root module `Main`, which the executable `auditApp` of
  -- the trusted `regula` also has: a trusted package's executable roots are not counted, so the
  -- incremental audit accepts it. An unused executable of the owned dependency with root module
  -- `Main` of its own package is a second provider, which every audit refuses before any build,
  -- whichever environment would load either.
  let ambiguous (label name : String) : Expectation := {
    label, exitCode := 3,
    contains := #["lake-query-malformed", s!"module {name} is provided by package",
      "package 'build_lint_support'", "one provider for each module name", unbuiltWorker,
      "regula lint: INCOMPLETE (exit 3)"] }
  let manifestFile := adopter / "foundation_manifest.json"
  let adopterManifest ← IO.FS.readFile manifestFile
  let mainSource := "/-! An entry point. -/\n\n/-- Runs nothing. -/\ndef main : IO Unit := pure ()\n"
  IO.FS.writeFile (adopter / "Main.lean") mainSource
  IO.FS.writeFile adopterLakefile <| adopterConfiguration ++
    "\nlean_exe widgetMain where\n  root := `Main\n"
  mutate manifestFile "\"excluded-executables\": []"
    "\"excluded-executables\": [{\"executable\": \"widgetMain\", \"rationale\": \"An entry point \
      outside the claimed surface.\"}]"
  failures := failures ++ (← expect adopter (owned "path/root-executable-main"))
  IO.FS.writeFile (support / "Main.lean") mainSource
  IO.FS.writeFile supportLakefile <| supportConfiguration ++
    "[[lean_exe]]\nname = \"supportUtil\"\nroot = \"Main\"\n"
  failures := failures ++ (← expect adopter (ambiguous "path/owned-executable-names" "Main"))
  IO.FS.writeFile adopterLakefile adopterConfiguration
  IO.FS.writeFile manifestFile adopterManifest
  IO.FS.writeFile supportLakefile supportConfiguration
  IO.FS.removeFile (adopter / "Main.lean")
  IO.FS.removeFile (support / "Main.lean")
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
  let some supportEntry := entries.find? (·.getObjValD "name" == toJson "build_lint_support")
    | return failures.push "lake-lint/path: the manifest has no build_lint_support entry"
  writeJson manifestPath <| projectManifest.setObjVal! "packages" <| toJson <| entries.push <|
    (supportEntry.setObjVal! "name" (toJson "build_lint_support_two")).setObjVal! "dir"
      (toJson second.toString)
  IO.FS.writeFile adopterLakefile <| adopterConfiguration ++
    "\nrequire build_lint_support_two from \"support2\"\n"
  failures := failures ++ (← expect adopter (ambiguous "path/owned-duplicate-provider" "Support"))
  IO.FS.writeFile adopterLakefile adopterConfiguration
  writeJson manifestPath projectManifest
  IO.FS.removeDirAll second
  -- The owned dependency's configuration as a `lakefile.lean`, for the two controls below.
  let asLean (configuration : String) : IO Unit := do
    writeJson manifestPath <| projectManifest.setObjVal! "packages" <| toJson <|
      entries.map fun item =>
        if item.getObjValD "name" == toJson "build_lint_support" then
          item.setObjVal! "configFile" (toJson "lakefile.lean")
        else item
    IO.FS.removeFile supportLakefile
    IO.FS.writeFile (support / "lakefile.lean") configuration
  let restore : IO Unit := do
    IO.FS.removeFile (support / "lakefile.lean")
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
  IO.FS.removeFile (support / "Aux.lean")
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
      contains := #["surface-attribution", "is an absolute path",
        "regula lint: INCOMPLETE (exit 3)"] })
  IO.FS.writeFile claimed claimedSource
  -- The payloads' sources, and any compiled part a build left beside them.
  for directory in #[support, adopter] do
    for entry in ← directory.readDir do
      if entry.fileName.startsWith "Payload." then IO.FS.removeFile entry.path
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
  let some entry := entries.find? (·.getObjValD "name" == toJson "build_lint_support")
    | return failures.push "lake-lint/path: the manifest has no build_lint_support entry"
  writeJson manifestPath <| manifest.setObjVal! "packages" <| toJson <| entries.map fun item =>
    if item == entry then item.setObjVal! "dir" (toJson external.toString) else item
  let override ← IO.ofExcept <| _root_.Lake.PackageEntry.fromJson?
    (entry.setObjVal! "dir" (toJson "support"))
  _root_.Lake.Manifest.saveEntries (adopter / ".lake" / "package-overrides.json") #[override]
  failures := failures ++ (← expect adopter (owned "path/owned-override"))
  failures := failures ++
    (← expect adopter (owned "path/owned-override-fresh" (fresh := true)) #["--", "--fresh"])
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
      #["trusted dependencies, not replayed through Lean's kernel:", "build_lint_support"] }
    #["--", "--fresh"])
  IO.FS.removeFile (adopter / ".lake" / "package-overrides.json")
  writeJson manifestPath manifest
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
      #["trusted dependencies, not replayed through Lean's kernel:", "build_lint_support"] })
  return failures

/-- The `lakefile.lean` adopter in the checker's own Git work tree, so `regula` is an owned
dependency, with a claimed import of `Regula.Linter`, as the adoption guide recommends. Its closure
holds modules of `regula` under the checker's reserved prefixes, such as `RegulaPolicy.Identity`,
whose decision contract lies in `RegulaPolicy.Claim`, which no claimed module imports, and modules
outside them, such as `RegulaCore.EditorPolicy`. A module under those prefixes is the checker's own
code, which no environment owns (`Environment.projectModules`); the audit owns and replays the
others, and replays each reserved module that imports one of them, such as `Regula.Linter.Rules`
(`Admission.replaySet`). A `lake lint -- --fresh` must accept the adopter and name no trusted
dependency: when the audit owned the reserved modules, it reported RG1008 for `admitIdentity`, and
before that, the admission refused `RegulaPolicy.Codec`, which the reporter loads under `--fresh`,
as an unreplayed module that imports a replayed one. -/
private def ownedChecker (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  IO.FS.removeDirAll (adopter / ".git")
  mutate (adopter / "Widget.lean") "import Regula.Contract\n"
    "import Regula.Contract\nimport Regula.Linter\n"
  let positive := accepted "owned-checker/fresh" (fresh := true)
  let noneTrusted := "trusted dependencies, not replayed through Lean's kernel: none\n"
  expect adopter { positive with contains := positive.contains.push noneTrusted }
    #["--", "--fresh"]

/-- With the checker's `axiomGate` worker binary removed, `lake lint` builds it and still
reaches the accepted result: Lake's lint dispatch itself builds only the driver. -/
private def absentWorker (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter "lake-lint-toml" #["Gadget.lean", "Gadget/Double.lean"]
    "lakefile.toml"
  IO.FS.removeFile (repo / ".lake" / "build" / "bin" / "axiomGate")
  expect adopter (accepted "toml/absent-worker")

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

/-- The absent-worker control first, alone, since the adopters share the checker's binaries;
then the path-dependency adopter, both independent adopters, the owned-checker adopter, the
artifact-cache controls, `escapedNameWarning` and the cold compiler guard, each in its own
disposable workspace. `mapConcurrent` joins each batch of `jobs` controls before it starts the
next, so the longest controls come first, and with four jobs share the first batch. The
adopters' decision probes load their workspaces one at a time (`probe`). -/
def qualify (repo scratch : FilePath) (jobs : Nat) : IO (Array String) := do
  let absent ← withScratch scratch "lake-lint-worker" fun adopter => absentWorker repo adopter
  if !absent.isEmpty then return absent
  let probes ← Std.Mutex.new ()
  let results ← mapConcurrent jobs
    #[("path", pathDependency), ("lean", leanAdopter probes), ("toml", tomlAdopter probes),
      ("owned-checker", ownedChecker), ("cache", cachedWarning),
      ("dependency-cache", dependencyCachedWarning), ("empty-facets", emptyFacetsWarning),
      ("escaped-name", escapedNameWarning), ("guard", compilerGuard)]
    fun (name, control) => withScratch scratch s!"lake-lint-{name}" fun adopter =>
                            control repo adopter
  return results.foldl (· ++ ·) #[]

end Regula.Checker.LintQualification
