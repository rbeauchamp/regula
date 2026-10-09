import Regula.Checker.BuildLintQualification
import Regula.Checker.Lake

/-!
# Lake lint driver qualification

Qualification of the `lake lint` driver path. Each control copies a shipped adopter
(`examples/build-lint` in `lakefile.lean` format, `examples/lake-lint-toml` in
`lakefile.toml` format), establishes a green `lake lint`, applies one intended
mutation, and re-establishes the green control after removing all build output.
The driver reuses the build-policy audit body, whose detectors the build-policy
partition qualifies; these controls establish Lake's dispatch, the exit classes,
and the editor/builtin boundaries of this invocation path. Decision probes load a changed
adopter's workspace in-process, as the driver does, and check the decision of its claimed build
under the owner's `--ordinary-lakefiles` without running an audit. They are diagnostics,
not proofs of the driver or of Lake.
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
(`Lake.markerInputs`, `Lake.checked_auditMarkerNeeded`) must be `marked`: `true` keeps the
audit-build marker, `false` omits it. A failure names `Lake.markerReason`. The loads share the
process's search path, so they run one at a time under `probes`. -/
private def probe (probes : Std.Mutex Unit) (adopter : FilePath) (label : String)
    (targets : Array String) (marked : Bool) : IO (Array String) := do
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
      let text (keeps : Bool) := if keeps then "keeps" else "omits"
      pure <| match decision with
        | .error error => #[s!"lake-lint/{label}: the workspace could not be read: {error}"]
        | .ok (decided, reason) => if decided == marked then #[] else
            #[s!"lake-lint/{label}: the claimed build {text decided} the marker, expected \
              {text marked}: {reason.getD "the workspace has the plain shape"}"]
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
the guard (`probe`), each with one change to the adopter: the custom `policy` target and a
library in `needs` keep the marker, an `input_file` in `needs` does not, and each change to the
plain shape below keeps it: Lake's `ilean` facet declared again with Lake's own configuration, a
library field outside the plain shape's list (`libName`), a `nativeFacets` that is not Lake's
whole default term, a lakefile declaration beside Lake's configuration declarations, and a theorem
that equates two functions. A custom target also brings declarations that are not Lake's
configuration declarations and a configuration term that `Lake.defaultFunctionFields` does not
read, so it keeps the marker on each of these counts. -/
private def leanAdopter (probes : Std.Mutex Unit) (repo adopter : FilePath) :
    IO (Array String) := do
  BuildLintQualification.setup repo adopter
  -- The first run builds every module, showing Lake's progress line for each.
  let positive := accepted "lean/positive"
  let mut failures ← expect adopter
    { positive with contains := positive.contains.push "] Built Widget" }
  if !failures.isEmpty then return failures
  failures := failures ++ (← probe probes adopter "lean/custom-target-marked" #["Widget"] true)
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
  -- A library outside the claim that the claimed library has built first (`needs`).
  let tooling := adopter / "Tooling.lean"
  IO.FS.writeFile tooling "/-! Tooling outside the claim. -/\n"
  IO.FS.writeFile lakefile <| widgetLibrary "needs := #[`@/Tooling]\n\nlean_lib Tooling where\n  \
    globs := #[.one `Tooling]"
  failures := failures ++ (← probe probes adopter "lean/needed-library-marked" #["Widget"] true)
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
  failures := failures ++ (← probe probes adopter "lean/input-needs-plain" #["Widget"] false)
  IO.FS.removeFile notes
  -- Each of these keeps the marker: Lake's `ilean` facet declared again with Lake's own
  -- configuration, which the compiled configuration file records as a facet declaration; a field
  -- outside the plain shape's list with another value than Lake's default; a `nativeFacets` that
  -- differs from Lake's default only in the `Decidable` instance of its `if`, which adds code; a
  -- declaration of the lakefile beside Lake's configuration declarations; and a theorem that
  -- equates two functions, the form of a compiler replacement (`csimp`).
  let marked (label text : String) : IO (Array String) := do
    IO.FS.writeFile lakefile text
    probe probes adopter label #["Widget"] true
  failures := failures ++ (← marked "lean/lake-facet-marked" (plain ++
    "\n@[«module_facet»] def ileanAgain : ModuleFacetDecl :=\n  \
      ⟨Module.ileanFacet, Module.ileanFacetConfig⟩\n"))
  failures := failures ++ (← marked "lean/field-marked" (widgetLibrary "libName := \"widget\""))
  failures := failures ++ (← marked "lean/native-facets-marked"
    (widgetLibrary "nativeFacets := fun b => #[@ite (ModuleFacet System.FilePath) (b = true)\n    \
      (dbgTrace \"extra\" (fun _ => inferInstance)) Module.oExportFacet Module.oFacet]"))
  failures := failures ++ (← marked "lean/declaration-marked"
    (plain ++ "\ndef helperVersion : Nat := 1\n"))
  failures := failures ++ (← marked "lean/theorem-marked"
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
marker, and an ordinary build reuses its output. Decision probes (`probe`) of the guard, each one
change to the adopter: the filter `"*"` does not keep the marker, and a filter by extension and
the `Regula.Linter` import each keep it. -/
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
  failures := failures ++ (← probe probes adopter "toml/star-plain" #[] false)
  withFilter "filter = { extension = [\"lean\"] }"
  failures := failures ++ (← probe probes adopter "toml/filter-marked" #[] true)
  withFilter "filter = \"*\""
  IO.FS.writeFile double doubleSource
  failures := failures ++ (← probe probes adopter "toml/linter-import-marked" #[] true)
  IO.FS.removeDirAll inputs
  restore adopter (originals ++ targetOriginals)
  failures := failures ++
      (← expect adopter (accepted "toml/fresh-restored" (fresh := true)) #["--", "--fresh"])
  return failures

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
then both independent adopters and the cold compiler guard, each in its own disposable
workspace. The adopters' decision probes load their workspaces one at a time (`probe`). -/
def qualify (repo scratch : FilePath) (jobs : Nat) : IO (Array String) := do
  let absent ← withScratch scratch "lake-lint-worker" fun adopter => absentWorker repo adopter
  if !absent.isEmpty then return absent
  let probes ← Std.Mutex.new ()
  let results ← mapConcurrent jobs
    #[("lean", leanAdopter probes), ("toml", tomlAdopter probes), ("guard", compilerGuard)]
    fun (name, control) => withScratch scratch s!"lake-lint-{name}" fun adopter =>
                            control repo adopter
  return results.foldl (· ++ ·) #[]

end Regula.Checker.LintQualification
