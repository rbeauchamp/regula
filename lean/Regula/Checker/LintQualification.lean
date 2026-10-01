import Regula.Checker.BuildLintQualification

/-!
# Lake lint driver qualification

Qualification of the `lake lint` driver path. Each control copies a shipped adopter
(`examples/build-lint` in `lakefile.lean` format, `examples/lake-lint-toml` in
`lakefile.toml` format), establishes a green `lake lint`, applies one intended
mutation, and re-establishes the green control after removing all build output.
The driver reuses the build-policy audit body, whose detectors the build-policy
partition qualifies; these controls establish Lake's dispatch, the exit classes,
and the editor/builtin boundaries of this invocation path. They are diagnostics,
not proofs of the driver or of Lake.
-/

namespace Regula.Checker.LintQualification

open Lean System

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
      "regula lint: PASS — fresh whole-project acceptance"
    else "regula lint: PASS — incremental project acceptance"],
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

/-- `lakefile.lean` adopter: every exit class with its summary counts, a repeated cached failure,
a claimed import outside every library (RG2004) in the driver and the file audit, a failed audit
worker reported with its own error, Lake's builtin-only and combined dispatch, and the read-only
configuration explanation. Default output shows Lake's build progress and no timing span; the
file audit lists every classified declaration only with `--verbose`. -/
private def leanAdopter (repo adopter : FilePath) : IO (Array String) := do
  BuildLintQualification.setup repo adopter
  -- The first run builds every module, showing Lake's progress line for each.
  let positive := accepted "lean/positive"
  let mut failures ← expect adopter
    { positive with contains := positive.contains.push "] Built Widget" }
  if !failures.isEmpty then return failures
  failures := failures ++ (← expect adopter {
      label := "lean/explain-config", exitCode := 2,
      contains := #["no audit was run", "Widget.Additional", "kernel-only"],
      excludes := #["regula lint: PASS"] } #["--", "--explain-config"])
  -- The file audit lists only declarations with a finding, and timing spans are verbose output.
  failures := failures ++ (← assess {
      label := "lean/file-positive", exitCode := 0, contains := #["file audit: PASS"],
      excludes := #["[OK]", "verification phase", "diagnostic span"] }
    (← fileAudit adopter "Widget.lean"))
  failures := failures ++ (← assess {
      label := "lean/file-verbose", exitCode := 0,
      contains := #["file audit: PASS", "[OK]", "diagnostic span"] }
    (← fileAudit adopter "Widget.lean" #["--verbose"]))
  let additional := adopter / "Widget" / "Additional.lean"
  let manifest := adopter / "foundation_manifest.json"
  let widget := adopter / "Widget.lean"
  let lakefile := adopter / "lakefile.lean"
  let originals := #[(additional, ← IO.FS.readFile additional),
    (manifest, ← IO.FS.readFile manifest), (widget, ← IO.FS.readFile widget),
    (lakefile, ← IO.FS.readFile lakefile)]
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
A claimed `lean_exe` whose Lake target name is not a Lean identifier is accepted under that name
and classified alike under the name as Lean prints it; naming both is a configuration refusal,
and so is an entry, claimed or excluded, that names no root executable: one refusal that quotes
the entry as the manifest writes it and lists the root executables by Lake target name. -/
private def tomlAdopter (repo adopter : FilePath) : IO (Array String) := do
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
      excludes := #["regula lint: PASS"] } #["-d", adopter.toString])
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
  failures := failures ++ (← expect adopter {
      label := "toml/live-finding", exitCode := 1,
      contains := #["RG1001", "liveFinding", "regula lint: VIOLATION (exit 1)"],
      excludes := #["build-failed", "editorSnapshot"] })
  restore adopter originals
  -- A `lean_exe` whose Lake target name is not a Lean identifier (#163). The manifest names it
  -- by that name or as Lean prints it; both are one claim, naming both is a duplicate, and an
  -- entry, claimed or excluded, that names no executable is one manifest refusal that quotes it
  -- as written and lists the root executables by Lake target name.
  let lakefile := adopter / "lakefile.toml"
  let manifest := adopter / "foundation_manifest.json"
  let cli := adopter / "Gadget" / "Cli.lean"
  let targetOriginals := #[(lakefile, ← IO.FS.readFile lakefile),
    (manifest, ← IO.FS.readFile manifest)]
  let claiming (executables : Array String) (excluded : Array String := #[]) : String :=
    Json.compress <| Json.mkObj [
      ("schema-version", toJson (2 : Nat)),
      ("surfaces", toJson #[Json.mkObj [
        ("library", toJson "Gadget"), ("executables", toJson executables),
        ("claim", toJson "choice-free"), ("execution", toJson "report"),
        ("rationale", toJson "target-name control")]]),
      ("excluded-libraries", toJson (#[] : Array Json)),
      ("excluded-executables", toJson <| excluded.map fun executable => Json.mkObj [
        ("executable", toJson executable), ("rationale", toJson "target-name control")])]
  let explained (label : String) : Expectation := {
    label, exitCode := 2, contains := #["no audit was run", "executables: «gadget-tool»"],
    excludes := #["regula lint: PASS", "manifest-"] }
  IO.FS.writeFile lakefile <| (← IO.FS.readFile lakefile) ++
    "\n[[lean_exe]]\nname = \"gadget-tool\"\nroot = \"Gadget.Cli\"\n"
  IO.FS.writeFile cli
    "/-! The adopter's command. -/\n\n/-- Does nothing. -/\ndef main : IO Unit := pure ()\n"
  IO.FS.writeFile manifest (claiming #["gadget-tool"])
  failures := failures ++ (← expect adopter (accepted "toml/target-name"))
  failures := failures ++
    (← expect adopter (explained "toml/target-name-config") #["--", "--explain-config"])
  IO.FS.writeFile manifest (claiming #["«gadget-tool»"])
  failures := failures ++
    (← expect adopter (explained "toml/printed-name-config") #["--", "--explain-config"])
  IO.FS.writeFile manifest (claiming #["gadget-tool", "«gadget-tool»"])
  failures := failures ++ (← expect adopter {
      label := "toml/both-spellings", exitCode := 2,
      contains := #["RG2002", "manifest-schema: duplicate executable '«gadget-tool»'",
        "regula lint: INVALID CONFIGURATION (exit 2)"] })
  IO.FS.writeFile manifest (claiming #["gadget-tol"])
  let unknown (label entry : String) : Expectation := {
    label, exitCode := 2,
    contains := #["RG2002",
      s!"manifest-incomplete: executable '{entry}' is not a root Lean executable",
      "the root Lean executables are [\"gadget-tool\"]",
      "regula lint: INVALID CONFIGURATION (exit 2)"],
    excludes := #["RG2001", s!"«{entry}»", "«gadget-tool»"] }
  failures := failures ++ (← expect adopter (unknown "toml/unknown-executable" "gadget-tol"))
  IO.FS.writeFile manifest (claiming #["gadget-tool"] #["old-tool"])
  failures := failures ++ (← expect adopter (unknown "toml/unknown-excluded" "old-tool"))
  IO.FS.removeFile cli
  restore adopter targetOriginals
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

/-- The absent-worker control first, alone, since the adopters share the checker's binaries;
then both independent adopters, each in its own disposable workspace. -/
def qualify (repo scratch : FilePath) (jobs : Nat) : IO (Array String) := do
  let absent ← withScratch scratch "lake-lint-worker" fun adopter => absentWorker repo adopter
  if !absent.isEmpty then return absent
  let results ← mapConcurrent jobs #[("lean", leanAdopter), ("toml", tomlAdopter)]
    fun (name, control) => withScratch scratch s!"lake-lint-{name}" fun adopter =>
                            control repo adopter
  return results.foldl (· ++ ·) #[]

end Regula.Checker.LintQualification
