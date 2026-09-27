import Regula.Checker.PolicyCodec
import Regula.Checker.Documentation
import Regula.Checker.Lake
import Regula.Checker.CompilerPaths
import Regula.Checker.PolicyQualification
import Regula.Checker.BuildLintQualification
import Regula.Checker.LintQualification

/-!
# Checker qualification suite

Focused qualification suite for the repository's Lean-native checkers.

The suite runs in two tiers that share one invariant prefix instead of
re-paying it per verdict:

* The **default tier** attacks declaration policy with every fixed fixture,
  attacks the Markdown protocol in memory and through the in-process fence
  auditor, attacks strict manifest parsing, and applies every structural
  mutation in parallel isolated project copies. Fixture verdicts are computed
  in this process: all fixture sources compile in bounded parallel batches and
  are then inspected by isolated group workers, using
  the same `SourceAudit`/`Environment`/`Frontend`/`Policy` functions the public
  gate uses. A thin real-CLI smoke tier (a handful of fixtures through actual
  `axiomGate --file` spawns) keeps end-to-end evidence for the public
  interface contract.
* The **conditional tier** (`--build-bound`) holds the inherently build-bound
  controls that cannot be sub-second by construction: the full real-CLI
  fixture sweep, the end-to-end fence-corpus run, external adoption of the
  checker package from scratch projects in both lakefile formats, and the
  clean-checkout environment, public-surface, and fresh-plan controls. Its
  trigger is unchanged: checker policy, fixture, or claimed detection-behavior
  changes, plus CI.

With `--build-bound`, the closed partitions are `fixtures` (in-process fixtures,
scanner, and fence corpus), `structural` (structural/compiler-path and
manifest controls), `cli` (the complete CLI sweep), `environments` (packaging
and fresh-state controls), `build-policy` (ordinary-build enforcement), and `lint-driver` (`lake
lint`
dispatch and exit classes).
Each starts with the same baseline preparation.
Their disjoint union is the full run; no partition alone reports full qualification.

It is intentionally qualification-only, not an ordinary build.
-/

namespace Regula.Checker.CheckerSelftest

open Lean System
open Regula.Checker
open Regula.Checker.Documentation
open Regula.Checker.Policy

/-- The verdict a fixture declares in `fixtures.json` (`expect`). -/
inductive Expectation where
  /-- The checker must accept the fixture. -/
  | pass
  /-- The checker must reject the fixture, for the declared reasons. -/
  | fail
  deriving Repr, BEq

/-- One entry of `Fixtures/fixtures.json`, resolved to its Lake fixture module. -/
structure FixtureSpec where
  /-- The fixture's module name, the entry's key. -/
  moduleName : String
  /-- The fixture's source file, as Lake resolves it in the `Fixtures` library. -/
  source : FilePath
  /-- Whether the checker must accept or reject the fixture. -/
  expectation : Expectation
  /-- For a rejection, the exact set of `VIOLATION[...]` reasons expected, or
  `#["compile-error"]` for a fixture that must fail to compile. -/
  reasons : Array String := #[]
  /-- The foundation profile passed as `--claim`, when the entry sets one. -/
  claim : Option Profile := none
  /-- The execution mode passed as `--execution`, when the entry sets one. -/
  execution : Option String := none
  /-- For an accepted fixture, a foundation label some declaration must be reported with. -/
  label : Option String := none
  /-- For a compile-error fixture, the pattern its output must match (default `error`). -/
  pattern : Option String := none
  /-- Texts the checker output must contain, whatever the verdict. -/
  output : Array String := #[]
  deriving Repr

/-- Disjoint groups whose union is the complete build-bound qualification. -/
inductive Partition where
  /-- In-process fixture verdicts, the Markdown scanner and the fence corpus. -/
  | fixtures
  /-- Structural, compiler-path and manifest controls. -/
  | structural
  /-- Every fixture through a real `axiomGate --file` invocation. -/
  | cli
  /-- The end-to-end fence corpus and the external-adopter and clean-checkout controls. -/
  | environments
  /-- Ordinary-build enforcement controls (`build-policy`). -/
  | buildPolicy
  /-- `lake lint` dispatch and exit-class controls (`lint-driver`). -/
  | lintDriver
  deriving Repr, BEq, DecidableEq

private def Partition.label : Partition → String
  | .fixtures => "fixtures"
  | .structural => "structural"
  | .cli => "cli"
  | .environments => "environments"
  | .buildPolicy => "build-policy"
  | .lintDriver => "lint-driver"

/-- The full run enumerates each supported partition exactly once. -/
private def Partition.all : List Partition :=
    [.fixtures, .structural, .cli, .environments, .buildPolicy, .lintDriver]

private theorem Partition.all_complete (partition : Partition) : partition ∈ all := by
  cases partition <;> simp [all]

private theorem Partition.all_nodup : all.Nodup := by decide

/-- The parsed `checkerSelftest` command-line options. -/
structure Options where
  /-- `--jobs N`: the number of parallel workers; must be positive. -/
  jobs : Nat := 4
  /-- `--structural-only`: run only the structural controls after the baseline build. -/
  structuralOnly : Bool := false
  /-- `--build-bound`: also run the conditional, build-bound tier. -/
  buildBound : Bool := false
  /-- `--partition NAME`: run only this build-bound group; requires `--build-bound`. -/
  partition : Option Partition := none
  /-- `--help` or `-h`: print the usage and exit. -/
  help : Bool := false

private def usage : String :=
  "usage: lake exe checkerSelftest -- [--jobs N] [--structural-only] [--build-bound [--partition \
    fixtures|structural|cli|environments|build-policy|lint-driver]]\n" ++
  "--fences-only: focused in-process and public fence qualification, without the full suite\n" ++
  "default tier: every planted-defect verdict in one process plus a real-CLI smoke tier\n" ++
  "--build-bound: additionally run the conditional tier (real-CLI sweep, end-to-end\n" ++
  "fence corpus, external adopters, clean-checkout environment, public controls)\n" ++
  "--partition: run only the named build-bound group; all six groups are required for full \
    qualification"

private def parseArgs : List String → Options → IO Options
  | [], options => do
      if options.partition.isSome && !options.buildBound then
        throw <| IO.userError "--partition requires --build-bound"
      if options.structuralOnly && (options.buildBound || options.partition.isSome) then
        throw <| IO.userError "--structural-only conflicts with --build-bound and --partition"
      return options
  | "--" :: rest, options => parseArgs rest options
  | "--jobs" :: value :: rest, options => do
      let jobs ← parseNatArg "--jobs" value
      parseArgs rest { options with jobs }
  | "--structural-only" :: rest, options => do
      if options.structuralOnly then throw <| IO.userError "duplicate --structural-only"
      parseArgs rest { options with structuralOnly := true }
  | "--build-bound" :: rest, options => do
      if options.buildBound then throw <| IO.userError "duplicate --build-bound"
      parseArgs rest { options with buildBound := true }
  | "--partition" :: value :: rest, options => do
      if options.partition.isSome then throw <| IO.userError "duplicate --partition"
      let partition ← match value with
        | "fixtures" => pure Partition.fixtures
        | "structural" => pure Partition.structural
        | "cli" => pure Partition.cli
        | "environments" => pure Partition.environments
        | "build-policy" => pure Partition.buildPolicy
        | "lint-driver" => pure Partition.lintDriver
        | _ => throw <| IO.userError s!"unknown partition: {value}"
      parseArgs rest { options with partition := some partition }
  | "--help" :: rest, options | "-h" :: rest, options =>
      parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def requiredString (value : Json) (key where_ : String) : IO String := do
  let field ← IO.ofExcept <| value.getObjVal? key
  match field with
  | .str text => return text
  | _ => throw <| IO.userError s!"{where_}.{key} must be a string"

private def optionalString (value : Json) (key where_ : String) : IO (Option String) :=
  match value.getObjVal? key with
  | .error _ => return none
  | .ok (.str text) => return some text
  | .ok _ => throw <| IO.userError s!"{where_}.{key} must be a string"

/-- Immutable Lake-derived coordinates, acquired before fixture imports can
register additional environment extensions. Scratch controls reanchor the
relative directory without loading cold Lake configurations in this process. -/
private structure SourceLayout where
  relativeDir : FilePath

private def loadSourceLayout (repo : FilePath) : IO SourceLayout := do
  let relativeDir ← Workspace.withRootWorkspace repo fun ws => pure ws.root.config.srcDir.normalize
  if relativeDir.isAbsolute || relativeDir.components.contains ".." then
    throw <|
        IO.userError "self-test: package source directory must stay inside the copied repository"
  return { relativeDir }

private def loadFixtureManifest (layout : SourceLayout) (repo : FilePath) : IO
    (Array FixtureSpec) := do
  let path := (repo / layout.relativeDir) / "Fixtures" / "fixtures.json"
  let inventory ← Lake.surfaceInventory repo
  let some library := inventory.libraries.find? (·.library == "Fixtures")
    | throw <| IO.userError "fixture manifest: Lake omitted the Fixtures library"
  let value ← readJson path
  let object ← IO.ofExcept value.getObj?
  let allowed :=
      #["expect", "reason", "reasons", "claim", "execution", "label", "pattern", "output"]
  let mut fixtures : Array FixtureSpec := #[]
  for moduleName in object.keysArray.qsort (· < ·) do
    let some source := library.sources.find? (·.«module» == moduleName.toName)
      | throw <| IO.userError s!"{moduleName}: manifest entry has no Lake fixture module"
    let spec ← IO.ofExcept <| value.getObjVal? moduleName
    let specObject ← IO.ofExcept spec.getObj?
    let unknown := specObject.keysArray.filter fun key => !allowed.contains key
    if !unknown.isEmpty then
      throw <|
          IO.userError s!"{moduleName}: fixture manifest has unknown keys {repr unknown.toList}"
    let expectation ← match ← requiredString spec "expect" moduleName with
      | "pass" => pure Expectation.pass
      | "fail" => pure Expectation.fail
      | _ => throw <| IO.userError s!"{moduleName}: expect must be pass or fail"
    let reason ← optionalString spec "reason" moduleName
    let reasons ← match spec.getObjVal? "reasons" with
      | .error _ => pure #[]
      | .ok value => jsonStringArray s!"{moduleName}.reasons" value
    if reason.isSome && !reasons.isEmpty then
      throw <| IO.userError s!"{moduleName}: use exactly one of reason or reasons"
    let reasons := match reason with
      | some text => #[text]
      | none => reasons
    let claim ← match ← optionalString spec "claim" moduleName with
      | none => pure none
      | some text => match Profile.parse? text with
        | some claim => pure (some claim)
        | none => throw <| IO.userError s!"{moduleName}: unknown claim {text}"
    let execution ← optionalString spec "execution" moduleName
    if let some mode := execution then
      if (ExecutionClaim.parse? mode).isNone then
        throw <| IO.userError s!"{moduleName}: unknown execution mode {mode}"
    let label ← optionalString spec "label" moduleName
    let pattern ← optionalString spec "pattern" moduleName
    let output ← match spec.getObjVal? "output" with
      | .error _ => pure #[]
      | .ok value => jsonStringArray s!"{moduleName}.output" value
    fixtures := fixtures.push {
      moduleName, source := source.source, expectation, reasons, claim, execution, label,
          pattern, output }
  if library.modules.size != fixtures.size then
    throw <| IO.userError <|
      s!"fixture manifest/Lake module count mismatch: {fixtures.size}/{library.modules.size}"
  return fixtures

private def uniqueSorted (values : Array String) : Array String :=
  values.foldl (fun found value => if found.contains value then found else found.push value) #[]
    |>.qsort (· < ·)

private def violationReasons (output : String) : Array String := Id.run do
  let mut reasons : Array String := #[]
  for line in output.splitOn "\n" do
    match line.splitOn "VIOLATION[" with
    | _ :: suffix :: _ =>
        if let some reason := (suffix.splitOn "]").head? then reasons := reasons.push reason
    | _ => pure ()
  uniqueSorted reasons

private def runBinary (repo : FilePath) (name : String)
    (args : Array String) : IO ProcessResult :=
  runProcess repo (repo / ".lake" / "build" / "bin" / name).toString args

private def runBinaryFrom (binaryRepo cwd : FilePath) (name : String)
    (args : Array String) : IO ProcessResult :=
  runProcess cwd (binaryRepo / ".lake" / "build" / "bin" / name).toString args

/-- Exact verdict assessment for one fixture against gate (or gate-equivalent)
output. The same function assesses real CLI output and the in-process batch
verdicts, so both paths assert identical intended reasons. -/
private def assessFixtureOutput (fixture : FixtureSpec) (succeeded : Bool)
    (output : String) : Option String := Id.run do
  if let some missing := fixture.output.find? fun needle => !output.contains needle then
    return some s!"{fixture.moduleName}: missing expected output {repr missing}:\n{output}"
  match fixture.expectation with
  | .pass =>
      if !succeeded then
        return some s!"{fixture.moduleName}: expected PASS:\n{output}"
      if let some label := fixture.label then
        if !output.contains s!"-> {label}" then
          return some s!"{fixture.moduleName}: no declaration had expected label {label}:\n{output}"
      return none
  | .fail =>
      if succeeded then
        return some s!"{fixture.moduleName}: expected failure, checker passed"
      if fixture.reasons == #["compile-error"] then
        let pattern := fixture.pattern.getD "error"
        if !Documentation.matchesPattern pattern.toLower output.toLower then
          return some
              s!"{fixture.moduleName}: compile failure missed pattern {repr pattern}:\n{output}"
        return none
      let actual := violationReasons output
      let expected := uniqueSorted fixture.reasons
      if actual != expected then
        return some <| s!"{fixture.moduleName}: intended exact reason set " ++
          s!"{repr expected.toList}, got {repr actual.toList}:\n{output}"
      return none

/-- Real-CLI fixture control: one actual `axiomGate --file` invocation. -/
private def checkFixtureCli (repo : FilePath) (fixture : FixtureSpec) : IO (Option String) := do
  let args := #["--file", fixture.source.toString] ++ match fixture.claim with
    | some claim => #["--claim", claim.toString]
    | none => #[]
  let args := args ++ match fixture.execution with
    | some mode => #["--execution", mode]
    | none => #[]
  let result ← runBinary repo "axiomGate" args
  return assessFixtureOutput fixture result.succeeded result.output

private structure CompiledFixture where
  index : Nat
  fixture : FixtureSpec
  compilation : SourceAudit.Compilation
  constantNames : Array String
  importNames : Array Name
  wantsTranscript : Bool

private def disjointNames (left right : Array String) : Bool :=
  left.all fun name => !right.contains name

/-- Render the exact per-declaration and execution-coverage lines the public
`axiomGate --file` audit prints for one elaborated fixture, using the same
`Policy` functions, so the shared assessment sees an equivalent report. -/
private def renderFileAudit (fixture : FixtureSpec) (_moduleName : String)
    (declarations : Array Regula.Report.Declaration)
    (roots : Array Regula.Report.ExecutionRoot)
    (transcripts : Array Frontend.Transcript) : String × Bool := Id.run do
  let .ok scope := Policy.admitScope declarations transcripts
    | return ("invalid policy observation inventory", true)
  let execution := match fixture.execution with
    | some mode => (ExecutionClaim.parse? mode).getD .report
    | none => .report
  let mut lines : Array String := #[]
  let mut failed := false
  for h : decl in scope.inventory.declarations do
    let rule := Policy.ruleForMember decl fixture.claim scope h
    failed := failed || rule.isSome
    let verdict := match rule with
      | none => "OK"
      | some id => s!"VIOLATION[{(Regula.descriptor id).applicability}]"
    lines := lines.push s!"[{verdict}] {Policy.classifyMember decl scope h}"
  let .ok executionInventory := Policy.admitExecution roots
    | return ("invalid execution inventory", true)
  let executionViolations := Policy.executionFailures executionInventory execution
  for root in roots do
    if !root.boundaries.isEmpty || !root.unresolved.isEmpty then
      lines := lines.push s!"  execution root {root.name}"
      for boundary in root.boundaries do
        lines := lines.push s!"    {Policy.describeBoundary boundary}"
      for item in root.unresolved do
        lines := lines.push s!"    unresolved {item}"
  for violation in executionViolations do
    let reason := (violation.splitOn ":").head?.getD "execution-unresolved"
    lines := lines.push s!"[VIOLATION[{reason}]] {violation}"
  return ("\n".intercalate lines.toList, !failed && executionViolations.isEmpty)

/-- Batched in-process fixture qualification: every fixture compiles in
bounded parallel batches, fresh-frontend transcripts are re-elaborated by
isolated spawned worker processes (the checker's own pinned frontend, exactly
the process environment the public CLI provides) before one
isolated environment worker per compatible import group (split further whenever
constant names collide), reusing the checker's own `SourceAudit`, `Environment`,
`Frontend`, and `Policy` functions. Compile failures are assessed against the
compiler output, exactly as the public gate's file mode reports them. -/
private unsafe def fixtureVerdicts (repo scratch : FilePath) (jobs : Nat)
    (fixtures : Array FixtureSpec) (leanPath : Array FilePath) : IO (Array (Option String)) := do
  let indexed := fixtures.mapIdx fun index fixture => (index, fixture)
  let compilations ← mapConcurrent jobs indexed fun (index, fixture) => do
    let outcome ← SourceAudit.compile repo scratch {
      «module» := s!"SelftestFixture_{index + 1}"
      source := ← IO.FS.readFile fixture.source
    }
    let compilation ← IO.ofExcept <| outcome.mapError (·.detail)
    return (index, fixture, compilation)
  let mut results : Array (Option String) := Array.replicate fixtures.size none
  let mut pending : Array CompiledFixture := #[]
  for (index, fixture, compilation) in compilations do
    if !SourceAudit.compilationPassed compilation then
      results := results.set! index
        (assessFixtureOutput fixture false compilation.process.output)
    else
      let (moduleData, _) ← Lean.readModuleData compilation.oleanPath
      pending := pending.push {
        index, fixture, compilation
        constantNames := moduleData.constNames.map (·.toString)
        importNames := moduleData.imports.map (·.module)
        -- Same transcript predicate as the post-load check, applied to the
        -- raw module constant records with the probe's own kind mapping, so
        -- only fixtures that can need a transcript pay for one. A divergence
        -- (post-load need with no worker transcript) fails closed below.
        wantsTranscript := moduleData.constants.any fun info =>
          Policy.declarationNeedsTranscript info.isUnsafe info.isPartial
            (Regula.Probe.kindOf info) info.name
      }
  -- Group by exact constant-name disjointness (the `Documentation.auditTasks`
  -- strategy): one environment load per collision group covers every fixture
  -- whose names do not collide, so the large shared dependency closure is
  -- loaded once. In-process imports run initializers through Lean's global
  -- importing flag, so group loads stay sequential on this thread, exactly as
  -- in `Documentation.auditTasks`.
  let mut groups : Array (Array String × Array CompiledFixture) := #[]
  for item in pending do
    let mut placed := false
    for groupIndex in [:groups.size] do
      let (names, items) := groups[groupIndex]!
      -- Admission failures invalidate an environment before it has a report.
      -- Keep those single-fault controls isolated from unrelated fixtures.
      if !item.fixture.reasons.contains "kernel-admission" &&
          !(items.any (·.fixture.reasons.contains "kernel-admission")) &&
          (items.all fun other => other.importNames == item.importNames) &&
          disjointNames item.constantNames names then
        groups := groups.set! groupIndex (names ++ item.constantNames, items.push item)
        placed := true
        break
    if !placed then
      groups := groups.push (item.constantNames, #[item])
  IO.println (s!"fixture compilations complete: {fixtures.size}; " ++
    s!"inspecting {pending.size} elaborated fixture(s) in {groups.size} collision group(s)")
  (← IO.getStdout).flush
  let selfLib ← checkerPackageLibDir
  let oldSearchPath ← Lean.searchPathRef.get
  let scopedPath := scratch :: leanPath.toList ++ selfLib.toList ++ oldSearchPath
  -- Transcript workers run in isolated spawned processes and finish before
  -- the parent loads environments, avoiding simultaneous large imports. Spawning
  -- keeps each transcript byte-identical in provenance to the public CLI's
  -- fresh re-elaboration (a fresh process can never see this harness's
  -- attribute state). Failures are tolerated here (a `sorry` fixture fails
  -- its warning-free transcript by design); consumers below fail closed on a
  -- missing transcript with the same text the CLI path reports.
  let leanPathEnv := SearchPath.toString scopedPath
  let transcriptTask ← IO.asTask (prio := .dedicated) do
    mapConcurrent jobs pending fun item => do
      let moduleName := item.compilation.spec.«module»
      if !item.wantsTranscript then return (moduleName, none)
      try
        let out := scratch / s!"transcript-{item.index + 1}.json"
        let spawned ← runProcess repo
          (repo / ".lake" / "build" / "bin" / "checkerSelftest").toString
          #["--transcript-worker", (Regula.RegistryCodec.nameJson moduleName.toName).compress,
              item.compilation.sourcePath.toString,
            out.toString]
          #[("LEAN_PATH", some leanPathEnv)]
        if !spawned.succeeded then return (moduleName, none)
        match Regula.Checker.PolicyCodec.parse (← IO.FS.readFile out) with
        | .error _ => return (moduleName, none)
        | .ok json =>
          let payload := readWorkerPacket (sourceWorkerRequest "transcript" moduleName.toName
            item.compilation.sourcePath item.compilation.spec.source) json
          match payload >>= fromJson? with
          | .error _ => return (moduleName, none)
          | .ok transcript => return (moduleName, some (transcript : Frontend.Transcript))
      catch _ => return (moduleName, none)
  -- Complete all transcript workers before starting isolated report workers.
  let transcripts ← IO.ofExcept (← IO.wait transcriptTask)
  let mut inspected : Array (CompiledFixture × Array Regula.Report.Declaration ×
      Array Regula.Report.ExecutionRoot) := #[]
  Lean.searchPathRef.set scopedPath
  try
    for (_, items) in groups do
      try
        let outcome ← SourceAudit.inspectGroupCurrentSearchPath
          (items.map (·.compilation.spec.«module».toName))
          (compiledSources := items.map fun item => {
            moduleName := item.compilation.spec.module.toName
            path := item.compilation.sourcePath.toString
            content := item.compilation.spec.source })
        let inspectedGroup ← IO.ofExcept <| outcome.mapError (·.detail)
        let report := inspectedGroup.report
        for item in items do
          let moduleName := item.compilation.spec.«module»
          let declarations := report.declarations.filter (·.«module» == moduleName.toName)
            |>.qsort fun left right => Name.quickLt left.name right.name
          let roots := report.execution.filter (·.«module» == moduleName.toName)
          inspected := inspected.push (item, declarations, roots)
      catch error =>
        for item in items do
          results := results.set! item.index (assessFixtureOutput item.fixture false error.toString)
    pure ()
  finally Lean.searchPathRef.set oldSearchPath
  for (item, declarations, roots) in inspected do
    let moduleName := item.compilation.spec.«module»
    if Policy.needsFrontendTranscript declarations then
      match transcripts.find? (·.1 == moduleName) with
      | some (_, some transcript) =>
        let (output, succeeded) := renderFileAudit item.fixture moduleName
          declarations roots #[transcript]
        results := results.set! item.index (assessFixtureOutput item.fixture succeeded output)
      | _ =>
        results := results.set! item.index
          (assessFixtureOutput item.fixture false
            (if item.wantsTranscript then
              s!"fresh frontend elaboration failed for {moduleName}"
            else
              s!"transcript need pre-filter diverged for {moduleName}"))
    else
      let (output, succeeded) := renderFileAudit item.fixture moduleName
        declarations roots #[]
      results := results.set! item.index (assessFixtureOutput item.fixture succeeded output)
  return results

/-- Real-CLI smoke tier: a small diverse set of fixtures through actual
`axiomGate --file` invocations, keeping end-to-end evidence for the public
interface contract in the default tier. -/
private def smokeFixtureNames : Array String :=
  #["Fixtures.Positive.KernelOnly", "Fixtures.Mutations.DirectAxiom",
    "Fixtures.Positive.ExternBoundary", "Fixtures.Positive.DependentCorrespondence",
    "Fixtures.Mutations.ConditionalCorrespondence"]

/-- Counterexample aid, not correctness evidence (standard §0 "The Role of Testing"):
concrete `Documentation.scan` inputs for each marker/fence problem class. A universal
statement of the scanner's problem coverage is not yet proved; until it is, these cases
only search for counterexamples. -/
private def scannerQualification : Array String := Id.run do
  let cases : Array (String × String × String) := #[
    ("positive", "```lean\ntheorem ok : True := trivial\n```\n", ""),
    ("unclosed", "```lean\ntheorem x : True := trivial\n", "never closed"),
    ("empty-pattern", "<!-- lean-fail: -->\n```lean\ndef n : Nat := \"x\"\n```\n",
        "pattern is empty"),
    ("invalid-pattern", "<!-- lean-fail: [ -->\n```lean\ndef n : Nat := \"x\"\n```\n",
        "unsupported"),
    ("malformed-marker", "<!-- lean-fail -->\n```lean\ndef n : Nat := \"x\"\n```\n", "malformed"),
    ("marker-typo", "<!--lean-fail: Type mismatch-->\n```lean\ntheorem t : 1 = 1 := rfl\n```\n",
        "malformed"),
    ("marker-truncated", "<!-- lean-trusted -->\n```lean\ntheorem t : 1 = 1 := rfl\n```\n",
        "malformed"),
    ("duplicate-marker", "<!-- lean-fail: Type mismatch -->\n<!-- lean-trusted-compiler \
      -->\n```lean\ndef n : Nat := \"x\"\n```\n", "multiple markers"),
    ("blank-separation",
        "<!-- lean-fail: Type mismatch -->\n\n```lean\ndef n : Nat := \"x\"\n```\n",
            "not immediately adjacent"),
    ("prose-orphan",
        "<!-- lean-fail: Type mismatch -->\nprose\n```lean\ndef n : Nat := \"x\"\n```\n",
            "not immediately adjacent"),
    ("nonlean-target", "<!-- lean-fail: Type mismatch -->\n```text\ndef n : Nat := \"x\"\n```\n",
        "not attached"),
    ("eof-marker", "<!-- lean-fail: Type mismatch -->", "left at end")
  ]
  let mut failures : Array String := #[]
  for (name, text, expectedProblem) in cases do
    let result := Documentation.scan text name
    if expectedProblem.isEmpty then
      if result.fences.size != 1 || !result.problems.isEmpty then
        failures := failures.push s!"scanner/{name}: expected one clean fence"
    else if !result.problems.any (·.contains expectedProblem) then
      failures :=
          failures.push s!"scanner/{name}: missing problem containing {repr expectedProblem}"
  if !Documentation.matchesPattern "(?s)failed.*law|Fields missing"
      "prefix failed\nfor a law suffix" then
    failures := failures.push "scanner/pattern: ordered/alternative matching failed"
  failures

/-- A committed LRAT certificate for `(x &&& y) + (x ||| y) = x + y` over `BitVec 2`, which
`bv_check` reads by absolute path because a fence compiles in a scratch directory. -/
private def bvCheckCertificate (repo : FilePath) : FilePath :=
  repo / "lean" / "Fixtures" / "BvCheck.lrat"

/-- The adversarial fence corpus shared by the in-process default-tier audit
and the end-to-end public `docFenceAudit` control in the conditional tier. -/
private def fenceCorpusCases (repo : FilePath) : Array (String × String × String) := #[
  ("unclosed", "```lean\ntheorem x : True := trivial\n", "never closed"),
  ("empty-pattern", "<!-- lean-fail: -->\n```lean\ndef n : Nat := \"x\"\n```\n",
      "pattern is empty"),
  ("invalid-pattern", "<!-- lean-fail: [ -->\n```lean\ndef n : Nat := \"x\"\n```\n", "unsupported"),
  ("malformed-marker", "<!-- lean-fail -->\n```lean\ndef n : Nat := \"x\"\n```\n",
      "malformed Lean fence marker"),
  ("duplicate-marker", "<!-- lean-fail: Type mismatch -->\n<!-- lean-trusted-compiler \
    -->\n```lean\ndef n : Nat := \"x\"\n```\n", "multiple markers target one fence"),
  ("blank-separation", "<!-- lean-fail: Type mismatch -->\n\n```lean\ndef n : Nat := \"x\"\n```\n",
      "not immediately adjacent"),
  ("prose-orphan", "<!-- lean-fail: Type mismatch -->\nprose\n```lean\ndef n : Nat := \"x\"\n```\n",
      "not immediately adjacent"),
  ("nonlean-target", "<!-- lean-fail: Type mismatch -->\n```text\ndef n : Nat := \"x\"\n```\n",
      "not attached to a ```lean fence"),
  ("eof-marker", "<!-- lean-fail: Type mismatch -->", "left at end of file"),
  ("positive", "```lean\ntheorem nested_ok : 1 = 1 := rfl\n```\n", "positive.md:1 PASS"),
  ("raw-import", "```lean\ntheorem missing_import : Glossary.Time = Glossary.Time := rfl\n```\n",
      "did not elaborate verbatim"),
  ("warning", "```lean\nset_option warningAsError false in\ndef hidden_warning (unused : Nat) : \
    Nat := 1\n```\n", "emitted warning"),
  ("hole", "```lean\ntheorem docs_hole : False := by sorry\n```\n", "hole.md:1 FAIL"),
  ("project-axiom", "```lean\naxiom docs_axiom : False\n```\n", "project-axiom"),
  ("valid-negative", "<!-- lean-fail: Type mismatch -->\n```lean\ndef n : Nat := \"x\"\n```\n",
      "valid-negative.md:2 PASS_NEG"),
  ("negative-info-only", "<!-- lean-fail: expectedOnlyInfo -->\n```lean\n#eval IO.println \
    \"expectedOnlyInfo\"\n#check missingActualError\n```\n", "negative-info-only.md:2 FAIL"),
  ("negative-cross-errors", "<!-- lean-fail: missingFirst.*missingSecond -->\n```lean\n#check \
    missingFirst\n#check missingSecond\n```\n", "negative-cross-errors.md:2 FAIL"),
  ("negative-multiline",
      "<!-- lean-fail: Type mismatch.*String.*Nat -->\n```lean\ndef n : Nat := \"x\"\n```\n",
          "negative-multiline.md:2 PASS_NEG"),
  ("negative-import",
      "<!-- lean-fail: unknown module prefix -->\n```lean\nimport MissingDiagnosticModule\n```\n",
          "negative-import.md:2 PASS_NEG"),
  ("negative-promoted-warning", "<!-- lean-fail: promotedWarning -->\n```lean\nimport \
    Lean\nset_option warningAsError true in\nrun_cmd Lean.logWarning \"promotedWarning\"\n```\n",
        "negative-promoted-warning.md:2 PASS_NEG"),
  ("negative-header-syntax", "<!-- lean-fail: unexpected -->\n```lean\nimport (\n```\n",
      "negative-header-syntax.md:2 PASS_NEG"),
  ("negative-abnormal", "<!-- lean-fail: deliberate -->\n```lean\nimport Lean\nrun_cmd do\n  let \
    child ← IO.Process.spawn { cmd := \"echo\", args := #[\"error: deliberate\"] }\n  discard \
    child.wait\n  Lean.logError \"deliberate\"\nrun_cmd (IO.Process.exit 7 : IO Unit)\n```\n",
        "diagnostic worker did not complete"),
  ("trusted-native", "<!-- lean-trusted-compiler -->\n```lean\nimport Init\ntheorem docs_native : \
    Nat.gcd 1071 462 = 21 := by native_decide\n```\n", "trusted-native.md:2 PASS_TRUSTED"),
  ("trusted-spoof", "<!-- lean-trusted-compiler -->\n```lean\naxiom \
    Attack._native.native_decide.ax_1 : False\n```\n", "trusted-spoof.md:2 FAIL"),
  -- `decide +native` and `bv_decide` add their axioms through the same `nativeEqTrue`, named
  -- after their own tactic: authenticated teaching passes, a positive fence reports the
  -- compiler-trusting rule (not a project or unknown axiom), and a spoofed name still fails.
  ("trusted-decide-native", "<!-- lean-trusted-compiler -->\n```lean\nimport Init\ntheorem \
    docs_decide_native : Nat.gcd 1071 462 = 21 := by decide +native\n```\n",
      "trusted-decide-native.md:2 PASS_TRUSTED"),
  ("trusted-bv-decide", "<!-- lean-trusted-compiler -->\n```lean\nimport Std.Tactic.BVDecide\n\
    theorem docs_bv_decide (x y : BitVec 8) : x * y = y * x := by bv_decide\n```\n",
      "trusted-bv-decide.md:2 PASS_TRUSTED"),
  ("positive-decide-native", "```lean\nimport Init\ntheorem docs_positive_decide_native : \
    Nat.gcd 1071 462 = 21 := by decide +native\n```\n",
      "compiler-trusting: docs_positive_decide_native"),
  ("positive-bv-decide", "```lean\nimport Std.Tactic.BVDecide\ntheorem docs_positive_bv_decide \
    (x y : BitVec 8) : x * y = y * x := by bv_decide\n```\n",
      "compiler-trusting: docs_positive_bv_decide"),
  ("trusted-tactic-spoof", "<!-- lean-trusted-compiler -->\n```lean\naxiom \
    Attack._native.decide.ax_1 : False\naxiom Attack._native.bv_decide.ax_1 : False\n```\n",
      "trusted-tactic-spoof.md:2 FAIL"),
  -- A public theorem of a `module` file elaborates its proof without exporting, so its generated
  -- names are private to the module; each native tactic is still authenticated.
  ("trusted-module-native", "<!-- lean-trusted-compiler -->\n```lean\nmodule\nimport \
    Std.Tactic.BVDecide\nmeta import Std.Tactic.BVDecide.Reflect\npublic theorem \
    docs_module_native_decide : (2 : Nat) = 2 := by native_decide\npublic theorem \
    docs_module_decide_native : Nat.gcd 1071 462 = 21 := by decide +native\npublic theorem \
    docs_module_bv_decide (x y : BitVec 8) : x * y = y * x := by bv_decide\n```\n",
      "trusted-module-native.md:2 PASS_TRUSTED"),
  -- `bv_decide?` and `bv_check` reach the same `nativeEqTrue` call through their own evaluators.
  ("trusted-bv-trace", "<!-- lean-trusted-compiler -->\n```lean\nimport Std.Tactic.BVDecide\n\
    theorem docs_bv_trace (x y : BitVec 2) : (x &&& y) + (x ||| y) = x + y := by bv_decide?\n\
    ```\n", "trusted-bv-trace.md:2 PASS_TRUSTED"),
  ("trusted-bv-check", s!"<!-- lean-trusted-compiler -->\n```lean\nimport Std.Tactic.BVDecide\n\
    theorem docs_bv_check (x y : BitVec 2) : (x &&& y) + (x ||| y) = x + y := by\n  bv_check \
    -binaryProofs \"{bvCheckCertificate repo}\"\n```\n", "trusted-bv-check.md:2 PASS_TRUSTED"),
  ("negative-compiles", "<!-- lean-fail: Type mismatch -->\n```lean\ndef n : Nat := 1\n```\n",
      "negative example elaborated successfully"),
  ("negative-other-diagnostic",
      "<!-- lean-fail: Unknown constant -->\n```lean\ndef n : Nat := \"x\"\n```\n",
          "failed, but not with expected diagnostic"),
  ("trusted-without-mechanism",
      "<!-- lean-trusted-compiler -->\n```lean\ntheorem plain : 1 = 1 := rfl\n```\n",
          "trusted marker found no compiler-trusting declaration"),
  -- The pinned renderer prints a named diagnostic as `warning(name):`
  -- (`Lean.mkErrorStringWithPos`); the audit must reject that form too.
  ("named-warning", "```lean\nimport Lean\nopen Lean\nset_option warningAsError false in\nrun_cmd \
    Lean.logNamedWarningAt (← getRef) `lean.selftestNamedWarning m!\"named\"\n```\n",
        "emitted warning")
]

/-- Corpus cases that only the public `docFenceAudit` control can exercise:
they depend on the process environment the public command runs its fence
workers in, which the in-process auditor does not reproduce. -/
private def publicOnlyFenceCases : Array (String × String × String) := #[
  -- Resolvable only through an inherited `LEAN_PATH`: the control injects a
  -- search-path entry holding a compiled module that no Lake workspace owns.
  ("stale-import",
      "```lean\nimport StaleImport\ntheorem stale_ok : staleImportValue = 1 := rfl\n```\n",
          "did not elaborate verbatim")
]

/-- A valid source rejection must not be satisfied by an import setup error.
Use a private package and the real diagnostic-worker/classification path. -/
private unsafe def diagnosticSetupQualification (repo scratch : FilePath) : IO (Array String) := do
  let project := scratch / "diagnostic-project"
  let output := project / ".lake" / "build" / "lib" / "lean"
  let compiled := project / "compiled"
  IO.FS.createDirAll output
  IO.FS.createDirAll compiled
  IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
  IO.FS.writeFile (project / "lakefile.toml") <|
    "name = \"diagnostic_control\"\n[leanOptions]\nautoImplicit = false\n" ++
      "relaxedAutoImplicit = false\nlinter.missingDocs = true\n[[lean_lib]]\nname = \
        \"SetupSentinel\"\n"
  let source := project / "SetupSentinel.lean"
  let artifact := output / "SetupSentinel.olean"
  IO.FS.writeFile source "def setupValue : Nat := 0\n"
  let build := runProcess project "lake" #["env", "lean", "-o", artifact.toString, source.toString]
  let first ← build
  if !first.succeeded then return #[s!"diagnostic setup baseline failed: {first.output}"]
  let check (body pattern : String) := do
    let text := s!"<!-- lean-fail: {pattern} -->\n```lean\n{body}```\n"
    let scan := Documentation.scan text "setup.md"
    let tasks := scan.fences.map fun fence =>
      ({ fence, origin := "setup.md:2", kind := .negative } : Documentation.Task)
    Documentation.auditTasks project compiled 1 tasks #[] #[]
  let body := "import SetupSentinel\ndef invalid : Nat := \"value\"\n"
  let mut failures := #[]
  for phase in #["baseline", "corrupt", "restored"] do
    if phase == "corrupt" then
      IO.FS.writeFile artifact "invalid serialized artifact"
    if phase == "restored" then
      let restored ← build
      if !restored.succeeded then
        failures := failures.push s!"diagnostic setup restoration failed: {restored.output}"
    let results ← check body (if phase == "corrupt" then "SetupSentinel" else "Type mismatch")
    let accepted := results.size == 1 && results.all fun result =>
      if phase == "corrupt" then
        result.status == .fail && result.detail.contains "diagnostic worker did not complete"
      else result.status == .passNegative
    if !accepted then
      failures := failures.push s!"diagnostic setup/{phase}: {repr (results.map (·.detail))}"
  -- A direct source module-mode error remains a legitimate rejection.
  let moduleResults ← check "module\nimport SetupSentinel\n" "cannot import non-"
  if moduleResults.size != 1 || !(moduleResults.all (·.status == .passNegative)) then
    failures := failures.push "diagnostic setup/module-mode: source rejection was not preserved"
  return failures

/-- Associate each expected diagnostic with its own rendered file record.
A different failing case cannot satisfy this case's expected reason. -/
private def fenceOriginOutput (output filename : String) : String := Id.run do
  let mut active := false
  let mut selected : Array String := #[]
  for line in output.splitOn "\n" do
    if line.startsWith "[" then active := line.contains s!" {filename}:"
    if line.isEmpty then active := false
    if active then selected := selected.push line
  return "\n".intercalate selected.toList

/-- The public command prints a success label only with accepted evidence, which
the failing corpus never has. A passing fence there keeps its status mark and is
labelled as observed; failing records keep their expected diagnostic. -/
private def publicExpectation (expected : String) : String :=
  match expected.splitOn " " with
  | [origin, "PASS"] => s!"[.] {origin} OBSERVED (audit incomplete)"
  | [origin, "PASS_NEG"] => s!"[n] {origin} OBSERVED (audit incomplete)"
  | [origin, "PASS_TRUSTED"] => s!"[t] {origin} OBSERVED (audit incomplete)"
  | _ => expected

/-- In-process fence-corpus qualification: the same corpus the public
`docFenceAudit` control audits end-to-end, scanned and assessed through the
checker's own `Documentation.auditTasks` batch auditor without the
clean-checkout rebuild. -/
private unsafe def fenceCorpusQualification (repo scratch : FilePath) (jobs : Nat)
    : IO (Array String) := do
  let mut tasks : Array Documentation.Task := #[]
  let mut structural : Array String := #[]
  for (name, text, _) in fenceCorpusCases repo do
    let scan := Documentation.scan text s!"{name}.md"
    structural := structural ++ scan.problems
    for fence in scan.fences do
      tasks := tasks.push {
        fence
        origin := s!"{name}.md:{fence.line}"
        kind := kindOf fence
      }
  let results ← Documentation.auditTasks repo scratch jobs tasks #[] #[]
  let mut rendered : Array String := structural.map (s!"[X] {·}")
  for result in results do
    let mark := match result.status with
      | .pass => "." | .passNegative => "n" | .passTrusted => "t" | .fail => "X"
    rendered := rendered.push s!"[{mark}] {result.task.origin} {statusName result.status}"
    if result.status == .fail then
      rendered := rendered.push s!"      {result.detail}"
  let output := "\n".intercalate rendered.toList
  let mut failures : Array String := #[]
  let mut failCount := 0
  for result in results do
    if result.status == .fail then failCount := failCount + 1
  if structural.isEmpty && failCount == 0 then
    failures := failures.push "scanner/corpus: malformed corpus unexpectedly passed"
  for (name, _, expected) in fenceCorpusCases repo do
    if !(fenceOriginOutput output s!"{name}.md").contains expected then
      failures :=
          failures.push s!"scanner/corpus/{name}: missing diagnostic {repr expected}:\n{output}"
  return failures ++ (← diagnosticSetupQualification repo scratch)

/-- End-to-end public `docFenceAudit` control over the adversarial corpus
(conditional tier: it re-runs the auditor against a clean-checkout copy). -/
private unsafe def publicScannerQualification (repo scratch : FilePath) : IO (Array String) := do
  let cases := fenceCorpusCases repo ++ publicOnlyFenceCases
  let docsRoot := scratch / "docs"
  IO.FS.createDirAll docsRoot
  for (name, text, _) in cases do
    IO.FS.writeFile (docsRoot / s!"{name}.md") text
  -- A compiled module outside every Lake workspace, reachable only through
  -- the inherited `LEAN_PATH` the public command must not pass to its workers.
  let staleDir := scratch / "stale-lean-path"
  IO.FS.createDirAll staleDir
  IO.FS.writeFile (staleDir / "StaleImport.lean") "def staleImportValue : Nat := 1\n"
  let compiled ← runProcess repo "lake" #["env", "lean", "-o",
    (staleDir / "StaleImport.olean").toString, (staleDir / "StaleImport.lean").toString]
  if !compiled.succeeded then
    return #[s!"scanner/public/stale-setup: {compiled.output}"]
  let inheritedLeanPath := (← IO.getEnv "LEAN_PATH").getD ""
  let result ← runProcess repo (repo / ".lake" / "build" / "bin" / "docFenceAudit").toString
    #["--jobs", "4", "--docs-root", docsRoot.toString]
    #[("LEAN_PATH", some (if inheritedLeanPath.isEmpty then staleDir.toString
      else s!"{staleDir}:{inheritedLeanPath}"))]
  let mut failures : Array String := #[]
  if result.succeeded then
    failures := failures.push "scanner/public: malformed corpus unexpectedly passed"
  -- A malformed marker is reported at its own file and line; it must not abort
  -- the run with a bare, unlocated failure.
  if !result.output.contains
      "[X] empty-pattern.md:1: invalid lean-fail pattern: diagnostic pattern is empty"
      || result.output.contains "FAIL: diagnostic pattern is empty" then
    failures := failures.push s!"scanner/public/located-marker: missing located malformed-marker \
      diagnostic:\n{result.output}"
  for (name, _, expected) in cases do
    if !(fenceOriginOutput result.output s!"{name}.md").contains (publicExpectation expected) then
      failures := failures.push s!"scanner/public/{name}: missing \
        diagnostic {repr (publicExpectation expected)}:\n{result.output}"
  return failures

private def expectManifestFailure (name : String) (action : IO Manifest)
    (expected : String) : IO (Option String) := do
  try
    let _ ← action
    return some s!"manifest/{name}: expected failure"
  catch error =>
    if toString error |>.contains expected then return none
    return some s!"manifest/{name}: wrong diagnostic: {error}"

private def expectManifestPublicFailure (repo : FilePath) (name : String)
    (path : FilePath) (expected : String) : IO (Option String) := do
  let result ← runBinary repo "axiomGate"
    #["--manifest", path.toString, "--incremental"]
  if result.succeeded then return some s!"manifest/public/{name}: expected failure"
  if result.output.contains expected then return none
  return some s!"manifest/public/{name}: wrong diagnostic:\n{result.output}"

/-- External manifest controls only: the real repository manifest, a missing file, and the
public `axiomGate` CLI rendering the malformed, incomplete, wrong-version, unknown-key and
bad-execution refusal classes and a Lake-inventory refusal. The pure parser is proved for every
input instead of sampled in process: `Manifest.parse_sound` and `Manifest.parse_input` for what
it accepts, `Manifest.parseValue_ok` for exactly which JSON values its value stage accepts,
`Manifest.parse_emptyExclusions` for empty exclusions, and the refusal-class
theorems (`parse_malformed`, `topLevel_emptySurfaces`, `topLevel_schemaVersion`,
`objectWithKeys_unknown`, `parseSurface_execution_refuses` and their lifts) for the
message of each of those defects. -/
private def manifestQualification (repo scratch : FilePath) : IO (Array String) := do
  let mut failures : Array String := #[]
  let valid ← Manifest.load (Manifest.defaultPath repo)
  if valid.surfaces.isEmpty then failures := failures.push "manifest/valid: no surfaces"
  if valid.excludedExecutables.isEmpty then
    failures := failures.push "manifest/valid: no excluded executables"
  let missing := scratch / "missing.json"
  if let some failure ← expectManifestFailure "missing"
      (Manifest.load missing) "manifest-missing" then
    failures := failures.push failure
  if let some failure ← expectManifestPublicFailure repo "missing" missing "manifest-missing" then
    failures := failures.push failure
  let malformed := scratch / "malformed.json"
  IO.FS.writeFile malformed "{"
  if let some failure ← expectManifestPublicFailure repo "malformed" malformed
      "manifest-malformed" then
    failures := failures.push failure
  let incomplete := scratch / "incomplete.json"
  IO.FS.writeFile incomplete
    "{\"schema-version\":2,\"surfaces\":[],\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "incomplete" incomplete
      "manifest-incomplete: surfaces must be a nonempty array" then
    failures := failures.push failure
  let wrongVersion := scratch / "wrong-version.json"
  IO.FS.writeFile wrongVersion <| "{\"schema-version\":1,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"rationale\":\"control\"}]," ++
    "\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "wrong-version" wrongVersion
      "manifest-schema: schema-version must be exactly 2" then
    failures := failures.push failure
  let unknown := scratch / "unknown.json"
  IO.FS.writeFile unknown <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"rationale\":\"control\",\"extra\":true}\
      ]," ++
    "\"excluded-libraries\":[{\"library\":\"Fixtures\",\"rationale\":\"mutations\"}]," ++
    "\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "unknown" unknown
      "manifest-schema: surfaces[0] has unknown key(s)" then
    failures := failures.push failure
  let badExecution := scratch / "bad-execution.json"
  IO.FS.writeFile badExecution <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"AuditApp\",\"claim\":\"standard-logical\",\"execution\":\"bogus\",\"rationale\":\"c\
      ontrol\"}]," ++
    "\"excluded-libraries\":[],\"excluded-executables\":[]}"
  if let some failure ← expectManifestPublicFailure repo "bad-execution" badExecution
      "manifest-schema: surfaces[0].execution must be \"report\" or \"checked\"" then
    failures := failures.push failure
  let unknownLibrary := scratch / "unknown-library.json"
  IO.FS.writeFile unknownLibrary <| "{\"schema-version\":2,\"surfaces\":[{" ++
    "\"library\":\"NoSuchLibrary\",\"claim\":\"standard-logical\",\"rationale\":\"negative\"}]," ++
    "\"excluded-libraries\":[{\"library\":\"Fixtures\",\"rationale\":\"mutations\"}," ++
    "{\"library\":\"Regula\",\"rationale\":\"checker\"}]," ++
    "\"excluded-executables\":[{\"executable\":\"axiomGate\",\"rationale\":\"tooling\"}," ++
    "{\"executable\":\"docFenceAudit\",\"rationale\":\"tooling\"}," ++
    "{\"executable\":\"freshChecker\",\"rationale\":\"tooling\"}," ++
    "{\"executable\":\"checkerSelftest\",\"rationale\":\"tooling\"}]}"
  if let some failure ← expectManifestPublicFailure repo "unknown-library" unknownLibrary
      "manifest surface missing from Lake discovery" then
    failures := failures.push failure
  return failures

private def appendFailure (failures : IO.Ref (Array String)) (value : Option String) : IO Unit :=
  if let some failure := value then failures.modify (·.push failure) else pure ()

/-- Preserve project-relative source and asset locations using the same fresh
copy operation as the public gate, rather than a second fixed source list. -/
private def prepareScratchRepo (repo scratch : FilePath) : IO Unit :=
  copyProject repo scratch scratch

private def withNewFile {α : Type} (path : FilePath) (text : String) (action : IO α) : IO α := do
  if ← path.pathExists then
    throw <| IO.userError s!"refusing to overwrite structural fixture {path}"
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path text
  try action
  finally if ← path.pathExists then IO.FS.removeFile path

private def withReplacedFile {α : Type} (path : FilePath) (text : String) (action : IO α) :
    IO α := do
  let original ← IO.FS.readFile path
  IO.FS.writeFile path text
  try action
  finally IO.FS.writeFile path original

private def withRemovedFile {α : Type} (path : FilePath) (action : IO α) : IO α := do
  let original ← IO.FS.readFile path
  IO.FS.removeFile path
  try action
  finally IO.FS.writeFile path original

private def expectedFailure (name : String) (result : ProcessResult)
    (needles : Array String) : Option String :=
  if result.succeeded then
    some s!"structural/{name}: mutation unexpectedly passed:\n{result.output}"
  else if let some missing := needles.find? fun needle => !result.output.contains needle then
    some s!"structural/{name}: missing diagnostic {repr missing}:\n{result.output}"
  else none

/-- `AuditApp` and the policy library the probe imports; every other library stays excluded. -/
private def structuralClaims : Array String := #["AuditApp", "RegulaPolicy"]

/-- Manifest claimed inside every structural copy: the actual repository manifest's
`AuditApp` surface and the `RegulaPolicy` surface, with every other actual library
and executable excluded. `RegulaPolicy` must stay claimed because the checker probe's
own imports resolve to it inside a self-hosted copy. It is derived from the actual
manifest, so `Manifest.structural_libraries` and `structural_executables` make the
classified names of this in-memory manifest exactly the actual ones.
`Manifest.structural_roundtrip` proves that the JSON value stage of the gate's `parse` recovers
this manifest exactly from `Manifest.toJson`. Its hypothesis that the copy claims an actual
surface is what the guard below checks at run time, not a theorem. Rendering with
`Json.compress` and reading with `PolicyCodec.parse` stay trusted,
as do the `auditAppVariant` rewrites. The mutations'
intended reasons are surface-content-agnostic; the
heavy-surface end-to-end coverage stays in the conditional tier's public-surface
control and the standalone CI gate. -/
private def structuralBase (repo : FilePath) : IO Manifest := do
  let actual ← Manifest.load (Manifest.defaultPath repo)
  for library in structuralClaims do
    unless actual.surfaces.any (·.library == library) do
      throw <| IO.userError s!"structural control requires the actual {library} surface"
  return Manifest.structuralManifest actual structuralClaims

private def structuralManifestText (repo : FilePath) : IO String := do
  return (Manifest.toJson (← structuralBase repo)).compress

/-- A structural manifest whose `AuditApp` surface claims exactly `executables`; the actual
`AuditApp` executables it no longer claims are excluded when `excludeApp`, and otherwise
left unclassified. -/
private def auditAppVariant (repo : FilePath) (executables : Array String) (excludeApp : Bool) :
    IO String := do
  let base ← structuralBase repo
  let released := (base.surfaces.filter (·.library == "AuditApp")).flatMap (·.executables)
    |>.filter (!executables.contains ·)
  let surfaces := base.surfaces.map fun s =>
    if s.library == "AuditApp" then { s with executables } else s
  let excludedExecutables := if excludeApp then
    base.excludedExecutables ++ released.map (⟨·, "application"⟩) else base.excludedExecutables
  return (Manifest.toJson { base with surfaces, excludedExecutables }).compress

/-- Structural mutation cluster: discovery of added modules, suppressed
warnings, and contamination of the claimed library root by excluded fixture
modules (direct and exact-prefix-lookalike). -/
private unsafe def structuralPartA (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let unchecked := "import Lean\nopen Lean Elab Command\n" ++
    "run_cmd do\n  let d := Declaration.thmDecl { name := `admissionFalse, " ++
    "levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n" ++
    "  match (← getEnv).addDeclCore 200000 1000 d none false with\n" ++
    "  | .ok env => setEnv env\n  | .error _ => throwError \"construction failed\"\n"
  withNewFile (sources / "AuditApp" / "AdmissionProbe.lean") unchecked do
    for (name, args) in #[("project-admission", #["--incremental"]),
        ("build-admission", #["--build-lint"])] do
      if let some failure := expectedFailure name (← gate args)
          #["kernel-admission", "admissionFalse"] then
        failures.modify (·.push failure)
    let imported :=
        "import AuditApp.AdmissionProbe\ntheorem importedAdmission : False := admissionFalse\n"
    withNewFile (copy / "ImportedAdmission.lean") imported do
      if let some failure := expectedFailure "file-imported-admission"
          (← gate #["--file", "ImportedAdmission.lean"])
          #["kernel-admission", "admissionFalse"] then
        failures.modify (·.push failure)
    withNewFile (copy / "admission-docs" / "example.md") ("```lean\n" ++ imported ++ "```\n") do
      if let some failure := expectedFailure "fence-imported-admission"
          (← runBinaryFrom repo copy "docFenceAudit" #["--docs-root", "admission-docs"])
          #["kernel-admission", "admissionFalse"] then
        failures.modify (·.push failure)
  withNewFile (sources / "AuditApp" / "DiscoveryAxiom.lean")
      "/-! Discovery control for an otherwise unused owned axiom. -/\n/-- An unused owned axiom, \
        which RG1001 rejects. -/\naxiom selftest_discovered_axiom : False\n" do
    if let some failure := expectedFailure "add-only-discovery" (← gate)
        #["project-axiom", "selftest_discovered_axiom"] then
      failures.modify (·.push failure)
  withNewFile (sources / "AuditApp" / "SuppressedWarning.lean")
      "set_option warningAsError false in\ndef selftest_suppressed_warning (unused : Nat) : Nat := \
        1\n" do
    -- `linter.unusedVariables` occurs only on the warning's continuation
    -- line, so the transcript must carry the whole diagnostic block.
    if let some failure := expectedFailure "warning-suppression" (← gate)
        #["build-failed", "warning", "linter.unusedVariables"] then
      failures.modify (·.push failure)
  let appRoot := sources / "AuditApp.lean"
  let originalRoot ← IO.FS.readFile appRoot
  let contaminated := originalRoot.replace "import AuditApp.Demo\n"
    "import AuditApp.Demo\nimport Fixtures.Mutations.DirectAxiom\n"
  withReplacedFile appRoot contaminated do
    if let some failure := expectedFailure "fixture-contamination" (← gate)
        #["unexpected-project-module", "Fixtures.Mutations.DirectAxiom"] then
      failures.modify (·.push failure)
  -- The probe modules are exempt from the environment-level exclusion check
  -- (the force import always brings them in); a claimed module importing the
  -- probe's report records must still be rejected as excluded-module
  -- contamination.
  let probeContaminated := originalRoot.replace "import AuditApp.Demo\n"
    "import AuditApp.Demo\nimport Regula.Report\n"
  withReplacedFile appRoot probeContaminated do
    if let some failure := expectedFailure "probe-contamination" (← gate)
        #["unexpected-project-module", "Regula.Report"] then
      failures.modify (·.push failure)
  let prefixFixture := sources / "Fixtures" / "Mutations" / "PrefixLookalike.lean"
  withNewFile prefixFixture "axiom AuditApp.lookalike_project_axiom : False\n" do
    let prefixed := originalRoot.replace "import AuditApp.Demo\n"
      "import AuditApp.Demo\nimport Fixtures.Mutations.PrefixLookalike\n"
    withReplacedFile appRoot prefixed do
      if let some failure := expectedFailure "exact-prefix-lookalike" (← gate)
          #["unexpected-project-module", "Fixtures.Mutations.PrefixLookalike"] then
        failures.modify (·.push failure)
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- Structural mutation cluster: unlisted root-owned modules, unclassified
Lake libraries and executables, claimed standalone executable roots, and
executable contamination. -/
private unsafe def structuralPartB (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let appRoot := sources / "AuditApp.lean"
  let originalRoot ← IO.FS.readFile appRoot
  -- Library-only variant of the structural manifest: the unlisted root-owned
  -- module mutation must only build the claimed library (linking the
  -- application executable would require the unlisted module's initializer,
  -- which Lake never compiled), so this control claims the `AuditApp` library
  -- and classifies the application executable as excluded.
  let libOnlyManifest := copy / "lib-only.json"
  IO.FS.writeFile libOnlyManifest (← auditAppVariant repo #[] true)
  withNewFile (sources / "AuditLookalike.lean") "axiom Attack.lookalikeAxiom : False\n" do
    let outputDir := copy / ".lake" / "build" / "lib" / "lean"
    IO.FS.createDirAll outputDir
    let compiled ← runProcess copy "lake" #["env", "lean", "-R", sources.toString, "-o",
      (outputDir / "AuditLookalike.olean").toString,
      (sources / "AuditLookalike.lean").toString]
    if !compiled.succeeded then
      failures.modify (·.push s!"structural/unlisted-root-setup: {compiled.output}")
    else
      let unlisted := originalRoot.replace "import AuditApp.Demo\n"
        "import AuditApp.Demo\nimport AuditLookalike\n"
      withReplacedFile appRoot unlisted do
        if let some failure := expectedFailure "unlisted-root-module"
            (← gate #["--manifest", libOnlyManifest.toString, "--incremental"])
            #["unexpected-project-module", "AuditLookalike"] then
          failures.modify (·.push failure)
  let lakefile := copy / "lakefile.lean"
  let originalLakefile ← IO.FS.readFile lakefile
  withNewFile (sources / "ExtraSurface.lean") "def extraSurfaceValue : Nat := 1\n" do
    withReplacedFile lakefile
        (originalLakefile ++ "\nlean_lib «ExtraSurface» where\n  roots := #[`ExtraSurface]\n") do
      if let some failure := expectedFailure "unclassified-library" (← gate)
          #["manifest-incomplete", "ExtraSurface"] then
        failures.modify (·.push failure)
  let exeDecl :=
    "\nlean_exe «selftestTool» where\n  root := `SelftestMain\n"
  let claimedManifest := copy / "claimed-exe.json"
  -- The claimed-exe controls claim only the added executable: the application
  -- executable's root `Main` already defines `main`, so a surface claiming
  -- both would collide in one environment for reasons unrelated to the
  -- mutation under test.
  let claimedManifestText ← auditAppVariant repo #["selftestTool"] true
  let claimedGate := gate #["--manifest", claimedManifest.toString, "--incremental"]
  withNewFile (sources / "SelftestMain.lean") "/-! Standalone no-effect IO entrypoint. -/\n/-- \
    Does nothing. -/\ndef main : IO Unit := pure ()\n" do
    withReplacedFile lakefile (originalLakefile ++ exeDecl) do
      if let some failure := expectedFailure "unclassified-exe" (← gate)
          #["manifest-incomplete", "selftestTool"] then
        failures.modify (·.push failure)
      IO.FS.writeFile claimedManifest claimedManifestText
      let claimed ← claimedGate
      if !claimed.succeeded then
        failures.modify (·.push
          s!"structural/claimed-exe: claimed standalone exe root did not pass:\n{claimed.output}")
      else
        let plan ← runBinaryFrom repo copy "freshChecker"
          #["--plan-only", "--manifest", claimedManifest.toString]
        if !plan.succeeded || !plan.output.contains "SelftestMain" then
          failures.modify (·.push
            s!"structural/claimed-exe-fresh: exe root missing its own fresh coverage \
              root:\n{plan.output}")
      withRemovedFile (sources / "SelftestMain.lean") do
        if let some failure := expectedFailure "claimed-exe-source-removed" (← claimedGate)
            #["lake-query-malformed", "invalid source"] then
          failures.modify (·.push failure)
  withNewFile (sources / "SelftestMain.lean")
      "import Fixtures.Mutations.DirectAxiom\n/-! Standalone import-contamination control. -/\n/-- \
        Does nothing. -/\ndef main : IO Unit := pure ()\n" do
    withReplacedFile lakefile (originalLakefile ++ exeDecl) do
      IO.FS.writeFile claimedManifest claimedManifestText
      if let some failure := expectedFailure "exe-contamination" (← claimedGate)
          #["unexpected-project-module", "Fixtures.Mutations.DirectAxiom"] then
        failures.modify (·.push failure)
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- Structural mutation cluster: omitted executable classification,
application-surface proof erasure and admission weakening. -/
private unsafe def structuralPartC (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  let appOmittedManifest := copy / "app-omitted-exe.json"
  IO.FS.writeFile appOmittedManifest (← auditAppVariant repo #[] false)
  if let some failure := expectedFailure "app-omitted-exe"
      (← gate #["--manifest", appOmittedManifest.toString, "--incremental"])
      #["manifest-incomplete", "auditApp"] then
    failures.modify (·.push failure)
  let appCore := sources / "AuditApp" / "Limiter.lean"
  let originalCore ← IO.FS.readFile appCore
  -- Change exactly one source fragment; a stale fixture is a setup failure.
  -- Every negative uses the public gate and every restoration builds fresh.
  let mutate (name before after : String) (needles : Array String) : IO Unit := do
    if (originalCore.splitOn before).length != 2 then
      failures.modify (·.push s!"structural/{name}: expected exactly one source fragment")
      return
    withReplacedFile appCore (originalCore.replace before after) do
      if let some failure := expectedFailure name (← gate) needles then
        failures.modify (·.push failure)
    let restored ← gate #[]
    if !restored.succeeded then
      failures.modify (·.push s!"structural/{name}/restored: fresh gate failed:\n{restored.output}")
  let resetProof := "/-- A reset limiter has no slots in use. -/\n" ++
    "theorem reset_inUse (l : Limiter) : (reset l).inUse = 0 := rfl\n"
  mutate "app-unproved-update" resetProof ""
    #["build-failed", "Unknown identifier", "reset_inUse"]
  mutate "app-trivial-update" resetProof
    "/-- Deliberately unrelated proof. -/\ntheorem reset_inUse : True := True.intro\n"
    #["build-failed", "Type mismatch", "reset_inUse", "∀ (l : Limiter), (reset l).inUse = 0"]
  mutate "app-weakened-update" resetProof
    ("/-- Deliberately conditional proof. -/\n" ++
      "theorem reset_inUse (l : Limiter) (_h : l.inUse = 0) : (reset l).inUse = 0 := rfl\n")
    #["build-failed", "Type mismatch", "reset_inUse", "∀ (l : Limiter), (reset l).inUse = 0"]
  mutate "app-missing-contract-field" "  reset_empty := reset_inUse\n" ""
    #["build-failed", "Fields missing", "reset_empty"]
  mutate "app-weakened-admission"
    "if _h : 0 < capacity then" "if _h : 0 ≤ capacity then"
    #["build-failed", "hpos", "0 <", "0 ≤"]
  -- Empty-exclusion acceptance is covered by adopterQualification's fresh
  -- standalone library/executable controls in both Lake formats. Reusing those
  -- avoids a second, dependency-fragile copy of the application as an adopter.
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- Structural mutation cluster: fresh-checker coverage of an added module and
the final restored-state control. -/
private unsafe def structuralPartD (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let gate (args : Array String := #["--incremental"]) :=
    runBinaryFrom repo copy "axiomGate" args
  withNewFile (sources / "AuditApp" / "UnimportedSafe.lean")
      "namespace AuditApp.UnimportedSafe\ndef value : Nat := 1\nend AuditApp.UnimportedSafe\n" do
    let plan ← runBinaryFrom repo copy "freshChecker" #["--plan-only"]
    if !plan.succeeded || !plan.output.contains "AuditApp.UnimportedSafe" then
      failures.modify
          (·.push s!"structural/fresh-coverage: added module was omitted:\n{plan.output}")
  -- Restored control in fresh mode (empty-output elaboration of the copy), so the
  -- harness's green-restore evidence covers stale-artifact freedom, not only
  -- incremental rebuilds.
  let restored ← gate #[]
  if !restored.succeeded then
    failures.modify (·.push s!"structural/restored: final fresh gate failed:\n{restored.output}")
  failures.get

/-- Each restricted-domain/universe mutation starts from its own passing source
and restores that source through a fresh public file audit. `--file` creates and
removes a separate elaboration directory for every invocation. The fixed
negative sweep additionally asserts the exact violation set. -/
private def correspondenceRestoration (layout : SourceLayout) (repo scratch : FilePath) : IO
    (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let controls := #[
    ("RepeatedCorrespondence", "Nat := _n\n", "Nat := _m\n"),
    ("OmittedCorrespondence", "Nat := m\n", "Nat := m + _n\n"),
    ("SpecializedUniverseCorrespondence", "{α : Type}", "{α : Type u}")]
  for (fixture, restricted, general) in controls do
    let negative ← IO.FS.readFile
        ((repo / layout.relativeDir) / "Fixtures" / "Mutations" / s!"{fixture}.lean")
    let positive := negative.replace restricted general
    if positive == negative then
      failures.modify (·.push s!"correspondence/{fixture}: mutation anchor missing")
      continue
    let source := scratch / s!"{fixture}.lean"
    withNewFile source positive do
      let gate := runBinary repo "axiomGate"
        #["--file", source.toString, "--claim", "standard-logical", "--execution", "checked"]
      let green ← gate
      if !green.succeeded || !green.output.contains "correspondence=checked" then
        failures.modify
            (·.push s!"correspondence/{fixture}: expected checked PASS:\n{green.output}")
      withReplacedFile source negative do
        if let some failure := expectedFailure fixture (← gate)
            #["execution-trusted-boundary", "no kernel-checked unconditional correspondence proof"]
                then
          failures.modify (·.push failure)
      let restored ← gate
      if !restored.succeeded || !restored.output.contains "correspondence=checked" then
        failures.modify
            (·.push s!"correspondence/{fixture}: fresh restored control failed:\n{restored.output}")
  failures.get

/-- Public project-surface correspondence control, the exact conditional-premise
mutation, and a fresh restored control. Only the reference body changes: the
positive reference equals the replacement by reduction; the mutation removes
that equality and leaves only a theorem requiring False. -/
private unsafe def structuralCorrespondence (layout : SourceLayout) (repo copy : FilePath) : IO
    (Array String) := do
  let sources := copy / layout.relativeDir
  let failures ← IO.mkRef (#[] : Array String)
  let lakefile := copy / "lakefile.lean"
  let originalLakefile ← IO.FS.readFile lakefile
  let manifest := copy / "foundation_manifest.json"
  let originalManifest ← IO.FS.readFile manifest
  let checkedManifest := originalManifest.replace "\"surfaces\":["
    ("\"surfaces\":[{\"library\":\"CorrespondenceControl\",\"claim\":\"standard-logical\"," ++
      "\"execution\":\"checked\",\"rationale\":\"correspondence control\"},")
  if checkedManifest == originalManifest then
      return #["correspondence/control: manifest anchor missing"]
  let negative ← IO.FS.readFile
      ((repo / layout.relativeDir) / "Fixtures" / "Mutations" / "ConditionalCorrespondence.lean")
  let positive := negative.replace "def falseReference (n : Nat) : Nat := n\n"
    "def falseReference (n : Nat) : Nat := n + 1\n"
  if positive == negative then return #["correspondence/control: mutation anchor missing"]
  let source := sources / "CorrespondenceControl.lean"
  -- Boundary evidence text is printed only in verbose mode.
  let gate := runBinaryFrom repo copy "axiomGate" #["--verbose"]
  withReplacedFile lakefile (originalLakefile ++ "\nlean_lib CorrespondenceControl\n") do
    withReplacedFile manifest checkedManifest do
      withNewFile source positive do
        let green ← gate
        if !green.succeeded || !green.output.contains "kernel-defeq" then
          failures.modify
              (·.push s!"correspondence/control: expected checked PASS:\n{green.output}")
        withReplacedFile source negative do
          if let some failure := expectedFailure "conditional-correspondence" (← gate)
              #["execution-trusted-boundary", "falseReference",
                "no kernel-checked unconditional correspondence proof"] then
            failures.modify (·.push failure)
        let restored ← gate
        if !restored.succeeded || !restored.output.contains "kernel-defeq" then
          failures.modify
              (·.push s!"correspondence/restored: fresh control failed:\n{restored.output}")
  for failure in ← correspondenceRestoration layout repo copy do
    failures.modify (·.push failure)
  failures.get

/-- Structural qualification: the mutation clusters run in parallel, each in
its own isolated project copy claiming the derived structural surfaces, so no
two concurrent Lake builds ever share a build directory. -/
private unsafe def structuralQualification (layout : SourceLayout) (repo scratch : FilePath)
    (jobs : Nat)
    : IO (Array String) := do
  let parts : Array (FilePath → FilePath → IO (Array String)) :=
    #[structuralPartA layout, structuralPartB layout, structuralPartC layout,
        structuralPartD layout, structuralCorrespondence layout,
      CompilerPaths.qualify]
  let results ← mapConcurrent (min parts.size (max 1 jobs))
    (parts.mapIdx fun index part => (index, part)) fun (index, part) => do
      let copy := scratch / s!"copy{index + 1}"
      prepareScratchRepo repo copy
      IO.FS.writeFile (copy / "foundation_manifest.json") ((← structuralManifestText repo) ++ "\n")
      let setup ← runProcess copy "lake"
        #["build", "AuditApp", "auditApp", "Fixtures.Mutations.DirectAxiom"]
      if !setup.succeeded then
        return #[s!"structural/setup: copy{index + 1} baseline did not build:\n{setup.output}"]
      part repo copy
  return results.foldl (· ++ ·) #[]

/-- Flush phase boundaries so CI timestamps and elapsed times identify the
actual work, even when stdout is redirected. Timings are observations only. -/
private def timedPhase {α : Type} (label : String) (action : IO α) : IO α := do
  IO.println s!"phase {label}: start"
  (← IO.getStdout).flush
  let started ← IO.monoNanosNow
  try action finally
    IO.println s!"phase {label}: {((← IO.monoNanosNow) - started) / 1000000}ms"
    (← IO.getStdout).flush

/-- Two mutually independent modules, so the fresh control has two maximal roots. -/
private def freshControlStems : Array String := #["Left", "Right"]

/-- The fresh control claims only `FreshControl`; every repository library and
executable is excluded, so the classification stays complete as they change. -/
private def freshControlManifest (manifest : Manifest) : Json :=
  let excluded (kind : String) (names : Array String) := Json.arr <| names.map fun name =>
    Json.mkObj [(kind, .str name), ("rationale", .str "outside the fresh-checker control")]
  Json.mkObj [
    ("schema-version", (2 : Nat)),
    ("surfaces", Json.arr #[Json.mkObj [("library", .str "FreshControl"),
      ("claim", .str "kernel-only"), ("rationale", .str "clean-checkout freshChecker control")]]),
    ("excluded-libraries", excluded "library" <|
      manifest.surfaces.map (·.library) ++ manifest.excludedLibraries.map (·.library)),
    ("excluded-executables", excluded "executable" <|
      manifest.surfaces.flatMap (·.executables) ++ manifest.excludedExecutables.map (·.executable))]

/-- Clean-checkout environment controls: each public checker that builds
project-owned modules must itself build the claimed libraries when the main
build directory is empty, instead of relying on a prior `lake build`. Each
control starts from a copied repository with no `.lake/build` at all. -/
private unsafe def fenceEnvironmentQualification (layout : SourceLayout) (repo scratch : FilePath) :
    IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let runScrubbed (dir : FilePath) (name : String) (args : Array String) : IO ProcessResult :=
    runProcess dir (repo / ".lake" / "build" / "bin" / name).toString args
      scrubbedLeanPathEnv
  let unbuilt (name : String) (action : FilePath → IO Unit) : IO Unit := do
    let dir := scratch / name
    IO.FS.createDirAll dir
    prepareScratchRepo repo dir
    if ← (dir / ".lake" / "build").pathExists then
      failures.modify (·.push s!"fence-env/{name}: setup unexpectedly has a build directory")
    action dir
  timedPhase "clean-checkout/doc-fences" <| unbuilt "doc-fences" fun dir => do
    let corpus := dir / "fence-corpus"
    IO.FS.createDirAll corpus
    IO.FS.writeFile (corpus / "owned-import.md")
      "```lean\nimport AuditApp.Limiter\n\ntheorem fence_uses_owned : 1 = 1 := rfl\n```\n"
    let result ← runScrubbed dir "docFenceAudit"
      #["--jobs", "4", "--docs-root", corpus.toString]
    if !result.succeeded || !result.output.contains "conforming-positive-pass=1/1" then
      failures.modify (·.push
        s!"fence-env/doc-fences: fence importing an owned module failed from unbuilt \
          state:\n{result.output}")
  timedPhase "clean-checkout/file-mode" <| unbuilt "file-mode" fun dir => do
    let result ← runScrubbed dir "axiomGate"
      #["--file",
          ((dir / layout.relativeDir) / "Fixtures" / "Positive" / "ExternalUse.lean").toString,
        "--claim", "standard-logical"]
    if !result.succeeded then
      failures.modify (·.push
        s!"fence-env/file-mode: --file importing the owned library failed from unbuilt \
          state:\n{result.output}")
  -- The driver's build and root selection depend only on the manifest and Lake's
  -- import graph, never on which declarations a module holds. So this control
  -- claims two import-free `prelude` modules instead of the repository surface:
  -- `leanchecker --fresh` on the real claimed graph replays Init, Lean and
  -- Mathlib once per root, which is the separate optional serialized-graph
  -- claim (`scripts/verify.sh serialized-graph`), not a clean-checkout property.
  timedPhase "clean-checkout/fresh-checker" <| unbuilt "fresh-checker" fun dir => do
    let sources := dir / layout.relativeDir
    let expected := freshControlStems.map (s!"FreshControl.{·}")
    IO.FS.createDirAll (sources / "FreshControl")
    for stem in freshControlStems do
      IO.FS.writeFile ((sources / "FreshControl") / s!"{stem}.lean")
        s!"prelude\n/-! Import-free clean-checkout freshChecker root. -/\n/-- A type with one \
          value. -/\ninductive FreshControl.{stem} : Type where\n  /-- Its one value. -/\n  | \
          unit\n"
    let lakefile := dir / "lakefile.lean"
    IO.FS.writeFile lakefile ((← IO.FS.readFile lakefile) ++
      "\nlean_lib FreshControl where\n  globs := #[.submodules `FreshControl]\n")
    let manifest := dir / "foundation_manifest.json"
    writeJson manifest (freshControlManifest (← Manifest.load manifest))
    let reportPath := dir / "fresh-report.json"
    let result ← runScrubbed dir "freshChecker" #["--json-out", reportPath.toString]
    if !result.succeeded then
      failures.modify (·.push
        s!"fence-env/fresh-checker: freshChecker failed from unbuilt state:\n{result.output}")
    else
      -- Reconcile the actual run against the modules written above: each is a
      -- maximal root, and every root's successful check must cover it.
      let report ← readJson reportPath
      let status ← IO.ofExcept <| report.getObjValAs? String "status"
      let modules ← jsonStringArray "fresh control modules" <| ← IO.ofExcept <|
        report.getObjVal? "modules"
      let roots ← jsonStringArray "fresh control roots" <| ← IO.ofExcept <|
        report.getObjVal? "roots"
      let checks ← IO.ofExcept <| report.getObjValAs? (Array Json) "checks"
      let mut checked : Array String := #[]
      for check in checks do
        let exitCode ← IO.ofExcept <| check.getObjValAs? Nat "exitCode"
        if exitCode != 0 then
          failures.modify (·.push "fence-env/fresh-checker: a root was not checked successfully")
        let covered ← jsonStringArray "fresh control coveredModules" <| ← IO.ofExcept <|
          check.getObjVal? "coveredModules"
        checked := checked ++ covered
      if status != "completed" || checks.size != expected.size
          || uniqueSorted modules != uniqueSorted expected || uniqueSorted roots !=
              uniqueSorted expected
          || uniqueSorted checked != uniqueSorted expected then
        failures.modify (·.push
          s!"fence-env/fresh-checker: accepted root checks did not cover \
            exactly {expected}:\n{result.output}")
  failures.get

private def adopterManifestText : String :=
  "{\"schema-version\":2,\"surfaces\":[{" ++
  "\"library\":\"Widget\",\"executables\":[\"widget_tool\"]," ++
  "\"claim\":\"choice-free\",\"rationale\":\"external adopter control\"}]," ++
  "\"excluded-libraries\":[],\"excluded-executables\":[]}"

private def adopterOmittedExeText : String :=
  "{\"schema-version\":2,\"surfaces\":[{" ++
  "\"library\":\"Widget\",\"claim\":\"choice-free\"," ++
  "\"rationale\":\"omitted executable control\"}]," ++
  "\"excluded-libraries\":[],\"excluded-executables\":[]}"

private def adopterTomlLakefile (checkerPath : String) : String :=
  "name = \"widget_adopter\"\n\n" ++
  "[leanOptions]\nautoImplicit = false\nrelaxedAutoImplicit = false\nlinter.missingDocs = \
    true\n\n" ++
  "[[require]]\nname = \"regula\"\n" ++
  s!"path = \"{checkerPath}\"\n\n" ++
  "[[lean_lib]]\nname = \"Widget\"\nglobs = [\"Widget\", \"Widget.+\"]\n\n" ++
  "[[lean_exe]]\nname = \"widget_tool\"\nroot = \"Main\"\n"

private def adopterLeanLakefile (checkerPath : String) : String :=
  "import Lake\nopen Lake DSL\n\n" ++
  "package «widget_adopter» where\n" ++
  "  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩, ⟨`linter.missingDocs, \
    true⟩]\n\n" ++
  s!"require «regula» from \"{checkerPath}\"\n\n" ++
  "@[default_target]\nlean_lib «Widget» where\n  globs := #[.andSubmodules `Widget]\n\n" ++
  "lean_exe «widget_tool» where\n  root := `Main\n"

/-- The adopting workspace inherits every transitive dependency through the
checker package's own `require`, pinned exactly as in this repository. -/
private def adopterLakeManifest (repo : FilePath) (checkerDir : String) : IO Json := do
  let base ← readJson (repo / "lake-manifest.json")
  let .arr packages ← IO.ofExcept (base.getObjVal? "packages")
    | throw <| IO.userError "adopter manifest setup: no packages array"
  let inherited := packages.map fun entry =>
    entry.setObjVal! "inherited" (Json.bool true)
  let pathEntry := Json.mkObj [
    ("name", Json.str "regula"),
    ("scope", Json.str ""),
    ("configFile", Json.str "lakefile.lean"),
    ("manifestFile", Json.str "lake-manifest.json"),
    ("inherited", Json.bool false),
    ("type", Json.str "path"),
    ("dir", Json.str checkerDir)
  ]
  return base.setObjVal! "packages" (Json.arr (#[pathEntry] ++ inherited))

/-- External adopter qualification: a scratch project that requires the
checker package by local path in each lakefile format, with one conforming
library, a standalone `Main` executable root, and empty exclusion arrays. The
scratch projects contain nothing named `Audit` or `Fixtures` and share only
the pinned dependency checkouts. The `relative` variant requires the checker
by a relative path (the form a project nested inside another repository
uses), which the §8.3 isolated copy must re-anchor to the original project;
its setup verifies that the relative path really names this repository. -/
private unsafe def adopterQualification (repo scratch : FilePath) : IO (Array String) := do
  let failures ← IO.mkRef (#[] : Array String)
  let depth := (← IO.FS.realPath scratch).components.length + 1 -
    (← IO.FS.realPath repo).components.length
  let variants : Array (String × String × String × (String → String)) := #[
    ("toml", "toml", repo.toString, adopterTomlLakefile),
    ("lean", "lean", repo.toString, adopterLeanLakefile),
    ("relative", "toml", "/".intercalate (List.replicate depth ".."), adopterTomlLakefile)
  ]
  for (label, format, checkerDir, lakefileText) in variants do
    let adopter := scratch / label
    IO.FS.createDirAll (adopter / "Widget")
    if !(FilePath.mk checkerDir).isAbsolute then
      let resolved ← IO.FS.realPath (adopter / checkerDir)
      if resolved != (← IO.FS.realPath repo) then
        throw <| IO.userError <|
          s!"adopter/{label}/setup: relative checker path {checkerDir} resolves to {resolved}, \
            not {repo}"
    let lakeManifest ← adopterLakeManifest repo checkerDir
    IO.FS.writeFile (adopter / s!"lakefile.{format}") (lakefileText checkerDir)
    IO.FS.writeBinFile (adopter / "lean-toolchain")
      (← IO.FS.readBinFile (repo / "lean-toolchain"))
    IO.FS.writeFile
        (adopter / "Widget.lean")
            "import Widget.Extra\n/-! Re-export the arithmetic identity in Widget.Extra. -/\n"
    IO.FS.writeFile (adopter / "Widget" / "Extra.lean")
      "/-! Closed natural-number arithmetic identity. -/\ntheorem widget_extra_thm : 1 + 1 = 2 := \
        rfl\n"
    IO.FS.writeFile (adopter / "Main.lean") "/-! Standalone no-effect IO entrypoint. -/\n/-- Does \
      nothing. -/\ndef main : IO Unit := pure ()\n"
    IO.FS.writeFile (adopter / "foundation_manifest.json") (adopterManifestText ++ "\n")
    writeJson (adopter / "lake-manifest.json") lakeManifest
    IO.FS.createDirAll (adopter / ".lake")
    let link ← runProcess adopter "ln" #["-s", (repo / ".lake" / "packages").toString,
      (adopter / ".lake" / "packages").toString]
    if !link.succeeded then
      throw <| IO.userError s!"could not link pinned Lake packages: {link.output}"
    let gate (args : Array String := #[]) :=
      runBinaryFrom repo adopter "axiomGate" args
    let positive ← gate #["--verbose"]
    if !positive.succeeded then
      failures.modify (·.push
        s!"adopter/{label}/positive: fresh gate failed:\n{positive.output}")
    else
      for needle in #["module Widget.Extra", "module Main", "widget_extra_thm",
          "-> kernel-only", "claimed profile for Widget: choice-free"] do
        if !positive.output.contains needle then
          failures.modify (·.push
            s!"adopter/{label}/positive: missing classification {repr needle}:\n{positive.output}")
    let viaProject ← runBinary repo "axiomGate" #["--project", adopter.toString]
    if !viaProject.succeeded then
      failures.modify (·.push
        s!"adopter/{label}/project-flag: gate from foreign cwd failed:\n{viaProject.output}")
    let omittedManifest := adopter / "omitted-exe.json"
    IO.FS.writeFile omittedManifest (adopterOmittedExeText ++ "\n")
    if let some failure := expectedFailure s!"adopter/{label}/omitted-exe"
        (← gate #["--manifest", omittedManifest.toString, "--incremental"])
        #["manifest-incomplete", "widget_tool"] then
      failures.modify (·.push failure)
    withNewFile (adopter / "Widget" / "Rogue.lean")
        "/-! Discovery control for a glob-owned axiom. -/\n/-- A glob-owned axiom, which RG1001 \
          rejects. -/\naxiom widget_rogue_axiom : False\n" do
      if let some failure := expectedFailure s!"adopter/{label}/rogue-module" (← gate)
          #["project-axiom", "widget_rogue_axiom"] then
        failures.modify (·.push failure)
    if label == "toml" then
      let originalExtra ← IO.FS.readFile (adopter / "Widget" / "Extra.lean")
      let unlistedSource := adopter / "WidgetRogue.lean"
      IO.FS.writeFile unlistedSource "axiom widget_unlisted_axiom : False\n"
      let outDir := adopter / ".lake" / "build" / "lib" / "lean"
      IO.FS.createDirAll outDir
      let compiled ← runProcess adopter "lake" #["env", "lean", "-o",
        (outDir / "WidgetRogue.olean").toString, unlistedSource.toString]
      if !compiled.succeeded then
        failures.modify (·.push s!"adopter/toml/unlisted-setup: {compiled.output}")
      else
        withReplacedFile (adopter / "Widget" / "Extra.lean")
            ("import WidgetRogue\n" ++ originalExtra) do
          if let some failure := expectedFailure "adopter/toml/unlisted-module"
              (← gate #["--incremental"])
              #["unexpected-project-module", "WidgetRogue"] then
            failures.modify (·.push failure)
      let fresh ← runBinaryFrom repo adopter "freshChecker" #["--plan-only"]
      if !fresh.succeeded || !fresh.output.contains "Widget" || !fresh.output.contains "Main" then
        failures.modify (·.push
          s!"adopter/toml/fresh-plan: exact adopter coverage plan failed:\n{fresh.output}")
  failures.get

/-- In-process fixture, scanner, and fence-corpus controls. Imports
remain serialized, and transcript workers finish before parent imports. -/
private unsafe def runFixtures (repo : FilePath) (jobs : Nat)
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit := do
  let inventory ← Lake.surfaceInventory repo
  withScratch repo "checker-fixtures" fun scratch => do
    let fixtureResults ← timedPhase "in-process fixtures" <|
      fixtureVerdicts repo scratch jobs fixtures inventory.leanPath
    for result in fixtureResults do appendFailure failures result
    IO.println (s!"self-test fixtures: " ++
      (if fixtureResults.all (·.isNone) then "PASS" else "FAIL") ++
      s!" ({fixtures.size} in one process, one environment load per import closure)")
  for failure in scannerQualification do failures.modify (·.push failure)
  withScratch repo "checker-fence-corpus" fun scratch => do
    let corpus ← timedPhase "in-process fence corpus" <|
      fenceCorpusQualification repo scratch jobs
    for failure in corpus do failures.modify (·.push failure)
    IO.println <| "self-test Markdown: " ++
      (if corpus.isEmpty then "PASS" else "FAIL") ++
      s!" (scanner controls + {(fenceCorpusCases repo).size} in-process corpus cases)"

/-- Structural/compiler-path mutations and manifest controls retain their
isolated copies, task joins, and complete failure accumulation. -/
private unsafe def runStructural (layout : SourceLayout) (repo : FilePath) (jobs : Nat)
    (failures : IO.Ref (Array String)) : IO Unit := do
  let structuralTask ← IO.asTask (prio := .dedicated) do
    timedPhase "structural controls" <| withScratch repo "checker-structural" fun scratch =>
      structuralQualification layout repo scratch jobs
  let manifestTask ← IO.asTask (prio := .dedicated) do
    timedPhase "manifest controls" <| withScratch repo "checker-manifest" fun scratch =>
      manifestQualification repo scratch
  for failure in ← IO.ofExcept (← IO.wait manifestTask) do failures.modify (·.push failure)
  IO.println "self-test manifest: completed (valid + missing in-process; missing, malformed, \
    incomplete, wrong-version, unknown-key, bad-execution and unknown-library public cases)"
  let structural ← IO.ofExcept (← IO.wait structuralTask)
  for failure in structural do failures.modify (·.push failure)
  IO.println <| "self-test structural: " ++
    (if structural.isEmpty then "PASS" else "FAIL") ++
    " (discovery, warning, contamination, exact ownership, unlisted root module, " ++
    "library and exe classification, claimed exe root, exe contamination, app exe omission, " ++
    "app missing/trivial/weakened update evidence, missing proof field, weakened admission, " ++
    "fresh coverage, conditional correspondence, restore; " ++
    "isolated copies, bounded parallelism)"

/-- Public CLI fixtures: the complete sweep for qualification, or the unchanged
smoke subset for the default development tier. -/
private def runCli (repo : FilePath) (jobs : Nat) (fullCli : Bool)
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit := do
  let smokeFixtures := fixtures.filter (smokeFixtureNames.contains ·.moduleName)
  if smokeFixtures.size != smokeFixtureNames.size then
    failures.modify (·.push "smoke: expected smoke fixtures are missing from the manifest")
  -- The build-bound sweep contains every smoke control; each runs once.
  let cliFixtures := if fullCli then fixtures else smokeFixtures
  let cliLabel := if fullCli then "full CLI sweep" else "CLI smoke"
  let cliResults ← timedPhase cliLabel <|
    mapConcurrent jobs cliFixtures (checkFixtureCli repo)
  for result in cliResults do appendFailure failures result
  IO.println <| s!"self-test {cliLabel}: " ++
    (if cliResults.all (·.isNone) then "PASS" else "FAIL") ++
    s!" ({cliFixtures.size} real axiomGate --file invocations)"

/-- Build-bound packaging and fresh-state controls, each retaining its isolated
source/build directory and exact failure accumulation. -/
private unsafe def runEnvironments (layout : SourceLayout) (repo : FilePath)
    (failures : IO.Ref (Array String)) : IO Unit := do
  -- This tier only starts after the earlier subprocess tasks have joined.
  -- Its builds live in isolated copies; the other public controls cannot
  -- consume or alter those owned outputs.
  let fenceEnvTask ← IO.asTask (prio := .dedicated) do
    timedPhase "clean-checkout environments" <|
      withScratch repo "checker-fence-env" fun scratch =>
        fenceEnvironmentQualification layout repo scratch
  withScratch repo "checker-scanner" fun scratch => do
    for failure in ← timedPhase "public fence corpus" (publicScannerQualification repo scratch) do
      failures.modify (·.push failure)
  IO.println s!"self-test public fence corpus: completed \
    ({(fenceCorpusCases repo ++ publicOnlyFenceCases).size} end-to-end cases)"
  withScratch repo "checker-adopter" fun scratch => do
    let adopter ← timedPhase "external adopters" (adopterQualification repo scratch)
    for failure in adopter do failures.modify (·.push failure)
    IO.println <| "self-test external adopters: " ++
      (if adopter.isEmpty then "PASS" else "FAIL") ++
      " (lakefile.toml + lakefile.lean + relative-path require: empty exclusions, fresh positive \
        gate, --project, omitted exe, " ++
      "rogue module, unlisted-module contamination, fresh plan)"
  let fenceEnv ← IO.ofExcept (← IO.wait fenceEnvTask)
  for failure in fenceEnv do failures.modify (·.push failure)
  IO.println <| "self-test fence environment: " ++
    (if fenceEnv.isEmpty then "PASS" else "FAIL") ++
    " (clean-checkout doc fences, --file, freshChecker with no prior build on a two-root control \
      surface)"
  let surface ← timedPhase "public surface" <| runBinary repo "axiomGate" #["--incremental"]
  if !surface.succeeded then
    failures.modify (·.push s!"surface/baseline: public incremental gate failed:\n{surface.output}")
  IO.println "self-test public controls: completed (surface)"

/-- Ordinary-build controls are a separate required partition so they do not
share the clean-checkout environment controls' CI time budget. -/
private def runBuildPolicy (repo : FilePath) (jobs : Nat)
    (failures : IO.Ref (Array String)) : IO Unit := do
  withScratch repo "checker-build-lint" fun scratch => do
    let buildLint ← timedPhase "ordinary-build policy controls" <|
      BuildLintQualification.qualify repo scratch jobs
    for failure in buildLint do failures.modify (·.push failure)
    IO.println <| "self-test build policy linter: " ++
      (if buildLint.isEmpty then "PASS" else "FAIL")

/-- `lake lint` driver controls: Lake dispatch in both lakefile formats and exit classes.
The shared audit body's detectors are qualified by the build-policy partition. -/
private def runLintDriver (repo : FilePath) (jobs : Nat)
    (failures : IO.Ref (Array String)) : IO Unit := do
  withScratch repo "checker-lake-lint" fun scratch => do
    let lint ← timedPhase "lake lint driver controls" <|
      LintQualification.qualify repo scratch jobs
    for failure in lint do failures.modify (·.push failure)
    IO.println <| "self-test lake lint driver: " ++ (if lint.isEmpty then "PASS" else "FAIL")

/-- Full and selected runs use the same group implementations. This exhaustive
match assigns each supported partition exactly one implementation. -/
private unsafe def runPartition (layout : SourceLayout) (partition : Partition) (repo : FilePath)
    (jobs : Nat)
    (fixtures : Array FixtureSpec) (failures : IO.Ref (Array String)) : IO Unit :=
  match partition with
  | .fixtures => runFixtures repo jobs fixtures failures
  | .structural => runStructural layout repo jobs failures
  | .cli => runCli repo jobs true fixtures failures
  | .environments => runEnvironments layout repo failures
  | .buildPolicy => runBuildPolicy repo jobs failures
  | .lintDriver => runLintDriver repo jobs failures

/-- The combined public command must preserve Markdown discovery even in
subdirectories pruned by the generic project copier. Exercise a fresh positive,
a single invalid fence, and its restored positive in an isolated tiny project. -/
private def combinedSnapshotQualification (repo : FilePath) : IO (Array String) :=
  withScratch repo "combined-snapshot-control" fun project => do
    IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile (repo / "lean-toolchain"))
    IO.FS.writeFile (project / "lakefile.toml") <|
      "name = \"snapshot_control\"\n[leanOptions]\nautoImplicit = false\n" ++
        "relaxedAutoImplicit = false\nlinter.missingDocs = true\n[[lean_lib]]\nname = \
          \"Snapshot\"\n" ++
        "[[lean_lib]]\nname = \"Companion\"\n"
    IO.FS.writeFile (Manifest.defaultPath project)
      "{\"schema-version\":2,\"surfaces\":[{\"library\":\"Snapshot\",\"executables\":[],\"claim\":\
        \"standard-logical\",\"execution\":\"report\",\"rationale\":\"Control\"},{\"library\":\"Com\
        panion\",\"executables\":[],\"claim\":\"standard-logical\",\"execution\":\"report\",\"ratio\
        nale\":\"Parallel surface \
        control\"}],\"excluded-libraries\":[],\"excluded-executables\":[]}"
    let docs := project / "docs" / ".cache"
    IO.FS.createDirAll docs
    let mut failures := #[]
    for phase in
        #["baseline", "invalid", "restored", "invalid-source", "invalid-companion",
            "source-restored"] do
      IO.FS.writeFile (project / "Snapshot.lean") <|
        "/-! Source used for fence-import isolation qualification. -/\n" ++
        (if phase == "invalid-source" then "axiom unproved : True\n"
        else "theorem snapshot_ok : True := True.intro\n")
      IO.FS.writeFile (project / "Companion.lean") <|
        "/-! Companion surface for fence-import isolation qualification. -/\n" ++
        (if phase == "invalid-companion" then "axiom companion_unproved : True\n"
        else "theorem companion_ok : True := True.intro\n")
      let body := if phase == "invalid" then "def docWitness : Nat := \"bad\""
        else "theorem docWitness : True := True.intro"
      IO.FS.writeFile (docs / "sentinel.md") s!"```lean\n{body}\n```\n"
      let result ← runProcess project (repo / ".lake/build/bin/axiomGate").toString
        #["--project", project.toString, "--with-docs", "--verbose"] scrubbedLeanPathEnv
      let accepted := if phase == "invalid" then
          !result.succeeded && result.output.contains "[X] .cache/sentinel.md:"
            && result.output.contains "Type mismatch"
        else if phase == "invalid-source" || phase == "invalid-companion" then
          !result.succeeded && result.output.contains "project-axiom"
            && !(result.output.contains "fence compilation: start")
        else result.succeeded && result.output.contains "conforming-positive-pass=1/1"
      if !accepted then failures := failures.push s!"combined snapshot/{phase}: {result.output}"
    return failures

/-- Distinguish the canonical force-loaded collector from a real import of an
excluded root-library module, through the public fresh project entry point. -/
private def forcedCollectorQualification (repo scratch : FilePath) : IO (Array String) := do
  let layout ← loadSourceLayout repo
  prepareScratchRepo repo scratch
  -- Retain the complete original manifest, including pure-policy dependencies.
  -- Excluding them would reject the positive for an unrelated import reason.
  let root := scratch / layout.relativeDir / "AuditApp.lean"
  let source ← IO.FS.readFile root
  let invoke := runBinaryFrom repo scratch "axiomGate" #[]
  let positive ← invoke
  unless positive.succeeded do return #[s!"forced-collector-positive: {positive.output}"]
  IO.FS.writeFile root ("import Regula.Collect\n" ++ source)
  let negative ← invoke
  IO.FS.writeFile root source
  let restored ← invoke
  let mut failures := #[]
  if let some failure := expectedFailure "source-imported-excluded-collector" negative
      #["unexpected-project-module", "excluded module Regula.Collect"] then
    failures := failures.push failure
  unless restored.succeeded do failures :=
                                failures.push s!"forced-collector-restored: {restored.output}"
  return failures

/-- Runs the qualification suite: one of the focused `--…-only` controls or the internal
transcript worker when the arguments name it, otherwise the baseline build and then the
selected tiers or partition. Prints each failure and returns `1` when any control fails, `0`
otherwise. -/
unsafe def run (args : List String) : IO UInt32 := do
  if args == ["--forced-collector-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "forced-collector-control" (forcedCollectorQualification repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
        IO.println "forced collector qualification: PASS (fresh positive, excluded-source refusal, \
          restored)"
    return if failures.isEmpty then 0 else 1
  if args == ["--policy-transport-only"] then
    let failures := PolicyQualification.transport
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then IO.println "policy transport qualification: PASS"
    return if failures.isEmpty then 0 else 1
  if args == ["--native-adopter-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate", "Regula.Linter"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "native-adopter-control" (PolicyQualification.nativeImport repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    return if failures.isEmpty then 0 else 1
  if args == ["--policy-domain-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    let failures ← withScratch repo "policy-domain-controls" fun scratch => do
      return PolicyQualification.transport ++ (← PolicyQualification.publicPaths repo scratch)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
        IO.println "policy domain qualification: PASS (transport and public paths)"
    return if failures.isEmpty then 0 else 1
  if args == ["--combined-snapshot-only"] then
    let failures ← combinedSnapshotQualification (← repoRoot)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then IO.println "combined snapshot qualification: PASS"
    return if failures.isEmpty then 0 else 1
  if args == ["--fences-only"] then
    let repo ← repoRoot
    let inProcess ← withScratch repo "checker-focused-fences" fun scratch =>
      fenceCorpusQualification repo scratch 4
    let publicCases ← withScratch repo "checker-focused-public-fences" fun scratch =>
      publicScannerQualification repo scratch
    let failures := inProcess ++ publicCases ++ (← combinedSnapshotQualification repo)
    for failure in failures do IO.println s!"FAIL: {failure}"
    if failures.isEmpty then
      IO.println "focused fence qualification: PASS (in-process, import setup/restoration, public \
        corpus; not full qualification)"
    return if failures.isEmpty then 0 else 1
  if args == ["--build-lint-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    return ← withScratch repo "build-lint-controls" fun scratch => do
      let failures ← BuildLintQualification.qualify repo scratch 4
      for failure in failures do IO.println s!"FAIL: {failure}"
      if failures.isEmpty then IO.println "build policy linter qualification: PASS"
      return if failures.isEmpty then 0 else 1
  if args == ["--compiler-paths-only"] then
    let repo ← repoRoot
    let build ← runProcess repo "lake" #["build", "axiomGate"]
    if !build.succeeded then IO.println build.output; return 1
    return ← withScratch repo "compiler-path-controls" fun scratch => do
      let failures ← CompilerPaths.qualify repo scratch
      for failure in failures do IO.println s!"FAIL: {failure}"
      return if failures.isEmpty then 0 else 1
  -- Internal transcript worker: one isolated fresh-frontend re-elaboration
  -- with the checker's own pinned frontend, serialized as JSON. The batched
  -- fixture pipeline spawns these so every transcript is built in exactly the
  -- isolated process environment the public CLI provides (a fresh process can
  -- never see the harness's imported attribute state), before the parent
  -- shared environment load.
  if let ["--transcript-worker", moduleWire, source, out] := args then
    let moduleName ← IO.ofExcept <| Regula.RegistryCodec.parseName
        (← IO.ofExcept <| Regula.Checker.PolicyCodec.parse moduleWire)
    let transcript ← Frontend.buildCurrentSearchPath moduleName source
    writeJson out
        (workerPacket (sourceWorkerRequest "transcript" moduleName source transcript.sourceContent)
            (toJson transcript))
    return 0
  let options ← parseArgs args {}
  if options.help then IO.println usage; return 0
  if options.jobs == 0 then throw <| IO.userError "--jobs must be positive"
  let repo ← repoRoot
  let started ← IO.monoNanosNow
  let failures ← IO.mkRef (#[] : Array String)
  -- One baseline build pays the invariant prefix once: the checker
  -- executables, the fixture import anchor, and the claimed positive surface
  -- (fixture sources import the owned library, e.g. `import AuditApp`), so every
  -- later phase sees an already-warm build.
  let surfaceManifest ← Manifest.load (Manifest.defaultPath repo)
  let build ← timedPhase "baseline build" <| runProcess repo "lake"
    (#["build", "axiomGate", "lint", "docFenceAudit", "freshChecker",
        "Fixtures.Mutations.DirectAxiom"]
      ++ Manifest.positiveTargets surfaceManifest)
  if !build.succeeded then
    IO.println s!"FAIL: baseline checker and claimed-surface build failed:\n{build.output}"
    return 1
  let layout ← loadSourceLayout repo
  if options.structuralOnly then
    return ← withScratch repo "checker-structural" fun scratch => do
      let structural ← structuralQualification layout repo scratch options.jobs
      if structural.isEmpty then
        IO.println s!"checker structural self-test: PASS (including {CompilerPaths.caseCount} \
          compiler-path mutations with fresh restorations)"
        return 0
      IO.println s!"FAIL: {structural.size} structural qualification failure(s)"
      for failure in structural do IO.println s!"\n{failure}"
      return 1
  let fixtures ← loadFixtureManifest layout repo
  match options.partition with
  | some partition => runPartition layout partition repo options.jobs fixtures failures
  | none =>
    if options.buildBound then
      for partition in Partition.all do
        runPartition layout partition repo options.jobs fixtures failures
    else
      runFixtures repo options.jobs fixtures failures
      runStructural layout repo options.jobs failures
      runCli repo options.jobs false fixtures failures
  let failures ← failures.get
  if !failures.isEmpty then
    IO.println s!"FAIL: {failures.size} checker qualification failure(s)"
    for failure in failures do IO.println s!"\n{failure}"
    return 1
  let elapsed := (← IO.monoNanosNow) - started
  if let some partition := options.partition then
    IO.println s!"checker self-test partition {partition.label}: PASS ({elapsed / 1000000000}s; \
      this partition alone is not full qualification)"
    return 0
  IO.println <| s!"checker self-test: PASS ({fixtures.size} fixed fixtures in-process; " ++
    (if options.buildBound then
        s!"{fixtures.size} real-CLI controls (including all smoke controls); "
      else s!"{smokeFixtureNames.size} real-CLI smoke controls; ") ++
    s!"{(fenceCorpusCases repo).size + publicOnlyFenceCases.size} Markdown cases plus import-setup \
      controls; 9 manifest cases; structural controls including explicit contract mutations; " ++
    s!"{CompilerPaths.caseCount} imported compiler-path mutations with fresh restorations; " ++
    (if options.buildBound then
      "build-bound tier: full real-CLI fixture sweep, end-to-end fence corpus, " ++
      "external adopter controls in both lakefile formats, " ++
      "clean-checkout fence environment controls, public surface and fresh-plan controls; "
    else "") ++
    s!"{elapsed / 1000000000}s)"
  return 0

end Regula.Checker.CheckerSelftest

/-- The `checkerSelftest` executable: initializes Lean's search path, enables initializer
execution and runs `Regula.Checker.CheckerSelftest.run`, printing any exception as `FAIL:` and
returning `1`. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Lean.enableInitializersExecution
    Regula.Checker.CheckerSelftest.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
