import Regula.Checker.Acceptance
import Regula.Checker.ResultProtocol

/-!
# Serialized-environment qualification

Optional serialized-environment qualification. This is separate from ordinary
kernel elaboration and declaration-policy conformance.
-/

namespace Regula.Checker.FreshChecker

open Lean System
open Regula.Checker

/-- The modules one manifest surface claims: its library's Lake modules and its executables'
roots. -/
structure ModuleSet where
  /-- The surface's library name, as in `foundation_manifest.json`. -/
  library : String
  /-- The library's Lake-resolved modules, then the root module of each claimed executable. -/
  modules : Array String
  deriving Repr

/-- The claimed modules one fresh `leanchecker` root covers. -/
structure Coverage where
  /-- The root module passed to `lake env leanchecker --fresh`. -/
  root : String
  /-- The root and its transitive imports that are claimed modules, sorted and without
  duplicates. -/
  modules : Array String
  deriving Repr

/-- The serialized-graph checking plan over every claimed module of the manifest. -/
structure Plan where
  /-- The claimed modules of each manifest surface, in manifest order. -/
  moduleSets : Array ModuleSet
  /-- Every claimed module, sorted and without duplicates. -/
  modules : Array String
  /-- The claimed modules no other claimed module imports, ordered by coverage size then name. -/
  roots : Array String
  /-- The claimed modules each root covers, one entry per root in `roots` order. -/
  coverage : Array Coverage
  deriving Repr

/-- The observed outcome of one `leanchecker --fresh` process. -/
structure Check where
  /-- The root module that was checked. -/
  root : String
  /-- The claimed modules the plan says this root covers. -/
  coveredModules : Array String
  /-- The process exit code; `0` is a completed check. -/
  exitCode : UInt32
  deriving Repr

/-- The parsed `freshChecker` command-line options. -/
structure Options where
  /-- `--manifest PATH`: the surface manifest; `foundation_manifest.json` at the project root
  when absent. -/
  manifest : Option FilePath := none
  /-- `--project DIR`: a directory inside the project to check; the current repository when
  absent. -/
  project : Option FilePath := none
  /-- `--json-out PATH`: where to write the plan, checks and result status as JSON. -/
  jsonOut : Option FilePath := none
  /-- `--plan-only`: compute and reconcile the plan without building or checking. -/
  planOnly : Bool := false
  /-- `--fail-fast`: stop at the first root whose check fails. -/
  failFast : Bool := false
  /-- `--verbose`: print the modules each root covers before checking it. -/
  verbose : Bool := false
  /-- `--help` or `-h`: print the usage and exit. -/
  help : Bool := false

private def usage : String :=
  "usage: lake exe freshChecker -- [--project DIR] [--manifest PATH] [--json-out PATH] " ++
  "[--plan-only] [--fail-fast] [--verbose]"

private def parseArgs : List String → Options → IO Options
  | [], options => return options
  | "--" :: rest, options => parseArgs rest options
  | "--manifest" :: value :: rest, options =>
      parseArgs rest { options with manifest := some (FilePath.mk value) }
  | "--project" :: value :: rest, options =>
      parseArgs rest { options with project := some (FilePath.mk value) }
  | "--json-out" :: value :: rest, options =>
      parseArgs rest { options with jsonOut := some (FilePath.mk value) }
  | "--plan-only" :: rest, options => parseArgs rest { options with planOnly := true }
  | "--fail-fast" :: rest, options => parseArgs rest { options with failFast := true }
  | "--verbose" :: rest, options => parseArgs rest { options with verbose := true }
  | "--help" :: rest, options | "-h" :: rest, options =>
      parseArgs rest { options with help := true }
  | flag :: _, _ => throw <| IO.userError s!"unknown or incomplete argument: {flag}"

private def resolve (repo path : FilePath) : FilePath :=
  if path.isAbsolute then path else repo / path.toString

private def uniqueSorted (values : Array String) : Array String :=
  values.foldl (fun found value => if found.contains value then found else found.push value) #[]
    |>.qsort (· < ·)

private def coverageFor (root : String) (imports modules : Array String) : Array String :=
  uniqueSorted <| (#[root] ++ imports).filter modules.contains

/-- Builds the plan from the manifest and Lake's surface inventory: collects each surface's
modules, selects as roots the claimed modules no other claimed module imports, and throws
`fresh-coverage-incomplete` unless the roots' claimed transitive imports cover every claimed
module. -/
def buildPlan (repo manifestPath : FilePath) : IO Plan := do
  let inventory ← Lake.surfaceInventory repo
  let manifest ← Manifest.loadFor manifestPath inventory
  let mut moduleSets : Array ModuleSet := #[]
  for surface in manifest.surfaces do
    let some library := inventory.libraries.find? (·.library == surface.library)
      | throw <| IO.userError s!"lake-query-malformed: auditPlan omitted {surface.library}"
    let mut modules := library.modules
    for exeName in surface.executables do
      let some exe := inventory.executables.find? (·.executable == exeName)
        | throw <| IO.userError s!"lake-query-malformed: auditPlan omitted {exeName}"
      modules := modules.push exe.root
    moduleSets := moduleSets.push {
      library := surface.library
      modules := modules.map (·.toString)
    }
  let modules := uniqueSorted <| moduleSets.foldl (fun all item => all ++ item.modules) #[]
  let mut importSets : Array (String × Array String) := #[]
  for moduleName in modules do
    importSets := importSets.push (moduleName, ← Lake.transitiveImports repo moduleName)
  let mut roots : Array String := #[]
  for moduleName in modules do
    let importedByAnother := importSets.any fun (other, imports) =>
      other != moduleName && imports.contains moduleName
    if !importedByAnother then roots := roots.push moduleName
  roots := roots.qsort fun left right =>
    let leftImports := (importSets.find? (·.1 == left)).map (·.2) |>.getD #[]
    let rightImports := (importSets.find? (·.1 == right)).map (·.2) |>.getD #[]
    let leftSize := (coverageFor left leftImports modules).size
    let rightSize := (coverageFor right rightImports modules).size
    leftSize < rightSize || (leftSize == rightSize && left < right)
  let mut coverage : Array Coverage := #[]
  for root in roots do
    let imports := (importSets.find? (·.1 == root)).map (·.2) |>.getD #[]
    coverage := coverage.push { root, modules := coverageFor root imports modules }
  let covered := uniqueSorted <| coverage.foldl (fun all item => all ++ item.modules) #[]
  if covered != modules then
    let missing := modules.filter fun moduleName => !covered.contains moduleName
    throw <|
        IO.userError s!"fresh-coverage-incomplete: no selected root covers {repr missing.toList}"
  return { moduleSets, modules, roots, coverage }

private def planJson (plan : Plan) (checks : Array Check) : Json :=
  Json.mkObj [
    ("moduleSets", Json.mkObj <| plan.moduleSets.toList.map fun item =>
      (item.library, Json.arr <| item.modules.map Json.str)),
    ("modules", Json.arr <| plan.modules.map Json.str),
    ("roots", Json.arr <| plan.roots.map Json.str),
    ("coverage", Json.mkObj <| plan.coverage.toList.map fun item =>
      (item.root, Json.arr <| item.modules.map Json.str)),
    ("checks", Json.arr <| checks.map fun check => Json.mkObj [
      ("root", Json.str check.root),
      ("coveredModules", Json.arr <| check.coveredModules.map Json.str),
      ("exitCode", Json.num check.exitCode.toNat)
    ])
  ]

private structure FrozenGraph where
  claim : RegulaPolicy.Claim
  census : RegulaPolicy.Census
  plan : RegulaPolicy.Plan claim census
  roles : RegulaPolicy.CensusRoles census

private unsafe def freezeGraph (plan : Plan) (snapshot : RegulaPolicy.AdmittedSnapshot)
    (manifest : Manifest) (inventory : Lake.SurfaceInventory)
    (sources : Array ProducerReport.SourceBinding) : IO FrozenGraph := do
  let assignments ← IO.ofExcept <| Acceptance.surfaceAssignments manifest inventory
  let claim ← IO.ofExcept <| RegulaPolicy.admitClaim {
    scope := .project, mode := .serializedGraph, snapshot := snapshot.val, surfaces := assignments }
  let names := assignments.flatMap fun assignment => assignment.modules.map (·.name)
  let modules ← names.mapM fun name => do
    pure (⟨snapshot, ← IO.ofExcept (RegulaPolicy.admitIdentity name)⟩ : RegulaPolicy.ModuleKey)
  let keyFor (name : String) : IO RegulaPolicy.ModuleKey := do
    let [key] := (modules.filter fun key => key.name.name.toString == name).toList
      | throw <| IO.userError "unknown or ambiguous graph module identity"
    pure key
  unless uniqueSorted (names.map (·.toString)) == plan.modules do
    throw <| IO.userError "graph plan differs from independently discovered module inventory"
  let graphRoots ← plan.roots.mapM keyFor
  let graphCoverage ← plan.coverage.mapM fun entry => do
    pure (← keyFor entry.root, ← entry.modules.mapM keyFor)
  let moduleSources ← modules.mapM fun key => do
    let [source] := (sources.filter (·.moduleName == key.name.name)).toList
      | throw <| IO.userError "missing or duplicate graph source binding"
    pure (key, (⟨source.path, source.content⟩ : RegulaPolicy.SourceSnapshot))
  let previous ← Lean.searchPathRef.get
  let origins ← try
      Lean.searchPathRef.set inventory.leanPath.toList
      modules.mapM fun key => do
        let path ← IO.FS.realPath (← Lean.findOLean key.name.name)
        unless ← pathWithin path inventory.leanLibDir do
          throw <| IO.userError "graph module resolved outside owned build output"
        let (data, _) ← Lean.readModuleData path
        pure
            (⟨key.name.name, path.toString, data.imports.map (·.module)⟩ :
                RegulaPolicy.ModuleOrigin)
    finally Lean.searchPathRef.set previous
  let compiler ← IO.ofExcept <|
    RegulaPolicy.Compiler.admitCapability (← Regula.Collect.compilerCapability)
  let policy ← IO.ofExcept <| RegulaPolicy.admitInventory compiler #[] #[]
  let execution ← IO.ofExcept <| RegulaPolicy.admitExecution #[]
  let request : RegulaPolicy.EnvironmentRequest := { key := ⟨snapshot, 0⟩, modules }
  let environment : RegulaPolicy.EnvironmentCensus := {
    request, policy, execution, modules, importedModules := #[], origins, moduleSources,
        importedSources := #[],
    unclassifiedRootImports := #[], admissionDeclarations := #[], declarations := #[], roots := #[],
    materialDeclarations := #[] }
  let census : RegulaPolicy.Census := {
    requests := #[request], environments := #[environment], modules, moduleSources, graphRoots,
        graphCoverage,
    configuredTargets := Acceptance.configuredTargets manifest, discoveredTargets :=
        Acceptance.discoveredTargets inventory }
  let admitted ← IO.ofExcept <| RegulaPolicy.buildPlan claim census
  return ⟨claim, census, admitted, fun slot =>
      RegulaPolicy.authorize census.environments[slot].policy⟩

private def finishGraph (frozen : FrozenGraph) (build : ProcessResult) (checks : Array Check) :
    Except String (RegulaPolicy.AcceptedRun frozen.claim) := do
  let checked ← checks.mapM fun check => do
    let [key] :=
        (frozen.census.graphRoots.filter fun key => key.name.name.toString == check.root).toList
      | throw "unrequested graph root response"
    let [coverage] :=
        (frozen.census.graphCoverage.filter (fun entry => decide (entry.1 = key))).toList
      | throw "missing frozen graph coverage"
    unless coverage.2.map (·.name.name.toString) == check.coveredModules do
      throw "graph response coverage mismatch"
    unless check.exitCode == 0 do throw "graph checker process failed"
    pure key
  let graph : RegulaPolicy.GraphObservation := {
    selected := frozen.census.graphRoots, checked,
    covered := frozen.census.graphCoverage.flatMap (·.2), failures := #[], plannedOnly := false }
  let inputs ← frozen.plan.jobs.mapIdxM fun slot key => do
    let evidence ← match key.stage, key.subject with
      | .configuration, .scope =>
          pure
              (RegulaPolicy.JobEvidence.configuration frozen.census.configuredTargets
                  frozen.census.discoveredTargets)
      | .discovery, .scope => pure (.discovery frozen.census)
      | .build, .scope => pure (.build (Acceptance.buildObservation build))
      | .graph, .scope => pure (.graph graph)
      | _, _ => throw "unsupported graph observation stage"
    pure
        (slot, ({ key, snapshot := frozen.claim.val.snapshot, completion := .completed, evidence } :
            RegulaPolicy.JobObservation))
  let result ← (RegulaPolicy.finalize frozen.plan frozen.roles inputs.toList).mapError
    (fun failure => s!"graph acceptance refused: {repr failure}")
  return ⟨frozen.census, frozen.plan, frozen.roles, inputs.toList, result⟩

private def optionValues (flag : String) : List String → List String
  | option :: value :: rest =>
      if option == flag then value :: optionValues flag rest
      else optionValues flag (value :: rest)
  | _ => []

/-- Runs the serialized-graph qualification: invalidates every `--json-out` destination, builds
the plan, and unless `--plan-only` builds the positive targets, runs
`lake env leanchecker --fresh` on each root, rechecks the captured inputs and admits the result
through `RegulaPolicy.finalize`, then writes the JSON result when requested. Returns `1` when the
build or a check fails and `0` otherwise. -/
unsafe def run (args : List String) : IO UInt32 := do
  let destinations := (optionValues "--json-out" args).eraseDups.map FilePath.mk
  let invalidate (path : FilePath) :=
    writeJson path (Json.mkObj [("mode", .str "serializedGraph"),
      ("status", .str "incomplete"), ("unresolved", toJson #["graph audit has not completed"])])
  -- Invalidate recognizable outputs before parsing; absolute paths do not need
  -- valid project discovery. Relative paths retain the public repo-root meaning.
  for path in destinations.filter (·.isAbsolute) do invalidate path
  let relative := destinations.filter (!·.isAbsolute)
  if !relative.isEmpty then
    let root ← match optionValues "--project" args with
      | [dir] => findRepoRoot dir
      | [] => repoRoot
      | _ => throw <| IO.userError "duplicate --project option"
    for path in relative do invalidate (resolve root path)
  CompilerMode.requireAllowed
  let options ← parseArgs args {}
  if options.help then IO.println usage; return 0
  let repo ← match options.project with
    | some dir => findRepoRoot dir
    | none => repoRoot
  let manifestPath := options.manifest.map (resolve repo) |>.getD (Manifest.defaultPath repo)
  let configuration ← SourceBinding.configuration repo manifestPath
  let inventory ← Lake.surfaceInventory repo
  let sources ← SourceBinding.capture inventory.moduleSources
  let dependencies ← Snapshot.dependencies inventory
  let snapshots ← Acceptance.sourceSnapshots sources #[]
  let snapshot ← IO.ofExcept <| Snapshot.make repo configuration snapshots dependencies
  let plan ← buildPlan repo manifestPath
  let mut checks : Array Check := #[]
  let mut failures : Array String := #[]
  let mut accepted : Option ((c : RegulaPolicy.Claim) × RegulaPolicy.AcceptedRun c) := none
  if !options.planOnly then
    let manifest ← Manifest.loadFor manifestPath inventory
    let (build, buildResult) ← Lake.buildCheckedObservation repo
        (Manifest.positiveTargets manifest) "incrementally"
    if let some lines := buildResult then
      for line in lines do IO.println s!"    {line}"
      return 1
    let frozen ← freezeGraph plan snapshot manifest inventory sources
    for root in plan.roots do
      let covered := (plan.coverage.find? (·.root == root)).map (·.modules) |>.getD #[]
      if options.verbose then
        IO.println s!"fresh root {root}: covers {", ".intercalate covered.toList}"
      let result ← runProcess repo "lake" #["env", "leanchecker", "--fresh", root]
      checks := checks.push { root, coveredModules := covered, exitCode := result.exitCode }
      if !result.succeeded then
        let tail := "\n".intercalate (takeLast 20 (outputLines result.output)).toList
        failures := failures.push s!"fresh-check-failed: {root}: {tail}"
        if options.failFast then break
    SourceBinding.unchanged sources
    SourceBinding.configurationUnchanged configuration
    Snapshot.inputsUnchanged inventory dependencies
    if failures.isEmpty then
      accepted := some ⟨frozen.claim, ← IO.ofExcept (finishGraph frozen build checks)⟩
  if let some path := options.jsonOut then
    let value := (planJson plan checks).setObjVal! "mode" (.str "serializedGraph")
    let value := match accepted with
      | some ⟨_, receipt⟩ => (value.setObjVal! "status"
          (.str (Account.Status.completed (Account.account receipt)).spelling)).setObjVal!
          "acceptance" (ResultProtocol.acceptedJson receipt)
      | none =>
          value.setObjVal! "status" (.str (if options.planOnly then "planned" else "incomplete"))
    writeJson (resolve repo path) (CompilerMode.envelope value)
  IO.println
      s!"Lake modules: {plan.modules.size}   fresh roots: {", ".intercalate plan.roots.toList}"
  if !failures.isEmpty then
    IO.println s!"FAIL: {failures.size} fresh-check violation(s)"
    for failure in failures do IO.println s!"  {failure}"
    return 1
  if options.planOnly then
    IO.println "fresh checker plan: coverage reconciled (planning only; no audit certificate)"
  else
    let some ⟨_, receipt⟩ := accepted | throw <| IO.userError "missing accepted graph evidence"
    let account := Account.account receipt
    for line in account.lines do IO.println line
    IO.println s!"{account.pass "fresh checker"} ({receipt.report.census.modules.size} \
      modules, {account.val.jobs} accepted serialized-graph jobs)"
  return 0

end Regula.Checker.FreshChecker

/-- The `freshChecker` executable: initializes Lean's search path and runs
`Regula.Checker.FreshChecker.run`, printing any exception as `FAIL:` and returning `1`. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Regula.Checker.FreshChecker.run args
  catch error =>
    IO.eprintln s!"FAIL: {error}"
    return 1
