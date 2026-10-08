import Regula.Checker.Acceptance
import Regula.Checker.FenceScan
import RegulaPolicy.Pattern
import Regula.Checker.SourceAudit
import Regula.Checker.Lake
import Regula.Checker.RuleDiagnostics
import Regula.Checker.RunFeedback
import RegulaCore.Account

/-!
# Markdown fence auditing

Exact, verbatim Lean-source auditing of the fences that the scanner of
`Regula.Checker.FenceScan` finds: this module reads the documents, gives each text to a scanner,
and compiles and inspects each fence.
-/

namespace Regula.Checker.Documentation

open Lean System
open Regula.Checker
open Regula.Checker.Policy

/-- How a documentation example is audited, from its fence's marker (`kindOf`). -/
inductive Kind where
  /-- An unmarked example: it must elaborate warning-free and meet the Standard-Logical
  declaration rules. -/
  | positive
  /-- A `lean-fail` example: it must fail to elaborate with a matching diagnostic. -/
  | negative
  /-- A `lean-trusted-compiler` example: it must elaborate warning-free, meet the declaration
  rules at the compiler-trusting profile and contain a compiler-trusting declaration. -/
  | trusted
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- One documentation example to audit. -/
structure Task where
  /-- The fence holding the example. -/
  fence : Fence
  /-- `path:line` of the fence, the path relative to the Markdown root, or for a Verso source to
  the repository. -/
  origin : String
  /-- How the example is audited. -/
  kind : Kind
  deriving Repr, DecidableEq

/-- The verdict on one documentation example. -/
inductive Status where
  /-- A positive example elaborated warning-free and met the declaration rules. -/
  | pass
  /-- A negative example failed with a diagnostic matching its pattern. -/
  | passNegative
  /-- A trusted example elaborated warning-free, met the declaration rules and has a
  compiler-trusting declaration. -/
  | passTrusted
  /-- Any other outcome, including a check that did not complete. -/
  | fail
  deriving Repr, BEq, DecidableEq, ToJson, FromJson

/-- Real compiler/group observations retained for finalization. Every unit carries
its original fence and exact compiled source; classifications alone are not evidence. -/
structure RawExample where
  /-- The example's own compilation. -/
  compilation : SourceAudit.Compilation
  /-- The inspection of the example's group, for a compiled positive or trusted example. -/
  group : Option SourceAudit.GroupReport := none
  /-- Every example inspected in that group with its compilation; the example alone when it was
  not inspected. -/
  units : Array (Task × SourceAudit.Compilation)
  deriving Repr

/-- The audit result of one documentation example. -/
structure Result where
  /-- The audited example. -/
  task : Task
  /-- Its verdict. -/
  status : Status
  /-- Why the example failed; empty on success. -/
  detail : String := ""
  /-- Each declaration of the example a declaration rule rejects, with that rule. -/
  policyProblems : Array (Regula.RuleId × Regula.Report.Declaration) := #[]
  /-- The check did not complete, so a `fail` status is not evidence that the example is wrong. -/
  incomplete : Bool := false
  /-- The source-evidence or report-admission failure that left the check incomplete, if any. -/
  admissionFailure : Option ProducerReport.AdmissionFailure := none
  /-- The compiler and inspection observations `exampleObservation` finalizes. -/
  raw : Option RawExample := none
  deriving Repr

/-- The kind, verdict and completeness of one result, without its evidence. -/
structure Classification where
  /-- The example's kind. -/
  kind : Kind
  /-- The example's verdict. -/
  status : Status
  /-- Whether the check did not complete. -/
  incomplete : Bool
  deriving DecidableEq, ToJson, FromJson

/-- The classification of a result. -/
def classification (result : Result) : Classification :=
  ⟨result.task.kind, result.status, result.incomplete⟩

/-- The results are nonempty and each is a completed positive example that passed. -/
def PositiveClassifications (results : Array Classification) : Prop :=
  results ≠ #[] ∧ ∀ result ∈ results,
    result.kind = .positive ∧ result.status = .pass ∧ result.incomplete = false

instance (results : Array Classification) : Decidable (PositiveClassifications results) := by
  unfold PositiveClassifications
  infer_instance

/-- Returns `results` with a proof of `PositiveClassifications`, or an error when they do not
satisfy it. -/
def admitPositiveClassifications (results : Array Classification) :
    Except String
        { checked : Array Classification // checked = results ∧ PositiveClassifications checked } :=
  if h : PositiveClassifications results then .ok ⟨results, rfl, h⟩
  else .error "documentation correction requires completed positive fences"

theorem positiveClassifications_sound (results : Array Classification)
    (checked : { cs : Array Classification // cs = results ∧ PositiveClassifications cs })
    (_ : admitPositiveClassifications results = .ok checked) :
    checked.val = results ∧ PositiveClassifications checked.val := checked.property

private def withSourceEvidence (tasks : Array Task)
    (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (action : IO (Array Result)) : IO (Array Result) := do
  match ← SourceBinding.withUnchanged sources configuration action with
  | .ok results => return results
  | .error failure => return tasks.map fun task => {
      task, status := .fail, detail := failure.detail
      incomplete := true, admissionFailure := some failure }

/-- A fence with a failure pattern is negative, otherwise a trusted one is trusted, otherwise it
is positive. -/
def kindOf (fence : Fence) : Kind :=
  if fence.failPattern.isSome then .negative else if fence.trusted then .trusted else .positive

/-- The label a status is printed with. -/
def statusName : Status → String
  | .pass => "PASS"
  | .passNegative => "PASS_NEG"
  | .passTrusted => "PASS_TRUSTED"
  | .fail => "FAIL"

/-- The positive documentation count label. -/
def positiveSummary : String :=
  "conforming-positive-pass"

private def diagnostics (output : String) : String :=
  let lines := errorLines output
  " | ".intercalate (if lines.isEmpty then takeLast 4 (outputLines output) else lines).toList

private def compilationFailure (compilation : SourceAudit.Compilation)
    (task : Task) : Result :=
  let warnings := warningLines compilation.process.output
  let detail := if warnings.isEmpty then
    "did not elaborate verbatim: " ++ diagnostics compilation.process.output
  else "emitted warning: " ++ " | ".intercalate (warnings.extract 0 4).toList
  { task, status := .fail, detail, incomplete := !SourceAudit.sourceDiagnosticFailure compilation }

private def assessPositive (observed : RegulaPolicy.Compiler.LegacyCompilerTrust)
    (task : Task) (unitName : Name)
    (declarations : Array Regula.Report.Declaration)
    (transcripts : Array Frontend.Transcript) : Result := Id.run do
  let .ok scope := Policy.admitScope observed declarations transcripts
    | return { task, status := .fail, detail := "invalid policy observation inventory",
                 incomplete := true }
  let claim := if task.kind == .trusted then Profile.compilerTrusting
    else Profile.standardLogical
  let (problems, policyProblems, compilerCount) := Id.run do
    let mut policyProblems := #[]
    let mut problems : Array String := #[]
    let mut compilerCount := 0
    -- The admitted inventory is exactly `declarations` (`ScopeContract`).
    for h : decl in scope.inventory.declarations do
      if decl.module != unitName then continue
      if let some id := Policy.ruleForMember decl (some claim) scope h then
        let reason := Regula.Findings.ruleDetail id decl
        -- The finding names the declaration the author wrote (`Policy.subject_contract`).
        let named := Policy.subject decl scope h
        problems := problems.push s!"{reason}: {named.name} axioms={repr decl.axioms.toList}"
        policyProblems := policyProblems.push (id, named)
      if Policy.labelOfMember decl scope h == .compilerTrusting then
        compilerCount := compilerCount + 1
    return (problems, policyProblems, compilerCount)
  return if !problems.isEmpty then
    { task, status := .fail, detail := "; ".intercalate (problems.extract 0 4).toList,
        policyProblems }
  else if task.kind == .trusted && compilerCount == 0 then
    { task, status := .fail, detail := "trusted marker found no compiler-trusting declaration" }
  else
    { task, status := if task.kind == .trusted then .passTrusted else .pass }

private def auditNegative (compilation : SourceAudit.Compilation) (task : Task) : Result :=
  if let some errors := compilation.errors then
   if errors.isEmpty then
    { task, status := .fail, detail := "negative example elaborated successfully" }
   else
    let pattern := task.fence.failPattern.getD ""
    if errors.any (matchesPattern pattern) then
      { task, status := .passNegative }
    else
      { task, status := .fail, detail :=
          s!"failed, but not with expected diagnostic {repr pattern}: " ++
        diagnostics ("\n".intercalate errors.toList) }
  else
    { task, status := .fail, detail := "diagnostic worker did not complete: " ++
      diagnostics compilation.process.output, incomplete := true }

private structure PendingPositive where
  index : Nat
  task : Task
  compilation : SourceAudit.Compilation
  constantNames : Array String
  importNames : Array Name

private structure InspectionGroup where
  items : Array PendingPositive
  constantNames : Array String

private def disjoint (left right : Array String) : Bool :=
  left.all fun name => !right.contains name

private def addToGroups (groups : Array InspectionGroup)
    (item : PendingPositive) : Array InspectionGroup := Id.run do
  let mut result := groups
  for index in [:groups.size] do
    let some group := result[index]? | continue
    if (group.items.all fun other => other.importNames == item.importNames) &&
        disjoint item.constantNames group.constantNames then
      result := result.set! index {
        items := group.items.push item
        constantNames := group.constantNames ++ item.constantNames
      }
      return result
  return result.push { items := #[item], constantNames := item.constantNames }

/-- Compile every fence in bounded parallel workers, then import compatible
positive modules together. Compatibility requires the same direct imports and
disjoint exact constant names serialized in each `.olean`, so independent snippets remain verbatim
while the
large shared dependency environment is loaded only once per collision group.
Each group runs in a child process so extension-held imports are released on exit.
`extraSearchRoots` carries the freshly built claimed-surface libraries of the
checked project, ahead of any inherited search path. -/
unsafe def auditTasks (repo scratch : FilePath) (jobs : Nat)
    (tasks : Array Task) (sourceBindings : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (extraSearchRoots : Array FilePath := #[]) (ownedOutput : Option FilePath := none) : IO
    (Array Result) := do
  withSourceEvidence tasks sourceBindings configuration do
    SourceBinding.unchanged sourceBindings
    SourceBinding.configurationUnchanged configuration
    let indexed := tasks.mapIdx fun index task => (task, index)
    let specs := indexed.map fun (task, index) =>
      ({
        «module» := s!"DocFence_{index + 1}"
        source := task.fence.body
        warningAsError := task.kind != .negative
        rejectWarnings := task.kind != .negative
        captureRejection := task.kind == .negative
      } : SourceAudit.SourceSpec)
    let compilationOutcome ← timedPhase "fence compilation" <|
        SourceAudit.compileBatch repo scratch jobs specs
    SourceBinding.unchanged sourceBindings
    SourceBinding.configurationUnchanged configuration
    if let .error failure := compilationOutcome then
      return tasks.map fun task => {
        task, status := .fail, detail := failure.detail
        incomplete := true, admissionFailure := some failure }
    let .ok compilations := compilationOutcome
      | throw <| IO.userError "unreachable compilation outcome"
    let snippets := compilations.map fun compilation => ({
      moduleName := compilation.spec.module.toName
      path := compilation.sourcePath.toString
      content := compilation.spec.source } : ProducerReport.SourceBinding)
    withSourceEvidence tasks snippets #[] do
      IO.println s!"fence compilations complete: {tasks.size}; inspecting declarations"
      (← IO.getStdout).flush
      let mut responses : Array (Nat × Result) := #[]
      let mut groups : Array InspectionGroup := #[]
      for index in [:tasks.size] do
        let some task := tasks[index]?
          | throw <| IO.userError "internal error: missing documentation task"
        let some compilation := compilations[index]?
          | throw <| IO.userError "internal error: missing documentation compilation"
        if task.kind == .negative then
          responses := responses.push (index, { auditNegative compilation task with
            raw := some ⟨compilation, none, #[(task, compilation)]⟩ })
        else if !SourceAudit.compilationPassed compilation then
          responses := responses.push (index, { compilationFailure compilation task with
            raw := some ⟨compilation, none, #[(task, compilation)]⟩ })
        else
          let (moduleData, _) ← Lean.readModuleData compilation.oleanPath
          let item : PendingPositive := {
            index, task, compilation
            constantNames := moduleData.constNames.map (·.toString)
            importNames := moduleData.imports.map (·.module)
          }
          groups := addToGroups groups item
      let selfLib ← checkerPackageLibDir
      let oldSearchPath ← Lean.searchPathRef.get
      Lean.searchPathRef.set (scratch :: extraSearchRoots.toList ++ selfLib.toList ++ oldSearchPath)
      -- Each worker owns its imported environments and scratch files. Keep the
      -- search path fixed until all workers finish; merge immutable results only
      -- afterward. Use the same bounded worker count as fence compilation.
      let inspectGroups := mapWorkQueue jobs (groups.mapIdx fun i group => (i, group))
        fun (index, group) => do
          IO.println s!"inspection group {index + 1}/{groups.size}: {group.items.size} fence(s)"
          (← IO.getStdout).flush
          let modules := group.items.map (·.compilation.spec.«module».toName)
          try
            let outcome ← SourceAudit.inspectGroupCurrentSearchPath modules
              (group.items.map fun item =>
                  (item.compilation.spec.«module».toName, item.compilation.sourcePath))
              (sourceBindings.map fun source => (source.moduleName, FilePath.mk source.path))
              ownedOutput (includeExecution := false) (includeModuleOrigins := false)
              (compiledSources := sourceBindings ++ group.items.map fun item => {
                moduleName := item.compilation.spec.module.toName
                path := item.compilation.sourcePath.toString
                content := item.compilation.spec.source })
            if let .error refusal := outcome then
              -- Unowned imported modules are not an admission failure; they stay an incomplete
              -- inspection here, as the documentation mode has no coverage finding.
              let (detail, admissionFailure) := match refusal with
                | .admission failure => (failure.detail, some failure)
                | .unowned _ => (s!"checker inspection failed: {refusal.detail}", none)
              return group.items.map fun item =>
                let result : Result := {
                  task := item.task, status := .fail, detail, incomplete := true, admissionFailure }
                (item.index, result)
            let .ok inspected := outcome
              | throw <| IO.userError "unreachable admission outcome"
            let units := group.items.map fun item => (item.task, item.compilation)
            return group.items.map fun item =>
              let assessed := assessPositive inspected.report.compilerCapability
                item.task item.compilation.spec.module.toName
                inspected.report.declarations inspected.transcripts
              (item.index, { assessed with raw := some ⟨item.compilation, some inspected, units⟩ })
          catch error =>
            return group.items.map fun item =>
              let failure : Result :=
                  { task := item.task, status := .fail, detail :=
                      s!"checker inspection failed: {error}", incomplete := true }
              (item.index, failure)
      let updates ← try timedPhase "fence inspection" inspectGroups
        finally Lean.searchPathRef.set oldSearchPath
      for group in updates do responses := responses ++ group
      -- `IndexedResultsContract`: exactly one result per task, in task order, each bound
      -- to its own task; missing, duplicate, unknown and rebound results are refused.
      let complete ← IO.ofExcept <| (RegulaPolicy.checked_indexedResults.run tasks.size
        (fun index (result : Result) => decide (tasks[index]? = some result.task))
        responses.toList).mapError
        (fun failure => s!"documentation result admission: {repr failure}")
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      return complete

/-- Admit the scanner's exact original byte spans. Verbatim body equality is checked
before a fence can become a required coverage key. -/
def Fence.key (fence : Fence) : Except String RegulaPolicy.FenceKey := do
  let expectation ← match fence.failPattern with
    | some pattern => do
      if fence.trusted then throw "conflicting example classifications"
      validatePattern pattern
      if hp : pattern ≠ "" then pure (.compilerRejection pattern hp)
      else throw "empty compiler rejection expectation"
    | none => pure (if fence.trusted then .trustedTeaching else .positive)
  if hn : fence.document.uri ≠ "" then
    if ho : fence.opening.start ≤ fence.opening.stop ∧ fence.opening.stop ≤ fence.bodyRange.start ∧
        fence.bodyRange.start ≤ fence.bodyRange.stop ∧ fence.bodyRange.stop ≤ fence.closing.start ∧
        fence.closing.start ≤ fence.closing.stop then
      if hp : ∀ n ∈ [fence.opening.start, fence.opening.stop, fence.bodyRange.start,
          fence.bodyRange.stop, fence.closing.start, fence.closing.stop],
          String.Pos.Raw.isValid fence.document.source ⟨n⟩ = true then
        unless fence.body == String.Pos.Raw.extract fence.document.source
            ⟨fence.bodyRange.start⟩ ⟨fence.bodyRange.stop⟩ do
          throw "fence body differs from original document bytes"
        return ⟨fence.document, fence.opening, fence.bodyRange, fence.closing, expectation,
            hn, ho, hp⟩
      else throw "fence span is not a UTF-8 boundary"
    else throw "unordered fence byte spans"
  else throw "missing fence document identity"

/-- Documentation has no positive project ownership. Its fixed fence inventory is
independent of returned compilation results, including when a document has no fences. -/
structure DocumentPlan (claim : RegulaPolicy.Claim) where
  /-- A census holding only the fence inventory: no environment, module or target. -/
  census : RegulaPolicy.Census
  /-- The job plan built for the claim and that census. -/
  plan : RegulaPolicy.Plan claim census
  /-- The policy roles of the census's environment slots. -/
  roles : RegulaPolicy.CensusRoles census

/-- Builds the document plan from the admitted fence key of every task, failing when a fence is
not admissible (`Fence.key`) or the plan is refused. -/
def freezeDocuments (claim : RegulaPolicy.Claim) (tasks : Array Task) :
    Except String (DocumentPlan claim) := do
  let fences ← tasks.mapM (·.fence.key)
  let census : RegulaPolicy.Census := {
    requests := #[], environments := #[], modules := #[], moduleSources := #[],
    fences, configuredTargets := #[], discoveredTargets := #[] }
  let plan ← RegulaPolicy.buildPlan claim census
  return ⟨census, plan, fun slot => RegulaPolicy.authorize census.environments[slot].policy⟩

/-- Convert retained real production into observations. Roles are authenticated against
the entire compatible group; each policy check then selects only its original unit. -/
def exampleObservation (result : Result) : IO RegulaPolicy.ExampleObservation := do
  let some raw := result.raw | throw <| IO.userError "missing example production observations"
  if result.incomplete then throw <| IO.userError "example production incomplete"
  unless raw.compilation.process.succeeded do throw <|
                                               IO.userError "example compiler process failed"
  let fence ← IO.ofExcept result.task.fence.key
  let before := raw.compilation.spec.source
  let after ← IO.FS.readFile raw.compilation.sourcePath
  let units ← raw.units.mapM fun (task, compilation) => do
    let key ← IO.ofExcept task.fence.key
    pure ({
      moduleName := compilation.spec.module.toName, fence := key,
      source := ⟨compilation.sourcePath.toString, compilation.spec.source⟩ } :
          RegulaPolicy.ExampleUnit)
  let (census, outcome) ← if result.task.kind == .negative then do
      let some errors := raw.compilation.errors
        | throw <| IO.userError "missing completed compiler diagnostics"
      pure (#[], RegulaPolicy.ExampleOutcome.compilerRejection errors)
    else do
      let some group := raw.group | throw <| IO.userError "missing example group inspection"
      IO.ofExcept (ProducerReport.checked_validate.run group.report)
      IO.ofExcept <| group.report.validateSourceEvidence.mapError (·.detail)
      let scope ← IO.ofExcept <|
        Policy.admitScope group.report.compilerCapability group.report.declarations group.transcripts
      let some replay := group.report.admission
        | throw <| IO.userError "missing example logical admission"
      pure (group.report.census.declarations,
        RegulaPolicy.ExampleOutcome.elaborated scope.inventory replay.required replay.admitted #[])
  return {
    fence, unitName := raw.compilation.spec.module.toName, units, before, after,
    warnings := warningLines raw.compilation.process.output, declarationCensus := census, outcome }

/-- Finalize the frozen document plan using the unchanged output of `auditTasks`,
which has already collected every task occurrence and refused unknown, duplicate,
or missing results. This private helper does not admit arbitrary raw result arrays.
Neither per-example labels nor a zero failure count can accept the document plan. -/
private def finishDocuments {claim : RegulaPolicy.Claim} (frozen : DocumentPlan claim)
    (build : RegulaPolicy.BuildObservation) (documents : Array RegulaPolicy.SourceSnapshot)
    (structural : Array String) (results : Array Result) : IO (RegulaPolicy.AcceptedRun claim) := do
  let examples ← results.mapM exampleObservation
  let inputs ← frozen.plan.jobs.mapIdxM fun slot key => do
    let evidence ← match key.stage, key.subject with
      | .discovery, .scope => pure (RegulaPolicy.JobEvidence.discovery frozen.census)
      | .build, .scope => pure (.build build)
      | .documentScan, .scope => pure (.documentScan ⟨documents, frozen.census.fences, structural⟩)
      | .example, .fence fence => do
          let matching := examples.filter (fun observation => decide (observation.fence = fence))
          let [observation] := matching.toList
            | throw <| IO.userError "missing or repeated documentation example observation"
          pure (.example observation)
      | _, _ => throw <| IO.userError "unsupported documentation observation stage"
    pure
        (slot,
            ({ key, snapshot := claim.val.snapshot, completion := .completed, evidence } :
                RegulaPolicy.JobObservation))
  let result ← IO.ofExcept <|
      (RegulaPolicy.finalize frozen.plan frozen.roles inputs.toList).mapError
    (fun failure => s!"documentation acceptance refused: {repr failure}")
  return ⟨frozen.census, frozen.plan, frozen.roles, inputs.toList, result⟩

private def relativeDisplay (root path : FilePath) : String :=
  let rootComponents := root.normalize.components
  let pathComponents := path.normalize.components
  if rootComponents.isPrefixOf pathComponents then
    "/".intercalate (pathComponents.drop rootComponents.length)
  else path.toString

/-- Preserve the documentation discovery domain independently of the project
copy's build/cache exclusions. Only Markdown is consumed by the fence scanner,
and every such file is copied verbatim, including cache-named subdirectories. -/
def snapshotMarkdown (source target : FilePath) : IO Unit := do
  if !(← source.isDir) then return
  let rootComponents := source.normalize.components
  for path in ← source.walkDir do
    if path.extension != some "md" then continue
    let relative := path.normalize.components.drop rootComponents.length
    let destination := relative.foldl (fun base part => base / part) target
    if let some parent := destination.parent then IO.FS.createDirAll parent
    IO.FS.writeFile destination (← IO.FS.readFile path)

/-- Reads every `.md` file below `root`, recursively, in path order; fails when `root` is not a
directory. -/
def captureMarkdown (root : FilePath) : IO (Array RegulaPolicy.SourceSnapshot) := do
  unless ← root.isDir do throw <| IO.userError s!"documentation root is not a directory: {root}"
  let paths := ((← root.walkDir).filter (·.extension == some "md")).qsort
    (fun left right => left.toString < right.toString)
  paths.mapM fun path => do pure ⟨path.toString, ← IO.FS.readFile path⟩

/-- Rereads the Markdown below `root` and throws when its paths or contents differ from
`documents`. -/
def checkMarkdown (root : FilePath) (documents : Array RegulaPolicy.SourceSnapshot) : IO Unit := do
  let current ← captureMarkdown root
  unless current.map (·.uri) == documents.map (·.uri) do
    throw <| IO.userError "documentation inventory changed"
  unless current == documents do throw <| IO.userError "documentation source changed"

/-- A Verso documentation package, given as `DIR:LIBRARY:RENDER`: its directory, its
documentation library and the executable that renders that library alone. -/
structure VersoPackage where
  /-- The Verso package's directory. -/
  dir : FilePath
  /-- The documentation library whose modules are audited. -/
  library : Name
  /-- The executable that renders that library. -/
  render : String

/-- Parse `DIR:LIBRARY:RENDER`, the Verso documentation option of the audit commands. -/
def parseVersoOption (value : String) : Except String VersoPackage :=
  match value.splitOn ":" with
  | [dir, library, render] =>
    if dir.isEmpty || library.isEmpty || render.isEmpty then
        .error s!"expected DIR:LIBRARY:RENDER, got {value}"
    else .ok ⟨FilePath.mk dir, library.toName, render⟩
  | _ => .error s!"expected DIR:LIBRARY:RENDER, got {value}"

/-- Exact module sources of the documentation library of `verso`, discovered through Lake's
elaborated package model, in path order. -/
def captureVerso (verso : VersoPackage) : IO (Array RegulaPolicy.SourceSnapshot) := do
  let dir := verso.dir
  let paths ← Workspace.withRootWorkspace dir fun ws => do
    let some lib := ws.root.leanLibs.find? (·.name == verso.library)
      | throw <| IO.userError s!"Verso package {dir} has no library {verso.library}"
    let modules ← lib.getModuleArray
    if modules.isEmpty then throw <| IO.userError s!"Verso library {verso.library} has no modules"
    -- Re-anchor Lake's real paths at `dir` as given, so document identities stay relative.
    let real := (← IO.FS.realPath dir).normalize.components
    modules.mapM fun m => do
      let file := (← IO.FS.realPath m.leanFile).normalize.components
      unless real.isPrefixOf file do
        throw <| IO.userError s!"Verso module {m.name} is outside its package {dir}"
      return (file.drop real.length).foldl (· / ·) dir
  let paths := paths.qsort (fun left right => left.toString < right.toString)
  paths.mapM fun path => do pure ⟨path.toString, ← IO.FS.readFile path⟩

/-- The modules that `key`, an entry of a library's `needs`, names in a package that `captured`
selects: an executable's root or a library's modules. A target of any other package names none:
its sources are the accepted project's or a pinned dependency's. -/
private partial def neededModules (ws : _root_.Lake.Workspace)
    (captured : _root_.Lake.Package → Bool) (key : _root_.Lake.BuildKey) :
    IO (Array _root_.Lake.Module) :=
  match key with
  | .facet target _ => neededModules ws captured target
  | .packageTarget package target => do
    let some pkg := if package.isAnonymous then some ws.root else ws.findPackageByName? package
      | throw <| IO.userError s!"Verso package need @{package}/{target} names no package"
    if !captured pkg then return #[]
    if let some exe := pkg.leanExes.find? (·.name == target) then return #[exe.root]
    if let some lib := pkg.leanLibs.find? (·.name == target) then return ← lib.getModuleArray
    throw <| IO.userError s!"Verso package need {target} is not a target of {pkg.baseName}"
  | .module name | .packageModule _ name => pure (ws.findModule? name).toArray
  | .package package => throw <| IO.userError s!"unsupported Verso package need @{package}"

/-- The modules of the packages that `captured` selects reachable from `roots` by import, the
roots included, each once. Imports are read with Lean's header parser and resolved through Lake;
a module of another package or of the toolchain ends its path. -/
private def localClosure (ws : _root_.Lake.Workspace) (captured : _root_.Lake.Package → Bool)
    (roots : Array _root_.Lake.Module) : IO (Array _root_.Lake.Module) := do
  let mut seen : NameSet := {}
  let mut pending := roots.toList
  let mut closure := #[]
  repeat
    let m :: rest := pending | break
    pending := rest
    if seen.contains m.name then continue
    seen := seen.insert m.name
    closure := closure.push m
    let header ← Lean.parseImports' (← IO.FS.readFile m.leanFile) m.leanFile.toString
    for i in header.imports do
      if let some imported := ws.findModule? i.module then
        if captured imported.pkg then pending := imported :: pending
  return closure

/-- The packages the Verso package at `dir` requires by local path, other than the accepted
project at `project`, whose sources the link accepts: each by its manifest name and the directory
Lake actually loaded, relative to `dir`. This includes materialized copies and overrides. -/
private def localPackages (project dir : FilePath) (ws : _root_.Lake.Workspace) :
    IO (Array (Name × FilePath)) := do
  let some manifest ← _root_.Lake.Manifest.load? (dir / "lake-manifest.json") | return #[]
  let accepted ← IO.FS.realPath project
  manifest.packages.filterMapM fun entry => do
    let .path .. := entry.src | return none
    let some pkg := ws.findPackageByName? entry.name
      | throw <| IO.userError s!"Verso package {dir} requires {entry.name}, which Lake did not load"
    if (← IO.FS.realPath pkg.dir) == accepted then return none
    return some (entry.name, pkg.relDir)

/-- Every library module of each package the Verso package requires by local path other than the
accepted project (`localPackages`), with its source file: for this repository, the modules of the
`audit/` package, whose `Audit` library the standard's examples import. The
documentation audit owns them alongside the project's claimed modules when examples elaborate in
the Verso package's workspace, so an example's owned logical dependencies stay closed under
import and pass kernel admission with it. -/
def versoLocalModules (project : FilePath) (verso : VersoPackage) :
    IO (Array (Name × FilePath)) := do
  Workspace.withRootWorkspace verso.dir fun ws => do
    let locals ← localPackages project verso.dir ws
    let mut modules := #[]
    for (name, _) in locals do
      let some pkg := ws.findPackageByName? name
        | throw <| IO.userError s!"Verso package {verso.dir} requires {name}, which Lake did not load"
      for lib in pkg.leanLibs do
        for m in ← lib.getModuleArray do
          modules := modules.push (m.name, m.leanFile)
    return modules

/-- The inputs of the Verso package that decide how its documentation library is checked and
rendered, in path order: its Lake configuration and lock files and, discovered through Lake, the
modules reachable by import from the library's modules, from the root of each executable the
library `needs` and from the root of the render executable. Modules are followed in the Verso
package itself and in each package it requires by local path other than the accepted project
`project` (`localPackages`); for this repository that is the `audit/` package whose
`Audit` library the standard's examples import, whose configuration and lock files, and surface
manifest, are captured too. A target of a Git dependency is pinned and is not read, nor are the
packages' other targets (the site's generated pages). Each path is anchored at the Verso
directory as given (a local package's through its recorded relative directory), so the identity
stays location-independent. The linked acceptance identity brackets these inputs together with
the documentation itself. -/
def captureVersoPackage (project : FilePath) (verso : VersoPackage) :
    IO (Array RegulaPolicy.SourceSnapshot) := do
  let dir := verso.dir
  let (locals, modules) ← Workspace.withRootWorkspace dir fun ws => do
    let locals ← localPackages project dir ws
    let some lib := ws.root.leanLibs.find? (·.name == verso.library)
      | throw <| IO.userError s!"Verso package {dir} has no library {verso.library}"
    let some render := ws.root.leanExes.find?
        (·.name == _root_.Lake.stringToLegalOrSimpleName verso.render)
      | throw <| IO.userError s!"Verso package {dir} has no executable {verso.render}"
    -- Each captured package, by its key, with the directory its sources are anchored at.
    let mut anchors : Array (Name × FilePath) := #[(ws.root.keyName, dir)]
    for (name, relative) in locals do
      let some pkg := ws.findPackageByName? name
        | throw <| IO.userError s!"Verso package {dir} requires {name}, which Lake did not load"
      anchors := anchors.push (pkg.keyName, dir / relative)
    let captured := fun (pkg : _root_.Lake.Package) => anchors.any (·.1 == pkg.keyName)
    let mut roots ← lib.getModuleArray
    for key in lib.config.needs do roots := roots ++ (← neededModules ws captured key)
    let closure ← localClosure ws captured (roots.push render.root)
    let modules ← closure.mapM fun m => do
      let some (_, anchor) := anchors.find? (·.1 == m.pkg.keyName)
        | throw <| IO.userError s!"Verso package source {m.leanFile} is outside its packages"
      let real := (← IO.FS.realPath anchor).normalize.components
      let components := (← IO.FS.realPath m.leanFile).normalize.components
      unless real.isPrefixOf components do
        throw <| IO.userError s!"Verso package source {m.leanFile} is outside its package {anchor}"
      return (components.drop real.length).foldl
          (fun (acc : FilePath) (part : String) => acc / part) anchor
    return (locals, modules)
  let packageDirs := #[dir] ++ locals.map fun (_, relative) => dir / relative
  let config ← packageDirs.flatMapM fun (packageDir : FilePath) =>
    (#["lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain",
        "foundation_manifest.json"] : Array String).filterMapM fun (name : String) => do
      let path : FilePath := packageDir / name
      return if ← path.pathExists then some path else none
  let paths := (modules ++ config).qsort (fun left right => left.toString < right.toString)
  let paths := paths.toList.eraseDups.toArray
  paths.mapM fun path => do pure ⟨path.toString, ← IO.FS.readFile path⟩

/-- The documentation one run covers: every Markdown file below `markdown` and, when given,
every module of the documentation library of the Verso package `verso`. -/
structure Sources where
  /-- The directory whose Markdown files, recursively, are covered. -/
  markdown : FilePath
  /-- The Verso package whose documentation library is also covered, if any. -/
  verso : Option VersoPackage := none

/-- The Markdown snapshots (`captureMarkdown`), then the Verso library's module sources
(`captureVerso`). -/
def Sources.capture (sources : Sources) : IO (Array RegulaPolicy.SourceSnapshot) := do
  let markdown ← captureMarkdown sources.markdown
  let verso ← match sources.verso with
    | some verso => captureVerso verso
    | none => pure #[]
  return markdown ++ verso

/-- Recaptures the sources and throws when their paths or contents differ from `documents`. -/
def Sources.check (sources : Sources) (documents : Array RegulaPolicy.SourceSnapshot) :
    IO Unit := do
  let current ← sources.capture
  unless current.map (·.uri) == documents.map (·.uri) do
    throw <| IO.userError "documentation inventory changed"
  unless current == documents do throw <| IO.userError "documentation source changed"

/-- The documentation together with its Verso package's inputs (`captureVersoPackage`, for the
accepted project at `project`): what the linked acceptance identity brackets. -/
def Sources.captureLinked (sources : Sources) (project : FilePath) :
    IO (Array RegulaPolicy.SourceSnapshot) := do
  let package ← match sources.verso with
    | some verso => captureVersoPackage project verso
    | none => pure #[]
  return (← sources.capture) ++ package

/-- Recaptures the linked sources (`captureLinked`) and throws when they differ from `linked`. -/
def Sources.checkLinked (sources : Sources) (project : FilePath)
    (linked : Array RegulaPolicy.SourceSnapshot) : IO Unit := do
  unless (← sources.captureLinked project) == linked do
    throw <| IO.userError "documentation or its Verso package changed"

/-- Audit all documentation against the caller's freshly built isolated workspace.
The standalone command creates that workspace itself; combined verification owns
it from declaration admission through the last fence inspection. Every example elaborates in the
project's Lake environment, or, when `environment` gives a workspace directory, its search
path and its own modules, in that workspace: the documentation audit passes the freshly built
Verso package, which requires the project and resolves every module the standard's examples
import, with the modules of the packages it requires by local path (`versoLocalModules`). The
owned modules are the project's claimed ones and those environment modules. Each structural
problem and each fence result obtained is reported before a failure of the fence audit or of the
terminal recheck is rethrown. -/
unsafe def auditBuiltProject (repo docsRoot : FilePath) (inventory : Lake.SurfaceInventory)
    (sourceBindings : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String))
    (dependencies : Array Snapshot.DependencyObservation)
    (documents : Array RegulaPolicy.SourceSnapshot)
    (build : RegulaPolicy.BuildObservation) (jobs : Nat) (verbose : Bool)
    (emit : Regula.Finding → IO Unit := fun _ => pure ())
    (observe : Array Result → IO Unit := fun _ => pure ())
    (observeAccepted : (claim : RegulaPolicy.Claim) → RegulaPolicy.AcceptedRun claim → IO Unit :=
        fun _ _ => pure ())
    (sharedSnapshot : Option RegulaPolicy.AdmittedSnapshot := none)
    (verso : Option VersoPackage := none)
    (environment : Option (FilePath × Array FilePath × Array (Name × FilePath)) := none) :
    IO UInt32 := do
  let sources : Sources := ⟨docsRoot, verso⟩
  let (fenceWorkspace, fenceSearchPath, environmentModules) :=
    environment.getD (repo, inventory.leanPath, #[])
  -- The environment's own modules are owned too, and their sources stay bound while fences run.
  let ownedBindings := sourceBindings ++ (← SourceBinding.capture environmentModules)
  let outcome : Except ProducerReport.AdmissionFailure UInt32 ←
    SourceBinding.withUnchanged sourceBindings configuration do
      if documents.isEmpty then
        IO.println s!"FAIL: no Markdown files found recursively below {docsRoot}"
        return 1
      sources.check documents
      let snapshot ← match sharedSnapshot with
        | some snapshot => pure snapshot
        | none => do
            let allSources ← Acceptance.sourceSnapshots sourceBindings #[] documents
            IO.ofExcept <| Snapshot.make repo configuration allSources dependencies
      let claim ← IO.ofExcept <| RegulaPolicy.admitClaim {
        scope := .documentation documents, mode := .documentationExample,
        snapshot := snapshot.val, surfaces := #[] }
      let mut tasks : Array Task := #[]
      let mut structural : Array String := #[]
      for document in documents do
        let path := FilePath.mk document.uri
        -- Markdown documents below `docsRoot`; Verso sources (`.lean`) by repository path.
        let (relative, scan) := if path.extension == some "lean" then
            let relative := relativeDisplay (docsRoot.parent.getD docsRoot) path
            (relative, Documentation.scanVerso document.source relative (some document.uri))
          else
            let relative := relativeDisplay docsRoot path
            (relative, Documentation.scan document.source relative (some document.uri))
        structural := structural ++ scan.problems
        for fence in scan.fences do
          tasks := tasks.push {
            fence
            origin := s!"{relative}:{fence.line}"
            kind := kindOf fence
          }
      let positiveCount := (tasks.filter (·.kind == .positive)).size
      let negativeCount := (tasks.filter (·.kind == .negative)).size
      let trustedCount := (tasks.filter (·.kind == .trusted)).size
      IO.println <| s!"```lean fences: {tasks.size} " ++
        s!"(conforming-positive {positiveCount}, negative {negativeCount}, trusted {trustedCount})"
      (← IO.getStdout).flush
      -- A structural problem already refuses acceptance, and a malformed marker's
      -- fence has no request key. Freeze only a structurally clean corpus, so its
      -- located problems are still reported; a key error without one still throws.
      let frozen ← if structural.isEmpty then
          some <$> timedPhase "documentation request freeze" do
            IO.ofExcept (← IO.lazyPure fun _ => freezeDocuments claim tasks)
        else pure none
      let fenceScratch := fenceWorkspace / "tmp" / "fence-build"
      -- A failed fence audit or terminal recheck must not drop a finding that is already
      -- established (a structural problem or a fence result). Both run in `BaseIO`, which cannot
      -- throw; the report follows, and the first failure is rethrown only after it.
      let audit : IO (Array Result) := do
        IO.FS.createDirAll fenceScratch
        auditTasks fenceWorkspace fenceScratch jobs tasks ownedBindings configuration
          fenceSearchPath (some inventory.leanLibDir)
      let audited ← audit.toBaseIO
      let recheck : IO (Option (RegulaPolicy.AcceptedRun claim)) := do
        let results ← MonadExcept.ofExcept audited
        sources.check documents
        Snapshot.inputsUnchanged inventory dependencies
        match frozen with
        | some frozen =>
            if results.all (·.status != .fail) then
              pure (some (← finishDocuments frozen build documents structural results))
            else pure none
        | none => pure none
      let rechecked ← recheck.toBaseIO
      let results := audited.toOption.getD #[]
      let accepted := rechecked.toOption.join
      let mut failures := structural.size
      for problem in structural do
        IO.println s!"[X] {problem}"
        let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding .fenceStructure
            docsRoot.toString
          problem .documentationExample .violation
        RunFeedback.emit IO.println finding
        emit finding
      for result in results.qsort fun left right => left.task.origin < right.task.origin do
        let mark := match result.status with
          | .pass => "." | .passNegative => "n" | .passTrusted => "t" | .fail => "X"
        let label := if result.status == .fail || accepted.isSome then statusName result.status
          else "OBSERVED (audit incomplete)"
        IO.println s!"[{mark}] {result.task.origin} {label}"
        if result.status == .fail then
          failures := failures + 1
          let detail := if verbose then result.detail
            else (result.detail.splitOn " | ").head?.getD result.detail |>.take 180 |>.toString
          IO.println s!"      {detail}"
          let id : Regula.RuleId := match result.task.kind with
            | .positive => .positiveExample | .negative => .negativeExample | .trusted =>
                                                                               .trustedExample
          let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding id result.task.origin
            result.detail .documentationExample
                (if result.incomplete then .incomplete else .violation)
          RunFeedback.emit IO.println finding
          emit finding
          if let some failure := result.admissionFailure then
            let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding .admission
                result.task.origin
              failure.detail .documentationExample .incomplete
            RunFeedback.emit IO.println finding
            emit finding
          for (rule, decl) in result.policyProblems do
            -- Ranges are relative to the exact verbatim snippet, explicitly a virtual source.
            let snapshot : Regula.SourceSnapshot := {
              uri :=
                  s!"{if (FilePath.mk result.task.fence.document.uri).extension == some "lea\
                    n" then docsRoot.parent.getD docsRoot else docsRoot}/{result.task.origin}#lean-\
                    snippet"
              source := result.task.fence.body }
            let location ← IO.ofExcept <| RuleDiagnostics.declarationLocation decl (some snapshot)
            let finding ← IO.ofExcept <| RuleDiagnostics.declarationFinding rule
              (← IO.ofExcept <| RuleDiagnostics.declarationName decl) result.detail location
              .documentationExample
                  (some
                      (if result.task.kind == .trusted then "compiler-trusting" else
                                                             "standard-logical"))
            RunFeedback.emit IO.println finding
            emit finding
      let positivePass := (results.filter (·.status == .pass)).size
      let negativePass := (results.filter (·.status == .passNegative)).size
      let trustedPass := (results.filter (·.status == .passTrusted)).size
      IO.println <| "\nsummary: " ++
        s!"{positiveSummary}={positivePass}/{positiveCount} " ++
        s!"negative-pass={negativePass}/{negativeCount} " ++
        s!"trusted-classified={trustedPass}/{trustedCount} fail={failures}"
      let accepted ← MonadExcept.ofExcept rechecked
      SourceBinding.unchanged sourceBindings
      SourceBinding.configurationUnchanged configuration
      observe results
      if failures != 0 then return 1
      let some accepted := accepted | throw <|
                                       IO.userError "missing accepted documentation evidence"
      observeAccepted claim accepted
      let account := Account.account accepted
      IO.println
          s!"accepted {account.val.jobs} documentation policy jobs for {account.val.mode.spelling}"
      for line in account.lines do IO.println line
      return 0
  match outcome with
  | .ok result => return result
  | .error failure =>
      let finding ← IO.ofExcept <| RuleDiagnostics.contextFinding .admission docsRoot.toString
        failure.detail .documentationExample .incomplete
      -- Both public callers own the enclosing frozen-project guard and render
      -- its refusal. Keep the finding callback without rendering it twice.
      emit finding
      return 1

end Regula.Checker.Documentation
