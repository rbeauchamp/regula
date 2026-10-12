import Regula.Removal
import Regula.TaskManagerCheck
import Regula.Checker.Documentation
import Regula.Checker.AxiomGate
import Regula.Checker.ResultProtocol
import Regula.Website

/-! # Rule-example detector adapters

Source-owned example adapters. These invoke the shipped compilation, admission,
policy and documentation detectors; they define no second linter. Diagnostic-only
inspection deliberately retains compiler warnings and never returns positive conformance.
Lean's compiler, process completion and filesystem observations remain trusted. -/
namespace Regula.Checker.RuleExamples
open Lean System

/-- Reuse the engine's owner for all completed and exceptional exits. A refused adapter
returns no qualifying result; no exception text is classified as a diagnostic. -/
private def stable {α : Type} (sources : Array ProducerReport.SourceBinding)
    (configuration : Array (FilePath × Option String)) (action : IO α) : IO α := do
  IO.ofExcept <| (← SourceBinding.withUnchanged sources configuration action).mapError (·.detail)

/-- A negative policy example may need inspection of an elaborated hole even though the
compiler warned. Keep that warning in the receipt; corrections use the ordinary strict gate. -/
unsafe def inspectNegative (repo path output : FilePath) : IO UInt32 := do
  let configuration ← SourceBinding.configuration repo (Manifest.defaultPath repo)
  let (scopeJson, findings) ← stable #[] configuration do
    let source ← IO.FS.readFile path
    let inventory ← Lake.surfaceInventory repo
    let sources := (← SourceBinding.capture inventory.moduleSources).push {
      moduleName := `RuleExample, path := path.toString, content := source }
    stable sources configuration do
      let manifest ← Manifest.loadFor (Manifest.defaultPath repo) inventory
      if let some lines ← Lake.buildChecked repo
          (Lake.claimedTargets manifest) "incrementally" then
        throw <| IO.userError ("example dependency build failed: " ++ "\n".intercalate lines.toList)
      withScratch repo "rule-policy-example" fun scratch => do
        let compilation ← IO.ofExcept <| (← SourceAudit.compile repo scratch
          { «module» := "RuleExample", source, rejectWarnings := false }).mapError (·.detail)
        unless SourceAudit.compilationPassed compilation do
          throw <|
              IO.userError
                  "policy example did not elaborate; compiler failure is not policy rejection"
        let inspected ← IO.ofExcept <| (← SourceAudit.inspectOutcome compilation inventory.leanPath
          inventory.leanSrcPath inventory.moduleSources inventory.ownership).mapError
              (·.detail)
        let declarations := inspected.report.declarations.qsort fun a b =>
            Name.quickLt a.name b.name
        let scope ← IO.ofExcept <|
          Policy.admitScope inspected.report.compilerCapability declarations inspected.transcripts
            inspected.report.imported
        let mut findings := #[]
        let index := Regula.Findings.declarationIndex declarations
        let helpers := scope.helpers
        -- The admitted inventory is exactly `declarations` (`ScopeContract`).
        for h : decl in scope.inventory.declarations do
          if let some id := Policy.ruleForMember decl (some .standardLogical) scope h then
            -- The finding names the declaration the author wrote (`Policy.subject_contract`).
            let named := Policy.subject decl scope h
            let location ← IO.ofExcept <| Regula.Findings.findingLocation index helpers named
                fun _ => some ⟨path.toString, source⟩
            let (sourceDeclaration, related) := Regula.Findings.attribution index helpers named
            findings := findings.push
                (← IO.ofExcept <| RuleDiagnostics.declarationFinding id named.name
              (Policy.subjectDetail decl scope h) location .freshFile (some "standard-logical")
              sourceDeclaration related)
        return (Json.mkObj [
          ("file", toJson path.toString), (SourceTexts.textKey, toJson source),
          ("configuration", toJson configuration), ("configurationRoot", toJson repo.toString),
          ("claim", toJson (some "standard-logical" : Option String)), ("execution", Json.null),
          ("diagnosticOnly", toJson true), ("compilerOutput", toJson compilation.process.output),
          ("report", inspected.report.resultJson),
          ("frontendTranscripts",
            toJson (inspected.transcripts.map (Frontend.transcriptResultJson ·)))], findings)
  ResultProtocol.write output scopeJson .freshFile
    (if findings.isEmpty then .classified else .rejected) findings
    (ResultProtocol.stagesOf .freshFile) [.discovery, .build, .admission, .declarationPolicy]
  let value ← ResultProtocol.readDocument output
  let request := ResultProtocol.requestJson "policyNegative" repo.toString path.toString none none
      configuration
  let origins ← IO.ofExcept <| Lake.configurationOrigins repo.toString
    (configuration.map fun (path, source) => (path.toString, source)) none repo
  ResultProtocol.writeDocument output ((value.setObjVal! "request" request).setObjVal! "effective"
    (Json.mkObj [("root", toJson repo.toString), ("configuration", toJson configuration),
      ("configurationOrigins", origins)]))
  return if findings.isEmpty then 0 else 1

/-- Capture emitted findings from the actual documentation driver in the same canonical
result envelope used by project/file consumers. The fresh copy owns build and fence artifacts. -/
unsafe def documentation (repo docsRoot output : FilePath) : IO UInt32 := do
  let requestedConfiguration ← SourceBinding.configuration repo (Manifest.defaultPath repo)
  let documents ← Documentation.captureMarkdown docsRoot
  if documents.isEmpty then throw <| IO.userError "empty example documentation tree"
  let sources := documents.map fun document => (FilePath.mk document.uri, document.source)
  let outcome ← (stable #[] requestedConfiguration <| withScratch repo "rule-document-example"
      fun scratch => do
    let copied ← Lake.copyProject repo (scratch / "project") scratch
    let copy := copied.project
    let configuration ← SourceBinding.configuration copy (Manifest.defaultPath copy)
    stable #[] configuration do
      let inventory ← Lake.checkCopiedWorkspace copied.root (some copied.selection)
        (← Lake.surfaceInventory copy)
      let manifest ← Manifest.loadFor (Manifest.defaultPath copy) inventory
      let projectSources ← SourceBinding.capture inventory.moduleSources
      let dependencies ← Snapshot.dependencies inventory
      stable projectSources configuration do
        let (buildProcess, buildResult) ← Lake.buildCheckedObservation copy
            (Lake.claimedTargets manifest) "fresh"
        if let some lines := buildResult then
          throw <| IO.userError
              ("example dependency build failed: " ++ "\n".intercalate lines.toList)
        let findings ← IO.mkRef (#[] : Array Finding)
        let classifications ← IO.mkRef (#[] : Array Documentation.Classification)
        let certificate ← IO.mkRef
            (none : Option ((c : RegulaPolicy.Claim) × RegulaPolicy.AcceptedRun c))
        let code ← Documentation.auditBuiltProject copy docsRoot inventory projectSources
            configuration dependencies documents (Acceptance.buildObservation buildProcess) 1 true
          (fun finding => findings.modify (·.push finding))
          (fun results => classifications.set (results.map Documentation.classification))
          (fun claim accepted => certificate.set (some ⟨claim, accepted⟩))
        let actual ← findings.get
        unless (code == 0) == actual.isEmpty do
          throw <| IO.userError "documentation completion/findings mismatch"
        return (code, actual, ← classifications.get, copy.toString, configuration,
            ← certificate.get, copied.configurationInputs)).toBaseIO
  -- Markdown is not a Lean module map. Preserve its own exact snapshots even on errors.
  Documentation.checkMarkdown docsRoot documents
  let (code, actual, classifications, configurationRoot, configuration, certificate, inputs) ← IO.ofExcept
      <| outcome.mapError (fun error => toString error)
  let completion ← if code == 0 then do
      let some ⟨_, accepted⟩ := certificate
        | throw <| IO.userError "documentation adapter lacks accepted evidence"
      let report := accepted.report
      unless report.claim.val.scope == .documentation
          (sources.map fun (path, source) => ⟨path.toString, source⟩) do
        throw <| IO.userError "documentation adapter request mismatch"
      -- Only an all-positive fence set is conforming evidence; expectations are classified.
      let account := Regula.Checker.Account.account accepted
      let fences := account.val.fences
      pure (if fences.positive > 0 && fences.compilerRejection + fences.policyRejection +
          fences.trustedTeaching == 0 then Regula.Checker.Account.Status.completed account else
                                            .classified)
    else pure (if actual.any (·.2.impact == .incomplete) then .incomplete else .rejected)
  ResultProtocol.write output (Json.mkObj [
    ("configuration", toJson configuration), ("configurationRoot", toJson configurationRoot),
    ("fences", toJson classifications),
    ("documents", toJson (sources.map fun (path, source) =>
      ResultProtocol.sourceJson ⟨path.toString, source⟩))])
    .documentationExample completion actual (ResultProtocol.stagesOf .documentationExample)
    (ResultProtocol.stagesOf .documentationExample)
  let value ← ResultProtocol.readDocument output
  let value := match certificate with
    | some ⟨_, accepted⟩ => value.setObjVal! "acceptance" (ResultProtocol.acceptedJson accepted)
    | none => value
  let request := ResultProtocol.requestJson "documentation" repo.toString docsRoot.toString none
      none requestedConfiguration (some inputs)
  let origins ← IO.ofExcept <| Lake.configurationOrigins repo.toString
    (requestedConfiguration.map fun (path, source) => (path.toString, source)) (some inputs)
    (FilePath.mk configurationRoot)
  ResultProtocol.writeDocument output ((value.setObjVal! "request" request).setObjVal! "effective"
    (Json.mkObj [("root", toJson configurationRoot), ("configuration", toJson configuration),
      ("configurationOrigins", origins)]))
  return code

/-- One rule-example production, as `Production.parse?` reads its arguments. -/
inductive Production where
  /-- `--policy-negative PROJECT SOURCE OUTPUT`. -/
  | policyNegative (repo source output : String)
  /-- `--documentation PROJECT DOCS OUTPUT`. -/
  | documentation (repo docs output : String)

/-- The production the arguments name, read from their whole shape, or none. -/
def Production.parse? : List String → Option Production
  | ["--policy-negative", repo, source, output] => some (.policyNegative repo source output)
  | ["--documentation", repo, docs, output] => some (.documentation repo docs output)
  | _ => none

/-- The result file a production writes. -/
def Production.output : Production → String
  | .policyNegative _ _ output | .documentation _ _ output => output

/-- Run one rule-example production, as the caller parsed it one time (`Production.parse?`), and
return its exit code: `--policy-negative PROJECT SOURCE OUTPUT` runs `inspectNegative`,
`--documentation PROJECT DOCS OUTPUT` runs `documentation`, and arguments that name no production
(`none`) throw the usage text. -/
unsafe def run (production : Option Production) : IO UInt32 := do
  match production with
  | some (.policyNegative repo source output) =>
      inspectNegative ⟨repo⟩ ⟨source⟩ ⟨output⟩
  | some (.documentation repo docs output) =>
      documentation ⟨repo⟩ ⟨docs⟩ ⟨output⟩
  | none =>
      throw <| IO.userError "usage: ruleExamples (--policy-negative PROJECT SOURCE | \
        --documentation PROJECT DOCS) OUTPUT"
end Regula.Checker.RuleExamples

/-- The exit code of an incomplete production: outside `axiomGate`'s exit codes 0 to 3, so the
qualifier (`RuleExampleQualification.qualify`, which admits only 0 to 3) never mistakes it for an
audit's own result. -/
private def productionIncomplete : UInt32 := 4

private unsafe def ruleExamplesEntry (production : Option Regula.Checker.RuleExamples.Production) :
    IO UInt32 := do
  try
    Regula.Checker.initializeLeanSearchPath
    Regula.Checker.RuleExamples.run production
  catch error =>
    IO.eprintln s!"rule example production incomplete: {error}"
    return productionIncomplete

/-- Qualification-only binary. `--injected-git-facts FACTS` is the internal
corpus-producer entry: it installs the runner's once-captured shared-dependency
Git facts (`Snapshot.GitFacts`), then runs either the exact `axiomGate` body
(`AxiomGate.entry`) or this binary's own modes. Facts only replace the Git part
of a capture whose exact request they answer; every source and configuration
byte is still read fresh, and the result is marked `"gitFacts": "injected"`. An empty table
answers nothing. The user-facing `axiomGate` never accepts them. -/
unsafe def ruleExamplesMain (args : List String) : IO UInt32 := do
  match args with
  | "--injected-git-facts" :: facts :: rest =>
    let loaded ← (do
      let json ← IO.ofExcept (Regula.Checker.PolicyCodec.parse (← IO.FS.readFile facts))
      IO.ofExcept (Lean.fromJson? (α := Array Regula.Checker.Snapshot.GitFacts) json)).toBaseIO
    match loaded with
    | .error error =>
      IO.eprintln s!"rule example production incomplete: injected git facts: {error}"
      return productionIncomplete
    | .ok table =>
      -- An empty table, from a project with no dependency, answers no capture request: every
      -- capture then observes Git itself.
      Regula.Checker.Snapshot.injectedGitFacts.set table
      let (code, output) ← match rest with
        | "axiomGate" :: gateArgs =>
          -- The result destination the audit's own plan resolved and marked, whatever the working
          -- directory, read after the audit ran.
          let code ← Regula.Checker.AxiomGate.entry gateArgs
          pure (code, (← Regula.Checker.AxiomGate.resultTarget.get).map (·.toString))
        | "--injected-git-facts" :: _ =>
          IO.eprintln "rule example production incomplete: repeated injected git facts"
          return productionIncomplete
        | _ =>
          -- One parse of the production, which both the run and the marker take.
          let production := Regula.Checker.RuleExamples.Production.parse? rest
          pure (← ruleExamplesEntry production, production.map (·.output))
      -- Mark the result so it cannot be mistaken for Git-observed output. The
      -- qualification-only result view keeps this field and admission ignores it. The file is
      -- marked only when it is a written result document (`ResultProtocol.readDocument`), and the
      -- marked document is written as every result document is (`ResultProtocol.writeDocument`).
      if let some path := output.filter (· != "") then
        unless ← System.FilePath.pathExists path do return code
        let marked ← (do
          let document ← Regula.Checker.ResultProtocol.readDocument path
          Regula.Checker.ResultProtocol.writeDocument path
            (document.setObjVal! "gitFacts" (.str "injected")) "injectedFactsMarker").toBaseIO
        if let .error error := marked then
          IO.eprintln s!"rule example production incomplete: injected-facts marker: {error}"
          return productionIncomplete
      return code
  | _ => ruleExamplesEntry (Regula.Checker.RuleExamples.Production.parse? args)

/-- The refusal of a production in a process without Lean's task manager, which the guard of the
executable runs (`Regula.TaskManager.guard`). For the `axiomGate` form it marks each destination
of the audit's arguments incomplete with `reason`, as the gate's own refusal does
(`AxiomGate.refuseWithoutTaskManager`); for a production that the arguments name
(`Production.parse?`) it marks its result file incomplete with `reason`. It returns the exit code of
an incomplete production. No production runs. -/
private def refuseProduction (reason : String) (args : List String) : IO UInt32 := do
  match args with
  | "--injected-git-facts" :: _ :: "axiomGate" :: gateArgs =>
    let _ ← Regula.Checker.AxiomGate.refuseWithoutTaskManager reason gateArgs
  | "--injected-git-facts" :: _ :: rest | rest =>
    if let some production := Regula.Checker.RuleExamples.Production.parse? rest then
      let marked ← (Regula.Checker.AxiomGate.invalidateResult ⟨production.output⟩ reason).toBaseIO
      if let .error error := marked then
        IO.eprintln s!"rule example production incomplete: could not mark \
          {production.output} incomplete: {error}"
  return productionIncomplete

/-- The `ruleExamples` executable: `ruleExamplesMain` on the command-line arguments. A process
without Lean's task manager is refused before any production starts: the result destinations that
the arguments name are marked incomplete with the reason, and the exit code is that of an
incomplete production (`Regula.TaskManager.guard`, `refuseProduction`). -/
unsafe def main : List String → IO UInt32 :=
  Regula.TaskManager.guard "ruleExamples" refuseProduction ruleExamplesMain

-- The removals that the compiled code of `main`, and of the initializers of the modules it links,
-- reaches are the filesystem observer's and those that `Regula.Removal.libraryRemovals` lists: the
-- build of this module fails otherwise (`Regula.Removal.checkProgram`).
run_cmd Regula.Removal.checkProgram

-- A program that needs Lean's task manager starts through its guard (`Regula.TaskManager.guard`),
-- and its refusal needs none: the build of this module fails otherwise
-- (`Regula.TaskManagerCheck.checkProgram`).
run_cmd Regula.TaskManagerCheck.checkProgram
