import Regula.DiagnosticCodec
import Regula.Checker.ResultProtocol
import Regula.Checker.SourceAudit
import Regula.Website
import RegulaCore.Guidance

/-! # Registry transport qualification

Focused transport and source-boundary qualification for CATALOG-01.
Universal identity/name laws are theorems, not inferred from these controls.
Canonical metadata motivation credits con-leche (Regula.RuleId). -/
open Lean Regula Regula.RegistryCodec

universe u v

-- This named set is the public theorem claim, not a module-discovery substitute.
run_cmd do
  for name in #[``RuleId.parse_spelling, ``RuleId.spelling_injective, ``RuleId.mem_all,
      ``RuleId.all_nodup, ``RuleId.route_injective, ``mode_roundtrip, ``rule_roundtrip,
      ``nameParts_roundtrip, ``name_roundtrip, ``mem_firedRules, ``firedRules_nodup,
      ``Regula.sortFindings_entries, ``Regula.sortFindings_perm,
      ``Regula.Checker.ResultProtocol.stagesOf_required,
      ``Regula.Checker.ResultProtocol.notRun_completedStages_eq_nil_iff,
      ``Regula.Checker.ResultProtocol.stagesOf_ordered,
          ``Regula.Checker.ResultProtocol.withDocs_ordered,
      ``Regula.Checker.ResultProtocol.completedStages_idem,
      ``Regula.Checker.ResultProtocol.guidanceFields_recorded,
      ``Regula.Checker.ResultProtocol.parseStage_stageName] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => #[`propext, `Quot.sound, `Classical.choice].contains ax) do
      throwError "registry theorem {name} exceeds Standard-Logical: {axioms}"

private def require (ok : Bool) (claim : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"registry qualification failed: {claim}"

private def succeeded {ε : Type u} {α : Type v} : Except ε α → Bool
  | .ok _ => true | .error _ => false

/-- The registry transport qualification that acceptance runs with `lean --run`: it checks
every rule's descriptor codec, the embedded example pairs against their corpus files, the
committed agent skill, and fixed accept and refuse controls for registry, page, source,
result, diagnostic and example admission, throwing on the first failed check and printing
`PASS` otherwise. These controls are observations, not proofs of the laws. -/
def main : IO Unit := do
  let producer := Regula.Checker.ResultProtocol.producer
  let manifest := registryJson producer
  -- Exhaustive checks over the genuinely closed 22-rule vocabulary.
  for id in RuleId.all do
    require (succeeded (parseDescriptor (descriptorJson id))) s!"descriptor {id}"
    require (!(descriptor id).title.isEmpty && !(descriptor id).normativeClauses.isEmpty)
      s!"metadata completeness {id}"
    require (!succeeded (parseDescriptor ((descriptorJson id).setObjVal! "extra" .null)))
      s!"unknown field {id}"
  require (!succeeded (parseRule (.str "RG9999"))) "unknown rule"
  require (!succeeded (parseMode "fresh")) "unknown mode"
  require
      (!succeeded
          (validateRegistry producer (manifest.setObjVal! "schemaVersion" (toJson (2 : Nat)))))
    "superseded registry version"
  -- The embedded example pairs are exactly the corpus files the rule-example campaign runs:
  -- this rejects a stale build and an `include_str` of the wrong file.
  for id in RuleId.all do
    let e := (descriptor id).examples
    require ((← IO.FS.readFile (e.compliantPath id)) == e.compliant)
        s!"{id} compliant example is {e.compliantPath id}"
    require ((← IO.FS.readFile (e.noncompliantPath id)) == e.noncompliant)
      s!"{id} noncompliant example is {e.noncompliantPath id}"
  -- The committed agent skill is the generated briefing of this build.
  require ((← IO.FS.readFile ".agents/skills/regula/SKILL.md") == Regula.Guidance.skill)
    "committed .agents/skills/regula/SKILL.md is current (regenerate with `lake exe regula skill`)"
  require
      (!succeeded (validateRegistry producer (manifest.setObjVal! "sourceRevision" (.str "stale"))))
    "stale revision"
  require
      (!succeeded
          (validateRegistry producer
              (manifest.setObjVal! "rules"
                  (toJson [descriptorJson .projectAxiom, descriptorJson .projectAxiom]))))
    "duplicate and missing IDs"
  let page : RegistryCodec.Page := ⟨.projectAxiom, RuleId.projectAxiom.route, true, true⟩
  require (succeeded (validatePages producer manifest [.projectAxiom] [page]))
      "actual one-page scope"
  require (!succeeded (validatePages producer manifest [.projectAxiom] [])) "missing page"
  require (!succeeded (validatePages producer manifest [.projectAxiom] [page, page]))
      "duplicate page"
  require
      (!succeeded
          (validatePages producer manifest [.projectAxiom] [{ page with route := "wrong" }]))
              "wrong route"
  require
      (!succeeded
          (validatePages producer manifest [.projectAxiom] [{ page with checkedExample := false }]))
              "unchecked example"
  require (succeeded (validatePages producer manifest [.moduleDocumentation]
    [⟨.moduleDocumentation, RuleId.moduleDocumentation.route, true, true⟩]))
        "implemented module-doc detector"
  let emoji := String.singleton (Char.ofNat 0x1F600)  -- a non-BMP character
  let candidate : SourceCandidate :=
    ⟨⟨"qualification://unicode", "α" ++ emoji ++ "\r\nx"⟩, ⟨0, 9⟩, ⟨2, 6⟩⟩
  let source ← IO.ofExcept (admitSource candidate)
  require (source.selectionLsp.start.line == 0 && source.selectionLsp.start.character == 1 &&
    source.selectionLsp.end.line == 0 && source.selectionLsp.end.character == 3)
        "UTF-8 to UTF-16 conversion"
  require (!succeeded (admitSource { candidate with selection := ⟨3, 6⟩ })) "mid-character offset"
  require (!succeeded (admitSource { candidate with selection := ⟨6, 2⟩ })) "reversed range"
  require (!succeeded (admitSource { candidate with full := ⟨0, 99⟩ })) "out-of-bounds range"
  require (!succeeded (admitSource { candidate with full := ⟨3, 9⟩ }))
      "selection outside full range"
  let name := Name.num (.str .anonymous "a.b") 2
  let d ← IO.ofExcept <| makeDiagnostic .projectAxiom ⟨name, "project-axiom"⟩
    (.source source) .freshFile (some "standard-logical") .violation
  let json := diagnosticJson ⟨.projectAxiom, d⟩
  let fileStages := Regula.Checker.ResultProtocol.stagesOf .freshFile
  -- Every writer records the request of a result with a mode.
  let requested (kind : String) (j : Json) : Json := j.setObjVal! "request"
    (Regula.Checker.ResultProtocol.requestJson kind "control" "control" none none #[])
  let envelope := requested "file" <| Regula.Checker.ResultProtocol.resultJson (.str "control")
    .freshFile .rejected #[⟨.projectAxiom, d⟩, ⟨.projectAxiom, d⟩] fileStages fileStages #[]
  let partialRun := requested "file" <| Regula.Checker.ResultProtocol.resultJson (.str "control")
    .freshFile .rejected #[⟨.projectAxiom, d⟩] fileStages
    (fileStages.filter (· ∉ [.execution, .origin])) #[]
  let projectStages := Regula.Checker.ResultProtocol.stagesOf .freshProject
  let omission ← IO.ofExcept <| Regula.Findings.contextFinding .coverage "control"
    "surface-omission: Lake module M was not elaborated" .freshProject .incomplete
  let blockedRun := requested "project" <| Regula.Checker.ResultProtocol.resultJson
    (.str "control") .freshProject .incomplete #[omission] projectStages projectStages #[]
  -- A run whose documentation scan found nothing, and a configuration refusal.
  let unscanned := requested "projectWithDocs" <| Regula.Checker.ResultProtocol.resultJson
    (.str "control") .freshProject .incomplete #[]
    (projectStages ++ Regula.Checker.ResultProtocol.documentationStages) projectStages #[]
  let refusal ← IO.ofExcept <| Regula.Findings.contextFinding .configuration "control"
    "manifest-schema: surfaces[0].claim must be one of kernel-only, choice-free, standard-logical"
    .freshProject .violation
  let refused := requested "project" <| Regula.Checker.ResultProtocol.resultJson
    (.str "control") .freshProject .rejected #[refusal] projectStages [] #[]
  -- A `--with-docs` run whose project stages found a violation, so its documentation stages
  -- never started, although its writer recorded them.
  let withDocsStages := projectStages ++ Regula.Checker.ResultProtocol.documentationStages
  let projectFinding ← IO.ofExcept <| makeDiagnostic .moduleDocumentation ⟨"M", "missing docs"⟩
    (.module `M) .freshProject none .violation
  let projectRejected := requested "projectWithDocs" <| Regula.Checker.ResultProtocol.resultJson
    (.str "control") .freshProject .rejected
        #[⟨.moduleDocumentation, projectFinding⟩] withDocsStages
    withDocsStages #[]
  let allStageNames := toJson (projectStages.map Regula.Checker.ResultProtocol.stageName)
  let claimAllRan (j : Json) (stages : Json) : Json :=
    ((j.setObjVal! "stagesCompleted" stages).setObjVal! "stagesNotRun"
      (toJson ([] : List Json))).setObjVal! "complete" (.bool true)
  let admit := Regula.Checker.ResultProtocol.admitGuidance
  require (succeeded (admit envelope)) "result guidance admission"
  require (succeeded (admit partialRun)) "partial result guidance admission"
  require (succeeded (admit blockedRun)) "blocked result guidance admission"
  require (succeeded (admit unscanned)) "unscanned documentation admission"
  require (succeeded (admit refused)) "configuration refusal admission"
  require
      ((unscanned.getObjVal? "stagesNotRun").toOption == some (toJson ["documentScan", "example"]))
    "an empty documentation scan leaves the documentation stages not run"
  require (!succeeded (admit (claimAllRan unscanned (unscanned.getObjValD "stagesCompleted"))))
    "unscanned run claimed complete"
  require (!succeeded (admit (claimAllRan unscanned (unscanned.getObjValD "stages"))))
    "finding-free incomplete result with every stage recorded as run"
  require (!succeeded (admit (claimAllRan refused allStageNames)))
      "configuration refusal claimed complete"
  require (succeeded (admit projectRejected)) "rejected documentation run admission"
  require
      ((projectRejected.getObjVal? "stagesNotRun").toOption == some
          (toJson ["documentScan", "example"]))
    "a project finding leaves the documentation stages not run"
  -- The shrink-stages edit of that run with its request deleted.
  let unrequested := Regula.Checker.ResultProtocol.resultJson (.str "control") .freshProject
    .rejected #[⟨.moduleDocumentation, projectFinding⟩] projectStages projectStages #[]
  require (succeeded (admit (requested "project" unrequested))) "requested project run admission"
  require (!succeeded (admit unrequested)) "result with a mode but no request"
  require (!succeeded (admit (claimAllRan projectRejected (toJson (withDocsStages.map
    Regula.Checker.ResultProtocol.stageName))))) "unstarted documentation stages reported as run"
  require (!succeeded (admit (claimAllRan (projectRejected.setObjVal! "stages" allStageNames)
    allStageNames))) "documentation stages dropped from a documentation request"
  require (!succeeded (admit ((claimAllRan refused (toJson ([] : List Json))).setObjVal! "stages"
    (toJson ([] : List Json))))) "required stages dropped"
  require ((blockedRun.getObjVal? "stagesNotRun").toOption ==
      some
          (toJson ["admission", "declarationPolicy", "execution", "transcript", "history", "origin",
        "documentationPresence"]))
    "an incomplete finding blocks its stage and every later stage"
  require (!succeeded (admit (claimAllRan blockedRun allStageNames)))
      "blocked stages reported as run"
  require (!succeeded (admit (blockedRun.setObjVal! "stagesNotRun" (toJson ["history"]))))
    "blocked stage reported as run"
  require (!succeeded (admit (envelope.setObjVal! "rules" (toJson ([] : List Json)))))
      "missing rule guidance"
  require (!succeeded (admit (envelope.setObjVal! "complete" (.bool false)))) "wrong completeness"
  require (!succeeded (admit (partialRun.setObjVal! "complete" (.bool true))))
      "partial run claimed complete"
  require (!succeeded (admit (partialRun.setObjVal! "stagesNotRun" (toJson ([] : List Json)))))
      "omitted stages"
  require
      (!succeeded
          (admit (partialRun.setObjVal! "stagesCompleted" (toJson ["discovery", "linking"]))))
    "unknown stage"
  require (!succeeded (admit (partialRun.setObjVal! "status" (.str "completed"))))
    "completed result with stages not run"
  require (!succeeded (admit (envelope.setObjVal! "schemaVersion" (toJson (2 : Nat)))))
      "superseded result schema"
  require (!succeeded (DiagnosticCodec.parseDiagnostic (json.setObjVal! "remedy" (.str "stale"))))
      "stale remedy"
  let parsed ← IO.ofExcept <| DiagnosticCodec.parseDiagnostic json
  require (diagnosticJson parsed == json) "diagnostic transport control"
  require (!succeeded (DiagnosticCodec.parseDiagnostic (json.setObjVal! "extra" .null)))
      "unknown diagnostic field"
  require
      (!succeeded
          (DiagnosticCodec.parseDiagnostic (json.setObjVal! "mode" (.str "serializedGraph"))))
              "unsupported diagnostic mode"
  require (!succeeded (DiagnosticCodec.parseDiagnostic (json.setObjVal! "impact" (.str "pass"))))
      "unknown impact"
  require
      (!succeeded (DiagnosticCodec.parseDiagnostic (json.setObjVal! "severity" (.str "hidden"))))
          "unknown severity"
  require (succeeded (makeDiagnostic .moduleDocumentation ⟨"M", "missing docs"⟩
    (.module `M) .freshProject none .violation)) "module-doc detector admission"
  let native ← IO.ofExcept d.nativeMessage
  require (native.pos.line == 1 && native.pos.column == 1 &&
    native.endPos == some ⟨1, 2⟩) "native codepoint coordinates"
  require ((← native.data.toString) == d.text) "native/text agreement"
  let compilation : Regula.Checker.SourceAudit.Compilation := {
    spec := { «module» := "Control", source := "" }
    sourcePath := "/control.lean", oleanPath := "/control.olean", ileanPath := "/control.ilean"
    process := { exitCode := 1, stdout := "/control.lean:1:0: error: intended", stderr := "" } }
  require (Regula.Checker.SourceAudit.sourceDiagnosticFailure compilation)
      "completed source diagnostic"
  require (!Regula.Checker.SourceAudit.sourceDiagnosticFailure
    { compilation with process := { compilation.process with exitCode := 137 } })
        "termination is incomplete"
  require (!Regula.Checker.SourceAudit.sourceDiagnosticFailure
    { compilation with process := { compilation.process with stdout := "compiler crashed" } })
        "crash is incomplete"
  require (succeeded (Website.validateExample (.policyRejection .projectAxiom "project-axiom")
    (.checked #[⟨.projectAxiom, d⟩] false))) "policy rejection after elaboration"
  require
      (!succeeded
          (Website.validateExample (.compilerRejection "error") (.incomplete "worker crashed")))
    "crash cannot satisfy negative example"
  IO.println "registry qualification: PASS (closed metadata, transport, source and mode boundaries)"
