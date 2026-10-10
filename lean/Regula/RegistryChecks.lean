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
      ``nameParts_roundtrip, ``name_roundtrip, ``printsExactly_iff, ``printedNameJson_roundtrip,
      ``printedNameJson_eq_str_iff, ``parsePrintedNameJson_str, ``mem_firedRules,
      ``firedRules_nodup, ``Regula.sortFindings_entries, ``Regula.sortFindings_perm,
      ``Regula.Feedback.flatten_runs, ``Regula.groupFindings_flatten,
      ``Regula.groupFindings_perm, ``Regula.groupEntry_alone,
      ``Regula.Findings.declarationIndex_get, ``Regula.Findings.chainEnd_eq_some_iff,
      ``Regula.Findings.sourceName?_eq_some_iff, ``Regula.Findings.sourceName?_source,
      ``Regula.Findings.stepOf_eq_some_iff, ``Regula.Findings.helperStep_base,
      ``Regula.Findings.declarationFinding_groupUnder?, ``Regula.Feedback.flatten_runs_go,
      ``Regula.GeneratedFamily.mem_all,
      ``Regula.Checker.ResultProtocol.stagesOf_required,
      ``Regula.Checker.ResultProtocol.notRun_completedStages_eq_nil_iff,
      ``Regula.Checker.ResultProtocol.stagesOf_ordered,
          ``Regula.Checker.ResultProtocol.withDocs_ordered,
      ``Regula.Checker.ResultProtocol.completedStages_idem,
      ``Regula.Checker.ResultProtocol.guidanceFields_recorded,
      ``Regula.Checker.ResultProtocol.parseStage_stageName,
      ``Regula.SourceTexts.expand_intern, ``Regula.SourceTexts.intern_isOk_iff,
      ``Regula.SourceTexts.intern_table, ``Regula.SourceTexts.expand_texts,
      ``Regula.SharedExecution.same_eq, ``Regula.SharedExecution.restoreMembers_mapMembers,
      ``Regula.SharedExecution.restore?_internValue, ``Regula.SharedExecution.expand_intern,
      ``Regula.SharedExecution.slots_intern, ``Regula.SharedExecution.read_write,
      ``Regula.Checker.ResultProtocol.resultJson_slots] do
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
  -- Where no classification line is printed (the editor, the self-audit and a documentation
  -- example), the detail of a finding of the shared-test rule names the shared tests that the
  -- record holds, and the detail of another rule is its applicability.
  let sharing : RegulaPolicy.Declaration := { RegulaPolicy.witnessDeclaration .«definition» with
    executableContract := some { root := `check, requirement := "", failure := none,
                                 shared := { booleans := #[`small] } } }
  require (Regula.Findings.ruleDetail .sharedTest sharing ==
    "shared-test shared-booleans=[\"small\"]") "shared-test detail names the shared tests"
  require (Regula.Findings.ruleDetail .executableContract sharing == "executable-contract")
    "detail of a rule with no names"
  -- Exhaustive checks over the genuinely closed 24-rule vocabulary.
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
          (validateRegistry producer
            (manifest.setObjVal! "schemaVersion" (toJson (registrySchemaVersion - 1)))))
    "superseded registry version"
  -- The embedded example pairs are exactly the corpus files the rule-example campaign runs:
  -- this rejects a stale build and an `include_str` of the wrong file.
  for id in RuleId.all do
    let e := (descriptor id).examples
    require ((← IO.FS.readFile (e.compliantPath id)) == e.compliant)
        s!"{id} compliant example is {e.compliantPath id}"
    require ((← IO.FS.readFile (e.noncompliantPath id)) == e.noncompliant)
      s!"{id} noncompliant example is {e.noncompliantPath id}"
  -- The committed agent skill is the generated briefing of an unreleased build, which every
  -- commit of `main` is (`Regula.Guidance.skill_unreleased`); the release commit keeps the file.
  require ((← IO.FS.readFile ".agents/skills/regula/SKILL.md") == Regula.Guidance.skillIn .dev)
    "committed .agents/skills/regula/SKILL.md is current (regenerate with `lake exe regula skill`)"
  -- The adoption guide quotes, on one line, the RG1005 guidance that names the families of
  -- declarations Lean generates, rendered from the list the checker runs (`GeneratedFamily.all`).
  let some families := (descriptor .profileExceeded).rewrites.getLast?
    | throw <| IO.userError "registry qualification failed: RG1005 names no generated families"
  require (((← IO.FS.readFile "docs/guides/adoption.md").splitOn s!"\n> {families}\n").length == 2)
    "docs/guides/adoption.md quotes the RG1005 generated-family guidance once, verbatim"
  require
      (!succeeded (validateRegistry producer (manifest.setObjVal! "sourceRevision" (.str "stale"))))
    "stale revision"
  require
      (!succeeded
          (validateRegistry producer
              (manifest.setObjVal! "rules"
                  (toJson [descriptorJson .projectAxiom, descriptorJson .projectAxiom]))))
    "duplicate and missing IDs"
  let page : RegistryCodec.Page := ⟨.projectAxiom, RuleId.projectAxiom.route, true⟩
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
  let d ← IO.ofExcept <| makeDiagnostic .projectAxiom
    ({ declaration := name, sourceDeclaration := none, detail := "project-axiom" } :
      DeclarationArguments)
    (.source source) .freshFile (some "standard-logical") .violation
  let json := diagnosticJson ⟨.projectAxiom, d⟩
  -- Printed names: Lean's printer and parser agree on an escaped component, so the text stands
  -- for the name; a component containing `»` cannot be escaped, so its parts stand for it.
  require ((json.getObjValD "arguments").getObjValD "declaration" == .str "«a.b».2")
    "escaped name as its printed text"
  let unescapable := Name.str (.str .anonymous "Acorn") "a»b"
  let generated ← IO.ofExcept <| makeDiagnostic .profileExceeded
    ({ declaration := unescapable, sourceDeclaration := some `Acorn, detail := "choice-free" } :
      DeclarationArguments) (.module `Acorn.Admission) .freshProject (some "kernel-only") .violation
  let generatedJson := diagnosticJson ⟨.profileExceeded, generated⟩
  require ((generatedJson.getObjValD "arguments").getObjValD "declaration" == nameJson unescapable &&
    (generatedJson.getObjValD "arguments").getObjValD "sourceDeclaration" == .str "Acorn" &&
    (generatedJson.getObjValD "location").getObjValD "name" == .str "Acorn.Admission")
    "components only for a name Lean's parser does not read back"
  let reparsed ← IO.ofExcept <| DiagnosticCodec.parseDiagnostic generatedJson
  require (diagnosticJson reparsed == generatedJson && reparsed.sourceDeclaration? == some `Acorn)
    "generated finding transport control"
  let printedOnly := generatedJson.setObjVal! "arguments" (Json.mkObj [
    ("declaration", .str unescapable.toString), ("sourceDeclaration", .str "Acorn"),
    ("detail", .str "choice-free")])
  require (!succeeded (DiagnosticCodec.parseDiagnostic printedOnly))
    "printed text for a name it does not denote"
  let structural := json.setObjVal! "arguments" ((json.getObjValD "arguments").setObjVal!
    "declaration" (nameJson name))
  require (!succeeded (DiagnosticCodec.parseDiagnostic structural))
    "components for a name its printed text denotes"
  let fileStages := Regula.Checker.ResultProtocol.stagesOf .freshFile
  -- Every writer records the request of a result with a mode.
  let requested (kind : String) (j : Json) : Json := j.setObjVal! "request"
    (Regula.Checker.ResultProtocol.requestJson kind "control" "control" none none #[])
  let envelope := requested "file" <| Regula.Checker.ResultProtocol.resultJson (.str "control")
    .freshFile .rejected #[⟨.projectAxiom, d⟩, ⟨.projectAxiom, d⟩] fileStages fileStages #[]
  -- Source texts stored once. `SourceTexts.expand_intern` and `intern_table` prove the laws for
  -- every document; these observe the wiring they do not cover: that the document `resultJson`
  -- builds is one `intern` writes, that its locations carry `sourceText` members, and what the
  -- reader does with a document `intern` did not write.
  let written ← IO.ofExcept (SourceTexts.intern envelope)
  let location (j : Json) (position : Nat) : Json :=
    (((j.getObjValD "diagnostics").getArrVal? position).toOption.getD .null).getObjValD "location"
  require (written.getObjValD SourceTexts.tableKey == toJson #[candidate.snapshot.source])
    "two findings in one file store its text once"
  require ((location written 0).getObjValD SourceTexts.textKey == toJson (0 : Nat) &&
    (location written 1).getObjValD SourceTexts.textKey == toJson (0 : Nat))
    "a written location names its text by index"
  let expanded ← IO.ofExcept (SourceTexts.expand written)
  require (expanded == envelope) "the reader recovers the document written"
  require (!succeeded (SourceTexts.intern written)) "a written document is not written again"
  require (!succeeded (SourceTexts.expand envelope)) "an unwritten document is not expanded"
  require (!succeeded (SourceTexts.expand
    (written.setObjVal! SourceTexts.tableKey (toJson (#[] : Array String)))))
    "sourceText index outside the stored texts"
  require (!succeeded (SourceTexts.expand (written.setObjVal! SourceTexts.tableKey
    (toJson #[candidate.snapshot.source, candidate.snapshot.source])))) "stored text repeated"
  require (!succeeded (SourceTexts.expand (written.setObjVal! SourceTexts.tableKey
    (toJson #[(0 : Nat)])))) "stored text that is not a string"
  -- Execution accounts stored once. `SharedExecution.expand_intern` and `read_write` prove that
  -- the reader recovers every document, whatever the writer proposes; these observe what they
  -- do not cover: that the writer's proposal is kept for accounts of the form the collector
  -- produces, built or parsed, so two roots store what both reach once, that the reader returns
  -- the built account from a parsed shared form, whose object trees are not the written ones,
  -- what the writer does with an account of another form or without roots, and what the reader
  -- does with a malformed one.
  let evidence ← IO.ofExcept
    (RegulaPolicy.admitBoundaryEvidence .partialComputation .trusted none none)
  let account (root : Name) (visits : Array RegulaPolicy.ExecutionVisit) :
      RegulaPolicy.ExecutionRoot := {
    name := root, «module» := `M
    boundaries := #[{
      occurrence := 0, name := `shared, «module» := `M, boundary := .partialComputation,
      account := evidence, owned := true, replacement := none, compilerCallers := #[root] }]
    unresolved := #[]
    compilerEdges := #[(root, `shared)]
    closure := {
      nodes := RegulaPolicy.canonicalNames #[root, `shared]
      visits
      logicalEdges := #[(root, `shared)]
      requiredCode := RegulaPolicy.canonicalNames #[root, `shared] } }
  let walked (root : Name) : Array RegulaPolicy.ExecutionVisit :=
    #[{ name := root, moduleName := some `M, parent := none },
      { name := `shared, moduleName := some `M, parent := some 0 }]
  let report (accounts : Array RegulaPolicy.ExecutionRoot) : Json :=
    Json.mkObj [(SharedExecution.accountKey, toJson accounts)]
  let logical := report #[account `first (walked `first), account `second (walked `second)]
  let stored := SharedExecution.intern ExecutionShare.proposals logical
  let storedAccount := stored.getObjValD SharedExecution.accountKey
  let count (member : String) : Option Nat :=
    (storedAccount.getObjValD member).getArr?.toOption.map (·.size)
  require (SharedExecution.derivedOnly storedAccount)
    "accounts the walk reproduces are stored as derived root entries"
  require (count "names" == some 3 && count "boundaries" == some 1 &&
    count "compilerEdges" == some 2 && count "logicalEdges" == some 2)
    "two roots store the name and boundary both reach once"
  require ((SharedExecution.expand stored).toOption == some logical)
    "the reader rebuilds each root's account"
  -- The JSON parser builds an account's objects as the codec and the reader do, so a document
  -- that was read back is written in the shared form again.
  let reread := Regula.Checker.ResultProtocol.normalize logical
  require (SharedExecution.same reread logical)
    "a parsed account is the same value as the built one"
  require (SharedExecution.derivedOnly ((SharedExecution.intern ExecutionShare.proposals
      reread).getObjValD SharedExecution.accountKey))
    "a parsed account is stored as derived root entries"
  require (match SharedExecution.expand (Regula.Checker.ResultProtocol.normalize stored) with
    | .ok restored => SharedExecution.same restored logical
    | .error _ => false)
    "the reader rebuilds the built account from a parsed shared form"
  let rootless := report #[]
  let storedNone := SharedExecution.intern ExecutionShare.proposals rootless
  require
    (SharedExecution.field? SharedExecution.rootsKey
        (storedNone.getObjValD SharedExecution.accountKey) == some (Json.arr #[]) &&
      (SharedExecution.expand storedNone).toOption == some rootless)
    "an environment without roots is stored as a shared form without roots"
  -- Visits the walk does not produce: the root's entry holds its account as it is, and the
  -- reader still returns the account.
  let other := report #[account `first #[{ name := `shared, moduleName := some `M, parent := none },
      { name := `first, moduleName := some `M, parent := some 0 }],
    account `second (walked `second)]
  let full := SharedExecution.intern ExecutionShare.proposals other
  let entries := (SharedExecution.field? SharedExecution.rootsKey
    (full.getObjValD SharedExecution.accountKey)).bind SharedExecution.array?
  require
    (entries.map (·.map fun entry => (SharedExecution.field? "explicit" entry).isSome) ==
        some #[true, false] &&
      (SharedExecution.expand full).toOption == some other)
    "an account the walk does not reproduce is written as `explicit` and read back"
  let claim := Json.mkObj [(SharedExecution.accountKey, .str "checked")]
  require (SharedExecution.intern ExecutionShare.proposals claim == claim &&
    (SharedExecution.expand claim).toOption == some claim)
    "an execution member that is not an account is kept"
  require (!succeeded (SharedExecution.expand (stored.setObjVal! SharedExecution.accountKey
    (storedAccount.setObjVal! "names" (toJson (#[] : Array Json))))))
    "a shared account whose names do not cover its indices is refused"
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
