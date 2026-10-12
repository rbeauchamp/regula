import Regula.DiagnosticCodec
import Regula.Checker.ResultProtocol
import Regula.Checker.SourceAudit
import Regula.Checker.Workspace
import Regula.Website
import RegulaCore.Guidance
import Regula.Campaigns.Workflow
import Regula.Checker.Lake

/-! # Registry transport qualification

Focused transport and source-boundary qualification for CATALOG-01.
Universal identity/name laws are theorems, not inferred from these controls.
Canonical metadata motivation credits con-leche (Regula.RuleId). -/
open Lean Regula Regula.RegistryCodec

universe u v

-- This named set is the public theorem claim, not a module-discovery substitute.
run_cmd do
  let names := #[``RuleId.parse_spelling, ``RuleId.spelling_injective, ``RuleId.mem_all,
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
      ``Regula.Checker.ResultProtocol.statusAgrees_completed,
      ``Regula.Checker.ResultProtocol.tally_rejected_iff,
      ``Regula.Checker.ResultProtocol.statusAgrees_observation,
      ``Regula.Checker.ResultProtocol.statusAgrees_iff,
      ``Regula.Checker.ResultProtocol.guidanceFields_keys,
      ``Regula.Checker.ResultProtocol.notRun_self,
      ``Regula.Checker.ResultProtocol.guidanceVerdict_eq_ok_iff,
      ``Regula.Checker.ResultProtocol.guidanceVerdict_completed,
      ``Regula.Checker.ResultProtocol.guidanceVerdict_unblocked,
      ``Regula.Checker.ResultProtocol.membersConform_iff,
      ``Regula.Checker.ResultProtocol.readGuidance_eq_ok,
      ``Regula.Checker.ResultProtocol.admitGuidance_eq_ok_iff,
      ``Regula.Checker.ResultProtocol.admitGuidance_completed,
      ``Regula.Checker.ResultProtocol.mapM_eq_ok_nil,
      ``Regula.Checker.ResultProtocol.admitGuidance_completed_diagnostics,
      ``Regula.Checker.ResultProtocol.admitDocument_eq_ok_iff,
      ``Regula.Checker.ResultProtocol.inRunOrder_iff,
      ``Regula.Checker.ResultProtocol.inRunOrder_sortFindings,
      ``Regula.Checker.ResultProtocol.mapMembers_mapMembers,
      ``Regula.Checker.ResultProtocol.admitDocument_read,
      ``Regula.Checker.ResultProtocol.admitDocument_of_forms,
      ``Regula.Checker.ResultProtocol.admitDocument_write,
      ``Regula.Checker.ResultProtocol.admitDocument_writeAs,
      ``Regula.ExecutionShare.getObjVal?_mkObj_last,
      ``Regula.ExecutionShare.getObjVal?_mkObj_absent,
      ``Regula.ExecutionShare.rootEntries?_sharedForm,
      ``Regula.ExecutionShare.rootEntries?_verbatim,
      ``Regula.ExecutionShare.rootEntries?_arr, ``Regula.ExecutionShare.isExplicit_explicitEntry,
      ``Regula.ExecutionShare.isExplicit_derivedEntry, ``Regula.ExecutionShare.sharedAs_explicitAt,
      ``Regula.ExecutionShare.sharedAs_fitted, ``Regula.ExecutionShare.sharedAs_self,
      ``Regula.ExecutionShare.fitted_self, ``Regula.ExecutionShare.internValue_congr,
      ``Regula.ExecutionShare.formLike_internValue, ``Regula.ExecutionShare.formLike_sharedAs,
      ``Regula.ExecutionShare.isExplicit_canon_mkObj, ``Regula.ExecutionShare.explicitAt_map_canon,
      ``Regula.ExecutionShare.rootEntries?_canon_sharedForm, ``Regula.ExecutionShare.fitted_shared,
      ``Regula.ExecutionShare.sharedAs_shared, ``Regula.ExecutionShare.kinds_canon,
      ``Regula.ExecutionShare.canonical_mapTexts, ``Regula.ExecutionShare.canonical_mapMembers,
      ``Regula.ExecutionShare.canonical_setTable, ``Regula.ExecutionShare.firstRecovered_mem,
      ``Regula.ExecutionShare.canonical_internValue, ``Regula.ExecutionShare.canonical_proposals,
      ``Regula.ExecutionShare.canonical_write,
      ``Regula.JsonCanon.mkObj_eq, ``Regula.JsonCanon.members_treeOf, ``Regula.JsonCanon.treeOf_map,
      ``Regula.JsonCanon.sortMembers_increasing, ``Regula.JsonCanon.sortMembers_of_increasing,
      ``Regula.JsonCanon.canonical_canon, ``Regula.JsonCanon.Canonical.canon_eq,
      ``Regula.JsonCanon.Canonical.regular, ``Regula.JsonCanon.Regular.canon_agree,
      ``Regula.JsonCanon.Canonical.map, ``Regula.JsonCanon.getObjVal?_canon,
      ``Regula.JsonCanon.Canonical.single, ``Regula.JsonCanon.canonAll_eq,
      ``Regula.JsonCanon.insertMemberTR_eq, ``Regula.JsonCanon.insertMember_eq_insertMemberImpl,
      ``Regula.JsonCanon.treeOf_concat, ``Regula.JsonCanon.contains_treeOf,
      ``Regula.Checker.JsonRoundTrip.strCore_text, ``Regula.Checker.JsonRoundTrip.num_text,
      ``Regula.Checker.JsonRoundTrip.value_text, ``Regula.Checker.JsonRoundTrip.parse_compress_ws,
      ``Regula.Checker.JsonRoundTrip.parse_compress_canonical_ws,
      ``Regula.Checker.JsonRoundTrip.parse_compress,
      ``Regula.Checker.JsonRoundTrip.parse_compress_canonical,
      ``Regula.Checker.ResultProtocol.admitDocument_parse_encodeDocument,
      ``Regula.JsonAgreement.Regular.agree_self,
      ``Regula.Checker.ResultProtocol.parseStage_stageName,
      ``Regula.SourceTexts.expand_intern, ``Regula.SourceTexts.intern_isOk_iff,
      ``Regula.SourceTexts.intern_table, ``Regula.SourceTexts.expand_texts,
      ``Regula.SharedExecution.same_eq, ``Regula.SharedExecution.restoreMembers_mapMembers,
      ``Regula.SharedExecution.restore?_internValue, ``Regula.SharedExecution.expand_intern,
      ``Regula.SharedExecution.slots_intern, ``Regula.SharedExecution.read_write,
      ``Regula.SharedExecution.Graph.bounds, ``Regula.SharedExecution.Graph.walk_accepted,
      ``Regula.SharedExecution.walk_eq, ``Regula.ExecutionShare.walk_agree,
      ``Regula.Checker.ResultProtocol.resultJson_slots]
  let some table := RegulaPolicy.KernelAxioms.reachedAxiomTable (← Lean.getEnv) names
    | throwError "the axiom search ran out of fuel"
  for name in names do
    let some axioms := table[name]? | throwError "the axiom search did not reach {name}"
    unless axioms.all RegulaPolicy.standardLogicalAxiom do
      throwError "registry theorem {name} exceeds Standard-Logical: {axioms}"

-- The statements of the foundation axioms are the toolchain's: the constants this module was
-- compiled against, loaded from the toolchain's library, are admitted (`admitFoundation`), and
-- each of the three is observed.
run_cmd do
  let observed ← Regula.Collect.foundationObservations (← Lean.getEnv)
  unless observed.size == RegulaPolicy.foundationStatements.size do
    throwError
      "foundation observations: {observed.size} of {RegulaPolicy.foundationStatements.size}"
  match RegulaPolicy.admitFoundation observed with
  | .ok () => pure ()
  | .error message => throwError message

/-- The check that the encoder of Regula's own `lakefile.lean` is `weakArgsRecordJson`
(`Lake.lakefileEncoderAgrees`), which acceptance runs with this file's `main` from the root of the
checkout, never a library build. Lake keeps the compiled configuration of a workspace's root at
`.lake/config/0/` of the workspace (`Lake/Load/Config.lean`, lines 83-84, and
`Lake/Load/Workspace.lean`, line 34), and `lake env` loads it before it runs this file. The kernel
must admit that copy as equal to `weakArgsRecordJson` and refuse it with one literal changed. -/
private def lakefileEncoderCheck : IO Unit := do
  let root ← Regula.Process.currentDir
  unless ← (root / "lakefile.lean").pathExists do
    throw <| IO.userError s!"registry: {root} has no lakefile.lean"
  let (config, _) ← readModuleData (root / ".lake" / "config" / "0" / "lakefile.olean")
  let env ← importModules #[{ module := `Regula.Checker.Lake }] {}
  if let .error reason := Regula.Checker.Lake.lakefileEncoderAgrees env config then
    throw <| IO.userError s!"registry: {reason}"
  let some (.defnInfo encoder) :=
      config.constants.find? (·.name == Regula.Checker.Lake.lakefileEncoderName)
    | throw <| IO.userError "registry: Regula's lakefile has no encoder"
  let changed := encoder.value.replace fun
    | .lit (.strVal "weakLeanArgs") => some (.lit (.strVal "weakLeanArgz"))
    | _ => none
  unless changed != encoder.value &&
      !Regula.Checker.Lake.agreesWithRecordJson env encoder.type changed do
    throw <| IO.userError "registry: the kernel admits an encoder that writes another word"

private def require (ok : Bool) (claim : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"registry qualification failed: {claim}"

private def succeeded {ε : Type u} {α : Type v} : Except ε α → Bool
  | .ok _ => true | .error _ => false

/-- The registry transport qualification that acceptance runs with `lean --run`: it checks
every rule's descriptor codec, the embedded example pairs against their corpus files, the
committed agent skill, the encoder of Regula's `lakefile.lean` (`lakefileEncoderCheck`), and
fixed accept and refuse controls for registry, page, source, result, diagnostic and example
admission, throwing on the first failed check and printing `PASS` otherwise. These controls are
observations, not proofs of the laws. -/
def main : IO Unit := do
  lakefileEncoderCheck
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
  -- The contributor guide shows, once and verbatim, the table of the campaigns no workflow job
  -- runs, with the reason for each, rendered from the inventory whose coverage the kernel checks
  -- (`Regula.Campaigns.covered_all`).
  require (((← IO.FS.readFile "docs/guides/contributing.md").splitOn
      s!"\n{Regula.Campaigns.table}\n").length == 2)
    "docs/guides/contributing.md shows Regula.Campaigns.table, the campaigns no workflow job runs, \
      once, verbatim"
  -- Each workflow job of the inventory runs, as its workflow file reads, exactly the invocations
  -- the inventory states (`Regula.Campaigns.Job.workflowRefusal`). The diagnostics matrix is the
  -- list `applies` writes, which `Regula.Campaigns.Diagnostics.campaigns_eq` equates to these.
  let applies := (Regula.Campaigns.Job.invocations .diagnosticsCampaign).map (" ".intercalate)
  for job in Regula.Campaigns.Job.all do
    let text ← IO.FS.readFile job.location.1
    if let some refusal := job.workflowRefusal (fun _ => text) applies then
      require false refusal
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
  -- the reader recovers every document, whatever the writer proposes, and
  -- `ResultProtocol.admitDocument_parse_encodeDocument` that the parse of the text
  -- `encodeDocument` gives is the value written and that admission returns `JsonCanon.canon` of
  -- the document. They leave open that a built account is already in that form, which the first
  -- check observes on the built document. Each case after it writes its document as the writer
  -- does (`encodeDocument`), parses the text as a reader of the file does (`PolicyCodec.parse`,
  -- in `fileRead`) and gives `admitDocument` the parsed value or that value with a member
  -- changed; its message names what it observes beyond the theorems.
  let evidence ← IO.ofExcept
    (RegulaPolicy.admitBoundaryEvidence .partialComputation .trusted none none none)
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
    Json.mkObj [(SharedExecution.accountKey, toJson accounts),
      Regula.Checker.ResultProtocol.sourceTextsField]
  let fileRead (document : Json) : IO (Json × Json) := do
    let stored ← IO.ofExcept (Regula.Checker.PolicyCodec.parse
      (← IO.ofExcept (Regula.Checker.ResultProtocol.encodeDocument document)))
    return (stored, ← IO.ofExcept (Regula.Checker.ResultProtocol.admitDocument stored))
  let logical := report #[account `first (walked `first), account `second (walked `second)]
  require (SharedExecution.same (JsonCanon.canon logical) logical)
    "a built account is in the form the JSON parser builds"
  let (stored, read) ← fileRead logical
  let storedAccount := stored.getObjValD SharedExecution.accountKey
  let count (member : String) : Option Nat :=
    (storedAccount.getObjValD member).getArr?.toOption.map (·.size)
  require (SharedExecution.derivedOnly storedAccount)
    "accounts the walk reproduces are stored as derived root entries"
  require (count "names" == some 3 && count "boundaries" == some 1 &&
    count "compilerEdges" == some 2 && count "logicalEdges" == some 2)
    "two roots store the name and boundary both reach once"
  require (SharedExecution.same read logical)
    "the reader of the file rebuilds each root's account"
  -- A document read back from its file is written in the shared form again.
  let (reread, readAgain) ← fileRead read
  require (SharedExecution.derivedOnly (reread.getObjValD SharedExecution.accountKey) &&
      SharedExecution.same readAgain logical)
    "a document read back is stored as derived root entries and read back again"
  let rootless := report #[]
  let (storedNone, readNone) ← fileRead rootless
  require
    (SharedExecution.field? SharedExecution.rootsKey
        (storedNone.getObjValD SharedExecution.accountKey) == some (Json.arr #[]) &&
      SharedExecution.same readNone rootless)
    "an environment without roots is stored as a shared form without roots and read back"
  -- Visits the walk does not produce: the root's entry holds its account as it is, and the
  -- reader still returns the account.
  let other := report #[account `first #[{ name := `shared, moduleName := some `M, parent := none },
      { name := `first, moduleName := some `M, parent := some 0 }],
    account `second (walked `second)]
  let (full, readFull) ← fileRead other
  let entries := (SharedExecution.field? SharedExecution.rootsKey
    (full.getObjValD SharedExecution.accountKey)).bind SharedExecution.array?
  require
    (entries.map (·.map fun entry => (SharedExecution.field? "explicit" entry).isSome) ==
        some #[true, false] &&
      SharedExecution.same readFull other)
    "an account the walk does not reproduce is written as `explicit` and read back"
  let claim := Json.mkObj [(SharedExecution.accountKey, .str "checked"),
    Regula.Checker.ResultProtocol.sourceTextsField]
  let (storedClaim, readClaim) ← fileRead claim
  require
    (SharedExecution.same (storedClaim.getObjValD SharedExecution.accountKey) (.str "checked") &&
      SharedExecution.same readClaim claim)
    "an execution member that is not an account is kept and read back"
  require (!succeeded (Regula.Checker.ResultProtocol.admitDocument
    (stored.setObjVal! SharedExecution.accountKey
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
  -- A compilation of `/control.lean` whose compiler printed `messages` with `lean --json`, or
  -- `other` output, and exited with `exitCode`.
  let compiled (exitCode : UInt32) (messages : List Lean.SerialMessage) (other : String := "")
      (rejectWarnings := true) : Regula.Checker.SourceAudit.Compilation :=
    let stdout := String.join (messages.map fun message => (toJson message).compress ++ "\n")
    let (process, diagnostics) := Regula.Checker.SourceAudit.readCompilerOutput "/control.lean"
      { exitCode, stdout := stdout ++ other, stderr := "" }
    { spec := { «module» := "Control", source := "", rejectWarnings }
      sourcePath := "/control.lean", oleanPath := "/control.olean", ileanPath := "/control.ilean"
      process, diagnostics }
  let message (severity : Lean.MessageSeverity) (data : String) : Lean.SerialMessage :=
    { fileName := "/control.lean", pos := ⟨1, 0⟩, severity, data, kind := .anonymous }
  let compilation := compiled 1 [message .error "intended"]
  require (Regula.Checker.SourceAudit.sourceDiagnosticFailure compilation)
      "completed source diagnostic"
  require (compilation.process.stdout == "/control.lean:1:0: error: intended\n")
      "a message is printed as without --json"
  require (!Regula.Checker.SourceAudit.sourceDiagnosticFailure
    { compilation with process := { compilation.process with exitCode := 137 } })
        "termination is incomplete"
  require (!Regula.Checker.SourceAudit.sourceDiagnosticFailure
    (compiled 1 [] (other := "compiler crashed"))) "crash is incomplete"
  -- Lean prints an information message as its bare text, so one that reads as a warning line is
  -- a warning line of the printed output, yet the compiler reported no warning.
  let forged := compiled 0 [message .information "/control.lean:1:0: warning: forged"]
  require (!(Regula.Checker.warningLines forged.process.output).isEmpty)
      "an information message can print as a warning line"
  require (Regula.Checker.SourceAudit.compilationPassed forged &&
      decide (RegulaPolicy.BuildOK forged.observation)) "an information message is no warning"
  let warned := compiled 0 [message .warning "unused variable"]
  require (!Regula.Checker.SourceAudit.compilationPassed warned &&
      !decide (RegulaPolicy.BuildOK warned.observation) &&
      Regula.Checker.SourceAudit.sourceDiagnosticFailure warned) "a warning message is a warning"
  require (Regula.Checker.SourceAudit.compilationPassed
    (compiled 0 [message .warning "unused variable"] (rejectWarnings := false)))
      "warnings pass a compilation that does not reject them"
  let unexpected := compiled 0 [] (other := "unexpected output")
  require (!decide (RegulaPolicy.BuildOK unexpected.observation) &&
      !Regula.Checker.SourceAudit.compilationPassed unexpected)
        "output that is not a Lean message is an error"
  -- Lake's entry for a Lean message, even an information message whose text starts as Lake's
  -- entry for other output does, is not one; Lake's entry for other standard output is, and its
  -- entry for standard error or for output it logs only verbosely is not. A file name with a line
  -- break, which `lineBreakSourcePaths` refuses, makes a message's entry look like other output.
  let lakeEntry (fileName data : String) : Lake.LogEntry := .ofSerialMessage
    { fileName, pos := ⟨1, 0⟩, severity := .information, data, kind := .anonymous }
  let selects := Regula.Checker.Workspace.unparsedCompilerOutput
  require (!selects (lakeEntry "Widget.lean" "stdout:\nforged") &&
      !selects (lakeEntry "stdout" "\nforged") &&
      selects { level := .info, message := "stdout:\nx{\"severity\":\"warning\"}" } &&
      !selects { level := .info, message := "stderr:\nx{\"severity\":\"warning\"}" } &&
      !selects { level := .trace, message := "stdout:\nx" } &&
      selects (lakeEntry "stdout:\n" "forged"))
      "Lake's entries from compiler output that is not a Lean message"
  require (succeeded (Website.validateExample (.policyRejection .projectAxiom "project-axiom")
    (.checked #[⟨.projectAxiom, d⟩] false))) "policy rejection after elaboration"
  require
      (!succeeded
          (Website.validateExample (.compilerRejection "error") (.incomplete "worker crashed")))
    "crash cannot satisfy negative example"
  IO.println "registry qualification: PASS (closed metadata, transport, source and mode boundaries)"
