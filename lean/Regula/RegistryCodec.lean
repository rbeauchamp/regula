import Regula.Diagnostic
import Regula.StructuralName
import Regula.SourceTexts
import Regula.Decision

/-! # Registry transport codec

Versioned transport and website admission derived from the registry. The exact
canonical comparison follows con-leche's representation idea (RuleId attribution).
JSON syntax parsing and external producer/source identity remain trusted boundaries. -/
namespace Regula.RegistryCodec
open Lean

/-- The text of an evidence mode in registry and result JSON (`EvidenceMode.spelling`). -/
def modeText := EvidenceMode.spelling

/-- The evidence mode a text names; it recovers every mode from its `modeText`
(`mode_roundtrip`). -/
@[regula_decision]
def parseMode : String → Except String EvidenceMode
  | "editorSnapshot" => .ok .editorSnapshot
  | "incrementalProject" => .ok .incrementalProject
  | "freshProject" => .ok .freshProject
  | "freshFile" => .ok .freshFile
  | "documentationExample" => .ok .documentationExample
  | "serializedGraph" => .ok .serializedGraph
  | s => .error s!"unknown evidence mode: {s}"

theorem mode_roundtrip (m : EvidenceMode) : parseMode (modeText m) = .ok m := by
  cases m <;> rfl

/-- `parseMode` is a complete decision of the written modes (`mode_roundtrip`): it accepts the
text of every evidence mode, and it refuses the empty text. The kind is one-way: that it accepts
only those texts is not stated for this reader; `EvidenceMode.checked_parse` states it for the
policy's own parser. -/
theorem checked_parseMode : Regula.ExecutableContract parseMode
    (Regula.DecidesCompletely (·.isOk = true) fun text => ∃ mode, text = modeText mode) :=
  ⟨{ complete := fun _ ⟨mode, written⟩ => by
       rw [written, mode_roundtrip]
       rfl
     refused := ⟨"", by decide⟩ }⟩

/-- A rule ID as its JSON string, such as `"RG1001"`. -/
def ruleJson (id : RuleId) : Json := .str id.spelling

/-- The rule a JSON string names; it recovers every rule from its `ruleJson`
(`rule_roundtrip`). -/
@[regula_decision]
def parseRule (j : Json) : Except String RuleId := do
  let s ← j.getStr?
  match RuleId.parse? s with
  | some id => return id
  | none => throw s!"unknown rule ID: {s}"

theorem rule_roundtrip (id : RuleId) : parseRule (ruleJson id) = .ok id := by
  cases id <;> rfl

/-- `parseRule` is a complete decision of the written rule IDs (`rule_roundtrip`): it accepts
the JSON string of every rule, and it refuses `null`. The kind is one-way: that it accepts only
those strings is not stated for this reader; `RuleId.checked_parse` states it for the parser of
the spelling. -/
theorem checked_parseRule : Regula.ExecutableContract parseRule
    (Regula.DecidesCompletely (·.isOk = true) fun json => ∃ id, json = ruleJson id) :=
  ⟨{ complete := fun _ ⟨id, written⟩ => by
       rw [written, rule_roundtrip]
       rfl
     refused := ⟨.null, by decide⟩ }⟩

private def categoryText : RuleCategory → String
  | .foundation => "foundation" | .declaration => "declaration"
  | .execution => "execution" | .environment => "environment"
  | .configuration => "configuration" | .elaboration => "elaboration"
  | .coverage => "coverage" | .admission => "admission" | .documentation => "documentation"

private def scopeText : RuleScope → String
  | .declaration => "declaration" | .project => "project" | .executionRoot => "executionRoot"
  | .documentationFence => "documentationFence" | .module => "module"
  | .materialDeclaration => "materialDeclaration"

private def evidenceText : EvidenceKind → String
  | .kernelAxioms => "kernelAxioms" | .generatedRole => "generatedRole"
  | .contractEvidence => "contractEvidence" | .environment => "environment"
  | .configuration => "configuration" | .compilation => "compilation"
  | .inventory => "inventory" | .admission => "admission" | .executionClosure => "executionClosure"
  | .fenceGrammar => "fenceGrammar" | .checkedExample => "checkedExample"
  | .metadataPresence => "metadataPresence"

private def languageText : ExampleLanguage → String
  | .lean => "lean" | .json => "json" | .markdown => "markdown"

private def audienceJson : ExampleAudience → Json
  | .adopter => Json.mkObj [("kind", .str "adopter")]
  | .qualification files => Json.mkObj [("kind", .str "qualification"), ("files", toJson files)]

/-- A rule's checked example pair with its derived repository paths. -/
def examplesJson (id : RuleId) : Json :=
  let e := (descriptor id).examples
  Json.mkObj [
    ("language", toJson (languageText e.language)), ("audience", audienceJson e.audience),
    ("compliant", Json.mkObj [("path", toJson (e.compliantPath id)), ("text", toJson e.compliant)]),
    ("noncompliant", Json.mkObj
        [("path", toJson (e.noncompliantPath id)), ("text", toJson e.noncompliant)]),
    ("correction", toJson e.correction)]

/-- A rule's registry record: its guidance, checked examples, category, scope, evidence kind,
cited clauses, modes, message template, help route and URL and lifecycle, all read from its
descriptor. -/
def descriptorJson (id : RuleId) : Json :=
  let d := descriptor id
  Json.mkObj [
    ("id", ruleJson id), ("title", toJson d.title),
    ("requirement", toJson d.requirement), ("rationale", toJson d.rationale),
    ("remedy", toJson d.remedy), ("rewrites", toJson d.rewrites), ("examples", examplesJson id),
    ("category", toJson (categoryText d.category)),
    ("scope", toJson (scopeText d.scope)), ("evidenceKind", toJson (evidenceText d.evidenceKind)),
    ("normativeClauses", toJson (d.normativeClauses.map fun c => Json.mkObj [
      ("section", toJson c.number), ("title", toJson c.title), ("source", toJson c.source),
      ("url", toJson c.url)])),
    ("applicability", toJson d.applicability),
    ("defaultStrictSeverity", toJson d.defaultStrictSeverity.spelling),
    ("evidenceModes", toJson (d.evidenceModes.map modeText)),
    ("messageTemplate", toJson d.messageTemplate),
    ("helpRoute", toJson id.route), ("helpUrl", toJson (helpUrl id)),
    ("introduced", toJson d.lifecycle.introduced.spelling),
    ("retired", match d.lifecycle with
      | .active _ => Json.null | .retired _ version _ => toJson version.spelling),
    ("replacement", match d.lifecycle with
      | .active _ => Json.null
      | .retired _ _ replacement => (replacement.map (ruleJson ∘ Subtype.val)).getD Json.null),]

/-- Reject metadata drift, unknown fields, missing fields, routes and lifecycle values. -/
def parseDescriptor (j : Json) : Except String RuleId := do
  let id ← parseRule (← j.getObjVal? "id")
  if j == descriptorJson id then return id
  else throw s!"noncanonical or stale descriptor: {id}"

/-- The identity of the build that produced a registry or result: its version, toolchain and
source revision. -/
structure ProducerIdentity where
  /-- The producer's version, such as `unreleased`. -/
  producerVersion : String
  /-- The Lean version string of the toolchain it was built with. -/
  toolchain : String
  /-- The Git revision of the producer's source, with any worktree marker. -/
  sourceRevision : String
  deriving BEq

/-- Identity is supplied by the build/collector, not inferred from diagnostic text.
Registry and result envelopes carry independent schema versions. -/
def identityFields (p : ProducerIdentity) (schemaVersion : Nat := 1) : List (String × Json) := [
  ("schemaVersion", toJson schemaVersion), ("producerVersion", toJson p.producerVersion),
  ("toolchain", toJson p.toolchain), ("sourceRevision", toJson p.sourceRevision)]

/-- The registry export's schema version: each rule's record is `descriptorJson`, whose
`normativeClauses` are objects with the cited section's number (`section`), heading (`title`),
Verso source path (`source`) and URL in the installed build's edition (`url`). -/
def registrySchemaVersion : Nat := 4

/-- The registry JSON: the identity fields at `registrySchemaVersion` and every rule's
`descriptorJson`, in `RuleId.all` order. -/
def registryJson (p : ProducerIdentity) : Json :=
  Json.mkObj
      (identityFields p registrySchemaVersion ++
          [("rules", toJson (RuleId.all.map descriptorJson))])

/-- A manifest is accepted only if it is exactly the current closed registry and identity.
Array ordering is canonical; duplicate, omitted, extra and stale records all fail. -/
def validateRegistry (p : ProducerIdentity) (j : Json) : Except String Unit :=
  if j == registryJson p then .ok () else .error "registry or producer identity mismatch"

/-- A byte range as JSON: its start offset and its stop offset. -/
def rangeJson (r : ByteRange) : Json :=
  Json.mkObj [("startByte", toJson r.start), ("endByte", toJson r.stop)]

/-- A location's JSON: its kind with the module name (`printedNameJson`), the project identity,
or the source's URI, text, byte ranges and LSP ranges. The text is the `sourceText` member, which
a result file stores once for all its locations (`SourceTexts.intern`). -/
def locationJson : Location → Json
  | .module n => Json.mkObj [("kind", .str "module"), ("name", printedNameJson n)]
  | .project s => Json.mkObj [("kind", .str "project"), ("identity", .str s)]
  | .source s => Json.mkObj [
      ("kind", .str "source"), ("uri", .str s.val.snapshot.uri),
      (SourceTexts.textKey, .str s.val.snapshot.source), ("range", rangeJson s.val.full),
      ("selectionRange", rangeJson s.val.selection),
      ("lspRange", toJson s.fullLsp), ("lspSelectionRange", toJson s.selectionLsp)]

/-- The payload of a finding as JSON, in the argument domain of its rule: a declaration with its
source declaration and detail, an execution root with its detail, or a subject with its detail. -/
def argumentsJson : (id : RuleId) → Payload id → Json
  | .projectAxiom, a | .proofHole, a | .unknownAxiom, a | .compilerTrusting, a
  | .profileExceeded, a | .escapeHatch, a | .executableContract, a | .decisionContract, a
  | .sharedTest, a | .materialDocumentation, a | .materialIntent, a =>
      Json.mkObj [("declaration", printedNameJson a.declaration),
        ("sourceDeclaration", (a.sourceDeclaration.map printedNameJson).getD .null),
        ("detail", toJson a.detail)]
  | .executionUnresolved, a | .executionBoundary, a =>
      Json.mkObj [("root", printedNameJson a.root), ("detail", toJson a.detail)]
  | .environment, a | .configuration, a | .sourceBuild, a | .coverage, a
  | .admission, a | .communityConfiguration, a | .fenceStructure, a | .positiveExample, a
  | .negativeExample, a
  | .trustedExample, a | .moduleDocumentation, a =>
      Json.mkObj [("subject", toJson a.subject), ("detail", toJson a.detail)]

/-- A finding's JSON: its rule, payload, locations, mode, claim, impact, severity, rendered
text, remedy and help URL. -/
def diagnosticJson (f : Finding) : Json :=
  let ⟨id, d⟩ := f
  Json.mkObj [
    ("id", ruleJson id), ("arguments", argumentsJson id d.arguments),
    ("location", locationJson d.location),
    ("related", toJson (d.related.map fun r => Json.mkObj [
      ("relation", toJson r.relation), ("location", locationJson r.location)])),
    ("mode", toJson (modeText d.mode)), ("claim", toJson d.claim),
    ("impact", .str (if d.impact == .violation then "violation" else "incomplete")),
    ("severity", toJson d.severity.spelling),
    ("text", toJson d.text), ("remedy", toJson (descriptor id).remedy),
    ("helpUrl", toJson (helpUrl id))]

/-- The guidance of one rule that fired in a run: what a consumer needs to comply without the
website. `compliantExample` is null where the checked files are qualification inputs, and
`correction` states the fix the pair demonstrates. -/
def guidanceJson (id : RuleId) : Json :=
  let d := descriptor id
  Json.mkObj [
    ("id", ruleJson id), ("title", toJson d.title), ("requirement", toJson d.requirement),
    ("rationale", toJson d.rationale), ("remedy", toJson d.remedy), ("rewrites", toJson d.rewrites),
    ("compliantExample", (d.examples.adopterExample.map fun text => Json.mkObj [
      ("path", toJson (d.examples.compliantPath id)),
      ("language", toJson (languageText d.examples.language)), ("text", toJson text)]).getD .null),
    ("correction", toJson d.examples.correction),
    ("helpUrl", toJson (helpUrl id)), ("explain", toJson (Feedback.explainCommand id))]

/-- The rules among `ids`, each once, in registry order. -/
def firedRules (ids : List RuleId) : List RuleId := RuleId.all.filter (· ∈ ids)

/-- Every rule that fired receives exactly one entry. -/
theorem mem_firedRules (ids : List RuleId) (id : RuleId) : id ∈ firedRules ids ↔ id ∈ ids := by
  simp [firedRules, RuleId.mem_all]

theorem firedRules_nodup (ids : List RuleId) : (firedRules ids).Nodup :=
  RuleId.all_nodup.filter _

/-- The `rules` member of a result: the guidance of every rule that fired, once each. -/
def rulesJson (ids : List RuleId) : Json := toJson ((firedRules ids).map guidanceJson)

/-- Website artifact admission uses actual produced pages, not descriptors pretending to be
pages. -/
structure Page where
  /-- The rule the page documents. -/
  rule : RuleId
  /-- The route the page was written at. -/
  route : String
  /-- Whether the page includes the rule's checked example. -/
  checkedExample : Bool

/-- Accept a site's pages only when the manifest equals `registryJson p`, the rules and routes
are unique, there is one page for each rule of `required` and no other, and each page is at
its rule's route with a checked example. -/
def validatePages (p : ProducerIdentity) (manifest : Json) (required : List RuleId)
    (pages : List Page) : Except String Unit := do
  validateRegistry p manifest
  unless required.Nodup && (pages.map (·.rule)).Nodup && (pages.map (·.route)).Nodup do
    throw "duplicate rule or route"
  unless pages.length == required.length && required.all (fun id => pages.any (·.rule == id)) do
    throw "missing or unexpected rule page"
  for page in pages do
    unless page.route == page.rule.route && page.checkedExample do
      throw s!"missing checked example or wrong route: {page.rule}"
end Regula.RegistryCodec
