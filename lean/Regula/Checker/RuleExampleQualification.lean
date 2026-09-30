import Regula.Checker.Documentation
import Regula.Checker.ResultProtocol
import Regula.Checker.PolicyCodec
import Regula.Website
import RegulaPolicy.Guards
import RegulaCore.Lint

/-! # Rule-example receipt qualification

Qualification and export admission for actual source-owned example receipts.
Expected selectors are fixed before running the detector. This module checks canonical
registry diagnostics and binds them to observed exact source/configuration/mode. -/
-- Exact dependency ceiling for the new claimed data-level guarantees. Acquisition,
-- JSON and compiler authenticity are expressly outside these theorem statements.
run_cmd do
  for name in #[``Regula.Website.admitDemonstration_complete,
      ``Regula.Website.admitDemonstration_sound, ``Regula.Website.demonstration_completed,
      ``Regula.Website.demonstration_observed_incomplete,
      ``Regula.Website.demonstration_selected_rule,
      ``Regula.Website.demonstration_not_accepted,
      ``RegulaPolicy.incomplete_example_refused,
      ``Regula.Website.admitExampleRequest_sound,
      ``Regula.Website.admitExampleSources_sound,
      ``Regula.Website.admitExampleSources_complete,
      ``Regula.Checker.Documentation.positiveClassifications_sound] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => #[`propext, `Quot.sound, `Classical.choice].contains ax) do
      throwError "example theorem {name} exceeds Standard-Logical: {axioms}"

namespace Regula.Checker.RuleExampleQualification
open Lean Regula Regula.Website

/-- The value of `key` in the JSON object `j`, or an error when it has none. -/
def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
/-- The string value of `key` in the JSON object `j`, or an error. -/
def string (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

/-- A JSON array of source snapshots, each an object with exactly the fields `uri` and
`source`. -/
def sources (j : Json) : Except String (Array RegulaPolicy.SourceSnapshot) := do
  (← j.getArr?).mapM fun source => do
    PolicyCodec.exactFields source ["uri", "source"]
    return ⟨← string source "uri", ← string source "source"⟩

private def parseRequest (json : Json) : Except String ExampleRequest := do
  let request : ExampleRequest ← fromJson? json
  unless ["file", "project", "documentation", "policyNegative"].contains request.kind do
    throw "unsupported example request kind"
  unless toJson (request : ExampleRequest) == json do throw "invalid example request account"
  return request

theorem parseRequest_sound {json : Json} {r : ExampleRequest} (h : parseRequest json = .ok r) :
    (fromJson? json : Except String ExampleRequest) = .ok r := by
  unfold parseRequest at h
  simp only [RegulaPolicy.Guards.bind_eq_ok] at h
  obtain ⟨d, hd, h⟩ := h
  by_cases c₂ : (toJson d == json) = true <;>
    simp [c₂, throw, throwThe, MonadExceptOf.throw, pure, Except.pure, bind, Except.bind] at h <;>
    split at h <;> simp_all

/-- The example binding of a receipt record: its `before` and `after` inputs must be equal;
their sources and configuration, the result's toolchain and source revision and the record's
checker sources form the admitted snapshot; the record's request must have that
configuration's URI as its project and its parsed text as its configuration. -/
def binding (record : Json) (mode : EvidenceMode) : Except String ExampleBinding := do
  let input ← field record "before"
  let after ← field record "after"
  unless input == after do throw "example source/configuration changed"
  let ss ← sources (← field input "sources")
  let configuration : RegulaPolicy.SourceSnapshot :=
    ⟨← string (← field input "configuration") "uri", ← string
        (← field input "configuration") "source"⟩
  let result ← field record "result"
  let snapshot ← RegulaPolicy.admitSnapshot {
    sources := ss, configuration
    toolchain := {
      leanVersion := ← string result "toolchain"
      compilerCommit := Lean.githash
      producerRevision := ← string result "sourceRevision" }
    dependencies := #[{
      package := "regula"
      nominalRevision := some (← string result "sourceRevision")
      dirty := true
      files := ← sources (← field record "checkerSources") }] }
  let request ← parseRequest (← field record "request")
  unless request.project == configuration.uri &&
      toJson request.configuration == (← PolicyCodec.parse configuration.source) do
    throw "request configuration differs from frozen snapshot"
  return ⟨snapshot, mode, request⟩

/-- The producer's account of the sources it read: its source account, or the
diagnostic-only file or documentation scope. -/
def observedSources (result : Json) (bound : ExampleBinding) :
    Except String (Array RegulaPolicy.SourceSnapshot) := do
  let scope ← field result "scope"
  if let .ok raw := field result "sourceAccount" then do
    let entries ← fromJson? (α := Array ProducerReport.SourceBinding) raw
    pure (entries.map fun entry => (⟨entry.path, entry.content⟩ : RegulaPolicy.SourceSnapshot))
  else if bound.request.kind == "policyNegative" then do
    pure #[⟨← string scope "file", ← string scope "source"⟩]
  else if bound.request.kind == "documentation" then sources (← field scope "documents")
  else throw "missing result source account"

/-- The producer's observed sources pass `admitExampleSources` against the bound snapshot
and the displayed text, and a file or policy-negative request's own file was observed with
exactly the displayed text. -/
def sourceAccount (result : Json) (bound : ExampleBinding) (displayed : String) :
    Except String Unit := do
  let observed ← observedSources result bound
  let _ ← admitExampleSources bound.snapshot.val.sources observed displayed
  if bound.request.kind == "file" || bound.request.kind == "policyNegative" then
    unless observed.any
        (fun source => source.uri == bound.request.subject && source.source == displayed) do
      throw "missing requested file source account"

private def configurationAccount (root : String) (configuration : Array (String × Option String)) :
    Except String (Array (String × Option String)) := do
  unless !root.isEmpty do throw "missing configuration root"
  configuration.mapM fun (path, source) => do
    unless path.startsWith (root ++ "/") do throw "configuration outside captured project"
    return ((path.drop (root.length + 1)).toString, source)

/-- The effective configuration and scope agree with the admitted request. -/
def effectiveAccount (result : Json) (admitted : ExampleRequest) : Except String Unit := do
  let requested ← configurationAccount admitted.project admitted.configuration
  let effectiveAccount ← field result "effective"
  if effectiveAccount != Json.null then
    let effective ← configurationAccount (← string effectiveAccount "root")
      (← fromJson? (α := Array (String × Option String)) (← field effectiveAccount "configuration"))
    unless effective == requested do throw "effective configuration differs from request"
  let scope ← field result "scope"
  if let .ok _ := scope.getObj? then
    unless effectiveAccount != Json.null do throw "missing effective request account"
    let configuration ← fromJson? (α := Array (String × Option String))
        (← field scope "configuration")
    let effective ← configurationAccount (← string scope "configurationRoot") configuration
    unless effective == requested &&
        (← field scope "configuration") == (← field effectiveAccount "configuration") &&
        (← field scope "configurationRoot") == (← field effectiveAccount "root") do
      throw "effective configuration differs from request"
    match admitted.kind with
    | "file" =>
        unless (← field scope "claim") == toJson admitted.claim &&
            (← field scope "execution") == toJson admitted.execution &&
            (← string scope "file") == admitted.subject do
          throw "effective file claim or execution differs from request"
    | "policyNegative" =>
        unless (← field scope "claim") == toJson (some "standard-logical" : Option String) &&
            (← field scope "execution") == Json.null && (← string scope "file") ==
                admitted.subject &&
            (← field scope "diagnosticOnly") == toJson true do
          throw "wrong diagnostic-only effective request"
    | "documentation" => pure ()
    | "project" =>
        unless (← string scope "project") == admitted.subject do throw "wrong effective project"
        let some (_, some text) := requested.find? (·.1 == "foundation_manifest.json")
          | throw "missing requested manifest"
        let manifest ← PolicyCodec.parse text
        let surfaces ← (← field manifest "surfaces").getArr?
        let actual ← (← field scope "surfaces").getArr?
        unless actual.size == surfaces.size do
            throw "effective surface coverage differs from request"
        for (expected, actual) in surfaces.zip actual do
          unless (← field expected "library") == (← field actual "library") &&
              (← field expected "claim") == (← field actual "claim") &&
              ((field expected "execution").toOption.getD (.str "report")) ==
              (← field actual "execution") do
            throw "effective surface claim or execution differs from request"
    | _ => throw "unknown example request kind"

/-- The result's request, admitted as equal to the bound request, with its effective
configuration and scope checked by `effectiveAccount`. -/
def requestAccount (result : Json) (bound : ExampleBinding) : Except String ExampleRequest := do
  let observed ← parseRequest (← field result "request")
  let admitted ← admitExampleRequest bound.request observed
  effectiveAccount result admitted.val
  return admitted.val

/-- Every declared selector is required; no filtering of the actual findings occurs.
Patterns use the same proved single-message language as compiler-negative fences. -/
private def matchFinding (expected : Json) (actual : Finding) (input : ExampleBinding) :
    Except String Unit := do
  PolicyCodec.exactFields expected
      ["id", "subreason", "detailPattern", "location", "subject", "impact", "claim"]
  let id ← RegistryCodec.parseRule (← field expected "id")
  unless actual.1 == id do throw "unexpected rule diagnostic"
  unless (← string expected "subreason") == (descriptor id).applicability do
    throw "wrong expected rule subreason"
  let encoded := RegistryCodec.diagnosticJson actual
  let arguments ← field encoded "arguments"
  unless RegulaPolicy.matchesPattern (← string expected "detailPattern")
      (← string arguments "detail") do
    throw s!"wrong diagnostic reason for {id}"
  unless (← field expected "impact") == (← field encoded "impact") do
      throw "wrong diagnostic impact"
  unless (← field expected "claim") == (← field encoded "claim") && actual.2.severity == .error do
    throw "wrong diagnostic claim or severity"
  unless actual.2.mode == input.mode do throw "wrong diagnostic mode"
  unless actual.2.related.isEmpty do throw "unexpected related diagnostics"
  let subject ← field expected "subject"
  let args := (← arguments.getObj?).toList.filter (·.1 != "detail")
  unless Json.mkObj args == subject do throw s!"wrong diagnostic subject for {id}"
  let location ← field expected "location"
  unless (← field encoded "location") == location do throw s!"wrong primary location for {id}"
  match actual.2.location with
  | .source source =>
      unless input.snapshot.val.sources.any (fun s => s == source.val.snapshot) do
        throw "diagnostic source is outside the fixed example snapshot"
  | .module name => unless name != .anonymous do throw "anonymous diagnostic module"
  | .project name => unless !name.isEmpty do throw "missing diagnostic context"


/-- The result retains one exact producer identity field. -/
def checkIdentity (result : Json) (entry : String × Json) : Except String Unit := do
  unless (← field result entry.1) == entry.2 do throw s!"stale result identity: {entry.1}"

/-- The request kind agrees with the evidence mode it was produced under. -/
def modeMatches (kind : String) (mode : EvidenceMode) : Bool :=
  match kind with
  | "file" | "policyNegative" => mode == .freshFile
  | "documentation" => mode == .documentationExample
  | "project" => mode == .freshProject || mode == .incrementalProject
  | _ => false

/-- Exactly the expected diagnostics, in order, and exactly the expected unresolved
evidence. -/
def expectFindings (record result : Json) (bound : ExampleBinding) (actual : Array Finding) :
    Except String Unit := do
  let expected ← (← field record "expected").getArr?
  unless expected.size == actual.size do throw "missing or unexpected diagnostic"
  for (spec, finding) in expected.zip actual do matchFinding spec finding bound
  let unresolved ← (← (← field result "unresolved").getArr?).mapM Json.getStr?
  let patterns ← (← (← field record "unresolvedPatterns").getArr?).mapM Json.getStr?
  unless unresolved.size == patterns.size && (patterns.zip unresolved).all
      (fun (pattern, detail) => RegulaPolicy.matchesPattern pattern detail) do
    throw "unexpected unresolved evidence"

/-- The parsed actual findings, once they meet `expectFindings`. -/
def checkFindings (record result : Json) (bound : ExampleBinding) : Except String
    (Array Finding) := do
  let actual ← (← (← field result "diagnostics").getArr?).mapM DiagnosticCodec.parseDiagnostic
  expectFindings record result bound actual
  return actual

/-- The kind-specific classification of an admitted record. -/
def qualifyKind (record result : Json) (bound : ExampleBinding) (observedRequest : ExampleRequest)
    (mode : EvidenceMode) (code : Nat) (status kind : String) (actual : Array Finding) :
    Except String Unit := do
  let observation : BoundObservation :=
      ⟨{ bound with request := observedRequest }, .completed, .checked actual false⟩
  match kind with
  | "positive" =>
      unless bound.request.kind != "policyNegative" do
          throw "diagnostic-only adapter cannot qualify positive"
      if mode == .documentationExample then
        let raw ← (← field (← field result "scope") "fences").getArr?
        let classifications ← raw.mapM (fromJson? (α := Documentation.Classification))
        let _ ← Documentation.admitPositiveClassifications classifications
        pure ()
      unless code == 0 && status == "completed" && actual.isEmpty do
          throw "positive check incomplete"
      validateBoundExample bound .positive #[] observation
  | "policyRejection" =>
      -- The producer's exit code for exactly these findings (`Lint.Observation.exitCode`): 1, or
      -- 2 when every one is configuration (RG2002).
      let exit := (Lint.Observation.refused (actual.toList.map fun f => (f.1, f.2.impact))
        false).exitCode
      unless code == exit.toNat && status == "rejected" && !actual.isEmpty do
          throw "policy rejection incomplete"
      let rule ← RegistryCodec.parseRule (← field record "rule")
      validateBoundExample bound (.policyRejection rule (descriptor rule).applicability) actual
          observation
  | "diagnosticDemonstration" =>
      unless code == Lint.Outcome.incomplete.exitCode.toNat && status == "incomplete" do
          throw "not the expected unavailable-analysis result"
      let rule ← RegistryCodec.parseRule (← field record "rule")
      let _ ← admitDemonstration ⟨bound, rule, actual⟩ observation
      pure ()
  | _ => throw "unknown example or demonstration kind"

/-- Validate an actual subprocess record. A normal terminal exit, bound canonical result,
exact expectation list and source stability are jointly required. No exit-only acceptance. -/
def qualify (record : Json) : Except String Unit := do
  let result ← field record "result"
  ResultProtocol.identityFields.forM (checkIdentity result)
  let mode ← RegistryCodec.parseMode (← string record "mode")
  unless (← string result "mode") == mode.spelling do throw "wrong example evidence mode"
  let bound ← binding record mode
  let observedRequest ← requestAccount result bound
  unless modeMatches observedRequest.kind mode do
      throw "request invocation differs from evidence mode"
  let code ← (← field record "exitCode").getNat?
  unless code ≤ 3 do throw "example process did not complete normally"
  let actual ← checkFindings record result bound
  let status ← string result "status"
  let kind ← string record "kind"
  sourceAccount result bound (← string record "source")
  qualifyKind record result bound observedRequest mode code status kind actual

open RegulaPolicy.Guards

theorem qualify_parts (record : Json) (h : qualify record = .ok ()) :
    ∃ result mode bound observedRequest code actual status kind displayed,
      field record "result" = .ok result ∧
      (∀ entry ∈ ResultProtocol.identityFields, checkIdentity result entry = .ok ()) ∧
      (string record "mode" >>= RegistryCodec.parseMode) = .ok mode ∧
      string result "mode" = .ok mode.spelling ∧
      binding record mode = .ok bound ∧
      requestAccount result bound = .ok observedRequest ∧
      modeMatches observedRequest.kind mode = true ∧
      (field record "exitCode" >>= Json.getNat?) = .ok code ∧ code ≤ 3 ∧
      checkFindings record result bound = .ok actual ∧
      string result "status" = .ok status ∧ string record "kind" = .ok kind ∧
      string record "source" = .ok displayed ∧
      sourceAccount result bound displayed = .ok () ∧
      qualifyKind record result bound observedRequest mode code status kind actual = .ok () := by
  unfold qualify at h
  simp only [bind_eq_ok] at h
  obtain ⟨result, hr, _, hid, ms, hms, mode, hmode, rm, hrm, h⟩ := h
  simp only [ite_throw_eq_ok, bind_eq_ok, throw_bind, beq_iff_eq] at h
  obtain ⟨hrm2, bound, hb, req, hreq, hmm, ec, hec, code, hcode, hle, actual, ha, status, hs, kind,
      hk, src, hsrc, ⟨⟩, hsa, hq⟩ := h
  subst hrm2
  refine
      ⟨result, mode, bound, req, code, actual, status, kind, src, hr, ?_, by simp
          [bind_eq_ok, hms, hmode], hrm, hb, hreq, hmm, by simp [bind_eq_ok, hec, hcode], hle, ha,
              hs, hk, hsrc, hsa, hq⟩
  exact listForM_eq_ok.mp hid

theorem checkIdentity_sound {result : Json} {entry : String × Json}
    (h : checkIdentity result entry = .ok ()) :
    ∃ value, field result entry.1 = .ok value ∧ (value == entry.2) = true := by
  unfold checkIdentity at h
  simp only [bind_eq_ok] at h
  obtain ⟨value, hv, h⟩ := h
  exact ⟨value, hv, by simpa using h⟩

theorem binding_sound {record : Json} {mode : EvidenceMode} {bound : ExampleBinding}
    (h : binding record mode = .ok bound) :
    ∃ before after, field record "before" = .ok before ∧ field record "after" = .ok after ∧
      (before == after) = true ∧ bound.mode = mode ∧
      ∃ requestJson, field record "request" = .ok requestJson ∧
        (fromJson? requestJson : Except String ExampleRequest) = .ok bound.request := by
  unfold binding at h
  simp only [bind_eq_ok] at h
  obtain ⟨before, hb, after, ha, h⟩ := h
  split at h
  next heq =>
    simp only [bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, snapshot, _, rj,
        hrj, req, hreq, _, _, h⟩ := h
    split at h
    next =>
      simp only [pure_eq_ok] at h
      subst h
      refine ⟨before, after, hb, ha, heq, rfl, rj, hrj, ?_⟩
      exact parseRequest_sound hreq
    next => simp only [throw_bind] at h; cases h
  next => simp only [throw_bind] at h; cases h


theorem requestAccount_sound {result : Json} {bound : ExampleBinding} {req : ExampleRequest}
    (h : requestAccount result bound = .ok req) :
    req = bound.request ∧ ∃ requestJson, field result "request" = .ok requestJson ∧
      (fromJson? requestJson : Except String ExampleRequest) = .ok req := by
  unfold requestAccount at h
  simp only [bind_eq_ok] at h
  obtain ⟨rj, hrj, observed, hobs, admitted, hadm, ⟨⟩, _, h⟩ := h
  simp only [pure_eq_ok] at h
  subst h
  have hsound := admitted.property
  refine ⟨hsound.2, rj, hrj, ?_⟩
  rw [hsound.1]
  exact parseRequest_sound hobs

theorem checkFindings_sound {record result : Json} {bound : ExampleBinding} {actual : Array Finding}
    (h : checkFindings record result bound = .ok actual) :
    ((field result "diagnostics" >>= Json.getArr?) >>=
      (·.mapM DiagnosticCodec.parseDiagnostic)) = .ok actual := by
  unfold checkFindings at h
  simp only [bind_eq_ok] at h
  obtain ⟨raw, hraw, parsed, hparsed, found, hfound, _, _, h⟩ := h
  rw [pure_eq_ok] at h
  subst h
  simp [bind_eq_ok, hraw, hparsed, hfound]

theorem sourceAccount_sound {result : Json} {bound : ExampleBinding} {displayed : String}
    (h : sourceAccount result bound displayed = .ok ()) :
    (∃ observed, observedSources result bound = .ok observed ∧
      ExampleSourcesOK bound.snapshot.val.sources observed displayed ∧
      (bound.request.kind = "file" ∨ bound.request.kind = "policyNegative" →
        ∃ s ∈ observed, s.uri = bound.request.subject ∧ s.source = displayed)) ∧
    ((∃ raw, field result "sourceAccount" = .ok raw) ∨
      bound.request.kind = "policyNegative" ∨ bound.request.kind = "documentation") := by
  unfold sourceAccount at h
  simp only [bind_eq_ok] at h
  obtain ⟨observed, hobs, admitted, hadm, h⟩ := h
  refine ⟨⟨observed, hobs, admitExampleSources_sound _ _ _ admitted hadm, fun hk => ?_⟩, ?_⟩
  · have hc : (bound.request.kind == "file" || bound.request.kind == "policyNegative") = true := by
      rcases hk with hk | hk <;> simp [hk]
    simp only [hc, ↓reduceIte, unless_eq_ok] at h
    obtain ⟨s, hs, hsub⟩ := Array.any_eq_true'.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsub
    exact ⟨s, hs, hsub⟩
  unfold observedSources at hobs
  simp only [bind_eq_ok] at hobs
  obtain ⟨_, _, hobs⟩ := hobs
  split at hobs
  next raw hraw => exact Or.inl ⟨raw, hraw⟩
  next =>
    by_cases hp : bound.request.kind = "policyNegative"
    · exact Or.inr (Or.inl hp)
    · by_cases hd : bound.request.kind = "documentation"
      · exact Or.inr (Or.inr hd)
      · simp [hp, hd, throw, throwThe, MonadExceptOf.throw] at hobs


theorem qualifyKind_sound {record result : Json} {bound : ExampleBinding} {req : ExampleRequest}
    {mode : EvidenceMode} {code : Nat} {status kind : String} {actual : Array Finding}
    (h : qualifyKind record result bound req mode code status kind actual = .ok ()) :
    (kind = "positive" ∨ kind = "policyRejection" ∨ kind = "diagnosticDemonstration") ∧
    (kind = "diagnosticDemonstration" → ∃ rule,
      (field record "rule" >>= RegistryCodec.parseRule) = .ok rule ∧
      DemonstrationOK ⟨bound, rule, actual⟩
        ⟨{ bound with request := req }, .completed, .checked actual false⟩) := by
  unfold qualifyKind at h
  split at h
  · exact ⟨Or.inl rfl, by simp⟩
  · exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · refine ⟨Or.inr (Or.inr rfl), fun _ => ?_⟩
    split at h
    · simp only [bind_eq_ok] at h
      obtain ⟨rj, hrj, rule, hrule, admitted, hadm, _⟩ := h
      exact
          ⟨rule, by simp [bind_eq_ok, hrj, hrule], (admitDemonstration_sound _ _ admitted hadm).1 ▸
              admitted.property.2⟩
    · simp only [throw_bind] at h
      cases h
  · simp at h


/-- What admitting one rule-example record establishes about the record itself. -/
def RecordAdmissible (record : Json) : Prop :=
  ∃ result mode bound code displayed kind actual,
    field record "result" = .ok result ∧
    (∀ entry ∈ ResultProtocol.identityFields,
      ∃ value, field result entry.1 = .ok value ∧ (value == entry.2) = true) ∧
    (string record "mode" >>= RegistryCodec.parseMode) = .ok mode ∧
    string result "mode" = .ok mode.spelling ∧
    (∃ before after, field record "before" = .ok before ∧ field record "after" = .ok after ∧
      (before == after) = true) ∧
    binding record mode = .ok bound ∧
    (∃ requestJson, field record "request" = .ok requestJson ∧
      (fromJson? requestJson : Except String ExampleRequest) = .ok bound.request) ∧
    (∃ requestJson, field result "request" = .ok requestJson ∧
      (fromJson? requestJson : Except String ExampleRequest) = .ok bound.request) ∧
    (field record "exitCode" >>= Json.getNat?) = .ok code ∧ code ≤ 3 ∧
    string record "source" = .ok displayed ∧
    (∃ observed, observedSources result bound = .ok observed ∧
      ExampleSourcesOK bound.snapshot.val.sources observed displayed ∧
      (bound.request.kind = "file" ∨ bound.request.kind = "policyNegative" →
        ∃ s ∈ observed, s.uri = bound.request.subject ∧ s.source = displayed)) ∧
    ((∃ raw, field result "sourceAccount" = .ok raw) ∨
      bound.request.kind = "policyNegative" ∨ bound.request.kind = "documentation") ∧
    ((field result "diagnostics" >>= Json.getArr?) >>=
      (·.mapM DiagnosticCodec.parseDiagnostic)) = .ok actual ∧
    string record "kind" = .ok kind ∧
    (kind = "positive" ∨ kind = "policyRejection" ∨ kind = "diagnosticDemonstration") ∧
    (kind = "diagnosticDemonstration" → ∃ rule,
      (field record "rule" >>= RegistryCodec.parseRule) = .ok rule ∧
      DemonstrationOK ⟨bound, rule, actual⟩ ⟨bound, .completed, .checked actual false⟩)

theorem qualify_sound (record : Json) (h : qualify record = .ok ()) : RecordAdmissible record := by
  obtain ⟨result, mode, bound, req, code, actual, status, kind, displayed, hr, hid, hmode,
      hrm, hb, hreq,
    _, hcode, hle, hfind, _, hk, hsrc, hsa, hq⟩ := qualify_parts record h
  obtain ⟨before, after, hbefore, hafter, hstable, _, rj, hrj, hbreq⟩ := binding_sound hb
  obtain ⟨rfl, oj, hoj, horeq⟩ := requestAccount_sound hreq
  obtain ⟨hsources, hpresent⟩ := sourceAccount_sound hsa
  obtain ⟨hkind, hdemo⟩ := qualifyKind_sound hq
  refine ⟨result, mode, bound, code, displayed, kind, actual, hr, fun e he => checkIdentity_sound
                                                                               (hid e he),
    hmode, hrm, ⟨before, after, hbefore, hafter, hstable⟩, hb, ⟨rj, hrj, hbreq⟩, ⟨oj, hoj, horeq⟩,
    hcode, hle, hsrc, hsources, hpresent, checkFindings_sound hfind, hk, hkind, ?_⟩
  simpa using hdemo

/-- Full-corpus coverage derives from the sole closed registry; every selected rule has
one fixed and one intended diagnostic record, each produced in its own fresh workspace
with no restored rerun (standard §7.8). -/
def qualifyCorpus (json : Json) : Except String Unit := do
  unless (← field json "schemaVersion") == toJson (1 : Nat) do throw "unsupported corpus schema"
  let selected ← (← (← field json "selected").getArr?).mapM RegistryCodec.parseRule
  unless decide selected.toList.Nodup do throw "duplicate selected rule"
  let complete ← (← field json "completeCorpus").getBool?
  if complete then
    unless selected.size == RuleId.all.length && RuleId.all.all selected.contains do
      throw "incomplete rule corpus: not every registered rule"
  let checkerBefore ← field json "checkerBefore"
  unless checkerBefore == (← field json "checkerAfter") do throw "checker sources changed"
  let checkerFiles ← sources checkerBefore
  unless !checkerFiles.isEmpty do throw "missing checker source state"
  let records := (← (← field json "records").getArr?).map
    (fun record => record.setObjVal! "checkerSources" checkerBefore)
  unless records.size == selected.size * 2 do throw "missing or extra fixture phase"
  for rule in selected do
    for phase in #["Fixed", "Violation"] do
      let matching ← records.filterM fun record => do
        return (← string record "rule") == rule.spelling && (← string record "phase") == phase
      unless matching.size == 1 do throw "missing or repeated fixture phase"
      let some record := matching[0]? | throw "missing fixture record"
      unless ((← string record "kind") == "positive") == (phase != "Violation") do
        throw "fixture phase classification mismatch"
      qualify record

end Regula.Checker.RuleExampleQualification

-- Exact dependency ceiling for the record-admission guarantee: Standard-Logical.
run_cmd do
  for name in #[``Regula.Checker.RuleExampleQualification.qualify_sound] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun ax => #[`propext, `Quot.sound, `Classical.choice].contains ax) do
      throwError "record-admission theorem {name} exceeds Standard-Logical: {axioms}"
