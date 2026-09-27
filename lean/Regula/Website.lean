import Regula.DiagnosticCodec
import RegulaPolicy.Observation

/-! # Website metadata and example interfaces

Shared website metadata and checked-example interfaces. The registry metadata's
design credit is in RuleId; presentation credits Verso and Microsoft CA1416, neither of
which supplies rule semantics. Collector completion remains an explicit trusted boundary. -/
namespace Regula.Website
open Lean RegistryCodec

/-- Policy rejection may follow successful elaboration; it is not a compiler failure. -/
inductive ExampleExpectation where
  /-- The example is checked, not as trusted teaching, with no finding. -/
  | positive
  /-- The compiler rejects the example with a message the pattern `expectedMessage` matches
  (`RegulaPolicy.matchesPattern`). -/
  | compilerRejection (expectedMessage : String)
  /-- The example is checked and `rule` rejects it: exactly one finding, a violation of `rule`,
  where `subreason` is the rule's applicability. -/
  | policyRejection (rule : RuleId) (subreason : String)
  /-- The example is checked as trusted teaching with no finding. -/
  | trustedTeaching

/-- Only a completed collector may supply a classified outcome. -/
inductive ExampleOutcome where
  /-- The collector did not complete; `detail` says why. No expectation accepts it. -/
  | incomplete (detail : String)
  /-- The compiler rejected the example with `messages`. -/
  | compilerRejected (messages : Array String)
  /-- The example elaborated and was checked with `findings`; `compilerTeaching` is `true` when
  it was checked as a trusted teaching example. -/
  | checked (findings : Array Finding) (compilerTeaching : Bool)

/-- Succeeds when `outcome` meets `expected` as each `ExampleExpectation` constructor states;
otherwise fails with the mismatch, including for any incomplete outcome. -/
def validateExample (expected : ExampleExpectation) (outcome : ExampleOutcome) : Except String Unit := do
  match expected, outcome with
  | .positive, .checked findings false =>
      unless findings.isEmpty do throw "unexpected diagnostics in positive example"
  | .trustedTeaching, .checked findings true =>
      unless findings.isEmpty do throw "unexpected diagnostics in trusted teaching example"
  | .compilerRejection text, .compilerRejected messages =>
      unless messages.any (RegulaPolicy.matchesPattern text) do throw "wrong compiler rejection"
  | .policyRejection rule subreason, .checked findings false =>
      unless !subreason.isEmpty && subreason == (descriptor rule).applicability && findings.size == 1 do
        throw "wrong policy diagnostic expectation"
      let some finding := findings[0]? | throw "missing policy diagnostic"
      unless finding.1 == rule && finding.2.impact == .violation do throw "wrong policy rejection"
      -- A source-free detector retains its authentic module/project attribution.
      -- Exact location, detail and snapshot matching belongs to validateBoundExample.
      pure ()
  | _, .incomplete detail => throw s!"example collection incomplete: {detail}"
  | _, _ => throw "example outcome does not match its classification"


/-- The request a corpus producer run was given for one example, recorded before the run. -/
structure ExampleRequest where
  /-- The route: `file`, `project`, `documentation` or `policyNegative`. -/
  kind : String
  /-- The example project's directory. -/
  project : String
  /-- What is checked: the example file for `file` and `policyNegative`, the `docs` directory
  for `documentation`, and the project otherwise. -/
  subject : String
  /-- The foundation claim of a `file` request; `none` for the other kinds. -/
  claim : Option String
  /-- The execution mode of a `file` request; `none` for the other kinds. -/
  execution : Option String
  /-- Each configuration file path of the project with its text, `none` when it is absent. -/
  configuration : Array (String × Option String)
  deriving DecidableEq, ToJson, FromJson

/-- Admit `observed` only when it equals the frozen `expected` request; the admitted value
carries both equalities. -/
def admitExampleRequest (expected observed : ExampleRequest) :
    Except String { request : ExampleRequest // request = observed ∧ request = expected } :=
  if h : observed = expected then .ok ⟨observed, rfl, h⟩
  else .error "producer request differs from frozen example request"

theorem admitExampleRequest_sound (expected observed : ExampleRequest)
    (request : { r : ExampleRequest // r = observed ∧ r = expected })
    (_ : admitExampleRequest expected observed = .ok request) :
    observed = expected := request.property.1.symm.trans request.property.2

/-- Exact observation identity. Dependency state and source bytes are retained rather than
replaced by a nominal revision or digest. Acquiring these values remains an IO obligation. -/
structure ExampleBinding where
  /-- The admitted sources, configuration, toolchain and checker dependency of the run. -/
  snapshot : RegulaPolicy.AdmittedSnapshot
  /-- The evidence mode the example was produced in. -/
  mode : EvidenceMode
  /-- The producer request. -/
  request : ExampleRequest
  deriving DecidableEq

/-- Every observed source is one of the expected sources, and some observed source has exactly
the `displayed` text. -/
def ExampleSourcesOK (expected observed : Array RegulaPolicy.SourceSnapshot)
    (displayed : String) : Prop :=
  (∀ source ∈ observed, source ∈ expected) ∧
  (∃ source ∈ observed, source.source = displayed)

instance (expected observed : Array RegulaPolicy.SourceSnapshot) (displayed : String) :
    Decidable (ExampleSourcesOK expected observed displayed) := by
  unfold ExampleSourcesOK
  infer_instance

/-- Admit the observed sources exactly when `ExampleSourcesOK` holds, carrying that proof
(`admitExampleSources_sound`, `admitExampleSources_complete`). -/
def admitExampleSources (expected observed : Array RegulaPolicy.SourceSnapshot)
    (displayed : String) :
    Except String { actual : Array RegulaPolicy.SourceSnapshot //
      actual = observed ∧ ExampleSourcesOK expected actual displayed } :=
  if h : ExampleSourcesOK expected observed displayed then .ok ⟨observed, rfl, h⟩
  else .error "missing or mismatched producer source account"

theorem admitExampleSources_sound (expected observed : Array RegulaPolicy.SourceSnapshot)
    (displayed : String)
    (admitted : { actual : Array RegulaPolicy.SourceSnapshot //
      actual = observed ∧ ExampleSourcesOK expected actual displayed })
    (_ : admitExampleSources expected observed displayed = .ok admitted) :
    ExampleSourcesOK expected observed displayed := admitted.property.1 ▸ admitted.property.2

theorem admitExampleSources_complete (expected observed : Array RegulaPolicy.SourceSnapshot)
    (displayed : String) (h : ExampleSourcesOK expected observed displayed) :
    admitExampleSources expected observed displayed = .ok ⟨observed, rfl, h⟩ := by
  simp [admitExampleSources, h]

/-- Canonical diagnostic encoding retains the indexed payload, full/selection ranges,
related locations, mode, claim, impact and severity. The codec validates actual findings. -/
def diagnosticRecords (findings : Array Finding) : List String :=
  findings.toList.map (fun finding => (diagnosticJson finding).compress)

/-- The collector's observation is separate from the requested binding. The operational
adapter must report crash/cancellation honestly; admission requires completed production. -/
structure BoundObservation where
  /-- The binding the collector reports it ran under. -/
  binding : ExampleBinding
  /-- Whether the collector's production completed. -/
  completion : RegulaPolicy.Completion
  /-- The classified outcome the collector reports. -/
  outcome : ExampleOutcome

/-- Exact snapshot/mode identity and completed production. This is a data relation,
not authentication of Lean or process observations. -/
def BindingOK (expected : ExampleBinding) (observed : BoundObservation) : Prop :=
  observed.binding = expected ∧ observed.completion = .completed
instance (expected : ExampleBinding) (observed : BoundObservation) :
    Decidable (BindingOK expected observed) := by unfold BindingOK; infer_instance

/-- Ranged findings use an exact source in the bound snapshot. Source-free observations
retain a nonempty module/project identity; their external attribution remains trusted. -/
def FindingBound (binding : ExampleBinding) (finding : Finding) : Prop :=
  finding.2.mode = binding.mode ∧ match finding.2.location with
  | .source source => source.val.snapshot ∈ binding.snapshot.val.sources
  | .module name => name ≠ .anonymous
  | .project identity => identity ≠ ""
instance (binding : ExampleBinding) (finding : Finding) : Decidable (FindingBound binding finding) := by
  unfold FindingBound
  cases finding.2.location <;> infer_instance

/-- Bound accepted examples retain exactly the original four classifications. -/
def validateBoundExample (binding : ExampleBinding) (expected : ExampleExpectation)
    (expectedFindings : Array Finding) (observed : BoundObservation) : Except String Unit := do
  unless decide (BindingOK binding observed) do throw "example binding or production incomplete"
  let actual := match observed.outcome with | .checked fs _ => fs | _ => #[]
  unless !actual.any (fun f => f.2.impact == .incomplete) do
    throw "incomplete diagnostics cannot qualify an accepted example"
  unless actual.all (fun f => decide (FindingBound binding f)) do
    throw "example diagnostic source or mode mismatch"
  unless diagnosticRecords actual == diagnosticRecords expectedFindings do
    throw "example diagnostic evidence mismatch"
  match expected, observed.outcome with
  | .policyRejection rule subreason, .checked findings false =>
      unless !subreason.isEmpty && subreason == (descriptor rule).applicability &&
          findings.any (fun f => f.1 == rule) && findings.all (fun f => f.2.impact == .violation) do
        throw "wrong policy rejection"
  | _, _ => validateExample expected observed.outcome

/-- Expected unavailable analysis is a diagnostic demonstration, never a fifth accepted
example kind. Exact findings and binding are required even though the audit is incomplete. -/
structure DemonstrationRequest where
  /-- The binding the demonstration must be observed under. -/
  binding : ExampleBinding
  /-- The rule whose unavailable analysis the demonstration shows. -/
  rule : RuleId
  /-- The exact findings expected, including an incomplete one for `rule`. -/
  findings : Array Finding

/-- Diagnostic production must complete; analysis unavailability is carried by the actual
findings. A crash or an empty/mismatched diagnostic list cannot satisfy this relation. -/
def DemonstrationOK (request : DemonstrationRequest) (observed : BoundObservation) : Prop :=
  BindingOK request.binding observed ∧ request.findings ≠ #[] ∧
  (∀ f ∈ request.findings, FindingBound request.binding f) ∧
  (∃ f ∈ request.findings, f.1 = request.rule ∧ f.2.impact = .incomplete) ∧
  match observed.outcome with
  | .checked actual false =>
      (∃ f ∈ actual, f.1 = request.rule ∧ f.2.impact = .incomplete) ∧
      (∀ f ∈ actual, FindingBound request.binding f) ∧
      diagnosticRecords actual = diagnosticRecords request.findings
  | _ => False
instance (request : DemonstrationRequest) (observed : BoundObservation) :
    Decidable (DemonstrationOK request observed) := by
  unfold DemonstrationOK
  cases observed.outcome with
  | incomplete _ => infer_instance
  | compilerRejected _ => infer_instance
  | checked _ teaching => cases teaching <;> infer_instance

/-- Admission returns the supplied observation unchanged with its exact relation. No
conversion to Accepted or accepted example expectations is provided. -/
def admitDemonstration (request : DemonstrationRequest) (observed : BoundObservation) :
    Except String { o : BoundObservation // o = observed ∧ DemonstrationOK request o } :=
  if h : DemonstrationOK request observed then .ok ⟨observed, rfl, h⟩
  else .error "diagnostic demonstration mismatch or incomplete production"

theorem admitDemonstration_complete (request : DemonstrationRequest) (observed : BoundObservation)
    (h : DemonstrationOK request observed) :
    admitDemonstration request observed = .ok ⟨observed, rfl, h⟩ := by
  simp [admitDemonstration, h]

theorem admitDemonstration_sound (request : DemonstrationRequest) (observed : BoundObservation)
    (accepted : { o : BoundObservation // o = observed ∧ DemonstrationOK request o })
    (_ : admitDemonstration request observed = .ok accepted) :
    accepted.val = observed ∧ DemonstrationOK request accepted.val := accepted.property

/-- Every admitted demonstration comes from completed diagnostic production, independently
of whether analysis was available. -/
theorem demonstration_completed (request : DemonstrationRequest) (observed : BoundObservation)
    (h : DemonstrationOK request observed) : observed.completion = .completed := h.1.2

/-- The incomplete finding is required in the observed list itself, independently of
any injectivity assumption about canonical JSON or its string renderer. -/
theorem demonstration_selected_rule (request : DemonstrationRequest)
    (observed : BoundObservation) (h : DemonstrationOK request observed) :
    ∃ actual, observed.outcome = .checked actual false ∧
      ∃ f ∈ actual, f.1 = request.rule ∧ f.2.impact = .incomplete := by
  rcases h with ⟨_, _, _, _, h⟩
  cases he : observed.outcome with
  | incomplete _ => simp [he] at h
  | compilerRejected _ => simp [he] at h
  | checked actual teaching =>
      cases teaching with
      | true => simp [he] at h
      | false =>
          simp only [he] at h
          exact ⟨actual, rfl, h.1⟩

theorem demonstration_observed_incomplete (request : DemonstrationRequest)
    (observed : BoundObservation) (h : DemonstrationOK request observed) :
    ∃ actual, observed.outcome = .checked actual false ∧
      ∃ f ∈ actual, f.2.impact = .incomplete := by
  obtain ⟨actual, outcome, f, member, _, impact⟩ := demonstration_selected_rule request observed h
  exact ⟨actual, outcome, f, member, impact⟩

/-- The executed accepted-example validator refuses every admitted demonstration,
for every one of the four expectations and any supplied expected finding list. -/
theorem demonstration_not_accepted (request : DemonstrationRequest)
    (observed : BoundObservation) (h : DemonstrationOK request observed)
    (expected : ExampleExpectation) (findings : Array Finding) :
    validateBoundExample request.binding expected findings observed ≠ .ok () := by
  obtain ⟨actual, outcome, f, member, impact⟩ := demonstration_observed_incomplete request observed h
  have incomplete : actual.any (fun f => f.2.impact == .incomplete) = true := by
    rw [Array.any_eq_true']
    exact ⟨f, member, by rw [impact]; rfl⟩
  simp [validateBoundExample, outcome, incomplete, h.1, bind, Except.bind, throw]

/-- This artifact list is supplied by the builder after inspecting its actual output tree. -/
def parsePage (j : Json) : Except String Page := do
  let rule ← parseRule (← j.getObjVal? "id")
  let route ← (← j.getObjVal? "route").getStr?
  let checkedExample ← (← j.getObjVal? "checkedExample").getBool?
  let advertisedEnforced ← (← j.getObjVal? "advertisedEnforced").getBool?
  unless j == Json.mkObj [("id", ruleJson rule), ("route", toJson route),
    ("checkedExample", toJson checkedExample), ("advertisedEnforced", toJson advertisedEnforced)] do
    throw "unknown page fields"
  return ⟨rule, route, checkedExample, advertisedEnforced⟩

/-- Required IDs come from the selected site scope plus every emitted example diagnostic.
Production #15 uses its full scope; the bounded prototype explicitly selects one rule. -/
def validateArtifact (p : ProducerIdentity) (manifest artifact : Json) : Except String Unit := do
  let required ← (← (← artifact.getObjVal? "required").getArr?).toList.mapM parseRule
  let emitted ← (← (← artifact.getObjVal? "emitted").getArr?).toList.mapM parseRule
  let rawPages ← (← artifact.getObjVal? "pages").getArr?
  let pages ← rawPages.toList.mapM parsePage
  unless artifact == Json.mkObj [("required", toJson (required.map ruleJson)),
    ("emitted", toJson (emitted.map ruleJson)), ("pages", toJson rawPages)] do
    throw "unknown artifact fields"
  unless emitted.all (fun id => required.contains id) do throw "emitted diagnostic has no required page"
  validatePages p manifest required pages
end Regula.Website
