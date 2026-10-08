import Regula.RegistryCodec
import Regula.JsonAgreement

/-! # Fail-closed diagnostic transport

Fail-closed diagnostic transport. Decode to the indexed domain, then compare with
canonical re-encoding to reject unknown fields and redundant-coordinate disagreement.
Payloads are indexed by the registry's closed `RuleId` (design credit in Regula.RuleId).

Each decoder is `JsonAgreement.canonical` of a reader of the members and of the encoder of
`Regula.RegistryCodec`. The comparison is the registered decision `JsonAgreement.agrees`, so
`parseLocation_canonical` and `parseDiagnostic_canonical` hold for every input: an accepted
value agrees with the encoding of what the decoder returns. `checked_parseLocation` and
`checked_parseDiagnostic` register the sound kinds. These theorems are relative to the encoder
that the decoder runs. They do not say that the encoder writes the intended form, and they do
not say that a decoder accepts every encoding. -/
namespace Regula.DiagnosticCodec
open Lean RegistryCodec
open Regula.JsonAgreement (Agree canonical canonical_eq_ok_iff canonical_encode)

private def field (j : Json) (k : String) : Except String Json := j.getObjVal? k
private def string (j : Json) (k : String) : Except String String := do
  (← field j k).getStr?
private def nat (j : Json) (k : String) : Except String Nat := do
  (← field j k).getNat?

private def byteRange (j : Json) : Except String ByteRange := do
  return ⟨← nat j "startByte", ← nat j "endByte"⟩

/-- Read a module, project or source location from the members of an object; a source
location's coordinates must pass `admitSource`. A source location's text is its `sourceText`
member, as `SourceTexts.expand` leaves it for a location read from a result file. -/
private def readLocation (j : Json) : Except String Location := do
  match ← string j "kind" with
    | "module" => pure <| Location.module (← parsePrintedNameJson (← field j "name"))
    | "project" => pure <| Location.project (← string j "identity")
    | "source" => do
        let c : SourceCandidate := {
          snapshot := ⟨← string j "uri", ← string j SourceTexts.textKey⟩
          full := ← byteRange (← field j "range")
          selection := ← byteRange (← field j "selectionRange") }
        pure <| Location.source (← admitSource c)
    | _ => throw "unknown location kind"

/-- Decode a module, project or source location (`readLocation`); the input must agree with the
canonical `locationJson` of the result (`parseLocation_canonical`). -/
@[regula_decision]
def parseLocation (j : Json) : Except String Location :=
  canonical readLocation locationJson "noncanonical location or unknown fields" j

/-- **An accepted location is canonical.** The input agrees with the encoding of the location
that the decoder returns: it has the members that `locationJson` writes, with those values, and
no other member. -/
theorem parseLocation_canonical {j : Json} {location : Location}
    (accepted : parseLocation j = .ok location) : Agree j (locationJson location) :=
  ((canonical_eq_ok_iff _ _ _ j location).mp accepted).2

/-- The decoder accepts the encoding of each project location, and returns that location. -/
theorem parseLocation_project (identity : String) :
    parseLocation (locationJson (.project identity)) = .ok (.project identity) :=
  canonical_encode _ rfl

/-- `parseLocation` is a sound decision of the encoded locations (`parseLocation_canonical`): it
accepts only an input that agrees with the encoding of a location, and it accepts the encoding
of a project location. The kind is one-way. That it accepts the encoding of each location is
proved for a project location only (`parseLocation_project`), and an input that agrees with an
encoding can have an object tree that is not a search tree, in which the reader does not find a
member. The specification names the encoder `locationJson`, which the decoder runs: the kind
does not say that the encoder writes the intended form. -/
theorem checked_parseLocation : Regula.ExecutableContract parseLocation
    (Regula.DecidesSoundly (·.isOk = true) fun j => ∃ location, Agree j (locationJson location)) :=
  ⟨{ sound := fun j accepted => by
       cases found : parseLocation j with
       | ok location => exact ⟨location, parseLocation_canonical found⟩
       | error message => rw [found] at accepted; exact absurd accepted Bool.false_ne_true
     accepted := ⟨locationJson (.project ""), by rw [parseLocation_project]; rfl⟩ }⟩

private def parseSource (j : Json) : Except String (Option Name) := do
  match ← field j "sourceDeclaration" with
  | .null => return none
  | name => return some (← parsePrintedNameJson name)

private def parseArguments (id : RuleId) (j : Json) : Except String (Payload id) := do
  let detail ← string j "detail"
  match (dependent := true) id with
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded
  | .escapeHatch | .executableContract | .decisionContract | .sharedTest
  | .materialDocumentation | .materialIntent =>
      return { declaration := ← parsePrintedNameJson (← field j "declaration"),
               sourceDeclaration := ← parseSource j, detail := detail : DeclarationArguments }
  | .executionUnresolved | .executionBoundary =>
      return ⟨← parsePrintedNameJson (← field j "root"), detail⟩
  | .environment | .configuration | .sourceBuild | .coverage | .admission | .communityConfiguration
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample
  | .moduleDocumentation => return ⟨← string j "subject", detail⟩

/-- Read one finding from the members of an object: its rule, payload, location, mode, claim,
impact, severity and related locations, built through `makeDiagnostic`. -/
private def readDiagnostic (j : Json) : Except String Finding := do
  let id ← parseRule (← field j "id")
  let arguments ← parseArguments id (← field j "arguments")
  let location ← parseLocation (← field j "location")
  let mode ← parseMode (← string j "mode")
  let claim ← match ← field j "claim" with
    | .null => pure none
    | .str s => pure (some s)
    | _ => throw "invalid claim"
  let impact ← match ← string j "impact" with
    | "violation" => pure Impact.violation | "incomplete" => pure Impact.incomplete
    | _ => throw "unknown strict impact"
  let severity ← match ← string j "severity" with
    | "error" => pure Severity.error | "warning" => pure Severity.warning
    | "information" => pure Severity.information | _ => throw "unknown display severity"
  let related ← (← (← field j "related").getArr?).mapM fun r => do
    let relation ← string r "relation"
    let location ← parseLocation (← field r "location")
    return ({ relation, location } : RelatedLocation)
  let d ← makeDiagnostic id arguments location mode claim impact severity related
  return ⟨id, d⟩

/-- Decode one finding (`readDiagnostic`); the input must agree with the canonical
`diagnosticJson` of the result, so unknown fields and inconsistent coordinates are refused
(`parseDiagnostic_canonical`). -/
@[regula_decision]
def parseDiagnostic (j : Json) : Except String Finding :=
  canonical readDiagnostic diagnosticJson "noncanonical diagnostic or unknown fields" j

/-- **An accepted finding is canonical.** The input agrees with the encoding of the finding that
the decoder returns: it has the members that `diagnosticJson` writes, with those values, and no
other member. The rendered text, the remedy and the help address are such members, so a value
of one of them that the registry of this checker does not give is refused. -/
theorem parseDiagnostic_canonical {j : Json} {finding : Finding}
    (accepted : parseDiagnostic j = .ok finding) : Agree j (diagnosticJson finding) :=
  ((canonical_eq_ok_iff _ _ _ j finding).mp accepted).2

/-- A finding at a project location with no related location. -/
private def sample : Finding :=
  ⟨.environment, { arguments := ⟨"subject", "detail"⟩, location := .project "project",
                   mode := .freshProject, claim := none, impact := .incomplete,
                   severity := .error, related := #[], supportedMode := by decide }⟩

/-- **The decoder accepts an encoding.** It reads the encoding of one finding at a project
location back to that finding, so `parseDiagnostic_canonical` is about a decoder that accepts an
input. That it accepts the encoding of every finding is not proved. -/
theorem parseDiagnostic_accepts :
    ∃ finding, parseDiagnostic (diagnosticJson finding) = .ok finding := by
  refine ⟨sample, canonical_encode _ ?_⟩
  have id : field (diagnosticJson sample) "id" = .ok (ruleJson .environment) := rfl
  have arguments : field (diagnosticJson sample) "arguments" =
      .ok (Json.mkObj [("subject", .str "subject"), ("detail", .str "detail")]) := rfl
  have parsed : parseArguments .environment
      (Json.mkObj [("subject", .str "subject"), ("detail", .str "detail")]) =
        .ok ⟨"subject", "detail"⟩ := rfl
  have location : field (diagnosticJson sample) "location" =
      .ok (locationJson (.project "project")) := rfl
  have mode : string (diagnosticJson sample) "mode" = .ok "freshProject" := rfl
  have claim : field (diagnosticJson sample) "claim" = .ok .null := rfl
  have impact : string (diagnosticJson sample) "impact" = .ok "incomplete" := rfl
  have severity : string (diagnosticJson sample) "severity" = .ok "error" := rfl
  have related : field (diagnosticJson sample) "related" = .ok (.arr #[]) := by
    have written : field (diagnosticJson sample) "related" =
        .ok (toJson ((#[] : Array RelatedLocation).map fun r => Json.mkObj [
          ("relation", toJson r.relation), ("location", locationJson r.location)])) := rfl
    rw [written]
    simp [toJson, Array.toJson]
  simp only [readDiagnostic, id, arguments, parsed, location, mode, claim, impact, severity,
    related, rule_roundtrip, parseLocation_project, bind, Except.bind]
  have run : parseMode "freshProject" = .ok .freshProject := rfl
  have made : makeDiagnostic .environment (⟨"subject", "detail"⟩ : ContextArguments)
      (.project "project") .freshProject none .incomplete .error #[] = .ok sample.2 := rfl
  simp only [run, Json.getArr?, pure, Except.pure, Functor.map, Except.map, List.mapM_nil,
    Array.mapM_eq_mapM_toList, made]
  rfl
/-- `parseDiagnostic` is a sound decision of the encoded findings (`parseDiagnostic_canonical`):
it accepts only an input that agrees with the encoding of a finding, and it accepts the encoding
of one finding (`parseDiagnostic_accepts`). The kind is one-way. That it accepts the encoding of
each finding is not proved, and an input that agrees with an encoding can have an object tree
that is not a search tree, in which the reader does not find a member. The specification names
the encoder `diagnosticJson`, which the decoder runs: the kind does not say that the encoder
writes the intended form. -/
theorem checked_parseDiagnostic : Regula.ExecutableContract parseDiagnostic
    (Regula.DecidesSoundly (·.isOk = true) fun j => ∃ finding, Agree j (diagnosticJson finding)) :=
  ⟨{ sound := fun j accepted => by
       cases found : parseDiagnostic j with
       | ok finding => exact ⟨finding, parseDiagnostic_canonical found⟩
       | error message => rw [found] at accepted; exact absurd accepted Bool.false_ne_true
     accepted := by
       obtain ⟨finding, accepts⟩ := parseDiagnostic_accepts
       exact ⟨diagnosticJson finding, by rw [accepts]; rfl⟩ }⟩

end Regula.DiagnosticCodec
