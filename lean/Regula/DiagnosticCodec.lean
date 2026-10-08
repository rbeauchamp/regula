import Regula.RegistryCodec
import Regula.JsonAgreement

/-! # Fail-closed diagnostic transport

Fail-closed diagnostic transport. Decode to the indexed domain, then compare with
canonical re-encoding to reject unknown fields and redundant-coordinate disagreement.
Payloads are indexed by the registry's closed `RuleId` (design credit in Regula.RuleId).

Each decoder is `JsonAgreement.canonical` of a reader of the members and of an encoder of
`Regula.RegistryCodec`. The comparison is the registered decision `JsonAgreement.agrees`.

The form of an encoded location and of an encoded finding is stated here without an encoder:
`LocationWire` and `FindingWire` say which members the object has and what the value of each is
(`JsonAgreement.Shaped`). The encoders write that form (`locationJson_wire`,
`diagnosticJson_wire`), and the decoders accept each value of that form and return the location
or the finding of it (`parseLocation_of_wire`, `parseDiagnostic_of_wire`). So each decoder reads
the encoding of each value back to that value (`parseLocation_roundtrip`,
`parseDiagnostic_roundtrip`).

The converse, that an accepted value has the form, is proved for an input whose object trees are
search trees (`parseLocation_iff`, `parseDiagnostic_iff`). It is false for some other `Json`
values: the comparison reads each member of the input and looks its name up in the encoding, and
the reader does not look up a redundant member, so an object tree that gives one name twice and
has no member `remedy` is accepted
(https://github.com/rbeauchamp/regula/issues/269). The registered kind of each decoder is
complete for that reason, and `parseLocation_canonical` and `parseDiagnostic_canonical` state,
for every input, the agreement of an accepted value with the encoding that the decoder runs. -/
namespace Regula.DiagnosticCodec
open Lean RegistryCodec
open Regula.JsonAgreement (Agree Aligned Entry Shaped canonical canonical_eq_ok_iff)

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

/-- **An accepted location agrees with its encoding.** The input has as many members as the
encoding of the location that the decoder returns, and each member of the input is found by its
name in that encoding, with a value that it agrees with. So the input has no member with a name
that `locationJson` does not write, and the value of each member agrees with the written value,
which is equality for a string, a number, a Boolean and null. The theorem does not say that each
member of the encoding is a member of the input: an object tree that is not a search tree can
give one name twice and not give a second name. For an input whose object trees are search trees,
`parseLocation_wire` gives the members. -/
theorem parseLocation_canonical {j : Json} {location : Location}
    (accepted : parseLocation j = .ok location) : Agree j (locationJson location) :=
  ((canonical_eq_ok_iff _ _ _ j location).mp accepted).2

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

/-- **An accepted finding agrees with its encoding.** The input has as many members as the
encoding of the finding that the decoder returns, and each member of the input is found by its
name in that encoding, with a value that it agrees with. So the input has no member with a name
that `diagnosticJson` does not write, and the value of each member agrees with the written value,
which is equality for a string, a number, a Boolean and null: a member `text`, `remedy` or
`helpUrl` with a value that the registry of this checker does not give is refused. The theorem
does not say that
each member of the encoding is a member of the input: an object tree that is not a search tree
can give one name twice and have no member `remedy`
(https://github.com/rbeauchamp/regula/issues/269). For an input whose object trees are search
trees, `parseDiagnostic_wire` gives the members. -/
theorem parseDiagnostic_canonical {j : Json} {finding : Finding}
    (accepted : parseDiagnostic j = .ok finding) : Agree j (diagnosticJson finding) :=
  ((canonical_eq_ok_iff _ _ _ j finding).mp accepted).2

/-! ## The form of an encoded value

Each relation says which members an object has, and what the value of each is. No relation of
this section mentions an encoder of this library. Three meanings name a written form that another
codec states: the form of a name (`printedNameJson`, with `printedNameJson_roundtrip`), the form
that Lean writes for a natural number, and the form that Lean writes for an LSP range. -/

/-- The form of a byte range: an object with two members. `endByte` is the offset one past the
last byte, and `startByte` is the offset of the first byte, each as a number. -/
def RangeWire (range : ByteRange) : Json → Prop :=
  Shaped [⟨"endByte", (· = toJson range.stop)⟩, ⟨"startByte", (· = toJson range.start)⟩]

/-- The form of a location.

A module has the members `kind`, the string `module`, and `name`, the written form of the name.

A project has the members `identity`, a string, and `kind`, the string `project`.

A source has seven members. `kind` is the string `source`. `uri` and `sourceText` are the strings
of the snapshot. `range` and `selectionRange` are the two byte ranges. `lspRange` and
`lspSelectionRange` are redundant: each agrees with the form that Lean writes for the LSP range
that the source text gives for the byte range. -/
def LocationWire : Location → Json → Prop
  | .module name => Shaped [⟨"kind", (· = .str "module")⟩, ⟨"name", (· = printedNameJson name)⟩]
  | .project identity =>
      Shaped [⟨"identity", (· = .str identity)⟩, ⟨"kind", (· = .str "project")⟩]
  | .source source => Shaped [
      ⟨"kind", (· = .str "source")⟩,
      ⟨"lspRange", (Agree · (toJson source.fullLsp))⟩,
      ⟨"lspSelectionRange", (Agree · (toJson source.selectionLsp))⟩,
      ⟨"range", RangeWire source.val.full⟩,
      ⟨"selectionRange", RangeWire source.val.selection⟩,
      ⟨"sourceText", (· = .str source.val.snapshot.source)⟩,
      ⟨"uri", (· = .str source.val.snapshot.uri)⟩]

/-! ## The encoders write the form -/

/-- The written form of a name agrees with itself: it is a string, or an array of arrays of
strings and numbers, so it has no object. -/
private theorem agree_printedName (name : Name) :
    Agree (printedNameJson name) (printedNameJson name) := by
  have parts : ∀ name : Name, JsonAgreement.AgreeAll (nameParts name) (nameParts name) := by
    intro name
    induction name with
    | anonymous => exact .nil
    | str parent value step =>
      exact .cons (.arr (.cons (.str _) (.cons (.str _) .nil))) step
    | num parent value step =>
      exact .cons (.arr (.cons (.str _) (.cons (.num _) .nil))) step
  unfold printedNameJson
  split
  · exact .str _
  · exact .arr (parts name)

/-- The form that Lean writes for an LSP position agrees with itself. -/
private theorem agree_position (position : Lsp.Position) :
    Agree (toJson position) (toJson position) :=
  Agree.obj_self _ [("character", toJson position.character), ("line", toJson position.line)]
    rfl fun member present => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact .num _

/-- The form that Lean writes for an LSP range agrees with itself. -/
private theorem agree_lspRange (range : Lsp.Range) : Agree (toJson range) (toJson range) :=
  Agree.obj_self _ [("end", toJson range.end), ("start", toJson range.start)]
    rfl fun member present => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> exact agree_position _

/-- The encoder of a byte range writes the form of that range. -/
theorem rangeJson_wire (range : ByteRange) : RangeWire range (rangeJson range) :=
  Shaped.of_members _ [("endByte", toJson range.stop), ("startByte", toJson range.start)]
    rfl (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil))

/-- **The encoder of a location writes the form of that location.** -/
theorem locationJson_wire (location : Location) :
    LocationWire location (locationJson location) := by
  cases location with
  | module name =>
    exact Shaped.of_members _ [("kind", .str "module"), ("name", printedNameJson name)]
      rfl (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil))
  | project identity =>
    exact Shaped.of_members _ [("identity", .str identity), ("kind", .str "project")]
      rfl (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil))
  | source source =>
    exact Shaped.of_members _
      [("kind", .str "source"), ("lspRange", toJson source.fullLsp),
        ("lspSelectionRange", toJson source.selectionLsp),
        ("range", rangeJson source.val.full), ("selectionRange", rangeJson source.val.selection),
        ("sourceText", .str source.val.snapshot.source), ("uri", .str source.val.snapshot.uri)]
      rfl
      (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, agree_lspRange _⟩ (.cons ⟨rfl, agree_lspRange _⟩
        (.cons ⟨rfl, rangeJson_wire _⟩ (.cons ⟨rfl, rangeJson_wire _⟩
          (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil)))))))

/-! ## The decoders accept the form -/

/-- A value of the form of a byte range agrees with the encoding of that range. -/
private theorem agree_of_rangeWire {range : ByteRange} {j : Json} (wire : RangeWire range j) :
    Agree j (rangeJson range) :=
  wire.agree_of_members _ [("endByte", toJson range.stop), ("startByte", toJson range.start)]
    rfl
    (.cons ⟨rfl, fun value same => by rw [same]; exact .num _⟩
      (.cons ⟨rfl, fun value same => by rw [same]; exact .num _⟩ .nil))

/-- The reader of a byte range reads a value of the form of a range to that range. -/
private theorem byteRange_of_wire {range : ByteRange} {j : Json} (wire : RangeWire range j) :
    byteRange j = .ok range := by
  obtain ⟨stop, readStop, rfl⟩ := wire.member (.head _)
  obtain ⟨start, readStart, rfl⟩ := wire.member (.tail _ (.head _))
  simp only [byteRange, nat, field, readStart, readStop, bind, Except.bind]
  rfl

/-- A value of the form of a location agrees with the encoding of that location. -/
theorem agree_of_locationWire {location : Location} {j : Json}
    (wire : LocationWire location j) : Agree j (locationJson location) := by
  cases location with
  | module name =>
    exact wire.agree_of_members _ [("kind", .str "module"), ("name", printedNameJson name)]
      rfl (.cons ⟨rfl, fun _ same => same ▸ .str _⟩
        (.cons ⟨rfl, fun _ same => same ▸ agree_printedName name⟩ .nil))
  | project identity =>
    exact wire.agree_of_members _ [("identity", .str identity), ("kind", .str "project")]
      rfl (.cons ⟨rfl, fun _ same => same ▸ .str _⟩
        (.cons ⟨rfl, fun _ same => same ▸ .str _⟩ .nil))
  | source source =>
    exact wire.agree_of_members _
      [("kind", .str "source"), ("lspRange", toJson source.fullLsp),
        ("lspSelectionRange", toJson source.selectionLsp),
        ("range", rangeJson source.val.full), ("selectionRange", rangeJson source.val.selection),
        ("sourceText", .str source.val.snapshot.source), ("uri", .str source.val.snapshot.uri)]
      rfl
      (.cons ⟨rfl, fun _ same => same ▸ .str _⟩ (.cons ⟨rfl, fun _ agree => agree⟩
        (.cons ⟨rfl, fun _ agree => agree⟩ (.cons ⟨rfl, fun _ wire => agree_of_rangeWire wire⟩
          (.cons ⟨rfl, fun _ wire => agree_of_rangeWire wire⟩
            (.cons ⟨rfl, fun _ same => same ▸ .str _⟩
              (.cons ⟨rfl, fun _ same => same ▸ .str _⟩ .nil)))))))

/-- The reader of a location reads a value of the form of a location to that location. -/
private theorem readLocation_of_wire {location : Location} {j : Json}
    (wire : LocationWire location j) : readLocation j = .ok location := by
  cases location with
  | module name =>
    obtain ⟨kind, readKind, rfl⟩ := wire.member (.head _)
    obtain ⟨written, readName, rfl⟩ := wire.member (.tail _ (.head _))
    simp only [readLocation, string, field, readKind, readName, bind, Except.bind, Json.getStr?,
      printedNameJson_roundtrip]
    rfl
  | project identity =>
    obtain ⟨written, readIdentity, rfl⟩ := wire.member (.head _)
    obtain ⟨kind, readKind, rfl⟩ := wire.member (.tail _ (.head _))
    simp only [readLocation, string, field, readKind, readIdentity, bind, Except.bind,
      Json.getStr?]
    rfl
  | source source =>
    obtain ⟨kind, readKind, rfl⟩ := wire.member (.head _)
    obtain ⟨full, readFull, fullWire⟩ := wire.member (.tail _ (.tail _ (.tail _ (.head _))))
    obtain ⟨selection, readSelection, selectionWire⟩ :=
      wire.member (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    obtain ⟨text, readText, rfl⟩ :=
      wire.member (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    obtain ⟨uri, readUri, rfl⟩ :=
      wire.member (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
    have admitted : admitSource source.val = .ok source := by
      unfold admitSource
      split
      · rfl
      · exact absurd source.property ‹_›
    simp only [readLocation, string, field, readKind, readFull, readSelection, readText,
      readUri, bind, Except.bind, Json.getStr?, byteRange_of_wire fullWire,
      byteRange_of_wire selectionWire, SourceTexts.textKey]
    exact congrArg (fun result => result.map Location.source) admitted

/-- **The decoder of a location accepts each value of the form of a location**, and returns that
location. -/
theorem parseLocation_of_wire {location : Location} {j : Json}
    (wire : LocationWire location j) : parseLocation j = .ok location :=
  (canonical_eq_ok_iff _ _ _ _ _).mpr ⟨readLocation_of_wire wire, agree_of_locationWire wire⟩

/-- **Each location is read back from its encoding.** -/
theorem parseLocation_roundtrip (location : Location) :
    parseLocation (locationJson location) = .ok location :=
  parseLocation_of_wire (locationJson_wire location)

/-! ## The form of a payload, of a related location and of a finding -/

/-- The form of the payload of a declaration rule: an object with three members. `declaration` is
the written form of the name of the declaration. `detail` is a string. `sourceDeclaration` is the
written form of the name of the source declaration, or `null` when there is none. -/
def DeclarationWire (arguments : DeclarationArguments) : Json → Prop :=
  Shaped [⟨"declaration", (· = printedNameJson arguments.declaration)⟩,
    ⟨"detail", (· = .str arguments.detail)⟩,
    ⟨"sourceDeclaration", (· = match arguments.sourceDeclaration with
      | none => .null
      | some name => printedNameJson name)⟩]

/-- The form of the payload of an execution rule: `detail` is a string, and `root` is the written
form of the name of the execution root. -/
def ExecutionWire (arguments : ExecutionArguments) : Json → Prop :=
  Shaped [⟨"detail", (· = .str arguments.detail)⟩, ⟨"root", (· = printedNameJson arguments.root)⟩]

/-- The form of the payload of a rule of a project, a configuration, a module or a document:
`detail` and `subject` are strings. -/
def ContextWire (arguments : ContextArguments) : Json → Prop :=
  Shaped [⟨"detail", (· = .str arguments.detail)⟩, ⟨"subject", (· = .str arguments.subject)⟩]

/-- The form of the payload of a rule, in the argument domain of that rule. -/
def ArgumentsWire : (id : RuleId) → Payload id → Json → Prop
  | .projectAxiom, a | .proofHole, a | .unknownAxiom, a | .compilerTrusting, a
  | .profileExceeded, a | .escapeHatch, a | .executableContract, a | .decisionContract, a
  | .sharedTest, a | .materialDocumentation, a | .materialIntent, a => DeclarationWire a
  | .executionUnresolved, a | .executionBoundary, a => ExecutionWire a
  | .environment, a | .configuration, a | .sourceBuild, a | .coverage, a
  | .admission, a | .communityConfiguration, a | .fenceStructure, a | .positiveExample, a
  | .negativeExample, a | .trustedExample, a | .moduleDocumentation, a => ContextWire a

/-- The form of a related location: `location` has the form of the location, and `relation` is a
string. -/
def RelatedWire (related : RelatedLocation) : Json → Prop :=
  Shaped [⟨"location", LocationWire related.location⟩, ⟨"relation", (· = .str related.relation)⟩]

/-- The form of a finding: an object with eleven members.

`id` is the spelling of the rule. `arguments` has the form of the payload of that rule.
`location` has the form of the location. `related` is an array with one value of the form of a
related location for each related location, in order. `mode` is the spelling of the evidence
mode. `claim` is the claim as a string, or `null` when there is none. `impact` is the string
`violation` or the string `incomplete`. `severity` is the spelling of the severity.

Three members are redundant: `text` is the rendered text of the finding, `remedy` is the remedy
of the rule in the registry, and `helpUrl` is the address of the page of the rule. -/
def FindingWire (finding : Finding) : Json → Prop :=
  Shaped [
    ⟨"arguments", ArgumentsWire finding.1 finding.2.arguments⟩,
    ⟨"claim", (· = match finding.2.claim with
      | none => .null
      | some claim => .str claim)⟩,
    ⟨"helpUrl", (· = .str (helpUrl finding.1))⟩,
    ⟨"id", (· = .str finding.1.spelling)⟩,
    ⟨"impact", (· = .str (match finding.2.impact with
      | .violation => "violation"
      | .incomplete => "incomplete"))⟩,
    ⟨"location", LocationWire finding.2.location⟩,
    ⟨"mode", (· = .str finding.2.mode.spelling)⟩,
    ⟨"related", fun value => ∃ items : Array Json, value = .arr items ∧
      Aligned (fun item related => RelatedWire related item) items.toList
        finding.2.related.toList⟩,
    ⟨"remedy", (· = .str (descriptor finding.1).remedy)⟩,
    ⟨"severity", (· = .str finding.2.severity.spelling)⟩,
    ⟨"text", (· = .str finding.2.text)⟩]

/-! ### The encoders write these forms -/

private theorem declaration_wire (a : DeclarationArguments) :
    DeclarationWire a (Json.mkObj [("declaration", printedNameJson a.declaration),
      ("sourceDeclaration", (a.sourceDeclaration.map printedNameJson).getD .null),
      ("detail", toJson a.detail)]) :=
  Shaped.of_members _
    [("declaration", printedNameJson a.declaration), ("detail", .str a.detail),
      ("sourceDeclaration", (a.sourceDeclaration.map printedNameJson).getD .null)]
    rfl
    (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, by cases a.sourceDeclaration <;> rfl⟩ .nil)))

private theorem execution_wire (a : ExecutionArguments) :
    ExecutionWire a (Json.mkObj [("root", printedNameJson a.root), ("detail", toJson a.detail)]) :=
  Shaped.of_members _ [("detail", .str a.detail), ("root", printedNameJson a.root)]
    rfl (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil))

private theorem context_wire (a : ContextArguments) :
    ContextWire a (Json.mkObj [("subject", toJson a.subject), ("detail", toJson a.detail)]) :=
  Shaped.of_members _ [("detail", .str a.detail), ("subject", .str a.subject)]
    rfl (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil))

/-- The encoder of a payload writes the form of that payload. -/
theorem argumentsJson_wire (id : RuleId) (arguments : Payload id) :
    ArgumentsWire id arguments (argumentsJson id arguments) := by
  cases id <;> first
    | exact declaration_wire arguments
    | exact execution_wire arguments
    | exact context_wire arguments

/-- The object that the encoder of a finding writes for one related location. -/
private abbrev relatedJson (related : RelatedLocation) : Json :=
  Json.mkObj [("relation", toJson related.relation), ("location", locationJson related.location)]

private theorem related_wire (related : RelatedLocation) :
    RelatedWire related (relatedJson related) :=
  Shaped.of_members _
    [("location", locationJson related.location), ("relation", .str related.relation)]
    rfl (.cons ⟨rfl, locationJson_wire _⟩ (.cons ⟨rfl, rfl⟩ .nil))

private theorem aligned_related (related : List RelatedLocation) :
    Aligned (fun item related => RelatedWire related item) (related.map relatedJson) related := by
  induction related with
  | nil => exact .nil
  | cons head rest step => exact .cons (related_wire head) step

/-- The value that the encoder of a finding writes for the related locations is the array of
their objects. -/
private theorem toJson_relatedJson (related : Array RelatedLocation) :
    toJson (related.map relatedJson) = .arr ⟨related.toList.map relatedJson⟩ := by
  simp only [toJson, Array.toJson, Array.map_map]
  exact congrArg Json.arr (Array.ext' (by simp))

/-- **The encoder of a finding writes the form of that finding.** -/
theorem diagnosticJson_wire (finding : Finding) : FindingWire finding (diagnosticJson finding) := by
  obtain ⟨id, d⟩ := finding
  exact Shaped.of_members _
    [("arguments", argumentsJson id d.arguments), ("claim", toJson d.claim),
      ("helpUrl", .str (helpUrl id)), ("id", .str id.spelling),
      ("impact", .str (if d.impact == .violation then "violation" else "incomplete")),
      ("location", locationJson d.location), ("mode", .str d.mode.spelling),
      ("related", toJson (d.related.map relatedJson)),
      ("remedy", .str (descriptor id).remedy), ("severity", .str d.severity.spelling),
      ("text", .str d.text)]
    rfl
    (.cons ⟨rfl, argumentsJson_wire id d.arguments⟩ (.cons ⟨rfl, by cases d.claim <;> rfl⟩
      (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, by cases d.impact <;> rfl⟩
        (.cons ⟨rfl, locationJson_wire _⟩ (.cons ⟨rfl, rfl⟩
          (.cons ⟨rfl, ⟨d.related.map relatedJson, by simp [toJson, Array.toJson], by
              rw [Array.toList_map]
              exact aligned_related _⟩⟩
            (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ (.cons ⟨rfl, rfl⟩ .nil)))))))))))

/-! ### The decoders accept these forms -/

private theorem agree_of_declarationWire {a : DeclarationArguments} {j : Json}
    (wire : DeclarationWire a j) :
    Agree j (Json.mkObj [("declaration", printedNameJson a.declaration),
      ("sourceDeclaration", (a.sourceDeclaration.map printedNameJson).getD .null),
      ("detail", toJson a.detail)]) :=
  wire.agree_of_members _
    [("declaration", printedNameJson a.declaration), ("detail", .str a.detail),
      ("sourceDeclaration", (a.sourceDeclaration.map printedNameJson).getD .null)]
    rfl
    (.cons ⟨rfl, fun value same => by rw [same]; exact agree_printedName _⟩
      (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
        (.cons ⟨rfl, fun value same => by
          rw [same]
          cases a.sourceDeclaration with
          | none => exact .null
          | some name => exact agree_printedName name⟩ .nil)))

private theorem agree_of_executionWire {a : ExecutionArguments} {j : Json}
    (wire : ExecutionWire a j) :
    Agree j (Json.mkObj [("root", printedNameJson a.root), ("detail", toJson a.detail)]) :=
  wire.agree_of_members _ [("detail", .str a.detail), ("root", printedNameJson a.root)] rfl
    (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
      (.cons ⟨rfl, fun value same => by rw [same]; exact agree_printedName _⟩ .nil))

private theorem agree_of_contextWire {a : ContextArguments} {j : Json} (wire : ContextWire a j) :
    Agree j (Json.mkObj [("subject", toJson a.subject), ("detail", toJson a.detail)]) :=
  wire.agree_of_members _ [("detail", .str a.detail), ("subject", .str a.subject)] rfl
    (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
      (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩ .nil))

/-- A value of the form of a payload agrees with the encoding of that payload. -/
theorem agree_of_argumentsWire {id : RuleId} {arguments : Payload id} {j : Json}
    (wire : ArgumentsWire id arguments j) : Agree j (argumentsJson id arguments) := by
  cases id <;> first
    | exact agree_of_declarationWire wire
    | exact agree_of_executionWire wire
    | exact agree_of_contextWire wire

/-- The reader of the source declaration reads `null` to no name, and the written form of a name
to that name. -/
private theorem parseSource_of {j : Json} {source : Option Name}
    (read : j.getObjVal? "sourceDeclaration" = .ok (match source with
      | none => .null
      | some name => printedNameJson name)) : parseSource j = .ok source := by
  cases source with
  | none =>
    simp only [parseSource, field, read, bind, Except.bind]
    rfl
  | some name =>
    have roundtrip := printedNameJson_roundtrip name
    simp only [parseSource, field, read, bind, Except.bind]
    cases written : printedNameJson name with
    | null =>
      unfold printedNameJson at written
      split at written <;> exact nomatch written
    | _ =>
      rw [written] at roundtrip
      simp only [roundtrip]
      rfl

/-- The reader of a payload reads a value of the form of a payload to that payload. -/
private theorem parseArguments_of_wire {id : RuleId} {arguments : Payload id} {j : Json}
    (wire : ArgumentsWire id arguments j) : parseArguments id j = .ok arguments := by
  cases id <;> first
    | (have wire : DeclarationWire arguments j := wire
       obtain ⟨declaration, readDeclaration, rfl⟩ := wire.member (.head _)
       obtain ⟨detail, readDetail, rfl⟩ := wire.member (.tail _ (.head _))
       obtain ⟨source, readSource, rfl⟩ := wire.member (.tail _ (.tail _ (.head _)))
       simp only [parseArguments, string, field, readDeclaration, readDetail, bind, Except.bind,
         Json.getStr?, printedNameJson_roundtrip, parseSource_of readSource]
       rfl)
    | (have wire : ExecutionWire arguments j := wire
       obtain ⟨detail, readDetail, rfl⟩ := wire.member (.head _)
       obtain ⟨root, readRoot, rfl⟩ := wire.member (.tail _ (.head _))
       simp only [parseArguments, string, field, readDetail, readRoot, bind, Except.bind,
         Json.getStr?, printedNameJson_roundtrip]
       rfl)
    | (have wire : ContextWire arguments j := wire
       obtain ⟨detail, readDetail, rfl⟩ := wire.member (.head _)
       obtain ⟨subject, readSubject, rfl⟩ := wire.member (.tail _ (.head _))
       simp only [parseArguments, string, field, readDetail, readSubject, bind, Except.bind,
         Json.getStr?]
       rfl)

private theorem agree_of_relatedWire {related : RelatedLocation} {j : Json}
    (wire : RelatedWire related j) : Agree j (relatedJson related) :=
  wire.agree_of_members _
    [("location", locationJson related.location), ("relation", .str related.relation)] rfl
    (.cons ⟨rfl, fun _ wire => agree_of_locationWire wire⟩
      (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩ .nil))

private theorem agreeAll_of_aligned {items : List Json} {related : List RelatedLocation}
    (aligned : Aligned (fun item related => RelatedWire related item) items related) :
    JsonAgreement.AgreeAll items (related.map relatedJson) := by
  induction aligned with
  | nil => exact .nil
  | cons head _ step => exact .cons (agree_of_relatedWire head) step

/-- A reader that reads each value of a relation to its partner reads a list of such values to
the list of the partners. -/
private theorem mapM_of_aligned {α : Type} {R : Json → α → Prop} {read : Json → Except String α}
    (reads : ∀ item value, R item value → read item = .ok value) {items : List Json}
    {values : List α} (aligned : Aligned R items values) : items.mapM read = .ok values := by
  induction aligned with
  | nil => rfl
  | cons head _ step =>
    simp only [List.mapM_cons, reads _ _ head, step, bind, Except.bind]
    rfl

/-- A value of the form of a finding agrees with the encoding of that finding. -/
theorem agree_of_findingWire {finding : Finding} {j : Json} (wire : FindingWire finding j) :
    Agree j (diagnosticJson finding) := by
  obtain ⟨id, d⟩ := finding
  exact wire.agree_of_members _
    [("arguments", argumentsJson id d.arguments), ("claim", toJson d.claim),
      ("helpUrl", .str (helpUrl id)), ("id", .str id.spelling),
      ("impact", .str (if d.impact == .violation then "violation" else "incomplete")),
      ("location", locationJson d.location), ("mode", .str d.mode.spelling),
      ("related", toJson (d.related.map relatedJson)),
      ("remedy", .str (descriptor id).remedy), ("severity", .str d.severity.spelling),
      ("text", .str d.text)]
    rfl
    (.cons ⟨rfl, fun _ wire => agree_of_argumentsWire wire⟩
      (.cons ⟨rfl, fun value same => by
          rw [same]
          cases d.claim with
          | none => exact .null
          | some claim => exact .str _⟩
        (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
          (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
            (.cons ⟨rfl, fun value same => by rw [same]; cases d.impact <;> exact .str _⟩
              (.cons ⟨rfl, fun _ wire => agree_of_locationWire wire⟩
                (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
                  (.cons ⟨rfl, fun value ⟨items, same, aligned⟩ => by
                      rw [same, toJson_relatedJson d.related]
                      exact .arr (agreeAll_of_aligned aligned)⟩
                    (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
                      (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
                        (.cons ⟨rfl, fun value same => by rw [same]; exact .str _⟩
                          .nil)))))))))))

/-- The reader of a finding reads a value of the form of a finding to that finding. -/
private theorem readDiagnostic_of_wire {finding : Finding} {j : Json}
    (wire : FindingWire finding j) : readDiagnostic j = .ok finding := by
  obtain ⟨id, ⟨payload, place, others, mode, claim, impact, severity, supported⟩⟩ := finding
  obtain ⟨arguments, readArguments, argumentsWire⟩ :=
    wire.member (List.mem_of_getElem? (i := 0) rfl)
  obtain ⟨written, readClaim, rfl⟩ := wire.member (List.mem_of_getElem? (i := 1) rfl)
  obtain ⟨rule, readRule, rfl⟩ := wire.member (List.mem_of_getElem? (i := 3) rfl)
  obtain ⟨effect, readImpact, rfl⟩ := wire.member (List.mem_of_getElem? (i := 4) rfl)
  obtain ⟨location, readPlace, locationWire⟩ := wire.member (List.mem_of_getElem? (i := 5) rfl)
  obtain ⟨evidence, readMode, rfl⟩ := wire.member (List.mem_of_getElem? (i := 6) rfl)
  obtain ⟨related, readRelated, items, rfl, aligned⟩ :=
    wire.member (List.mem_of_getElem? (i := 7) rfl)
  obtain ⟨level, readSeverity, rfl⟩ := wire.member (List.mem_of_getElem? (i := 9) rfl)
  have relatedRead := mapM_of_aligned (R := fun item related => RelatedWire related item)
    (read := fun r => do
      let relation ← string r "relation"
      let location ← parseLocation (← field r "location")
      return ({ relation, location } : RelatedLocation))
    (fun item related wire => by
      obtain ⟨place, readPlace, placeWire⟩ := Shaped.member wire (.head _)
      obtain ⟨relation, readRelation, rfl⟩ := Shaped.member wire (.tail _ (.head _))
      simp only [string, field, readPlace, readRelation, bind, Except.bind, Json.getStr?,
        parseLocation_of_wire placeWire]
      rfl) aligned
  simp only [string, field, bind, Except.bind, Json.getStr?, pure, Except.pure]
    at relatedRead
  have made : makeDiagnostic id payload place mode claim impact severity others =
      .ok { arguments := payload, location := place, related := others, mode, claim, impact,
            severity, supportedMode := supported } := by
    unfold makeDiagnostic
    split
    · rfl
    · exact absurd supported ‹_›
  have ruleRead : parseRule (.str id.spelling) = .ok id := rule_roundtrip id
  have modeRead : parseMode mode.spelling = .ok mode := mode_roundtrip mode
  simp only [readDiagnostic, string, field, readRule, readArguments, readPlace, readMode,
    readClaim, readImpact, readSeverity, readRelated, bind, Except.bind, Json.getStr?,
    Json.getArr?, ruleRead, modeRead, parseArguments_of_wire argumentsWire,
    parseLocation_of_wire locationWire, Array.mapM_eq_mapM_toList, relatedRead, pure,
    Except.pure, Functor.map, Except.map]
  cases claim <;> cases impact <;> cases severity <;>
    simp only [Severity.spelling, Array.toArray_toList, made]

/-- **The decoder of a finding accepts each value of the form of a finding**, and returns that
finding. -/
theorem parseDiagnostic_of_wire {finding : Finding} {j : Json} (wire : FindingWire finding j) :
    parseDiagnostic j = .ok finding :=
  (canonical_eq_ok_iff _ _ _ _ _).mpr ⟨readDiagnostic_of_wire wire, agree_of_findingWire wire⟩

/-- **Each finding is read back from its encoding**, with each number of related locations. -/
theorem parseDiagnostic_roundtrip (finding : Finding) :
    parseDiagnostic (diagnosticJson finding) = .ok finding :=
  parseDiagnostic_of_wire (diagnosticJson_wire finding)

/-- `parseLocation` is a complete decision of the form of a location
(`parseLocation_of_wire`): it accepts each value of that form, and it refuses `null`. The
specification says which members the object has and what each is, and it names no encoder of
this library. The kind is one-way: `parseLocation_wire` proves the other direction for an input
whose object trees are search trees, and the decoder also accepts object trees that are not
(https://github.com/rbeauchamp/regula/issues/269). -/
theorem checked_parseLocation : Regula.ExecutableContract parseLocation
    (Regula.DecidesCompletely (·.isOk = true) fun j => ∃ location, LocationWire location j) :=
  ⟨{ complete := fun _ ⟨_, wire⟩ => by
       rw [parseLocation_of_wire wire]
       rfl
     refused := ⟨.null, by decide⟩ }⟩

/-- `parseDiagnostic` is a complete decision of the form of a finding
(`parseDiagnostic_of_wire`): it accepts each value of that form, and it refuses `null`. The
specification says which members the object has and what each is, and it names no encoder of
this library. The kind is one-way: `parseDiagnostic_wire` proves the other direction for an input
whose object trees are search trees, and the decoder also accepts object trees that are not,
one of them with no member `remedy` (https://github.com/rbeauchamp/regula/issues/269). -/
theorem checked_parseDiagnostic : Regula.ExecutableContract parseDiagnostic
    (Regula.DecidesCompletely (·.isOk = true) fun j => ∃ finding, FindingWire finding j) :=
  ⟨{ complete := fun _ ⟨_, wire⟩ => by
       rw [parseDiagnostic_of_wire wire]
       rfl
     refused := ⟨.null, by decide⟩ }⟩

/-! ## An accepted value has the form, for search trees

The converse of the two decoder theorems above holds for an input whose object trees are search
trees (`JsonAgreement.Regular`), as the text parser and `Json.mkObj` build them. It does not hold
for each `Json` value: the comparison reads each member of the input and looks its name up in the
encoding, so it accepts an object tree that gives one name twice in the place of another name.
`parseLocation_iff` and `parseDiagnostic_iff` state the two directions together. -/

/-- A value that agrees with the written form of a name is that written form. -/
private theorem eq_of_agree_printedName {value : Json} {name : Name}
    (agree : Agree value (printedNameJson name)) : value = printedNameJson name := by
  have parts : ∀ (name : Name) (items : List Json),
      JsonAgreement.AgreeAll items (nameParts name) → items = nameParts name := by
    intro name
    induction name with
    | anonymous =>
      intro items all
      cases all
      rfl
    | str parent text step =>
      intro items all
      cases all with
      | cons head rest =>
        cases head with
        | arr pair =>
          cases pair with
          | cons tag more =>
            cases more with
            | cons component none =>
              cases none
              rw [tag.eq_str, component.eq_str, step _ rest]
              rfl
    | num parent number step =>
      intro items all
      cases all with
      | cons head rest =>
        cases head with
        | arr pair =>
          cases pair with
          | cons tag more =>
            cases more with
            | cons component none =>
              cases none
              rw [tag.eq_str, component.eq_num, step _ rest]
              rfl
  unfold printedNameJson at agree ⊢
  split at agree
  · rename_i same
    simp only [same, ↓reduceIte]
    exact agree.eq_str
  · rename_i differs
    simp only [differs, ↓reduceIte]
    unfold nameJson at agree ⊢
    cases agree with
    | arr all => rw [parts name _ all]

open JsonAgreement (Regular) in
/-- A value with search trees that agrees with the encoding of a byte range has the form of that
range. -/
private theorem rangeWire_of_agree {range : ByteRange} {j : Json} (regular : Regular j)
    (agree : Agree j (rangeJson range)) : RangeWire range j :=
  Shaped.of_agree [("endByte", toJson range.stop), ("startByte", toJson range.start)]
    regular agree rfl
    (.cons ⟨rfl, fun _ _ agree => agree.eq_num⟩ (.cons ⟨rfl, fun _ _ agree => agree.eq_num⟩ .nil))

open JsonAgreement (Regular) in
/-- A value with search trees that agrees with the encoding of a location has the form of that
location. -/
theorem locationWire_of_agree {location : Location} {j : Json} (regular : Regular j)
    (agree : Agree j (locationJson location)) : LocationWire location j := by
  cases location with
  | module name =>
    exact Shaped.of_agree [("kind", .str "module"), ("name", printedNameJson name)]
      regular agree rfl
      (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
        (.cons ⟨rfl, fun _ _ agree => eq_of_agree_printedName agree⟩ .nil))
  | project identity =>
    exact Shaped.of_agree [("identity", .str identity), ("kind", .str "project")]
      regular agree rfl
      (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ .nil))
  | source source =>
    exact Shaped.of_agree
      [("kind", .str "source"), ("lspRange", toJson source.fullLsp),
        ("lspSelectionRange", toJson source.selectionLsp),
        ("range", rangeJson source.val.full), ("selectionRange", rangeJson source.val.selection),
        ("sourceText", .str source.val.snapshot.source), ("uri", .str source.val.snapshot.uri)]
      regular agree rfl
      (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ (.cons ⟨rfl, fun _ _ agree => agree⟩
        (.cons ⟨rfl, fun _ _ agree => agree⟩
          (.cons ⟨rfl, fun _ regular agree => rangeWire_of_agree regular agree⟩
            (.cons ⟨rfl, fun _ regular agree => rangeWire_of_agree regular agree⟩
              (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
                (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ .nil)))))))

open JsonAgreement (Regular) in
/-- **An accepted location with search trees has the form of the location that the decoder
returns.** -/
theorem parseLocation_wire {location : Location} {j : Json} (regular : Regular j)
    (accepted : parseLocation j = .ok location) : LocationWire location j :=
  locationWire_of_agree regular (parseLocation_canonical accepted)

open JsonAgreement (Regular) in
/-- For an input with search trees, the decoder of a location returns a location exactly when
the input has the form of that location. -/
theorem parseLocation_iff {location : Location} {j : Json} (regular : Regular j) :
    parseLocation j = .ok location ↔ LocationWire location j :=
  ⟨parseLocation_wire regular, parseLocation_of_wire⟩

open JsonAgreement (Regular) in
/-- A value with search trees that agrees with the encoding of a payload has the form of that
payload. -/
theorem argumentsWire_of_agree {id : RuleId} {arguments : Payload id} {j : Json}
    (regular : Regular j) (agree : Agree j (argumentsJson id arguments)) :
    ArgumentsWire id arguments j := by
  cases id <;> first
    | exact (Shaped.of_agree
        [("declaration", printedNameJson (arguments : DeclarationArguments).declaration),
          ("detail", .str (arguments : DeclarationArguments).detail),
          ("sourceDeclaration",
            ((arguments : DeclarationArguments).sourceDeclaration.map printedNameJson).getD
              .null)]
        regular agree rfl
        (.cons ⟨rfl, fun _ _ agree => eq_of_agree_printedName agree⟩
          (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
            (.cons ⟨rfl, fun value _ agree => by
              cases source : (arguments : DeclarationArguments).sourceDeclaration with
              | none =>
                rw [source] at agree
                exact agree.eq_null
              | some name =>
                rw [source] at agree
                exact eq_of_agree_printedName agree⟩ .nil))) :
        DeclarationWire arguments j)
    | exact (Shaped.of_agree
        [("detail", .str (arguments : ExecutionArguments).detail),
          ("root", printedNameJson (arguments : ExecutionArguments).root)]
        regular agree rfl
        (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
          (.cons ⟨rfl, fun _ _ agree => eq_of_agree_printedName agree⟩ .nil)) :
        ExecutionWire arguments j)
    | exact (Shaped.of_agree
        [("detail", .str (arguments : ContextArguments).detail),
          ("subject", .str (arguments : ContextArguments).subject)]
        regular agree rfl
        (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
          (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ .nil)) :
        ContextWire arguments j)

open JsonAgreement (Regular) in
private theorem aligned_of_agreeAll :
    ∀ (related : List RelatedLocation) (items : List Json),
      (∀ item ∈ items, Regular item) → JsonAgreement.AgreeAll items (related.map relatedJson) →
        Aligned (fun item related => RelatedWire related item) items related := by
  intro related
  induction related with
  | nil =>
    intro items _ all
    cases all
    exact .nil
  | cons head rest step =>
    intro items regular all
    cases all with
    | cons first more =>
      rename_i item others
      refine .cons ?_ (step _ (fun value present => regular value (List.mem_cons_of_mem _ present))
        more)
      exact Shaped.of_agree
        [("location", locationJson head.location), ("relation", .str head.relation)]
        (regular item List.mem_cons_self) first rfl
        (.cons ⟨rfl, fun _ regular agree => locationWire_of_agree regular agree⟩
          (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ .nil))

open JsonAgreement (Regular) in
/-- A value with search trees that agrees with the encoding of a finding has the form of that
finding. -/
theorem findingWire_of_agree {finding : Finding} {j : Json} (regular : Regular j)
    (agree : Agree j (diagnosticJson finding)) : FindingWire finding j := by
  obtain ⟨id, d⟩ := finding
  exact Shaped.of_agree
    [("arguments", argumentsJson id d.arguments), ("claim", toJson d.claim),
      ("helpUrl", .str (helpUrl id)), ("id", .str id.spelling),
      ("impact", .str (if d.impact == .violation then "violation" else "incomplete")),
      ("location", locationJson d.location), ("mode", .str d.mode.spelling),
      ("related", toJson (d.related.map relatedJson)),
      ("remedy", .str (descriptor id).remedy), ("severity", .str d.severity.spelling),
      ("text", .str d.text)]
    regular agree rfl
    (.cons ⟨rfl, fun _ regular agree => argumentsWire_of_agree regular agree⟩
      (.cons ⟨rfl, fun value _ agree => by
          cases claim : d.claim with
          | none =>
            rw [claim] at agree
            exact agree.eq_null
          | some text =>
            rw [claim] at agree
            exact agree.eq_str⟩
        (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
          (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
            (.cons ⟨rfl, fun value _ agree => by
                cases impact : d.impact <;> rw [impact] at agree <;> exact agree.eq_str⟩
              (.cons ⟨rfl, fun _ regular agree => locationWire_of_agree regular agree⟩
                (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
                  (.cons ⟨rfl, fun value regular agree => by
                      rw [toJson_relatedJson d.related] at agree
                      cases agree with
                      | arr all =>
                        rename_i items
                        cases regular with
                        | arr elements =>
                          exact ⟨⟨items⟩, rfl, aligned_of_agreeAll _ _
                            (fun item present => elements item (Array.mem_def.mpr present))
                            all⟩⟩
                    (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
                      (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩
                        (.cons ⟨rfl, fun _ _ agree => agree.eq_str⟩ .nil)))))))))))

open JsonAgreement (Regular) in
/-- **An accepted finding with search trees has the form of the finding that the decoder
returns.** -/
theorem parseDiagnostic_wire {finding : Finding} {j : Json} (regular : Regular j)
    (accepted : parseDiagnostic j = .ok finding) : FindingWire finding j :=
  findingWire_of_agree regular (parseDiagnostic_canonical accepted)

open JsonAgreement (Regular) in
/-- For an input with search trees, the decoder of a finding returns a finding exactly when the
input has the form of that finding. -/
theorem parseDiagnostic_iff {finding : Finding} {j : Json} (regular : Regular j) :
    parseDiagnostic j = .ok finding ↔ FindingWire finding j :=
  ⟨parseDiagnostic_wire regular, parseDiagnostic_of_wire⟩

end Regula.DiagnosticCodec
