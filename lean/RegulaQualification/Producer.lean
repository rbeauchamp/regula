import RegulaQualification.Json
import Regula.StructuralName
import Regula.Decision
import RegulaCore.JsonAgreement

/-! # Producer observation requirements

Exact producer-observation requirements for RG5001/RG5002 and standalone roots.
Every mandatory JSON access may refuse. The required census, source, documentation,
foundation fields, diagnostics, and ranges are compared, not inferred from a PASS label.
The proofs concern these supplied observations, not Lean/OS authenticity. -/
namespace RegulaQualification.Producer
open Lean
open Regula.JsonAgreement (Conforms)

private def field (j : Json) (key : String) := j.getObjVal? key
private def array (j : Json) (key : String) := j.getObjValAs? (Array Json) key
private def text (j : Json) (key : String) := j.getObjValAs? String key
/-- A dotted Lean name as result documents write it (`Regula.RegistryCodec.printedNameJson`). -/
private def nameJson (name : String) : Json := Regula.RegistryCodec.printedNameJson name.toName
private def first (values : Array Json) : Except String Json :=
  match values[0]? with | some value => .ok value | none => .error "missing required first element"

/-- Mandatory surface report selected by the public project protocol. -/
def account (report : Json) : Except String Json := do
  field (← first (← array (← field report "scope") "surfaces")) "report"

/-- The report of the first surface's first claimed executable, which the public project
protocol lists in that surface's `executables`: each executable root is inspected in an
environment of its own. -/
def executableAccount (report : Json) : Except String Json := do
  let surface ← first (← array (← field report "scope") "surfaces")
  field (← first (← array surface "executables")) "report"

/-- Exact byte offset of the prefix before the first occurrence. Callers separately
require the expected source fragments; this helper alone does not promise a match. -/
private def beforeBytes (source marker : String) : Nat :=
  (source.splitOn marker).head!.utf8ByteSize

/-- The key of the fixture's theorem `reflexive` in module `Example`, as a census lists it. -/
def declarationKey : Json := toJson #[nameJson "Example", nameJson "reflexive"]

/-- The census of an audit of the producer fixture: the module `Example` and its theorem, and no
dependency module, execution root or history request. -/
def censusJson : Json := Json.mkObj [
  ("modules", toJson #[nameJson "Example"]),
  ("dependencyModules", toJson (#[] : Array Json)), ("declarations", toJson #[declarationKey]),
  ("executionRoots", toJson (#[] : Array Json)),
  ("historyRequests", toJson (#[] : Array Json))]

/-- Build all preserved source-producer requirements. `theoremType` is the first
observed type shared across invocations; equality is checked, never parsed from prose. It is the
declaration's `type`, the `repr` of its kernel type expression, which a result carries only when
the audit was asked for it (`axiomGate --kernel-types`): a report without it is refused. -/
def requirements (report : Json) (code : Nat) (rule mode source : String)
    (fixed : Bool) (theoremType : Json) : Except String (List Check) := do
  let account ← account report
  let diagnostics ← array report "diagnostics"
  let ids ← diagnostics.toList.mapM (fun d => text d "id")
  let receipt ← field account "admission"
  let key := declarationKey
  let required ← array receipt "required"
  let snapshots ← array (← field report "scope") "sources"
  let snapshot ← first snapshots
  let docs ← field account "documentation"
  let declarations ← array account "declarations"
  let declaration ← first declarations
  let material := if rule == "RG5002" then #[key] else #[]
  -- The RG5001 header observation: RG5002's fixtures import `Regula.MaterialClaim`; a
  -- documented fixture's docstring is its first command.
  let documented := rule == "RG5002" || fixed
  let imports := if rule == "RG5002" then toJson #[Json.mkObj [
      ("module", nameJson "Regula.MaterialClaim"), ("importAll", .bool false),
      ("isExported", .bool true), ("isMeta", .bool false)]]
    else toJson (#[] : Array Json)
  let header := Json.mkObj [("documented", .bool documented),
    ("documentationFirst", .bool documented), ("imports", imports)]
  let doc := if fixed then Json.str
                            ("Every natural number equals itself, without additional \
                              hypotheses.\n\n" ++
    "# Intent\nEquality on natural numbers must be reflexive for every value, with no side \
      condition.") else .null
  let mut checks : List Check := [
    ⟨"exact diagnostic list", ids == (if fixed then [] else [rule])⟩,
    ⟨"exact exit", code == (if fixed then 0 else 1)⟩,
    ⟨"exact status", (← text report "status") == (if fixed then "completed" else "rejected")⟩,
    ⟨"admission receipt complete", (← field receipt "required") == (← field receipt "admitted")⟩,
    ⟨"exact mode", (← text report "mode") == mode⟩,
    ⟨"no unresolved evidence", (← array report "unresolved").isEmpty⟩,
    ⟨"exact census", decide (Conforms (← field account "census") censusJson)⟩,
    ⟨"reflexivity admitted", required.contains key⟩,
    ⟨"one source snapshot", snapshots.size == 1⟩,
    ⟨"snapshot module", (← field snapshot "module") == nameJson "Example"⟩,
    ⟨"exact source bytes", (← text snapshot "sourceText") == source⟩,
    ⟨"snapshot filename", (System.FilePath.mk (← text snapshot "path")).fileName ==
        some "Example.lean"⟩,
    ⟨"module documentation",
      decide (Conforms (← field docs "modules")
        (toJson #[toJson #[nameJson "Example", header]]))⟩,
    ⟨"material selection", decide (Conforms (← field docs "materialDeclarations")
        (toJson material))⟩,
    ⟨"declaration documentation", decide (Conforms (← field docs "declarations")
        (toJson (if material.isEmpty then #[] else #[toJson #[key, doc]])))⟩,
    ⟨"one declaration", declarations.size == 1⟩,
    ⟨"no axioms", (← array declaration "axioms").isEmpty⟩,
    ⟨"safe declaration", !(← declaration.getObjValAs? Bool "isUnsafe")⟩,
    ⟨"total declaration", !(← declaration.getObjValAs? Bool "isPartial")⟩,
    ⟨"unchanged elaborated theorem", decide (Conforms (← field declaration "type")
        theoremType)⟩]
  if !fixed then
    let finding ← first diagnostics
    let location ← field finding "location"
    checks := checks ++ [
      ⟨"violation impact", (← text finding "impact") == "violation"⟩,
      ⟨"location kind", (← text location "kind") ==
          (if rule == "RG5001" then "module" else "source")⟩,
      ⟨"no related findings", (← array finding "related").isEmpty⟩,
      ⟨"finding mode", (← text finding "mode") == mode⟩,
      ⟨"kernel-only finding", (← text finding "claim") == "kernel-only"⟩,
      ⟨"error severity", (← text finding "severity") == "error"⟩]
    if rule == "RG5001" then
      checks := checks ++ [
        ⟨"exact module location", decide (Conforms location (Json.mkObj
            [("kind", .str "module"), ("name", nameJson "Example")]))⟩,
        ⟨"module arguments", decide (Conforms (← field finding "arguments")
            (Json.mkObj [("subject", .str "Example"),
          ("detail",
              .str "module-documentation: add a module doc comment describing this module")]))⟩]
    else
      let start := beforeBytes source "theorem" + "theorem".utf8ByteSize +
        beforeBytes ((source.splitOn "theorem").drop 1 |>.head!) "reflexive"
      checks := checks ++ [
        ⟨"source contains expected selection", source.contains "theorem reflexive" &&
            source.contains "@["⟩,
        ⟨"material arguments", decide (Conforms (← field finding "arguments")
            (Json.mkObj [("declaration", nameJson "reflexive"), ("sourceDeclaration", .null),
          ("detail", .str "material-documentation: document the claim, assumptions and evidence at \
            this declaration")]))⟩,
        ⟨"location binds source", (← text location "sourceText") == source⟩,
        ⟨"location filename", (System.FilePath.mk (← text location "uri")).fileName ==
            some "Example.lean"⟩,
        ⟨"selection byte range", decide (Conforms (← field location "selectionRange")
            (Json.mkObj [("startByte", toJson start), ("endByte", toJson (start + 9))]))⟩,
        ⟨"declaration byte range", decide (Conforms (← field location "range")
            (Json.mkObj [("startByte", toJson (beforeBytes source "@[")),
          ("endByte", toJson (source.utf8ByteSize - 1))]))⟩]
  return checks

/-- Actual executable oracle, with fail-closed mandatory decoding. -/
@[regula_decision]
def validate (report : Json) (code : Nat) (rule mode source : String)
    (fixed : Bool) (theoremType : Json) : Except String Unit :=
  checked_decoded.run (requirements report code rule mode source fixed theoremType)

/-- Admission succeeds exactly when decoding succeeds and every source-producer
requirement holds. This statement includes both success and refusal. -/
theorem checked_validation : Regula.ExecutableContract validate
    (fun run => ∀ report code rule mode source fixed theoremType,
      run report code rule mode source fixed theoremType = .ok () ↔
        ∃ checks, requirements report code rule mode source fixed theoremType = .ok checks ∧
            Satisfied checks) :=
  ⟨fun _ _ _ _ _ _ _ => validateDecoded_exact _⟩

/-- `validate` is a complete decision of its requirements: it accepts every report whose
requirements decode and all hold, and it refuses a `null` report. Soundness also holds
(`checked_validation` registers the equivalence), but the kind is one-way because a sound kind
requires a report the function accepts, and a conforming producer report is a result document
that only an audit produces; accepted reports are observed by the `producers` diagnostic. -/
theorem checked_validation_complete : Regula.ExecutableContract validate (fun run =>
    Regula.DecidesCompletely (· = .ok ())
      (fun input : (((((Json × Nat) × String) × String) × String) × Bool) × Json =>
        ∃ checks, requirements input.1.1.1.1.1.1 input.1.1.1.1.1.2 input.1.1.1.1.2
          input.1.1.1.2 input.1.1.2 input.1.2 input.2 = .ok checks ∧ Satisfied checks)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
        (Function.uncurry (Function.uncurry run))))))) :=
  ⟨{ complete := fun input holds =>
       (checked_validation.evidence input.1.1.1.1.1.1 input.1.1.1.1.1.2 input.1.1.1.1.2
         input.1.1.1.2 input.1.1.2 input.1.2 input.2).mpr holds
     refused := ⟨((((((.null, 0), ""), ""), ""), false), .null),
       fun accepted => absurd (congrArg Except.isOk accepted) (by decide +kernel)⟩ }⟩

/-- `validate` accepts exactly the reports whose requirements decode and all hold, as a law
(`Regula.DecisionEquivalence`) on the product of its seven arguments, from `checked_validation`.
The complete kind `checked_validation_complete` is kept: it adds the report the function refuses,
which the law does not supply. -/
theorem checked_validation_law : Regula.ExecutableContract validate (fun run =>
    Regula.DecisionEquivalence (· = .ok ())
      (fun input : (((((Json × Nat) × String) × String) × String) × Bool) × Json =>
        ∃ checks, requirements input.1.1.1.1.1.1 input.1.1.1.1.1.2 input.1.1.1.1.2
          input.1.1.1.2 input.1.1.2 input.1.2 input.2 = .ok checks ∧ Satisfied checks)
      (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
        (Function.uncurry (Function.uncurry run))))))) :=
  ⟨⟨fun input => checked_validation.evidence input.1.1.1.1.1.1 input.1.1.1.1.1.2 input.1.1.1.1.2
    input.1.1.1.2 input.1.1.2 input.1.2 input.2⟩⟩

/-- An admitted requirement list holds the census check and the theorem-type check. Each decides
`Conforms` with `conforms`, with the received value first: the census of the report's account
against `censusJson`, and the `type` of its first declaration against `theoremType`. -/
theorem requirements_census_type {report : Json} {code : Nat} {rule mode source : String}
    {fixed : Bool} {theoremType : Json} {checks : List Check}
    (h : requirements report code rule mode source fixed theoremType = .ok checks) :
    ∃ acc census declarations declaration type, account report = .ok acc ∧
      acc.getObjVal? "census" = .ok census ∧
      acc.getObjValAs? (Array Json) "declarations" = .ok declarations ∧
      declarations[0]? = some declaration ∧ declaration.getObjVal? "type" = .ok type ∧
      ⟨"exact census", decide (Conforms census censusJson)⟩ ∈ checks ∧
      ⟨"unchanged elaborated theorem", decide (Conforms type theoremType)⟩ ∈ checks := by
  unfold requirements at h
  simp only [RegulaPolicy.Guards.bind_eq_ok] at h
  obtain ⟨acc, hacc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, declarations, hdecls,
    declaration, hdecl, _, _, _, _, _, _, _, _, _, _, census, hcensus, rest⟩ := h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, type, htype, rest⟩ := rest
  have firstDeclaration : declarations[0]? = some declaration := by
    unfold first at hdecl
    split at hdecl
    · rename_i value found
      cases hdecl
      exact found
    · cases hdecl
  refine ⟨acc, census, declarations, declaration, type, hacc, hcensus, hdecls, firstDeclaration,
    htype, ?_⟩
  split at rest
  · simp only [RegulaPolicy.Guards.bind_eq_ok] at rest
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rest⟩ := rest
    split at rest
    · simp only [RegulaPolicy.Guards.bind_eq_ok, RegulaPolicy.Guards.pure_eq_ok] at rest
      obtain ⟨_, _, rfl⟩ := rest
      exact ⟨by simp only [List.mem_append, List.mem_cons, true_or, or_true],
        by simp only [List.mem_append, List.mem_cons, true_or, or_true]⟩
    · simp only [RegulaPolicy.Guards.bind_eq_ok, RegulaPolicy.Guards.pure_eq_ok] at rest
      obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := rest
      exact ⟨by simp only [List.mem_append, List.mem_cons, true_or, or_true],
        by simp only [List.mem_append, List.mem_cons, true_or, or_true]⟩
  · simp only [RegulaPolicy.Guards.pure_eq_ok] at rest
    subst rest
    exact ⟨by simp only [List.mem_cons, true_or, or_true],
      by simp only [List.mem_cons, true_or, or_true]⟩

/-- An admitted producer report's census has search trees at each depth and agrees with
`censusJson`. The `type` of its first declaration has search trees and agrees with
`theoremType`. The converse is not claimed here: `validate` also requires the other checks
(`checked_validation`). -/
theorem validate_census_type {report : Json} {code : Nat} {rule mode source : String}
    {fixed : Bool} {theoremType : Json}
    (h : validate report code rule mode source fixed theoremType = .ok ()) :
    ∃ acc census declarations declaration type, account report = .ok acc ∧
      acc.getObjVal? "census" = .ok census ∧
      acc.getObjValAs? (Array Json) "declarations" = .ok declarations ∧
      declarations[0]? = some declaration ∧ declaration.getObjVal? "type" = .ok type ∧
      Regula.JsonAgreement.Regular census ∧ Regula.JsonAgreement.Agree census censusJson ∧
      Regula.JsonAgreement.Regular type ∧ Regula.JsonAgreement.Agree type theoremType := by
  obtain ⟨checks, hreq, hsat⟩ := (validateDecoded_exact _).mp h
  obtain ⟨acc, census, declarations, declaration, type, hacc, hcensus, hdecls, hfirst, htype,
    censusMember, typeMember⟩ := requirements_census_type hreq
  obtain ⟨censusRegular, censusAgree⟩ :=
    of_decide_eq_true (hsat _ censusMember)
  obtain ⟨typeRegular, typeAgree⟩ :=
    of_decide_eq_true (hsat _ typeMember)
  exact ⟨acc, census, declarations, declaration, type, hacc, hcensus, hdecls, hfirst, htype,
    censusRegular, censusAgree, typeRegular, typeAgree⟩

/-- Standalone executable observations, from the executable's own environment report: exact
intended rejection, module documentation and `main` in the execution-root census. -/
def standaloneRequirements (report : Json) (code : Nat) (mutated : Bool) : Except String
    (List Check) := do
  let account ← executableAccount report
  let ids ← (← array report "diagnostics").toList.mapM (fun d => text d "id")
  return [
    ⟨"standalone exit", code == (if mutated then 1 else 0)⟩,
    ⟨"standalone diagnostics", ids == (if mutated then ["RG1001"] else [])⟩,
    ⟨"standalone status", (← text report "status") ==
        (if mutated then "rejected" else "completed")⟩,
    ⟨"standalone documentation", (← array (← field account "documentation") "modules").contains
      (toJson #[nameJson "SelftestMain", Json.mkObj [("documented", .bool true),
        ("documentationFirst", .bool true), ("imports", toJson (#[] : Array Json))]])⟩,
    ⟨"standalone main root", (← array (← field account "census") "executionRoots").contains
      (toJson #[nameJson "SelftestMain", nameJson "main"])⟩]

end RegulaQualification.Producer
