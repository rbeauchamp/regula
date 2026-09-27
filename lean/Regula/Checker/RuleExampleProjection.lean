import Regula.Checker.RuleExampleQualification
import Std.Data.TreeMap.Raw.Lemmas
import Regula.Checker.JsonProjectionTree

/-! # Rule-example qualification view

Qualification-only view of one rule-example record and its congruence laws.
`resultView` blanks exactly the `acceptance` and `documentationAcceptance` payloads of a result;
`qualify_result_congr` and its lemmas prove that `RuleExampleQualification.qualify` decides a
record and its view identically, because the qualifier reads no other changed field. The laws
concern these JSON values, not the producer that wrote them. -/

namespace Regula.Checker.RuleExampleProjection
open Lean RuleExampleQualification

/-- The qualification-only view changes no tree key, shape, or required nested value. -/
def payload (key : String) (value : Json) : Json :=
  if key == "acceptance" || key == "documentationAcceptance" then .null else value

/-- A result object with its `acceptance` and `documentationAcceptance` values replaced by
`null` and every other field unchanged; any other JSON value is returned unchanged. -/
def resultView : Json → Json
  | .obj fields => .obj (fields.map payload)
  | value => value

/-- Canonical construction used by the producer adapter; result is inserted last. -/
def record (fields : List (String × Json)) (result : Json) : Json :=
  (Json.mkObj fields).setObjVal! "result" result

/-- Equality of every top-level lookup consumed by the unchanged qualifier. -/
def ResultRel (a b : Json) : Prop :=
  ∀ key, key ≠ "acceptance" → key ≠ "documentationAcceptance" → field a key = field b key

/-- The record may carry arbitrary metadata; only the result value changes. -/
def RecordRel (a b : Json) : Prop :=
  ∀ key, key ≠ "result" → field a key = field b key

theorem binding_congr (a b ra rb : Json) (mode : Regula.EvidenceMode)
    (ha : field a "result" = .ok ra) (hb : field b "result" = .ok rb)
    (hr : RecordRel a b) (hresult : ResultRel ra rb) : binding a mode = binding b mode := by
  simp only [binding, string, ha, hb, hr "before" (by decide), hr "after" (by decide),
    hr "checkerSources" (by decide), hr "request" (by decide)]
  simp only [Except.bind, bind, Bind.bind, hresult "toolchain" (by decide) (by decide),
    hresult "sourceRevision" (by decide) (by decide)]

theorem observedSources_congr (a b : Json) (bound : Regula.Website.ExampleBinding)
    (h : ResultRel a b) : observedSources a bound = observedSources b bound := by
  simp only [observedSources, h "scope" (by decide) (by decide),
    h "sourceAccount" (by decide) (by decide)]

theorem sourceAccount_congr (a b : Json) (bound : Regula.Website.ExampleBinding)
    (displayed : String)
    (h : ResultRel a b) : sourceAccount a bound displayed = sourceAccount b bound displayed := by
  simp only [sourceAccount, observedSources_congr a b bound h]

theorem effectiveAccount_congr (a b : Json) (admitted : Regula.Website.ExampleRequest)
    (h : ResultRel a b) : effectiveAccount a admitted = effectiveAccount b admitted := by
  simp only [effectiveAccount, h "effective" (by decide) (by decide), h "scope" (by decide)
      (by decide)]

theorem requestAccount_congr (a b : Json) (bound : Regula.Website.ExampleBinding)
    (h : ResultRel a b) : requestAccount a bound = requestAccount b bound := by
  simp only [requestAccount, h "request" (by decide) (by decide), effectiveAccount_congr a b _ h]

theorem identity_congr (ra rb : Json) (h : ResultRel ra rb) :
    ResultProtocol.identityFields.forM (checkIdentity ra) =
      ResultProtocol.identityFields.forM (checkIdentity rb) := by
  simp only [ResultProtocol.identityFields, RegistryCodec.identityFields, List.forM, checkIdentity,
    h "schemaVersion" (by decide) (by decide), h "producerVersion" (by decide) (by decide),
    h "toolchain" (by decide) (by decide), h "sourceRevision" (by decide) (by decide)]

theorem qualify_congr (a b ra rb : Json)
    (ha : field a "result" = .ok ra) (hb : field b "result" = .ok rb)
    (hr : RecordRel a b) (hresult : ResultRel ra rb) : qualify a = qualify b := by
  unfold qualify
  rw [ha, hb]
  simp only [Except.bind, bind, Bind.bind]
  rw [identity_congr ra rb hresult]
  simp only [checkFindings, expectFindings, qualifyKind, Except.bind, bind, Bind.bind]
  simp only [string, hresult "mode" (by decide) (by decide),
    hresult "diagnostics" (by decide) (by decide), hresult "unresolved" (by decide) (by decide),
    hresult "status" (by decide) (by decide), hresult "scope" (by decide) (by decide),
    hr "mode" (by decide), hr "exitCode" (by decide), hr "expected" (by decide),
    hr "unresolvedPatterns" (by decide), hr "kind" (by decide), hr "source" (by decide),
    hr "rule" (by decide), binding_congr a b ra rb _ ha hb hr hresult,
    requestAccount_congr ra rb _ hresult, sourceAccount_congr ra rb _ _ hresult]


/-- The JSON value is an object whose underlying tree map is well-formed. -/
def ObjectWF : Json → Prop
  | .obj t => t.WF
  | _ => False

theorem record_wf (fields : List (String × Json)) (result : Json) : ObjectWF
    (record fields result) :=
  Std.TreeMap.Raw.WF.insert Std.TreeMap.Raw.WF.ofList

theorem field_set (j : Json) (h : ObjectWF j) (key : String) (value : Json) (query : String) :
    field (j.setObjVal! key value) query = if key = query then .ok value else field j query := by
  cases j <;> try contradiction
  rename_i t
  simp only [field, Json.setObjVal!, Json.getObjVal?]
  change
      (match (t.insert key value)[query]? with | some v => Except.ok v | none =>
                                                                          Except.error s!"property \
                                                                            not found: {query}") = _
  rw [Std.TreeMap.Raw.getElem?_insert h]
  by_cases heq : key = query
  · subst query; simp
  · simp [heq]; rfl

theorem wf_set (j : Json) (h : ObjectWF j) (key : String) (value : Json) :
    ObjectWF (j.setObjVal! key value) := by
  cases j <;> try contradiction
  exact Std.TreeMap.Raw.WF.insert h

theorem field_record (fields : List (String × Json)) (result : Json) :
    field (record fields result) "result" = .ok result := by
  exact (field_set (Json.mkObj fields) Std.TreeMap.Raw.WF.ofList "result" result "result").trans
      (ite_eq_left rfl)

theorem record_rel (fields : List (String × Json)) (a b : Json) : RecordRel (record fields a)
    (record fields b) := by
  intro key hkey
  simp only [record, field_set (Json.mkObj fields) Std.TreeMap.Raw.WF.ofList]
  simp [Ne.symm hkey]

theorem recordRel_set (a b : Json) (ha : ObjectWF a) (hb : ObjectWF b) (h : RecordRel a b)
    (key : String) (value : Json) : RecordRel (a.setObjVal! key value)
    (b.setObjVal! key value) := by
  intro query hquery
  simp only [field_set a ha, field_set b hb, h query hquery]


theorem qualify_set_congr (a b ra rb : Json)
    (hwa : ObjectWF a) (hwb : ObjectWF b)
    (ha : field a "result" = .ok ra) (hb : field b "result" = .ok rb)
    (hr : RecordRel a b) (hresult : ResultRel ra rb)
    (key : String) (value : Json) (hk : key ≠ "result") :
    qualify (a.setObjVal! key value) = qualify (b.setObjVal! key value) := by
  apply qualify_congr _ _ ra rb
  · simpa only [field_set a hwa, ite_eq_right hk] using ha
  · simpa only [field_set b hwb, ite_eq_right hk] using hb
  · exact recordRel_set a b hwa hwb hr key value
  · exact hresult

theorem qualify_result_congr (a b ra rb : Json)
    (hwa : ObjectWF a) (hwb : ObjectWF b)
    (hr : RecordRel a b) (hresult : ResultRel ra rb) :
    qualify (a.setObjVal! "result" ra) = qualify (b.setObjVal! "result" rb) := by
  apply qualify_congr _ _ ra rb
  · simp [field_set a hwa]
  · simp [field_set b hwb]
  · intro key hkey
    simp only [field_set a hwa, field_set b hwb, ite_eq_right (Ne.symm hkey), hr key hkey]
  · exact hresult

theorem resultView_rel (result : Json) : ResultRel (resultView result) result := by
  intro key hka hkd
  cases result <;> try rfl
  rename_i tree
  simp only [resultView, field, Json.getObjVal?, JsonProjectionTree.get_map]
  have hp : ∀ value, payload key value = value := by
    intro value
    simp [payload, hka, hkd]
  cases tree.get? key <;> simp [hp]

theorem resultView_set (result : Json) (key : String) (value : Json)
    (hka : key ≠ "acceptance") (hkd : key ≠ "documentationAcceptance") :
    resultView (result.setObjVal! key value) = (resultView result).setObjVal! key value := by
  cases result <;> try rfl
  rename_i tree
  simp only [resultView, Json.setObjVal!, JsonProjectionTree.map_insert]
  simp [payload, hka, hkd]


/-- Full decision equality at the actual adapter constructor, with no assumptions on
producer JSON (including its raw object map). -/
theorem qualify_record (fields : List (String × Json)) (result : Json) :
    qualify (record fields (resultView result)) = qualify (record fields result) :=
  qualify_congr _ _ _ _ (field_record _ _) (field_record _ _) (record_rel _ _ _) (resultView_rel _)

/-- Single-record admission injects the identical checked source snapshot. -/
theorem qualify_record_checkerSources (fields : List (String × Json))
    (result checker : Json) :
    qualify ((record fields (resultView result)).setObjVal! "checkerSources" checker) =
      qualify ((record fields result).setObjVal! "checkerSources" checker) :=
  qualify_set_congr _ _ _ _ (record_wf _ _) (record_wf _ _)
    (field_record _ _) (field_record _ _) (record_rel _ _ _) (resultView_rel _)
    "checkerSources" checker (by decide)


theorem map_insertMany (f : String → Json → Json) (tree : Std.TreeMap.Raw String Json compare)
    (fields : List (String × Json)) :
    (tree.insertMany fields).map f = (tree.map f).insertMany
    (fields.map fun p => (p.1, f p.1 p.2)) := by
  induction fields generalizing tree with
  | nil => rfl
  | cons head tail ih =>
    rw [Std.TreeMap.Raw.insertMany_cons, List.map_cons, Std.TreeMap.Raw.insertMany_cons]
    rw [ih, JsonProjectionTree.map_insert]

theorem resultView_mkObj (fields : List (String × Json)) :
    resultView (Json.mkObj fields) = Json.mkObj (fields.map fun p => (p.1, payload p.1 p.2)) := by
  simp only [resultView, Json.mkObj, Std.TreeMap.Raw.ofList_eq_insertMany_empty]
  rw [map_insertMany]
  rfl

end Regula.Checker.RuleExampleProjection
