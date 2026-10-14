import Lean.Data.Json.FromToJson.Basic

/-! # Required members of a JSON document

The one reader through which a qualification driver takes a required member of a result document
or a manifest. Lean's `Json.getObjValAs?` decodes `Json.getObjValD`, which is `null` both for an
absent member and for a parent that is not an object, so for a required array it refuses with
`expected JSON array, got 'null'` and names neither the member nor the document (issue #458).
`get` refuses with the member's name, and says whether the member is absent, its parent is not an
object, or its value does not decode as the required type; `within` adds the document's path.

`get` admits exactly what `getObjValAs?` admits whenever the required type does not decode `null`
(`get_eq_ok_iff_getObjValAs?`), as for an array (`array_eq_ok_iff`), a string and a Boolean: only
the refusal's text differs. -/
namespace RegulaQualification.Member
open Lean

/-- The member `key` of `value`, which must be an object that has it. -/
def field (value : Json) (key : String) : Except String Json :=
  match value with
  | .obj members => match members.get? key with
    | some member => .ok member
    | none => .error s!"member '{key}' is absent"
  | _ => .error s!"member '{key}' is absent: its parent is not an object"

/-- The member `key` of `value`, decoded as `α`; a refusal names the member. -/
def get (α : Type) [FromJson α] (value : Json) (key : String) : Except String α := do
  let member ← field value key
  match (fromJson? member : Except String α) with
  | .ok decoded => .ok decoded
  | .error reason => .error s!"member '{key}': {reason}"

/-- The required array member `key` of `value`. -/
def array (value : Json) (key : String) : Except String (Array Json) := get (Array Json) value key

/-- The required string member `key` of `value`. -/
def text (value : Json) (key : String) : Except String String := get String value key

/-- The required Boolean member `key` of `value`. -/
def bool (value : Json) (key : String) : Except String Bool := get Bool value key

/-- `decoded`, a reading of the document `source`, or its refusal prefixed by `source`: with the
readers above, the refusal of a required member names the document and the member. -/
def within {α σ : Type} [ToString σ] (source : σ) (decoded : Except String α) :
    Except String α :=
  match decoded with
  | .ok value => .ok value
  | .error reason => .error s!"{source}: {reason}"

/-- `field` admits exactly the members Lean's `Json.getObjVal?` admits. -/
theorem field_eq_ok_iff (value member : Json) (key : String) :
    field value key = .ok member ↔ value.getObjVal? key = .ok member := by
  unfold field Json.getObjVal?
  split
  · split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp [throw, throwThe, MonadExceptOf.throw]

/-- `get` admits `decoded` exactly when the member is present and decodes to it. -/
theorem get_eq_ok_iff (α : Type) [FromJson α] (value : Json) (key : String) (decoded : α) :
    get α value key = .ok decoded ↔
      ∃ member, value.getObjVal? key = .ok member ∧ fromJson? member = .ok decoded := by
  unfold get
  cases hfield : field value key with
  | error reason =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro member hmember
    rw [← field_eq_ok_iff] at hmember
    rw [hfield] at hmember
    cases hmember
  | ok member =>
    have hmember := (field_eq_ok_iff value member key).mp hfield
    simp only [bind, Except.bind]
    constructor
    · intro h
      refine ⟨member, hmember, ?_⟩
      split at h
      · rename_i found heq
        cases h
        exact heq
      · cases h
    · rintro ⟨other, hother, hdecoded⟩
      rw [hmember] at hother
      cases hother
      rw [hdecoded]

/-- For a type that does not decode `null`, `get` admits exactly what `Json.getObjValAs?` admits:
the two differ only in the text of a refusal. -/
theorem get_eq_ok_iff_getObjValAs? (α : Type) [FromJson α]
    (refusesNull : ∀ decoded : α, (fromJson? Json.null : Except String α) ≠ .ok decoded)
    (value : Json) (key : String) (decoded : α) :
    get α value key = .ok decoded ↔ value.getObjValAs? α key = .ok decoded := by
  rw [get_eq_ok_iff]
  unfold Json.getObjValAs? Json.getObjValD
  cases hmember : value.getObjVal? key with
  | error reason =>
    simp only [Except.toOption, Option.getD_none, reduceCtorEq, false_and, exists_false,
      false_iff]
    exact refusesNull decoded
  | ok member => simp [Except.toOption]

/-- `array` admits exactly what `Json.getObjValAs? (Array Json)` admits. -/
theorem array_eq_ok_iff (value : Json) (key : String) (items : Array Json) :
    array value key = .ok items ↔ value.getObjValAs? (Array Json) key = .ok items :=
  get_eq_ok_iff_getObjValAs? (Array Json) (fun _ h => by cases h) value key items

/-- `text` admits exactly what `Json.getObjValAs? String` admits. -/
theorem text_eq_ok_iff (value : Json) (key : String) (decoded : String) :
    text value key = .ok decoded ↔ value.getObjValAs? String key = .ok decoded :=
  get_eq_ok_iff_getObjValAs? String (fun _ h => by cases h) value key decoded

/-- `bool` admits exactly what `Json.getObjValAs? Bool` admits. -/
theorem bool_eq_ok_iff (value : Json) (key : String) (decoded : Bool) :
    bool value key = .ok decoded ↔ value.getObjValAs? Bool key = .ok decoded :=
  get_eq_ok_iff_getObjValAs? Bool (fun _ h => by cases h) value key decoded

/-- Each refusal of `get` names the member. -/
theorem get_refusal_names (α : Type) [FromJson α] (value : Json) (key reason : String)
    (h : get α value key = .error reason) :
    ∃ detail, reason = "member '" ++ (key ++ detail) := by
  unfold get field at h
  split at h
  · rename_i members
    split at h
    · simp only [bind, Except.bind] at h
      split at h
      · cases h
      · cases h
        exact ⟨_, by simp only [String.append_assoc]; rfl⟩
    · cases h
      exact ⟨_, by simp only [String.append_assoc]; rfl⟩
  · cases h
    exact ⟨_, by simp only [String.append_assoc]; rfl⟩

end RegulaQualification.Member
