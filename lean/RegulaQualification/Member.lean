import Lean.Data.Json.FromToJson.Basic

/-! # Required members of a JSON document

The one reader through which a qualification driver takes a required member of a result document
or a manifest. Lean's `Json.getObjValAs?` decodes `Json.getObjValD`, which is `null` both for an
absent member and for a parent that is not an object, so for a required array it refuses with
`expected JSON array, got 'null'` and names neither the member nor the document (issue #458).

Each reader here finds the member and decodes it at its required shape in one step, so a refusal
names the member, and says whether the member is absent, its parent is not an object, or its
value does not decode: `object` for a parent of further members, `array`, `text`, `bool` and `get`
at a `FromJson` type, and `decoded` with a caller's decoder, such as one that also requires unique
nonempty strings. `value` hands out a member whole, for a caller that compares it by agreement or
keeps it as an expected value; a member of a known shape goes through the reader of that shape,
not through `value` and a later decoder. `within` adds the document's path.

`get` admits exactly what `getObjValAs?` admits whenever the required type does not decode `null`
(`get_eq_ok_iff_getObjValAs?`), as for an array (`array_eq_ok_iff`), a string and a Boolean: only
the refusal's text differs. -/
namespace RegulaQualification.Member
open Lean

/-- The required member `key` of `parent`, whole, for a caller that compares it by agreement or
keeps it as an expected value; `parent` must be an object that has it. A member of a known shape is
read with `object`, `array`, `text`, `bool`, `get` or `decoded` instead, which decode it in the same
step, so that its refusal names it. -/
def value (parent : Json) (key : String) : Except String Json :=
  match parent with
  | .obj members => match members.get? key with
    | some member => .ok member
    | none => .error s!"member '{key}' is absent"
  | _ => .error s!"member '{key}' is absent: its parent is not an object"

/-- The required member `key` of `value`, decoded by `decode`; a refusal names the member. -/
def decoded {α : Type} (decode : Json → Except String α) (value : Json) (key : String) :
    Except String α := do
  let member ← Member.value value key
  match decode member with
  | .ok result => .ok result
  | .error reason => .error s!"member '{key}': {reason}"

/-- The required object member `key` of `value`, the parent of further required members. -/
def object (value : Json) (key : String) : Except String Json :=
  decoded (fun member => match member with
    | .obj _ => .ok member
    | _ => .error "expected a JSON object") value key

/-- The member `key` of `value`, decoded as `α`; a refusal names the member. -/
def get (α : Type) [FromJson α] (value : Json) (key : String) : Except String α :=
  decoded fromJson? value key

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

/-- `value` admits exactly the members Lean's `Json.getObjVal?` admits. -/
theorem value_eq_ok_iff (value member : Json) (key : String) :
    Member.value value key = .ok member ↔ value.getObjVal? key = .ok member := by
  -- Each side is reduced by definition, not rewritten with the equations of `Json.getObjVal?`,
  -- which would declare them here a second time beside another module (`qualify combined`'s
  -- `unique-constants`).
  cases value with
  | obj members =>
    show (match members.get? key with
        | some found => Except.ok found
        | none => Except.error s!"member '{key}' is absent") = Except.ok member ↔
      (match members.get? key with
        | some found => Except.ok found
        | none => Except.error s!"property not found: {key}") = Except.ok member
    cases members.get? key with
    | some found => exact Iff.rfl
    | none => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | _ => exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- `decoded` admits `result` exactly when the member is present and `decode` gives it. -/
theorem decoded_eq_ok_iff {α : Type} (decode : Json → Except String α) (value : Json)
    (key : String) (result : α) :
    decoded decode value key = .ok result ↔
      ∃ member, value.getObjVal? key = .ok member ∧ decode member = .ok result := by
  unfold decoded
  cases hfield : Member.value value key with
  | error reason =>
    simp only [bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro member hmember
    rw [← value_eq_ok_iff] at hmember
    rw [hfield] at hmember
    cases hmember
  | ok member =>
    have hmember := (value_eq_ok_iff value member key).mp hfield
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

/-- `object` admits exactly a present member that is an object. -/
theorem object_eq_ok_iff (value member : Json) (key : String) :
    object value key = .ok member ↔
      value.getObjVal? key = .ok member ∧ ∃ members, member = .obj members := by
  unfold object
  rw [decoded_eq_ok_iff]
  constructor
  · rintro ⟨found, hfound, hdecode⟩
    split at hdecode
    · rename_i members
      cases hdecode
      exact ⟨hfound, members, rfl⟩
    · cases hdecode
  · rintro ⟨hfound, members, rfl⟩
    exact ⟨_, hfound, rfl⟩

/-- `get` admits `result` exactly when the member is present and decodes to it. -/
theorem get_eq_ok_iff (α : Type) [FromJson α] (value : Json) (key : String) (result : α) :
    get α value key = .ok result ↔
      ∃ member, value.getObjVal? key = .ok member ∧ fromJson? member = .ok result :=
  decoded_eq_ok_iff fromJson? value key result

/-- For a type that does not decode `null`, `get` admits exactly what `Json.getObjValAs?` admits:
the two differ only in the text of a refusal. -/
theorem get_eq_ok_iff_getObjValAs? (α : Type) [FromJson α]
    (refusesNull : ∀ result : α, (fromJson? Json.null : Except String α) ≠ .ok result)
    (value : Json) (key : String) (result : α) :
    get α value key = .ok result ↔ value.getObjValAs? α key = .ok result := by
  rw [get_eq_ok_iff]
  -- `Json.getObjValAs?` is `fromJson?` of `(value.getObjVal? key).toOption.getD null`, reduced by
  -- definition below, so that no equation of `Except.toOption` is declared here (see
  -- `value_eq_ok_iff`).
  show _ ↔ (fromJson? ((value.getObjVal? key).toOption.getD Json.null) : Except String α) = _
  cases value.getObjVal? key with
  | error reason =>
    exact ⟨(fun ⟨_, found, _⟩ => nomatch found), (fun h => absurd h (refusesNull result))⟩
  | ok member =>
    exact ⟨fun ⟨_, found, decodes⟩ => by cases found; exact decodes, fun h => ⟨member, rfl, h⟩⟩

/-- `array` admits exactly what `Json.getObjValAs? (Array Json)` admits. -/
theorem array_eq_ok_iff (value : Json) (key : String) (items : Array Json) :
    array value key = .ok items ↔ value.getObjValAs? (Array Json) key = .ok items :=
  get_eq_ok_iff_getObjValAs? (Array Json) (fun _ h => by cases h) value key items

/-- `text` admits exactly what `Json.getObjValAs? String` admits. -/
theorem text_eq_ok_iff (value : Json) (key : String) (result : String) :
    text value key = .ok result ↔ value.getObjValAs? String key = .ok result :=
  get_eq_ok_iff_getObjValAs? String (fun _ h => by cases h) value key result

/-- `bool` admits exactly what `Json.getObjValAs? Bool` admits. -/
theorem bool_eq_ok_iff (value : Json) (key : String) (result : Bool) :
    bool value key = .ok result ↔ value.getObjValAs? Bool key = .ok result :=
  get_eq_ok_iff_getObjValAs? Bool (fun _ h => by cases h) value key result

/-- Each refusal of `decoded` names the member, whichever decoder it runs; so does each refusal
of `object`, `get`, `array`, `text` and `bool`, which are `decoded` at their decoders. -/
theorem decoded_refusal_names {α : Type} (decode : Json → Except String α) (value : Json)
    (key reason : String) (h : decoded decode value key = .error reason) :
    ∃ detail, reason = "member '" ++ (key ++ detail) := by
  unfold decoded Member.value at h
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

/-- Each refusal of `value` names the member. -/
theorem value_refusal_names (value : Json) (key reason : String)
    (h : Member.value value key = .error reason) :
    ∃ detail, reason = "member '" ++ (key ++ detail) := by
  unfold Member.value at h
  split at h
  · split at h
    · cases h
    · cases h
      exact ⟨_, by simp only [String.append_assoc]; rfl⟩
  · cases h
    exact ⟨_, by simp only [String.append_assoc]; rfl⟩

end RegulaQualification.Member
