import Lean.Data.Json
import Std.Data.TreeMap.Raw.AdditionalOperations

/-! # Source texts of a result document, stored once

A result document names every source text it carries with one member, `sourceText`. In the
document a checker builds and a reader consumes (the *logical* document) that member holds the text
and the top-level `sourceTexts` member is `null`. In the document a result file holds (the
*written* document) `sourceTexts` lists each distinct text once and every `sourceText` member is
the index of its text in that list. `intern` turns the first into the second and `expand` the
second into the first. `expand_intern` proves that the reader recovers exactly the document the
writer was given, and `intern_table` that the list holds each distinct text once and only texts the
document refers to, for every `Json` value, including one whose object trees are malformed. The
laws concern `Json` values, not JSON text, the files that hold it or the strings elsewhere in a
document. -/
namespace Regula.SourceTexts
open Lean
open Std.DTreeMap.Internal (Impl)

/-- The fields of a JSON object, as `Json.obj` stores them. -/
abbrev Fields := Impl String (fun _ => Json)

/-- The member whose value is a source text (logical document) or its index (written document). -/
def textKey : String := "sourceText"

/-- The top-level member that lists the distinct source texts of a written document. -/
def tableKey : String := "sourceTexts"

/-- A source text as the logical document carries it: an object whose `sourceText` is the text. -/
def textJson (text : String) : Json := Json.mkObj [(textKey, .str text)]

mutual
/-- Apply `leaf` to the value of every `sourceText` member of `value`, at any depth; everything
else, including each object tree's shape, is kept. -/
def mapTexts (leaf : Json → Json) : Json → Json
  | .arr elems => .arr (elems.map (mapTexts leaf))
  | .obj ⟨⟨fields⟩⟩ => .obj ⟨⟨mapFields leaf fields⟩⟩
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
termination_by value => sizeOf value
/-- `mapTexts` on the fields of one object. -/
def mapFields (leaf : Json → Json) : Fields → Fields
  | .leaf => .leaf
  | .inner size key value left right =>
      .inner size key (if key == textKey then leaf value else mapTexts leaf value)
        (mapFields leaf left) (mapFields leaf right)
termination_by fields => sizeOf fields
end

mutual
/-- The value of every `sourceText` member of `value`, at any depth, in document order. -/
def texts : Json → List Json
  | .arr elems => (elems.map texts).toList.flatten
  | .obj ⟨⟨fields⟩⟩ => textsFields fields
  | .null => []
  | .bool _ => []
  | .num _ => []
  | .str _ => []
termination_by value => sizeOf value
/-- `texts` on the fields of one object. -/
def textsFields : Fields → List Json
  | .leaf => []
  | .inner _ key value left right =>
      textsFields left ++ (if key == textKey then [value] else texts value) ++ textsFields right
termination_by fields => sizeOf fields
end

/-- The values of the `sourceTexts` members among `fields`, in tree order. -/
def slotsFields : Fields → List Json
  | .leaf => []
  | .inner _ key value left right =>
      slotsFields left ++ (if key == tableKey then [value] else []) ++ slotsFields right

/-- The values of the top-level `sourceTexts` members of a document: one for a well-formed result
object, none for any other value. -/
def slots : Json → List Json
  | .obj ⟨⟨fields⟩⟩ => slotsFields fields
  | _ => []

/-- `fields` with the value of every `sourceTexts` member replaced by `table`. -/
def setFields (table : Json) (fields : Fields) : Fields :=
  fields.map fun key value => if key == tableKey then table else value

/-- A document with the value of every top-level `sourceTexts` member replaced by `table`. -/
def setTable (table : Json) : Json → Json
  | .obj ⟨⟨fields⟩⟩ => .obj ⟨⟨setFields table fields⟩⟩
  | value => value

/-- The index of a text, as a written document carries it. -/
def refJson (index : Nat) : Json := .num ⟨.ofNat index, 0⟩

/-- The index a written `sourceText` value is, if it is a natural number. -/
def refOf? : Json → Option Nat
  | .num ⟨.ofNat index, 0⟩ => some index
  | _ => none

/-- The string a JSON value is, if it is one. -/
def strOf? : Json → Option String
  | .str text => some text
  | _ => none

/-- The position of `text` in `table`: its first occurrence, or the length of `table`. -/
def index (text : String) : List String → Nat
  | [] => 0
  | head :: rest => if head = text then 0 else index text rest + 1

/-- The distinct texts of `found`, each at its first occurrence. -/
def dedup (found : List String) : List String :=
  found.foldl (fun table text => if text ∈ table then table else table ++ [text]) []

/-- A text as the written document carries it: its index in `table`. -/
def internLeaf (table : List String) : Json → Json
  | .str text => refJson (index text table)
  | value => value

/-- An index as the logical document carries it: the text `table` holds there. -/
def expandLeaf (table : List String) (value : Json) : Json :=
  match refOf? value with
  | some position =>
      match table[position]? with
      | some text => .str text
      | none => value
  | none => value

/-- The `sourceTexts` member of a written document: its texts in order. -/
def tableJson (table : List String) : Json := .arr (table.map Json.str).toArray

/-- The texts a `sourceTexts` member lists, if it is an array of strings. -/
def tableOf? : Json → Option (List String)
  | .arr elems =>
      if elems.toList.all (fun value => (strOf? value).isSome) then
        some (elems.toList.filterMap strOf?)
      else none
  | _ => none

/-- Every `sourceText` member of `value` is an index into `table`. -/
def refsValid (table : List String) (value : Json) : Bool :=
  (texts value).all fun ref =>
    match refOf? ref with
    | some position => position < table.length
    | none => false

/-- The written form of a logical result document: `sourceTexts` lists each distinct text of a
`sourceText` member once, at its first occurrence, and each such member holds the index of its
text. Refused unless the document is an object with exactly one `sourceTexts` member, whose value
is `null`, and every `sourceText` member is a string. -/
def intern (document : Json) : Except String Json :=
  match slots document with
  | [.null] =>
      let found := texts document
      if found.all (fun value => (strOf? value).isSome) then
        let table := dedup (found.filterMap strOf?)
        .ok (setTable (tableJson table) (mapTexts (internLeaf table) document))
      else .error "result document: a sourceText member is not a string"
  | _ => .error "result document: expected one top-level sourceTexts member, null"

/-- The logical document a written one stands for: each `sourceText` member holds the text its
index names and `sourceTexts` is `null`. Refused unless the document is an object with exactly one
`sourceTexts` member, an array of distinct strings, and every `sourceText` member is an index
into it. -/
def expand (written : Json) : Except String Json :=
  match slots written with
  | [slot] =>
      match tableOf? slot with
      | some table =>
          if table.Nodup ∧ refsValid table written = true then
            .ok (mapTexts (expandLeaf table) (setTable .null written))
          else .error "result document: repeated source text or sourceText index out of range"
      | none => .error "result document: sourceTexts is not an array of strings"
  | _ => .error "result document: expected one top-level sourceTexts member"

/-! ### Laws -/

private theorem sizeOf_lt_arr {value : Json} {elems : Array Json} (h : value ∈ elems) :
    sizeOf value < sizeOf (Json.arr elems) := by
  have := Array.sizeOf_lt_of_mem h
  simp only [Json.arr.sizeOf_spec]
  omega

/-- The cases of an induction over a JSON value and the object trees inside it. -/
structure Cases (motive : Json → Prop) (fieldsMotive : Fields → Prop) : Prop where
  /-- `null`. -/
  null : motive .null
  /-- A boolean. -/
  bool : ∀ b, motive (.bool b)
  /-- A number. -/
  num : ∀ n, motive (.num n)
  /-- A string. -/
  str : ∀ s, motive (.str s)
  /-- An array whose elements have the property. -/
  arr : ∀ elems : Array Json, (∀ value ∈ elems, motive value) → motive (.arr elems)
  /-- An object whose fields have the property. -/
  obj : ∀ fields : Fields, fieldsMotive fields → motive (.obj ⟨⟨fields⟩⟩)
  /-- The empty tree. -/
  leaf : fieldsMotive .leaf
  /-- A tree node whose value and subtrees have the property. -/
  inner : ∀ size key value left right, motive value → fieldsMotive left → fieldsMotive right →
    fieldsMotive (.inner size key value left right)

mutual
/-- Induction over a JSON value, through the object trees inside it. -/
theorem Cases.value {motive : Json → Prop} {fieldsMotive : Fields → Prop}
    (cases : Cases motive fieldsMotive) : ∀ value : Json, motive value
  | .null => cases.null
  | .bool b => cases.bool b
  | .num n => cases.num n
  | .str s => cases.str s
  | .arr elems => cases.arr elems fun value _ => cases.value value
  | .obj ⟨⟨fields⟩⟩ => cases.obj fields (cases.fields fields)
termination_by value => sizeOf value
decreasing_by
  · exact sizeOf_lt_arr ‹_›
  · simp only [Json.obj.sizeOf_spec, Std.TreeMap.Raw.mk.sizeOf_spec,
      Std.DTreeMap.Raw.mk.sizeOf_spec]
    omega
/-- Induction over an object tree, through the JSON values inside it. -/
theorem Cases.fields {motive : Json → Prop} {fieldsMotive : Fields → Prop}
    (cases : Cases motive fieldsMotive) : ∀ fields : Fields, fieldsMotive fields
  | .leaf => cases.leaf
  | .inner size key value left right =>
      cases.inner size key value left right (cases.value value) (cases.fields left)
        (cases.fields right)
termination_by fields => sizeOf fields
end

theorem textKey_ne_tableKey : (tableKey == textKey) = false := by decide

/-- `mapFields` is the tree's own value map, so it keeps every key and the tree's shape. -/
theorem mapFields_eq_map (leaf : Json → Json) (fields : Fields) :
    mapFields leaf fields =
      fields.map fun key value => if key == textKey then leaf value else mapTexts leaf value := by
  induction fields with
  | leaf => simp [mapFields, Impl.map]
  | inner size key value left right hl hr => simp [mapFields, Impl.map, hl, hr]

/-- The `sourceText` values of a mapped document are the mapped values, in the same order. -/
theorem texts_mapTexts (leaf : Json → Json) (value : Json) :
    texts (mapTexts leaf value) = (texts value).map leaf := by
  refine Cases.value (motive := fun value => texts (mapTexts leaf value) = (texts value).map leaf)
    (fieldsMotive := fun fields =>
      textsFields (mapFields leaf fields) = (textsFields fields).map leaf) ?_ value
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mapTexts, texts]
  · intro b; simp [mapTexts, texts]
  · intro n; simp [mapTexts, texts]
  · intro s; simp [mapTexts, texts]
  · intro elems ih
    simp only [mapTexts, texts, Array.toList_map, List.map_map, List.map_flatten]
    congr 1
    apply List.map_congr_left
    intro value member
    exact ih value (Array.mem_toList_iff.mp member)
  · intro fields ih
    simpa [mapTexts, texts] using ih
  · simp [mapFields, textsFields]
  · intro size key value left right hv hl hr
    simp only [mapFields, textsFields, List.map_append, hl, hr]
    by_cases h : (key == textKey) = true <;> simp [h, hv]

theorem refOf?_refJson (position : Nat) : refOf? (refJson position) = some position := rfl

theorem getElem?_index {text : String} :
    ∀ {table : List String}, text ∈ table → table[index text table]? = some text
  | head :: rest, member => by
    by_cases h : head = text
    · simp [index, h]
    · have tail : text ∈ rest := by
        rcases List.mem_cons.mp member with rfl | tail
        · exact absurd rfl h
        · exact tail
      simpa [index, h] using getElem?_index tail

theorem index_lt {text : String} :
    ∀ {table : List String}, text ∈ table → index text table < table.length
  | head :: rest, member => by
    by_cases h : head = text
    · simp [index, h]
    · have tail : text ∈ rest := by
        rcases List.mem_cons.mp member with rfl | tail
        · exact absurd rfl h
        · exact tail
      simpa [index, h] using index_lt tail

/-- A text of the table survives the writer's index and the reader's lookup. -/
theorem expandLeaf_internLeaf {table : List String} {text : String} (member : text ∈ table) :
    expandLeaf table (internLeaf table (.str text)) = .str text := by
  simp [expandLeaf, internLeaf, refOf?_refJson, getElem?_index member]

private theorem dedup_fold (found : List String) :
    ∀ table : List String, table.Nodup →
      (found.foldl (fun table text => if text ∈ table then table else table ++ [text])
        table).Nodup ∧
      ∀ text, text ∈ found.foldl
        (fun table text => if text ∈ table then table else table ++ [text]) table ↔
          text ∈ table ∨ text ∈ found := by
  induction found with
  | nil => intro table nodup; simp [nodup]
  | cons head rest ih =>
    intro table nodup
    by_cases h : head ∈ table
    · obtain ⟨distinct, members⟩ := ih table nodup
      refine ⟨by simpa [List.foldl, h] using distinct, fun text => ?_⟩
      simp only [List.foldl, h, ↓reduceIte, members, List.mem_cons]
      constructor
      · rintro (m | m)
        · exact .inl m
        · exact .inr (.inr m)
      · rintro (m | rfl | m)
        · exact .inl m
        · exact .inl h
        · exact .inr m
    · have extended : (table ++ [head]).Nodup := by
        rw [List.nodup_append]
        refine ⟨nodup, by simp, ?_⟩
        intro a ha b hb
        rcases List.mem_singleton.mp hb with rfl
        rintro rfl
        exact h ha
      obtain ⟨distinct, members⟩ := ih (table ++ [head]) extended
      refine ⟨by simpa [List.foldl, h] using distinct, fun text => ?_⟩
      simp only [List.foldl, h, ↓reduceIte, members, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact or_assoc

/-- `dedup` lists no text twice. -/
theorem dedup_nodup (found : List String) : (dedup found).Nodup :=
  (dedup_fold found [] List.nodup_nil).1

/-- `dedup` lists exactly the texts it was given. -/
theorem mem_dedup (found : List String) (text : String) : text ∈ dedup found ↔ text ∈ found := by
  simpa [dedup] using (dedup_fold found [] List.nodup_nil).2 text

/-- The reader recovers the texts the writer listed. -/
theorem tableOf?_tableJson (table : List String) : tableOf? (tableJson table) = some table := by
  have strings : (table.map Json.str).all (fun value => (strOf? value).isSome) = true := by
    simp [strOf?]
  have recovered : (table.map Json.str).filterMap strOf? = table := by
    induction table with
    | nil => rfl
    | cons head rest ih => simp [strOf?] at ih ⊢; exact ih
  simp [tableOf?, tableJson, strings, recovered]

/-- Values that are all strings are the strings `filterMap strOf?` extracts from them. -/
theorem str_of_all {found : List Json}
    (strings : found.all (fun value => (strOf? value).isSome) = true) {value : Json}
    (member : value ∈ found) : ∃ text, value = .str text ∧ text ∈ found.filterMap strOf? := by
  have isString := List.all_eq_true.mp strings value member
  cases value with
  | str text => exact ⟨text, rfl, List.mem_filterMap.mpr ⟨_, member, rfl⟩⟩
  | _ => simp [strOf?] at isString

/-- A document whose `sourceText` members are texts of `table` survives the writer's indices and
the reader's lookups unchanged. -/
theorem mapTexts_expand_intern (table : List String) (value : Json) :
    (∀ ref ∈ texts value, ∃ text, ref = .str text ∧ text ∈ table) →
      mapTexts (expandLeaf table) (mapTexts (internLeaf table) value) = value := by
  refine Cases.value (motive := fun value =>
    (∀ ref ∈ texts value, ∃ text, ref = .str text ∧ text ∈ table) →
      mapTexts (expandLeaf table) (mapTexts (internLeaf table) value) = value)
    (fieldsMotive := fun fields =>
      (∀ ref ∈ textsFields fields, ∃ text, ref = .str text ∧ text ∈ table) →
        mapFields (expandLeaf table) (mapFields (internLeaf table) fields) = fields) ?_ value
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _; simp [mapTexts]
  · intro b _; simp [mapTexts]
  · intro n _; simp [mapTexts]
  · intro s _; simp [mapTexts]
  · intro elems ih covered
    simp only [mapTexts, Array.map_map]
    congr 1
    conv => rhs; rw [← Array.map_id elems]
    apply Array.map_congr_left
    intro element member
    exact ih element member fun ref inside => covered ref (by
      simp only [texts, Array.toList_map]
      exact List.mem_flatten.mpr ⟨texts element,
        List.mem_map.mpr ⟨element, Array.mem_toList_iff.mpr member, rfl⟩, inside⟩)
  · intro fields ih covered
    simp only [mapTexts]
    rw [ih (by simpa [texts] using covered)]
  · intro _; simp [mapFields]
  · intro size key value left right hv hl hr covered
    have parts : ∀ ref, (ref ∈ textsFields left ∨
        ref ∈ (if key == textKey then [value] else texts value) ∨ ref ∈ textsFields right) →
          ∃ text, ref = .str text ∧ text ∈ table := by
      intro ref inside
      apply covered ref
      simp only [textsFields, List.mem_append]
      rcases inside with m | m | m
      · exact .inl (.inl m)
      · exact .inl (.inr m)
      · exact .inr m
    simp only [mapFields]
    rw [hl fun ref m => parts ref (.inl m), hr fun ref m => parts ref (.inr (.inr m))]
    by_cases h : (key == textKey) = true
    · obtain ⟨text, rfl, member⟩ := parts value (.inr (.inl (by simp [h])))
      simp [h, expandLeaf_internLeaf member]
    · have inner := hv fun ref m => parts ref (.inr (.inl (by simpa [h] using m)))
      simp [h, inner]

theorem slotsFields_map (f : String → Json → Json) (fields : Fields) :
    slotsFields (fields.map f) = (slotsFields fields).map (f tableKey) := by
  induction fields with
  | leaf => simp [slotsFields, Impl.map]
  | inner size key value left right hl hr =>
    simp only [Impl.map, slotsFields, hl, hr, List.map_append]
    by_cases h : (key == tableKey) = true
    · have : key = tableKey := by simpa using h
      simp [this]
    · simp [h]

theorem map_map (f g : String → Json → Json) (fields : Fields) :
    (fields.map f).map g = fields.map fun key value => g key (f key value) := by
  induction fields with
  | leaf => simp [Impl.map]
  | inner size key value left right hl hr => simp [Impl.map, hl, hr]

/-- A value map that returns every value of the tree unchanged returns the tree. The conditions
are stated on the tree's `sourceTexts` and `sourceText` members, which decide the maps here. -/
theorem map_eq_self (f : String → Json → Json) (fields : Fields)
    (slot : ∀ value ∈ slotsFields fields, f tableKey value = value)
    (text : ∀ value ∈ textsFields fields, f textKey value = value)
    (other : ∀ key value, (key == tableKey) = false → (key == textKey) = false →
      (∀ ref ∈ texts value, ref ∈ textsFields fields) → f key value = value) :
    fields.map f = fields := by
  induction fields with
  | leaf => simp [Impl.map]
  | inner size key value left right hl hr =>
    have leftSlots : ∀ v ∈ slotsFields left, f tableKey v = v := fun v m =>
      slot v (by simp [slotsFields, m])
    have rightSlots : ∀ v ∈ slotsFields right, f tableKey v = v := fun v m =>
      slot v (by simp [slotsFields, m])
    have leftTexts : ∀ v ∈ textsFields left, v ∈ textsFields (.inner size key value left right) :=
      fun v m => by simp [textsFields, m]
    have rightTexts :
        ∀ v ∈ textsFields right, v ∈ textsFields (.inner size key value left right) :=
      fun v m => by simp [textsFields, m]
    simp only [Impl.map]
    rw [hl leftSlots (fun v m => text v (leftTexts v m))
        (fun k v a b inside => other k v a b fun ref m => leftTexts ref (inside ref m)),
      hr rightSlots (fun v m => text v (rightTexts v m))
        (fun k v a b inside => other k v a b fun ref m => rightTexts ref (inside ref m))]
    congr 1
    by_cases hs : (key == tableKey) = true
    · have : key = tableKey := by simpa using hs
      subst this
      exact slot value (by simp [slotsFields])
    · by_cases ht : (key == textKey) = true
      · have : key = textKey := by simpa using ht
        subst this
        exact text value (by simp [textsFields])
      · exact other key value (by simpa using hs) (by simpa using ht) fun ref m => by
          simp [textsFields, ht, m]

/-- Replacing the `sourceTexts` values by one without `sourceText` members, where they had none,
changes no `sourceText` member. -/
theorem textsFields_setFields (table : Json) (fields : Fields) (empty : texts table = [])
    (slot : ∀ value ∈ slotsFields fields, texts value = []) :
    textsFields (setFields table fields) = textsFields fields := by
  unfold setFields
  induction fields with
  | leaf => simp [Impl.map]
  | inner size key value left right hl hr =>
    have leftSlots : ∀ v ∈ slotsFields left, texts v = [] := fun v m =>
      slot v (by simp [slotsFields, m])
    have rightSlots : ∀ v ∈ slotsFields right, texts v = [] := fun v m =>
      slot v (by simp [slotsFields, m])
    simp only [Impl.map, textsFields, hl leftSlots, hr rightSlots]
    by_cases hs : (key == tableKey) = true
    · have : key = tableKey := by simpa using hs
      subst this
      have none := slot value (by simp [slotsFields])
      simp [textKey_ne_tableKey, empty, none]
    · simp [hs]

theorem texts_tableJson (table : List String) : texts (tableJson table) = [] := by
  simp only [tableJson, texts, Array.toList_map, List.map_map]
  apply List.flatten_eq_nil_iff.mpr
  intro l member
  obtain ⟨text, -, rfl⟩ := List.mem_map.mp member
  simp [texts]

/-- What a successful `intern` computed: the document is an object whose one `sourceTexts`
member is `null` and whose `sourceText` members are strings, and the written document is that
object with indices into the distinct texts. -/
theorem intern_eq_ok {document written : Json} (h : intern document = .ok written) :
    ∃ fields, document = .obj ⟨⟨fields⟩⟩ ∧ slotsFields fields = [.null] ∧
      (texts document).all (fun value => (strOf? value).isSome) = true ∧
      written = setTable (tableJson (dedup ((texts document).filterMap strOf?)))
        (mapTexts (internLeaf (dedup ((texts document).filterMap strOf?))) document) := by
  unfold intern at h
  split at h
  next slot =>
    by_cases strings : ((texts document).all fun value => (strOf? value).isSome) = true
    · simp only [strings, ↓reduceIte] at h
      obtain rfl := Except.ok.inj h
      cases document with
      | obj raw =>
        obtain ⟨⟨fields⟩⟩ := raw
        exact ⟨fields, rfl, slot, strings, rfl⟩
      | _ => simp [slots] at slot
    · simp [strings] at h
  next => cases h

/-- **The reader recovers the document the writer was given.** Whenever `intern` writes a
document, `expand` of what it wrote is that document: every `sourceText` member holds its text
again and `sourceTexts` is `null`. -/
theorem expand_intern {document written : Json} (h : intern document = .ok written) :
    expand written = .ok document := by
  obtain ⟨fields, rfl, slot, strings, rfl⟩ := intern_eq_ok h
  generalize hfound : (texts (Json.obj ⟨⟨fields⟩⟩)).filterMap strOf? = found at *
  have covered : ∀ ref ∈ textsFields fields, ∃ text, ref = .str text ∧ text ∈ dedup found := by
    intro ref member
    obtain ⟨text, rfl, inside⟩ := str_of_all strings (by simpa [texts] using member)
    exact ⟨text, rfl, (mem_dedup found text).mpr (hfound ▸ inside)⟩
  have nulls : ∀ value ∈ slotsFields fields, value = .null := by
    intro value member
    rw [slot] at member
    simpa using member
  -- The written document, as one value map of the logical fields.
  have writtenFields :
      setTable (tableJson (dedup found)) (mapTexts (internLeaf (dedup found)) (.obj ⟨⟨fields⟩⟩)) =
        .obj ⟨⟨setFields (tableJson (dedup found)) (mapFields (internLeaf (dedup found)) fields)⟩⟩ := by
    simp [mapTexts, setTable]
  rw [writtenFields]
  have mappedSlots : slotsFields (mapFields (internLeaf (dedup found)) fields) = [.null] := by
    rw [mapFields_eq_map, slotsFields_map, slot]
    simp [textKey_ne_tableKey, mapTexts]
  have writtenSlots : slotsFields (setFields (tableJson (dedup found))
      (mapFields (internLeaf (dedup found)) fields)) = [tableJson (dedup found)] := by
    unfold setFields
    rw [slotsFields_map, mappedSlots]
    simp
  have writtenTexts : textsFields (setFields (tableJson (dedup found))
      (mapFields (internLeaf (dedup found)) fields)) =
        (textsFields fields).map (internLeaf (dedup found)) := by
    rw [textsFields_setFields _ _ (texts_tableJson _) (by
      intro value member
      rw [mappedSlots] at member
      have : value = .null := by simpa using member
      subst this
      simp [texts])]
    have := texts_mapTexts (internLeaf (dedup found)) (.obj ⟨⟨fields⟩⟩)
    simpa [mapTexts, texts] using this
  have valid : refsValid (dedup found) (.obj ⟨⟨setFields (tableJson (dedup found))
      (mapFields (internLeaf (dedup found)) fields)⟩⟩) = true := by
    simp only [refsValid, texts, writtenTexts, List.all_eq_true, List.mem_map]
    rintro ref ⟨original, member, rfl⟩
    obtain ⟨text, rfl, inside⟩ := covered original member
    simp [internLeaf, refOf?_refJson, index_lt inside]
  simp only [expand, slots, writtenSlots, tableOf?_tableJson, dedup_nodup, valid, and_self,
    ↓reduceIte, setTable, mapTexts]
  refine congrArg (fun restored : Fields => (Except.ok (Json.obj ⟨⟨restored⟩⟩) : Except String Json))
    ?_
  -- Reset the table, then look every index up: one value map, which returns each value.
  unfold setFields
  rw [mapFields_eq_map, mapFields_eq_map, map_map, map_map, map_map]
  apply map_eq_self
  · intro value member
    have := nulls value member
    subst this
    simp [textKey_ne_tableKey, mapTexts]
  · intro value member
    obtain ⟨text, rfl, inside⟩ := covered value member
    have distinct : (textKey == tableKey) = false := by decide
    simp [distinct, expandLeaf_internLeaf inside]
  · intro key value notSlot notText inside
    simp only [notSlot, notText, Bool.false_eq_true, ↓reduceIte]
    exact mapTexts_expand_intern (dedup found) value fun ref member =>
      covered ref (inside ref member)

/-- `intern` writes every document that is an object with one `sourceTexts` member, `null`, and
whose `sourceText` members are all strings, and refuses every other: it is not an
always-refusing writer. -/
theorem intern_isOk_iff (document : Json) :
    (∃ written, intern document = .ok written) ↔
      slots document = [.null] ∧ ∀ value ∈ texts document, ∃ text, value = .str text := by
  constructor
  · rintro ⟨written, h⟩
    obtain ⟨fields, rfl, slot, strings, -⟩ := intern_eq_ok h
    exact ⟨slot, fun value member => (str_of_all strings member).imp fun _ h => h.1⟩
  · rintro ⟨slot, strings⟩
    have all : (texts document).all (fun value => (strOf? value).isSome) = true := by
      rw [List.all_eq_true]
      intro value member
      obtain ⟨text, rfl⟩ := strings value member
      rfl
    refine ⟨setTable (tableJson (dedup ((texts document).filterMap strOf?)))
      (mapTexts (internLeaf (dedup ((texts document).filterMap strOf?))) document), ?_⟩
    simp [intern, slot, all]

/-- **Each text once.** The `sourceTexts` member of a written document lists no text twice and
exactly the texts of the logical document's `sourceText` members, and every `sourceText` member
of the written document is an index into it: the written document holds each distinct text once,
in `sourceTexts`, and no text in a `sourceText` member. -/
theorem intern_table {document written : Json} (h : intern document = .ok written) :
    ∃ table : List String, slots written = [tableJson table] ∧ table.Nodup ∧
      (∀ text, text ∈ table ↔ Json.str text ∈ texts document) ∧
      ∀ ref ∈ texts written, ∃ position, ref = refJson position ∧ position < table.length := by
  obtain ⟨fields, rfl, slot, strings, rfl⟩ := intern_eq_ok h
  generalize hfound : (texts (Json.obj ⟨⟨fields⟩⟩)).filterMap strOf? = found at *
  have mappedSlots : slotsFields (mapFields (internLeaf (dedup found)) fields) = [.null] := by
    rw [mapFields_eq_map, slotsFields_map, slot]
    simp [textKey_ne_tableKey, mapTexts]
  refine ⟨dedup found, ?_, dedup_nodup found, fun text => ?_, ?_⟩
  · simp only [mapTexts, setTable, slots]
    unfold setFields
    rw [slotsFields_map, mappedSlots]
    simp
  · rw [mem_dedup, ← hfound, List.mem_filterMap]
    constructor
    · rintro ⟨value, member, isText⟩
      cases value <;> simp [strOf?] at isText
      subst isText
      exact member
    · intro member
      exact ⟨_, member, rfl⟩
  · intro ref member
    have writtenTexts : texts (setTable (tableJson (dedup found))
        (mapTexts (internLeaf (dedup found)) (.obj ⟨⟨fields⟩⟩))) =
          (texts (Json.obj ⟨⟨fields⟩⟩)).map (internLeaf (dedup found)) := by
      rw [← texts_mapTexts]
      simp only [mapTexts, setTable, texts]
      exact textsFields_setFields _ _ (texts_tableJson _) (by
        intro value inside
        rw [mappedSlots] at inside
        have : value = .null := by simpa using inside
        subst this
        simp [texts])
    rw [writtenTexts] at member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    obtain ⟨text, rfl, found'⟩ := str_of_all strings inside
    exact ⟨index text (dedup found), rfl,
      index_lt ((mem_dedup found text).mpr (hfound ▸ found'))⟩

/-- What a reader may rely on for any document `expand` admits, whoever wrote it: every
`sourceText` member of the result is a string. -/
theorem expand_texts {written document : Json} (h : expand written = .ok document) :
    ∀ value ∈ texts document, ∃ text, value = .str text := by
  unfold expand at h
  split at h
  next slot hslot =>
    split at h
    next table htable =>
      split at h
      next valid =>
        cases h
        intro value member
        rw [texts_mapTexts] at member
        obtain ⟨ref, inside, rfl⟩ := List.mem_map.mp member
        have refs : ∀ ref ∈ texts written, ∃ position, refOf? ref = some position ∧
            position < table.length := by
          intro ref member
          have := List.all_eq_true.mp valid.2 ref member
          split at this
          next position isRef => exact ⟨position, isRef, by simpa using this⟩
          next => cases this
        -- The reset table has no `sourceText` member, so the members are the written ones.
        have same : texts (setTable .null written) = texts written := by
          cases written with
          | obj raw =>
            obtain ⟨⟨fields⟩⟩ := raw
            simp only [setTable, texts]
            apply textsFields_setFields _ _ (by simp [texts])
            intro value member
            have : slotsFields fields = [slot] := by simpa [slots] using hslot
            rw [this] at member
            have : value = slot := by simpa using member
            subst this
            cases value with
            | arr elems =>
              have strings : elems.toList.all (fun value => (strOf? value).isSome) = true := by
                simp only [tableOf?] at htable
                split at htable
                next all => exact all
                next => cases htable
              simp only [texts, Array.toList_map]
              apply List.flatten_eq_nil_iff.mpr
              intro l member
              obtain ⟨element, inside, rfl⟩ := List.mem_map.mp member
              obtain ⟨text, rfl, -⟩ := str_of_all strings inside
              simp [texts]
            | _ => simp [tableOf?] at htable
          | _ => simp [setTable]
        rw [same] at inside
        obtain ⟨position, isRef, bound⟩ := refs ref inside
        obtain ⟨text, found⟩ : ∃ text, table[position]? = some text :=
          ⟨table[position], List.getElem?_eq_getElem bound⟩
        exact ⟨text, by simp [expandLeaf, isRef, found]⟩
      next => cases h
    next => cases h
  next => cases h

end Regula.SourceTexts
