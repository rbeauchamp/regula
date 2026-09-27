module

public import RegulaPolicy.Domain

/-! # Tagged wire codec

Pure tagged wire trees. The laws concern these exact encoders and decoders;
JSON text parsing, UTF-8 transport, and producer authenticity remain operational
boundaries. The JSON bridge uses this structural-name decoder directly. -/

@[expose] public section

namespace RegulaPolicy.Codec

universe u
open Lean

/-- Raw tree spines retain order and duplicate fields before any map construction. -/
inductive Wire where
  /-- The JSON `null` value. -/
  | null
  /-- A Boolean scalar. -/
  | bool (value : Bool)
  /-- A natural-number scalar. -/
  | nat (value : Nat)
  /-- A string scalar. -/
  | text (value : String)
  /-- The end of an array spine: the empty array, or the tail after its last element. -/
  | arrayNil
  /-- An array spine cell: the element `head`, then the rest of the spine `tail`. -/
  | arrayCons (head tail : Wire)
  /-- The end of an object spine: the empty object, or the tail after its last field. -/
  | objectNil
  /-- An object spine cell: the field `key` with `value`, then the rest of the spine `tail`;
  a repeated key stays in place. -/
  | objectCons (key : String) (value tail : Wire)

/-- Explicit tree spines keep recursion structural, including malformed raw trees.
Array decoding below accepts only correctly terminated array spines. -/
def Wire.array (items : List Wire) : Wire := items.foldr .arrayCons .arrayNil

/-- The object spine holding `fields` in order, duplicates included. -/
def Wire.object (fields : List (String × Wire)) : Wire :=
  fields.foldr (fun (key, value) tail => .objectCons key value tail) .objectNil

/-- The elements of an array spine ending in `arrayNil`; any other tree is an error.
`Wire.array_roundtrip` shows it inverts `Wire.array`. -/
def Wire.arrayItems : Wire → Except String (List Wire)
  | .arrayNil => .ok []
  | .arrayCons head tail => return head :: (← tail.arrayItems)
  | _ => .error "expected wire array"

@[simp] theorem Wire.array_roundtrip (items : List Wire) :
    (Wire.array items).arrayItems = .ok items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [Wire.array, List.foldr_cons, Wire.arrayItems, bind_pure_comp] at *
    rw [ih]
    rfl

/-- Outer components first, preserving Lean's anonymous/str/num distinction. -/
def nameParts : Name → List Wire
  | .anonymous => []
  | .str p s => .array [.text "str", .text s] :: nameParts p
  | .num p n => .array [.text "num", .nat n] :: nameParts p

/-- Decode the components `nameParts` writes, outermost first: each is a two-element array
`["str", s]` or `["num", n]`; anything else is an error. `nameParts_roundtrip` shows it inverts
`nameParts`. -/
def parseNameParts : List Wire → Except String Name
  | [] => .ok .anonymous
  | .arrayCons (.text "str") (.arrayCons (.text s) .arrayNil) :: rest =>
      return .str (← parseNameParts rest) s
  | .arrayCons (.text "num") (.arrayCons (.nat n) .arrayNil) :: rest =>
      return .num (← parseNameParts rest) n
  | _ => .error "invalid structural Lean name"

/-- The wire encoding of a Lean name: the array of its `nameParts`. -/
def nameWire (n : Name) : Wire := .array (nameParts n)

/-- Decode a name from an array of components; `name_roundtrip` shows it inverts `nameWire`. -/
def parseName (w : Wire) : Except String Name := do
  parseNameParts (← w.arrayItems)

/-- All structural names round-trip, with no string grammar assumption. -/
@[simp] theorem nameParts_roundtrip (n : Name) : parseNameParts (nameParts n) = .ok n := by
  induction n with
  | anonymous => rfl
  | str p s ih => simp [nameParts, Wire.array, parseNameParts, ih] <;> rfl
  | num p n ih => simp [nameParts, Wire.array, parseNameParts, ih] <;> rfl

/-- Law for the public wire encoder/decoder pair. -/
@[simp] theorem name_roundtrip (n : Name) : parseName (nameWire n) = .ok n := by
  unfold parseName nameWire
  rw [Wire.array_roundtrip]
  exact nameParts_roundtrip n

/-- Nonanonymous keys use the same wire tree with an additional admission check. -/
def identityWire (i : Identity) : Wire := nameWire i.name

/-- Decode a name with `parseName`, then admit it as an identity (`admitIdentity`), so the
anonymous name is rejected. -/
def parseIdentity (w : Wire) : Except String Identity := do
  admitIdentity (← parseName w)

/-- Key admission preserves every valid identity through the actual decoder. -/
@[simp] theorem identity_roundtrip (i : Identity) :
    parseIdentity (identityWire i) = .ok i := by
  unfold parseIdentity identityWire
  rw [name_roundtrip]
  exact admitIdentity_exact i.name i.nonanonymous

/-- Category tags share their proved spelling codec; no open strings enter the result. -/
def categoryWire {α : Type u} (spelling : α → String) (x : α) : Wire := .text (spelling x)

/-- Decode a category from a string scalar with the category's `parse`; an unknown spelling or
a non-string tree is an error. -/
def parseCategory {α : Type u} (parse : String → Option α) : Wire → Except String α
  | .text s => match parse s with
      | some x => .ok x
      | none => .error "unknown policy category"
  | _ => .error "expected policy category string"

/-- The accepted spelling has exactly one wire representation. -/
theorem category_canonical {α : Type u} (spelling : α → String) (parse : String → Option α)
    (law : ∀ s x, parse s = some x → spelling x = s) (w : Wire) (x : α)
    (h : parseCategory parse w = .ok x) : categoryWire spelling x = w := by
  cases w <;> simp only [parseCategory] at h
  case text s =>
    split at h
    next y hy => cases h; exact congrArg Wire.text (law s _ hy)
    next => contradiction
  all_goals contradiction

/-- Reuse the category's finite proof, instead of duplicating its value table. -/
theorem category_roundtrip {α : Type u} (spelling : α → String) (parse : String → Option α)
    (law : ∀ x, parse (spelling x) = some x) (x : α) :
    parseCategory parse (categoryWire spelling x) = .ok x := by
  simp [parseCategory, categoryWire, law]
end RegulaPolicy.Codec
