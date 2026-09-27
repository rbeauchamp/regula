module

public import RegulaPolicy.Domain

/-! Pure tagged wire trees. The laws concern these exact encoders and decoders;
JSON text parsing, UTF-8 transport, and producer authenticity remain operational
boundaries. The JSON bridge uses this structural-name decoder directly. -/

@[expose] public section

namespace RegulaPolicy.Codec
open Lean

/-- Raw tree spines retain order and duplicate fields before any map construction. -/
inductive Wire where
  | null
  | bool (value : Bool)
  | nat (value : Nat)
  | text (value : String)
  | arrayNil
  | arrayCons (head tail : Wire)
  | objectNil
  | objectCons (key : String) (value tail : Wire)

/-- Explicit tree spines keep recursion structural, including malformed raw trees.
Array decoding below accepts only correctly terminated array spines. -/
def Wire.array (items : List Wire) : Wire := items.foldr .arrayCons .arrayNil

def Wire.object (fields : List (String × Wire)) : Wire :=
  fields.foldr (fun (key, value) tail => .objectCons key value tail) .objectNil

def Wire.arrayItems : Wire → Except String (List Wire)
  | .arrayNil => .ok []
  | .arrayCons head tail => return head :: (← tail.arrayItems)
  | _ => .error "expected wire array"

@[simp] theorem Wire.array_roundtrip (items : List Wire) :
    (Wire.array items).arrayItems = .ok items := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp [Wire.array, Wire.arrayItems] at *; rw [ih]; rfl

/-- Outer components first, preserving Lean's anonymous/str/num distinction. -/
def nameParts : Name → List Wire
  | .anonymous => []
  | .str p s => .array [.text "str", .text s] :: nameParts p
  | .num p n => .array [.text "num", .nat n] :: nameParts p

def parseNameParts : List Wire → Except String Name
  | [] => .ok .anonymous
  | .arrayCons (.text "str") (.arrayCons (.text s) .arrayNil) :: rest =>
      return .str (← parseNameParts rest) s
  | .arrayCons (.text "num") (.arrayCons (.nat n) .arrayNil) :: rest =>
      return .num (← parseNameParts rest) n
  | _ => .error "invalid structural Lean name"

def nameWire (n : Name) : Wire := .array (nameParts n)

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

def parseIdentity (w : Wire) : Except String Identity := do
  admitIdentity (← parseName w)

/-- Key admission preserves every valid identity through the actual decoder. -/
@[simp] theorem identity_roundtrip (i : Identity) :
    parseIdentity (identityWire i) = .ok i := by
  unfold parseIdentity identityWire
  rw [name_roundtrip]
  exact admitIdentity_exact i.name i.nonanonymous

/-- Category tags share their proved spelling codec; no open strings enter the result. -/
def categoryWire (spelling : α → String) (x : α) : Wire := .text (spelling x)

def parseCategory (parse : String → Option α) : Wire → Except String α
  | .text s => match parse s with
      | some x => .ok x
      | none => .error "unknown policy category"
  | _ => .error "expected policy category string"

/-- The accepted spelling has exactly one wire representation. -/
theorem category_canonical (spelling : α → String) (parse : String → Option α)
    (law : ∀ s x, parse s = some x → spelling x = s) (w : Wire) (x : α)
    (h : parseCategory parse w = .ok x) : categoryWire spelling x = w := by
  cases w <;> simp only [parseCategory] at h
  case text s =>
    split at h
    next y hy => cases h; exact congrArg Wire.text (law s _ hy)
    next => contradiction
  all_goals contradiction

/-- Reuse the category's finite proof, instead of duplicating its value table. -/
theorem category_roundtrip (spelling : α → String) (parse : String → Option α)
    (law : ∀ x, parse (spelling x) = some x) (x : α) :
    parseCategory parse (categoryWire spelling x) = .ok x := by
  simp [parseCategory, categoryWire, law]
end RegulaPolicy.Codec
