import Lean.Data.Json
import RegulaPolicy.Codec

/-! # Structural-name transport

Public structural-name transport. The policy decoder is the pure wire decoder;
JSON scalar admission is the operational bridge. Names retain every constructor.
Result diagnostics write a name as Lean prints it, adding its structural components only where
Lean's own parser would not read that text back exactly (`printedName_roundtrip`). -/
namespace Regula.RegistryCodec
open Lean

/-- The JSON components of a name, innermost first: `["str", s]` for a string component and
`["num", n]` for a numeric one. -/
def nameParts : Name → List Json
  | .anonymous => []
  | .str parent value => Json.arr #[.str "str", .str value] :: nameParts parent
  | .num parent value => Json.arr #[.str "num", toJson value] :: nameParts parent

/-- A Lean name as a JSON array of its `nameParts`. -/
def nameJson (name : Name) : Json := .arr (nameParts name).toArray

private def component (j : Json) : Except String RegulaPolicy.Codec.Wire := do
  let a ← j.getArr?
  match a.toList with
  | [.str "str", .str s] => return .array [.text "str", .text s]
  | [.str "num", n] => return .array [.text "num", .nat (← n.getNat?)]
  | _ => throw "invalid structural Lean name"

private def components : List Json → Except String (List RegulaPolicy.Codec.Wire)
  | [] => .ok []
  | x :: xs => return (← component x) :: (← components xs)

/-- Decode name components with the pure `RegulaPolicy.Codec` decoder; it recovers every name
from its `nameParts` (`nameParts_roundtrip`). -/
def parseNameParts (xs : List Json) : Except String Name := do
  RegulaPolicy.Codec.parseNameParts (← components xs)

/-- Decode a JSON array of name components; it recovers every name from its `nameJson`
(`name_roundtrip`). -/
def parseName (j : Json) : Except String Name := do
  parseNameParts (← j.getArr?).toList

private theorem components_encoded (n : Name) :
    components (nameParts n) = .ok (RegulaPolicy.Codec.nameParts n) := by
  induction n with
  | anonymous => rfl
  | str p s ih =>
    simp [components, component, nameParts, RegulaPolicy.Codec.nameParts, ih, Json.getArr?] <;> rfl
  | num p n ih =>
    simp [components, component, nameParts, RegulaPolicy.Codec.nameParts, ih, Json.getArr?,
      toJson, Json.getNat?, JsonNumber.fromNat] <;> rfl

/-- The JSON-tree bridge and pure decoder round-trip every Lean name. -/
theorem nameParts_roundtrip (n : Name) : parseNameParts (nameParts n) = .ok n := by
  unfold parseNameParts
  rw [components_encoded]
  exact RegulaPolicy.Codec.nameParts_roundtrip n

/-- Exact law for the public JSON-tree API; this is not a JSON text parser theorem. -/
theorem name_roundtrip (n : Name) : parseName (nameJson n) = .ok n := by
  simpa [parseName, nameJson, Json.getArr?] using nameParts_roundtrip n

/-- Whether Lean's own name parser (`String.toName`) reads the text Lean prints for `n`
(`Name.toString`, which escapes a component with `«»` where Lean's escaping can) back as `n`
itself. It does not for some names, such as one with a component containing `»` or with macro
scopes, which Lean prints without escaping. -/
def printsExactly (n : Name) : Bool := n.toString.toName == n

/-- A name as result JSON writes it: the text Lean prints for it, and its structural components
(`nameJson`) exactly when Lean's parser would not read that text back as the name
(`printsExactly`). -/
def printedName (n : Name) : String × Option Json :=
  (n.toString, if printsExactly n then none else some (nameJson n))

/-- The name a `printedName` denotes: the structural components when present, and otherwise what
Lean's parser reads from the text. -/
def parsePrintedName : String × Option Json → Except String Name
  | (text, none) => .ok text.toName
  | (_, some parts) => parseName parts

/-- `printsExactly` decides exactly that Lean's parser reads the printed text back as the name. -/
theorem printsExactly_iff (n : Name) : printsExactly n = true ↔ n.toString.toName = n :=
  beq_iff_eq

/-- Every name survives its printed form, whatever it is: the text alone where Lean's printer and
parser agree on it, its structural components otherwise. The parser is executed Lean code whose
agreement `printsExactly` decides for each name; no claim is made about which names it reads
back. -/
theorem printedName_roundtrip (n : Name) : parsePrintedName (printedName n) = .ok n := by
  unfold printedName
  cases h : printsExactly n with
  | true => exact congrArg Except.ok ((printsExactly_iff n).mp h)
  | false => exact name_roundtrip n

/-- The structural components are written exactly for the names whose printed text alone does
not denote them. -/
theorem printedName_parts_eq_none_iff (n : Name) :
    (printedName n).2 = none ↔ n.toString.toName = n := by
  rw [← printsExactly_iff]
  unfold printedName
  cases printsExactly n <;> simp

/-- The members of a name in a JSON object under `key`: `key` with its printed text and, only when
that text does not denote it, `key ++ "Parts"` with its structural components (`printedName`). -/
def nameFields (key : String) (n : Name) : List (String × Json) :=
  let (text, parts) := printedName n
  (key, .str text) :: (parts.map fun parts => (key ++ "Parts", parts)).toList

/-- Read the name `nameFields key` wrote into `j` (`parsePrintedName`); callers compare `j` with
its canonical re-encoding, which refuses parts that are not needed and text that does not match. -/
def parseNameFields (j : Json) (key : String) : Except String Name := do
  let text ← (← j.getObjVal? key).getStr?
  parsePrintedName (text, (j.getObjVal? (key ++ "Parts")).toOption)
end Regula.RegistryCodec
