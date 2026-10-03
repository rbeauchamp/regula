import Lean.Data.Json
import RegulaPolicy.Codec

/-! # Structural-name transport

Public structural-name transport. The policy decoder is the pure wire decoder;
JSON scalar admission is the operational bridge. Names retain every constructor.
Result documents and producer reports write a name as the text Lean prints for it, and as its
structural components only where Lean's own parser would not read that text back exactly
(`printedNameJson_roundtrip`). -/
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

/-- `printsExactly` decides exactly that Lean's parser reads the printed text back as the name. -/
theorem printsExactly_iff (n : Name) : printsExactly n = true ↔ n.toString.toName = n :=
  beq_iff_eq

/-- A name as result JSON writes it, wherever it occurs: the text Lean prints for it when Lean's
parser reads that text back as the name (`printsExactly`), and otherwise its structural
components (`nameJson`), a JSON array. -/
def printedNameJson (n : Name) : Json :=
  if printsExactly n then .str n.toString else nameJson n

/-- Read a name `printedNameJson` wrote: a string is read with Lean's parser and must be the text
Lean prints for the name it reads (`parsePrintedNameJson_str`); anything else is read as structural
components (`parseName`) and must be of a name whose printed text Lean's parser does not read
back. -/
def parsePrintedNameJson : Json → Except String Name
  | .str text =>
    let n := text.toName
    if n.toString == text then .ok n else .error s!"not a Lean name as Lean prints it: {text}"
  | j => do
    let n ← parseName j
    if printsExactly n then .error s!"structural components of {n}, which its printed text denotes"
    else .ok n

/-- Every name survives its written form: the printed text where Lean's printer and parser agree
on it, its structural components otherwise. The parser is executed Lean code whose agreement
`printsExactly` decides for each name; no claim is made about which names it reads back. -/
theorem printedNameJson_roundtrip (n : Name) :
    parsePrintedNameJson (printedNameJson n) = .ok n := by
  unfold printedNameJson
  cases h : printsExactly n with
  | true =>
    have e := (printsExactly_iff n).mp h
    simp [parsePrintedNameJson, e]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have := name_roundtrip n
    unfold nameJson at this ⊢
    simp only [parsePrintedNameJson, this]
    simp [bind, Except.bind, h]

/-- A name is written as a string exactly when Lean's parser reads its printed text back as the
name, and the string is then that text. -/
theorem printedNameJson_eq_str_iff (n : Name) (text : String) :
    printedNameJson n = .str text ↔ n.toString.toName = n ∧ text = n.toString := by
  rw [← printsExactly_iff]
  unfold printedNameJson nameJson
  cases printsExactly n <;> simp [eq_comm]

/-- A string is read only as the name whose written form it is, so each name has one written form
that the reader admits. -/
theorem parsePrintedNameJson_str {text : String} {n : Name}
    (h : parsePrintedNameJson (.str text) = .ok n) : printedNameJson n = .str text := by
  simp only [parsePrintedNameJson] at h
  split at h
  · next hp =>
    cases h
    have e : text.toName.toString = text := beq_iff_eq.mp hp
    have hx : printsExactly text.toName = true := (printsExactly_iff _).mpr (by rw [e])
    simp [printedNameJson, hx, e]
  · cases h

/-- `parseName` is a complete decision of the written names (`name_roundtrip`): it accepts the
JSON components of every name, and it refuses `null`. The kind is one-way: no theorem says it
accepts only values `nameJson` writes. -/
theorem checked_parseName : Regula.ExecutableContract parseName
    (Regula.DecidesCompletely (·.isOk = true) fun json => ∃ name, json = nameJson name) :=
  ⟨{ complete := fun _ ⟨name, written⟩ => by
       rw [written, name_roundtrip]
       rfl
     refused := ⟨.null, by decide⟩ }⟩

/-- `parsePrintedNameJson` is a complete decision of the written names
(`printedNameJson_roundtrip`): it accepts what `printedNameJson` writes for every name, and it
refuses `null`. The kind is one-way: the string branch runs Lean's own name parser, about which
nothing is proved, so no theorem says it accepts only written values. -/
theorem checked_parsePrintedNameJson : Regula.ExecutableContract parsePrintedNameJson
    (Regula.DecidesCompletely (·.isOk = true) fun json =>
      ∃ name, json = printedNameJson name) :=
  ⟨{ complete := fun _ ⟨name, written⟩ => by
       rw [written, printedNameJson_roundtrip]
       rfl
     refused := ⟨.null, by decide⟩ }⟩

end Regula.RegistryCodec
