import Lean.Data.Json
import RegulaPolicy.Codec
import Regula.Contract
import Regula.Decision

/-! # Strict operational JSON text

Strict JSON parsing and compact printing, both total. The parser is adapted from the Lean 4
repository's `src/Lean/Data/Json/Parser.lean`: its string, number and container parsers, with
the container recursion rejecting a duplicate key before insertion and every recursive call
guarded with consumed input, which makes it total where Lean's own string, number and value
parsers are `partial`. `ws` and `literal` restate Std's `ws` and `skipString`
(`src/Std/Internal/Parsec/String.lean`) by characters. The printer `compress` is adapted from
`src/Lean/Data/Json/Printer.lean` (`Json.compress`, `Json.escape`), written by structural
recursion. Upstream notices as at `v4.34.1`, retained:

    src/Lean/Data/Json/Parser.lean:
    Copyright (c) 2019 Gabriel Ebner. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Gabriel Ebner, Marc Huisinga

    src/Lean/Data/Json/Printer.lean:
    Copyright (c) 2019 Gabriel Ebner. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Gabriel Ebner, Marc Huisinga, Wojciech Nawrocki

    src/Std/Internal/Parsec/String.lean:
    Copyright (c) 2021 Microsoft Corporation. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Author: Dany Fabian, Henrik Böving

The Apache 2.0 license text is `LICENSES/Apache-2.0.txt` in this repository.

`compress` follows `Json.compress`, except for a number with a positive exponent: it writes the
mantissa, then `e-` and the exponent, so that the parse is the same mantissa and exponent. That
the two texts are otherwise equal is not proved, since `Json.compress` is `partial`; no theorem
depends on it. `Json.compress` writes a number with a positive exponent as a decimal fraction
without trailing zeros, which reads back as a different `JsonNumber` when the mantissa ends in
zero. `JsonRoundTrip` proves that `parse` of the text `compress` writes for a value whose object
trees are search trees is the value with each object tree as the parser builds it
(`JsonCanon.canon`).

The reading of a document has two parts. `parse` turns a text into a `Json` value. `exactFields`
is a pure decision about the `Json` value that a caller gives: whether it is an object with
exactly the expected members. `checked_exactFields` registers its kind, sound and complete against
`ExactFields`. The pure laws do not prove external producer authenticity. -/
namespace Regula.Checker.PolicyCodec
open Lean Std.Internal.Parsec Std.Internal.Parsec.String

/-! ### Parsing -/

/-- The fields of a JSON object, as `Json.obj` stores them. -/
abbrev Fields := Std.DTreeMap.Internal.Impl String (fun _ => Json)

/-- Parser input: the text and the current position in it. -/
abbrev Input := Sigma String.Pos

/-- The result of a parser step. -/
abbrev Result (α : Type) := Std.Internal.Parsec.ParseResult α Input

/-- Input bytes after the current position, the measure of the recursion below. -/
def remaining (it : Input) : Nat :=
  it.1.utf8ByteSize - it.2.offset.byteIdx

/-- Continue with `k` only when input has been consumed since `start`. The check makes the
termination argument executable and cannot fail: each use follows a successful `skip` or
`any` after `start`, and core `Parsec` steps only advance within the same text. -/
@[inline] def descend {α : Type} (start : Input)
    (k : (it : Input) → remaining it < remaining start → Result α) : Parser α := fun it =>
  if h : remaining it < remaining start then k it h
  else .error it (.other "JSON parser made no progress")

/-- As `descend`, where no input need have been consumed since `start` (it has not grown). -/
@[inline] def stay {α : Type} (start : Input)
    (k : (it : Input) → remaining it ≤ remaining start → Result α) : Parser α := fun it =>
  if h : remaining it ≤ remaining start then k it h
  else .error it (.other "JSON parser made no progress")

/-- Whether `c` is JSON whitespace: tab, line feed, carriage return or space. -/
def isWs (c : Char) : Bool := c = '\t' || c = '\n' || c = '\r' || c = ' '

/-- The position after the whitespace at `p`. It restates the `skipWs` that Std's `ws` calls
(`Std/Internal/Parsec/String.lean`, v4.34.1), which is private to Std, so no proof here can name
it. -/
def skipWs {s : String} (p : s.Pos) : s.Pos :=
  if h : p ≠ s.endPos then
    if isWs (p.get h) then skipWs (p.next h) else p
  else p
termination_by p

/-- Skip whitespace, as Std's `ws` does, over `skipWs`, which a proof can unfold. -/
def ws : Parser Unit := fun it => .success ⟨_, skipWs it.2⟩ ()

/-- The characters of a JSON string after its opening quote, through its closing quote. Lean's
`Json.Parser.strCore` is `partial` (`Lean/Data/Json/Parser.lean:75`, v4.34.1), so no proof unfolds
it; this is its definition, made total by `descend`. -/
def strCore (acc : String) (start : Input) : Result String := (show Parser String from do
  let c ← peek!
  if c == '"' then
    skip
    return acc
  else
    let c ← any
    if c == '\\' then
      let e ← Json.Parser.escapedChar
      descend start fun it _ => strCore (acc.push e) it
    else if 0x0020 <= c.val && c.val <= 0x10ffff then
      descend start fun it _ => strCore (acc.push c) it
    else
      fail "unexpected character in string") start
termination_by remaining start

/-- A JSON string after its opening quote. -/
def str : Parser String := strCore ""

/-- The digits at the input, as a number after the digits `acc` stands for. Lean's
`Json.Parser.natCore` is `partial` (`Parser.lean:94`); this is its definition, made total. -/
def natCore (acc : Nat) (start : Input) : Result Nat := (show Parser Nat from do
  if ← isEof then
    return acc
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      skip
      descend start fun it _ => natCore (10*acc + (c.val - '0'.val).toNat) it
    else
      return acc) start
termination_by remaining start

/-- The digits at the input, as a number after the digits `acc` stands for, and their count after
`digits`. Lean's `Json.Parser.natCoreNumDigits` is `partial` (`Parser.lean:106`); this is its
definition, made total. -/
def natCoreNumDigits (acc digits : Nat) (start : Input) : Result (Nat × Nat) :=
  (show Parser (Nat × Nat) from do
  if ← isEof then
    return (acc, digits)
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      skip
      descend start fun it _ => natCoreNumDigits (10*acc + (c.val - '0'.val).toNat) (digits+1) it
    else
      return (acc, digits)) start
termination_by remaining start

/-- A number whose first digit is not zero. This and the number parsers below are Lean's
(`Parser.lean:127-200`) over the total `natCore` and `natCoreNumDigits` in place of the partial
ones. -/
def natNonZero : Parser Nat := do
  Json.Parser.lookahead (fun c => '1' <= c && c <= '9') "1-9"
  natCore 0

/-- Digits and their count. -/
def natNumDigits : Parser (Nat × Nat) := do
  Json.Parser.lookahead (fun c => '0' <= c && c <= '9') "digit"
  natCoreNumDigits 0 0

/-- Digits, at least one. -/
def natMaybeZero : Parser Nat := do
  Json.Parser.lookahead (fun c => '0' <= c && c <= '9') "0-9"
  natCore 0

/-- A natural number without a leading zero. -/
def nat : Parser Nat := do
  let c ← peek!
  if c == '0' then
    skip
    return 0
  else
    natNonZero

/-- A number before its exponent: sign, integer part and decimal digits. -/
def numWithDecimals : Parser JsonNumber := do
  let sign ← Json.Parser.numSign
  let whole ← nat
  if ← isEof then
    pure <| JsonNumber.fromInt (sign * whole)
  else
    let c ← peek!
    if c == '.' then
      skip
      let (n, d) ← natNumDigits
      if d > USize.size then fail "too many decimals"
      let mantissa' := sign * (whole * (10^d : Nat) + n)
      let exponent' := d
      pure <| JsonNumber.mk mantissa' exponent'
    else
      pure <| JsonNumber.fromInt (sign * whole)

/-- The exponent of a number, applied to `value`. -/
def exponent (value : JsonNumber) : Parser JsonNumber := do
  if ← isEof then
    return value
  else
    let c ← peek!
    if c == 'e' || c == 'E' then
      skip
      let c ← peek!
      if c == '-' then
        skip
        let n ← natMaybeZero
        return value.shiftr n
      else
        if c = '+' then skip
        let n ← natMaybeZero
        if n > USize.size then fail "exp too large"
        return value.shiftl n
    else
      return value

/-- A JSON number. -/
def num : Parser JsonNumber := do
  let res : JsonNumber ← numWithDecimals
  exponent res

/-- The characters `cs`, in order. -/
def chars : List Char → Parser Unit
  | [] => pure ()
  | c :: cs => do
    let d ← any
    if d = c then chars cs else fail ""

/-- The text `s`, refused at the start position with the message Std's `skipString` gives.
`skipString` compares a slice of the input with `startsWith`; `literal` reads the characters one
by one, so the proof of `JsonRoundTrip` steps through them as it does through the rest of the
text. -/
def literal (s : String) : Parser Unit := fun it =>
  match chars s.toList it with
  | .success it' () => .success it' ()
  | .error _ _ => .error it (.other s!"expected: {s}")

/-- A JSON value other than an array or an object, and the whitespace after it: the scalar cases of
Lean's `Json.Parser.anyCore`, which is `partial` (`Parser.lean:233`), over the total parsers
above. -/
def scalar : Parser Json := do
  let c ← peek!
  if c == '\"' then
    skip
    let s ← str
    ws
    return Json.str s
  else if c == 'f' then
    literal "false"; ws
    return Json.bool false
  else if c == 't' then
    literal "true"; ws
    return Json.bool true
  else if c == 'n' then
    literal "null"; ws
    return Json.null
  else if c == '-' || ('0' <= c && c <= '9') then
    let n ← num
    ws
    return Json.num n
  else
    fail "unexpected input"

mutual
/-- One JSON value and the whitespace after it. Total by well-founded recursion on the remaining
input: every recursive call is guarded, and `array`/`object` measure one more than the `value`
they call at the same input. Lean's `Json.Parser.anyCore`, `arrayCore` and `objectCore` are
`partial` (`Lean/Data/Json/Parser.lean:233`, `:204`, `:217`, v4.34.1), so no proof unfolds them,
and `objectCore` keeps the last of two members with one name. As `objectCore` does, `object`
inserts each member into the object's tree as it reads it. -/
def value (start : Input) : Result Json := (show Parser Json from do
  let c ← peek!
  if c == '[' then
    skip; ws
    if (← peek!) == ']' then skip; ws; return .arr #[]
    return .arr (← descend start fun it _ => array #[] it)
  else if c == '{' then
    skip; ws
    if (← peek!) == '}' then skip; ws; return Json.mkObj []
    return .obj ⟨⟨← descend start fun it _ => object .leaf it⟩⟩
  else scalar) start
termination_by 2 * remaining start
decreasing_by all_goals omega

/-- The elements of an array after `values`, through its closing bracket. -/
def array (values : Array Json) (start : Input) : Result (Array Json) :=
  (show Parser (Array Json) from do
  let values := values.push (← stay start fun it _ => value it)
  let c ← any
  if c == ']' then ws; return values
  else if c == ',' then ws; descend start fun it _ => array values it
  else fail "unexpected character in array") start
termination_by 2 * remaining start + 1
decreasing_by all_goals omega

/-- The members of an object inserted into the tree `fields`, through its closing brace. A name
already in `fields` is refused. Each name is looked up in the tree and inserted into it, as
`objectCore` does, instead of being compared with every member already read and appended to a
list. -/
def object (fields : Fields) (start : Input) : Result Fields := (show Parser Fields from do
  Json.Parser.lookahead (· == '"') "object key"
  skip
  let key ← str
  if fields.contains key then fail s!"duplicate JSON field: {key}"
  ws
  Json.Parser.lookahead (· == ':') ":"
  skip; ws
  let fields := fields.insert! key (← descend start fun it _ => value it)
  let c ← any
  if c == '}' then ws; return fields
  else if c == ',' then ws; descend start fun it _ => object fields it
  else fail "unexpected character in object") start
termination_by 2 * remaining start + 1
decreasing_by all_goals omega
end

/-- Parse `text` as exactly one JSON value surrounded only by whitespace, rejecting an object
with a repeated key; an error names what failed to parse. Its stack depth grows with the nesting
of the text, not with the length of an array, an object or a string: `skipWs`, `strCore`,
`natCore`, `natCoreNumDigits`, `chars`, `array` and `object` call themselves last, which the
pinned compiler emits as a jump. -/
def parse (text : String) : Except String Json :=
  Parser.run (do ws; let j ← value; eof; return j) text

/-! ### Printing -/

/-- Append the JSON text of the character `c` inside a string to `acc`: Lean's `escapeAux`
(`Lean/Data/Json/Printer.lean:36`, v4.34.1). `Json.escape` applies it to each character only
when its private byte table (`needEscape`, `Printer.lean:65`) finds one to escape, and appends the
string as it is otherwise, which is the same text; a proof here cannot name either private
definition. -/
def escapeTo (acc : String) (c : Char) : String :=
  if c = '"' then acc ++ "\\\""
  else if c = '\\' then acc ++ "\\\\"
  else if c = '\n' then acc ++ "\\n"
  else if c = '\r' then acc ++ "\\r"
  else if 0x0020 ≤ c.val then acc.push c
  else
    let n := c.toNat
    ((((acc ++ "\\u").push (Nat.digitChar (n / 4096))).push
      (Nat.digitChar ((n % 4096) / 256))).push (Nat.digitChar ((n % 256) / 16))).push
      (Nat.digitChar (n % 16))

/-- Append the JSON text of the string `s`, in quotes, to `acc`. -/
def stringTo (acc s : String) : String :=
  (s.foldl escapeTo (acc.push '"')).push '"'

/-- The JSON text of a number: its mantissa, then `e-` and its exponent when that is positive.
Lean's `JsonNumber.toString` calls the `partial` `countDigits`
(`Lean/Data/Json/Basic.lean:39`), and for a positive exponent it writes a decimal fraction
without trailing zeros, which the parser reads as a different number when the mantissa ends in
zero (`1.5` for `⟨150, 2⟩`). The exponent form is read back as the same mantissa and exponent
(`JsonRoundTrip.num_text`). -/
def numberText (n : JsonNumber) : String :=
  if n.exponent = 0 then n.mantissa.repr else n.mantissa.repr ++ "e-" ++ n.exponent.repr

mutual
/-- Append the compact JSON text of `j` to `acc`. -/
def printTo (acc : String) (j : Json) : String :=
  match j with
  | .null => acc ++ "null"
  | .bool b => acc ++ (if b then "true" else "false")
  | .num n => acc ++ numberText n
  | .str s => stringTo acc s
  | .arr ⟨elems⟩ => (elemsTo (acc.push '[') elems).push ']'
  | .obj ⟨⟨fields⟩⟩ => (fieldsTo (acc.push '{') true fields).1.push '}'
termination_by structural j
/-- Append the texts of the elements, separated by commas, to `acc`. -/
def elemsTo (acc : String) (elems : List Json) : String :=
  match elems with
  | [] => acc
  | [j] => printTo acc j
  | j :: rest => elemsTo ((printTo acc j).push ',') rest
termination_by structural elems
/-- Append the texts of the members of `fields` in the order of the tree, each a name, a colon
and a value, to `acc`, with a comma before each unless `first` and none came before; also whether
none has come. -/
def fieldsTo (acc : String) (first : Bool) (fields : Fields) : String × Bool :=
  match fields with
  | .leaf => (acc, first)
  | .inner _ k v l r =>
    let (acc, first) := fieldsTo acc first l
    fieldsTo (printTo ((stringTo (if first then acc else acc.push ',') k).push ':') v) false r
termination_by structural fields
end

/-- The compact JSON text of `j`: no whitespace, object members in the order of their tree. It
replaces Lean's `Json.compress`, which is `partial` (`Lean/Data/Json/Printer.lean:167`,
v4.34.1), so that `JsonRoundTrip` can state what `parse` returns for the text. It follows
`Json.compress` except for a number with a positive exponent (`numberText`); that the texts are
otherwise equal is not proved. Its stack depth grows with the nesting of `j` and the height of its
object trees, not with the length of an array or a string: `elemsTo`, the string fold and the right
subtree of `fieldsTo` are calls the pinned compiler emits as jumps. -/
def compress (j : Json) : String := printTo "" j

/-! ### Exact fields -/

/-- Exact object fields: optional data is encoded explicitly as null, never silently
omitted or supplemented by an unknown field. The expected names are distinct by the type of the
third argument, which a call with a list of literals proves by `decide`: a list that gives one
name twice has no call. -/
@[regula_decision]
def exactFields (j : Json) (expected : List String) (_distinct : expected.Nodup := by decide) :
    Except String Unit := do
  let fields ← j.getObj?
  let actual := fields.toList.map (·.1)
  unless actual.length == expected.length && expected.all actual.contains do
    throw "unknown or missing JSON object fields"

/-- The value is an object, and the names of its members, in the order of its tree, are the
expected names in some order: no member is unknown and no expected member is missing. No name
occurs twice when the expected names are distinct, which `exactFields_iff` and
`Expectation.distinct` supply. -/
def ExactFields (j : Json) (expected : List String) : Prop :=
  ∃ fields, j = .obj fields ∧ (fields.toList.map (·.1)).Perm expected

/-- `exactFields` accepts exactly the objects whose member names are the expected names in some
order. The proof of distinct names is the argument of the function: without it an object with
one expected name and one unknown name has the length of a list that gives that expected name
twice. -/
theorem exactFields_iff (j : Json) (expected : List String) (distinct : expected.Nodup) :
    (exactFields j expected distinct).isOk = true ↔ ExactFields j expected := by
  cases j with
  | obj fields =>
    have unfolded : exactFields (.obj fields) expected distinct =
        if (fields.toList.map (·.1)).length == expected.length &&
            expected.all (fields.toList.map (·.1)).contains then .ok ()
        else .error "unknown or missing JSON object fields" := by
      -- `delta`, not `Json.getObj?` in the simp set, which would realize here a copy of a lemma of
      -- Lean's `Json.beq'` that `RegulaQualification.Registry` also realizes.
      simp only [exactFields]
      delta Json.getObj?
      simp only [pure, Except.pure, bind, Except.bind]
      split <;> rfl
    rw [unfolded]
    constructor
    · intro accepted
      split at accepted
      · rename_i test
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
          List.contains_iff_mem] at test
        exact ⟨fields, rfl, RegulaPolicy.Codec.perm_of_length_of_mem distinct test.1 test.2⟩
      · exact absurd accepted (by simp [Except.isOk, Except.toBool])
    · rintro ⟨other, same, names⟩
      obtain rfl : fields = other := Json.obj.inj same
      have test : ((fields.toList.map (·.1)).length == expected.length &&
          expected.all (fields.toList.map (·.1)).contains) = true := by
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem]
        exact ⟨names.length_eq, fun name member => names.mem_iff.mpr member⟩
      rw [test]
      rfl
  | _ =>
    constructor
    · intro accepted
      exact absurd accepted (by
        simp only [exactFields]
        delta Json.getObj?
        simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool])
    · rintro ⟨fields, same, _⟩
      exact absurd same (by simp)

/-- What a call of `exactFields` gives: the value, the expected names and the proof that the
names are distinct. -/
structure Expectation where
  /-- The JSON value. -/
  value : Json
  /-- The names of the members that the value must have, and no other. -/
  expected : List String
  /-- No name is expected twice. -/
  distinct : expected.Nodup

/-- `exactFields` is a sound and complete decision of `ExactFields` (`exactFields_iff`), for
each value and each list of distinct names: it accepts the object with no member for no expected
name, and it refuses `null`. The kind is about the function that gives the three fields of an
`Expectation` to `exactFields`, so a list that gives one name twice is not an input. -/
theorem checked_exactFields : Regula.ExecutableContract (@exactFields)
    (fun check : (j : Json) → (expected : List String) → expected.Nodup → Except String Unit =>
      Regula.Decides (·.isOk = true)
        (fun input : Expectation => ExactFields input.value input.expected)
        (fun input : Expectation => check input.value input.expected input.distinct)) :=
  ⟨Regula.Decides.of_iff
    (fun input => exactFields_iff input.value input.expected input.distinct)
    ⟨⟨Json.mkObj [], [], List.nodup_nil⟩, rfl⟩
    ⟨⟨.null, [], List.nodup_nil⟩, by decide⟩⟩

end Regula.Checker.PolicyCodec
