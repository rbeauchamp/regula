import Lean.Data.Json
import RegulaPolicy.Codec

/-! Strict operational JSON parsing. Scalar syntax reuses Lean's parser; the container
recursion below is adapted from the Lean 4 repository's `src/Lean/Data/Json/Parser.lean` (notice as at
`v4.34.0`), modified to reject duplicate keys before insertion and to guard each recursive
call with consumed input, which makes it total. Upstream notice, retained:

    Copyright (c) 2019 Gabriel Ebner. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Gabriel Ebner, Marc Huisinga

The Apache 2.0 license text is `LICENSES/Apache-2.0.txt` in this repository.
The pure wire laws do not prove this text parser or external producer authenticity. -/
namespace Regula.Checker.PolicyCodec
open Lean Std.Internal.Parsec Std.Internal.Parsec.String

/-- Parser input: the text and the current position in it. -/
private abbrev Input := Sigma String.Pos

private abbrev Result (α : Type) := Std.Internal.Parsec.ParseResult α Input

/-- Input bytes after the current position, the measure of the container recursion below. -/
private def remaining (it : Input) : Nat :=
  it.1.utf8ByteSize - it.2.offset.byteIdx

/-- Continue with `k` only when input has been consumed since `start`. The check makes the
termination argument executable and cannot fail: each use follows a successful `skip` or
`any` after `start`, and core `Parsec` steps only advance within the same text. -/
@[inline] private def descend {α : Type} (start : Input)
    (k : (it : Input) → remaining it < remaining start → Result α) : Parser α := fun it =>
  if h : remaining it < remaining start then k it h
  else .error it (.other "JSON parser made no progress")

/-- As `descend`, where no input need have been consumed since `start` (it has not grown). -/
@[inline] private def stay {α : Type} (start : Input)
    (k : (it : Input) → remaining it ≤ remaining start → Result α) : Parser α := fun it =>
  if h : remaining it ≤ remaining start then k it h
  else .error it (.other "JSON parser made no progress")

mutual
/-- One JSON value. Total by well-founded recursion on the remaining input: every recursive
call is guarded, and `array`/`object` measure one more than the `value` they call at the
same input. -/
private def value (start : Input) : Result Json := (show Parser Json from do
  let c ← peek!
  if c == '[' then
    skip; ws
    if (← peek!) == ']' then skip; ws; return .arr #[]
    return .arr (← descend start fun it _ => array #[] it)
  else if c == '{' then
    skip; ws
    if (← peek!) == '}' then skip; ws; return Json.mkObj []
    return Json.mkObj (← descend start fun it _ => object [] it)
  else Json.Parser.anyCore) start
termination_by 2 * remaining start
decreasing_by all_goals omega

private def array (values : Array Json) (start : Input) : Result (Array Json) :=
  (show Parser (Array Json) from do
  let values := values.push (← stay start fun it _ => value it)
  let c ← any
  if c == ']' then ws; return values
  else if c == ',' then ws; descend start fun it _ => array values it
  else fail "unexpected character in array") start
termination_by 2 * remaining start + 1
decreasing_by all_goals omega

private def object (fields : List (String × Json)) (start : Input) :
    Result (List (String × Json)) := (show Parser (List (String × Json)) from do
  Json.Parser.lookahead (· == '"') "object key"
  skip
  let key ← Json.Parser.str
  if fields.any (·.1 == key) then fail s!"duplicate JSON field: {key}"
  ws
  Json.Parser.lookahead (· == ':') ":"
  skip; ws
  let fields := fields ++ [(key, ← descend start fun it _ => value it)]
  let c ← any
  if c == '}' then ws; return fields
  else if c == ',' then ws; descend start fun it _ => object fields it
  else fail "unexpected character in object") start
termination_by 2 * remaining start + 1
decreasing_by all_goals omega
end

def parse (text : String) : Except String Json :=
  Parser.run (do ws; let j ← value; eof; return j) text

/-- Exact object fields: optional data is encoded explicitly as null, never silently
omitted or supplemented by an unknown field. -/
def exactFields (j : Json) (expected : List String) : Except String Unit := do
  let fields ← j.getObj?
  let actual := fields.toList.map (·.1)
  unless actual.length == expected.length && expected.all actual.contains do
    throw "unknown or missing JSON object fields"

end Regula.Checker.PolicyCodec
