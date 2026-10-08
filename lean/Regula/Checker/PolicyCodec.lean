import Lean.Data.Json
import RegulaPolicy.Codec
import Regula.Contract
import Regula.Decision

/-! # Strict operational JSON parsing

Strict operational JSON parsing. Scalar syntax reuses Lean's parser; the container
recursion below is adapted from the Lean 4 repository's `src/Lean/Data/Json/Parser.lean` (notice as
at
`v4.34.0`), modified to reject duplicate keys before insertion and to guard each recursive
call with consumed input, which makes it total. Upstream notice, retained:

    Copyright (c) 2019 Gabriel Ebner. All rights reserved.
    Released under Apache 2.0 license as described in the file LICENSE.
    Authors: Gabriel Ebner, Marc Huisinga

The Apache 2.0 license text is `LICENSES/Apache-2.0.txt` in this repository.
The pure wire laws do not prove this text parser or external producer authenticity.

The reading of a document has two parts. `parse` is the observing pass: it turns a text into a
`Json` value with Lean's own scalar parsers, which are `partial`, so no theorem says what it
returns. `exactFields` is a pure decision about the value that the pass returned: whether it is
an object with exactly the expected members. `checked_exactFields` registers its kind, sound and
complete against `ExactFields`. -/
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

/-- Parse `text` as exactly one JSON value surrounded only by whitespace, rejecting an object
with a repeated key; an error names what failed to parse. -/
def parse (text : String) : Except String Json :=
  Parser.run (do ws; let j ← value; eof; return j) text

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
expected names in some order: no member is unknown, no expected member is missing, and no name
occurs twice. -/
def ExactFields (j : Json) (expected : List String) : Prop :=
  ∃ fields, j = .obj fields ∧ (fields.toList.map (·.1)).Perm expected

/-- A list with the length of a list of distinct names, and with each of those names, is those
names in some order. -/
private theorem perm_of_length_of_mem {expected : List String} (distinct : expected.Nodup) :
    ∀ {actual : List String}, actual.length = expected.length →
      (∀ name ∈ expected, name ∈ actual) → actual.Perm expected := by
  induction expected with
  | nil =>
    intro actual length _
    rw [List.length_nil, List.length_eq_zero_iff] at length
    rw [length]
  | cons name rest step =>
    intro actual length members
    obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
    have present : name ∈ actual := members name List.mem_cons_self
    have shorter : (actual.erase name).length = rest.length := by
      rw [List.length_erase_of_mem present, length, List.length_cons, Nat.add_sub_cancel]
    have others : ∀ other ∈ rest, other ∈ actual.erase name := fun other member =>
      (List.mem_erase_of_ne fun (same : other = name) => absent (same ▸ member)).mpr
        (members other (List.mem_cons_of_mem _ member))
    exact (List.perm_cons_erase present).trans ((step distinct shorter others).cons name)

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
      simp only [exactFields, Json.getObj?, pure, Except.pure, bind, Except.bind]
      split <;> rfl
    rw [unfolded]
    constructor
    · intro accepted
      split at accepted
      · rename_i test
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
          List.contains_iff_mem] at test
        exact ⟨fields, rfl, perm_of_length_of_mem distinct test.1 test.2⟩
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
      exact absurd accepted (by simp [exactFields, Json.getObj?, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Except.isOk, Except.toBool])
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
