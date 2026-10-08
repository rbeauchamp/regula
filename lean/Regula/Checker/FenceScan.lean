import RegulaPolicy.Pattern
import RegulaPolicy.Identity
import Regula.Contract
import Regula.Decision

/-!
# The scanner of the documentation fences

The pure part of the documentation audit: the scanner that finds the Lean fences of a Markdown
document (`scan`) and the code blocks of a Verso source (`scanVerso`), with the protocol
violations of each. `Regula.Checker.Documentation` reads the documents and gives each text to a
scanner.

Each scanner is a machine with one state (`Scan`, `VersoScan`): `step` reads one line by the
fence protocol, `shapedStep` adds the shape rule, and `finish` reads the end of the document. No
function of this module reads a file.

The shape rule closes the difference between lines and blocks. The scanner reads lines, and a
Markdown reader reads blocks, so a block of the reader can be at a place where the scanner sees
no fence. The rule refuses each line that can open a Lean block at such a place: a line with a
fence run and the language of Lean opens a `lean` fence in the first column, outside a fence,
and a Lean fence closes with a run in the first column. In a Markdown document it also refuses
the start tag of a code element of raw HTML.

A line of the scanner ends at a line feed. A Markdown reader also ends a line at a carriage
return, so the rule refuses a carriage return before the last character of a line. A carriage
return at the end of a line is the line ending of the reader, and `clean_iff_withoutReturn`
says that a document is clean exactly when its lines without that carriage return are clean.
A Verso source has no carriage return.

`scanLines` and `scanVersoLines` are the registered decisions. `checked_scanLines` and
`checked_scanVersoLines` state that each reports no violation exactly for a document with lines
that the relation admits (`Clean`, `VersoClean`): each line is a permitted transition of the
protocol and keeps the shape rule. `fence_of_leanShaped` and `example_of_leanShaped` state that
a clean document has a returned fence for each line of Lean shape. The input of a decision is a
`Source`: a document with its lines, bound to its text (`toList_linesOf`). The audit takes a
`Scanned`: a result that is bound to its input and to the scanner. No theorem is about the body
or the byte ranges of a returned fence.

Expected-failure markers use a deliberately small diagnostic pattern language:
`|` separates alternatives and `.*` separates ordered literal substrings. This
covers resilient compiler-diagnostic assertions without importing a second
language or pretending that diagnostic text is a stable full regular language.
-/

namespace Regula.Checker.Documentation

/-- The classification a fence marker (or a Verso block's info string) gives the next Lean fence. -/
inductive MarkerKind where
  /-- `<!-- lean-fail: PATTERN -->`: the example must fail to elaborate with a diagnostic that
  matches `pattern`. -/
  | fail (pattern : String)
  /-- `<!-- lean-trusted-compiler -->`: a teaching example that may rely on the compiler. -/
  | trusted
  deriving Repr

/-- A marker the scanner has read but not yet attached to a fence. -/
structure PendingMarker where
  /-- The marker's classification. -/
  kind : MarkerKind
  /-- The marker's 1-based line number; the fence must open on the next line. -/
  line : Nat
  deriving Repr

/-- One Lean code fence found by `scan` or `scanVerso`, with its exact location. -/
structure Fence where
  /-- The scanned document: its URI and full text. -/
  document : RegulaPolicy.SourceSnapshot
  /-- The byte range of the opening fence line. -/
  opening : RegulaPolicy.ByteRange
  /-- The byte range of the body, without the newline before the closing line; empty at the
  body's start when the body has no lines. -/
  bodyRange : RegulaPolicy.ByteRange
  /-- The byte range of the closing fence line. -/
  closing : RegulaPolicy.ByteRange
  /-- The body lines joined with newlines: the source compiled verbatim. -/
  body : String
  /-- The 1-based line number of the opening fence line. -/
  line : Nat
  /-- The expected-diagnostic pattern of a negative example, when it has one. -/
  failPattern : Option String
  /-- The example is a trusted-compiler teaching example. -/
  trusted : Bool
  /-- The 1-based line of the attached Markdown marker; `none` without one and for Verso. -/
  markerLine : Option Nat
  deriving Repr, DecidableEq

/-- The outcome of scanning one document. -/
structure ScanResult where
  /-- The Lean fences found, in document order. -/
  fences : Array Fence
  /-- The protocol violations found, each as `origin:line: message`. -/
  problems : Array String
  deriving Repr

private def firstWord (value : String) : String :=
  String.ofList <| (value.toList.dropWhile Char.isWhitespace).takeWhile (!Char.isWhitespace ·)

private def fenceRun? (line : String) : Option (Char × Nat × String) := do
  let chars := line.toList.dropWhile Char.isWhitespace
  let first ← chars.head?
  guard (first == '`' || first == '~')
  let count := (chars.takeWhile (· == first)).length
  guard (count >= 3)
  return (first, count, String.ofList (chars.drop count) |>.trimAscii.toString)

private def closingFence (line : String) (character : Char) (minimum : Nat) : Bool :=
  match fenceRun? line with
  | some (found, count, rest) => found == character && count >= minimum && rest.isEmpty
  | none => false

private def exactTrustedMarker (line : String) : Bool :=
  line.trimAscii.toString == "<!-- lean-trusted-compiler -->"

private def failMarker? (line : String) : Option String := do
  let value := line.trimAscii.toString
  let markerPrefix := "<!-- lean-fail:"
  let markerSuffix := "-->"
  guard (value.startsWith markerPrefix && value.endsWith markerSuffix)
  let inner := value.drop markerPrefix.length |>.dropEnd markerSuffix.length
  return inner.trimAscii.toString

/-- Any HTML comment whose content begins with `lean` is treated as an
attempted fence marker, so a misspelled or misspaced marker (`<!--lean-fail:
X-->`, `<!-- lean-trusted -->`) fails as malformed instead of silently
demoting its fence to an ordinary positive example. -/
private def markerLike (line : String) : Bool :=
  let value := line.trimAscii.toString
  value.startsWith "<!--" &&
    (value.drop 4 |>.toString.trimAscii.toString.startsWith "lean")

/-- The characters after a fence run name Lean: their first run of letters is `lean`, without
regard to case. So `lean`, `Lean`, `lean4` and `{.lean}` name Lean, also after characters that
are not letters, and `leanSketch` and `text lean` do not. The test does not use a notion of
white space, because Markdown readers differ in the characters that they remove around the
language of a fence. -/
private def namesLean (rest : List Char) : Bool :=
  ((rest.map Char.toLower).dropWhile (!·.isAlpha)).take 4 == ['l', 'e', 'a', 'n'] &&
    (((rest.map Char.toLower).dropWhile (!·.isAlpha)).drop 4).head?.all (!·.isAlpha)

/-- The characters after a fence run give the line Lean shape: they name Lean, or they have the
character `&` or a backslash, which Markdown decodes in an info string. -/
private def shapedAfter (rest : List Char) : Bool :=
  namesLean rest || rest.contains '&' || rest.contains '\\'

/-- The line has Lean shape: at some place of the line, a run of three or more back-ticks or
tildes with `shapedAfter` characters after it. A Markdown reader can take such a line as the
opening line of a Lean block, in a quotation, in a list item or at a place where the scanner
reads a different block structure. -/
private def leanShaped (line : String) : Bool :=
  runsIn none line.toList
where
  /-- `shapedAfter` at a run of the characters. `previous` is the character before them. A run
  is read one time, at its first character: the characters of the run after the first are
  passed with no test. -/
  runsIn (previous : Option Char) : List Char → Bool
    | [] => false
    | first :: rest =>
      ((first == '`' || first == '~') && previous != some first &&
        (3 ≤ 1 + (rest.takeWhile (· == first)).length &&
          shapedAfter (rest.dropWhile (· == first)))) ||
        runsIn (some first) rest

/-- The line has a carriage return before its last character. Markdown takes a carriage return
that no line feed follows as the end of a line, and the scanner divides a text at line feeds
only. -/
private def loneReturn (line : String) : Bool :=
  line.toList.dropLast.contains '\r'

/-- The line opens a Lean fence in the first column: it starts with the fence run, and the first
word of its info string is `lean`. -/
private def leanOpening (line : String) : Bool :=
  match fenceRun? line with
  | some (character, _, info) => line.toList.head? == some character && firstWord info == "lean"
  | none => false

/-- The names of the elements of HTML that a browser shows as preformatted text or as code, in
lower case. -/
def codeElements : List (List Char) :=
  [['p', 'r', 'e'], ['c', 'o', 'd', 'e'], ['x', 'm', 'p'], ['l', 'i', 's', 't', 'i', 'n', 'g'],
    ['p', 'l', 'a', 'i', 'n', 't', 'e', 'x', 't']]

/-- The character ends the name of an element in a start tag of HTML: a character that HTML
takes as white space (a space, a tab, a line feed, a form feed, a carriage return), `>` or `/`. -/
private def endsTagName (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r' || c == '>' || c == '/'

/-- The characters after a `<` are the name of a code element, without regard to case, and then
the end of the line or a character that ends the name. -/
private def codeTagAfter (rest : List Char) : Bool :=
  codeElements.any fun name =>
    (rest.take name.length).map Char.toLower == name &&
      (rest.drop name.length).head?.all endsTagName

/-- The line has the start tag of a code element of raw HTML, at some place of the line. -/
private def rawCodeTag (line : String) : Bool :=
  tagIn line.toList
where
  /-- A `<` with the name of a code element after it, at some place of the characters. -/
  tagIn : List Char → Bool
    | [] => false
    | first :: rest => (first == '<' && codeTagAfter rest) || tagIn rest

private def unsupportedPatternChar (character : Char) : Bool :=
  #['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\'].contains character

/-- Validate one alternative of a pattern: it is not empty, each of its ordered literals is not
empty, and no literal has a character of the regular-expression syntax that is not supported. -/
def validateAlternative (alternative : String) : Except String Unit := do
  if alternative.isEmpty then throw "diagnostic pattern has an empty alternative"
  let literals := alternative.splitOn ".*"
  if literals.any (·.isEmpty) then
    throw "diagnostic pattern has an empty ordered literal"
  let stripped := "".intercalate literals
  if stripped.toList.any unsupportedPatternChar || stripped.contains "*" then
    throw "diagnostic pattern contains unsupported regular-expression syntax"

/-- Validate the intentionally restricted expected-diagnostic pattern grammar: the body of the
pattern (`RegulaPolicy.patternBody`) is not empty, and each of its alternatives is valid
(`validateAlternative`). It accepts exactly the patterns of `RegulaPolicy.PatternValid`
(`validatePattern_eq_ok_iff`). -/
def validatePattern (pattern : String) : Except String Unit := do
  let pattern := RegulaPolicy.patternBody pattern
  if pattern.isEmpty then throw "diagnostic pattern is empty"
  for alternative in pattern.splitOn "|" do
    validateAlternative alternative

/-- Match one completed effective-error message using the proved pure pattern decision.
The scanner retains its detailed grammar-refusal diagnostics before dispatch. -/
def matchesPattern (pattern output : String) : Bool :=
  RegulaPolicy.matchesPattern pattern output


/-! ## The lines of a document -/

/-- One line of a document, with its place: its 1-based number, its text without the line break,
the byte offset of its first byte, and the byte offset after the line and its line break. The
last line has no line break. -/
structure Line where
  /-- The 1-based number of the line. -/
  number : Nat
  /-- The text of the line, without the line break. -/
  text : String
  /-- The byte offset of the first byte of the line. -/
  start : Nat
  /-- The byte offset after the line and its line break: the start of the next line. -/
  next : Nat
  deriving Repr

/-- The lines of a document from the line `number` at the byte offset `offset`: each line but the
last has one byte of line break after it. The theorems read this definition. The scanner runs
`layout`, which gives the same lines (`layout_eq`). -/
def layoutFrom (number offset : Nat) : List String → List Line
  | [] => []
  | [last] => [{ number, text := last, start := offset, next := offset + last.utf8ByteSize }]
  | line :: rest =>
      { number, text := line, start := offset, next := offset + line.utf8ByteSize + 1 } ::
        layoutFrom (number + 1) (offset + line.utf8ByteSize + 1) rest

/-- `layoutFrom` as a loop. The lines that are done are in `done`, and the call of the function
in its own body is the last step of that body. Thus the compiled function keeps no stack frame
for a line, where `layoutFrom` keeps one. -/
def layoutLoop (number offset : Nat) (done : Array Line) : List String → Array Line
  | [] => done
  | [last] =>
      done.push { number, text := last, start := offset, next := offset + last.utf8ByteSize }
  | line :: rest =>
      layoutLoop (number + 1) (offset + line.utf8ByteSize + 1)
        (done.push
          { number, text := line, start := offset, next := offset + line.utf8ByteSize + 1 }) rest

/-- **The loop gives the lines of `layoutFrom`**, after the lines that it starts with. -/
theorem layoutLoop_toList (lines : List String) : ∀ (number offset : Nat) (done : Array Line),
    (layoutLoop number offset done lines).toList =
      done.toList ++ layoutFrom number offset lines := by
  induction lines with
  | nil =>
    intro number offset done
    simp [layoutLoop, layoutFrom]
  | cons line rest step =>
    intro number offset done
    cases rest with
    | nil => simp [layoutLoop, layoutFrom]
    | cons second later =>
      have loop : layoutLoop number offset done (line :: second :: later) =
          layoutLoop (number + 1) (offset + line.utf8ByteSize + 1)
            (done.push ⟨number, line, offset, offset + line.utf8ByteSize + 1⟩)
            (second :: later) := by
        rw [layoutLoop]
        intro empty
        cases empty
      have lines : layoutFrom number offset (line :: second :: later) =
          ⟨number, line, offset, offset + line.utf8ByteSize + 1⟩ ::
            layoutFrom (number + 1) (offset + line.utf8ByteSize + 1) (second :: later) := by
        rw [layoutFrom]
        intro empty
        cases empty
      rw [loop, step, lines]
      simp

/-- The lines of a document, numbered from 1, with their byte offsets from 0. -/
def layout (lines : List String) : List Line := (layoutLoop 1 0 #[] lines).toList

/-- **`layout` gives the lines of `layoutFrom`** from the first line of the document. -/
theorem layout_eq (lines : List String) : layout lines = layoutFrom 1 0 lines := by
  rw [layout, layoutLoop_toList]
  rfl

/-- The byte range of a line, without its line break. -/
def Line.range (line : Line) : RegulaPolicy.ByteRange :=
  ⟨line.start, line.start + line.text.utf8ByteSize⟩

/-! ## The scanner of a Markdown document -/

/-- A fence that is open: what the scanner keeps from the opening line to the closing line. A
state with no open fence has none of these values. -/
structure OpenFence where
  /-- The character of the opening run: a back-tick or a tilde. -/
  character : Char
  /-- The length of the opening run. A closing run has that length at least. -/
  length : Nat
  /-- The text after the opening run, trimmed: its first word is the language. -/
  info : String
  /-- The 1-based number of the opening line. -/
  line : Nat
  /-- The byte range of the opening line. -/
  opening : RegulaPolicy.ByteRange
  /-- The byte offset of the first byte after the opening line. -/
  bodyStart : Nat
  /-- The body lines read so far. -/
  body : Array String
  deriving Repr

/-- The state of the Markdown scanner between two lines. -/
structure Scan where
  /-- The Lean fences found so far, in document order. -/
  fences : Array Fence := #[]
  /-- The protocol violations found so far. -/
  problems : Array String := #[]
  /-- The open fence, when the last line read is inside one. -/
  opened : Option OpenFence := none
  /-- The marker that waits for its fence. -/
  pending : Option PendingMarker := none
  deriving Repr

/-- The class of a line outside a fence, by the tests of the scanner in their order: a
`lean-fail` marker, the trusted marker, a line that looks like a marker and is neither, a line
that opens a fence, and each other line. -/
inductive LineClass where
  /-- `<!-- lean-fail: PATTERN -->`. -/
  | fail (pattern : String)
  /-- `<!-- lean-trusted-compiler -->`. -/
  | trusted
  /-- An HTML comment whose content starts with `lean`, and that is neither marker. -/
  | malformed
  /-- A run of three or more back-ticks or tildes after the indentation, with the rest of the
  line. -/
  | opener (character : Char) (count : Nat) (info : String)
  /-- Each other line. -/
  | plain
  deriving Repr

/-- The class of a line outside a fence. A marker comes before a fence opening, and a correct
marker before a malformed one. -/
def classify (line : String) : LineClass :=
  match failMarker? line with
  | some pattern => .fail pattern
  | none =>
    if exactTrustedMarker line then .trusted
    else if markerLike line then .malformed
    else match fenceRun? line with
      | some (character, count, info) => .opener character count info
      | none => .plain

/-- The fence of a closing line: its location, its body and what its marker says. -/
def closedFence (document : RegulaPolicy.SourceSnapshot) (fence : OpenFence)
    (pending : Option PendingMarker) (line : Line) : Fence :=
  { document
    opening := fence.opening
    bodyRange := ⟨fence.bodyStart, if fence.body.isEmpty then fence.bodyStart else line.start - 1⟩
    closing := line.range
    body := "\n".intercalate fence.body.toList
    line := fence.line
    failPattern := pending.bind fun marker =>
      match marker.kind with
      | .fail pattern => some pattern
      | .trusted => none
    trusted := pending.any fun marker =>
      match marker.kind with
      | .trusted => true
      | .fail _ => false
    markerLine := pending.map (·.line) }

/-- One line inside the open fence `fence`: a closing line ends the fence, and each other line
is a body line. A Lean fence is recorded with its marker. A marker that waits at the closing
line of a fence of another language is a violation. -/
def stepInside (document : RegulaPolicy.SourceSnapshot) (origin : String) (state : Scan)
    (fence : OpenFence) (line : Line) : Scan :=
  if closingFence line.text fence.character fence.length then
    if firstWord fence.info == "lean" then
      { state with
        fences := state.fences.push (closedFence document fence state.pending line)
        opened := none, pending := none }
    else match state.pending with
      | some marker =>
        { state with
          problems := state.problems.push
            s!"{origin}:{marker.line}: marker not attached to a ```lean fence"
          opened := none, pending := none }
      | none => { state with opened := none, pending := none }
  else { state with opened := some { fence with body := fence.body.push line.text } }

/-- The violations and the marker that waits at a line outside a fence, before the class of the
line is read: a marker that is not on the line before this one is a violation, and it waits no
more. -/
def adjacent (origin : String) (state : Scan) (line : Line) :
    Array String × Option PendingMarker :=
  match state.pending with
  | some marker =>
    if line.number != marker.line + 1 then
      (state.problems.push
        s!"{origin}:{marker.line}: marker is not immediately adjacent to a ```lean fence", none)
    else (state.problems, some marker)
  | none => (state.problems, none)

/-- What a line of the class `kind` does outside a fence, with the violations `problems` and the
marker `pending` that still waits. -/
def onClass (origin : String) (state : Scan) (line : Line) :
    LineClass → Array String → Option PendingMarker → Scan
  | .fail _, problems, some _ =>
    { state with
      problems := problems.push s!"{origin}:{line.number}: multiple markers target one fence"
      pending := none }
  | .fail pattern, problems, none =>
    { state with
      problems := match validatePattern pattern with
        | .ok _ => problems
        | .error error =>
          problems.push s!"{origin}:{line.number}: invalid lean-fail pattern: {error}"
      pending := some { kind := .fail pattern, line := line.number } }
  | .trusted, problems, some _ =>
    { state with
      problems := problems.push s!"{origin}:{line.number}: multiple markers target one fence"
      pending := none }
  | .trusted, problems, none =>
    { state with problems, pending := some { kind := .trusted, line := line.number } }
  | .malformed, problems, some marker =>
    { state with
      problems := (problems.push
        s!"{origin}:{marker.line}: previous marker is not immediately adjacent to a ```lean fence"
        ).push s!"{origin}:{line.number}: malformed Lean fence marker"
      pending := none }
  | .malformed, problems, none =>
    { state with
      problems := problems.push s!"{origin}:{line.number}: malformed Lean fence marker"
      pending := none }
  | .opener character count info, problems, some marker =>
    if firstWord info != "lean" then
      { state with
        problems := problems.push
          s!"{origin}:{marker.line}: marker not attached to a ```lean fence"
        pending := none
        opened := some { character, length := count, info, line := line.number
                         opening := line.range, bodyStart := line.next, body := #[] } }
    else
      { state with
        problems, pending := some marker
        opened := some { character, length := count, info, line := line.number
                         opening := line.range, bodyStart := line.next, body := #[] } }
  | .opener character count info, problems, none =>
    { state with
      problems, pending := none
      opened := some { character, length := count, info, line := line.number
                       opening := line.range, bodyStart := line.next, body := #[] } }
  | .plain, problems, some marker =>
    { state with
      problems := problems.push
        s!"{origin}:{marker.line}: marker is not immediately adjacent to a ```lean fence"
      pending := none }
  | .plain, problems, none => { state with problems, pending := none }

/-- One line outside a fence. First a marker that waits and is not on the line before this one
is a violation (`adjacent`). Then the class of the line and the marker that still waits say
what the line does (`onClass`). -/
def stepOutside (origin : String) (state : Scan) (line : Line) : Scan :=
  onClass origin state line (classify line.text) (adjacent origin state line).1
    (adjacent origin state line).2

/-- One line of a Markdown document. -/
def step (document : RegulaPolicy.SourceSnapshot) (origin : String) (state : Scan)
    (line : Line) : Scan :=
  match state.opened with
  | some fence => stepInside document origin state fence line
  | none => stepOutside origin state line

/-- What the shape rule refuses for a line, with the fence that is open: the reason, when the
rule refuses the line. A line with a carriage return before its last character and a line with
the start tag of a code element of raw HTML are refused at each place. Outside a fence, a line
of Lean shape is refused when it does not open a Lean fence in the first column. Inside a fence,
a line of Lean shape is refused, and so is a line that closes a Lean fence and does not start
with the run. -/
def shapeRefusal (opened : Option OpenFence) (line : String) : Option String :=
  if loneReturn line then
    some "a carriage return that no line feed follows; Markdown takes it as the end of a line, \
      and the audit divides a text at line feeds"
  else if rawCodeTag line then
    some "raw HTML opens a code element (pre, code, xmp, listing or plaintext), which the \
      audit does not read; write the tag with a character reference or in prose"
  else match opened with
    | none =>
      if leanShaped line && !leanOpening line then
        some "a line with a fence run that names Lean, or that has & or a backslash after the \
          run, does not open a `lean` fence in the first column; the audit does not check a \
          Lean fence in a quotation, in a list item, after indentation or with a different \
          spelling of the language, and it reads a run in a line of text as a fence run"
      else none
    | some fence =>
      if leanShaped line then
        some "a line with a fence run that names Lean, or that has & or a backslash after the \
          run, is inside a fence; the audit does not check it"
      else if firstWord fence.info == "lean" &&
          closingFence line fence.character fence.length &&
          line.toList.head? != some fence.character then
        some "the closing line of a Lean fence does not start in the first column"
      else none

/-- One line of a Markdown document with the shape rule: the line of the fence protocol
(`step`), and one more violation when the shape rule refuses the line. -/
def shapedStep (document : RegulaPolicy.SourceSnapshot) (origin : String) (state : Scan)
    (line : Line) : Scan :=
  match shapeRefusal state.opened line.text with
  | some reason =>
    { step document origin state line with
      problems := (step document origin state line).problems.push
        s!"{origin}:{line.number}: {reason}" }
  | none => step document origin state line

/-- The end of a Markdown document: a fence that is open and a marker that waits are
violations. -/
def finish (origin : String) (state : Scan) : ScanResult :=
  let problems := match state.opened with
    | some fence => state.problems.push s!"{origin}:{fence.line}: fence opened but never closed"
    | none => state.problems
  let problems := match state.pending with
    | some marker => problems.push s!"{origin}:{marker.line}: marker left at end of file"
    | none => problems
  { fences := state.fences, problems }

/-! ## A document with its lines -/

/-- The lines of a text: the parts of the text between its line breaks. -/
def linesOf (text : String) : List String :=
  (text.split '\n').toList.map String.Slice.copy

/-- **The lines of a text are its characters, divided at each line break.** `List.splitOn` is
the function of Lean's library for lists. -/
theorem toList_linesOf (text : String) :
    (linesOf text).map String.toList = text.toList.splitOn '\n' := by
  unfold linesOf
  rw [String.toList_split_char, List.map_map]
  simp

/-- A document with its lines. The field `divided` binds the lines to the text of the document,
so no value of this type has the lines of a different text. -/
structure Source where
  /-- The document: its URI and its full text. Each fence records it. -/
  document : RegulaPolicy.SourceSnapshot
  /-- The name of the document in the text of a violation. -/
  origin : String
  /-- The lines of the document. -/
  lines : List String
  /-- The lines are the characters of the text of the document, divided at each line break. -/
  divided : lines.map String.toList = document.source.toList.splitOn '\n'

/-- The document of a text, with the lines of that text. -/
def Source.of (text origin : String) (sourceURI : Option String := none) : Source where
  document := ⟨sourceURI.getD origin, text⟩
  origin := origin
  lines := linesOf text
  divided := toList_linesOf text

/-- The scanner of a Markdown document: each line in order from the empty state, then the end of
the document. -/
@[regula_decision]
def scanLines (source : Source) : ScanResult :=
  finish source.origin
    ((layout source.lines).foldl (shapedStep source.document source.origin) {})

/-- The code-block spellings a Verso documentation source may use, with the meaning the
standard's `lean` block (`website/RegulaExample.lean`) gives each: `lean` is a positive
example, `lean +trustedCompiler` a trusted teaching example and `lean (fails := "PATTERN")` a
negative example (`some` classification); `leanSketch`, `sh`, `text` and `toml` are not Lean
(`none`). Every other spelling, including an unnamed block, is refused, so a misspelled or
extended argument fails instead of changing an example's kind: `versoBlockKind_positive`,
`versoBlockKind_trusted`, `versoBlockKind_other` and `versoBlockKind_fail` state that each
classification comes only from its canonical spelling. -/
def versoBlockKind (info : String) : Except String (Option (Option MarkerKind)) :=
  let pre := "lean (fails := \""
  let post := "\")"
  if info == "lean" then .ok (some none)
  else if info == "lean +trustedCompiler" then .ok (some (some .trusted))
  else if ["leanSketch", "sh", "text", "toml"].contains info then .ok none
  else if info.startsWith pre && info.endsWith post && info.length ≥ pre.length + post.length then
    let pattern := ((info.drop pre.length).dropEnd post.length).toString
    if pattern.contains '"' || pattern.contains '\\' then
      .error "diagnostic pattern contains a quote or backslash"
    else match validatePattern pattern with
      | .ok _ => .ok (some (some (.fail pattern)))
      | .error error => .error s!"invalid lean-fail pattern: {error}"
  else .error s!"unsupported Verso code block `{info}`"

/-- Only the exact spelling `lean` is a positive example. -/
theorem versoBlockKind_positive {info : String} (h : versoBlockKind info = .ok (some none)) :
    info = "lean" := by
  unfold versoBlockKind at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all

/-- Only the exact spelling `lean +trustedCompiler` is a trusted teaching example. -/
theorem versoBlockKind_trusted {info : String}
    (h : versoBlockKind info = .ok (some (some .trusted))) :
    info = "lean +trustedCompiler" := by
  unfold versoBlockKind at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all

/-- Only the four listed names are non-Lean blocks. -/
theorem versoBlockKind_other {info : String} (h : versoBlockKind info = .ok none) :
    info ∈ ["leanSketch", "sh", "text", "toml"] := by
  unfold versoBlockKind at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all

/-- A negative example is spelled `lean (fails := "PATTERN")` exactly, `PATTERN` is the text
between that prefix and suffix, and the scanner's grammar accepts it. -/
theorem versoBlockKind_fail {info pattern : String}
    (h : versoBlockKind info = .ok (some (some (.fail pattern)))) :
    info.startsWith "lean (fails := \"" ∧ info.endsWith "\")" ∧
      pattern = ((info.drop "lean (fails := \"".length).dropEnd "\")".length).toString ∧
      validatePattern pattern = .ok () := by
  unfold versoBlockKind at h
  dsimp only at h
  repeat' split at h
  all_goals simp_all

/-! ## The scanner of a Verso source -/

/-- A code block that is open in a Verso source. -/
structure OpenBlock where
  /-- The length of the opening run. A closing run has that length at least. -/
  length : Nat
  /-- What the info string says: `none` for a block that is not Lean, and the marker of a Lean
  example, `none` for a positive one. -/
  kind : Option (Option MarkerKind)
  /-- The 1-based number of the opening line. -/
  line : Nat
  /-- The byte range of the opening line. -/
  opening : RegulaPolicy.ByteRange
  /-- The byte offset of the first byte after the opening line. -/
  bodyStart : Nat
  /-- The body lines read so far. -/
  body : Array String
  deriving Repr

/-- The state of the Verso scanner between two lines. -/
structure VersoScan where
  /-- The Lean examples found so far, in document order. -/
  fences : Array Fence := #[]
  /-- The protocol violations found so far. -/
  problems : Array String := #[]
  /-- The open block, when the last line read is inside one. -/
  opened : Option OpenBlock := none
  deriving Repr

/-- One line of a Verso source. Inside a block, a closing line of back-ticks ends the block, and
a Lean example is recorded. Outside a block, a line that opens a fence opens a block: an info
string that `versoBlockKind` refuses, a run of tildes, and a Lean example on a line that starts
with a space are violations. This step does not refuse a Lean example on a line that starts
with a tab or with a carriage return: the shape rule does (`shapedVersoStep`). Each other line
outside a block is read past. -/
def versoStep (document : RegulaPolicy.SourceSnapshot) (origin : String) (state : VersoScan)
    (line : Line) : VersoScan :=
  match state.opened with
  | some block =>
    if closingFence line.text '`' block.length then
      match block.kind with
      | some marker =>
        { state with
          fences := state.fences.push {
            document
            opening := block.opening
            bodyRange :=
              ⟨block.bodyStart, if block.body.isEmpty then block.bodyStart else line.start - 1⟩
            closing := line.range
            body := "\n".intercalate block.body.toList
            line := block.line
            failPattern := marker.bind fun
              | .fail pattern => some pattern
              | .trusted => none
            trusted := marker.any fun
              | .trusted => true
              | .fail _ => false
            markerLine := none }
          opened := none }
      | none => { state with opened := none }
    else { state with opened := some { block with body := block.body.push line.text } }
  | none =>
    match fenceRun? line.text with
    | some (character, count, info) =>
      let (kind, problems) : Option (Option MarkerKind) × Array String :=
        match versoBlockKind info with
        | .ok kind => (kind, state.problems)
        | .error error => (none, state.problems.push s!"{origin}:{line.number}: {error}")
      let problems :=
        if character != '`' then
          problems.push s!"{origin}:{line.number}: a Verso code block opens with back-ticks"
        else problems
      let problems :=
        if kind.isSome && line.text.startsWith " " then
          problems.push s!"{origin}:{line.number}: a Lean example must open in the first column"
        else problems
      { state with
        problems
        opened := some { length := count, kind, line := line.number, opening := line.range
                         bodyStart := line.next, body := #[] } }
    | none => state

/-- What the shape rule refuses for a line of a Verso source, with the block that is open: the
reason, when the rule refuses the line. A line with a carriage return is refused: the audit
shows nothing about a carriage return in a Verso source, so it reads sources with line feeds
only. Outside a block, a line of Lean shape is refused when it does not open a `lean` block in
the first column. Inside a block, a line of Lean shape is refused, and so is a line that closes
a Lean example and does not start with the run. -/
def versoShapeRefusal (opened : Option OpenBlock) (line : String) : Option String :=
  if line.toList.contains '\r' then
    some "a carriage return; a Verso source that the audit reads has line feeds only"
  else match opened with
  | none =>
    if leanShaped line && !leanOpening line then
      some "a line with a fence run that names Lean, or that has & or a backslash after the \
        run, does not open a `lean` block in the first column; the audit does not check a \
        Lean example in a quotation, in a list item or after indentation"
    else none
  | some block =>
    if leanShaped line then
      some "a line with a fence run that names Lean, or that has & or a backslash after the \
        run, is inside a code block; the audit does not check it"
    else if block.kind.isSome && closingFence line '`' block.length &&
        line.toList.head? != some '`' then
      some "the closing line of a Lean example does not start in the first column"
    else none

/-- One line of a Verso source with the shape rule: the line of the block protocol
(`versoStep`), and one more violation when the shape rule refuses the line. -/
def shapedVersoStep (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) : VersoScan :=
  match versoShapeRefusal state.opened line.text with
  | some reason =>
    { versoStep document origin state line with
      problems := (versoStep document origin state line).problems.push
        s!"{origin}:{line.number}: {reason}" }
  | none => versoStep document origin state line

/-- The end of a Verso source: a block that is open is a violation. -/
def versoFinish (origin : String) (state : VersoScan) : ScanResult :=
  { fences := state.fences
    problems := match state.opened with
      | some block =>
        state.problems.push s!"{origin}:{block.line}: code block opened but never closed"
      | none => state.problems }

/-- The scanner of a Verso source: each line in order from the empty state, then the end of the
source. -/
@[regula_decision]
def scanVersoLines (source : Source) : ScanResult :=
  versoFinish source.origin
    ((layout source.lines).foldl (shapedVersoStep source.document source.origin) {})

/-! ## A scan with its input -/

/-- The two forms of a documentation source. -/
inductive Format where
  /-- A Markdown document. -/
  | markdown
  /-- A Verso source. -/
  | verso
  deriving Repr, DecidableEq

/-- The scanner of a form, on a document. -/
def Source.scanned (source : Source) : Format → ScanResult
  | .markdown => scanLines source
  | .verso => scanVersoLines source

/-- The result of a scan, with its input. The field `executed` binds the result to the scanner:
no value of this type has the result of a different document, or a result that the scanner of
its form did not return. The documentation audit takes its fences and its violations from a
value of this type. -/
structure Scanned where
  /-- The form of the document. -/
  format : Format
  /-- The document with its lines. -/
  source : Source
  /-- The fences and the violations. -/
  result : ScanResult
  /-- The result is what the scanner of the form returns for the document. -/
  executed : result = source.scanned format

/-- The Lean fences of a scan, in document order. -/
def Scanned.fences (scan : Scanned) : Array Fence := scan.result.fences

/-- The protocol violations of a scan. -/
def Scanned.problems (scan : Scanned) : Array String := scan.result.problems

/-- Fail-closed, balanced scanner for the documented Lean fence protocol: the scan of a Markdown
text, with the lines of that text. -/
def scan (text origin : String) (sourceURI : Option String := none) : Scanned where
  format := .markdown
  source := .of text origin sourceURI
  result := scanLines (.of text origin sourceURI)
  executed := rfl

/-- Fail-closed, balanced scanner of the code blocks of a Verso source (`versoBlockKind`): the
scan of a Verso text, with the lines of that text. The block's info string is its whole
classification. A Lean example opens in the first column and closes in the first column, by the
shape rule. -/
def scanVerso (text origin : String) (sourceURI : Option String := none) : Scanned where
  format := .verso
  source := .of text origin sourceURI
  result := scanVersoLines (.of text origin sourceURI)
  executed := rfl

/-! ## The classes of a line, as propositions

Each test of the scanner on a line is stated here as a proposition about the characters of the
line, with the theorem that the test decides it. A proposition gives the line as parts, one after
the other: whitespace, the characters of a delimiter, and the characters between two delimiters.
`Trimmed` states what a text is without the whitespace at its two ends. The propositions use
`Char.isWhitespace` of Lean. They use no function of Lean that trims a text or takes a part of
it, and no test of this module. -/

private theorem takeWhile_beq_eq_replicate (character : Char) (chars : List Char) :
    chars.takeWhile (· == character) =
      List.replicate (chars.takeWhile (· == character)).length character := by
  induction chars with
  | nil => rfl
  | cons head rest step =>
    by_cases same : head = character
    · subst same
      simp only [List.takeWhile_cons, beq_self_eq_true, ↓reduceIte, List.length_cons,
        List.replicate_succ]
      rw [← step]
    · simp [same]

private theorem of_mem_takeWhile {p : Char → Bool} {chars : List Char} {c : Char}
    (member : c ∈ chars.takeWhile p) : p c = true := by
  induction chars with
  | nil => exact nomatch member
  | cons head rest step =>
    by_cases holds : p head = true
    · simp only [List.takeWhile_cons, holds, ↓reduceIte, List.mem_cons] at member
      rcases member with rfl | inRest
      · exact holds
      · exact step inRest
    · simp [holds] at member

private theorem drop_length_takeWhile (p : Char → Bool) (chars : List Char) :
    chars.drop (chars.takeWhile p).length = chars.dropWhile p := by
  induction chars with
  | nil => rfl
  | cons head rest step =>
    by_cases holds : p head = true
    · simp [holds, step]
    · simp [holds]

private theorem dropWhile_append_of_all (p : Char → Bool) {first : List Char}
    (all : ∀ c ∈ first, p c = true) (second : List Char) :
    (first ++ second).dropWhile p = second.dropWhile p := by
  induction first with
  | nil => rfl
  | cons head rest step =>
    have holds : p head = true := all head List.mem_cons_self
    simp only [List.cons_append, List.dropWhile_cons, holds, ↓reduceIte]
    exact step fun c member => all c (List.mem_cons_of_mem _ member)

private theorem takeWhile_replicate_append (character : Char) (count : Nat) {rest : List Char}
    (other : rest.head? ≠ some character) :
    (List.replicate count character ++ rest).takeWhile (· == character) =
      List.replicate count character := by
  induction count with
  | zero =>
    cases rest with
    | nil => rfl
    | cons head tail =>
      have differs : ¬ head = character := fun same => other (by simp [same])
      simp [differs]
  | succ count step => simp [List.replicate_succ, step]

/-- `inner` is `text` without the whitespace at its two ends: `text` is whitespace, then `inner`,
then whitespace, and `inner` does not start and does not end with a whitespace character. -/
def Trimmed (text inner : List Char) : Prop :=
  ∃ lead trail : List Char, text = lead ++ inner ++ trail ∧
    (∀ c ∈ lead, c.isWhitespace = true) ∧ (∀ c ∈ trail, c.isWhitespace = true) ∧
    (∀ c, inner.head? = some c → c.isWhitespace = false) ∧
    (∀ c, inner.getLast? = some c → c.isWhitespace = false)

/-- The start of a trimmed text: the text without its leading whitespace starts with `inner`,
and whitespace follows. -/
private theorem Trimmed.dropWhile {text inner : List Char} (trimmed : Trimmed text inner) :
    ∃ trail, text.dropWhile Char.isWhitespace = inner ++ trail ∧
      (∀ c ∈ trail, c.isWhitespace = true) := by
  obtain ⟨lead, trail, rfl, leading, trailing, first, _⟩ := trimmed
  rw [List.append_assoc, dropWhile_append_of_all _ leading]
  cases inner with
  | nil =>
    have empty : trail.dropWhile Char.isWhitespace = [] := by
      have all := List.dropWhile_append_of_pos (l₂ := []) trailing
      rwa [List.append_nil] at all
    exact ⟨[], empty, fun _ member => nomatch member⟩
  | cons head tail => exact ⟨trail, by simp [first head rfl], trailing⟩

/-- **A text has one trimmed form only.** -/
theorem Trimmed.unique {text first second : List Char} (one : Trimmed text first)
    (two : Trimmed text second) : first = second := by
  obtain ⟨trailOne, startOne, endOne⟩ := one.dropWhile
  obtain ⟨trailTwo, startTwo, endTwo⟩ := two.dropWhile
  obtain ⟨_, _, _, _, _, _, lastOne⟩ := one
  obtain ⟨_, _, _, _, _, _, lastTwo⟩ := two
  have same : first ++ trailOne = second ++ trailTwo := startOne.symm.trans startTwo
  -- a form that ends with a character that is not whitespace is not longer than a second form
  -- that whitespace follows
  have shorter : ∀ {a b ta tb : List Char}, a ++ ta = b ++ tb →
      (∀ c ∈ ta, c.isWhitespace = true) →
      (∀ c, b.getLast? = some c → c.isWhitespace = false) → b.length ≤ a.length := by
    intro a b ta tb equal white solid
    rcases List.append_eq_append_iff.mp equal with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
    case inr => simp
    case inl =>
      cases final : middle.getLast? with
      | none =>
        have empty : middle = [] := List.getLast?_eq_none_iff.mp final
        simp [empty]
      | some c =>
        have isWhite := white c (List.mem_append_left _ (List.mem_of_getLast? final))
        have last : (a ++ middle).getLast? = some c := by
          rw [List.getLast?_append, final]; rfl
        exact absurd isWhite (by rw [solid c last]; exact Bool.false_ne_true)
  have lengths : first.length = second.length :=
    Nat.le_antisymm (shorter same.symm endTwo lastOne) (shorter same endOne lastTwo)
  exact (List.append_inj same lengths).1

/-- The text with no character has one trimmed form, with no character. -/
private theorem Trimmed.of_nil {inner : List Char} (trimmed : Trimmed [] inner) : inner = [] := by
  obtain ⟨lead, trail, split, _⟩ := trimmed
  have parts := List.append_eq_nil_iff.mp split.symm
  exact (List.append_eq_nil_iff.mp parts.1).2

/-- The text with no character is its own trimmed form. -/
private theorem trimmed_empty : Trimmed [] "".toList :=
  ⟨[], [], rfl, fun _ member => (nomatch member), fun _ member => (nomatch member),
    fun _ head => (nomatch head), fun _ last => (nomatch last)⟩

/-- **What Lean's trimming of a slice gives**: the characters of the slice without the
whitespace at its two ends. The proof is from the theorems of Lean's library about the two
functions that `String.Slice.trimAscii` runs. -/
private theorem trimmed_slice (s : String.Slice) :
    Trimmed s.copy.toList s.trimAscii.toString.toList := by
  have startSplit := String.Slice.takeWhile_append_dropWhile (pat := Char.isWhitespace) (s := s)
  have endSplit := String.Slice.dropEndWhile_append_takeEndWhile (pat := Char.isWhitespace)
    (s := s.dropWhile Char.isWhitespace)
  have leading : (s.takeWhile Char.isWhitespace).copy.toList.all Char.isWhitespace = true := by
    rw [← String.Slice.all_bool_eq, ← String.Slice.takeWhile_eq_self_iff,
      String.Slice.takeWhile_takeWhile]
  have trailing : ((s.dropWhile Char.isWhitespace).takeEndWhile
      Char.isWhitespace).copy.toList.all Char.isWhitespace = true := by
    rw [← String.Slice.revAll_bool_eq, ← String.Slice.takeEndWhile_eq_self_iff,
      String.Slice.takeEndWhile_takeEndWhile]
  have first : (s.dropWhile Char.isWhitespace).copy.toList.head?.any Char.isWhitespace =
      false := by
    rw [← String.Slice.startsWith_bool_eq_head?, String.Slice.startsWith_dropWhile]
  have last : ((s.dropWhile Char.isWhitespace).dropEndWhile
      Char.isWhitespace).copy.toList.getLast?.any Char.isWhitespace = false := by
    rw [← String.Slice.endsWith_bool_eq_getLast?, String.Slice.endsWith_dropEndWhile]
  show Trimmed s.copy.toList
    ((s.dropWhile Char.isWhitespace).dropEndWhile Char.isWhitespace).copy.toList
  refine ⟨_, _, ?_, List.all_eq_true.mp leading, List.all_eq_true.mp trailing, ?_, ?_⟩
  · rw [List.append_assoc, ← String.toList_append, ← String.toList_append, endSplit, startSplit]
  · intro c head
    have whole := congrArg String.toList endSplit
    rw [String.toList_append] at whole
    rw [← whole, List.head?_append, head] at first
    simpa using first
  · intro c final
    rw [final] at last
    simpa using last

/-- What Lean's trimming of a text gives: `trimmed_slice` for a text. -/
private theorem trimmed_string (text : String) :
    Trimmed text.toList text.trimAscii.toString.toList := by
  have slice := trimmed_slice text.toSlice
  rwa [String.copy_toSlice] at slice

/-- A text is the trimmed form of a text exactly when its characters are. -/
private theorem trimAscii_eq_iff (text inner : String) :
    text.trimAscii.toString = inner ↔ Trimmed text.toList inner.toList :=
  ⟨fun same => same ▸ trimmed_string text,
    fun trimmed => String.toList_inj.mp ((trimmed_string text).unique trimmed)⟩

/-- A text with a first part and a last part that do not overlap has a middle part. -/
private theorem middle_of_prefix_suffix {first last text : List Char} (starts : first <+: text)
    (ends : last <:+ text) (long : first.length + last.length ≤ text.length) :
    ∃ middle, text = first ++ middle ++ last := by
  obtain ⟨rest, rfl⟩ := starts
  obtain ⟨before, same⟩ := ends
  rcases List.append_eq_append_iff.mp same with ⟨extra, rfl, split⟩ | ⟨middle, rfl, rfl⟩
  · have empty : extra = [] := by
      have lengths := congrArg List.length split
      simp only [List.length_append] at lengths long
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst empty
    exact ⟨[], by simp [split]⟩
  · exact ⟨middle, by simp⟩

/-- The characters between a first part and a last part of a text: what the scanner takes when
it drops the first part by its length from the start and the last part by its length from the
end. -/
private theorem toList_between (text : String) {first inner last : List Char}
    (shape : text.toList = first ++ inner ++ last) :
    ((text.drop first.length).dropEnd last.length).copy.toList = inner := by
  rw [String.Slice.toList_copy_dropEnd, String.toList_copy_drop, shape, List.append_assoc,
    List.drop_left' rfl, List.length_append, Nat.add_sub_cancel, List.take_left' rfl]

/-- The line has a fence run: after its leading whitespace come exactly `count` characters
`character`, a back-tick or a tilde, with `count` three or more, and `info` is the rest of the
line without the whitespace at its two ends. -/
def FenceLine (line : String) (character : Char) (count : Nat) (info : String) : Prop :=
  ∃ indent rest : List Char,
    line.toList = indent ++ List.replicate count character ++ rest ∧
    (∀ c ∈ indent, c.isWhitespace = true) ∧
    (character = '`' ∨ character = '~') ∧ 3 ≤ count ∧
    rest.head? ≠ some character ∧
    Trimmed rest info.toList

/-- `fenceRun?` returns a run exactly for a line with that fence run. -/
private theorem fenceRun?_eq_some_iff (line : String) (character : Char) (count : Nat)
    (info : String) :
    fenceRun? line = some (character, count, info) ↔ FenceLine line character count info := by
  constructor
  · intro found
    generalize chars : line.toList.dropWhile Char.isWhitespace = trimmed
    cases trimmed with
    | nil => simp [fenceRun?, chars] at found
    | cons first others =>
      by_cases mark : first = '`' ∨ first = '~'
      · by_cases long : 3 ≤ ((first :: others).takeWhile (· == first)).length
        · have value : fenceRun? line =
              some (first, ((first :: others).takeWhile (· == first)).length,
                (String.ofList ((first :: others).drop
                  ((first :: others).takeWhile (· == first)).length)).trimAscii.toString) := by
            unfold fenceRun?
            rw [chars]
            have marked : (first == '`' || first == '~') = true := by
              rcases mark with rfl | rfl <;> decide
            simp only [List.head?_cons, Option.bind_eq_bind, Option.bind_some, guard, marked,
              ↓reduceIte, Option.pure_def, ge_iff_le, long]
          rw [value] at found
          obtain ⟨rfl, rfl, rfl⟩ : first = character ∧
              ((first :: others).takeWhile (· == first)).length = count ∧
              (String.ofList ((first :: others).drop
                ((first :: others).takeWhile (· == first)).length)).trimAscii.toString = info := by
            simpa using found
          refine ⟨line.toList.takeWhile Char.isWhitespace,
            (first :: others).dropWhile (· == first), ?_, ?_, mark, long, ?_, ?_⟩
          · rw [← takeWhile_beq_eq_replicate, List.append_assoc,
              List.takeWhile_append_dropWhile, ← chars, List.takeWhile_append_dropWhile]
          · intro c member
            exact of_mem_takeWhile member
          · intro head
            have fails := List.head?_dropWhile_not (· == first) (first :: others)
            rw [head] at fails
            simp at fails
          · rw [drop_length_takeWhile]
            have trim := trimmed_string
              (String.ofList ((first :: others).dropWhile (· == first)))
            rwa [String.toList_ofList] at trim
        · have none : fenceRun? line = none := by
            unfold fenceRun?
            rw [chars]
            have marked : (first == '`' || first == '~') = true := by
              rcases mark with rfl | rfl <;> decide
            simp only [List.head?_cons, Option.bind_eq_bind, Option.bind_some, guard, marked,
              ↓reduceIte, Option.pure_def, ge_iff_le, long]
            rfl
          rw [none] at found
          cases found
      · have none : fenceRun? line = none := by
          unfold fenceRun?
          rw [chars]
          have unmarked : (first == '`' || first == '~') = false := by
            simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            exact ⟨fun same => mark (.inl same), fun same => mark (.inr same)⟩
          simp only [List.head?_cons, Option.bind_eq_bind, Option.bind_some, guard, unmarked,
            ↓reduceIte, Bool.false_eq_true]
          rfl
        rw [none] at found
        cases found
  · rintro ⟨indent, rest, split, blanks, mark, long, other, trim⟩
    obtain rfl : info = (String.ofList rest).trimAscii.toString :=
      ((trimAscii_eq_iff _ _).mpr (by rwa [String.toList_ofList])).symm
    have solid : character.isWhitespace = false := by
      rcases mark with rfl | rfl <;> decide
    have positive : 0 < count := by omega
    have trimmed : line.toList.dropWhile Char.isWhitespace =
        List.replicate count character ++ rest := by
      rw [split, List.append_assoc, dropWhile_append_of_all _ blanks]
      obtain ⟨less, rfl⟩ : ∃ less, count = less + 1 := ⟨count - 1, by omega⟩
      simp [List.replicate_succ, solid]
    obtain ⟨less, rfl⟩ : ∃ less, count = less + 1 := ⟨count - 1, by omega⟩
    have run : (List.replicate (less + 1) character ++ rest).takeWhile (· == character) =
        List.replicate (less + 1) character := takeWhile_replicate_append character _ other
    unfold fenceRun?
    rw [trimmed]
    have head : (List.replicate (less + 1) character ++ rest).head? = some character := by
      simp [List.replicate_succ]
    have marked : (character == '`' || character == '~') = true := by
      rcases mark with rfl | rfl <;> decide
    simp only [head, Option.bind_eq_bind, Option.bind_some, guard, marked, run,
      ↓reduceIte, Option.pure_def, List.length_replicate, ge_iff_le, long, List.drop_left']

/-- The line closes a fence that a run of `minimum` characters `character` opened: it has a run
of those characters of that length or more, and nothing after the run. -/
def ClosingLine (line : String) (character : Char) (minimum : Nat) : Prop :=
  ∃ count, FenceLine line character count "" ∧ minimum ≤ count

/-- `closingFence` accepts exactly a closing line. -/
private theorem closingFence_iff (line : String) (character : Char) (minimum : Nat) :
    closingFence line character minimum = true ↔ ClosingLine line character minimum := by
  unfold closingFence ClosingLine
  cases run : fenceRun? line with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro count fence
    rw [(fenceRun?_eq_some_iff line character count "").mpr fence] at run
    cases run
  | some found =>
    obtain ⟨symbol, count, rest⟩ := found
    simp only [Bool.and_eq_true, beq_iff_eq, ge_iff_le, decide_eq_true_eq, String.isEmpty_iff]
    constructor
    · rintro ⟨⟨rfl, long⟩, rfl⟩
      exact ⟨count, (fenceRun?_eq_some_iff line symbol count "").mp run, long⟩
    · rintro ⟨other, fence, long⟩
      rw [(fenceRun?_eq_some_iff line character other "").mpr fence] at run
      obtain ⟨rfl, rfl, rfl⟩ : character = symbol ∧ other = count ∧ "" = rest := by
        simpa using run
      exact ⟨⟨rfl, long⟩, rfl⟩

/-- The line is the trusted marker: without the whitespace at its two ends it is the text
`<!-- lean-trusted-compiler -->`. -/
def TrustedMarker (line : String) : Prop :=
  Trimmed line.toList "<!-- lean-trusted-compiler -->".toList

private theorem exactTrustedMarker_iff (line : String) :
    exactTrustedMarker line = true ↔ TrustedMarker line := by
  unfold exactTrustedMarker TrustedMarker
  rw [beq_iff_eq]
  exact trimAscii_eq_iff line _

/-- The test of Lean for the end of a text accepts exactly a text with the characters of `ending`
as its last characters. -/
private theorem endsWith_iff_suffix (text ending : String) :
    text.endsWith ending = true ↔ ending.toList <:+ text.toList := by
  rw [String.endsWith_eq_endsWith_toSlice, String.Slice.endsWith_string_iff, String.copy_toSlice]

/-- The line is a `lean-fail` marker with the pattern `pattern`. Without the whitespace at its
two ends the line is the characters `<!-- lean-fail:`, then the characters `inner`, then the
characters `-->`, and `pattern` is `inner` without the whitespace at its two ends. -/
def FailMarker (line pattern : String) : Prop :=
  ∃ inner : List Char,
    Trimmed line.toList ("<!-- lean-fail:".toList ++ inner ++ "-->".toList) ∧
    Trimmed inner pattern.toList

/-- A text that starts with `<!-- lean-fail:` and ends with `-->` has those two parts with
characters between them: the two parts do not overlap, because the first part ends with a colon
and the last part has no colon. -/
private theorem failMarker_middle {text : List Char}
    (starts : "<!-- lean-fail:".toList <+: text) (ends : "-->".toList <:+ text) :
    ∃ inner, text = "<!-- lean-fail:".toList ++ inner ++ "-->".toList := by
  obtain ⟨rest, rfl⟩ := starts
  obtain ⟨before, same⟩ := ends
  rcases List.append_eq_append_iff.mp same with ⟨shared, first, last⟩ | ⟨inner, rfl, rfl⟩
  · have empty : shared = [] := by
      cases final : shared.getLast? with
      | none => exact List.getLast?_eq_none_iff.mp final
      | some c =>
        have inLast : c ∈ "-->".toList := by
          rw [last]
          exact List.mem_append_left _ (List.mem_of_getLast? final)
        have colon : "<!-- lean-fail:".toList.getLast? = some c := by
          rw [first, List.getLast?_append, final]; rfl
        obtain rfl : ':' = c := Option.some.inj ((by decide :
          "<!-- lean-fail:".toList.getLast? = some ':').symm.trans colon)
        exact absurd inLast (by decide)
    subst empty
    rw [List.append_nil] at first
    rw [List.nil_append] at last
    exact ⟨[], by rw [← last, List.append_nil]⟩
  · exact ⟨inner, by simp⟩

/-- `failMarker?` returns a pattern exactly for a `lean-fail` marker with that pattern. -/
private theorem failMarker?_eq_some_iff (line pattern : String) :
    failMarker? line = some pattern ↔ FailMarker line pattern := by
  have value := trimmed_string line
  unfold failMarker? FailMarker
  by_cases starts : line.trimAscii.toString.startsWith "<!-- lean-fail:" = true
  · by_cases ends : line.trimAscii.toString.endsWith "-->" = true
    · obtain ⟨inner, shape⟩ := failMarker_middle (String.startsWith_string_iff.mp starts)
        ((endsWith_iff_suffix _ _).mp ends)
      have between := toList_between line.trimAscii.toString shape
      rw [String.length_toList, String.length_toList] at between
      have extracted := trimmed_slice
        ((line.trimAscii.toString.drop "<!-- lean-fail:".length).dropEnd "-->".length)
      rw [between] at extracted
      simp only [Option.bind_eq_bind, guard, starts, ends, Bool.and_self, ↓reduceIte,
        Option.bind_some, Option.pure_def, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨inner, by rw [← shape]; exact value, extracted⟩
      · rintro ⟨other, whole, trimmed⟩
        have equal := shape.symm.trans (value.unique whole)
        obtain rfl : inner = other :=
          List.append_cancel_left (List.append_cancel_right equal)
        exact String.toList_inj.mp (extracted.unique trimmed)
    · simp only [Option.bind_eq_bind, guard, starts, ends, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte]
      constructor
      · exact fun found => nomatch found
      · rintro ⟨other, whole, _⟩
        exact absurd ((endsWith_iff_suffix _ _).mpr (by
          rw [value.unique whole]; exact List.suffix_append _ _)) ends
  · simp only [Option.bind_eq_bind, guard, starts, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte]
    constructor
    · exact fun found => nomatch found
    · rintro ⟨other, whole, _⟩
      exact absurd (String.startsWith_string_iff.mpr (by
        rw [value.unique whole, List.append_assoc]; exact List.prefix_append _ _)) starts

/-- A line has one pattern as a `lean-fail` marker. -/
private theorem FailMarker.unique {line first second : String} (one : FailMarker line first)
    (two : FailMarker line second) : first = second := by
  have found := (failMarker?_eq_some_iff line first).mpr one
  rw [(failMarker?_eq_some_iff line second).mpr two] at found
  exact (Option.some.inj found).symm

/-- The line looks like a marker: without the whitespace at its two ends it is the characters
`<!--` and then the characters `rest`, and `rest` without the whitespace at its two ends starts
with `lean`. -/
def MarkerLike (line : String) : Prop :=
  ∃ rest inner : List Char,
    Trimmed line.toList ("<!--".toList ++ rest) ∧ Trimmed rest inner ∧ "lean".toList <+: inner

private theorem markerLike_iff (line : String) : markerLike line = true ↔ MarkerLike line := by
  have value := trimmed_string line
  have dropped : ∀ rest, line.trimAscii.toString.toList = "<!--".toList ++ rest →
      (line.trimAscii.toString.drop 4).toString.toList = rest := by
    intro rest shape
    show (line.trimAscii.toString.drop 4).copy.toList = rest
    rw [String.toList_copy_drop, shape]
    exact List.drop_left' (by decide)
  unfold markerLike MarkerLike
  simp only [Bool.and_eq_true, String.startsWith_string_iff]
  constructor
  · rintro ⟨⟨rest, shape⟩, word⟩
    have inner := trimmed_string (line.trimAscii.toString.drop 4).toString
    rw [dropped rest shape.symm] at inner
    exact ⟨rest, _, by rw [shape]; exact value, inner, word⟩
  · rintro ⟨rest, inner, whole, trimmed, word⟩
    have shape := value.unique whole
    have own := trimmed_string (line.trimAscii.toString.drop 4).toString
    rw [dropped rest shape] at own
    exact ⟨⟨rest, shape.symm⟩, by rw [own.unique trimmed]; exact word⟩

/-- The class of a line outside a fence, as a relation: the first class of the list of
`LineClass` that the line has. -/
def LineIs (line : String) : LineClass → Prop
  | .fail pattern => FailMarker line pattern
  | .trusted => (∀ pattern, ¬ FailMarker line pattern) ∧ TrustedMarker line
  | .malformed => (∀ pattern, ¬ FailMarker line pattern) ∧ ¬ TrustedMarker line ∧ MarkerLike line
  | .opener character count info =>
      (∀ pattern, ¬ FailMarker line pattern) ∧ ¬ TrustedMarker line ∧ ¬ MarkerLike line ∧
        FenceLine line character count info
  | .plain =>
      (∀ pattern, ¬ FailMarker line pattern) ∧ ¬ TrustedMarker line ∧ ¬ MarkerLike line ∧
        ∀ character count info, ¬ FenceLine line character count info

/-- **`classify` returns the class that the line has.** -/
theorem lineIs_classify (line : String) : LineIs line (classify line) := by
  unfold classify
  cases failed : failMarker? line with
  | some pattern => exact (failMarker?_eq_some_iff line pattern).mp failed
  | none =>
    have unmarked : ∀ pattern, ¬ FailMarker line pattern := fun pattern marker => by
      rw [(failMarker?_eq_some_iff line pattern).mpr marker] at failed
      cases failed
    by_cases trusted : exactTrustedMarker line = true
    · simp only [trusted, ↓reduceIte]
      exact ⟨unmarked, (exactTrustedMarker_iff line).mp trusted⟩
    · have untrusted : ¬ TrustedMarker line := fun marker =>
        trusted ((exactTrustedMarker_iff line).mpr marker)
      by_cases like : markerLike line = true
      · simp only [trusted, like, ↓reduceIte, Bool.false_eq_true]
        exact ⟨unmarked, untrusted, (markerLike_iff line).mp like⟩
      · have unlike : ¬ MarkerLike line := fun marker => like ((markerLike_iff line).mpr marker)
        simp only [trusted, like, ↓reduceIte, Bool.false_eq_true]
        cases run : fenceRun? line with
        | some found =>
          obtain ⟨character, count, info⟩ := found
          exact ⟨unmarked, untrusted, unlike,
            (fenceRun?_eq_some_iff line character count info).mp run⟩
        | none =>
          refine ⟨unmarked, untrusted, unlike, fun character count info fence => ?_⟩
          rw [(fenceRun?_eq_some_iff line character count info).mpr fence] at run
          cases run

private theorem takeWhile_append_of_all (p : Char → Bool) {first second : List Char}
    (all : ∀ c ∈ first, p c = true) (stops : ∀ c, second.head? = some c → p c = false) :
    (first ++ second).takeWhile p = first := by
  induction first with
  | nil =>
    cases second with
    | nil => rfl
    | cons head tail => simp [stops head rfl]
  | cons head rest step =>
    have holds : p head = true := all head List.mem_cons_self
    simp only [List.cons_append, List.takeWhile_cons, holds, ↓reduceIte, List.cons.injEq,
      true_and]
    exact step fun c member => all c (List.mem_cons_of_mem _ member)

/-- The first word of the text is `word`, which is not empty: after the leading whitespace of
the text come the characters of `word`, none of them whitespace, and then the end of the text
or a whitespace character. -/
def FirstWord (text word : String) : Prop :=
  word ≠ "" ∧ ∃ indent rest : List Char,
    text.toList = indent ++ word.toList ++ rest ∧
    (∀ c ∈ indent, c.isWhitespace = true) ∧
    (∀ c ∈ word.toList, c.isWhitespace = false) ∧
    (∀ c, rest.head? = some c → c.isWhitespace = true)

/-- `firstWord` returns a word that is not empty exactly for a text with that first word. -/
private theorem firstWord_eq_iff (text : String) {word : String} (nonempty : word ≠ "") :
    firstWord text = word ↔ FirstWord text word := by
  unfold firstWord
  constructor
  · rintro rfl
    refine ⟨nonempty, text.toList.takeWhile Char.isWhitespace,
      (text.toList.dropWhile Char.isWhitespace).dropWhile (!Char.isWhitespace ·), ?_, ?_, ?_, ?_⟩
    · rw [String.toList_ofList, List.append_assoc, List.takeWhile_append_dropWhile,
        List.takeWhile_append_dropWhile]
    · exact fun c member => of_mem_takeWhile member
    · intro c member
      rw [String.toList_ofList] at member
      simpa using of_mem_takeWhile member
    · intro c head
      have fails := List.head?_dropWhile_not (!Char.isWhitespace ·)
        (text.toList.dropWhile Char.isWhitespace)
      rw [head] at fails
      simpa using fails
  · rintro ⟨-, indent, rest, split, blanks, solid, stops⟩
    have first : ∃ head tail, word.toList = head :: tail := by
      cases chars : word.toList with
      | nil => exact absurd (String.toList_inj.mp (chars.trans String.toList_empty.symm)) nonempty
      | cons head tail => exact ⟨head, tail, rfl⟩
    obtain ⟨head, tail, chars⟩ := first
    have headSolid : head.isWhitespace = false :=
      solid head (by rw [chars]; exact List.mem_cons_self)
    have trimmed : text.toList.dropWhile Char.isWhitespace = word.toList ++ rest := by
      rw [split, List.append_assoc, dropWhile_append_of_all _ blanks, chars]
      simp [headSolid]
    rw [trimmed, takeWhile_append_of_all (!Char.isWhitespace ·)
      (fun c member => by simp [solid c member]) (fun c head => by simp [stops c head]),
      String.ofList_toList]

/-- A line has one class only. -/
theorem lineIs_unique {line : String} {first second : LineClass} (one : LineIs line first)
    (two : LineIs line second) : first = second := by
  cases first <;> cases second <;> simp only [LineIs] at one two <;>
    first
      | rfl
      | exact congrArg LineClass.fail (FailMarker.unique one two)
      | exact absurd one (two.1 _)
      | exact absurd two (one.1 _)
      | exact absurd one.2 two.2.1
      | exact absurd two.2 one.2.1
      | exact absurd one.2.2 two.2.2.1
      | exact absurd two.2.2 one.2.2.1
      | exact absurd one.2.2.2 (two.2.2.2 _ _ _)
      | exact absurd two.2.2.2 (one.2.2.2 _ _ _)
      | (have run := (fenceRun?_eq_some_iff _ _ _ _).mpr one.2.2.2
         rw [(fenceRun?_eq_some_iff _ _ _ _).mpr two.2.2.2] at run
         simp only [Option.some.injEq, Prod.mk.injEq] at run
         obtain ⟨rfl, rfl, rfl⟩ := run
         rfl)

/-- The class that `classify` returns is the one class of the line. -/
theorem classify_eq_of_lineIs {line : String} {kind : LineClass} (is : LineIs line kind) :
    classify line = kind :=
  lineIs_unique (lineIs_classify line) is

/-! ## The shape of a line

The scanner reads lines, and a Markdown reader reads blocks, so the two can take a different
block structure at a line. The statements of this section are about one line alone, with no
state: a line that a Markdown reader can take as the opening line of a Lean block, a line that
opens a Lean fence in the first column, and a line with the start tag of a code element of raw
HTML. -/

/-- The characters name Lean: without regard to case, they are characters that are not letters,
then `lean`, then the end or a character that is not a letter. So the first run of letters is
`lean`. The statement has no notion of white space: a Markdown reader can remove a form feed or
a no-break space before the language of a fence, and a different reader does not. -/
def NamesLean (rest : List Char) : Prop :=
  ∃ lead tail : List Char,
    rest.map Char.toLower = lead ++ ['l', 'e', 'a', 'n'] ++ tail ∧
    (∀ c ∈ lead, c.isAlpha = false) ∧ (∀ c, tail.head? = some c → c.isAlpha = false)

private theorem namesLean_iff (rest : List Char) : namesLean rest = true ↔ NamesLean rest := by
  unfold namesLean NamesLean
  generalize rest.map Char.toLower = chars
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨starts, stops⟩
    refine ⟨chars.takeWhile (!·.isAlpha), (chars.dropWhile (!·.isAlpha)).drop 4, ?_, ?_, ?_⟩
    · rw [List.append_assoc, ← starts, List.take_append_drop, List.takeWhile_append_dropWhile]
    · intro c member
      have holds := of_mem_takeWhile member
      simpa using holds
    · intro c head
      rw [head] at stops
      simpa using stops
  · rintro ⟨lead, tail, rfl, leading, stops⟩
    have dropped : (lead ++ ['l', 'e', 'a', 'n'] ++ tail).dropWhile (!·.isAlpha) =
        ['l', 'e', 'a', 'n'] ++ tail := by
      rw [List.append_assoc, dropWhile_append_of_all _ (fun c member => by
        simp [leading c member])]
      rfl
    rw [dropped]
    refine ⟨rfl, ?_⟩
    show Option.all (fun c => !c.isAlpha) tail.head? = true
    cases head : tail.head? with
    | none => rfl
    | some c => simp [stops c head]

/-- The line has Lean shape: at some place of the line is a run of three or more back-ticks or
tildes, and the characters after the run name Lean, or they have the character `&` or a
backslash, which Markdown decodes in an info string. The run is a whole run: the character
before it and the character after it are different from its character.

A Markdown reader can take such a line as the opening line of a Lean block: in a quotation, in a
list item, or at a place where the scanner reads a different block structure. The statement is
conservative. It does not read the inline structure of Markdown, so it also holds for a line of
prose such as "See ```x``` lean examples." and "See ```x``` lean/Regula.", where the run closes
an inline span. The remedy is an inline span with fewer back-ticks, or different words. -/
def LeanShaped (line : String) : Prop :=
  ∃ (before : List Char) (character : Char) (count : Nat) (rest : List Char),
    line.toList = before ++ List.replicate count character ++ rest ∧
    (character = '`' ∨ character = '~') ∧ 3 ≤ count ∧
    before.getLast? ≠ some character ∧ rest.head? ≠ some character ∧
    (NamesLean rest ∨ '&' ∈ rest ∨ '\\' ∈ rest)

private theorem shapedAfter_iff (rest : List Char) :
    shapedAfter rest = true ↔ (NamesLean rest ∨ '&' ∈ rest ∨ '\\' ∈ rest) := by
  unfold shapedAfter
  simp only [Bool.or_eq_true, List.contains_iff_mem, namesLean_iff, or_assoc]

/-- The character before a run that starts after `before`, when `previous` is the character
before `before`. -/
private theorem getLast?_cons_or (first : Char) (before : List Char) (previous : Option Char) :
    ((first :: before).getLast?.or previous) = (before.getLast?.or (some first)) := by
  cases before with
  | nil => rfl
  | cons second others =>
    rw [List.getLast?_cons_cons]
    cases last : (second :: others).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp last) (by simp)
    | some c => rfl

private theorem runsIn_iff (chars : List Char) : ∀ previous : Option Char,
    leanShaped.runsIn previous chars = true ↔
      ∃ (before : List Char) (character : Char) (count : Nat) (rest : List Char),
        chars = before ++ List.replicate count character ++ rest ∧
        (character = '`' ∨ character = '~') ∧ 3 ≤ count ∧
        (before.getLast?.or previous) ≠ some character ∧ rest.head? ≠ some character ∧
        (NamesLean rest ∨ '&' ∈ rest ∨ '\\' ∈ rest) := by
  induction chars with
  | nil =>
    intro previous
    constructor
    · intro shaped
      cases shaped
    · rintro ⟨before, character, count, rest, split, -, long, -⟩
      have length := congrArg List.length split
      simp only [List.length_nil, List.length_append, List.length_replicate] at length
      omega
  | cons first tail step =>
    intro previous
    simp only [leanShaped.runsIn, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
      ne_eq, decide_eq_true_eq, shapedAfter_iff, step]
    constructor
    · rintro (⟨⟨mark, fresh⟩, long, after⟩ | ⟨before, character, count, rest, rfl, facts⟩)
      · refine ⟨[], first, 1 + (tail.takeWhile (· == first)).length,
          tail.dropWhile (· == first), ?_, mark, long, fresh, ?_, after⟩
        · rw [List.nil_append, Nat.add_comm, List.replicate_succ, List.cons_append,
            ← takeWhile_beq_eq_replicate, List.takeWhile_append_dropWhile]
        · intro head
          have fails := List.head?_dropWhile_not (· == first) tail
          rw [head] at fails
          simp at fails
      · obtain ⟨mark, long, fresh, other, after⟩ := facts
        exact ⟨first :: before, character, count, rest, rfl, mark, long,
          by rw [getLast?_cons_or]; exact fresh, other, after⟩
    · rintro ⟨before, character, count, rest, split, mark, long, fresh, other, after⟩
      cases before with
      | nil =>
        obtain ⟨less, rfl⟩ : ∃ less, count = less + 1 := ⟨count - 1, by omega⟩
        rw [List.nil_append, List.replicate_succ, List.cons_append] at split
        obtain ⟨rfl, rfl⟩ := List.cons.inj split
        have run : (List.replicate less first ++ rest).takeWhile (· == first) =
            List.replicate less first := takeWhile_replicate_append first less other
        have dropped : (List.replicate less first ++ rest).dropWhile (· == first) = rest := by
          rw [← drop_length_takeWhile, run, List.length_replicate, List.drop_left' (by simp)]
        refine .inl ⟨⟨mark, fresh⟩, ?_, ?_⟩
        · rw [run, List.length_replicate]
          omega
        · rw [dropped]
          exact after
      | cons head others =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj split
        exact .inr ⟨others, character, count, rest, rfl, mark, long,
          by rw [← getLast?_cons_or]; exact fresh, other, after⟩

/-- `leanShaped` accepts exactly a line of Lean shape. -/
private theorem leanShaped_iff (line : String) : leanShaped line = true ↔ LeanShaped line := by
  unfold leanShaped LeanShaped
  rw [runsIn_iff]
  simp only [Option.or_none]

/-- The line has a carriage return before its last character: a carriage return that no line
feed follows. Markdown takes it as the end of a line. -/
def LoneReturn (line : String) : Prop :=
  ∃ before after : List Char, line.toList = before ++ '\r' :: after ∧ after ≠ []

private theorem loneReturn_iff (line : String) : loneReturn line = true ↔ LoneReturn line := by
  unfold loneReturn LoneReturn
  rw [List.contains_iff_mem]
  constructor
  · intro member
    obtain ⟨before, middle, split⟩ := List.append_of_mem member
    have nonempty : line.toList ≠ [] := by
      intro empty
      rw [empty] at member
      cases member
    refine ⟨before, middle ++ [line.toList.getLast nonempty], ?_, by simp⟩
    rw [← List.cons_append, ← List.append_assoc, ← split, List.dropLast_concat_getLast]
  · rintro ⟨before, after, split, nonempty⟩
    rw [split, List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil nonempty]
    simp

/-- The line opens a Lean fence in the first column: it starts with a fence run, and the first
word of its info string is `lean`. -/
def LeanOpening (line : String) : Prop :=
  ∃ (character : Char) (count : Nat) (info : String),
    FenceLine line character count info ∧ line.toList.head? = some character ∧
    FirstWord info "lean"

private theorem leanOpening_iff (line : String) : leanOpening line = true ↔ LeanOpening line := by
  unfold leanOpening LeanOpening
  cases run : fenceRun? line with
  | none =>
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro character count info fence
    rw [(fenceRun?_eq_some_iff line character count info).mpr fence] at run
    cases run
  | some found =>
    obtain ⟨symbol, length, text⟩ := found
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [firstWord_eq_iff text (by decide)]
    constructor
    · rintro ⟨head, word⟩
      exact ⟨symbol, length, text, (fenceRun?_eq_some_iff line symbol length text).mp run, head,
        word⟩
    · rintro ⟨character, count, info, fence, head, word⟩
      rw [(fenceRun?_eq_some_iff line character count info).mpr fence] at run
      obtain ⟨rfl, rfl, rfl⟩ : character = symbol ∧ count = length ∧ info = text := by
        simpa using run
      exact ⟨head, word⟩

/-- The character ends the name of an element in a start tag of HTML: a character that HTML
takes as white space there (a space, a tab, a line feed, a form feed, a carriage return), `>` or
`/`. -/
def EndsTagName (c : Char) : Prop :=
  c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\x0c' ∨ c = '\r' ∨ c = '>' ∨ c = '/'

private theorem endsTagName_iff (c : Char) : endsTagName c = true ↔ EndsTagName c := by
  unfold endsTagName EndsTagName
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]

/-- The line has the start tag of a code element of raw HTML: at some place of the line come the
character `<`, then the name of an element of `codeElements` without regard to case, and then
the end of the line or a character that ends the name (`EndsTagName`). The statement names no
attribute. -/
def RawCodeTag (line : String) : Prop :=
  ∃ before name rest : List Char,
    line.toList = before ++ '<' :: name ++ rest ∧ name.map Char.toLower ∈ codeElements ∧
    (∀ c, rest.head? = some c → EndsTagName c)

private theorem codeTagAfter_iff (tail : List Char) :
    codeTagAfter tail = true ↔
      ∃ name rest : List Char, tail = name ++ rest ∧ name.map Char.toLower ∈ codeElements ∧
        (∀ c, rest.head? = some c → EndsTagName c) := by
  unfold codeTagAfter
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨element, listed, named, stops⟩
    refine ⟨tail.take element.length, tail.drop element.length,
      (List.take_append_drop _ _).symm, by rw [named]; exact listed, ?_⟩
    intro c head
    rw [head] at stops
    exact (endsTagName_iff c).mp stops
  · rintro ⟨name, rest, rfl, listed, stops⟩
    have length : (name.map Char.toLower).length = name.length := List.length_map _
    refine ⟨name.map Char.toLower, listed, ?_, ?_⟩
    · rw [length, List.take_left' rfl]
    · rw [length, List.drop_left' rfl]
      cases head : rest.head? with
      | none => rfl
      | some c => exact (endsTagName_iff c).mpr (stops c head)

private theorem tagIn_iff (chars : List Char) :
    rawCodeTag.tagIn chars = true ↔
      ∃ before tail, chars = before ++ '<' :: tail ∧ codeTagAfter tail = true := by
  induction chars with
  | nil =>
    constructor
    · intro found
      cases found
    · rintro ⟨before, tail, split, _⟩
      exact absurd (congrArg List.length split) (by simp)
  | cons first rest step =>
    simp only [rawCodeTag.tagIn, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, step]
    constructor
    · rintro (⟨rfl, here⟩ | ⟨before, tail, rfl, found⟩)
      · exact ⟨[], rest, rfl, here⟩
      · exact ⟨first :: before, tail, rfl, found⟩
    · rintro ⟨before, tail, split, found⟩
      cases before with
      | nil =>
        obtain ⟨rfl, rfl⟩ := List.cons.inj split
        exact .inl ⟨rfl, found⟩
      | cons head others =>
        obtain ⟨-, rfl⟩ := List.cons.inj split
        exact .inr ⟨others, tail, rfl, found⟩

/-- `rawCodeTag` accepts exactly a line with the start tag of a code element. -/
private theorem rawCodeTag_iff (line : String) : rawCodeTag line = true ↔ RawCodeTag line := by
  unfold rawCodeTag RawCodeTag
  rw [tagIn_iff]
  constructor
  · rintro ⟨before, tail, split, found⟩
    obtain ⟨name, rest, rfl, facts⟩ := (codeTagAfter_iff tail).mp found
    exact ⟨before, name, rest, by rw [split]; simp, facts⟩
  · rintro ⟨before, name, rest, split, facts⟩
    exact ⟨before, name ++ rest, by rw [split]; simp,
      (codeTagAfter_iff _).mpr ⟨name, rest, rfl, facts⟩⟩

/-! ## The protocol of a Markdown document

The protocol is stated here with no function of the scanner: a mode between two lines, the
transitions that the protocol permits, and a document that is a run of permitted transitions. -/

/-- What the protocol knows between two lines. -/
inductive Mode where
  /-- Outside a fence, with the number of the line of a marker that waits for its fence. -/
  | outside (marker : Option Nat)
  /-- Inside a fence that a run of `length` characters `character` opened. -/
  | inside (character : Char) (length : Nat)

/-- The transitions that the protocol permits for the line `line` with the number `number`.
`valid` says which patterns a `lean-fail` marker can have. Each other line is a violation: a
marker after a marker, a marker that is not on the line before its fence, a marker before a
fence of another language, a malformed marker, and a pattern that is not valid. -/
inductive Permitted (valid : String → Prop) : Mode → Nat → String → Mode → Prop
  /-- A `lean-fail` marker with a valid pattern, when no marker waits. -/
  | failMarker {number : Nat} {line pattern : String} :
      LineIs line (.fail pattern) → valid pattern →
        Permitted valid (.outside none) number line (.outside (some number))
  /-- The trusted marker, when no marker waits. -/
  | trustedMarker {number : Nat} {line : String} :
      LineIs line .trusted → Permitted valid (.outside none) number line (.outside (some number))
  /-- A line that opens a fence, when no marker waits. -/
  | opening {number : Nat} {line : String} {character : Char} {count : Nat} {info : String} :
      LineIs line (.opener character count info) →
        Permitted valid (.outside none) number line (.inside character count)
  /-- A line that opens a Lean fence on the line after the marker that waits. -/
  | marked {marker number : Nat} {line : String} {character : Char} {count : Nat}
      {info : String} :
      LineIs line (.opener character count info) → number = marker + 1 → FirstWord info "lean" →
        Permitted valid (.outside (some marker)) number line (.inside character count)
  /-- A line of no class, when no marker waits. -/
  | plain {number : Nat} {line : String} :
      LineIs line .plain → Permitted valid (.outside none) number line (.outside none)
  /-- A line that closes the open fence. -/
  | closing {number : Nat} {line : String} {character : Char} {length : Nat} :
      ClosingLine line character length →
        Permitted valid (.inside character length) number line (.outside none)
  /-- A body line of the open fence. -/
  | body {number : Nat} {line : String} {character : Char} {length : Nat} :
      ¬ ClosingLine line character length →
        Permitted valid (.inside character length) number line (.inside character length)

/-- The lines, the first of them with the number `number`, are a run of permitted transitions
from `mode` that ends outside a fence with no marker that waits. -/
inductive Follows (valid : String → Prop) : Mode → Nat → List String → Prop
  /-- The end of the document, outside a fence and with no marker that waits. -/
  | done {number : Nat} : Follows valid (.outside none) number []
  /-- A permitted line before a clean rest. -/
  | line {mode next : Mode} {number : Nat} {text : String} {rest : List String} :
      Permitted valid mode number text next → Follows valid next (number + 1) rest →
        Follows valid mode number (text :: rest)

/-! ## The scanner follows the protocol -/

/-- The mode of a state of the scanner. -/
def Scan.mode (state : Scan) : Mode :=
  match state.opened with
  | some fence => .inside fence.character fence.length
  | none => .outside (state.pending.map (·.line))

/-- No marker waits inside a fence of another language than Lean: the scanner reports such a
marker at the opening line. Each state that the scanner reaches from the empty state has this
property (`coherent_step`). -/
def Scan.Coherent (state : Scan) : Prop :=
  ∀ fence, state.opened = some fence → firstWord fence.info ≠ "lean" → state.pending = none

private theorem ne_of_size_lt {first second : Array String} (longer : first.size < second.size) :
    second ≠ first :=
  fun same => Nat.lt_irrefl _ (same ▸ longer)

/-- What `adjacent` returns: the violations and the marker of the state when the marker that
waits is on the line before this one or no marker waits, and one more violation with no marker
when the marker that waits is on a different line. -/
private theorem adjacent_cases (origin : String) (state : Scan) (line : Line) :
    (adjacent origin state line = (state.problems, state.pending) ∧
      ∀ marker, state.pending = some marker → line.number = marker.line + 1) ∨
    (∃ marker extra, state.pending = some marker ∧ line.number ≠ marker.line + 1 ∧
      adjacent origin state line = (state.problems.push extra, none)) := by
  unfold adjacent
  cases waits : state.pending with
  | none => exact .inl ⟨rfl, fun _ same => nomatch same⟩
  | some marker =>
    by_cases near : line.number = marker.line + 1
    · have close : (line.number != marker.line + 1) = false := by simpa using near
      refine .inl ⟨by simp only [close, Bool.false_eq_true, ↓reduceIte], fun other same => ?_⟩
      cases same
      exact near
    · have far : (line.number != marker.line + 1) = true := by simpa using near
      refine .inr ⟨marker,
        s!"{origin}:{marker.line}: marker is not immediately adjacent to a ```lean fence",
        rfl, near, ?_⟩
      simp only [far, ↓reduceIte]

/-- A line of a class keeps the violations that it starts from, or it makes their list
longer. -/
private theorem onClass_quiet_or_loud (origin : String) (state : Scan) (line : Line)
    (kind : LineClass) (problems : Array String) (pending : Option PendingMarker) :
    (onClass origin state line kind problems pending).problems = problems ∨
      problems.size < (onClass origin state line kind problems pending).problems.size := by
  cases kind <;> cases pending <;> simp only [onClass]
  case fail.none pattern =>
    cases validatePattern pattern with
    | ok _ => exact .inl rfl
    | error _ =>
      refine .inr ?_
      simp [Array.size_push]
  case opener.some character count info marker =>
    split
    · refine .inr ?_
      simp [Array.size_push]
    · exact .inl rfl
  all_goals first
    | exact .inl rfl
    | exact .inl trivial
    | (refine .inr ?_; simp [Array.size_push]; done)
    | (refine .inr ?_; simp [Array.size_push]; omega)

/-- A step keeps the violations, or it makes their list longer. -/
theorem step_quiet_or_loud (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) :
    (step document origin state line).problems = state.problems ∨
      state.problems.size < (step document origin state line).problems.size := by
  unfold step
  cases opened : state.opened with
  | some fence =>
    simp only [stepInside]
    repeat' split
    all_goals first
      | exact .inl rfl
      | (refine .inr ?_; simp [Array.size_push]; done)
  | none =>
    simp only [stepOutside]
    have after := onClass_quiet_or_loud origin state line (classify line.text)
      (adjacent origin state line).1 (adjacent origin state line).2
    rcases adjacent_cases origin state line with ⟨same, -⟩ | ⟨marker, extra, -, -, other⟩
    · rw [same] at after ⊢
      exact after
    · rw [other] at after ⊢
      refine .inr ?_
      rcases after with quiet | loud
      · rw [quiet]
        simp [Array.size_push]
      · exact Nat.lt_trans (by simp [Array.size_push]) loud

/-- Outside a fence, a line that keeps the violations is a permitted transition to the mode of
the next state. -/
private theorem permitted_of_quiet_outside {valid : String → Prop}
    (sound : ∀ pattern, validatePattern pattern = .ok () → valid pattern) (origin : String)
    {state : Scan} (line : Line) (opened : state.opened = none)
    (quiet : (stepOutside origin state line).problems = state.problems) :
    Permitted valid state.mode line.number line.text (stepOutside origin state line).mode := by
  have kind := lineIs_classify line.text
  unfold stepOutside at quiet ⊢
  rcases adjacent_cases origin state line with ⟨same, near⟩ | ⟨marker, extra, -, -, other⟩
  · rw [same] at quiet ⊢
    simp only at quiet ⊢
    generalize classify line.text = found at kind quiet ⊢
    cases waits : state.pending with
    | none =>
      rw [waits] at quiet
      have mode : state.mode = .outside none := by simp [Scan.mode, opened, waits]
      rw [mode]
      cases found with
      | fail pattern =>
        simp only [onClass] at quiet ⊢
        cases checked : validatePattern pattern with
        | ok value =>
          have next : ∀ problems : Array String,
              Scan.mode { state with
                problems, pending := some { kind := .fail pattern, line := line.number } } =
                .outside (some line.number) := fun _ => by simp [Scan.mode, opened]
          rw [next]
          exact .failMarker kind (sound pattern checked)
        | error message =>
          rw [checked] at quiet
          exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
      | trusted =>
        simp only [onClass]
        have next : Scan.mode { state with
            problems := state.problems,
            pending := some { kind := .trusted, line := line.number } } =
            .outside (some line.number) := by simp [Scan.mode, opened]
        rw [next]
        exact .trustedMarker kind
      | malformed =>
        simp only [onClass] at quiet
        exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
      | opener character count info =>
        simp only [onClass]
        exact .opening kind
      | plain =>
        simp only [onClass]
        have next : Scan.mode { state with problems := state.problems, pending := none } =
            .outside none := by simp [Scan.mode, opened]
        rw [next]
        exact .plain kind
    | some marker =>
      rw [waits] at quiet
      have after := near marker waits
      have mode : state.mode = .outside (some marker.line) := by simp [Scan.mode, opened, waits]
      rw [mode]
      cases found with
      | fail pattern =>
        simp only [onClass] at quiet
        exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
      | trusted =>
        simp only [onClass] at quiet
        exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
      | malformed =>
        simp only [onClass] at quiet
        exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]; omega))
      | opener character count info =>
        simp only [onClass] at quiet ⊢
        by_cases lean : firstWord info = "lean"
        · simp only [lean, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
          exact .marked kind after ((firstWord_eq_iff info (by decide)).mp lean)
        · have other : (firstWord info != "lean") = true := by simpa using lean
          simp only [other, ↓reduceIte] at quiet
          exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
      | plain =>
        simp only [onClass] at quiet
        exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
  · rw [other] at quiet
    simp only at quiet
    rcases onClass_quiet_or_loud origin state line (classify line.text)
      (state.problems.push extra) none with same | longer
    · rw [same] at quiet
      exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
    · exact absurd quiet (ne_of_size_lt (Nat.lt_trans (by simp [Array.size_push]) longer))

/-- Outside a fence, a permitted transition keeps the violations and gives its mode. -/
private theorem quiet_of_permitted_outside {valid : String → Prop}
    (complete : ∀ pattern, valid pattern → validatePattern pattern = .ok ()) (origin : String)
    {state : Scan} (line : Line) (opened : state.opened = none) {next : Mode}
    (permitted : Permitted valid state.mode line.number line.text next) :
    (stepOutside origin state line).problems = state.problems ∧
      (stepOutside origin state line).mode = next := by
  have mode : state.mode = .outside (state.pending.map (·.line)) := by simp [Scan.mode, opened]
  rw [mode] at permitted
  generalize waits : state.pending.map (·.line) = marker at permitted
  unfold stepOutside
  cases permitted with
  | failMarker is ok =>
    have empty : state.pending = none := Option.map_eq_none_iff.mp waits
    have same : adjacent origin state line = (state.problems, none) := by simp [adjacent, empty]
    rw [same, classify_eq_of_lineIs is]
    simp only [onClass, complete _ ok]
    constructor <;> first | rfl | trivial | simp [Scan.mode, opened]
  | trustedMarker is =>
    have empty : state.pending = none := Option.map_eq_none_iff.mp waits
    have same : adjacent origin state line = (state.problems, none) := by simp [adjacent, empty]
    rw [same, classify_eq_of_lineIs is]
    simp only [onClass]
    constructor <;> first | rfl | trivial | simp [Scan.mode, opened]
  | opening is =>
    have empty : state.pending = none := Option.map_eq_none_iff.mp waits
    have same : adjacent origin state line = (state.problems, none) := by simp [adjacent, empty]
    rw [same, classify_eq_of_lineIs is]
    simp only [onClass]
    constructor <;> first | rfl | trivial | simp [Scan.mode, opened]
  | plain is =>
    have empty : state.pending = none := Option.map_eq_none_iff.mp waits
    have same : adjacent origin state line = (state.problems, none) := by simp [adjacent, empty]
    rw [same, classify_eq_of_lineIs is]
    simp only [onClass]
    constructor <;> first | rfl | trivial | simp [Scan.mode, opened]
  | marked is after lean =>
    obtain ⟨waiting, found, rfl⟩ := Option.map_eq_some_iff.mp waits
    have same : adjacent origin state line = (state.problems, some waiting) := by
      simp [adjacent, found, after]
    have language := (firstWord_eq_iff _ (by decide)).mpr lean
    rw [same, classify_eq_of_lineIs is]
    simp only [onClass, language, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    constructor <;> first | rfl | trivial | simp [Scan.mode, opened]

/-- Inside a fence, a line that keeps the violations is a permitted transition to the mode of
the next state. -/
private theorem permitted_of_quiet_inside {valid : String → Prop}
    (document : RegulaPolicy.SourceSnapshot) (origin : String) {state : Scan} (fence : OpenFence)
    (line : Line) (opened : state.opened = some fence) :
    Permitted valid state.mode line.number line.text
      (stepInside document origin state fence line).mode := by
  have mode : state.mode = .inside fence.character fence.length := by simp [Scan.mode, opened]
  rw [mode]
  unfold stepInside
  by_cases closes : closingFence line.text fence.character fence.length = true
  · have closing := (closingFence_iff _ _ _).mp closes
    simp only [closes, ↓reduceIte]
    repeat' split
    all_goals exact .closing closing
  · have open' : ¬ ClosingLine line.text fence.character fence.length := fun closing =>
      closes ((closingFence_iff _ _ _).mpr closing)
    simp only [closes, Bool.false_eq_true, ↓reduceIte]
    exact .body open'

/-- Inside a fence, a permitted transition keeps the violations and gives its mode. -/
private theorem quiet_of_permitted_inside {valid : String → Prop}
    (document : RegulaPolicy.SourceSnapshot) (origin : String) {state : Scan}
    (coherent : state.Coherent) (fence : OpenFence) (line : Line)
    (opened : state.opened = some fence) {next : Mode}
    (permitted : Permitted valid state.mode line.number line.text next) :
    (stepInside document origin state fence line).problems = state.problems ∧
      (stepInside document origin state fence line).mode = next := by
  have mode : state.mode = .inside fence.character fence.length := by simp [Scan.mode, opened]
  rw [mode] at permitted
  unfold stepInside
  cases permitted with
  | closing closing =>
    have closes := (closingFence_iff _ _ _).mpr closing
    simp only [closes, ↓reduceIte]
    by_cases lean : (firstWord fence.info == "lean") = true
    · simp only [lean, ↓reduceIte]
      constructor <;> first | rfl | trivial | simp [Scan.mode, opened]
    · have empty := coherent fence opened (by simpa using lean)
      simp only [lean, Bool.false_eq_true, ↓reduceIte, empty]
      constructor <;> first | rfl | trivial | simp [Scan.mode, opened]
  | body open' =>
    have closes : closingFence line.text fence.character fence.length = false := by
      cases test : closingFence line.text fence.character fence.length with
      | false => rfl
      | true => exact absurd ((closingFence_iff _ _ _).mp test) open'
    simp only [closes, Bool.false_eq_true, ↓reduceIte]
    constructor <;> first | rfl | trivial | simp [Scan.mode, opened]

/-- A step keeps a coherent state coherent. -/
theorem coherent_step (document : RegulaPolicy.SourceSnapshot) (origin : String) {state : Scan}
    (coherent : state.Coherent) (line : Line) : (step document origin state line).Coherent := by
  unfold step
  cases opened : state.opened with
  | some fence =>
    simp only [stepInside]
    by_cases closes : closingFence line.text fence.character fence.length = true
    · simp only [closes, ↓reduceIte]
      repeat' split
      all_goals exact fun _ same => nomatch same
    · simp only [closes, Bool.false_eq_true, ↓reduceIte]
      intro other same other'
      obtain rfl : { fence with body := fence.body.push line.text } = other :=
        Option.some.inj same
      exact coherent fence opened other'
  | none =>
    simp only [stepOutside]
    cases classify line.text <;> cases (adjacent origin state line).2 <;> simp only [onClass]
    case opener.some character count info marker =>
      split
      · exact fun _ _ _ => rfl
      · rename_i lean
        intro other same other'
        obtain rfl := Option.some.inj same
        exact absurd other' (by simpa using lean)
    case opener.none => exact fun _ _ _ => rfl
    all_goals exact fun _ same => nomatch (opened ▸ same)

/-- A line that keeps the violations is a permitted transition to the mode of the next state. -/
theorem permitted_of_quiet {valid : String → Prop}
    (sound : ∀ pattern, validatePattern pattern = .ok () → valid pattern)
    (document : RegulaPolicy.SourceSnapshot) (origin : String) {state : Scan} (line : Line)
    (quiet : (step document origin state line).problems = state.problems) :
    Permitted valid state.mode line.number line.text (step document origin state line).mode := by
  unfold step at quiet ⊢
  cases opened : state.opened with
  | some fence => exact permitted_of_quiet_inside document origin fence line opened
  | none =>
    rw [opened] at quiet
    exact permitted_of_quiet_outside sound origin line opened quiet

/-- In a coherent state, a permitted transition keeps the violations and gives its mode. -/
theorem quiet_of_permitted {valid : String → Prop}
    (complete : ∀ pattern, valid pattern → validatePattern pattern = .ok ())
    (document : RegulaPolicy.SourceSnapshot) (origin : String) {state : Scan}
    (coherent : state.Coherent) (line : Line) {next : Mode}
    (permitted : Permitted valid state.mode line.number line.text next) :
    (step document origin state line).problems = state.problems ∧
      (step document origin state line).mode = next := by
  unfold step
  cases opened : state.opened with
  | some fence =>
    exact quiet_of_permitted_inside document origin coherent fence line opened permitted
  | none => exact quiet_of_permitted_outside complete origin line opened permitted

/-- The end of the document keeps the violations exactly outside a fence with no marker that
waits. -/
private theorem finish_problems_eq_iff (origin : String) (state : Scan) :
    (finish origin state).problems = state.problems ↔ state.mode = .outside none := by
  unfold finish Scan.mode
  cases state.opened <;> cases state.pending <;> simp only
  case none.none => simp
  all_goals
    refine ⟨fun same => absurd same (ne_of_size_lt ?_), fun same => nomatch same⟩
    simp [Array.size_push]
    try omega

private theorem size_le_finish (origin : String) (state : Scan) :
    state.problems.size ≤ (finish origin state).problems.size := by
  unfold finish
  cases state.opened <;> cases state.pending <;> simp [Array.size_push] <;> omega

/-- The violations of a run are no fewer than those of its first state. -/
private theorem size_le_run (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (lines : List Line) (state : Scan),
      state.problems.size ≤
        (finish origin (lines.foldl (step document origin) state)).problems.size := by
  intro lines
  induction lines with
  | nil => exact size_le_finish origin
  | cons line rest tail =>
    intro state
    refine Nat.le_trans ?_ (tail (step document origin state line))
    rcases step_quiet_or_loud document origin state line with same | longer
    · rw [same]
      exact Nat.le_refl _
    · exact Nat.le_of_lt longer

private theorem layoutFrom_cons (number offset : Nat) (text : String) (rest : List String) :
    ∃ next later, layoutFrom number offset (text :: rest) =
      { number, text, start := offset, next } :: layoutFrom (number + 1) later rest := by
  cases rest with
  | nil => exact ⟨_, 0, rfl⟩
  | cons second others => exact ⟨_, _, rfl⟩

/-- **The scanner keeps the violations of a coherent state exactly on a clean run.** The lines
from the number `number` add no violation, and the end of the document adds none, exactly when
the texts of the lines are a run of permitted transitions from the mode of the state. -/
theorem problems_eq_iff_follows {valid : String → Prop}
    (exact : ∀ pattern, valid pattern ↔ validatePattern pattern = .ok ())
    (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : Scan), state.Coherent →
      ((finish origin ((layoutFrom number offset texts).foldl (step document origin)
        state)).problems = state.problems ↔ Follows valid state.mode number texts) := by
  intro texts
  induction texts with
  | nil =>
    intro number offset state _
    rw [show layoutFrom number offset [] = [] from rfl, List.foldl_nil, finish_problems_eq_iff]
    constructor
    · intro mode
      rw [mode]
      exact .done
    · intro clean
      generalize state.mode = mode at clean
      cases clean
      rfl
  | cons text rest tail =>
    intro number offset state coherent
    obtain ⟨next, later, lines⟩ := layoutFrom_cons number offset text rest
    rw [lines, List.foldl_cons]
    generalize first : ({ number, text, start := offset, next } : Line) = line
    have numbered : line.number = number := by rw [← first]
    have worded : line.text = text := by rw [← first]
    have after := tail (number + 1) later (step document origin state line)
      (coherent_step document origin coherent line)
    constructor
    · intro same
      rcases step_quiet_or_loud document origin state line with quiet | loud
      · have permitted := permitted_of_quiet (fun pattern ok => (exact pattern).mpr ok)
          document origin line quiet
        rw [numbered, worded] at permitted
        rw [← quiet] at same
        exact .line permitted (after.mp same)
      · exact absurd same (ne_of_size_lt (Nat.lt_of_lt_of_le loud
          (size_le_run document origin _ _)))
    · intro clean
      generalize current : state.mode = mode at clean
      cases clean with
      | line permitted others =>
        rw [← current, ← numbered, ← worded] at permitted
        obtain ⟨quiet, mode⟩ := quiet_of_permitted (fun pattern ok => (exact pattern).mp ok)
          document origin coherent line permitted
        rw [← mode] at others
        rw [after.mpr others, quiet]

/-! ## The shape rule

The fence protocol above reads lines, and a Markdown reader reads blocks. Where the two read a
different block structure, a Lean block of the reader is not a fence of the scanner. The shape
rule does not make the two agree. It refuses each line that can open a Lean block at such a
place: a line of Lean shape opens a Lean fence in the first column, outside a fence, and a Lean
fence closes with a run in the first column. It also refuses the start tag of a code element of
raw HTML, at each place. -/

/-- The open fence of the state is a Lean fence. -/
def Scan.lean (state : Scan) : Bool :=
  state.opened.any fun fence => firstWord fence.info == "lean"

/-- **The shape rule for one line**, with the mode of the protocol before the line. `lean` says
that the open fence is a Lean fence. No line has the start tag of a code element of raw HTML.
Outside a fence, a line of Lean shape opens a Lean fence in the first column. Inside a fence, no
line has Lean shape, and a line that closes a Lean fence starts with the run. -/
def ShapeRule (mode : Mode) (lean : Bool) (line : String) : Prop :=
  ¬ LoneReturn line ∧ ¬ RawCodeTag line ∧
    match mode with
    | .outside _ => LeanShaped line → LeanOpening line
    | .inside character length =>
        ¬ LeanShaped line ∧
          (lean = true → ClosingLine line character length →
            line.toList.head? = some character)

/-- `shapeRefusal` refuses no line exactly when the line keeps the shape rule. -/
private theorem shapeRefusal_eq_none_iff (state : Scan) (line : String) :
    shapeRefusal state.opened line = none ↔ ShapeRule state.mode state.lean line := by
  unfold shapeRefusal ShapeRule Scan.mode Scan.lean
  by_cases lone : loneReturn line = true
  · simp [lone, (loneReturn_iff line).mp lone]
  have noLone : ¬ LoneReturn line := fun found => lone ((loneReturn_iff line).mpr found)
  simp only [lone, Bool.false_eq_true, ↓reduceIte, noLone, not_false_eq_true, true_and]
  by_cases raw : rawCodeTag line = true
  · simp [raw, (rawCodeTag_iff line).mp raw]
  · have noTag : ¬ RawCodeTag line := fun tag => raw ((rawCodeTag_iff line).mpr tag)
    simp only [raw, Bool.false_eq_true, ↓reduceIte, noTag, not_false_eq_true, true_and]
    cases state.opened with
    | none =>
      by_cases shaped : leanShaped line = true <;> by_cases opening : leanOpening line = true <;>
        simp [shaped, opening, ← leanShaped_iff, ← leanOpening_iff]
    | some fence =>
      by_cases shaped : leanShaped line = true
      · simp [shaped, ← leanShaped_iff]
      · by_cases lean : (firstWord fence.info == "lean") = true <;>
          by_cases closes : closingFence line fence.character fence.length = true <;>
          by_cases starts : line.toList.head? = some fence.character <;>
          simp [shaped, lean, closes, starts, ← leanShaped_iff, ← closingFence_iff]

/-- The open fence after a line is a Lean fence. A line that opens a fence gives a Lean fence
exactly when the first word of its info string is `lean`. A body line keeps what the fence is.
After a line that ends outside a fence there is no open fence. -/
def LeanAfter (mode : Mode) (lean : Bool) (line : String) (next : Mode) (after : Bool) : Prop :=
  match mode, next with
  | .outside _, .inside _ _ =>
      (after = true ↔
        ∃ (character : Char) (count : Nat) (info : String),
          FenceLine line character count info ∧ FirstWord info "lean")
  | .inside _ _, .inside _ _ => after = lean
  | _, .outside _ => after = false

/-- One line gives one answer to "the open fence is a Lean fence". -/
private theorem LeanAfter.unique {mode next : Mode} {lean first second : Bool} {line : String}
    (one : LeanAfter mode lean line next first) (two : LeanAfter mode lean line next second) :
    first = second := by
  cases mode <;> cases next <;> simp only [LeanAfter] at one two
  · rw [one, two]
  · exact Bool.eq_iff_iff.mpr (one.trans two.symm)
  · rw [one, two]
  · rw [one, two]

/-- The fence that a line outside a fence opens: the fence of a line that opens one, and none
for each other line. -/
private theorem stepOutside_opened (origin : String) (state : Scan) (line : Line)
    (opened : state.opened = none) :
    (stepOutside origin state line).opened =
      match classify line.text with
      | .opener character count info =>
        some { character, length := count, info, line := line.number, opening := line.range,
               bodyStart := line.next, body := #[] }
      | _ => none := by
  unfold stepOutside
  generalize classify line.text = kind
  generalize (adjacent origin state line).1 = problems
  generalize (adjacent origin state line).2 = pending
  cases kind <;> cases pending <;> simp only [onClass, opened]
  split <;> rfl

/-- **Each step of the fence protocol gives the answer of `LeanAfter`.** -/
private theorem leanAfter_step (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) :
    LeanAfter state.mode state.lean line.text (step document origin state line).mode
      (step document origin state line).lean := by
  unfold step
  cases opened : state.opened with
  | none =>
    have before : state.mode = .outside (state.pending.map (·.line)) := by
      simp [Scan.mode, opened]
    have result := stepOutside_opened origin state line opened
    have is := lineIs_classify line.text
    rw [before]
    cases kind : classify line.text with
    | opener character count info =>
      rw [kind] at result is
      have fence : FenceLine line.text character count info := is.2.2.2
      simp only [Scan.mode, Scan.lean, result, LeanAfter, Option.any_some]
      rw [beq_iff_eq, firstWord_eq_iff info (by decide)]
      constructor
      · intro word
        exact ⟨character, count, info, fence, word⟩
      · rintro ⟨symbol, length, text, other, word⟩
        have run := (fenceRun?_eq_some_iff _ _ _ _).mpr other
        rw [(fenceRun?_eq_some_iff _ _ _ _).mpr fence] at run
        obtain ⟨-, -, rfl⟩ : character = symbol ∧ count = length ∧ info = text := by
          simpa using run
        exact word
    | _ =>
      rw [kind] at result
      simp [Scan.mode, Scan.lean, result, LeanAfter]
  | some fence =>
    have before : state.mode = .inside fence.character fence.length := by
      simp [Scan.mode, opened]
    rw [before]
    simp only [stepInside]
    by_cases closes : closingFence line.text fence.character fence.length = true
    · simp only [closes, ↓reduceIte]
      repeat' split
      all_goals simp [Scan.mode, Scan.lean, LeanAfter]
    · simp [closes, Scan.mode, Scan.lean, LeanAfter, opened]

private theorem shapedStep_opened (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) :
    (shapedStep document origin state line).opened = (step document origin state line).opened ∧
      (shapedStep document origin state line).pending =
        (step document origin state line).pending ∧
      (shapedStep document origin state line).fences =
        (step document origin state line).fences := by
  unfold shapedStep
  split <;> exact ⟨rfl, rfl, rfl⟩

private theorem shapedStep_mode (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) :
    (shapedStep document origin state line).mode = (step document origin state line).mode ∧
      (shapedStep document origin state line).lean = (step document origin state line).lean := by
  obtain ⟨opened, pending, -⟩ := shapedStep_opened document origin state line
  simp [Scan.mode, Scan.lean, opened, pending]

/-- A step with the shape rule keeps the violations exactly when the step of the protocol keeps
them and the shape rule refuses nothing. -/
private theorem shapedStep_quiet_iff (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) :
    (shapedStep document origin state line).problems = state.problems ↔
      (step document origin state line).problems = state.problems ∧
        shapeRefusal state.opened line.text = none := by
  unfold shapedStep
  cases refusal : shapeRefusal state.opened line.text with
  | none => simp
  | some reason =>
    simp only [reduceCtorEq, and_false, iff_false]
    refine ne_of_size_lt ?_
    rcases step_quiet_or_loud document origin state line with same | longer
    · simp [Array.size_push, same]
    · simp only [Array.size_push]
      omega

/-- A step with the shape rule keeps the violations, or it makes their list longer. -/
private theorem shapedStep_quiet_or_loud (document : RegulaPolicy.SourceSnapshot)
    (origin : String) (state : Scan) (line : Line) :
    (shapedStep document origin state line).problems = state.problems ∨
      state.problems.size < (shapedStep document origin state line).problems.size := by
  unfold shapedStep
  cases shapeRefusal state.opened line.text with
  | none => exact step_quiet_or_loud document origin state line
  | some reason =>
    refine .inr ?_
    rcases step_quiet_or_loud document origin state line with same | longer
    · simp [Array.size_push, same]
    · simp only [Array.size_push]
      omega

private theorem size_le_shapedRun (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (lines : List Line) (state : Scan),
      state.problems.size ≤
        (finish origin (lines.foldl (shapedStep document origin) state)).problems.size := by
  intro lines
  induction lines with
  | nil => exact size_le_finish origin
  | cons line rest tail =>
    intro state
    refine Nat.le_trans ?_ (tail (shapedStep document origin state line))
    rcases shapedStep_quiet_or_loud document origin state line with same | longer
    · rw [same]
      exact Nat.le_refl _
    · exact Nat.le_of_lt longer

/-- The lines, the first of them with the number `number`, are clean: each line is a permitted
transition of the fence protocol and keeps the shape rule, and the run ends outside a fence with
no marker that waits. `lean` says that the open fence is a Lean fence. -/
inductive Clean (valid : String → Prop) : Mode → Bool → Nat → List String → Prop
  /-- The end of the document, outside a fence and with no marker that waits. -/
  | done {lean : Bool} {number : Nat} : Clean valid (.outside none) lean number []
  /-- A line that the protocol permits and that keeps the shape rule, before a clean rest. -/
  | line {mode next : Mode} {lean after : Bool} {number : Nat} {text : String}
      {rest : List String} :
      Permitted valid mode number text next → ShapeRule mode lean text →
      LeanAfter mode lean text next after → Clean valid next after (number + 1) rest →
        Clean valid mode lean number (text :: rest)

/-- **The scanner keeps the violations of a coherent state exactly on a clean run.** The lines
from the number `number` add no violation, and the end of the document adds none, exactly when
each line is a permitted transition of the protocol that keeps the shape rule. -/
theorem problems_eq_iff_clean {valid : String → Prop}
    (exact : ∀ pattern, valid pattern ↔ validatePattern pattern = .ok ())
    (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : Scan), state.Coherent →
      ((finish origin ((layoutFrom number offset texts).foldl (shapedStep document origin)
        state)).problems = state.problems ↔
          Clean valid state.mode state.lean number texts) := by
  intro texts
  induction texts with
  | nil =>
    intro number offset state _
    rw [show layoutFrom number offset [] = [] from rfl, List.foldl_nil, finish_problems_eq_iff]
    constructor
    · intro mode
      rw [mode]
      exact .done
    · intro clean
      generalize state.mode = mode at clean
      cases clean
      rfl
  | cons text rest tail =>
    intro number offset state coherent
    obtain ⟨next, later, lines⟩ := layoutFrom_cons number offset text rest
    rw [lines, List.foldl_cons]
    generalize first : ({ number, text, start := offset, next } : Line) = line
    have numbered : line.number = number := by rw [← first]
    have worded : line.text = text := by rw [← first]
    obtain ⟨sameMode, sameLean⟩ := shapedStep_mode document origin state line
    have stays : (shapedStep document origin state line).Coherent := by
      obtain ⟨opened, pending, -⟩ := shapedStep_opened document origin state line
      intro fence open' other
      rw [opened] at open'
      rw [pending]
      exact coherent_step document origin coherent line fence open' other
    have after := tail (number + 1) later (shapedStep document origin state line) stays
    rw [sameMode, sameLean] at after
    have answer := leanAfter_step document origin state line
    constructor
    · intro same
      rcases shapedStep_quiet_or_loud document origin state line with quiet | loud
      · obtain ⟨base, kept⟩ := (shapedStep_quiet_iff document origin state line).mp quiet
        have permitted := permitted_of_quiet (fun pattern ok => (exact pattern).mpr ok)
          document origin line base
        have rule := (shapeRefusal_eq_none_iff state line.text).mp kept
        rw [numbered, worded] at permitted
        rw [worded] at rule answer
        rw [← quiet] at same
        exact .line permitted rule answer (after.mp same)
      · exact absurd same (ne_of_size_lt (Nat.lt_of_lt_of_le loud
          (size_le_shapedRun document origin _ _)))
    · intro clean
      generalize current : state.mode = mode at clean
      generalize flag : state.lean = lean at clean
      cases clean with
      | line permitted rule answered others =>
        rw [← current, ← numbered, ← worded] at permitted
        rw [← current, ← flag, ← worded] at rule answered
        obtain ⟨base, mode⟩ := quiet_of_permitted (fun pattern ok => (exact pattern).mp ok)
          document origin coherent line permitted
        have kept := (shapeRefusal_eq_none_iff state line.text).mpr rule
        have quiet := (shapedStep_quiet_iff document origin state line).mpr ⟨base, kept⟩
        rw [← mode] at others answered
        rw [answer.unique answered] at after
        rw [after.mpr others, quiet]

/-! ## The lines of a Markdown reader

For a Markdown reader a line ends at a line feed, at a carriage return with a line feed after
it, and at a carriage return alone. The scanner divides a text at line feeds only. In a clean
document no line has a carriage return before its last character (`LoneReturn`), so each line
of the scanner is a line of the reader, with one carriage return after it when the line ending
has one. The theorems of this section say that each statement about a line holds for the line
with that carriage return exactly when it holds for the line without it. So a clean document is
clean line by line as a Markdown reader divides it. -/

/-- The line without its last character, when that character is a carriage return. -/
def withoutReturn (line : String) : String :=
  if line.toList.getLast? = some '\r' then String.ofList line.toList.dropLast else line

/-- A line is its form without the carriage return and then one carriage return, or it does not
end with a carriage return. -/
private theorem withoutReturn_cases (line : String) :
    line.toList = (withoutReturn line).toList ++ ['\r'] ∨
      (withoutReturn line = line ∧ line.toList.getLast? ≠ some '\r') := by
  unfold withoutReturn
  by_cases last : line.toList.getLast? = some '\r'
  · refine .inl ?_
    obtain ⟨core, split⟩ := List.getLast?_eq_some_iff.mp last
    simp only [last, ↓reduceIte, String.toList_ofList]
    rw [split, List.dropLast_concat]
  · simp only [last, ↓reduceIte]
    exact .inr ⟨trivial, last⟩

/-- The parts of a text with one more character at its end: the last part has that character
at its end, when it has a character. -/
private theorem append_singleton_split {text first last : List Char} {extra : Char}
    (split : text ++ [extra] = first ++ last) (nonempty : last ≠ []) :
    ∃ rest, last = rest ++ [extra] ∧ text = first ++ rest := by
  rcases List.eq_nil_or_concat last with empty | ⟨rest, final, rfl⟩
  · exact absurd empty nonempty
  · rw [List.concat_eq_append, ← List.append_assoc] at split
    obtain ⟨same, single⟩ := List.append_inj' split rfl
    obtain rfl : extra = final := List.head_eq_of_cons_eq single
    exact ⟨rest, List.concat_eq_append, same⟩

/-- One more whitespace character at the end of a text does not change its trimmed form. -/
private theorem trimmed_append_white {text inner : List Char} {white : Char}
    (isWhite : white.isWhitespace = true) :
    Trimmed (text ++ [white]) inner ↔ Trimmed text inner := by
  constructor
  · rintro ⟨lead, trail, split, leading, trailing, first, final⟩
    by_cases empty : trail = []
    · subst empty
      rw [List.append_nil] at split
      by_cases none : inner = []
      · subst none
        rw [List.append_nil] at split
        refine ⟨text, [], by simp, ?_, fun _ member => (nomatch member), first, final⟩
        intro c member
        exact leading c (by rw [← split]; exact List.mem_append_left _ member)
      · obtain ⟨rest, rfl, -⟩ := append_singleton_split split none
        exact absurd isWhite (by rw [final white List.getLast?_concat]; exact Bool.false_ne_true)
    · obtain ⟨rest, rfl, same⟩ := append_singleton_split split empty
      exact ⟨lead, rest, same, leading,
        fun c member => trailing c (List.mem_append_left _ member), first, final⟩
  · rintro ⟨lead, trail, rfl, leading, trailing, first, final⟩
    refine ⟨lead, trail ++ [white], by simp, leading, ?_, first, final⟩
    intro c member
    rcases List.mem_append.mp member with old | new
    · exact trailing c old
    · obtain rfl : c = white := by simpa using new
      exact isWhite

/-- A fence run of a line with a carriage return at its end is the fence run of the line
without it. -/
private theorem fenceLine_return {line core : String} (ends : line.toList = core.toList ++ ['\r'])
    (character : Char) (count : Nat) (info : String) :
    FenceLine line character count info ↔ FenceLine core character count info := by
  unfold FenceLine
  rw [ends]
  constructor
  · rintro ⟨indent, rest, split, blanks, mark, long, other, trimmed⟩
    have nonempty : rest ≠ [] := by
      rintro rfl
      rw [List.append_nil] at split
      have last := congrArg List.getLast? split
      rw [List.getLast?_concat, List.getLast?_append, List.getLast?_replicate] at last
      have positive : ¬ count = 0 := by omega
      simp only [positive, ↓reduceIte, Option.some_or] at last
      rcases mark with rfl | rfl <;> exact absurd (Option.some.inj last) (by decide)
    obtain ⟨shorter, rfl, same⟩ := append_singleton_split split nonempty
    refine ⟨indent, shorter, same, blanks, mark, long, ?_, (trimmed_append_white rfl).mp trimmed⟩
    intro head
    exact other (by rw [List.head?_append, head]; rfl)
  · rintro ⟨indent, rest, split, blanks, mark, long, other, trimmed⟩
    refine ⟨indent, rest ++ ['\r'], by rw [split]; simp, blanks, mark, long, ?_,
      (trimmed_append_white rfl).mpr trimmed⟩
    intro head
    cases rest with
    | nil =>
      rcases mark with rfl | rfl <;> exact absurd (Option.some.inj head) (by decide)
    | cons first others => exact other head

/-- The class of a line with a carriage return at its end is the class of the line without
it. -/
private theorem lineIs_return {line core : String} (ends : line.toList = core.toList ++ ['\r'])
    (kind : LineClass) : LineIs line kind ↔ LineIs core kind := by
  have fail : ∀ pattern, FailMarker line pattern ↔ FailMarker core pattern := fun pattern => by
    unfold FailMarker
    simp only [ends, trimmed_append_white (white := '\r') rfl]
  have trusted : TrustedMarker line ↔ TrustedMarker core := by
    unfold TrustedMarker
    simp only [ends, trimmed_append_white (white := '\r') rfl]
  have like : MarkerLike line ↔ MarkerLike core := by
    unfold MarkerLike
    simp only [ends, trimmed_append_white (white := '\r') rfl]
  cases kind <;>
    simp only [LineIs, fail, trusted, like, fenceLine_return ends]

/-- A line with a carriage return at its end closes a fence exactly when the line without it
closes the fence. -/
private theorem closingLine_return {line core : String}
    (ends : line.toList = core.toList ++ ['\r']) (character : Char) (minimum : Nat) :
    ClosingLine line character minimum ↔ ClosingLine core character minimum := by
  unfold ClosingLine
  simp only [fenceLine_return ends]

/-- A line with a carriage return at its end is a permitted transition exactly when the line
without it is. -/
private theorem permitted_return {valid : String → Prop} {line core : String}
    (ends : line.toList = core.toList ++ ['\r']) (mode : Mode) (number : Nat) (next : Mode) :
    Permitted valid mode number line next ↔ Permitted valid mode number core next := by
  have is := lineIs_return ends
  have closes := closingLine_return ends
  constructor
  · intro permitted
    cases permitted with
    | failMarker class' ok => exact .failMarker ((is _).mp class') ok
    | trustedMarker class' => exact .trustedMarker ((is _).mp class')
    | opening class' => exact .opening ((is _).mp class')
    | marked class' adjacent word => exact .marked ((is _).mp class') adjacent word
    | plain class' => exact .plain ((is _).mp class')
    | closing closed => exact .closing ((closes _ _).mp closed)
    | body open' => exact .body fun closed => open' ((closes _ _).mpr closed)
  · intro permitted
    cases permitted with
    | failMarker class' ok => exact .failMarker ((is _).mpr class') ok
    | trustedMarker class' => exact .trustedMarker ((is _).mpr class')
    | opening class' => exact .opening ((is _).mpr class')
    | marked class' adjacent word => exact .marked ((is _).mpr class') adjacent word
    | plain class' => exact .plain ((is _).mpr class')
    | closing closed => exact .closing ((closes _ _).mpr closed)
    | body open' => exact .body fun closed => open' ((closes _ _).mp closed)

/-- Characters with a carriage return at their end name Lean exactly when the characters
without it name Lean. -/
private theorem namesLean_return (rest : List Char) :
    NamesLean (rest ++ ['\r']) ↔ NamesLean rest := by
  unfold NamesLean
  rw [List.map_append]
  constructor
  · rintro ⟨lead, tail, split, leading, stops⟩
    have nonempty : tail ≠ [] := by
      rintro rfl
      have last := congrArg List.getLast? split
      simp at last
    obtain ⟨shorter, rfl, same⟩ := append_singleton_split split nonempty
    refine ⟨lead, shorter, same, leading, ?_⟩
    intro c head
    exact stops c (by rw [List.head?_append, head]; rfl)
  · rintro ⟨lead, tail, split, leading, stops⟩
    refine ⟨lead, tail ++ ['\r'], by rw [split]; simp, leading, ?_⟩
    intro c head
    cases tail with
    | nil =>
      obtain rfl : '\r' = c := Option.some.inj head
      decide
    | cons first others => exact stops c head

/-- A line with a carriage return at its end has Lean shape exactly when the line without it
has. -/
private theorem leanShaped_return {line core : String}
    (ends : line.toList = core.toList ++ ['\r']) : LeanShaped line ↔ LeanShaped core := by
  unfold LeanShaped
  rw [ends]
  constructor
  · rintro ⟨before, character, count, rest, split, mark, long, fresh, other, named⟩
    have nonempty : rest ≠ [] := by
      rintro rfl
      rw [List.append_nil] at split
      have last := congrArg List.getLast? split
      rw [List.getLast?_concat, List.getLast?_append, List.getLast?_replicate] at last
      have positive : ¬ count = 0 := by omega
      simp only [positive, ↓reduceIte, Option.some_or] at last
      rcases mark with rfl | rfl <;> exact absurd (Option.some.inj last) (by decide)
    obtain ⟨shorter, rfl, same⟩ := append_singleton_split split nonempty
    refine ⟨before, character, count, shorter, same, mark, long, fresh, ?_, ?_⟩
    · intro head
      exact other (by rw [List.head?_append, head]; rfl)
    · rcases named with lean | amp | slash
      · exact .inl ((namesLean_return shorter).mp lean)
      · exact .inr (.inl (by simpa using amp))
      · exact .inr (.inr (by simpa using slash))
  · rintro ⟨before, character, count, rest, split, mark, long, fresh, other, named⟩
    refine ⟨before, character, count, rest ++ ['\r'], by rw [split]; simp, mark, long, fresh,
      ?_, ?_⟩
    · intro head
      cases rest with
      | nil => rcases mark with rfl | rfl <;> exact absurd (Option.some.inj head) (by decide)
      | cons first others => exact other head
    · rcases named with lean | amp | slash
      · exact .inl ((namesLean_return rest).mpr lean)
      · exact .inr (.inl (List.mem_append_left _ amp))
      · exact .inr (.inr (List.mem_append_left _ slash))

/-- No name of a code element has a carriage return. -/
private theorem return_notMem_codeElement {name : List Char}
    (listed : name.map Char.toLower ∈ codeElements) : '\r' ∉ name := by
  intro member
  have lowered : '\r' ∈ name.map Char.toLower := List.mem_map.mpr ⟨'\r', member, rfl⟩
  revert lowered
  generalize name.map Char.toLower = element at listed
  revert element
  decide

/-- A line with a carriage return at its end has the start tag of a code element exactly when
the line without it has. -/
private theorem rawCodeTag_return {line core : String}
    (ends : line.toList = core.toList ++ ['\r']) : RawCodeTag line ↔ RawCodeTag core := by
  unfold RawCodeTag
  rw [ends]
  constructor
  · rintro ⟨before, name, rest, split, listed, stops⟩
    have nonempty : rest ≠ [] := by
      rintro rfl
      rw [List.append_nil] at split
      have last := congrArg List.getLast? split
      rw [List.getLast?_concat] at last
      have member : '\r' ∈ before ++ '<' :: name := List.mem_of_getLast? last.symm
      rcases List.mem_append.mp member with _ | tag
      · have final : (before ++ '<' :: name).getLast? = ('<' :: name).getLast? := by
          rw [List.getLast?_append]
          cases shape : ('<' :: name).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp shape) (by simp)
          | some c => rfl
        rw [final] at last
        have inTag : '\r' ∈ '<' :: name := List.mem_of_getLast? last.symm
        rcases List.mem_cons.mp inTag with bad | inName
        · exact absurd bad (by decide)
        · exact return_notMem_codeElement listed inName
      · rcases List.mem_cons.mp tag with bad | inName
        · exact absurd bad (by decide)
        · exact return_notMem_codeElement listed inName
    obtain ⟨shorter, rfl, same⟩ := append_singleton_split (text := core.toList)
      (extra := '\r') (first := before ++ '<' :: name) (last := rest)
      (by simpa using split) nonempty
    refine ⟨before, name, shorter, by simp [same], listed, ?_⟩
    intro c head
    exact stops c (by rw [List.head?_append, head]; rfl)
  · rintro ⟨before, name, rest, split, listed, stops⟩
    refine ⟨before, name, rest ++ ['\r'], by rw [split]; simp, listed, ?_⟩
    intro c head
    cases rest with
    | nil =>
      obtain rfl : '\r' = c := Option.some.inj head
      exact .inr (.inr (.inr (.inr (.inl rfl))))
    | cons first others => exact stops c head

/-- A line with a carriage return at its end has a carriage return before its last character
exactly when the line without it has a carriage return. -/
private theorem loneReturn_return {line core : String}
    (ends : line.toList = core.toList ++ ['\r']) : LoneReturn line ↔ '\r' ∈ core.toList := by
  rw [← loneReturn_iff]
  unfold loneReturn
  rw [ends, List.dropLast_concat, List.contains_iff_mem]

/-- A line with a fence run has a character. -/
private theorem ne_nil_of_fenceLine {line : String} {character : Char} {count : Nat}
    {info : String} (fence : FenceLine line character count info) : line.toList ≠ [] := by
  obtain ⟨indent, rest, split, -, -, long, -⟩ := fence
  intro empty
  have length := congrArg List.length split
  rw [empty] at length
  simp only [List.length_nil, List.length_append, List.length_replicate] at length
  omega

/-- A line with a carriage return at its end starts as the line without it, when that line has
a character. -/
private theorem head?_return {line core : String} (ends : line.toList = core.toList ++ ['\r'])
    (nonempty : core.toList ≠ []) : line.toList.head? = core.toList.head? := by
  rw [ends, List.head?_append]
  cases first : core.toList.head? with
  | none => exact absurd (List.head?_eq_none_iff.mp first) nonempty
  | some c => rfl

/-- A line with a carriage return at its end opens a Lean fence in the first column exactly when
the line without it does. -/
private theorem leanOpening_return {line core : String}
    (ends : line.toList = core.toList ++ ['\r']) : LeanOpening line ↔ LeanOpening core := by
  unfold LeanOpening
  simp only [fenceLine_return ends]
  constructor
  · rintro ⟨character, count, info, fence, head, word⟩
    exact ⟨character, count, info, fence,
      by rw [← head?_return ends (ne_nil_of_fenceLine fence)]; exact head, word⟩
  · rintro ⟨character, count, info, fence, head, word⟩
    exact ⟨character, count, info, fence,
      by rw [head?_return ends (ne_nil_of_fenceLine fence)]; exact head, word⟩

/-- A line with no carriage return before its last character and none at its end has no
carriage return. -/
private theorem return_notMem {line : String} (noLone : ¬ LoneReturn line)
    (last : line.toList.getLast? ≠ some '\r') : '\r' ∉ line.toList := by
  intro member
  obtain ⟨before, after, split⟩ := List.append_of_mem member
  by_cases empty : after = []
  · subst empty
    exact last (by rw [split, List.getLast?_concat])
  · exact noLone ⟨before, after, split, empty⟩

/-- A line with no carriage return has none before its last character. -/
private theorem not_loneReturn {line : String} (noReturn : '\r' ∉ line.toList) :
    ¬ LoneReturn line := by
  rintro ⟨before, after, split, -⟩
  exact noReturn (by rw [split]; simp)

/-- **A line is a permitted transition exactly when the line without its carriage return
is.** -/
theorem permitted_withoutReturn {valid : String → Prop} (line : String) (mode : Mode)
    (number : Nat) (next : Mode) :
    Permitted valid mode number line next ↔
      Permitted valid mode number (withoutReturn line) next := by
  rcases withoutReturn_cases line with ends | ⟨same, -⟩
  · exact permitted_return ends mode number next
  · rw [same]

/-- **A line keeps the shape rule exactly when the line without its carriage return has no
carriage return and keeps the shape rule.** -/
theorem shapeRule_withoutReturn (line : String) (mode : Mode) (lean : Bool) :
    ShapeRule mode lean line ↔
      '\r' ∉ (withoutReturn line).toList ∧ ShapeRule mode lean (withoutReturn line) := by
  rcases withoutReturn_cases line with ends | ⟨same, last⟩
  · unfold ShapeRule
    rw [loneReturn_return ends, rawCodeTag_return ends]
    cases mode with
    | outside marker =>
      simp only [leanShaped_return ends, leanOpening_return ends]
      exact ⟨fun ⟨noReturn, tag, opens⟩ => ⟨noReturn, not_loneReturn noReturn, tag, opens⟩,
        fun ⟨noReturn, _, tag, opens⟩ => ⟨noReturn, tag, opens⟩⟩
    | inside character length =>
      simp only [leanShaped_return ends, closingLine_return ends]
      have heads : ClosingLine (withoutReturn line) character length →
          line.toList.head? = (withoutReturn line).toList.head? := fun ⟨_, fence, _⟩ =>
        head?_return ends (ne_nil_of_fenceLine fence)
      constructor
      · rintro ⟨noReturn, tag, shaped, closes⟩
        exact ⟨noReturn, not_loneReturn noReturn, tag, shaped,
          fun isLean closed => by rw [← heads closed]; exact closes isLean closed⟩
      · rintro ⟨noReturn, -, tag, shaped, closes⟩
        exact ⟨noReturn, tag, shaped,
          fun isLean closed => by rw [heads closed]; exact closes isLean closed⟩
  · rw [same]
    exact ⟨fun rule => ⟨return_notMem rule.1 last, rule⟩, fun rule => rule.2⟩

/-- **The answer of `LeanAfter` for a line is its answer for the line without its carriage
return.** -/
theorem leanAfter_withoutReturn (line : String) (mode : Mode) (lean : Bool) (next : Mode)
    (after : Bool) :
    LeanAfter mode lean line next after ↔ LeanAfter mode lean (withoutReturn line) next after := by
  rcases withoutReturn_cases line with ends | ⟨same, -⟩
  · cases mode <;> cases next <;> simp only [LeanAfter, fenceLine_return ends]
  · rw [same]

/-- **A document is clean exactly when its lines, as a Markdown reader divides the text, are
clean.** The lines of the scanner end at line feeds. Without the carriage return at its end,
each of them has no carriage return, so it is a line of a Markdown reader, and those lines are
clean. -/
theorem clean_iff_withoutReturn {valid : String → Prop} :
    ∀ (lines : List String) (mode : Mode) (lean : Bool) (number : Nat),
      Clean valid mode lean number lines ↔
        (∀ line ∈ lines, '\r' ∉ (withoutReturn line).toList) ∧
          Clean valid mode lean number (lines.map withoutReturn) := by
  intro lines
  induction lines with
  | nil =>
    intro mode lean number
    exact ⟨fun clean => ⟨fun _ member => (nomatch member), clean⟩, fun clean => clean.2⟩
  | cons text rest tail =>
    intro mode lean number
    constructor
    · intro clean
      cases clean with
      | line permitted rule answered others =>
        obtain ⟨noReturn, kept⟩ := (shapeRule_withoutReturn text _ _).mp rule
        obtain ⟨noReturnRest, cleanRest⟩ := (tail _ _ _).mp others
        refine ⟨?_, .line ((permitted_withoutReturn text _ _ _).mp permitted) kept
          ((leanAfter_withoutReturn text _ _ _ _).mp answered) cleanRest⟩
        intro line member
        rcases List.mem_cons.mp member with rfl | later
        · exact noReturn
        · exact noReturnRest line later
    · rintro ⟨noReturn, clean⟩
      rw [List.map_cons] at clean
      cases clean with
      | line permitted rule answered others =>
        exact .line ((permitted_withoutReturn text _ _ _).mpr permitted)
          ((shapeRule_withoutReturn text _ _).mpr ⟨noReturn text List.mem_cons_self, rule⟩)
          ((leanAfter_withoutReturn text _ _ _ _).mpr answered)
          ((tail _ _ _).mpr ⟨fun line member => noReturn line (List.mem_cons_of_mem _ member),
            others⟩)

/-! ## The valid patterns -/

private theorem flatten_intersperse_nil (lists : List (List Char)) :
    (lists.intersperse []).flatten = lists.flatten := by
  induction lists with
  | nil => rfl
  | cons head rest step =>
    cases rest with
    | nil => rfl
    | cons second others =>
      simp only [List.intersperse_cons_cons, List.flatten_cons, List.nil_append] at step ⊢
      rw [step]

private theorem toList_intercalate_empty (literals : List String) :
    ("".intercalate literals).toList = (literals.map String.toList).flatten := by
  rw [String.toList_intercalate, String.toList_empty]
  exact flatten_intersperse_nil _

private theorem singleton_infix_iff (c : Char) (chars : List Char) :
    [c] <:+: chars ↔ c ∈ chars := by
  constructor
  · rintro ⟨before, after, rfl⟩
    simp
  · intro member
    obtain ⟨before, after, rfl⟩ := List.append_of_mem member
    exact ⟨before, after, by simp⟩

private theorem unsupportedPatternChar_iff (c : Char) :
    unsupportedPatternChar c = true ↔
      c ∈ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\'] := by
  unfold unsupportedPatternChar
  simp

/-- `validateAlternative` accepts exactly an alternative that is not empty, with literals that
are not empty and that have no character of the syntax that is not supported. -/
private theorem validateAlternative_eq_ok_iff (alternative : String) :
    validateAlternative alternative = .ok () ↔
      alternative ≠ "" ∧ ∀ literal ∈ alternative.splitOn ".*", literal ≠ "" ∧
        ∀ ch ∈ literal.toList,
          ch ∉ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\', '*'] := by
  unfold validateAlternative
  by_cases empty : alternative.isEmpty = true
  · have none : alternative = "" := String.isEmpty_iff.mp empty
    simp [none, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have some : alternative ≠ "" := fun same => empty (String.isEmpty_iff.mpr same)
    simp only [empty, Bool.false_eq_true, ↓reduceIte, some, ne_eq, not_false_eq_true, true_and]
    generalize alternative.splitOn ".*" = literals
    have bad : ((("".intercalate literals).toList.any unsupportedPatternChar ||
        ("".intercalate literals).contains "*") = true) ↔
        ∃ literal ∈ literals, ∃ ch ∈ literal.toList,
          ch ∈ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\', '*'] := by
      rw [Bool.or_eq_true, List.any_eq_true, String.contains_string_iff,
        show "*".toList = ['*'] from rfl, singleton_infix_iff, toList_intercalate_empty]
      constructor
      · rintro (⟨ch, member, listed⟩ | member)
        · obtain ⟨chars, inLists, inChars⟩ := List.mem_flatten.mp member
          obtain ⟨literal, inLiterals, rfl⟩ := List.mem_map.mp inLists
          have known := (unsupportedPatternChar_iff ch).mp listed
          exact ⟨literal, inLiterals, ch, inChars,
            show ch ∈ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\'] ++ ['*'] from
              List.mem_append.mpr (.inl known)⟩
        · obtain ⟨chars, inLists, inChars⟩ := List.mem_flatten.mp member
          obtain ⟨literal, inLiterals, rfl⟩ := List.mem_map.mp inLists
          exact ⟨literal, inLiterals, '*', inChars, by simp⟩
      · rintro ⟨literal, inLiterals, ch, inChars, listed⟩
        have inAll : ch ∈ (literals.map String.toList).flatten :=
          List.mem_flatten.mpr
            ⟨literal.toList, List.mem_map.mpr ⟨literal, inLiterals, rfl⟩, inChars⟩
        by_cases star : ch = '*'
        · exact .inr (star ▸ inAll)
        · refine .inl ⟨ch, inAll, (unsupportedPatternChar_iff ch).mpr ?_⟩
          have split : ch ∈ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\'] ++ ['*'] :=
            listed
          rcases List.mem_append.mp split with known | last
          · exact known
          · exact absurd (List.mem_singleton.mp last) star
    by_cases blank : (literals.any fun x => x.isEmpty) = true
    · simp only [blank, ↓reduceIte, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      refine ⟨fun same => (nomatch same), fun all => ?_⟩
      obtain ⟨literal, member, isEmpty⟩ := List.any_eq_true.mp blank
      exact absurd (String.isEmpty_iff.mp isEmpty) (all literal member).1
    · have filled : ∀ literal ∈ literals, ¬ literal = "" := fun literal member same =>
        blank (List.any_eq_true.mpr ⟨literal, member, String.isEmpty_iff.mpr same⟩)
      simp only [blank, Bool.false_eq_true, ↓reduceIte]
      by_cases wrong : ((("".intercalate literals).toList.any unsupportedPatternChar ||
          ("".intercalate literals).contains "*") = true)
      · simp only [wrong, ↓reduceIte, throw, throwThe, MonadExceptOf.throw]
        refine ⟨fun same => (nomatch same), fun all => ?_⟩
        obtain ⟨literal, member, ch, inChars, listed⟩ := bad.mp wrong
        exact absurd listed ((all literal member).2 ch inChars)
      · simp only [wrong, Bool.false_eq_true, ↓reduceIte]
        exact ⟨fun _ literal member => ⟨filled literal member, fun ch inChars listed =>
          wrong (bad.mpr ⟨literal, member, ch, inChars, listed⟩)⟩, fun _ => rfl⟩

/-- The loop of the validator accepts exactly when each alternative is valid. -/
private theorem forIn_validateAlternative (alternatives : List String) :
    (forIn alternatives PUnit.unit (fun alternative _ => do
        validateAlternative alternative
        pure (ForInStep.yield PUnit.unit)) : Except String PUnit) = .ok PUnit.unit ↔
      ∀ alternative ∈ alternatives, validateAlternative alternative = .ok () := by
  induction alternatives with
  | nil => simp [forIn, pure, Except.pure]
  | cons head rest step =>
    rw [List.forIn_cons]
    cases checked : validateAlternative head with
    | error message =>
      simp only [bind, Except.bind, List.mem_cons, forall_eq_or_imp, checked, reduceCtorEq,
        false_and]
    | ok value =>
      simp only [bind, Except.bind, pure, Except.pure, List.mem_cons, forall_eq_or_imp, checked,
        true_and]
      exact step

/-- **`validatePattern` accepts exactly the valid patterns of the policy library.** -/
theorem validatePattern_eq_ok_iff (pattern : String) :
    validatePattern pattern = .ok () ↔ RegulaPolicy.PatternValid pattern := by
  rw [RegulaPolicy.patternValid_iff]
  unfold validatePattern RegulaPolicy.BodyValid
  generalize RegulaPolicy.patternBody pattern = body
  by_cases empty : body.isEmpty = true
  · have none : body = "" := String.isEmpty_iff.mp empty
    simp [none, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · have some : body ≠ "" := fun same => empty (String.isEmpty_iff.mpr same)
    simp only [empty, Bool.false_eq_true, ↓reduceIte, some, ne_eq, not_false_eq_true, true_and]
    have inner : ∀ alternative : String,
        (¬ alternative = "" ∧ ∀ literal ∈ alternative.splitOn ".*", ¬ literal = "" ∧
          ∀ ch ∈ literal.toList,
            ¬ ch ∈ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\', '*']) ↔
          validateAlternative alternative = .ok () :=
      fun alternative => (validateAlternative_eq_ok_iff alternative).symm
    simp only [inner]
    rw [← forIn_validateAlternative]
    generalize (forIn (body.splitOn "|") PUnit.unit _ : Except String PUnit) = result
    cases result <;> simp [bind, Except.bind, pure, Except.pure]

/-! ## The decision of the Markdown scanner -/

/-- **The Markdown scanner reports no violation exactly for a clean document**: the lines, with
numbers from 1, are a run from outside a fence of transitions that the protocol permits, with the
valid patterns of the policy library, and that keep the shape rule. The run ends outside a fence
with no marker that waits. -/
theorem scanLines_problems_eq_empty_iff (source : Source) :
    (scanLines source).problems = #[] ↔
      Clean RegulaPolicy.PatternValid (.outside none) false 1 source.lines := by
  unfold scanLines
  rw [layout_eq]
  exact problems_eq_iff_clean (valid := RegulaPolicy.PatternValid)
    (fun pattern => (validatePattern_eq_ok_iff pattern).symm) source.document source.origin
    source.lines 1 0 {} (fun _ opened => nomatch opened)

/-- **A scan of a Markdown document has no violation exactly for a clean document.** The
document is the one that the scan carries. -/
theorem Scanned.problems_eq_empty_iff (scan : Scanned) (markdown : scan.format = .markdown) :
    scan.result.problems = #[] ↔
      Clean RegulaPolicy.PatternValid (.outside none) false 1 scan.source.lines := by
  rw [scan.executed, markdown]
  exact scanLines_problems_eq_empty_iff scan.source

/-- The line with no character has no fence run. -/
private theorem no_fence_empty (character : Char) (count : Nat) (info : String) :
    ¬ FenceLine "" character count info := by
  rintro ⟨indent, rest, split, _, _, long, _⟩
  have split : ([] : List Char) = indent ++ List.replicate count character ++ rest := split
  have run := (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp split.symm).1).2
  have zero : count = 0 := by simpa using congrArg List.length run
  omega

/-- The line with no character is a plain line. -/
private theorem plain_empty : LineIs "" .plain := by
  refine ⟨?_, ?_, ?_, no_fence_empty⟩
  · rintro pattern ⟨inner, whole, _⟩
    exact absurd (List.append_eq_nil_iff.mp (show Trimmed [] _ from whole).of_nil).2
      (by decide)
  · intro marker
    exact absurd (show Trimmed [] _ from marker).of_nil (by decide)
  · rintro ⟨rest, inner, whole, _⟩
    exact absurd (List.append_eq_nil_iff.mp (show Trimmed [] _ from whole).of_nil).1
      (by decide)

/-- The line with no character keeps the shape rule outside a fence. -/
private theorem shapeRule_empty (marker : Option Nat) (lean : Bool) :
    ShapeRule (.outside marker) lean "" :=
  ⟨fun lone => absurd ((loneReturn_iff "").mpr lone) (by decide),
    fun tag => absurd ((rawCodeTag_iff "").mpr tag) (by decide),
    fun shaped => absurd ((leanShaped_iff "").mpr shaped) (by decide)⟩

/-- A document of one line that opens a fence is not clean: the fence is not closed. -/
private theorem not_clean_open (valid : String → Prop) :
    ¬ Clean valid (.outside none) false 1 ["```"] := by
  intro clean
  cases clean with
  | line permitted _ _ rest =>
    cases rest
    cases permitted with
    | plain is =>
      exact is.2.2.2 '`' 3 "" ⟨[], [], by decide, fun _ member => (nomatch member), .inl rfl,
        Nat.le_refl 3, fun head => (nomatch head), trimmed_empty⟩

/-- `scanLines` is a sound and complete decision of the clean documents
(`scanLines_problems_eq_empty_iff`): it reports no violation exactly for a document with lines
that are a run of transitions that the protocol permits and that keep the shape rule. It accepts
the document with no character, which has one line, and it refuses the document of one line
that opens a fence. The input is a `Source`, so the lines are those of the text of the document.
The specification is the relation `Clean` over propositions about the characters of each line.
It names no test of the scanner. It says nothing about the text of a violation. About the
fences of an accepted result, `fence_of_leanShaped` says that each line of Lean shape has one. -/
theorem checked_scanLines : Regula.ExecutableContract scanLines
    (Regula.Decides (fun result : ScanResult => result.problems = #[])
      (fun source : Source =>
        Clean RegulaPolicy.PatternValid (.outside none) false 1 source.lines)) :=
  ⟨Regula.Decides.of_iff scanLines_problems_eq_empty_iff
    ⟨⟨⟨"", ""⟩, "", [""], by decide⟩,
      (scanLines_problems_eq_empty_iff _).mpr
        (.line (.plain plain_empty) (shapeRule_empty none false) rfl .done)⟩
    ⟨⟨⟨"", "```"⟩, "", ["```"], by decide⟩, fun accepted =>
      not_clean_open _ ((scanLines_problems_eq_empty_iff _).mp accepted)⟩⟩

/-! ## Each line of Lean shape is a returned fence

In a clean document a line of Lean shape opens a Lean fence in the first column, and the fence
closes. The theorem of this section says that the result has a fence for that line. So a block
that a Markdown reader opens at a line of Lean shape is a fence that the audit takes. -/

/-- The scanner has the Lean fence that opens at the line `number`: among the fences that it
found, or as the fence that is open. -/
private def Covered (state : Scan) (number : Nat) : Prop :=
  (∃ fence ∈ state.fences, fence.line = number) ∨
    ∃ fence, state.opened = some fence ∧ fence.line = number ∧ firstWord fence.info = "lean"

/-- A trimmed form that starts with `first`: the text starts with whitespace or with `first`. -/
private theorem Trimmed.head {text rest : List Char} {first c : Char}
    (trimmed : Trimmed text (first :: rest)) (head : text.head? = some c) :
    c.isWhitespace = true ∨ c = first := by
  obtain ⟨lead, trail, rfl, leading, -⟩ := trimmed
  cases lead with
  | nil => exact .inr (Option.some.inj (by simpa using head.symm))
  | cons space others =>
    obtain rfl : space = c := Option.some.inj (by simpa using head)
    exact .inl (leading space List.mem_cons_self)

/-- A line that opens a Lean fence in the first column has the class of a line that opens a
fence, with an info string that has the first word `lean`: it is no marker, because it starts
with a back-tick or a tilde. -/
private theorem classify_of_leanOpening {line : String} (opening : LeanOpening line) :
    ∃ (character : Char) (count : Nat) (info : String),
      classify line = .opener character count info ∧ firstWord info = "lean" := by
  obtain ⟨character, count, info, fence, head, word⟩ := opening
  have mark : character = '`' ∨ character = '~' := by
    obtain ⟨_, _, _, _, mark, _⟩ := fence
    exact mark
  have notMarker : ∀ {rest : List Char}, ¬ Trimmed line.toList ('<' :: rest) := by
    intro rest trimmed
    rcases trimmed.head head with white | same
    · rcases mark with rfl | rfl <;> exact absurd white (by decide)
    · rcases mark with rfl | rfl <;> exact absurd same (by decide)
  have is := lineIs_classify line
  cases kind : classify line with
  | fail pattern =>
    rw [kind] at is
    obtain ⟨inner, whole, -⟩ := is
    exact absurd whole notMarker
  | trusted =>
    rw [kind] at is
    exact absurd is.2 notMarker
  | malformed =>
    rw [kind] at is
    obtain ⟨rest, inner, whole, -⟩ := is.2.2
    exact absurd whole notMarker
  | plain =>
    rw [kind] at is
    exact absurd fence (is.2.2.2 character count info)
  | opener symbol length text =>
    rw [kind] at is
    have run := (fenceRun?_eq_some_iff _ _ _ _).mpr is.2.2.2
    rw [(fenceRun?_eq_some_iff _ _ _ _).mpr fence] at run
    obtain ⟨rfl, rfl, rfl⟩ : character = symbol ∧ count = length ∧ info = text := by
      simpa using run
    exact ⟨character, count, info, rfl, (firstWord_eq_iff info (by decide)).mpr word⟩

/-- A line outside a fence keeps the fences that the scanner found. -/
private theorem stepOutside_fences (origin : String) (state : Scan) (line : Line) :
    (stepOutside origin state line).fences = state.fences := by
  unfold stepOutside
  generalize classify line.text = kind
  generalize (adjacent origin state line).1 = problems
  generalize (adjacent origin state line).2 = pending
  cases kind <;> cases pending <;> simp only [onClass]
  split <;> rfl

/-- A step keeps the Lean fence of a line that the scanner has. -/
private theorem covered_step (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) {number : Nat} (covered : Covered state number) :
    Covered (shapedStep document origin state line) number := by
  obtain ⟨opened, -, fences⟩ := shapedStep_opened document origin state line
  unfold Covered
  rw [opened, fences]
  unfold step
  cases open' : state.opened with
  | none =>
    rcases covered with found | ⟨fence, isOpen, -⟩
    · exact .inl (by rw [stepOutside_fences]; exact found)
    · rw [open'] at isOpen
      cases isOpen
  | some fence =>
    simp only [stepInside]
    by_cases closes : closingFence line.text fence.character fence.length = true
    · by_cases lean : (firstWord fence.info == "lean") = true
      · simp only [closes, lean, ↓reduceIte]
        refine .inl ?_
        rcases covered with ⟨found, member, numbered⟩ | ⟨other, isOpen, numbered, -⟩
        · exact ⟨found, Array.mem_push_of_mem _ member, numbered⟩
        · rw [open'] at isOpen
          obtain rfl := Option.some.inj isOpen
          exact ⟨_, Array.mem_push_self, numbered⟩
      · have other : (firstWord fence.info == "lean") = false := by simpa using lean
        simp only [closes, other, Bool.false_eq_true, ↓reduceIte]
        rcases covered with found | ⟨other, isOpen, -, word⟩
        · split <;> exact .inl found
        · rw [open'] at isOpen
          obtain rfl := Option.some.inj isOpen
          exact absurd (beq_iff_eq.mpr word) lean
    · simp only [closes, Bool.false_eq_true, ↓reduceIte]
      rcases covered with found | ⟨other, isOpen, numbered, word⟩
      · exact .inl found
      · rw [open'] at isOpen
        obtain rfl := Option.some.inj isOpen
        exact .inr ⟨_, rfl, numbered, word⟩

/-- After a line that opens a Lean fence in the first column, outside a fence, the scanner has
the Lean fence of that line. -/
private theorem covered_opening (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : Scan) (line : Line) (outside : state.opened = none)
    (opening : LeanOpening line.text) :
    Covered (shapedStep document origin state line) line.number := by
  obtain ⟨opened, -, -⟩ := shapedStep_opened document origin state line
  obtain ⟨character, count, info, kind, word⟩ := classify_of_leanOpening opening
  have result := stepOutside_opened origin state line outside
  simp only [kind] at result
  have opens : (shapedStep document origin state line).opened =
      some { character, length := count, info, line := line.number, opening := line.range,
             bodyStart := line.next, body := #[] } := by
    rw [opened]
    unfold step
    rw [outside]
    exact result
  exact .inr ⟨_, opens, rfl, word⟩

/-- On a run that adds no violation, the scanner keeps each Lean fence that it has, and it has
the Lean fence of each line of Lean shape of the run. -/
private theorem covered_run (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : Scan),
      (finish origin ((layoutFrom number offset texts).foldl (shapedStep document origin)
        state)).problems = state.problems →
      (∀ covered, Covered state covered →
        Covered ((layoutFrom number offset texts).foldl (shapedStep document origin) state)
          covered) ∧
      ∀ (index : Nat) (line : String), texts[index]? = some line → LeanShaped line →
        Covered ((layoutFrom number offset texts).foldl (shapedStep document origin) state)
          (number + index) := by
  intro texts
  induction texts with
  | nil =>
    intro number offset state _
    exact ⟨fun _ covered => covered, fun index line found => nomatch found⟩
  | cons text rest tail =>
    intro number offset state same
    obtain ⟨next, later, lines⟩ := layoutFrom_cons number offset text rest
    rw [lines, List.foldl_cons] at same ⊢
    generalize first : ({ number, text, start := offset, next } : Line) = line at same ⊢
    have numbered : line.number = number := by rw [← first]
    have worded : line.text = text := by rw [← first]
    have quiet : (shapedStep document origin state line).problems = state.problems := by
      rcases shapedStep_quiet_or_loud document origin state line with quiet | loud
      · exact quiet
      · exact absurd same (ne_of_size_lt (Nat.lt_of_lt_of_le loud
          (size_le_shapedRun document origin _ _)))
    rw [← quiet] at same
    obtain ⟨keeps, finds⟩ := tail (number + 1) later (shapedStep document origin state line) same
    refine ⟨fun covered has => keeps covered (covered_step document origin state line has), ?_⟩
    intro index found at' shaped
    cases index with
    | zero =>
      obtain rfl : text = found := Option.some.inj at'
      obtain ⟨-, kept⟩ := (shapedStep_quiet_iff document origin state line).mp quiet
      have rule := (shapeRefusal_eq_none_iff state line.text).mp kept
      rw [worded] at rule
      cases open' : state.opened with
      | some fence =>
        have mode : state.mode = .inside fence.character fence.length := by
          simp [Scan.mode, open']
        rw [mode] at rule
        exact absurd shaped rule.2.2.1
      | none =>
        have mode : state.mode = .outside (state.pending.map (·.line)) := by
          simp [Scan.mode, open']
        rw [mode] at rule
        have opening := rule.2.2 shaped
        rw [← worded] at opening
        have here := covered_opening document origin state line open' opening
        rw [numbered] at here
        exact keeps _ here
    | succ before =>
      have := finds before found at' shaped
      rwa [Nat.add_assoc, Nat.add_comm 1 before] at this

/-- **In a clean document, each line of Lean shape is the opening line of a returned fence.**
The fence has the number of that line. With the argument of the shape rule, each block that a
Markdown reader opens as Lean is thus a fence that the audit takes. The theorem says nothing
about the body or the byte ranges of that fence. -/
theorem fence_of_leanShaped (source : Source) (clean : (scanLines source).problems = #[])
    {index : Nat} {line : String} (at' : source.lines[index]? = some line)
    (shaped : LeanShaped line) :
    ∃ fence ∈ (scanLines source).fences, fence.line = index + 1 := by
  unfold scanLines at clean ⊢
  rw [layout_eq] at clean ⊢
  obtain ⟨-, finds⟩ := covered_run source.document source.origin source.lines 1 0 {} clean
  have covered := finds index line at' shaped
  rw [Nat.add_comm] at covered
  rcases covered with found | ⟨fence, isOpen, -⟩
  · exact found
  · -- a clean document ends outside a fence
    have size := size_le_finish source.origin
      ((layoutFrom 1 0 source.lines).foldl (shapedStep source.document source.origin) {})
    rw [clean] at size
    have empty := Array.eq_empty_of_size_eq_zero (Nat.le_zero.mp size)
    have ended := (finish_problems_eq_iff source.origin _).mp (clean.trans empty.symm)
    simp only [Scan.mode, isOpen] at ended
    cases ended

/-! ## The protocol of a Verso source -/

/-- The info string of a supported code block of a Verso source, with what it says about the
block: `lean` is a positive example, `lean +trustedCompiler` a trusted example, one of four
names a block that is not Lean, and `lean (fails := "PATTERN")` a negative example. The info
string of a negative example is the characters `lean (fails := "`, then the characters of the
pattern, then the characters `")`, and the pattern is valid and has no quote and no backslash. -/
inductive BlockKind : String → Option (Option MarkerKind) → Prop
  /-- `lean`: a positive example. -/
  | positive : BlockKind "lean" (some none)
  /-- `lean +trustedCompiler`: a trusted example. -/
  | trusted : BlockKind "lean +trustedCompiler" (some (some .trusted))
  /-- A block that is not Lean. -/
  | other {info : String} : info ∈ ["leanSketch", "sh", "text", "toml"] → BlockKind info none
  /-- `lean (fails := "PATTERN")`: a negative example. -/
  | fails {info pattern : String} :
      info.toList = "lean (fails := \"".toList ++ pattern.toList ++ "\")".toList →
      '"' ∉ pattern.toList → '\\' ∉ pattern.toList →
      RegulaPolicy.PatternValid pattern → BlockKind info (some (some (.fail pattern)))

/-- **`versoBlockKind` accepts exactly the supported info strings, each with its kind.** -/
theorem versoBlockKind_eq_ok_iff (info : String) (kind : Option (Option MarkerKind)) :
    versoBlockKind info = .ok kind ↔ BlockKind info kind := by
  constructor
  · intro accepted
    match kind with
    | none => exact .other (versoBlockKind_other accepted)
    | some none =>
      rw [versoBlockKind_positive accepted]
      exact .positive
    | some (some .trusted) =>
      rw [versoBlockKind_trusted accepted]
      exact .trusted
    | some (some (.fail pattern)) =>
      obtain ⟨starts, ends, text, valid⟩ := versoBlockKind_fail accepted
      have long : "lean (fails := \"".length + "\")".length ≤ info.length ∧
          pattern.contains '"' = false ∧ pattern.contains '\\' = false := by
        unfold versoBlockKind at accepted
        dsimp only at accepted
        repeat' split at accepted
        all_goals simp_all
      obtain ⟨middle, shape⟩ := middle_of_prefix_suffix (String.startsWith_string_iff.mp starts)
        ((endsWith_iff_suffix _ _).mp ends) (by
          rw [String.length_toList, String.length_toList, String.length_toList]; exact long.1)
      have between := toList_between info shape
      rw [String.length_toList, String.length_toList] at between
      have own : pattern.toList = middle := by rw [text]; exact between
      exact .fails (by rw [own]; exact shape)
        (by simpa [String.contains_char_eq] using long.2.1)
        (by simpa [String.contains_char_eq] using long.2.2)
        ((validatePattern_eq_ok_iff pattern).mp valid)
  · intro block
    cases block with
    | positive => rfl
    | trusted => rfl
    | other listed =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
      rcases listed with rfl | rfl | rfl | rfl <;> rfl
    | @fails _ pattern shape quote slash valid =>
      have starts : "lean (fails := \"".toList <+: info.toList := by
        rw [shape, List.append_assoc]; exact List.prefix_append _ _
      have ends : "\")".toList <:+ info.toList := by
        rw [shape]; exact List.suffix_append _ _
      have long : "lean (fails := \"".length + "\")".length ≤ info.length := by
        rw [← String.length_toList, ← String.length_toList, ← String.length_toList (s := info),
          shape, List.length_append, List.length_append]
        omega
      have text : pattern = ((info.drop "lean (fails := \"".length).dropEnd
          "\")".length).toString := by
        have between := toList_between info shape
        rw [String.length_toList, String.length_toList] at between
        exact String.toList_inj.mp between.symm
      have differs : ∀ other : String, ¬ "lean (fails := \"".toList <+: other.toList →
          (info == other) = false := fun other short => by
        rw [beq_eq_false_iff_ne]
        rintro rfl
        exact short starts
      unfold versoBlockKind
      simp only [differs "lean" (by decide), differs "lean +trustedCompiler" (by decide),
        Bool.false_eq_true, ↓reduceIte]
      have unlisted : ["leanSketch", "sh", "text", "toml"].contains info = false := by
        simp only [List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
          decide_eq_false_iff_not, not_or]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> exact absurd starts (by decide)
      have checked := (validatePattern_eq_ok_iff pattern).mpr valid
      have ends := (endsWith_iff_suffix _ _).mpr ends
      have quote : pattern.contains '"' = false := by simpa [String.contains_char_eq] using quote
      have slash : pattern.contains '\\' = false := by
        simpa [String.contains_char_eq] using slash
      simp only [unlisted, Bool.false_eq_true, ↓reduceIte, String.startsWith_string_iff.mpr starts,
        ends, Bool.and_self, ge_iff_le, long, decide_true, ← text, quote, slash, Bool.or_self]
      rw [checked]

/-- What the protocol of a Verso source knows between two lines. -/
inductive VersoMode where
  /-- Outside a code block. -/
  | outside
  /-- Inside a code block that a run of `length` back-ticks opened. -/
  | inside (length : Nat)

/-- The transitions that the protocol of a Verso source permits. Each other line is a
violation: an info string that is not supported, a block that opens with tildes, and a Lean
example on a line that starts with a space. This relation alone permits a Lean example on a line
that starts with a tab or with a carriage return. The shape rule (`VersoShapeRule`) refuses that
line: with it, a Lean example opens in the first column. -/
inductive VersoPermitted : VersoMode → String → VersoMode → Prop
  /-- A line with no fence run, outside a block. -/
  | text {line : String} :
      (∀ character count info, ¬ FenceLine line character count info) →
        VersoPermitted .outside line .outside
  /-- A line that opens a supported block with back-ticks. The line of a Lean example does not
  start with a space. -/
  | opening {line : String} {count : Nat} {info : String} {kind : Option (Option MarkerKind)} :
      FenceLine line '`' count info → BlockKind info kind →
      (∀ marker, kind = some marker → ¬ " ".toList <+: line.toList) →
        VersoPermitted .outside line (.inside count)
  /-- A line that closes the open block. -/
  | closing {line : String} {length : Nat} :
      ClosingLine line '`' length → VersoPermitted (.inside length) line .outside
  /-- A body line of the open block. -/
  | body {line : String} {length : Nat} :
      ¬ ClosingLine line '`' length → VersoPermitted (.inside length) line (.inside length)

/-- The lines are a run of permitted transitions from `mode` that ends outside a block. -/
inductive VersoFollows : VersoMode → List String → Prop
  /-- The end of the source, outside a block. -/
  | done : VersoFollows .outside []
  /-- A permitted line before a rest that follows the protocol. -/
  | line {mode next : VersoMode} {text : String} {rest : List String} :
      VersoPermitted mode text next → VersoFollows next rest →
        VersoFollows mode (text :: rest)

/-- The mode of a state of the Verso scanner. -/
def VersoScan.mode (state : VersoScan) : VersoMode :=
  match state.opened with
  | some block => .inside block.length
  | none => .outside

/-- A step of the Verso scanner keeps the violations, or it makes their list longer. -/
theorem versoStep_quiet_or_loud (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) :
    (versoStep document origin state line).problems = state.problems ∨
      state.problems.size < (versoStep document origin state line).problems.size := by
  unfold versoStep
  cases opened : state.opened with
  | some block =>
    simp only
    repeat' split
    all_goals exact .inl rfl
  | none =>
    simp only
    cases run : fenceRun? line.text with
    | none => exact .inl rfl
    | some found =>
      obtain ⟨character, count, info⟩ := found
      simp only
      cases versoBlockKind info <;> simp only <;>
        by_cases tick : (character != '`') = true <;>
        simp only [tick, ↓reduceIte, Bool.false_eq_true] <;> (try split) <;>
        first
          | exact .inl rfl
          | (refine .inr ?_; simp [Array.size_push]; done)
          | (refine .inr ?_; simp [Array.size_push]; omega)

/-- A line of a Verso source that keeps the violations is a permitted transition to the mode of
the next state. -/
theorem versoPermitted_of_quiet (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line)
    (quiet : (versoStep document origin state line).problems = state.problems) :
    VersoPermitted state.mode line.text (versoStep document origin state line).mode := by
  unfold versoStep at quiet ⊢
  cases opened : state.opened with
  | some block =>
    have mode : state.mode = .inside block.length := by simp [VersoScan.mode, opened]
    rw [mode]
    by_cases closes : closingFence line.text '`' block.length = true
    · have closing := (closingFence_iff _ _ _).mp closes
      simp only [closes, ↓reduceIte]
      split <;> exact .closing closing
    · have body : ¬ ClosingLine line.text '`' block.length := fun closing =>
        closes ((closingFence_iff _ _ _).mpr closing)
      simp only [closes, Bool.false_eq_true, ↓reduceIte]
      exact .body body
  | none =>
    rw [opened] at quiet
    have mode : state.mode = .outside := by simp [VersoScan.mode, opened]
    rw [mode]
    cases run : fenceRun? line.text with
    | none =>
      simp only [VersoScan.mode, opened]
      refine .text fun character count info fence => ?_
      rw [(fenceRun?_eq_some_iff _ _ _ _).mpr fence] at run
      cases run
    | some found =>
      obtain ⟨character, count, info⟩ := found
      have fence := (fenceRun?_eq_some_iff _ _ _ _).mp run
      rw [run] at quiet
      simp only at quiet ⊢
      cases checked : versoBlockKind info with
      | error message =>
        rw [checked] at quiet
        simp only at quiet
        repeat' split at quiet
        all_goals exact absurd quiet (ne_of_size_lt (by simp [Array.size_push] <;> omega))
      | ok kind =>
        rw [checked] at quiet
        simp only at quiet
        by_cases tick : character = '`'
        · subst tick
          by_cases indented : (kind.isSome && line.text.startsWith " ") = true
          · simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, indented] at quiet
            exact absurd quiet (ne_of_size_lt (by simp [Array.size_push]))
          · refine .opening fence ((versoBlockKind_eq_ok_iff info kind).mp checked) ?_
            intro marker same starts
            exact indented (by simp [same, String.startsWith_string_iff.mpr starts])
        · have other : (character != '`') = true := by simpa using tick
          simp only [other, ↓reduceIte] at quiet
          split at quiet
          all_goals exact absurd quiet (ne_of_size_lt (by simp [Array.size_push] <;> omega))

/-- A permitted transition of a Verso source keeps the violations and gives its mode. -/
theorem quiet_of_versoPermitted (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) {next : VersoMode}
    (permitted : VersoPermitted state.mode line.text next) :
    (versoStep document origin state line).problems = state.problems ∧
      (versoStep document origin state line).mode = next := by
  unfold versoStep
  cases opened : state.opened with
  | some block =>
    have mode : state.mode = .inside block.length := by simp [VersoScan.mode, opened]
    rw [mode] at permitted
    cases permitted with
    | closing closing =>
      have closes := (closingFence_iff _ _ _).mpr closing
      simp only [closes, ↓reduceIte]
      split <;> constructor <;> first | rfl | trivial | simp [VersoScan.mode]
    | body body =>
      have closes : closingFence line.text '`' block.length = false := by
        cases test : closingFence line.text '`' block.length with
        | false => rfl
        | true => exact absurd ((closingFence_iff _ _ _).mp test) body
      simp only [closes, Bool.false_eq_true, ↓reduceIte]
      constructor <;> first | rfl | trivial | simp [VersoScan.mode]
  | none =>
    have mode : state.mode = .outside := by simp [VersoScan.mode, opened]
    rw [mode] at permitted
    cases permitted with
    | text none =>
      have run : fenceRun? line.text = Option.none := by
        cases found : fenceRun? line.text with
        | none => rfl
        | some triple =>
          obtain ⟨character, count, info⟩ := triple
          exact absurd ((fenceRun?_eq_some_iff _ _ _ _).mp found) (none character count info)
      simp only [run]
      constructor <;> first | rfl | trivial | simp [VersoScan.mode, opened]
    | @opening _ count info kind fence block column =>
      have run := (fenceRun?_eq_some_iff _ _ _ _).mpr fence
      have checked := (versoBlockKind_eq_ok_iff info kind).mpr block
      have flush : (kind.isSome && line.text.startsWith " ") = false := by
        cases kind with
        | none => rfl
        | some marker =>
          cases starts : line.text.startsWith " " with
          | false => rfl
          | true => exact absurd (String.startsWith_string_iff.mp starts) (column marker rfl)
      simp only [run, checked, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, flush]
      constructor <;> first | rfl | trivial | simp [VersoScan.mode]

private theorem versoFinish_problems_eq_iff (origin : String) (state : VersoScan) :
    (versoFinish origin state).problems = state.problems ↔ state.mode = .outside := by
  unfold versoFinish VersoScan.mode
  cases state.opened with
  | none => simp
  | some block =>
    simp only
    refine ⟨fun same => absurd same (ne_of_size_lt ?_), fun same => (nomatch same)⟩
    simp [Array.size_push]

private theorem size_le_versoRun (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (lines : List Line) (state : VersoScan), state.problems.size ≤
      (versoFinish origin (lines.foldl (versoStep document origin) state)).problems.size := by
  intro lines
  induction lines with
  | nil =>
    intro state
    unfold versoFinish
    cases opened : state.opened <;> simp only [List.foldl_nil, opened] <;> simp [Array.size_push]
  | cons line rest tail =>
    intro state
    refine Nat.le_trans ?_ (tail (versoStep document origin state line))
    rcases versoStep_quiet_or_loud document origin state line with same | longer
    · rw [same]
      exact Nat.le_refl _
    · exact Nat.le_of_lt longer

/-- **The block protocol alone keeps the violations of a state exactly on a run of permitted
transitions.** -/
theorem versoProblems_eq_iff_follows (document : RegulaPolicy.SourceSnapshot)
    (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : VersoScan),
      ((versoFinish origin ((layoutFrom number offset texts).foldl (versoStep document origin)
        state)).problems = state.problems ↔ VersoFollows state.mode texts) := by
  intro texts
  induction texts with
  | nil =>
    intro number offset state
    rw [show layoutFrom number offset [] = [] from rfl, List.foldl_nil,
      versoFinish_problems_eq_iff]
    constructor
    · intro mode
      rw [mode]
      exact .done
    · intro clean
      generalize state.mode = mode at clean
      cases clean
      rfl
  | cons text rest tail =>
    intro number offset state
    obtain ⟨next, later, lines⟩ := layoutFrom_cons number offset text rest
    rw [lines, List.foldl_cons]
    generalize first : ({ number, text, start := offset, next } : Line) = line
    have worded : line.text = text := by rw [← first]
    have after := tail (number + 1) later (versoStep document origin state line)
    constructor
    · intro same
      rcases versoStep_quiet_or_loud document origin state line with quiet | loud
      · have permitted := versoPermitted_of_quiet document origin state line quiet
        rw [worded] at permitted
        rw [← quiet] at same
        exact .line permitted (after.mp same)
      · exact absurd same (ne_of_size_lt (Nat.lt_of_lt_of_le loud
          (size_le_versoRun document origin _ _)))
    · intro clean
      generalize current : state.mode = mode at clean
      cases clean with
      | line permitted others =>
        rw [← current, ← worded] at permitted
        obtain ⟨quiet, mode⟩ := quiet_of_versoPermitted document origin state line permitted
        rw [← mode] at others
        rw [after.mpr others, quiet]

/-! ## The shape rule of a Verso source

The same rule as for a Markdown document, with the block that is open: a line of Lean shape
opens a `lean` block in the first column, outside a block, and a Lean example closes with a run
in the first column. A Verso source has no raw HTML, so the rule has no part about it. -/

/-- The open block of the state is a Lean example. -/
def VersoScan.lean (state : VersoScan) : Bool :=
  state.opened.any fun block => block.kind.isSome

/-- **The shape rule for one line of a Verso source**, with the mode of the protocol before the
line. `lean` says that the open block is a Lean example. Outside a block, a line of Lean shape
opens a Lean block in the first column. Inside a block, no line has Lean shape, and a line that
closes a Lean example starts with the run. -/
def VersoShapeRule (mode : VersoMode) (lean : Bool) (line : String) : Prop :=
  '\r' ∉ line.toList ∧
    match mode with
    | .outside => LeanShaped line → LeanOpening line
    | .inside length =>
        ¬ LeanShaped line ∧
          (lean = true → ClosingLine line '`' length → line.toList.head? = some '`')

private theorem versoShapeRefusal_eq_none_iff (state : VersoScan) (line : String) :
    versoShapeRefusal state.opened line = none ↔
      VersoShapeRule state.mode state.lean line := by
  unfold versoShapeRefusal VersoShapeRule VersoScan.mode VersoScan.lean
  by_cases lone : line.toList.contains '\r' = true
  · simp [List.contains_iff_mem.mp lone]
  have noLone : '\r' ∉ line.toList := fun found => lone (List.contains_iff_mem.mpr found)
  simp only [lone, Bool.false_eq_true, ↓reduceIte, noLone, not_false_eq_true, true_and]
  cases state.opened with
  | none =>
    by_cases shaped : leanShaped line = true <;> by_cases opening : leanOpening line = true <;>
      simp [shaped, opening, ← leanShaped_iff, ← leanOpening_iff]
  | some block =>
    by_cases shaped : leanShaped line = true
    · simp [shaped, ← leanShaped_iff]
    · by_cases lean : block.kind.isSome = true <;>
        by_cases closes : closingFence line '`' block.length = true <;>
        by_cases starts : line.toList.head? = some '`' <;>
        simp [shaped, lean, closes, starts, ← leanShaped_iff, ← closingFence_iff]

/-- The open block after a line is a Lean example. A line that opens a block gives a Lean
example exactly when its info string is one of a Lean example (`BlockKind`). A body line keeps
what the block is. After a line that ends outside a block there is no open block. -/
def VersoLeanAfter (mode : VersoMode) (lean : Bool) (line : String) (next : VersoMode)
    (after : Bool) : Prop :=
  match mode, next with
  | .outside, .inside _ =>
      (after = true ↔
        ∃ (character : Char) (count : Nat) (info : String) (marker : Option MarkerKind),
          FenceLine line character count info ∧ BlockKind info (some marker))
  | .inside _, .inside _ => after = lean
  | _, .outside => after = false

private theorem VersoLeanAfter.unique {mode next : VersoMode} {lean first second : Bool}
    {line : String} (one : VersoLeanAfter mode lean line next first)
    (two : VersoLeanAfter mode lean line next second) : first = second := by
  cases mode <;> cases next <;> simp only [VersoLeanAfter] at one two
  · rw [one, two]
  · exact Bool.eq_iff_iff.mpr (one.trans two.symm)
  · rw [one, two]
  · rw [one, two]

/-- **Each step of the block protocol gives the answer of `VersoLeanAfter`.** -/
private theorem versoLeanAfter_step (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) :
    VersoLeanAfter state.mode state.lean line.text (versoStep document origin state line).mode
      (versoStep document origin state line).lean := by
  unfold versoStep
  cases opened : state.opened with
  | none =>
    have before : state.mode = .outside := by simp [VersoScan.mode, opened]
    rw [before]
    cases run : fenceRun? line.text with
    | none => simp [VersoScan.mode, VersoScan.lean, VersoLeanAfter, opened]
    | some found =>
      obtain ⟨character, count, info⟩ := found
      have fence := (fenceRun?_eq_some_iff _ _ _ _).mp run
      have same : ∀ {symbol : Char} {length : Nat} {text : String},
          FenceLine line.text symbol length text → text = info := by
        intro symbol length text other
        have again := (fenceRun?_eq_some_iff _ _ _ _).mpr other
        rw [run] at again
        simp only [Option.some.injEq, Prod.mk.injEq] at again
        exact again.2.2.symm
      cases kinds : versoBlockKind info with
      | error reason =>
        simp only [VersoScan.mode, VersoScan.lean, VersoLeanAfter, Option.any_some, kinds,
          Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
        intro symbol length text marker other block
        rw [same other] at block
        rw [(versoBlockKind_eq_ok_iff info _).mpr block] at kinds
        cases kinds
      | ok kind =>
        simp only [VersoScan.mode, VersoScan.lean, VersoLeanAfter, Option.any_some, kinds]
        constructor
        · intro some'
          obtain ⟨marker, rfl⟩ := Option.isSome_iff_exists.mp some'
          exact ⟨character, count, info, marker, fence,
            (versoBlockKind_eq_ok_iff info _).mp kinds⟩
        · rintro ⟨symbol, length, text, marker, other, block⟩
          rw [same other] at block
          rw [(versoBlockKind_eq_ok_iff info _).mpr block] at kinds
          obtain rfl : some marker = kind := Except.ok.inj kinds
          rfl
  | some block =>
    have before : state.mode = .inside block.length := by simp [VersoScan.mode, opened]
    rw [before]
    by_cases closes : closingFence line.text '`' block.length = true
    · simp only [closes, ↓reduceIte]
      split <;> simp [VersoScan.mode, VersoScan.lean, VersoLeanAfter]
    · simp [closes, VersoScan.mode, VersoScan.lean, VersoLeanAfter, opened]

private theorem shapedVersoStep_opened (document : RegulaPolicy.SourceSnapshot)
    (origin : String) (state : VersoScan) (line : Line) :
    (shapedVersoStep document origin state line).opened =
        (versoStep document origin state line).opened ∧
      (shapedVersoStep document origin state line).fences =
        (versoStep document origin state line).fences := by
  unfold shapedVersoStep
  split <;> exact ⟨rfl, rfl⟩

private theorem shapedVersoStep_mode (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) :
    (shapedVersoStep document origin state line).mode =
        (versoStep document origin state line).mode ∧
      (shapedVersoStep document origin state line).lean =
        (versoStep document origin state line).lean := by
  obtain ⟨opened, -⟩ := shapedVersoStep_opened document origin state line
  simp [VersoScan.mode, VersoScan.lean, opened]

private theorem shapedVersoStep_quiet_iff (document : RegulaPolicy.SourceSnapshot)
    (origin : String) (state : VersoScan) (line : Line) :
    (shapedVersoStep document origin state line).problems = state.problems ↔
      (versoStep document origin state line).problems = state.problems ∧
        versoShapeRefusal state.opened line.text = none := by
  unfold shapedVersoStep
  cases refusal : versoShapeRefusal state.opened line.text with
  | none => simp
  | some reason =>
    simp only [reduceCtorEq, and_false, iff_false]
    refine ne_of_size_lt ?_
    rcases versoStep_quiet_or_loud document origin state line with same | longer
    · simp [Array.size_push, same]
    · simp only [Array.size_push]
      omega

private theorem shapedVersoStep_quiet_or_loud (document : RegulaPolicy.SourceSnapshot)
    (origin : String) (state : VersoScan) (line : Line) :
    (shapedVersoStep document origin state line).problems = state.problems ∨
      state.problems.size < (shapedVersoStep document origin state line).problems.size := by
  unfold shapedVersoStep
  cases versoShapeRefusal state.opened line.text with
  | none => exact versoStep_quiet_or_loud document origin state line
  | some reason =>
    refine .inr ?_
    rcases versoStep_quiet_or_loud document origin state line with same | longer
    · simp [Array.size_push, same]
    · simp only [Array.size_push]
      omega

private theorem size_le_shapedVersoRun (document : RegulaPolicy.SourceSnapshot)
    (origin : String) :
    ∀ (lines : List Line) (state : VersoScan), state.problems.size ≤
      (versoFinish origin
        (lines.foldl (shapedVersoStep document origin) state)).problems.size := by
  intro lines
  induction lines with
  | nil =>
    intro state
    unfold versoFinish
    cases opened : state.opened <;> simp only [List.foldl_nil, opened] <;> simp [Array.size_push]
  | cons line rest tail =>
    intro state
    refine Nat.le_trans ?_ (tail (shapedVersoStep document origin state line))
    rcases shapedVersoStep_quiet_or_loud document origin state line with same | longer
    · rw [same]
      exact Nat.le_refl _
    · exact Nat.le_of_lt longer

/-- The lines are clean: each line is a permitted transition of the block protocol and keeps the
shape rule, and the run ends outside a block. `lean` says that the open block is a Lean
example. -/
inductive VersoClean : VersoMode → Bool → List String → Prop
  /-- The end of the source, outside a block. -/
  | done {lean : Bool} : VersoClean .outside lean []
  /-- A line that the protocol permits and that keeps the shape rule, before a clean rest. -/
  | line {mode next : VersoMode} {lean after : Bool} {text : String} {rest : List String} :
      VersoPermitted mode text next → VersoShapeRule mode lean text →
      VersoLeanAfter mode lean text next after → VersoClean next after rest →
        VersoClean mode lean (text :: rest)

/-- **The Verso scanner keeps the violations of a state exactly on a clean run.** -/
theorem versoProblems_eq_iff_clean (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : VersoScan),
      ((versoFinish origin ((layoutFrom number offset texts).foldl
        (shapedVersoStep document origin) state)).problems = state.problems ↔
          VersoClean state.mode state.lean texts) := by
  intro texts
  induction texts with
  | nil =>
    intro number offset state
    rw [show layoutFrom number offset [] = [] from rfl, List.foldl_nil,
      versoFinish_problems_eq_iff]
    constructor
    · intro mode
      rw [mode]
      exact .done
    · intro clean
      generalize state.mode = mode at clean
      cases clean
      rfl
  | cons text rest tail =>
    intro number offset state
    obtain ⟨next, later, lines⟩ := layoutFrom_cons number offset text rest
    rw [lines, List.foldl_cons]
    generalize first : ({ number, text, start := offset, next } : Line) = line
    have worded : line.text = text := by rw [← first]
    obtain ⟨sameMode, sameLean⟩ := shapedVersoStep_mode document origin state line
    have after := tail (number + 1) later (shapedVersoStep document origin state line)
    rw [sameMode, sameLean] at after
    have answer := versoLeanAfter_step document origin state line
    constructor
    · intro same
      rcases shapedVersoStep_quiet_or_loud document origin state line with quiet | loud
      · obtain ⟨base, kept⟩ := (shapedVersoStep_quiet_iff document origin state line).mp quiet
        have permitted := versoPermitted_of_quiet document origin state line base
        have rule := (versoShapeRefusal_eq_none_iff state line.text).mp kept
        rw [worded] at permitted rule answer
        rw [← quiet] at same
        exact .line permitted rule answer (after.mp same)
      · exact absurd same (ne_of_size_lt (Nat.lt_of_lt_of_le loud
          (size_le_shapedVersoRun document origin _ _)))
    · intro clean
      generalize current : state.mode = mode at clean
      generalize flag : state.lean = lean at clean
      cases clean with
      | line permitted rule answered others =>
        rw [← current, ← worded] at permitted
        rw [← current, ← flag, ← worded] at rule answered
        obtain ⟨base, mode⟩ := quiet_of_versoPermitted document origin state line permitted
        have kept := (versoShapeRefusal_eq_none_iff state line.text).mpr rule
        have quiet := (shapedVersoStep_quiet_iff document origin state line).mpr ⟨base, kept⟩
        rw [← mode] at others answered
        rw [answer.unique answered] at after
        rw [after.mpr others, quiet]

/-! ## Each line of Lean shape of a Verso source is a returned example -/

/-- The Verso scanner has the Lean example that opens at the line `number`: among the examples
that it found, or as the block that is open. -/
private def VersoCovered (state : VersoScan) (number : Nat) : Prop :=
  (∃ fence ∈ state.fences, fence.line = number) ∨
    ∃ block, state.opened = some block ∧ block.line = number ∧ block.kind.isSome = true

/-- A step keeps the Lean example of a line that the Verso scanner has. -/
private theorem versoCovered_step (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) {number : Nat} (covered : VersoCovered state number) :
    VersoCovered (shapedVersoStep document origin state line) number := by
  obtain ⟨opened, fences⟩ := shapedVersoStep_opened document origin state line
  unfold VersoCovered
  rw [opened, fences]
  unfold versoStep
  cases open' : state.opened with
  | none =>
    rcases covered with found | ⟨block, isOpen, -⟩
    · cases fenceRun? line.text with
      | none => exact .inl found
      | some run => exact .inl found
    · rw [open'] at isOpen
      cases isOpen
  | some block =>
    by_cases closes : closingFence line.text '`' block.length = true
    · simp only [closes, ↓reduceIte]
      cases kind : block.kind with
      | none =>
        rcases covered with found | ⟨other, isOpen, -, lean⟩
        · exact .inl found
        · rw [open'] at isOpen
          obtain rfl := Option.some.inj isOpen
          rw [kind] at lean
          cases lean
      | some marker =>
        refine .inl ?_
        rcases covered with ⟨found, member, numbered⟩ | ⟨other, isOpen, numbered, -⟩
        · exact ⟨found, Array.mem_push_of_mem _ member, numbered⟩
        · rw [open'] at isOpen
          obtain rfl := Option.some.inj isOpen
          exact ⟨_, Array.mem_push_self, numbered⟩
    · simp only [closes, Bool.false_eq_true, ↓reduceIte]
      rcases covered with found | ⟨other, isOpen, numbered, lean⟩
      · exact .inl found
      · rw [open'] at isOpen
        obtain rfl := Option.some.inj isOpen
        exact .inr ⟨_, rfl, numbered, lean⟩

/-- The block that a line outside a block opens has the number of that line. -/
private theorem versoStep_opened_line (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) (outside : state.opened = none) {block : OpenBlock}
    (opens : (versoStep document origin state line).opened = some block) :
    block.line = line.number := by
  unfold versoStep at opens
  rw [outside] at opens
  cases run : fenceRun? line.text with
  | none =>
    rw [run] at opens
    rw [outside] at opens
    cases opens
  | some found =>
    obtain ⟨character, count, info⟩ := found
    rw [run] at opens
    obtain rfl := Option.some.inj opens
    rfl

/-- After a line that opens a `lean` block in the first column, outside a block, and that adds
no violation, the Verso scanner has the Lean example of that line. -/
private theorem versoCovered_opening (document : RegulaPolicy.SourceSnapshot) (origin : String)
    (state : VersoScan) (line : Line) (outside : state.opened = none)
    (quiet : (versoStep document origin state line).problems = state.problems)
    (opening : LeanOpening line.text) :
    VersoCovered (shapedVersoStep document origin state line) line.number := by
  obtain ⟨opened, -⟩ := shapedVersoStep_opened document origin state line
  have mode : state.mode = .outside := by simp [VersoScan.mode, outside]
  have permitted := versoPermitted_of_quiet document origin state line quiet
  have answer := versoLeanAfter_step document origin state line
  rw [mode] at permitted answer
  obtain ⟨character, count, info, fence, -, word⟩ := opening
  generalize (versoStep document origin state line).mode = after at permitted answer
  cases permitted with
  | text none => exact absurd fence (none character count info)
  | @opening _ length text kind other block _ =>
    have run := (fenceRun?_eq_some_iff _ _ _ _).mpr other
    rw [(fenceRun?_eq_some_iff _ _ _ _).mpr fence] at run
    obtain ⟨-, -, rfl⟩ : character = '`' ∧ count = length ∧ info = text := by simpa using run
    have lean : ∃ marker, kind = some marker := by
      cases block with
      | positive => exact ⟨_, rfl⟩
      | trusted => exact ⟨_, rfl⟩
      | fails => exact ⟨_, rfl⟩
      | other listed =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
        rcases listed with rfl | rfl | rfl | rfl <;>
          exact absurd ((firstWord_eq_iff _ (by decide)).mpr word) (by decide)
    obtain ⟨marker, rfl⟩ := lean
    simp only [VersoLeanAfter] at answer
    have flag := answer.mpr ⟨'`', length, info, marker, other, block⟩
    cases opens : (versoStep document origin state line).opened with
    | none => simp [VersoScan.lean, opens] at flag
    | some open' =>
      refine .inr ⟨open', by rw [opened, opens], ?_, ?_⟩
      · exact versoStep_opened_line document origin state line outside opens
      · simpa [VersoScan.lean, opens] using flag

/-- On a run that adds no violation, the Verso scanner keeps each Lean example that it has, and
it has the Lean example of each line of Lean shape of the run. -/
private theorem versoCovered_run (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : VersoScan),
      (versoFinish origin ((layoutFrom number offset texts).foldl
        (shapedVersoStep document origin) state)).problems = state.problems →
      (∀ covered, VersoCovered state covered →
        VersoCovered ((layoutFrom number offset texts).foldl (shapedVersoStep document origin)
          state) covered) ∧
      ∀ (index : Nat) (line : String), texts[index]? = some line → LeanShaped line →
        VersoCovered ((layoutFrom number offset texts).foldl (shapedVersoStep document origin)
          state) (number + index) := by
  intro texts
  induction texts with
  | nil =>
    intro number offset state _
    exact ⟨fun _ covered => covered, fun index line found => nomatch found⟩
  | cons text rest tail =>
    intro number offset state same
    obtain ⟨next, later, lines⟩ := layoutFrom_cons number offset text rest
    rw [lines, List.foldl_cons] at same ⊢
    generalize first : ({ number, text, start := offset, next } : Line) = line at same ⊢
    have numbered : line.number = number := by rw [← first]
    have worded : line.text = text := by rw [← first]
    have quiet : (shapedVersoStep document origin state line).problems = state.problems := by
      rcases shapedVersoStep_quiet_or_loud document origin state line with quiet | loud
      · exact quiet
      · exact absurd same (ne_of_size_lt (Nat.lt_of_lt_of_le loud
          (size_le_shapedVersoRun document origin _ _)))
    rw [← quiet] at same
    obtain ⟨keeps, finds⟩ :=
      tail (number + 1) later (shapedVersoStep document origin state line) same
    refine ⟨fun covered has => keeps covered (versoCovered_step document origin state line has),
      ?_⟩
    intro index found at' shaped
    cases index with
    | zero =>
      obtain rfl : text = found := Option.some.inj at'
      obtain ⟨base, kept⟩ := (shapedVersoStep_quiet_iff document origin state line).mp quiet
      have rule := (versoShapeRefusal_eq_none_iff state line.text).mp kept
      rw [worded] at rule
      cases open' : state.opened with
      | some block =>
        have mode : state.mode = .inside block.length := by simp [VersoScan.mode, open']
        rw [mode] at rule
        exact absurd shaped rule.2.1
      | none =>
        have mode : state.mode = .outside := by simp [VersoScan.mode, open']
        rw [mode] at rule
        have opening := rule.2 shaped
        rw [← worded] at opening
        have here := versoCovered_opening document origin state line open' base opening
        rw [numbered] at here
        exact keeps _ here
    | succ before =>
      have := finds before found at' shaped
      rwa [Nat.add_assoc, Nat.add_comm 1 before] at this

/-- **In a clean Verso source, each line of Lean shape is the opening line of a returned
example.** The example has the number of that line. The theorem says nothing about the body or
the byte ranges of that example. -/
theorem example_of_leanShaped (source : Source) (clean : (scanVersoLines source).problems = #[])
    {index : Nat} {line : String} (at' : source.lines[index]? = some line)
    (shaped : LeanShaped line) :
    ∃ fence ∈ (scanVersoLines source).fences, fence.line = index + 1 := by
  unfold scanVersoLines at clean ⊢
  rw [layout_eq] at clean ⊢
  obtain ⟨-, finds⟩ := versoCovered_run source.document source.origin source.lines 1 0 {} clean
  have covered := finds index line at' shaped
  rw [Nat.add_comm] at covered
  rcases covered with found | ⟨block, isOpen, -⟩
  · exact found
  · have size := size_le_shapedVersoRun source.document source.origin [] ((layoutFrom 1 0
      source.lines).foldl (shapedVersoStep source.document source.origin) {})
    rw [List.foldl_nil, clean] at size
    have empty := Array.eq_empty_of_size_eq_zero (Nat.le_zero.mp size)
    have ended := (versoFinish_problems_eq_iff source.origin _).mp (clean.trans empty.symm)
    simp only [VersoScan.mode, isOpen] at ended
    cases ended

/-- **The Verso scanner reports no violation exactly for a clean source**: the lines are a run
from outside a block of transitions that the protocol permits and that keep the shape rule, and
the run ends outside a block. -/
theorem scanVersoLines_problems_eq_empty_iff (source : Source) :
    (scanVersoLines source).problems = #[] ↔ VersoClean .outside false source.lines := by
  unfold scanVersoLines
  rw [layout_eq]
  exact versoProblems_eq_iff_clean source.document source.origin source.lines 1 0 {}

/-- **A scan of a Verso source has no violation exactly for a clean source.** The source is the
one that the scan carries. -/
theorem Scanned.versoProblems_eq_empty_iff (scan : Scanned) (verso : scan.format = .verso) :
    scan.result.problems = #[] ↔ VersoClean .outside false scan.source.lines := by
  rw [scan.executed, verso]
  exact scanVersoLines_problems_eq_empty_iff scan.source

/-- A source of one line that opens a block is not clean: the block is not closed. -/
private theorem not_versoClean_open : ¬ VersoClean .outside false ["```"] := by
  intro clean
  cases clean with
  | line permitted _ _ rest =>
    cases rest
    cases permitted with
    | text none =>
      exact none '`' 3 "" ⟨[], [], by decide, fun _ member => (nomatch member), .inl rfl,
        Nat.le_refl 3, fun head => (nomatch head), trimmed_empty⟩

/-- `scanVersoLines` is a sound and complete decision of the clean Verso sources
(`scanVersoLines_problems_eq_empty_iff`): it reports no violation exactly for a source with lines
that are a run of transitions that the protocol permits and that keep the shape rule. It accepts
the source with no character, which has one line, and it refuses the source of one line that
opens a block. The input is a `Source`, so the lines are those of the text of the source. The
specification is the relation `VersoClean` over propositions about the characters of each line
and about the info string of each block (`BlockKind`). It names no test of the scanner. It says
nothing about the text of a violation. About the examples of an accepted result,
`example_of_leanShaped` says that each line of Lean shape has one. -/
theorem checked_scanVersoLines : Regula.ExecutableContract scanVersoLines
    (Regula.Decides (fun result : ScanResult => result.problems = #[])
      (fun source : Source => VersoClean .outside false source.lines)) :=
  ⟨Regula.Decides.of_iff scanVersoLines_problems_eq_empty_iff
    ⟨⟨⟨"", ""⟩, "", [""], by decide⟩,
      (scanVersoLines_problems_eq_empty_iff _).mpr
        (.line (.text no_fence_empty)
          ⟨by decide, (shapeRule_empty none false).2.2⟩ rfl .done)⟩
    ⟨⟨⟨"", "```"⟩, "", ["```"], by decide⟩, fun accepted =>
      not_versoClean_open ((scanVersoLines_problems_eq_empty_iff _).mp accepted)⟩⟩

end Regula.Checker.Documentation
