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

Each scanner is a machine with one state (`Scan`, `VersoScan`): `step` reads one line, and
`finish` reads the end of the document. No function of this module reads a file.

`scanLines` and `scanVersoLines` are the registered decisions. `checked_scanLines` and
`checked_scanVersoLines` state that each reports no violation exactly for a document with lines
that the protocol relation admits (`Clean`, `VersoClean`). The input of a decision is a `Source`:
a document with its lines, bound to its text (`toList_linesOf`). The audit takes a `Scanned`: a
result that is bound to its input and to the scanner. No theorem is about the fences of a
result.

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
  finish source.origin ((layout source.lines).foldl (step source.document source.origin) {})

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
with a space are violations. A Lean example on a line that starts with a tab or with a carriage
return is not a violation. Each other line outside a block is read past. -/
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
    ((layout source.lines).foldl (versoStep source.document source.origin) {})

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
classification. The opening line of a Lean example does not start with a space. The scanner
does not refuse an opening line that starts with a tab or with a carriage return, so the first
column is not a guarantee. -/
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
inductive Clean (valid : String → Prop) : Mode → Nat → List String → Prop
  /-- The end of the document, outside a fence and with no marker that waits. -/
  | done {number : Nat} : Clean valid (.outside none) number []
  /-- A permitted line before a clean rest. -/
  | line {mode next : Mode} {number : Nat} {text : String} {rest : List String} :
      Permitted valid mode number text next → Clean valid next (number + 1) rest →
        Clean valid mode number (text :: rest)

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
theorem problems_eq_iff_clean {valid : String → Prop}
    (exact : ∀ pattern, valid pattern ↔ validatePattern pattern = .ok ())
    (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : Scan), state.Coherent →
      ((finish origin ((layoutFrom number offset texts).foldl (step document origin)
        state)).problems = state.problems ↔ Clean valid state.mode number texts) := by
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
numbers from 1, are a run of permitted transitions from outside a fence, with the valid patterns
of the policy library, that ends outside a fence with no marker that waits. -/
theorem scanLines_problems_eq_empty_iff (source : Source) :
    (scanLines source).problems = #[] ↔
      Clean RegulaPolicy.PatternValid (.outside none) 1 source.lines := by
  unfold scanLines
  rw [layout_eq]
  exact problems_eq_iff_clean (valid := RegulaPolicy.PatternValid)
    (fun pattern => (validatePattern_eq_ok_iff pattern).symm) source.document source.origin
    source.lines 1 0 {} (fun _ opened => nomatch opened)

/-- **A scan of a Markdown document has no violation exactly for a clean document.** The
document is the one that the scan carries. -/
theorem Scanned.problems_eq_empty_iff (scan : Scanned) (markdown : scan.format = .markdown) :
    scan.result.problems = #[] ↔
      Clean RegulaPolicy.PatternValid (.outside none) 1 scan.source.lines := by
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

/-- A document of one line that opens a fence is not clean: the fence is not closed. -/
private theorem not_clean_open (valid : String → Prop) :
    ¬ Clean valid (.outside none) 1 ["```"] := by
  intro clean
  cases clean with
  | line permitted rest =>
    cases rest
    cases permitted with
    | plain is =>
      exact is.2.2.2 '`' 3 "" ⟨[], [], by decide, fun _ member => (nomatch member), .inl rfl,
        Nat.le_refl 3, fun head => (nomatch head), trimmed_empty⟩

/-- `scanLines` is a sound and complete decision of the clean documents
(`scanLines_problems_eq_empty_iff`): it reports no violation exactly for a document with lines
that are a run of permitted transitions. It accepts the document with no character, which has
one line, and it refuses the document of one line that opens a fence. The input is a `Source`,
so the lines are those of the text of the document. The specification is the relation `Clean`
over propositions about the characters of each line. It names no test of the scanner. It says
nothing about the fences that an accepted result carries, and nothing about the text of a
violation. -/
theorem checked_scanLines : Regula.ExecutableContract scanLines
    (Regula.Decides (fun result : ScanResult => result.problems = #[])
      (fun source : Source => Clean RegulaPolicy.PatternValid (.outside none) 1 source.lines)) :=
  ⟨Regula.Decides.of_iff scanLines_problems_eq_empty_iff
    ⟨⟨⟨"", ""⟩, "", [""], by decide⟩,
      (scanLines_problems_eq_empty_iff _).mpr (.line (.plain plain_empty) .done)⟩
    ⟨⟨⟨"", "```"⟩, "", ["```"], by decide⟩, fun accepted =>
      not_clean_open _ ((scanLines_problems_eq_empty_iff _).mp accepted)⟩⟩

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
example on a line that starts with a space. The relation states what the scanner tests. It does
not state that a Lean example opens in the first column: a line that starts with a tab or with a
carriage return is permitted. -/
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
inductive VersoClean : VersoMode → List String → Prop
  /-- The end of the source, outside a block. -/
  | done : VersoClean .outside []
  /-- A permitted line before a clean rest. -/
  | line {mode next : VersoMode} {text : String} {rest : List String} :
      VersoPermitted mode text next → VersoClean next rest → VersoClean mode (text :: rest)

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

/-- **The Verso scanner keeps the violations of a state exactly on a clean run.** -/
theorem versoProblems_eq_iff_clean (document : RegulaPolicy.SourceSnapshot) (origin : String) :
    ∀ (texts : List String) (number offset : Nat) (state : VersoScan),
      ((versoFinish origin ((layoutFrom number offset texts).foldl (versoStep document origin)
        state)).problems = state.problems ↔ VersoClean state.mode texts) := by
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

/-- **The Verso scanner reports no violation exactly for a clean source**: the lines are a run
of permitted transitions from outside a block that ends outside a block. -/
theorem scanVersoLines_problems_eq_empty_iff (source : Source) :
    (scanVersoLines source).problems = #[] ↔ VersoClean .outside source.lines := by
  unfold scanVersoLines
  rw [layout_eq]
  exact versoProblems_eq_iff_clean source.document source.origin source.lines 1 0 {}

/-- **A scan of a Verso source has no violation exactly for a clean source.** The source is the
one that the scan carries. -/
theorem Scanned.versoProblems_eq_empty_iff (scan : Scanned) (verso : scan.format = .verso) :
    scan.result.problems = #[] ↔ VersoClean .outside scan.source.lines := by
  rw [scan.executed, verso]
  exact scanVersoLines_problems_eq_empty_iff scan.source

/-- A source of one line that opens a block is not clean: the block is not closed. -/
private theorem not_versoClean_open : ¬ VersoClean .outside ["```"] := by
  intro clean
  cases clean with
  | line permitted rest =>
    cases rest
    cases permitted with
    | text none =>
      exact none '`' 3 "" ⟨[], [], by decide, fun _ member => (nomatch member), .inl rfl,
        Nat.le_refl 3, fun head => (nomatch head), trimmed_empty⟩

/-- `scanVersoLines` is a sound and complete decision of the clean Verso sources
(`scanVersoLines_problems_eq_empty_iff`): it reports no violation exactly for a source with lines
that are a run of permitted transitions. It accepts the source with no character, which has one
line, and it refuses the source of one line that opens a block. The input is a `Source`, so the
lines are those of the text of the source. The specification is the relation `VersoClean` over
propositions about the characters of each line and about the info string of each block
(`BlockKind`). It names no test of the scanner. It says nothing about the examples that an
accepted result carries, and nothing about the text of a violation. -/
theorem checked_scanVersoLines : Regula.ExecutableContract scanVersoLines
    (Regula.Decides (fun result : ScanResult => result.problems = #[])
      (fun source : Source => VersoClean .outside source.lines)) :=
  ⟨Regula.Decides.of_iff scanVersoLines_problems_eq_empty_iff
    ⟨⟨⟨"", ""⟩, "", [""], by decide⟩,
      (scanVersoLines_problems_eq_empty_iff _).mpr (.line (.text no_fence_empty) .done)⟩
    ⟨⟨⟨"", "```"⟩, "", ["```"], by decide⟩, fun accepted =>
      not_versoClean_open ((scanVersoLines_problems_eq_empty_iff _).mp accepted)⟩⟩

end Regula.Checker.Documentation
