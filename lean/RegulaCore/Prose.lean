import RegulaCore.Site

/-! # Rule IDs in prose

Every rule ID that a document mentions in prose is a link to that rule's page. This module
defines what prose is, as a property of a document's structure, decides whether a document has a
rule ID in prose that is not such a link, and rewrites generated prose so that it has none.

## Main declarations

- `tokenAt`, `splitTokens`: a rule-ID token is `RG` and four digits with no word character
  directly before or after it.
- `Run`, `Mention`, `Run.mentions`: a run is a maximal piece of prose with the destination of the
  link it lies in, if any; a mention is one token of a run.
- `Mention.Linked`, `bareMentions`, `bareMentions_nil_iff`, `checked_bareMentions`: a mention is
  linked when its token is a registered rule ID and its link's destination is that rule's page;
  the executed check returns nothing exactly when every mention of every run is linked.
- `developmentTarget`, `pageTarget`, `pageTarget_iff`: the page of a rule for a Markdown document
  of `main` (the development page, `Edition.url`, the definition `helpUrl` and `citation` use) and
  for a rendered page of an edition (the rule's page file of that edition).
- `markdownRuns`, `htmlRuns`: the prose of a Markdown document and of an HTML page.
- `markdownErrors`, `htmlErrors`, `markdownErrors_nil_iff`, `htmlErrors_nil_iff`: the two executed
  document checks, each reporting the file, the line and the ID.
- `relativeCitation`, `rewriteIds`, `linkVerso`: the link a generated page gives a rule, relative
  to its edition's root (`RuleId.route`), and the rewriting of generated prose that inserts it.

## What prose is

In a Markdown document, prose is the text outside fenced code blocks (`fenceRun?`), code spans,
headings, link reference definitions, link destinations, HTML tags and comments, autolinks and
bare URLs. In an HTML page, prose is the text outside the `code`, `pre`, `samp`, `kbd`, `title`,
`h1` to `h6`, `script` and `style` elements (`exemptElement`). Pasted tool output is a fenced block
or a `pre` element; a Lean identifier is code. A rule table that is the index of rule pages names
each rule as a link to its page, so its IDs are linked mentions. A heading names a section and is
the target of links, so it is not prose.

## Boundaries

`bareMentions_nil_iff` is about the runs it is given. `markdownRuns` and `htmlRuns` are small
scanners for this repository's documents and the builder's own output, not complete CommonMark
or HTML parsers: an indented code block, a setext heading and text between raw HTML tags are
read as prose, so an ID there must be linked, and only the constructs listed above are skipped.
A fenced block, element, comment or script that is never closed would hide the text after it, so
`markdownErrors` and `htmlErrors` refuse such a document; an element closed and reopened out of
order is not detected. `linkVerso` rewrites the prose `scanInline` finds; that its output has no
bare rule ID is established by `htmlErrors` on the rendered pages, not by a theorem about the
rewriting.
-/

namespace Regula.Prose

open Regula.Site

/-! ## Rule-ID tokens -/

/-- A character that continues a word: an ASCII letter or digit, or `_`. -/
def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The rule-ID token at the head of `text`, when `prev` is the character before it: `RG` and
four digits, with no word character directly before or after. -/
def tokenAt (prev : Option Char) : List Char → Option String
  | 'R' :: 'G' :: a :: b :: c :: d :: rest =>
    if !prev.any isWordChar && a.isDigit && b.isDigit && c.isDigit && d.isDigit &&
        !rest.head?.any isWordChar then
      some (String.ofList ['R', 'G', a, b, c, d])
    else none
  | _ => none

private def textPart (acc : List Char) : List (String ⊕ String) :=
  if acc.isEmpty then [] else [.inl (String.ofList acc.reverse)]

/-- `text` split at its rule-ID tokens, in order: `.inl` the text between tokens and `.inr` each
token. `prev` is the character before `text`, `skip` the number of characters of a token still to
pass, and `acc` the text since the last token, reversed. -/
def splitTokens : Option Char → Nat → List Char → List Char → List (String ⊕ String)
  | _, _, acc, [] => textPart acc
  | _, skip + 1, acc, c :: rest => splitTokens (some c) skip acc rest
  | prev, 0, acc, c :: rest =>
    match tokenAt prev (c :: rest) with
    | some token => textPart acc ++ .inr token :: splitTokens (some c) 5 [] rest
    | none => splitTokens (some c) 0 (c :: acc) rest

private def newlines (s : String) : Nat := s.toList.count '\n'

/-! ## Mentions and the decision -/

/-- A maximal piece of a document's prose. -/
structure Run where
  /-- The 1-based line on which the run starts. -/
  line : Nat
  /-- The run's text. -/
  text : String
  /-- The destination of the link whose text the run lies in, if any. -/
  link : Option String
  deriving DecidableEq, Repr

/-- One rule-ID token in prose. -/
structure Mention where
  /-- The 1-based line of the token. -/
  line : Nat
  /-- The token, such as `RG1001`. -/
  token : String
  /-- The destination of the link whose text the token lies in, if any. -/
  link : Option String
  deriving DecidableEq, Repr

/-- The rule-ID tokens of a run, in order, each on its own line of the document. -/
def Run.mentions (r : Run) : List Mention :=
  ((splitTokens none 0 [] r.text.toList).foldl (fun (acc : Nat × List Mention) part =>
    match part with
    | .inl text => (acc.1 + newlines text, acc.2)
    | .inr token => (acc.1, ⟨acc.1, token, r.link⟩ :: acc.2)) (r.line, [])).2.reverse

/-- Mention `m` is linked: its token is a registered rule ID, and it lies in the text of a link
whose destination `target` accepts as that rule's page. -/
def Mention.Linked (target : RuleId → String → Bool) (m : Mention) : Prop :=
  ∃ id destination, RuleId.parse? m.token = some id ∧ m.link = some destination ∧
    target id destination = true

/-- `Mention.Linked`, decided. -/
def Mention.linked (target : RuleId → String → Bool) (m : Mention) : Bool :=
  match RuleId.parse? m.token, m.link with
  | some id, some destination => target id destination
  | _, _ => false

theorem Mention.linked_iff (target : RuleId → String → Bool) (m : Mention) :
    m.linked target = true ↔ m.Linked target := by
  unfold Mention.linked Mention.Linked
  split
  · rename_i id destination hid hlink
    constructor
    · intro h
      exact ⟨id, destination, hid, hlink, h⟩
    · rintro ⟨id', destination', hid', hlink', h⟩
      rw [hid] at hid'
      rw [hlink] at hlink'
      cases hid'
      cases hlink'
      exact h
  · rename_i hnot
    constructor
    · intro h
      cases h
    · rintro ⟨id, destination, hid, hlink, _⟩
      exact (hnot id destination hid hlink).elim

/-- The mentions of `runs` that are not linked, in document order. -/
def bareMentions (target : RuleId → String → Bool) (runs : List Run) : List Mention :=
  (runs.flatMap Run.mentions).filter fun m => !m.linked target

/-- The executed check returns nothing exactly when every rule-ID token of every run is a
registered rule ID inside a link to that rule's page. -/
theorem bareMentions_nil_iff (target : RuleId → String → Bool) (runs : List Run) :
    bareMentions target runs = [] ↔ ∀ run ∈ runs, ∀ m ∈ run.mentions, m.Linked target := by
  simp only [bareMentions, List.filter_eq_nil_iff, List.mem_flatMap, Bool.not_eq_true',
    Bool.not_eq_false]
  constructor
  · intro h run hr m hm
    exact (Mention.linked_iff target m).mp (h m ⟨run, hr, hm⟩)
  · rintro h m ⟨run, hr, hm⟩
    exact (Mention.linked_iff target m).mpr (h run hr m hm)

/-- Registered contract of the executed prose check. -/
theorem checked_bareMentions : Regula.ExecutableContract bareMentions (fun run =>
    ∀ target runs, run target runs = [] ↔
      ∀ r ∈ runs, ∀ m ∈ r.mentions, m.Linked target) :=
  ⟨bareMentions_nil_iff⟩

/-- What a refused mention reports: the file, the line, the ID and why it is refused. -/
def Mention.describe (file : String) (m : Mention) : String :=
  s!"{file}:{m.line}: {m.token} " ++
    match RuleId.parse? m.token, m.link with
    | none, _ => "is not a registered rule ID"
    | some _, none => "is a bare rule ID in prose; make it a link to its rule page"
    | some _, some destination => s!"is linked to {destination}, which is not its rule page"

/-! ## Rule pages -/

/-- Whether `destination` is rule `id`'s page for a Markdown document of `main`: the rule's
development page, as `Edition.url` spells it (the definition `helpUrl` and `citation` use), alone
or followed by a fragment. -/
def developmentTarget (id : RuleId) (destination : String) : Bool :=
  destination == Edition.dev.url id.route ||
    destination.startsWith (Edition.dev.url id.route ++ "#")

/-- Whether `destination`, a link of the rendered page `page`, resolves to rule `id`'s page file
in the edition whose artifact root is `root`, with any fragment. -/
def pageTarget (root : String) (page : Page) (id : RuleId) (destination : String) : Bool :=
  match resolve page destination with
  | .internal file _ => file == root ++ id.route ++ "index.html"
  | _ => false

/-- In edition `e`, the accepted destinations are exactly those that resolve to the rule's page
file of that edition (`Edition.pageFile`), so a rendered page links within its own edition. -/
theorem pageTarget_iff (e : Edition) (page : Page) (id : RuleId) (destination : String) :
    pageTarget e.root page id destination = true ↔
      ∃ fragment, resolve page destination = .internal (e.pageFile id) fragment := by
  unfold pageTarget
  cases resolve page destination with
  | external => simp
  | invalid reason => simp
  | internal file fragment =>
    simp only [beq_iff_eq, Target.internal.injEq, Edition.pageFile, Edition.pagePath]
    constructor
    · intro h
      exact ⟨fragment, h, rfl⟩
    · rintro ⟨_, h, _⟩
      exact h

/-! ## Markdown prose -/

/-- The fence run of a line: after leading whitespace, three or more backticks or tildes, with
the character, the count and the trimmed text after the run. -/
def fenceRun? (line : String) : Option (Char × Nat × String) := do
  let chars := line.toList.dropWhile Char.isWhitespace
  let first ← chars.head?
  guard (first == '`' || first == '~')
  let count := (chars.takeWhile (· == first)).length
  guard (count >= 3)
  return (first, count, String.ofList (chars.drop count) |>.trimAscii.toString)

/-- Whether `line` closes a fenced block opened with `minimum` of `character`: a fence run of the
same character, at least as long, with nothing after it. -/
def closingFence (line : String) (character : Char) (minimum : Nat) : Bool :=
  match fenceRun? line with
  | some (found, count, rest) => found == character && count >= minimum && rest.isEmpty
  | none => false

/-- Whether `line` is an ATX heading: after leading spaces, one to six `#` and then a space or the
end of the line. -/
def isHeading (line : String) : Bool :=
  let chars := line.toList.dropWhile (· == ' ')
  let hashes := (chars.takeWhile (· == '#')).length
  1 ≤ hashes && hashes ≤ 6 && (chars.drop hashes).head?.all (· == ' ')

/-- The index of the `closer` that matches an opener already read, counting nested pairs;
`depth` is the number of nested openers still open. -/
def closeIndex (opener closer : Char) : Nat → List Char → Option Nat
  | _, [] => none
  | depth, c :: rest =>
    if c == closer then
      match depth with
      | 0 => some 0
      | d + 1 => (closeIndex opener closer d rest).map (· + 1)
    else (closeIndex opener closer (if c == opener then depth + 1 else depth) rest).map (· + 1)

/-- The destination a link's raw target names: the text in `<…>`, or the text up to the first
whitespace (which a title follows). -/
def destinationOf (raw : List Char) : String :=
  match raw.dropWhile Char.isWhitespace with
  | '<' :: rest => String.ofList (rest.takeWhile (· != '>'))
  | chars => String.ofList (chars.takeWhile (!Char.isWhitespace ·))

/-- Whether a link's raw target is a destination alone, or a destination and a quoted title, on
one line. Any other text in a link's parentheses or after a definition's colon is prose, so it is
not skipped as a destination. -/
def validTarget (raw : List Char) : Bool :=
  let chars := raw.dropWhile Char.isWhitespace
  let destination := match chars with
    | '<' :: rest => (rest.takeWhile (· != '>')).length + 2
    | _ => (chars.takeWhile (!Char.isWhitespace ·)).length
  let after := (chars.drop destination).dropWhile Char.isWhitespace
  !raw.contains '\n' && (after.isEmpty || after.head? == some '"' || after.head? == some '\'')

/-- A reference label as it is matched: trimmed and lowercase. -/
def label (chars : List Char) : String := (String.ofList chars).trimAscii.toString.toLower

/-- The label and destination of a link reference definition line, `[label]: destination`. -/
def referenceDefinition? (line : String) : Option (String × String) :=
  match line.toList.dropWhile (· == ' ') with
  | '[' :: rest =>
    (closeIndex '[' ']' 0 rest).bind fun i =>
      match rest.drop (i + 1) with
      | ':' :: target =>
        let destination := destinationOf target
        if i == 0 || destination.isEmpty || !validTarget target then none
        else some (label (rest.take i), destination)
      | _ => none
  | _ => none

/-- The open fenced code block after line `line` with text `text`, as the line that opened it and
its fence character and length, when `fence` is the one open before the line. -/
def fenceAfter (line : Nat) (fence : Option (Nat × Char × Nat)) (text : String) :
    Option (Nat × Char × Nat) :=
  match fence with
  | some (opened, character, count) =>
    if closingFence text character count then none else some (opened, character, count)
  | none => (fenceRun? text).map fun (character, count, _) => (line, character, count)

/-- Each line of a document with its 1-based number, or `none` for a line of a fenced code block
(its delimiters included). `fence` is the fenced block open before the first line. -/
def proseLines : Nat → Option (Nat × Char × Nat) → List String → List (Nat × Option String)
  | _, _, [] => []
  | line, fence, text :: rest =>
    let after := fenceAfter line fence text
    (line, if fence.isNone && after.isNone then some text else none) ::
      proseLines (line + 1) after rest

/-- The line that opens a fenced code block the document never closes, if there is one. Everything
after it is code, so the document's prose is refused instead of read short. -/
def unclosedFence (lines : List String) : Option Nat :=
  ((lines.foldl (fun (acc : Nat × Option (Nat × Char × Nat)) text =>
    (acc.1 + 1, fenceAfter acc.1 acc.2 text)) (1, none)).2).map (·.1)

/-- The link reference definitions of a document's lines outside fenced code blocks. -/
def definitions (lines : List (Nat × Option String)) : List (String × String) :=
  lines.filterMap fun (_, text) => text.bind referenceDefinition?

private def closeBlock (line : Nat) (acc : List String) : List (Nat × String) :=
  if acc.isEmpty then [] else [(line - acc.length, "\n".intercalate acc.reverse)]

/-- The paragraphs of a document: maximal runs of consecutive lines that are not in a fenced code
block, blank, a heading or a link reference definition, each with the line it starts on. `acc`
holds the lines of the paragraph in progress, reversed, which ends before line `line`. -/
def paragraphs : Nat → List String → List (Nat × Option String) → List (Nat × String)
  | line, acc, [] => closeBlock line acc
  | _, acc, (line, none) :: rest => closeBlock line acc ++ paragraphs (line + 1) [] rest
  | _, acc, (line, some text) :: rest =>
    if text.toList.all Char.isWhitespace || isHeading text ||
        (referenceDefinition? text).isSome then
      closeBlock line acc ++ paragraphs (line + 1) [] rest
    else paragraphs (line + 1) (text :: acc) rest

/-- One piece of a paragraph. The pieces' raw texts, in order, are the paragraph. -/
inductive Piece where
  /-- Prose, with the destination of the link whose text it lies in, if any. -/
  | prose (text : String) (link : Option String)
  /-- Text that is not prose: a code span, a link's brackets and destination, an HTML tag or
  comment, an autolink or a bare URL. -/
  | skip (raw : String)
  deriving DecidableEq, Repr

/-- The text of the paragraph that the piece stands for. -/
def Piece.raw : Piece → String
  | .prose text _ => text
  | .skip raw => raw

private def flush (link : Option String) (acc : List Char) : List Piece :=
  if acc.isEmpty then [] else [.prose (String.ofList acc.reverse) link]

/-- The number of characters through the end of the first run of exactly `n` backticks; `run` is
the length of the backtick run in progress. -/
def codeClose (n : Nat) : Nat → List Char → Option Nat
  | run, [] => if run == n then some 0 else none
  | run, c :: rest =>
    if c == '`' then (codeClose n (run + 1) rest).map (· + 1)
    else if run == n then some 0
    else (codeClose n 0 rest).map (· + 1)

/-- The number of characters of an HTML comment's text through its `-->`, or through the end of
the text when it is not closed. -/
def commentLength : List Char → Nat
  | '-' :: '-' :: '>' :: _ => 3
  | _ :: rest => commentLength rest + 1
  | [] => 0

/-- The number of characters after a `<` through the end of the HTML comment, tag or autolink
it opens, when it opens one; a tag or autolink closes on its own line. -/
def tagLength (rest : List Char) : Option Nat :=
  match rest with
  | '!' :: '-' :: '-' :: tail => some (3 + commentLength tail)
  | c :: _ =>
    let body := rest.takeWhile (· != '>')
    if (c.isAlpha || c == '/') && body.length < rest.length && !body.contains '\n' then
      some (body.length + 1)
    else none
  | [] => none

/-- Whether `chars` starts a bare URL. -/
def startsUrl (chars : List Char) : Bool :=
  "https://".toList.isPrefixOf chars || "http://".toList.isPrefixOf chars

/-- The length of the URL at the head of `chars`: up to whitespace, a bracket, a quote or a
backtick. -/
def urlLength (chars : List Char) : Nat :=
  (chars.takeWhile fun c => !(c.isWhitespace || c == '<' || c == '>' || c == '(' || c == ')' ||
    c == '[' || c == ']' || c == '`' || c == '"')).length

/-- The link that the text after a `[` continues, as the length of its text, the length of what
follows the text (from its `]` through the destination or label) and its destination: an inline
link `[text](destination)`, or a reference `[text][label]`, `[text][]` or `[text]` whose label
`definitions` defines. -/
def linkAt (definitions : List (String × String)) (rest : List Char) :
    Option (Nat × Nat × String) :=
  (closeIndex '[' ']' 0 rest).bind fun i =>
    let text := rest.take i
    match rest.drop (i + 1) with
    | '(' :: tail =>
      (closeIndex '(' ')' 0 tail).bind fun j =>
        if validTarget (tail.take j) then some (i, j + 3, destinationOf (tail.take j)) else none
    | '[' :: tail =>
      (closeIndex '[' ']' 0 tail).bind fun j =>
        (definitions.lookup (label (if j == 0 then text else tail.take j))).map fun destination =>
          (i, j + 3, destination)
    | _ => (definitions.lookup (label text)).map fun destination => (i, 1, destination)

/-- The pieces of a paragraph. `link` is the destination of the link whose text is being read and
`acc` the prose since the last piece, reversed; the first argument bounds the steps and is at
least the paragraph's length. A backslash keeps the character after it as text. -/
def scanInline (definitions : List (String × String)) :
    Nat → Option String → List Char → List Char → List Piece
  | 0, link, _, acc => flush link acc
  | _, link, [], acc => flush link acc
  | fuel + 1, link, c :: rest, acc =>
    let skip (n : Nat) : List Piece := flush link acc ++
      Piece.skip (String.ofList ((c :: rest).take n)) ::
        scanInline definitions fuel link ((c :: rest).drop n) []
    if c == '\\' then
      match rest with
      | d :: tail => scanInline definitions fuel link tail (d :: c :: acc)
      | [] => flush link (c :: acc)
    else if c == '`' then
      let n := 1 + (rest.takeWhile (· == '`')).length
      match codeClose n 0 (rest.drop (n - 1)) with
      | some k => skip (n + k)
      | none => scanInline definitions fuel link (rest.drop (n - 1)) (List.replicate n '`' ++ acc)
    else if c == '<' then
      match tagLength rest with
      | some k => skip (k + 1)
      | none => scanInline definitions fuel link rest (c :: acc)
    else if startsUrl (c :: rest) then skip (urlLength (c :: rest))
    else if c == '[' && link.isNone then
      match linkAt definitions rest with
      | some (textLength, tailLength, destination) =>
        flush link acc ++ Piece.skip "[" ::
          (scanInline definitions fuel (some destination) (rest.take textLength) [] ++
            Piece.skip (String.ofList ((rest.drop textLength).take tailLength)) ::
              scanInline definitions fuel none (rest.drop (textLength + tailLength)) [])
      | none => scanInline definitions fuel link rest (c :: acc)
    else scanInline definitions fuel link rest (c :: acc)

/-- The pieces of the paragraph `text`. -/
def pieces (definitions : List (String × String)) (text : String) : List Piece :=
  scanInline definitions (text.length + 1) none text.toList []

/-- The prose runs of `pieces`, a paragraph that starts on line `line`. -/
def runsOf (line : Nat) (pieces : List Piece) : List Run :=
  (pieces.foldl (fun (acc : Nat × List Run) piece =>
    (acc.1 + newlines piece.raw,
      match piece with
      | .prose text link => ⟨acc.1, text, link⟩ :: acc.2
      | .skip _ => acc.2)) (line, [])).2.reverse

/-- The prose of a Markdown document: for each paragraph outside fenced code blocks, headings and
link reference definitions, its text outside code spans, link destinations, HTML tags and
comments, autolinks and bare URLs. -/
def markdownRuns (text : String) : List Run :=
  let lines := proseLines 1 none (text.splitOn "\n")
  let defined := definitions lines
  (paragraphs 1 [] lines).flatMap fun (line, paragraph) => runsOf line (pieces defined paragraph)

/-- What the Markdown document `text` of `main` is refused for: a fenced code block that is never
closed, and each rule ID in its prose that is not a link to its development page, reported with
`file`, its line and the ID. -/
def markdownErrors (file text : String) : List String :=
  (match unclosedFence (text.splitOn "\n") with
    | some line => [s!"{file}:{line}: the fenced code block is not closed, so the text after it \
        is not read as prose"]
    | none => []) ++
  (bareMentions developmentTarget (markdownRuns text)).map (·.describe file)

/-- The Markdown check reports nothing exactly when every fenced code block is closed and every
rule-ID token in the document's prose is a registered rule ID linked to its development page. -/
theorem markdownErrors_nil_iff (file text : String) :
    markdownErrors file text = [] ↔ unclosedFence (text.splitOn "\n") = none ∧
      ∀ run ∈ markdownRuns text, ∀ m ∈ run.mentions, m.Linked developmentTarget := by
  unfold markdownErrors
  cases unclosedFence (text.splitOn "\n") <;> simp [bareMentions_nil_iff]

/-! ## HTML prose -/

/-- The elements whose text is not prose: code and sample output, the document title and
headings. The text of `script` and `style` elements is never read. -/
def exemptElement (name : String) : Bool :=
  ["code", "pre", "samp", "kbd", "title", "h1", "h2", "h3", "h4", "h5", "h6"].contains name

/-- The state of the prose scan of an HTML page. -/
structure HtmlScan where
  /-- Whether the scan is in markup, a comment or a raw-text element. -/
  mode : ScanMode
  /-- The number of open exempt elements. -/
  exempt : Nat
  /-- The `href` of the open `a` element, if there is one. -/
  link : Option String
  /-- The 1-based line at the scan position. -/
  line : Nat
  /-- The runs found so far, last first. -/
  runs : List Run

private def HtmlScan.withText (s : HtmlScan) (line : Nat) (text : String) : List Run :=
  if s.exempt == 0 && !text.isEmpty then ⟨line, text, s.link⟩ :: s.runs else s.runs

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '\x0c'

/-- Read `chunk`, the text between one `<` and the next: the tag, comment or raw text it
continues, and then the text after it. -/
def htmlStep (s : HtmlScan) (chunk : String) : HtmlScan :=
  let next := s.line + newlines chunk
  let body := tagBody chunk.toList none
  let text := String.ofList (chunk.toList.drop (body.length + 1))
  let textLine := s.line + body.count '\n'
  let afterComment : Option (Nat × String) :=
    match chunk.splitOn "-->" with
    | before :: after :: rest => some (s.line + newlines before, "-->".intercalate (after :: rest))
    | _ => none
  let endComment (s : HtmlScan) : HtmlScan :=
    match afterComment with
    | some (line, text) => { s with mode := .markup, line := next, runs := s.withText line text }
    | none => { s with mode := .comment, line := next }
  let endTag (s : HtmlScan) : HtmlScan :=
    let name := (String.ofList ((body.drop 1).takeWhile fun c => !isSpace c)).toLower
    let closed := { s with
      mode := .markup,
      exempt := if exemptElement name then s.exempt - 1 else s.exempt,
      link := if name == "a" then none else s.link }
    { closed with line := next, runs := closed.withText textLine text }
  match s.mode with
  | .comment => endComment s
  | .raw element =>
    if chunk.toLower.startsWith ("/" ++ element) then endTag s else { s with line := next }
  | .markup =>
    if chunk.startsWith "!--" then endComment s
    else if chunk.startsWith "/" then endTag s
    else if chunk.startsWith "!" || chunk.startsWith "?" then
      { s with line := next, runs := s.withText textLine text }
    else
      let name := (String.ofList (body.takeWhile fun c => !(isSpace c || c == '/'))).toLower
      if name.isEmpty then { s with line := next, runs := s.withText s.line ("<" ++ chunk) } else
      let rest := body.drop name.length
      let tag : Tag := ⟨name, parseAttributes (rest.length + 1) rest⟩
      if name == "script" || name == "style" then { s with mode := .raw name, line := next } else
      let opened := { s with
        exempt := if exemptElement name && body.getLast? != some '/' then s.exempt + 1
          else s.exempt,
        link := if name == "a" then tag.get? "href" else s.link }
      { opened with line := next, runs := opened.withText textLine text }

/-- The prose scan of a whole HTML page. -/
def htmlScan (html : String) : HtmlScan :=
  let start : HtmlScan := ⟨.markup, 0, none, 1, []⟩
  match html.splitOn "<" with
  | [] => start
  | first :: chunks =>
    chunks.foldl htmlStep { start with line := 1 + newlines first, runs := start.withText 1 first }

/-- The prose of an HTML page: its text outside `exemptElement` elements, comments and `script`
and `style` elements, each run with the `href` of the `a` element it lies in. -/
def htmlRuns (html : String) : List Run := (htmlScan html).runs.reverse

/-- Whether the page's scan ends in markup with every exempt element closed. An unclosed `code`
element, comment or script would hide the text after it, so such a page is refused instead of
read short. -/
def htmlClosed (html : String) : Bool :=
  match (htmlScan html).mode with
  | .markup => (htmlScan html).exempt == 0
  | _ => false

/-- What the rendered page `html` at artifact path `path` is refused for: an element, comment or
script that hides text and is never closed, and each rule ID in its prose that is not a link to
its page in the edition whose artifact root is `root`, reported with the path, its line and the
ID. -/
def htmlErrors (root path html : String) : List String :=
  (if htmlClosed html then [] else
    [s!"{path}: a code, title or heading element, a comment or a script is not closed, so the \
      text after it is not read as prose"]) ++
  (bareMentions (pageTarget root (Page.ofHtml path html)) (htmlRuns html)).map (·.describe path)

/-- The page check reports nothing exactly when the page's scan is closed and every rule-ID token
in the page's prose is a registered rule ID linked to its page under `root`. -/
theorem htmlErrors_nil_iff (root path html : String) :
    htmlErrors root path html = [] ↔ htmlClosed html = true ∧
      ∀ run ∈ htmlRuns html, ∀ m ∈ run.mentions,
        m.Linked (pageTarget root (Page.ofHtml path html)) := by
  unfold htmlErrors
  cases htmlClosed html <;> simp [bareMentions_nil_iff]

/-! ## Generated prose -/

/-- Rule `id`'s ID as a link to its page, relative to the edition root (`RuleId.route`), in the
link syntax that Markdown and Verso share. A generated page resolves it through its
`<base href>`, so the same page links within whichever edition it is published in. -/
def relativeCitation (id : RuleId) : String := "[" ++ id.spelling ++ "](" ++ id.route ++ ")"

/-- `text` with each registered rule ID replaced by `rule` of it and all other text passed
through `plain`. -/
def rewriteIds (plain : String → String) (rule : RuleId → String) (text : String) : String :=
  String.join ((splitTokens none 0 [] text.toList).map fun
    | .inl between => plain between
    | .inr token => match RuleId.parse? token with
      | some id => rule id
      | none => plain token)

/-- Generated Verso prose with each registered rule ID in prose made a link to its page in the
same edition (`relativeCitation`). Code spans, existing links and URLs are kept as written. -/
def linkVerso (text : String) : String :=
  String.join ((pieces [] text).map fun
    | .prose between none => rewriteIds id relativeCitation between
    | piece => piece.raw)

/-! Evaluated controls (observations of the compiled scanners, not proofs). A bare ID in prose is
refused in both formats, with its file and line; an unregistered ID and a link to another page are
refused; and each exempt construct is accepted: fenced and inline code, pasted tool output, a rule
index table whose IDs are links, Lean identifiers written as code, and headings. -/
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Intro.\n\nBuild warnings are\nreported as RG2003 here.\n" ==
  ["a.md:4: RG2003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "See RG9999." == ["a.md:1: RG9999 is not a registered rule ID"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
  ("See [RG1001](" ++ Edition.dev.url RuleId.proofHole.route ++ ").") != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See " ++ "[RG1001](" ++ Edition.dev.url RuleId.projectAxiom.route ++
  "), [RG1002] and [RG1003][].\n\n[RG1002]: " ++ Edition.dev.url RuleId.proofHole.route ++
  "\n[RG1003]: " ++ Edition.dev.url RuleId.unknownAxiom.route ++ "#RG1003-fix\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "```lean\ntheorem RG1001 : True := trivial\n```\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Run `lake exe\nregula explain RG1005` and ``Regula.RG1001``.\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
  "~~~text\nRG1001 [violation; freshFile]: reflexive\n  rule: https://x/rules/RG1001/\n~~~\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("| Rule | Checks |\n| --- | --- |\n| [`RG1001`](" ++
  Edition.dev.url RuleId.projectAxiom.route ++ ") | axioms |\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "## RG1001 in a heading\n\nSee <https://x/rules/RG1001/> and \
  https://x/rules/RG1002/, in xRG1001, RG10012 and RG1001_a.\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><p>It is\nreported as RG2003.</p>" ==
  ["dev/enforcement/index.html:2: RG2003 is a bare rule ID in prose; make it a link to its rule \
    page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><p>See <a href=\"rules/RG2003/\">RG2003</a> and \
      <a href=\"rules/RG2003/#RG2003-fix\">the RG2003 fix</a>.</p>" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><p><a href=\"rules/RG2002/\">RG2003</a> and \
      <a href=\"https://rbeauchamp.github.io/regula/dev/rules/RG2003/\">RG2003</a></p>" != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/rules/RG1001/index.html"
    "<base href=\"./../../\"><title>RG1001: Axioms</title><h1>RG1001: Axioms</h1>\
      <p><code>RG1001</code> <code class=\"hl lean\">Regula.RG1001</code></p>\
      <pre>RG1001 [violation]</pre><script>var a = \"RG1001\";</script><!-- RG1001 -->\
      <table><tr><th><a href=\"rules/RG1002/\"><code>RG1002</code></a></th>\
      <td><a href=\"rules/RG1002/\">RG1002</a></td></tr></table>" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "[note](see RG1001 below) and <b\nRG1002>.\n\n[x]: see RG1003\n" ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:2: RG1002 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:4: RG1003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Text.\n\n```text\nRG1001\n" ==
  ["a.md:3: the fenced code block is not closed, so the text after it is not read as prose"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/index.html" "<p>Text <code>x</p><p>RG1001</p>" != []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard linkVerso "RG2003 rejects `RG1002` code, [RG1005's page](rules/RG1005/) and \
    https://x/rules/RG1001/; RG9999 stays." ==
  "[RG2003](rules/RG2003/) rejects `RG1002` code, [RG1005's page](rules/RG1005/) and \
    https://x/rules/RG1001/; RG9999 stays."
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "" "6-code-organization/index.html"
    ("<base href=\"./../\"><p><a href=\"" ++ RuleId.sourceBuild.route ++ "\">RG2003</a></p>") == []

end Regula.Prose
