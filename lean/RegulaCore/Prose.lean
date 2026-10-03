import RegulaCore.Site

/-! # Rule IDs in prose

Every rule ID that a document mentions in prose is a link to that rule's page. This module
defines what prose is, as a property of a document's structure, decides whether a document has a
rule ID in prose that is not such a link, and rewrites generated prose so that it has none.

## Main declarations

- `tokenAt`, `splitTokens`: a rule-ID token is `RG` and four digits with no ASCII letter or digit
  directly before or after it, so emphasis such as `_RG2003_` does not hide one.
- `Run`, `Mention`, `Run.mentions`: a run is a maximal piece of prose with the destination of the
  link it lies in, if any; a mention is one token of a run.
- `Mention.Linked`, `bareMentions`, `bareMentions_nil_iff`, `checked_bareMentions`: a mention is
  linked when its token is a registered rule ID and its link's destination is that rule's page;
  the executed check returns nothing exactly when every mention of every run is linked.
- `developmentTarget`, `pageTarget`, `pageTarget_iff`: the page of a rule for a Markdown document
  of `main` (the development page, `Edition.url`, the definition `helpUrl` and `citation` use) and
  for a rendered page of an edition (the rule's page file of that edition).
- `markdownRuns`, `htmlRuns`, `ownPage`: the prose of a Markdown document and of an HTML page, and
  the one place a rule ID is not written as a link, a rule page's own title and top heading.
- `markdownErrors`, `htmlErrors`, `markdownErrors_nil_iff`, `htmlErrors_nil_iff`: the two executed
  document checks, each reporting the file, the line and the ID.
- `relativeCitation`, `rewriteIds`, `linkIds`, `linkVerso`: the link a generated page gives a
  rule, relative to its edition's root (`RuleId.route`), and the rewriting of generated prose that
  inserts a link.

## What prose is

In a Markdown document, prose is the text outside fenced code blocks (`fenceOpen?`), code spans,
link reference definitions, link destinations, HTML tags and comments, autolinks and bare URLs.
In an HTML page, prose is the text outside the `code`, `pre`, `script` and `style` elements
(`exemptElement`). Pasted tool output is a fenced block or a `pre` element; a Lean identifier is
code. A rule table that is the index of rule pages names each rule as a link to its page, so its
IDs are linked mentions. A heading is prose in both formats. The one rule ID that is not written
as a link is a rule page's own, in that page's `title` and `h1`, because a page cannot usefully
link to itself (`ownPage`): those two elements are read as text linked to the page they name.

## Boundaries

`bareMentions_nil_iff` is about the runs it is given. `markdownRuns` and `htmlRuns` are small
scanners for this repository's documents and the builder's own output, not Markdown or HTML
parsers.

The Markdown check's contract: it does not imitate CommonMark. It reads a supported subset of
Markdown, scans that subset exactly as these definitions say, and refuses every document outside
it, with the line, the construct and how to write it inside the subset (`refusals`,
`Refusal.message`). A construct it does not model is refused, not modelled.

The subset (`blocks`): fenced code blocks opened by a fence run after at most three spaces
(`fenceOpen?`), whose lines are indented at least as far as the fence and which close at a fence
run of the same character at least as long with nothing after it; ATX headings; comments alone on
a line; tables, a header row, a delimiter row (`delimiterRow`) and the rows after them to the
next blank line, fence, heading or comment line, each row split into cells at every `|` that no
backslash escapes (`cells`); link reference definitions after at most three spaces, whose label
does not start with `^`, at the start of the document or directly after a blank line, a fenced
code block, a heading, a comment line or another definition; and paragraphs of every other line.
A paragraph ends before a blank line, a fence, a heading, a comment line, a table's header row, a
line that starts with a list marker, a footnote marker (`[^label]:`) or `>` or holds only `-`,
`=`, `*` or `_` (`interrupts`), and, when its first line is indented four spaces or more, before
the first line that is not. A footnote definition is a container like a list item, whose text is
prose. In each paragraph, heading and cell, `scanInline` reads code spans, links whose text holds
no `[`, `<` or open code span and whose target is well formed (`validTarget`), HTML tags on one
line, comments that close in their paragraph other than `<!-->`, `<!--->` and one whose text
holds `--` or ends in `-`, autolinks and bare URLs; every other character is prose.

Refused (`Refusal`): a fenced code block that is never closed; a fence run indented four spaces
or more; a line of a fenced code block with fewer leading spaces than its fence; a line whose text
after its list markers, footnote markers or `>` starts with a fence run, an HTML tag, a comment, a
table's delimiter row or a link reference definition; a link reference definition indented four
spaces or more, or directly after a paragraph line, a table row or a line that ends a paragraph; a
line that starts with an HTML tag, processing instruction or declaration other than an autolink; a
line that starts with a comment that is not all of it; a numeric character reference; a code span
left open where a paragraph ends at an `interrupts` line, a table's header row or the end of an
indented first line's paragraph; and a code span, link or HTML tag that a `|` splits in a table
row (`splitCell`). That GitHub renders a document of the subset as these definitions read it is
the check's premise, observed in the controls below, not proved.

In HTML, an element, comment or script that is never closed would hide the text after it, so
`htmlErrors` refuses such a page; an element closed and reopened out of order is not detected.
`linkIds` rewrites the prose `scanInline` finds; that its output has no bare rule ID is
established by `htmlErrors` on the rendered pages and `markdownErrors` on the committed agent
skill, not by a theorem about the rewriting.
-/

namespace Regula.Prose

open Regula.Site

/-! ## Rule-ID tokens -/

/-- A character that continues a word: an ASCII letter or digit. `_` is not one, so a rule ID in
`_` emphasis is a token; an identifier that contains a rule ID is written as code. -/
def isWordChar (c : Char) : Bool := c.isAlphanum

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

/-- The index of the `closer` that matches an opener already read, counting nested pairs and
skipping each character a backslash escapes; `depth` is the number of nested openers still open. -/
def closeIndex (opener closer : Char) : Nat → List Char → Option Nat
  | _, [] => none
  | depth, '\\' :: _ :: rest => (closeIndex opener closer depth rest).map (· + 2)
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

/-- Whether the parentheses of `chars` are balanced, none closing before it opens. -/
def balanced (chars : List Char) : Bool :=
  chars.foldl (fun (depth : Option Nat) c => depth.bind fun d =>
    if c == '(' then some (d + 1) else if c == ')' then (if d == 0 then none else some (d - 1))
    else some d) (some 0) == some 0

/-- Whether a link's raw target is, on one line, a destination alone or a destination, whitespace
and a title in `"` or `'` that its quote closes with only whitespace after it. A destination is
`<`, text with no `<` or `>` and `>`, or text with no whitespace whose parentheses are balanced
(`balanced`). Any other text in a link's parentheses or after a definition's colon is prose, so it
is not skipped as a destination. -/
def validTarget (raw : List Char) : Bool :=
  let chars := raw.dropWhile Char.isWhitespace
  let after : Option (List Char) := match chars with
    | '<' :: rest =>
      let inside := rest.takeWhile (· != '>')
      if inside.length < rest.length && !inside.contains '<' then
        some (rest.drop (inside.length + 1))
      else none
    | _ =>
      let destination := chars.takeWhile (!Char.isWhitespace ·)
      if balanced destination then some (chars.drop destination.length) else none
  !raw.contains '\n' && match after with
    | none => false
    | some after => match after.dropWhile Char.isWhitespace with
      | [] => true
      | quote :: title => after.head?.any Char.isWhitespace && (quote == '"' || quote == '\'') &&
        match title.dropWhile (· != quote) with
        | _ :: tail => tail.all Char.isWhitespace
        | [] => false

/-- A reference label as it is matched: trimmed and lowercase. -/
def label (chars : List Char) : String := (String.ofList chars).trimAscii.toString.toLower

/-- The label and destination of a link reference definition line, `[label]: destination`, after
at most three spaces. A label that starts with `^` is a footnote's, whose definition is prose. -/
def referenceDefinition? (line : String) : Option (String × String) :=
  let indent := (line.toList.takeWhile (· == ' ')).length
  if indent > 3 then none else
  match line.toList.drop indent with
  | '[' :: rest =>
    (closeIndex '[' ']' 0 rest).bind fun i =>
      match rest.drop (i + 1) with
      | ':' :: target =>
        let destination := destinationOf target
        if i == 0 || rest.head? == some '^' || destination.isEmpty || !validTarget target then none
        else some (label (rest.take i), destination)
      | _ => none
  | _ => none

private def isBlank (c : Char) : Bool := c == ' ' || c == '\t'

private def blank (text : String) : Bool := text.toList.all Char.isWhitespace

/-- Whether `line` is an ATX heading: after at most three spaces, one to six `#` and then a space,
a tab or the end of the line. A heading ends the paragraph before it and is a paragraph of its own.
-/
def isHeading (line : String) : Bool :=
  let indent := (line.toList.takeWhile (· == ' ')).length
  let chars := line.toList.drop indent
  let hashes := (chars.takeWhile (· == '#')).length
  indent ≤ 3 && 1 ≤ hashes && hashes ≤ 6 && (chars.drop hashes).head?.all isBlank

/-- The fenced code block that `line` opens, as its fence character and length: after at most three
spaces, a fence run (`fenceRun?`), with no backtick in the text after a run of backticks. -/
def fenceOpen? (line : String) : Option (Char × Nat) :=
  let indent := (line.toList.takeWhile (· == ' ')).length
  match line.toList.drop indent, fenceRun? line with
  | first :: _, some (character, count, info) =>
    if indent ≤ 3 && first == character && !(character == '`' && info.toList.contains '`') then
      some (character, count)
    else none
  | _, _ => none

/-- Whether `line` is indented four spaces or more, or by a tab. -/
def indented (line : String) : Bool :=
  let leading := line.toList.takeWhile isBlank
  leading.contains '\t' || 4 ≤ leading.length

/-- Whether `line` is a fence run indented four spaces or more, or by a tab. -/
def indentedFence (line : String) : Bool := (fenceRun? line).isSome && indented line

/-- `chars` after its leading spaces and tabs and the block-quote `>`, list markers (`-`, `*` or
`+`, or one to nine digits and `.` or `)`, each followed by a space or a tab) and footnote markers
(`[^label]:`) that open it, with whether it had any. `fuel` bounds the markers read. -/
def afterContainers : Nat → Bool → List Char → Bool × List Char
  | 0, found, chars => (found, chars)
  | fuel + 1, found, chars =>
    let chars := chars.dropWhile isBlank
    let digits := chars.takeWhile Char.isDigit
    match chars with
    | '>' :: rest => afterContainers fuel true rest
    | '[' :: '^' :: rest =>
      let name := rest.takeWhile (· != ']')
      match rest.drop name.length with
      | ']' :: ':' :: after =>
        if name.isEmpty then (found, chars) else afterContainers fuel true after
      | _ => (found, chars)
    | c :: d :: rest =>
      if (c == '-' || c == '*' || c == '+') && isBlank d then afterContainers fuel true rest
      else match chars.drop digits.length with
        | m :: d :: rest =>
          if 1 ≤ digits.length && digits.length ≤ 9 && (m == '.' || m == ')') && isBlank d then
            afterContainers fuel true rest
          else (found, chars)
        | _ => (found, chars)
    | _ => (found, chars)

/-- Whether `chars` starts with an autolink: `<`, a scheme of two to 32 letters, digits, `+`, `.`
or `-` that starts with a letter, `:` and then no space, `<` or `>` before a `>`. -/
def startsAutolink (chars : List Char) : Bool :=
  match chars with
  | '<' :: rest =>
    let scheme := rest.takeWhile fun c => c.isAlphanum || c == '+' || c == '.' || c == '-'
    rest.head?.any Char.isAlpha && 2 ≤ scheme.length && scheme.length ≤ 32 &&
      match rest.drop scheme.length with
      | ':' :: link =>
        let target := link.takeWhile (· != '>')
        target.length < link.length && !target.any fun c => c.isWhitespace || c == '<'
      | _ => false
  | _ => false

/-- Whether `chars` is one HTML comment and nothing after it but spaces or tabs. -/
def wholeComment (chars : List Char) : Bool :=
  match chars with
  | '<' :: '!' :: '-' :: '-' :: rest =>
    match (String.ofList rest).splitOn "-->" with
    | _ :: after :: more => more.isEmpty && after.toList.all isBlank
    | _ => false
  | _ => false

/-- A construct outside the subset of Markdown that the check reads, for which a document is
refused. -/
inductive Refusal where
  /-- A fenced code block that the document never closes. -/
  | unclosedFence
  /-- A fence run indented four spaces or more, or by a tab. -/
  | indentedFence
  /-- A line of a fenced code block with fewer leading spaces than its fence. -/
  | shallowFenceLine
  /-- A line whose text after its list markers, footnote markers or `>` starts with a fence run, an
  HTML tag, a comment, a table's delimiter row or a link reference definition, or a link reference
  definition indented four spaces or more. -/
  | containedBlock
  /-- A line that starts with an HTML tag, processing instruction or declaration. -/
  | htmlLine
  /-- A line that starts with a comment that is not all of it. -/
  | partialComment
  /-- A numeric character reference. -/
  | characterReference
  /-- A code span left open where the scanner ends a paragraph (`interrupts`, a table's header
  row, the end of a paragraph whose first line is indented four spaces or more). -/
  | openCodeSpan
  /-- A line that is a link reference definition where the scanner does not read one: after a
  paragraph line, a table row or a line that ends a paragraph. -/
  | strayDefinition
  /-- A code span, link or HTML tag that a `|` splits in a table row. -/
  | splitTableCell
  deriving DecidableEq, Repr

/-- What a refusal reports: the construct, and how to write it inside the subset. -/
def Refusal.message (r : Refusal) : String :=
  let (construct, remedy) : String × String := match r with
    | .unclosedFence => ("a fenced code block that is never closed",
      "close it with a fence run of its character, at least as long, alone on its line")
    | .indentedFence => ("a fence run indented four spaces or more",
      "indent a fence at most three spaces")
    | .shallowFenceLine =>
      ("a line of a fenced code block with fewer leading spaces than its fence",
      "indent every line of the block at least as far as its fence")
    | .containedBlock =>
      ("a line whose text after its list markers, footnote markers or `>` starts with a fence run, \
        an HTML tag, a comment, a table's delimiter row or a link reference definition, or a link \
        reference definition indented four spaces or more",
      "start a fenced code block or a table on a line of its own, indented as the list item's text \
        and outside any block quote, put a link reference definition at the end of the document \
        outside any list or block quote, and write the rest in Markdown")
    | .htmlLine => ("a line that starts with an HTML tag, processing instruction or declaration",
      "write it in Markdown, or start the line with text")
    | .partialComment => ("a line that starts with a comment that is not all of it",
      "put each comment on a line of its own, opened and closed there")
    | .characterReference => ("a numeric character reference", "write the character itself")
    | .openCodeSpan => ("a code span left open before a line that ends the paragraph here (a list \
        marker, a footnote marker, `>`, a line of only `-`, `=`, `*` or `_`, a table's header row, \
        or the first less indented line after a paragraph indented four spaces or more)",
      "close the code span before that line")
    | .strayDefinition => ("a link reference definition directly after a paragraph line, a table \
        row or a line that ends a paragraph, where the scanner reads it as prose",
      "put each link reference definition after a blank line, at the end of the document")
    | .splitTableCell => ("a code span, link or HTML tag that a `|` splits in a table row",
      "escape the `|` as `\\|` or keep the construct in one cell")
  "unsupported Markdown construct: " ++ construct ++ "; " ++ remedy

/-- Whether `line` is a table's delimiter row: only `|`, `:`, `-` and whitespace, with a `|` and a
`-`. -/
def delimiterRow (line : String) : Bool :=
  let chars := line.toList
  chars.contains '|' && chars.contains '-' &&
    chars.all fun c => c == '|' || c == ':' || c == '-' || c.isWhitespace

/-- The construct outside the subset that `line`, outside a fenced code block, uses, if it uses
one: a fence run indented four spaces or more; text after list markers, footnote markers or `>`
that starts with a fence run, an HTML tag, a comment, a table's delimiter row (`delimiterRow`) or a
link reference definition, or a link reference definition indented four spaces or more; a line
that starts with an HTML tag, processing instruction or declaration, other than an autolink; a
line that starts with a comment that is not all of it; or a numeric character reference. -/
def unsupported? (line : String) : Option Refusal :=
  let chars := line.toList
  let (contained, content) := afterContainers chars.length false chars
  let html := match content with
    | '<' :: c :: _ => (c.isAlpha || c == '/' || c == '?' || c == '!') && !startsAutolink content
    | _ => false
  if indentedFence line then some .indentedFence
  else if contained && ((fenceRun? (String.ofList content)).isSome || html ||
      delimiterRow (String.ofList content) ||
      (referenceDefinition? (String.ofList content)).isSome) ||
      (indented line && (referenceDefinition? (String.ofList content)).isSome) then
    some .containedBlock
  else if html && !"<!--".toList.isPrefixOf content then some .htmlLine
  else if html && !wholeComment content then some .partialComment
  else if (line.splitOn "&#").length > 1 then some .characterReference
  else none

/-- Whether `line` ends the paragraph before it: a block quote, a list item or a footnote definition
(`afterContainers`), or a line of only `-`, `=`, `*`, `_`, spaces and tabs. -/
def interrupts (line : String) : Bool :=
  let chars := line.toList.dropWhile isBlank
  (afterContainers chars.length false chars).1 ||
    (!chars.isEmpty && chars.all fun c => c == '-' || c == '=' || c == '*' || c == '_' || isBlank c)

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

/-- Whether the backtick runs of `chars` pair up within it as `scanInline` pairs them: each run
that no backslash escapes, outside a code span, closes at a later run of the same length
(`codeClose`). `fuel` bounds the characters read. -/
def codeBalanced : Nat → List Char → Bool
  | _, [] => true
  | 0, chars => !chars.contains '`'
  | fuel + 1, '\\' :: _ :: rest => codeBalanced fuel rest
  | fuel + 1, '`' :: rest =>
    let n := 1 + (rest.takeWhile (· == '`')).length
    match codeClose n 0 (rest.drop (n - 1)) with
    | some k => codeBalanced fuel ((rest.drop (n - 1)).drop k)
    | none => false
  | fuel + 1, _ :: rest => codeBalanced fuel rest

/-- The number of characters of an HTML comment's text through its `-->`, when the text closes
it. -/
def commentLength : List Char → Option Nat
  | '-' :: '-' :: '>' :: _ => some 3
  | _ :: rest => (commentLength rest).map (· + 1)
  | [] => none

/-- The text after the attributes at the head of `chars`: each an attribute name after spaces or
tabs, with an optional `=` and a value, quoted or unquoted (the attribute grammar of CommonMark
§6.6), or `none` when a value is malformed. `fuel` bounds the attributes read. -/
def afterAttributes : Nat → List Char → Option (List Char)
  | 0, chars => some chars
  | fuel + 1, chars =>
    let spaced := chars.dropWhile isBlank
    match spaced with
    | [] => some chars
    | c :: _ =>
      if spaced.length == chars.length || !(c.isAlpha || c == '_' || c == ':') then some chars
      else
        let afterName := spaced.dropWhile fun c =>
          c.isAlphanum || c == '_' || c == '.' || c == ':' || c == '-'
        match afterName.dropWhile isBlank with
        | '=' :: value =>
          match value.dropWhile isBlank with
          | [] => none
          | q :: v =>
            if q == '"' || q == '\'' then
              match v.dropWhile (· != q) with
              | _ :: after => afterAttributes fuel after
              | [] => none
            else
              let n := ((q :: v).takeWhile fun c =>
                !(isBlank c || "\"'=<>`".toList.contains c)).length
              if n == 0 then none else afterAttributes fuel ((q :: v).drop n)
        | _ => afterAttributes fuel afterName

/-- Whether `body`, the text between a `<` and the next `>`, is an open tag, a closing tag or a
URI autolink, in the grammar of CommonMark §6.5 and §6.6. -/
def inlineTag (body : List Char) : Bool :=
  let tagName (chars : List Char) := chars.takeWhile fun c => c.isAlphanum || c == '-'
  match body with
  | '/' :: rest => rest.head?.any Char.isAlpha && (rest.drop (tagName rest).length).all isBlank
  | c :: _ =>
    let name := tagName body
    let after := body.drop name.length
    c.isAlpha && match after with
      | ':' :: link =>
        2 ≤ name.length && name.length ≤ 32 && !link.any fun c => c.isWhitespace || c == '<'
      | _ => match afterAttributes (after.length + 1) after with
        | some tail => match tail.dropWhile isBlank with
          | [] | ['/'] => true
          | _ => false
        | none => false
  | [] => false

/-- The number of characters after a `<` through the end of the HTML comment, tag or autolink
it opens, when it opens one: a comment closes in the rest of its paragraph, and a tag or autolink
(`inlineTag`) is well formed on its own line. Otherwise, as for a comment its paragraph does not
close, a malformed tag or an open tag that spans lines, the `<` is prose. -/
def tagLength (rest : List Char) : Option Nat :=
  match rest with
  | '!' :: '-' :: '-' :: '>' :: _ => none
  | '!' :: '-' :: '-' :: '-' :: '>' :: _ => none
  | '!' :: '-' :: '-' :: tail => (commentLength tail).bind fun k =>
    let text := tail.take (k - 3)
    if ((String.ofList text).splitOn "--").length > 1 || text.getLast? == some '-' then none
    else some (3 + k)
  | _ =>
    let body := rest.takeWhile (· != '>')
    if body.length < rest.length && !body.contains '\n' && inlineTag body then
      some (body.length + 1)
    else none

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
`definitions` defines. Text with a `[`, a `<` or a backtick run that does not close in it
(`codeBalanced`) is not a link's text. -/
def linkAt (definitions : List (String × String)) (rest : List Char) :
    Option (Nat × Nat × String) :=
  (closeIndex '[' ']' 0 rest).bind fun i =>
    let text := rest.take i
    if text.contains '[' || text.contains '<' || !codeBalanced (text.length + 1) text then none
    else
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

/-- Whether `chars` has an `<` that starts what could be an HTML tag or comment (a letter, `/` or
`!` after it) that `tagLength` does not close. -/
def tagUnclosed : List Char → Bool
  | '<' :: c :: rest =>
    ((c.isAlpha || c == '/' || c == '!') && (tagLength (c :: rest)).isNone) ||
      tagUnclosed (c :: rest)
  | _ :: rest => tagUnclosed rest
  | [] => false

/-- The cells of a table row: `chars` split at each `|` that no backslash escapes; `acc` holds the
cell in progress, reversed. -/
def cells : List Char → List Char → List (List Char)
  | acc, [] => [acc.reverse]
  | acc, '\\' :: c :: rest => cells (c :: '\\' :: acc) rest
  | acc, '|' :: rest => acc.reverse :: cells [] rest
  | acc, c :: rest => cells (c :: acc) rest

/-- Whether a cell of a table row holds part of a code span, link or HTML tag that a `|` splits:
a backtick run that does not close in it (`codeBalanced`), a `[` or `]` without its pair, or a
`<` that does not close as a tag or comment. -/
def splitCell (cell : List Char) : Bool :=
  !codeBalanced (cell.length + 1) cell || cell.count '[' != cell.count ']' || tagUnclosed cell

/-- A block of a document. -/
inductive Block where
  /-- A paragraph, a heading or a comment line, with the line it starts on. -/
  | paragraph (line : Nat) (text : String)
  /-- A table, with the line of its header row and its rows in order. -/
  | table (line : Nat) (rows : List String)
  /-- A link reference definition, with its label and destination. -/
  | definition (label destination : String)
  /-- A line for which the document is refused, with the construct. -/
  | refused (line : Nat) (refusal : Refusal)

/-- The block open before a line. -/
inductive Open where
  /-- No block: one can start. -/
  | idle
  /-- A paragraph, with its lines so far, last first. -/
  | paragraph (lines : List String)
  /-- A table, with the line of its header row and its rows so far, last first. -/
  | table (line : Nat) (rows : List String)
  /-- A fenced code block, with the line that opens it, the spaces before its fence and its fence
  character and length. -/
  | fence (line indent : Nat) (character : Char) (count : Nat)

/-- The block that `o` is when it ends before line `line`: a table with a refusal for each row
that a `|` splits a construct of (`splitCell`), and a refusal for a fenced code block that the
document never closes, since everything after it would be code. -/
def Open.close (line : Nat) : Open → List Block
  | .idle => []
  | .paragraph lines => [.paragraph (line - lines.length) ("\n".intercalate lines.reverse)]
  | .table start rows =>
    .table start rows.reverse :: ((List.range rows.length).zip rows.reverse).filterMap
      fun (i, row) =>
        if (cells [] row.toList).any splitCell then some (.refused (start + i) .splitTableCell)
        else none
  | .fence opened _ _ _ => [.refused opened .unclosedFence]

/-- The paragraph `o` when the scanner ends it before line `line` at an `interrupts` line or a
table's header row, refused (`Refusal.openCodeSpan`) when a code span is open there. -/
def Open.cut (line : Nat) (o : Open) : List Block :=
  o.close line ++ match o with
    | .paragraph lines =>
      let text := "\n".intercalate lines.reverse
      if codeBalanced (text.length + 1) text.toList then [] else [.refused line .openCodeSpan]
    | _ => []

/-- The blocks of a document's lines, from line `line` with `o` open before it. A fenced code
block (`fenceOpen?`) closes at a fence run of its character at least as long (`closingFence`); in
it, a fence run indented four spaces or more and a line with fewer leading spaces than its fence
are refused. Outside one, a line of a construct outside the subset is refused (`unsupported?`). A
heading, and a line that is one comment after at most three spaces, is a block of its own. A
paragraph ends before a blank line, a fence, a heading, such a comment line, an `interrupts` line or
a table's delimiter row (`delimiterRow`), whose previous line is the table's header row; a table's
rows run to the next blank line, fence, heading or comment line. A link reference definition is
one (`referenceDefinition?`) only at the start of the document or directly after a blank line, a
fenced code block, a heading, a comment line or another definition; anywhere else the line is
prose. -/
def blocks : Nat → Open → List String → List Block
  | line, o, [] => o.close line
  | line, .fence opened indent character count, text :: rest =>
    let spaces := (text.toList.takeWhile (· == ' ')).length
    let refused :=
      if indentedFence text then [Block.refused line .indentedFence]
      else if !blank text && spaces < indent then [.refused line .shallowFenceLine]
      else []
    refused ++ blocks (line + 1)
      (if closingFence text character count then .idle else .fence opened indent character count)
      rest
  | line, o, text :: rest =>
    let spaces := (text.toList.takeWhile (· == ' ')).length
    if let some refusal := unsupported? text then
      o.close line ++ .refused line refusal :: blocks (line + 1) .idle rest
    else if blank text then o.close line ++ blocks (line + 1) .idle rest
    else if let some (character, count) := fenceOpen? text then
      o.close line ++ blocks (line + 1) (.fence line spaces character count) rest
    else if isHeading text || (spaces ≤ 3 && wholeComment (text.toList.drop spaces)) then
      o.close line ++ .paragraph line text :: blocks (line + 1) .idle rest
    else if !(o matches .idle) &&
        (referenceDefinition? (String.ofList (text.toList.dropWhile isBlank))).isSome then
      o.close line ++ .refused line .strayDefinition :: blocks (line + 1) .idle rest
    else match o with
      | .table start rows => blocks (line + 1) (.table start (text :: rows)) rest
      | .paragraph (header :: before) =>
        if delimiterRow text then
          Open.cut (line - 1) (.paragraph before) ++
            blocks (line + 1) (.table (line - 1) [text, header]) rest
        else if interrupts text || (indented (before.getLast?.getD header) && !indented text) then
          o.cut line ++ blocks (line + 1) (.paragraph [text]) rest
        else blocks (line + 1) (.paragraph (text :: header :: before)) rest
      | _ =>
        if interrupts text then blocks (line + 1) (.paragraph [text]) rest
        else match referenceDefinition? text with
          | some (name, destination) => .definition name destination :: blocks (line + 1) .idle rest
          | none => blocks (line + 1) (.paragraph [text]) rest

/-- Each line for which the document `lines` is refused, with the construct (`blocks`). -/
def refusals (lines : List String) : List (Nat × Refusal) :=
  (blocks 1 .idle lines).filterMap fun
    | .refused line refusal => some (line, refusal)
    | _ => none

/-- The prose of a Markdown document (`blocks`): for each paragraph, heading and comment line, and
each cell of each table row (`cells`), its text outside code spans, link destinations, HTML tags
and comments, autolinks and bare URLs. -/
def markdownRuns (text : String) : List Run :=
  let parts := blocks 1 .idle (text.splitOn "\n")
  let defined := parts.filterMap fun
    | .definition name destination => some (name, destination)
    | _ => none
  parts.flatMap fun
    | .paragraph line paragraph => runsOf line (pieces defined paragraph)
    | .table line rows => ((List.range rows.length).zip rows).flatMap fun (i, row) =>
      (cells [] row.toList).flatMap fun cell =>
        runsOf (line + i) (pieces defined (String.ofList cell))
    | _ => []

/-- What the Markdown document `text` of `main` is refused for: each line of a construct outside
the subset (`refusals`, `Refusal.message`), and each rule ID in its prose that is not a link to its
development page, reported with `file`, the line and the construct or the ID. -/
def markdownErrors (file text : String) : List String :=
  (refusals (text.splitOn "\n")).map (fun (line, refusal) =>
    s!"{file}:{line}: {refusal.message}") ++
  (bareMentions developmentTarget (markdownRuns text)).map (·.describe file)

/-- The Markdown check reports nothing exactly when no line of the document is refused and every
rule-ID token in the document's prose is a registered rule ID linked to its development page. -/
theorem markdownErrors_nil_iff (file text : String) :
    markdownErrors file text = [] ↔ refusals (text.splitOn "\n") = [] ∧
      ∀ run ∈ markdownRuns text, ∀ m ∈ run.mentions, m.Linked developmentTarget := by
  unfold markdownErrors
  simp [bareMentions_nil_iff]

/-! ## HTML prose -/

/-- The elements whose text is not prose: code and pasted output. The text of `script` and `style`
elements is never read. -/
def exemptElement (name : String) : Bool := ["code", "pre"].contains name

/-- The elements that name the page itself: its title and its top heading. -/
def namingElement (name : String) : Bool := ["title", "h1"].contains name

/-- The destination that the title and top heading of the rendered file `path` are read as linked
to, in the edition whose artifact root is `root`: the file itself when it is a rule's page, and
none otherwise. A page cannot usefully link to itself, so a rule's own ID in its own page's title
and top heading is the one rule ID in prose that is not written as a link. A heading of any other
page, any other heading of a rule's page and any other rule's ID are prose like the rest. -/
def ownPage (root path : String) : Option String :=
  if RuleId.all.any fun id => path == root ++ id.route ++ "index.html" then
    some (basePath ++ path)
  else none

/-- The state of the prose scan of an HTML page. -/
structure HtmlScan where
  /-- Whether the scan is in markup, a comment or a raw-text element. -/
  mode : ScanMode
  /-- The number of open exempt elements. -/
  exempt : Nat
  /-- The number of open elements that name the page (`namingElement`). -/
  naming : Nat
  /-- The destination the text of those elements is read as linked to (`ownPage`), if any. -/
  own : Option String
  /-- The `href` of the open `a` element, if there is one. -/
  link : Option String
  /-- The 1-based line at the scan position. -/
  line : Nat
  /-- The runs found so far, last first. -/
  runs : List Run

private def HtmlScan.withText (s : HtmlScan) (line : Nat) (text : String) : List Run :=
  if s.exempt == 0 && !text.isEmpty then
    ⟨line, text, s.link <|> (if s.naming == 0 then none else s.own)⟩ :: s.runs
  else s.runs

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
      naming := if namingElement name then s.naming - 1 else s.naming,
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
        naming := if namingElement name && body.getLast? != some '/' then s.naming + 1
          else s.naming,
        link := if name == "a" then tag.get? "href" else s.link }
      { opened with line := next, runs := opened.withText textLine text }

/-- The prose scan of a whole HTML page, whose title and top heading are read as linked to `own`. -/
def htmlScan (own : Option String) (html : String) : HtmlScan :=
  let start : HtmlScan :=
    { mode := .markup, exempt := 0, naming := 0, own, link := none, line := 1, runs := [] }
  match html.splitOn "<" with
  | [] => start
  | first :: chunks =>
    chunks.foldl htmlStep { start with line := 1 + newlines first, runs := start.withText 1 first }

/-- The prose of an HTML page: its text outside `exemptElement` elements, comments and `script`
and `style` elements, each run with the `href` of the `a` element it lies in or, in the title and
top heading (`namingElement`) outside an `a` element, with `own`. -/
def htmlRuns (own : Option String) (html : String) : List Run := (htmlScan own html).runs.reverse

/-- Whether the page's scan ends in markup with every exempt and naming element closed. An
unclosed `code` element, comment or script would hide the text after it, and an unclosed title or
top heading would read it as naming the page, so such a page is refused instead of read short. -/
def htmlClosed (html : String) : Bool :=
  match (htmlScan none html).mode with
  | .markup => (htmlScan none html).exempt == 0 && (htmlScan none html).naming == 0
  | _ => false

/-- What the rendered page `html` at artifact path `path` is refused for: an element, comment or
script that hides text and is never closed, and each rule ID in its prose that is not a link to
its page in the edition whose artifact root is `root`, reported with the path, its line and the
ID. A rule page's own title and top heading name its rule without a link (`ownPage`). -/
def htmlErrors (root path html : String) : List String :=
  (if htmlClosed html then [] else
    [s!"{path}: a code, pre, title or h1 element, a comment or a script is not closed, so the \
      text after it cannot be read as prose"]) ++
  (bareMentions (pageTarget root (Page.ofHtml path html)) (htmlRuns (ownPage root path) html)).map
    (·.describe path)

/-- The page check reports nothing exactly when the page's scan is closed and every rule-ID token
in the page's prose is a registered rule ID linked to its page under `root`, where the title and
top heading of a rule's own page count as linked to that page (`ownPage`). -/
theorem htmlErrors_nil_iff (root path html : String) :
    htmlErrors root path html = [] ↔ htmlClosed html = true ∧
      ∀ run ∈ htmlRuns (ownPage root path) html, ∀ m ∈ run.mentions,
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

/-- Generated prose, in the link syntax Markdown and Verso share, with each registered rule ID in
its prose replaced by `rule` of it. Code spans, existing links and URLs are kept as written. -/
def linkIds (rule : RuleId → String) (text : String) : String :=
  String.join ((pieces [] text).map fun
    | .prose between none => rewriteIds id rule between
    | piece => piece.raw)

/-- Generated Verso prose with each registered rule ID in prose made a link to its page in the
same edition (`relativeCitation`). -/
def linkVerso (text : String) : String := linkIds relativeCitation text

/-! Evaluated controls (observations of the compiled scanners, not proofs). A bare ID in prose is
refused in both formats, with its file and line; an unregistered ID and a link to another page are
refused; a heading is prose, so a bare ID in one is refused, except a rule's own ID in the title
and top heading of its own page; and each exempt construct is accepted: fenced and inline code,
pasted tool output, a rule index table whose IDs are links and Lean identifiers written as code. -/
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
#guard markdownErrors "a.md" "See <https://x/rules/RG1001/> and https://x/rules/RG1002/, in \
  xRG1001, RG10012 and `RG1001_a`.\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "In RG1001_a, _RG2003_ and __RG2003__.\n" ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG2003 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG2003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Compare <!-- draft and RG1001 here.\n" ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Compare <!-- draft RG1001 --> and that.\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    ("See [RG1001] here.\n[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") ==
  ["a.md:2: " ++ Refusal.strayDefinition.message,
    "a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See [RG1001] here.\n\n    [RG1001]: " ++
    Edition.dev.url RuleId.projectAxiom.route ++ "\n") ==
  ["a.md:3: " ++ Refusal.containedBlock.message,
    "a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    ("See [RG1001] here.\n\n[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("# Links\n   [RG1001]: " ++
    Edition.dev.url RuleId.projectAxiom.route ++ "\nSee [RG1001].\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See [RG1001].\n\n<!-- Links -->\n[RG1001]: " ++
    Edition.dev.url RuleId.projectAxiom.route ++ "\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See [RG1001].\n\n[RG1001]: " ++
    Edition.dev.url RuleId.projectAxiom.route ++ " 'Bob's rule'\n") ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:3: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("<p align=\"center\">See [RG1001](" ++
    Edition.dev.url RuleId.projectAxiom.route ++ ").</p>\n") ==
  ["a.md:1: " ++ Refusal.htmlLine.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "<div>\n```\n</div>\n\nRG1001 here.\n\n```\n" ==
  ["a.md:1: " ++ Refusal.htmlLine.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "<!DOCTYPE html>\n<?php echo 1; ?>\n" ==
  ["a.md:1: " ++ Refusal.htmlLine.message, "a.md:2: " ++ Refusal.htmlLine.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    "<https://example.com/x>\n```text\nout\n\nmore\n```\n\nAfter RG1001.\n\n```lean\nx\n```\n" ==
  ["a.md:8: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("<https://example.com/x>\nSee [RG1001].\n\n[RG1001]: " ++
    Edition.dev.url RuleId.projectAxiom.route ++ "\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    "<!-- lean-trusted-compiler -->\n```lean\ntheorem RG1001 : True := trivial\n```\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "```text\nout\n    ```\n```\n\nSee RG1001.\n\n```lean\nx\n```\n" ==
  ["a.md:3: " ++ Refusal.indentedFence.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Text.\n\n    ```\ncode\n    ```\n" ==
  ["a.md:3: " ++ Refusal.indentedFence.message, "a.md:5: " ++ Refusal.indentedFence.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (markdownErrors "a.md"
    "- ```text\n output\n ```\n\nSee RG1001 here.\n\n```lean\nx\n```\n").head? ==
  some ("a.md:1: " ++ Refusal.containedBlock.message)
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "> ```lean\n> x\n> ```\n" ==
  ["a.md:1: " ++ Refusal.containedBlock.message, "a.md:3: " ++ Refusal.containedBlock.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "> | Rule | Note |\n> | --- | --- |\n> | `x | RG1001` |\n" ==
  ["a.md:2: " ++ Refusal.containedBlock.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("- [RG1001]: https://example.com/wrong\n\nSee [RG1001].\n\n" ++
    "[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") ==
  ["a.md:1: " ++ Refusal.containedBlock.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "See note[^1].\n\n[^1]: RG1001\n" ==
  ["a.md:3: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "See[^1][^2].\n\n[^1]: Run `lake\n[^2]: RG1001 y` more\n" ==
  ["a.md:4: " ++ Refusal.openCodeSpan.message,
    "a.md:4: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "# Usage\n    lake exe regula `x\nThen RG1001 `y` applies.\n" ==
  ["a.md:3: " ++ Refusal.openCodeSpan.message,
    "a.md:3: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("1. Item\n\n    [RG1001]: https://example.com/wrong\n\n" ++
    "See [RG1001].\n\n[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") ==
  ["a.md:3: " ++ Refusal.containedBlock.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See [RG1001].\n\n***\n[RG1001]: https://example.com/wrong\n\n" ++
    "[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") ==
  ["a.md:4: " ++ Refusal.strayDefinition.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    "Text <!--> RG1001 -->, <!---> RG1002 --> and <!-- a -- RG1003 -->.\n" ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG1002 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG1003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("- <p>See [RG1001](" ++ Edition.dev.url RuleId.projectAxiom.route ++
    ").</p>\n") == ["a.md:1: " ++ Refusal.containedBlock.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "1. Run:\n   ```sh\nRG1001 output\n   ```\n" ==
  ["a.md:3: " ++ Refusal.shallowFenceLine.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("1. Run:\n   ```sh\n   lake lint\n   ```\n\nSee [RG1001].\n\n" ++
    "[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "<!--\nRG1001\n-->\n" ==
  ["a.md:1: " ++ Refusal.partialComment.message,
    "a.md:2: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("<!-- note --> [RG1001](" ++
    Edition.dev.url RuleId.projectAxiom.route ++ ")\n") ==
  ["a.md:1: " ++ Refusal.partialComment.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "See &#82;G1001.\n" ==
  ["a.md:1: " ++ Refusal.characterReference.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "> Run `lake exe\n> regula` and see RG1001 `here`.\n" ==
  ["a.md:2: " ++ Refusal.openCodeSpan.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Text `x\n2. y` and RG1001 then `z`.\n" ==
  ["a.md:2: " ++ Refusal.openCodeSpan.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Text `x\n| a | b |\n| - | - |\n" ==
  ["a.md:2: " ++ Refusal.openCodeSpan.message]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See [RG1001 flags `sorry](" ++
    Edition.dev.url RuleId.projectAxiom.route ++ ") and `admit`.\n") ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "Text `x RG1001\n#\ty` z\n" ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "| Rule | Note |\n| --- | --- |\n| x | `a | RG1001` |\n" ==
  ["a.md:3: " ++ Refusal.splitTableCell.message,
    "a.md:3: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("| Rule | Checks |\n| --- | --- |\n| [RG1001] | `a \\| b` |\n\n" ++
    "[RG1001]: " ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    ("See [RG1001].\n\n[RG1001]: <" ++ Edition.dev.url RuleId.projectAxiom.route ++ "\n") ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:3: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("See [RG1001](<" ++ Edition.dev.url RuleId.projectAxiom.route ++
    ").\n") == ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" ("[RG1001 [x](u)](" ++ Edition.dev.url RuleId.projectAxiom.route ++
    ") and [RG1002\\](" ++ Edition.dev.url RuleId.proofHole.route ++ ")\n") ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG1002 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
    ("[RG1001\n---\n](" ++ Edition.dev.url RuleId.projectAxiom.route ++ ")\n") ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "See <a \"RG1001\"> and <a title=\"RG1002\">it</a>.\n" ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md" "## Why RG2003 fires first\n\nText.\n" ==
  ["a.md:1: RG2003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard markdownErrors "a.md"
  ("### [RG2003](" ++ Edition.dev.url RuleId.sourceBuild.route ++ ") fires first\n\nText.\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/enforcement/index.html"
    "<base href=\"./../\"><title>RG2003</title><h1>About RG2003</h1><h2>RG2003 and warnings</h2>" ==
  List.replicate 3
    "dev/enforcement/index.html:1: RG2003 is a bare rule ID in prose; make it a link to its rule \
      page"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard htmlErrors "dev/" "dev/rules/RG1001/index.html"
    "<base href=\"./../../\"><h1>RG1001: like RG1002</h1><h2>RG1001 again</h2>" ==
  ["dev/rules/RG1001/index.html:1: RG1002 is linked to /regula/dev/rules/RG1001/index.html, \
      which is not its rule page",
    "dev/rules/RG1001/index.html:1: RG1001 is a bare rule ID in prose; make it a link to its rule \
      page"]
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
  ["a.md:3: " ++ Refusal.unclosedFence.message]
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
