import MD4Lean
import RegulaCore.Markdown

/-! # Markdown documents, read by md4c

`read` parses a Markdown document with md4c (through `MD4Lean`, at the revision the website
package's pinned Verso resolves to) and reports its parse as the pieces
`Regula.Markdown.documentErrors` (`RegulaCore/Markdown.lean`) decides on. Nothing here reads
Markdown syntax: what is a paragraph, a code span, a table cell or a link, which link reference
definition a reference uses, and what a character reference stands for, is md4c's.

## The parse

md4c runs with its GitHub dialect: CommonMark with tables, strikethrough, task lists and
permissive autolinks (`MD4Lean.MD_DIALECT_GITHUB`). An image's description is read as md4c
renders it, as text alone: a link or a code span inside it is description text, and only a link
around the image links it.

## What is refused

No HTML is read. A raw HTML block is refused, a comment too, unless it is exactly one fence
marker of the documentation audit (`Regula.Markdown.auditMarker`). Inline raw HTML is refused
with its document: MD4Lean's wrapper stores its text as a string among the inline elements,
which is not a value of `MD4Lean.Text` (reading such a parse crashed when tried on the pinned
revision), so the parse runs with inline raw HTML read as text (`MD4Lean.MD_FLAG_NOHTMLSPANS`),
and a document is read only when md4c renders it to the same HTML with and without that flag.
The parse then describes the rendering GitHub's dialect gives.

A document is also refused when md4c renders a table head with no table body. A table with no
body row does that, and the wrapper cannot represent it; so can raw HTML that holds those bytes,
which is refused anyway. A document with a NUL character is refused, since the wrapper stores it
among the strings of a code block as an inline element.

Four constructs are refused where md4c's parse shows them, because GitHub reads them
otherwise or the parse does not show how GitHub reads them (the contributor guide names the
differences):

- a link whose text starts with `^` and an image whose description does, also inside an
  image's description: GitHub reads `[^label]` as a footnote reference, with or without a `!`
  before it;
- a pipe character inside a code span, a link's text or an image's description in a table
  cell, escaped or not: md4c reads those before it finds the cells of a row, and GitHub ends a
  cell at a pipe character that is not escaped. An escaped one ends no cell for either, and is
  refused too: md4c keeps its backslash in a code span, where GitHub removes it, and reports a
  link's text and an image's description without it, and the check reads no escapes, so it
  does not tell an escaped pipe character from another;
- an autolink whose text has a rule ID, since the two find the end of a bare URL by their own
  rules, and MD4Lean does not tell a bare URL from `<URL>`;
- a link inside a link's text, which md4c reports for an autolink there, a bare URL or `<URL>`.
  GitHub makes no link of a bare URL inside a link's text, and it renders `<URL>` there as a
  link inside a link, which a browser ends at the inner one, so the text after it is outside
  every link. MD4Lean does not tell the two apart, so both are refused.

## What is not seen

md4c's parse has no trace of these differences, so the check reads what md4c reports (the guide
gives each):

- a footnote that md4c reads as a link reference definition and that is referenced only in the
  second brackets of a full reference, and the indented lines that continue a footnote;
- a table whose header row has another number of cells than its delimiter row;
- the blocks GitHub starts where md4c reads on in one paragraph: a table whose header row is
  not the first line of its paragraph, and each footnote definition after a line of text or
  after another definition. A code span or a link's text that md4c reads across the cells, rows
  or definitions GitHub finds there is kept whole, so a rule ID inside it is code or linked
  here and prose on GitHub;
- YAML front matter, the lines between two `---` lines at the start of a document, which GitHub
  shows as a table of its raw values. md4c has no front matter and reads those lines as
  Markdown, a thematic break and then a heading, so a rule ID written there as a code span or a
  link is code or linked here and plain text on GitHub, backticks or brackets included;
- math that GitHub renders from a code span between two dollar signs or from a fenced code
  block with the info string `math`: both are code for md4c, so a rule ID there is accepted.

A document whose reading cannot be used (inline raw HTML, a table with no body row, a NUL
character, md4c failing) is refused by file and reason, without a line and without its rule
IDs, which are reported once it is read.

## Trusted

md4c's conformance to CommonMark and to GitHub's extensions it implements; MD4Lean's wrapper,
for documents not refused above; that md4c's HTML renderer and the wrapper see the same parse of
the same text and flags; and md4c's rendering of a character reference alone, which is how one
is decoded (`decode`).

## Not proved

The translation in this module from MD4Lean's document to pieces (`read` and every definition
it calls: `block`, `inline`, `flat`, `link` and the rest) has no theorem. It decides which piece
each element md4c reports becomes: what is prose, code, a link's edge, a boundary between runs
or lines, and a refusal. `Regula.Markdown.documentErrors_nil_iff` is about the pieces it is
given, so that an accepted document has no bare rule ID in the prose md4c reports rests on this
translation too, which only the evaluated controls below observe.
-/

namespace Regula.Markdown

open MD4Lean (Text Block AttrText)

/-- GitHub's dialect, as md4c implements it. -/
def github : UInt32 := MD4Lean.MD_DIALECT_GITHUB

/-- GitHub's dialect with inline raw HTML read as text. -/
def htmlAsText : UInt32 := MD4Lean.MD_DIALECT_GITHUB ||| MD4Lean.MD_FLAG_NOHTMLSPANS

/-- U+FFFD, which md4c renders for a NUL character. -/
def replacement : String := String.singleton (Char.ofNat 0xFFFD)

/-- Text with the four escapes of md4c's HTML renderer undone. -/
def unescape : List Char → List Char
  | '&' :: 'a' :: 'm' :: 'p' :: ';' :: rest => '&' :: unescape rest
  | '&' :: 'l' :: 't' :: ';' :: rest => '<' :: unescape rest
  | '&' :: 'g' :: 't' :: ';' :: rest => '>' :: unescape rest
  | '&' :: 'q' :: 'u' :: 'o' :: 't' :: ';' :: rest => '"' :: unescape rest
  | c :: rest => c :: unescape rest
  | [] => []

/-- What the character reference `reference` stands for, by md4c: md4c renders the reference
alone, as a paragraph, with its own table of named references, and the paragraph's text with the
renderer's escapes undone is the reference's text. A name md4c does not know is rendered as
written. `none` when md4c does not render a paragraph. -/
def decode (reference : String) : Option String :=
  (MD4Lean.renderHtml reference 0 0).bind fun html =>
    if html.startsWith "<p>" && html.endsWith "</p>\n" then
      some (String.ofList (unescape ((html.toList.drop 3).take (html.length - 8))))
    else none

/-- The text of a destination or title as md4c reports it, each character reference decoded. -/
def attrText (parts : Array AttrText) : String :=
  String.join (parts.toList.map fun
    | .normal text => text
    | .entity reference => (decode reference).getD reference
    | .nullchar => replacement)

/-- The pieces of one character reference in prose. -/
def reference (slice : String) : List Piece :=
  match decode slice with
  | some rendered => [.text slice rendered]
  | none => [.refused s!"md4c does not decode the character reference {slice}", .text slice slice]

/-- Why a pipe character inside a code span, a link's text or an image's description in a table
cell is refused, escaped or not. -/
def pipeReason : String :=
  "a pipe character inside a code span, a link's text or an image's description in a table \
    cell: GitHub ends the cell at it unless it is escaped, and the check does not tell an \
    escaped one from another; write the cell without it"

/-- Why a link inside a link's text is refused. md4c reports an autolink there, a bare URL or
`<URL>`, as a link of its own. GitHub makes no link of a bare URL inside a link's text, and it
renders `<URL>` there as a link inside a link, which a browser ends at the inner one, so the
text after it is outside every link. MD4Lean does not tell the two forms apart. -/
def nestedReason : String :=
  "a link inside a link's text (md4c reads an autolink there, a bare URL or <URL>, as one): \
    GitHub makes no link of a bare URL there and ends the outer link at <URL>; write the URL \
    outside the link's text"

/-- Why a link whose text starts with `^`, or an image whose description does, is refused:
GitHub reads `[^label]` as a footnote reference, with or without a `!` before it, and md4c makes
a link or an image of it only when it has read the footnote as a link reference definition,
whose text it does not report. MD4Lean does not tell such a reference from a link or an image
written with its destination, so those are refused too. -/
def caretReason : String :=
  "a link's text or an image's description starts with ^: GitHub reads [^label] as a footnote \
    reference, and where md4c makes a link or an image of it, md4c has read the footnote as a \
    link reference definition, so the footnote's text is not checked"

/-- The refusal of a pipe character among `texts` in a table cell (`cell`). md4c reads a code
span, a link's text and an image's description before it finds the cells of a row, so a pipe
character inside one stays there; GitHub finds the cells first and ends a cell at it unless it
is escaped. An escaped one is refused as well: `texts` are what md4c reports, a code span with
the backslash and a link's text or an image's description without it, and no escape is read
here. A pipe character in a destination ends the cell for md4c too. -/
def pipes (cell : Bool) (texts : List String) : List Piece :=
  if cell && texts.any (·.contains '|') then [.refused pipeReason] else []

/-- The refusal of a link whose text `body` holds another link (`nestedReason`). -/
def nested (body : List Piece) : List Piece :=
  if body.any (fun | .enter _ => true | _ => false) then [.refused nestedReason] else []

/-- The pieces of a code span: code, refused when it has a pipe character, escaped or not, in a
table cell. -/
def codeSpan (cell : Bool) (slices : Array String) : List Piece :=
  pipes cell slices.toList ++ slices.toList.map Piece.code

/-- The text a run of pieces renders as. -/
def visible (pieces : List Piece) : String :=
  String.join (pieces.map fun
    | .text _ rendered => rendered
    | .code slice => slice
    | _ => "")

/-- The prose a run of pieces renders as, without its code. -/
def prose (pieces : List Piece) : String :=
  String.join (pieces.map fun
    | .text _ rendered => rendered
    | _ => "")

/-- The refusal of a link's text or an image's description `body` that starts with `^`
(`caretReason`). -/
def caret (body : List Piece) : List Piece :=
  if (visible body).startsWith "^" then [.refused caretReason] else []

/-- The pieces of one element of an image's description, as md4c renders the description: its
text alone. Emphasis, links and images inside it give their text, and a code span's text is
description text too. A link inside it whose text starts with `^`, and an image inside it whose
description does, is refused as it is elsewhere (`caret`). -/
def flat (text : Text) : List Piece :=
  match text with
  | .normal slice => [.text slice slice]
  | .nullchar => [.text "" replacement]
  | .br _ | .softbr _ => [.line]
  | .entity slice => reference slice
  | .em texts | .strong texts | .u texts | .del texts | .wikiLink _ texts =>
    texts.attach.toList.flatMap fun ⟨inner, _⟩ => flat inner
  | .a _ _ _ texts =>
    let body := texts.attach.toList.flatMap fun ⟨inner, _⟩ => flat inner
    caret body ++ body
  | .img _ _ description =>
    let body := description.attach.toList.flatMap fun ⟨inner, _⟩ => flat inner
    caret body ++ body
  | .code slices | .latexMath slices | .latexMathDisplay slices =>
    slices.toList.map fun slice => .text slice slice
termination_by text
decreasing_by
  all_goals
    have := Array.sizeOf_lt_of_mem ‹inner ∈ _›
    simp_wf
    omega

/-- The first rule-ID token of `text`, if it has one. -/
def firstToken (text : String) : Option String :=
  (Regula.Prose.splitTokens none 0 [] text.toList).findSome? fun
    | .inr token => some token
    | .inl _ => none

/-- The pieces of a link with text `body` that leads to `leads`; `auto` is whether md4c reports
it as an autolink. A link whose text starts with `^` is refused (`caret`). An autolink
whose text has a rule ID is refused, and its text is then not read as link text. -/
def link (leads : String) (auto : Bool) (body : List Piece) : List Piece :=
  caret body ++
    match (if auto then firstToken (visible body) else none) with
    | some token =>
      .refused s!"{token} is in an autolink (a bare URL or <URL>), whose end GitHub and md4c \
        find by their own rules; write the link in brackets" ::
        body.map fun
          | .text slice _ => .code slice
          | piece => piece
    | none => .enter leads :: body ++ [.leave]

/-- The pieces of one inline element; `cell` is whether it lies in a table cell. Emphasis, strong
emphasis, underline and strikethrough continue the prose around them; a link's text is prose
between the link's edges; an image's description is a run of its own (`flat`); a code span is
code. In a table cell a pipe character inside a code span, a link's text or an image's
description is refused, escaped or not (`pipes`). A link whose text holds another link is
refused (`nested`), and so is a link whose text, or an image whose description, starts with `^`
(`caret`). LaTeX math and wiki links are not enabled; their text would be prose. -/
def inline (cell : Bool) (text : Text) : List Piece :=
  match text with
  | .normal slice => [.text slice slice]
  | .nullchar => [.text "" replacement]
  | .br _ | .softbr _ => [.line]
  | .entity slice => reference slice
  | .em texts | .strong texts | .u texts | .del texts | .wikiLink _ texts =>
    texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline cell inner
  | .a href _ auto texts =>
    let body := texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline cell inner
    pipes cell [prose body] ++ nested body ++ link (attrText href) auto body
  | .img _ _ description =>
    let body := description.toList.flatMap flat
    .gap :: pipes cell [prose body] ++ caret body ++ body ++ [.gap]
  | .code slices => codeSpan cell slices
  | .latexMath slices | .latexMathDisplay slices =>
    slices.toList.map fun slice => .text slice slice
termination_by text
decreasing_by
  all_goals
    have := Array.sizeOf_lt_of_mem ‹inner ∈ _›
    simp_wf
    omega

/-- The pieces of a block's inline content. -/
def inlines (cell : Bool) (texts : Array Text) : List Piece := texts.toList.flatMap (inline cell)

/-- The pieces of a code block or raw HTML block: md4c reports each line's text and then its
line end, so each `"\n"` is a line boundary. The text is located and not read. -/
def verbatim (slices : Array String) : List Piece :=
  slices.toList.map fun slice => if slice == "\n" then .line else .code slice

/-- The pieces of the cells of one table row, which lie on one source line. -/
def row (cells : Array (Array Text)) : List Piece :=
  cells.toList.flatMap fun cell => .gap :: inlines true cell

/-- The pieces of one block. Each leaf block starts on a later source line than the text before
it, as does each row of a table. A raw HTML block is refused unless it is a fence marker of the
documentation audit (`auditMarker`). -/
def block (b : Block) : List Piece :=
  match b with
  | .p texts | .header _ texts => .line :: inlines false texts
  | .ul _ _ items | .ol _ _ _ items =>
    items.attach.toList.flatMap fun ⟨item, _⟩ =>
      item.contents.attach.toList.flatMap fun ⟨inner, _⟩ => block inner
  | .hr => []
  | .code _ _ _ slices => .line :: verbatim slices
  | .html slices =>
    if auditMarker (String.join slices.toList) then .line :: verbatim slices
    else
      .line :: .refused "raw HTML block, which the check does not read; write it in Markdown" ::
        verbatim slices
  | .blockquote blocks => blocks.attach.toList.flatMap fun ⟨inner, _⟩ => block inner
  | .table head body => .line :: row head ++ body.toList.flatMap fun cells => .line :: row cells
termination_by b
decreasing_by
  all_goals simp_wf
  · have := Array.sizeOf_lt_of_mem ‹inner ∈ item.contents›
    have := Array.sizeOf_lt_of_mem ‹item ∈ items›
    have : sizeOf item.contents < sizeOf item := by cases item; simp_wf; omega
    omega
  · have := Array.sizeOf_lt_of_mem ‹inner ∈ item.contents›
    have := Array.sizeOf_lt_of_mem ‹item ∈ items›
    have : sizeOf item.contents < sizeOf item := by cases item; simp_wf; omega
    omega
  · have := Array.sizeOf_lt_of_mem ‹inner ∈ blocks›
    omega

/-- The text of `html` from the first character at which it differs from `other`, on one
line. -/
def difference (html other : String) : String :=
  let rec go : List Char → List Char → List Char
    | a :: as, b :: bs => if a == b then go as bs else a :: as
    | as, _ => as
  String.ofList (((go html.toList other.toList).take 60).map fun c => if c == '\n' then ' ' else c)

/-- md4c's reading of the Markdown document `source` in GitHub's dialect: its pieces, or why the
reading cannot be used (see the module documentation). -/
def read (source : String) : Reading :=
  if source.contains '\x00' then
    .unread "the document has a NUL character, which MD4Lean cannot represent in a code block"
  else
    match MD4Lean.renderHtml source github 0, MD4Lean.renderHtml source htmlAsText 0 with
    | some html, some escaped =>
      if html != escaped then
        .unread s!"inline raw HTML, which the check does not read (MD4Lean has no value for \
          it); write it in Markdown: {difference html escaped}"
      else if escaped.contains "</thead>\n</table>" then
        .unread "md4c renders a table head with no table body: a table with no body row, which \
          MD4Lean cannot represent, or raw HTML, which the check does not read"
      else
        match MD4Lean.parse source htmlAsText with
        | some document => .read (document.blocks.toList.flatMap block)
        | none => .unread "md4c could not parse the document"
    | _, _ => .unread "md4c could not render the document"

/-- What the Markdown document `file` with text `source` is refused for
(`Regula.Markdown.documentErrors` of md4c's reading). -/
def check (file source : String) : List String := documentErrors file source (read source)

/-- Whether `path` names a Markdown document: its extension is `md` or `markdown`, in any
case. -/
def isMarkdown (path : String) : Bool :=
  path.toLower.endsWith ".md" || path.toLower.endsWith ".markdown"

/-! Evaluated controls (observations of the compiled check on md4c's parse, not proofs). The
link every control accepts is the development page of the rule. -/

private def page (id : String) : String := s!"https://rbeauchamp.github.io/regula/dev/rules/{id}/"

private def bare (line : String) (id : String := "RG2003") : String :=
  s!"a.md:{line}: {id} is a bare rule ID in prose; make it a link to its rule page"

private def split (line : String) : String :=
  s!"a.md:{line}: RG2003 is only partly inside a link or a code span; write the whole ID as one \
    link to its rule page"

private def html (line : String) : String :=
  s!"a.md:{line}: raw HTML block, which the check does not read; write it in Markdown"

private def inlineHtml (shown : String) : String :=
  s!"a.md: inline raw HTML, which the check does not read (MD4Lean has no value for it); write \
    it in Markdown: {shown}"

private def bodyless : String :=
  "a.md: md4c renders a table head with no table body: a table with no body row, which MD4Lean \
    cannot represent, or raw HTML, which the check does not read"

-- A bare ID is refused in a paragraph, a heading, a list item, a block quote, a table cell and
-- emphasis, each with its line.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Text.\n\nIt is reported as RG2003 here.\n" == [bare "3"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "# About RG2003\n\nSetext RG2003\n===\n" == [bare "1", bare "3"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "- one\n- RG2003\n  1. nested RG2003\n\n> quoted RG2003\n" ==
  [bare "2", bare "3", bare "5"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "| Rule | Note |\n| --- | --- |\n| RG2003 | `RG2003` |\n| x | RG2003 |\n" ==
  [bare "3", bare "4"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "*RG2003*, **RG2003**, _RG2003_ and ~~RG2003~~\nthen RG**2003**\n" ==
  [bare "1", bare "1", bare "1", bare "1", bare "2"]
-- An ID in a code span, a fenced or indented code block, or a link to its rule page is
-- accepted, whether the link is inline or a reference.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" ("Use `RG2003` or ``a ` RG2003``.\n\n```text\nRG2003 [violation]\n```\n\n" ++
  "    RG2003 indented\n\n~~~\nRG2003\n~~~\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"See [RG2003]({page "RG2003"}), [the RG2003 fix]({page "RG2003"}#fix),\n" ++
  s!"[RG2003], [RG2003][], [it][RG2003] and [`RG2003`]({page "RG2002"})\n\n" ++
  s!"[RG2003]: {page "RG2003"}\n") == []
-- md4c reports an autolink inside a link's text as a link of its own, a bare URL and `<URL>`
-- alike. GitHub makes no link of the first and ends the outer link at the second, which leaves
-- the ID after it as prose; both are refused.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"[see https://example.org and RG2003]({page "RG2003"})\n\n" ++
  s!"[see <https://example.org> and RG2003]({page "RG2003"})\n\n" ++
  s!"[*<https://example.org>*]({page "RG2003"})\n") ==
  (["1", "3", "5"].map fun line => s!"a.md:{line}: {nestedReason}")
-- A link elsewhere and an unregistered ID are refused.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"[RG2003]({page "RG2002"}) and RG9999\n") ==
  [s!"a.md:1: RG2003 is linked to {page "RG2002"}, which is not its rule page",
    "a.md:1: RG9999 is not a registered rule ID"]
-- A token is read across the edges of links and code spans: one that an edge divides is refused,
-- also when both parts link to the rule's page.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"RG[2003](https://example.org), [RG]({page "RG2003"})[2003]" ++
  s!"({page "RG2003"}), RG`2003` and `RG`2003\n") == [split "1", split "1", split "1", split "1"]
-- An image's description is text alone: a link or a code span inside it does not count, and a
-- link around the image does.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"![RG2003](a.png) ![[RG2003]({page "RG2003"})](a.png) ![`RG2003`](a.png)\n" ++
  s!"\n[![RG2003](a.png)]({page "RG2003"})\n") == [bare "1", bare "1", bare "1"]
-- Link reference definitions: a reference without a definition is prose, a definition is not
-- prose, and a definition of another page is refused where it is used. That last link's text
-- also occurs on the definition's line, after everything else, so its lines are bracketed.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "See [RG2003] and [RG2002].\n\n[RG2002]: https://example.org/RG2002\n" ==
  [bare "1",
    "a.md:1-3: RG2002 is linked to https://example.org/RG2002, which is not its rule page"]
-- A line that only looks like the text is not reported: the definition's line is not the
-- mention's.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"[RG2002]: {page "RG2002"}\n\nSee RG2002 and [RG2002].\n") ==
  [bare "3" "RG2002"]
-- Character references are decoded by md4c, in text and in a link's destination: a numeric
-- reference spells the ID, `&sol;` is the destination's last character, `&fjlig;` continues the
-- word after the ID, and a name md4c does not know is text as written.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"R&#71;2003, [RG2003](https://rbeauchamp.github.io/regula/dev/rules/" ++
  "RG2003&sol;), RG2003&fjlig; and &RG2003;\n") == [bare "1", bare "1"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard decode "&amp;" == some "&" && decode "&lt;" == some "<" && decode "&#x47;" == some "G" &&
  decode "&fjlig;" == some "fj" && decode "&#0;" == some replacement &&
  decode "&RG2003;" == some "&RG2003;"
-- No HTML is read. A raw HTML block is refused, a comment too, whatever it holds: an ID spelled
-- with a character reference or divided by a tag would not be found in it.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "<p>R&#71;2003</p>\n\n<p>RG<em>2003</em></p>\n\n<!-- note -->\n\nText.\n" ==
  [html "1", html "3", html "5"]
-- The fence markers of the documentation audit are the raw HTML that is read.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" ("<!-- lean-fail: unknown identifier -->\n```lean\nexample := x\n```\n\n" ++
  "<!-- lean-trusted-compiler -->\n```lean\nexample := 1\n```\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "<!-- lean-fail: a --> RG2003 -->\n" == [html "1"]
-- Inline raw HTML is refused with its document. With it read as text, the backticks of the
-- second control would hide the ID in a code span.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Press <kbd>x</kbd> for `RG2003`.\n" ==
  [inlineHtml "<kbd>x</kbd> for <code>RG2003</code>.</p> "]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (check "a.md" "<span title=\"`\">RG2003`</span>\n").length == 1
-- A table with no body row is refused, and so is raw HTML that holds the same bytes, which is
-- refused as raw HTML in any case.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "| RG2003 |\n| --- |\n" == [bodyless]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "<!--\n</thead>\n</table>\n-->\n" == [bodyless]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "a\x00b\n" ==
  ["a.md: the document has a NUL character, which MD4Lean cannot represent in a code block"]
-- What GitHub reads otherwise is refused where md4c's parse shows it. A footnote that md4c reads
-- as a link reference definition makes its reference a link whose text starts with `^`.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Use[^n].\n\n[^n]: RG2003 \"description\"\n" == [s!"a.md:1: {caretReason}"]
-- The same inside an image's description, which is otherwise read as text alone.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "![caption[^n]](image.png).\n\n[^n]: RG2003 \"description\"\n" ==
  [s!"a.md:1: {caretReason}"]
-- With a `!` before it, md4c reads the reference as an image whose description starts with
-- `^`, also inside another image's description.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Note this![^1] here.\n\n[^1]: RG2003\n" == [s!"a.md:1: {caretReason}"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "![see ![^1] it](a.png) here.\n\n[^1]: RG2003\n" ==
  [s!"a.md:1: {caretReason}"]
-- Math: md4c reads `$…$` as text, where an ID is prose. A code span between dollar signs and a
-- fenced block with the info string `math` are code for md4c; GitHub renders both as math
-- (not seen).
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "$RG2003$ and $`RG2003`$\n\n```math\nRG2003\n```\n" == [bare "1"]
-- A footnote that md4c reads as a paragraph is prose, and its reference is text.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Use[^n].\n\n[^n]: See RG2003 for more.\n" == [bare "3"]
-- Not seen: GitHub starts a new block at the second footnote definition and at a table whose
-- header row follows a line of text, and shows each ID as prose; md4c reads on in one
-- paragraph, where the ID is code.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "[^a]: Use `x\n[^b]: RG2003 y` here.\n" == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Run it:\n| Command | Rule |\n| --- | --- |\n| `grep a | b RG2003` | x |\n" ==
  []
-- Not seen: GitHub shows YAML front matter as a table of its raw values; md4c reads it as a
-- thematic break and a heading, where a bare ID is refused and one in a code span is code.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard MD4Lean.renderHtml "---\nname: x\n---\n" github 0 == some "<hr>\n<h2>name: x</h2>\n"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "---\nname: x\ndescription: reports `RG2003`\n---\n\nText.\n" == [] &&
  check "a.md" "---\nname: x\ndescription: reports RG2003\n---\n\nText.\n" == [bare "3"]
-- A pipe character inside a code span in a table cell; outside a table the code span is code.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "| A | B |\n| --- | --- |\n| `a | b` `RG2003` | c |\n\n`a | RG2003`\n" ==
  [s!"a.md:3: {pipeReason}"]
-- A pipe character inside a link's text or an image's description in a table cell: md4c reads
-- the link or image whole, and GitHub ends the cell at the pipe character, which leaves the ID
-- of the first row as prose.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"| A |\n| --- |\n| [RG2003 | x]({page "RG2003"}) |\n" ++
  "| ![a | b](a.png) |\n") == (["3", "4"].map fun line => s!"a.md:{line}: {pipeReason}")
-- An escaped pipe character there is refused too, though it ends no cell for either: md4c
-- keeps the backslash in the code span, and the link's text and the image's description have
-- the pipe character without it.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"| A |\n| --- |\n| `a \\| b` |\n| [RG2003 \\| x]({page "RG2003"}) |\n" ++
  "| ![a \\| b](a.png) |\n") == (["3", "4", "5"].map fun line => s!"a.md:{line}: {pipeReason}")
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard match read "| A |\n| --- |\n| `a \\| b` |\n" with
  | .read pieces => pieces.contains (.code "a \\| b")
  | .unread _ => false
-- An escaped pipe character in a cell's own text is text for both, and is read.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "| A |\n| --- |\n| a \\| RG2003 |\n" == [bare "3"]
-- An autolink whose text has a rule ID, bare or in angle brackets, to the rule's page or not;
-- an autolink without one is a link.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"See {page "RG2003"} and\n<{page "RG2003"}> and\n" ++
  "<https://example.org/RG2003> and <https://example.org/>.\n") ==
  (["1", "2", "3"].map fun line => s!"a.md:{line}: RG2003 is in an autolink (a bare URL or \
    <URL>), whose end GitHub and md4c find by their own rules; write the link in brackets")

end Regula.Markdown
