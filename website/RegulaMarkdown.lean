import MD4Lean
import RegulaCore.Markdown

/-! # Markdown documents, read by md4c

`read` parses a Markdown document with md4c (through `MD4Lean`, which the pinned Verso brings)
and reports its parse as the pieces `Regula.Markdown.documentErrors` (`RegulaCore/Markdown.lean`)
decides on. Nothing here reads Markdown syntax: what is a paragraph, a code span, a table cell
or a link, which link reference definition a reference uses, and what a character reference
stands for, is md4c's.

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

Three constructs are refused where md4c's parse shows them, because GitHub reads them
otherwise (the contributor guide names the differences):

- a link whose text starts with `^`, which GitHub reads as a footnote reference;
- a code span with a pipe character in a table cell, where GitHub ends the cell;
- an autolink whose text has a rule ID, since the two find the end of a bare URL by their own
  rules, and MD4Lean does not tell a bare URL from `<URL>`.

## Trusted

md4c's conformance to CommonMark and to GitHub's extensions it implements; MD4Lean's wrapper,
for documents not refused above; that md4c's HTML renderer and the wrapper see the same parse of
the same text and flags; and md4c's rendering of a character reference alone, which is how one
is decoded (`decode`).
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

/-- The text of a link destination as md4c reports it, each character reference decoded. -/
def destination (parts : Array AttrText) : String :=
  String.join (parts.toList.map fun
    | .normal text => text
    | .entity reference => (decode reference).getD reference
    | .nullchar => replacement)

/-- The pieces of one character reference in prose. -/
def reference (slice : String) : List Piece :=
  match decode slice with
  | some rendered => [.text slice rendered]
  | none => [.refused s!"md4c does not decode the character reference {slice}", .text slice slice]

/-- Why a code span with a pipe character in a table cell is refused. -/
def pipeReason : String :=
  "a code span in a table cell has a pipe character, where GitHub ends the cell; write the \
    cell without it"

/-- The pieces of a code span: code, refused when it has a pipe character in a table cell
(`cell`). -/
def codeSpan (cell : Bool) (slices : Array String) : List Piece :=
  (if cell && slices.any (·.contains '|') then [.refused pipeReason] else []) ++
    slices.toList.map Piece.code

/-- The pieces of one element of an image's description, as md4c renders the description: its
text alone. Emphasis, links and images inside it give their text, and a code span's text is
description text too. -/
def flat (cell : Bool) (text : Text) : List Piece :=
  match text with
  | .normal slice => [.text slice slice]
  | .nullchar => [.text "" replacement]
  | .br _ | .softbr _ => [.line]
  | .entity slice => reference slice
  | .em texts | .strong texts | .u texts | .del texts | .a _ _ _ texts | .wikiLink _ texts =>
    texts.attach.toList.flatMap fun ⟨inner, _⟩ => flat cell inner
  | .img _ _ description => description.attach.toList.flatMap fun ⟨inner, _⟩ => flat cell inner
  | .code slices | .latexMath slices | .latexMathDisplay slices =>
    (if cell && slices.any (·.contains '|') then [.refused pipeReason] else []) ++
      slices.toList.map fun slice => .text slice slice
termination_by text
decreasing_by
  all_goals
    have := Array.sizeOf_lt_of_mem ‹inner ∈ _›
    simp_wf
    omega

/-- The text a run of pieces renders as. -/
def visible (pieces : List Piece) : String :=
  String.join (pieces.map fun
    | .text _ rendered => rendered
    | .code slice => slice
    | _ => "")

/-- The first rule-ID token of `text`, if it has one. -/
def firstToken (text : String) : Option String :=
  (Regula.Prose.splitTokens none 0 [] text.toList).findSome? fun
    | .inr token => some token
    | .inl _ => none

/-- The pieces of a link with text `body` that leads to `leads`; `auto` is whether md4c reports
it as an autolink. A link whose text starts with `^` is refused: GitHub reads `[^label]` as a
footnote reference, and md4c makes a link of it only when it has read the footnote as a link
reference definition, whose text it does not report. An autolink whose text has a rule ID is
refused, and its text is then not read as link text. -/
def link (leads : String) (auto : Bool) (body : List Piece) : List Piece :=
  if (visible body).startsWith "^" then
    .refused "a link's text starts with ^, which GitHub reads as a footnote reference; md4c \
      has read the footnote as a link reference definition, so its text is not checked" ::
      .enter leads :: body ++ [.leave]
  else
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
code. LaTeX math and wiki links are not enabled; their text would be prose. -/
def inline (cell : Bool) (text : Text) : List Piece :=
  match text with
  | .normal slice => [.text slice slice]
  | .nullchar => [.text "" replacement]
  | .br _ | .softbr _ => [.line]
  | .entity slice => reference slice
  | .em texts | .strong texts | .u texts | .del texts | .wikiLink _ texts =>
    texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline cell inner
  | .a href _ auto texts =>
    link (destination href) auto (texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline cell inner)
  | .img _ _ description => .gap :: description.toList.flatMap (flat cell) ++ [.gap]
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
#guard check "a.md" "Use[^n].\n\n[^n]: RG2003 \"description\"\n" ==
  ["a.md:1: a link's text starts with ^, which GitHub reads as a footnote reference; md4c has \
    read the footnote as a link reference definition, so its text is not checked"]
-- A footnote that md4c reads as a paragraph is prose, and its reference is text.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Use[^n].\n\n[^n]: See RG2003 for more.\n" == [bare "3"]
-- A code span with a pipe character in a table cell; outside a table it is code.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "| A | B |\n| --- | --- |\n| `a | b` `RG2003` | c |\n\n`a | RG2003`\n" ==
  ["a.md:3: a code span in a table cell has a pipe character, where GitHub ends the cell; write \
    the cell without it"]
-- An autolink whose text has a rule ID, bare or in angle brackets, to the rule's page or not;
-- an autolink without one is a link.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"See {page "RG2003"} and\n<{page "RG2003"}> and\n" ++
  "<https://example.org/RG2003> and <https://example.org/>.\n") ==
  (["1", "2", "3"].map fun line => s!"a.md:{line}: RG2003 is in an autolink (a bare URL or \
    <URL>), whose end GitHub and md4c find by their own rules; write the link in brackets")

end Regula.Markdown
