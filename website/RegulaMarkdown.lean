import MD4Lean
import RegulaCore.Markdown

/-! # Markdown documents, read by md4c

`read` parses a Markdown document with md4c (through `MD4Lean`, which the pinned Verso brings)
and reports its parse as the pieces `Regula.Markdown.documentErrors` (`RegulaCore/Markdown.lean`)
decides on. Nothing here reads Markdown syntax: what is a paragraph, a code span, a table cell
or a link, and which link reference definition a reference uses, is md4c's parse.

## The parse

md4c runs with its GitHub dialect: CommonMark with tables, strikethrough, task lists and
permissive autolinks (`MD4Lean.MD_DIALECT_GITHUB`). Three shapes of a document are refused
instead of read, each because `MD4Lean.parse` has no value for what md4c reports of it:

- Inline raw HTML. The wrapper stores its text as a string among the inline elements, which is
  not a value of `MD4Lean.Text` (reading such a parse crashed when tried on the pinned
  revision), so the parse runs with inline raw HTML read as text
  (`MD4Lean.MD_FLAG_NOHTMLSPANS`). A document is read only when md4c renders it to the same HTML
  with and without that flag: the parse then describes the rendering GitHub's dialect gives.
- A table with no body row, for which md4c reports no table body and the wrapper expects one.
- A NUL character, which the wrapper stores among the strings of a code block as an inline
  element.

Raw HTML blocks are read, as the text md4c reports.

## Trusted

md4c's conformance to CommonMark and to GitHub's extensions it implements; MD4Lean's wrapper,
for documents not refused above; and that md4c's HTML renderer and the wrapper see the same
parse of the same text and flags. The contributor guide names the differences between md4c and
GitHub's renderer that bear on this check.
-/

namespace Regula.Markdown

open MD4Lean (Text Block AttrText)

/-- GitHub's dialect, as md4c implements it. -/
def github : UInt32 := MD4Lean.MD_DIALECT_GITHUB

/-- GitHub's dialect with inline raw HTML read as text. -/
def htmlAsText : UInt32 := MD4Lean.MD_DIALECT_GITHUB ||| MD4Lean.MD_FLAG_NOHTMLSPANS

/-- The text of a link destination as md4c reports it. -/
def destination (parts : Array AttrText) : String :=
  String.join (parts.toList.map fun
    | .normal text => text
    | .entity reference => decodeReference reference
    | .nullchar => "�")

/-- The pieces of one inline element, where `link` is the destination of the link it lies in.
Emphasis, strong emphasis, underline and strikethrough continue the prose around them; a link's
text is prose linked to its destination; an image's description is prose where the image stands;
a code span is code. LaTeX math and wiki links are not enabled; their text would be prose. -/
def inline (link : Option String) (text : Text) : List Piece :=
  match text with
  | .normal slice => [.text slice slice link]
  | .nullchar => [.text "" "�" link]
  | .br _ | .softbr _ => [.line]
  | .entity reference => [.text reference (decodeReference reference) link]
  | .em texts | .strong texts | .u texts | .del texts =>
    texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline link inner
  | .a href _ _ texts =>
    .gap :: (texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline (some (destination href)) inner)
      ++ [.gap]
  | .img _ _ description => description.attach.toList.flatMap fun ⟨inner, _⟩ => inline link inner
  | .code slices => .gap :: slices.toList.map Piece.code
  | .latexMath slices | .latexMathDisplay slices =>
    .gap :: slices.toList.map fun slice => .text slice slice link
  | .wikiLink _ texts => texts.attach.toList.flatMap fun ⟨inner, _⟩ => inline link inner
termination_by text
decreasing_by
  all_goals
    have := Array.sizeOf_lt_of_mem ‹inner ∈ _›
    simp_wf
    omega

/-- The pieces of a block's inline content. -/
def inlines (texts : Array Text) : List Piece := texts.toList.flatMap (inline none)

/-- The pieces of a code block or raw HTML block: md4c reports each line's text and then its
line end, so each `"\n"` is a line boundary. -/
def verbatim (piece : String → Piece) (slices : Array String) : List Piece :=
  slices.toList.map fun slice => if slice == "\n" then .line else piece slice

/-- The pieces of the cells of one table row, which lie on one source line. -/
def row (cells : Array (Array Text)) : List Piece :=
  cells.toList.flatMap fun cell => .gap :: inlines cell

/-- The pieces of one block. Each leaf block starts on a later source line than the text before
it, as does each row of a table. -/
def block (b : Block) : List Piece :=
  match b with
  | .p texts | .header _ texts => .line :: inlines texts
  | .ul _ _ items | .ol _ _ _ items =>
    items.attach.toList.flatMap fun ⟨item, _⟩ =>
      item.contents.attach.toList.flatMap fun ⟨inner, _⟩ => block inner
  | .hr => []
  | .code _ _ _ slices => .line :: verbatim Piece.code slices
  | .html slices => .line :: verbatim Piece.raw slices
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
        .unread s!"md4c reads inline raw HTML, which this check cannot read (MD4Lean has no \
          value for it); write it in Markdown or as an HTML block: {difference html escaped}"
      else if escaped.contains "</thead>\n</table>" then
        .unread "a table has no body row, which MD4Lean cannot represent"
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
-- accepted, whether the link is inline, a reference, an autolink or a bare URL.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" ("Use `RG2003` or ``a ` RG2003``.\n\n```text\nRG2003 [violation]\n```\n\n" ++
  "    RG2003 indented\n\n~~~\nRG2003\n~~~\n") == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"See [RG2003]({page "RG2003"}), [the RG2003 fix]({page "RG2003"}#fix),\n" ++
  s!"[RG2003], [RG2003][], [it][RG2003], <{page "RG2003"}> and {page "RG2003"}\n\n" ++
  s!"[RG2003]: {page "RG2003"}\n") == []
-- A link elsewhere, an unregistered ID and an ID in an image description are refused.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"[RG2003]({page "RG2002"}) and RG9999 and ![RG2003](a.png)\n") ==
  [s!"a.md:1: RG2003 is linked to {page "RG2002"}, which is not its rule page",
    "a.md:1: RG9999 is not a registered rule ID", bare "1"]
-- Link reference definitions: a reference without a definition is prose, a definition is not
-- prose, and a definition of another page is refused where it is used. That last link's text
-- also occurs on the definition's line, after everything else, so its lines are bracketed.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "See [RG2003] and [RG2002].\n\n[RG2002]: https://example.org/RG2002\n" ==
  [bare "1",
    "a.md:1-3: RG2002 is linked to https://example.org/RG2002, which is not its rule page"]
-- A numeric character reference spells the ID; an unknown named reference is text.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "R&#71;2003 and &RG2003;\n" == [bare "1", bare "1"]
-- Raw HTML: an ID in a block is refused, in a comment too; inline raw HTML is not read.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "<p>\nSee RG2003\n</p>\n\n<!-- RG2003 -->\n\n<!-- lean-fail: x -->\n" ==
  ["a.md:2: RG2003 is in a raw HTML block, which is not read as prose; write it in Markdown, \
      as a link to its rule page",
    "a.md:5: RG2003 is in a raw HTML block, which is not read as prose; write it in Markdown, \
      as a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "Press <kbd>x</kbd> for `RG2003`.\n" ==
  ["a.md: md4c reads inline raw HTML, which this check cannot read (MD4Lean has no value for \
    it); write it in Markdown or as an HTML block: <kbd>x</kbd> for <code>RG2003</code>.</p> "]
-- With inline raw HTML read as text the backticks below would hide the ID in a code span.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard (check "a.md" "<span title=\"`\">RG2003`</span>\n").length == 1
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "| RG2003 |\n| --- |\n" ==
  ["a.md: a table has no body row, which MD4Lean cannot represent"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" "a\x00b\n" ==
  ["a.md: the document has a NUL character, which MD4Lean cannot represent in a code block"]
-- A line that only looks like the text is not reported: the definition's line is not the
-- mention's.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard check "a.md" (s!"[RG2002]: {page "RG2002"}\n\nSee RG2002 and [RG2002].\n") ==
  [bare "3" "RG2002"]

end Regula.Markdown
