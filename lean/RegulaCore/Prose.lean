import RegulaCore.Site
import Regula.Decision

/-! # Rule IDs in prose

Every rule ID that a page mentions in prose is a link to that rule's page. This module defines
what prose is in a rendered HTML page, decides whether a page has a rule ID in prose that is not
such a link, and rewrites generated prose so that it has none.

## Main declarations

- `tokenAt`, `splitTokens`: a rule-ID token is `RG` and four digits with no ASCII letter or digit
  directly before or after it, so emphasis such as `_RG2003_` does not hide one.
- `Run`, `Mention`, `Run.mentions`: a run is a maximal piece of prose with the destination of the
  link it lies in, if any; a mention is one token of a run.
- `Mention.Linked`, `bareMentions`, `bareMentions_nil_iff`, `checked_bareMentions`: a mention is
  linked when its token is a registered rule ID and its link's destination is that rule's page;
  the executed check returns nothing exactly when every mention of every run is linked.
- `pageTarget`, `pageTarget_iff`: the page of a rule for a rendered page of an edition (the rule's
  page file of that edition).
- `htmlRuns`, `ownPage`: the prose of an HTML page, and the one place a rule ID is not written as
  a link, a rule page's own title and top heading.
- `htmlErrors`, `htmlErrors_nil_iff`: the executed page check, reporting the file, the line and the
  ID.
- `relativeCitation`, `rewriteIds`, `linkIds`, `linkVerso`: the link a generated page gives a
  rule, relative to its edition's root (`RuleId.route`), and the rewriting of generated prose that
  inserts it.

## What prose is

In an HTML page, prose is the text outside the `code`, `pre`, `script` and `style` elements
(`exemptElement`). Pasted tool output is a `pre` element; a Lean identifier is code. A rule table
that is the index of rule pages names each rule as a link to its page, so its IDs are linked
mentions. A heading is prose. The one rule ID that is not written as a link is a rule page's own,
in that page's `title` and `h1`, because a page cannot usefully link to itself (`ownPage`): those
two elements are read as text linked to the page they name.

## Boundaries

`bareMentions_nil_iff` is about the runs it is given. `htmlRuns` is a small scanner for the
builder's own output, not an HTML parser. An element, comment or script that is never closed
would hide the text after it, so `htmlErrors` refuses such a page; an element closed and reopened
out of order is not detected. Markdown documents are not read here: `Regula.Markdown`
(`RegulaCore/Markdown.lean`) decides the same question for a tracked Markdown document from a
CommonMark parser's reading of it, with this module's tokens and `Mention.Linked`. `linkIds`
rewrites generated prose outside its code spans, inline links and bare URLs (`scanGenerated`);
that its output has no bare rule ID is established by `htmlErrors` on the rendered pages, not by a
theorem about the rewriting. The Markdown agent briefing (`Regula.Guidance.briefRule`) links its
rule IDs itself (`Regula.Guidance.citation`); the generated agent skill the repository tracks is
checked as a Markdown document.
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
@[regula_decision]
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

/-- Registered contract of the executed prose check, as a two-way decision over the page
predicate and the runs (`bareMentions_nil_iff`): it reports nothing for no run, and reports a
bare rule ID in a run outside every link. -/
theorem checked_bareMentions : Regula.ExecutableContract bareMentions (fun run =>
    Regula.Decides (· = [])
      (fun input : (RuleId → String → Bool) × List Run =>
        ∀ r ∈ input.2, ∀ m ∈ r.mentions, m.Linked input.1)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => bareMentions_nil_iff input.1 input.2)
    ⟨(fun _ _ => false, []), (bareMentions_nil_iff _ []).mpr (by simp)⟩
    ⟨(fun _ _ => false, [⟨1, "RG1001", none⟩]),
      (by decide +kernel : ¬ bareMentions (fun _ _ => false) [⟨1, "RG1001", none⟩] = [])⟩⟩

/-- Why a mention that is not linked is refused. -/
def Mention.reason (m : Mention) : String :=
  match RuleId.parse? m.token, m.link with
  | none, _ => "is not a registered rule ID"
  | some _, none => "is a bare rule ID in prose; make it a link to its rule page"
  | some _, some destination => s!"is linked to {destination}, which is not its rule page"

/-- What a refused mention reports: the file, the line, the ID and why it is refused. -/
def Mention.describe (file : String) (m : Mention) : String :=
  s!"{file}:{m.line}: {m.token} " ++ m.reason

/-! ## Rule pages -/

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

/-- One piece of generated prose. The pieces' texts, in order, are the text. -/
inductive Piece where
  /-- Prose, whose rule IDs `linkIds` makes links. -/
  | prose (text : String)
  /-- Text kept as written: a code span, an inline link or a bare URL. -/
  | kept (text : String)
  deriving DecidableEq, Repr

private def flush (acc : List Char) : List Piece :=
  if acc.isEmpty then [] else [.prose (String.ofList acc.reverse)]

/-- The number of characters through the end of the first run of exactly `n` backticks; `run` is
the length of the backtick run in progress. -/
def codeClose (n : Nat) : Nat → List Char → Option Nat
  | run, [] => if run == n then some 0 else none
  | run, c :: rest =>
    if c == '`' then (codeClose n (run + 1) rest).map (· + 1)
    else if run == n then some 0
    else (codeClose n 0 rest).map (· + 1)

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

/-- Whether `chars` starts a bare URL. -/
def startsUrl (chars : List Char) : Bool :=
  "https://".toList.isPrefixOf chars || "http://".toList.isPrefixOf chars

/-- The length of the URL at the head of `chars`: up to whitespace, a bracket, a quote or a
backtick. -/
def urlLength (chars : List Char) : Nat :=
  (chars.takeWhile fun c => !(c.isWhitespace || c == '<' || c == '>' || c == '(' || c == ')' ||
    c == '[' || c == ']' || c == '`' || c == '"')).length

/-- The number of characters after a `[` through the end of the inline link `[text](target)` it
opens, when it opens one. -/
def linkLength (rest : List Char) : Option Nat :=
  (closeIndex '[' ']' 0 rest).bind fun i =>
    match rest.drop (i + 1) with
    | '(' :: tail => (closeIndex '(' ')' 0 tail).map (i + · + 3)
    | _ => none

/-- The pieces of generated prose: its prose and, kept as written, its code spans, inline links
and bare URLs. `acc` is the prose since the last piece, reversed; the first argument bounds the
steps and is at least the text's length. A backslash keeps the character after it as prose. -/
def scanGenerated : Nat → List Char → List Char → List Piece
  | 0, _, acc => flush acc
  | _, [], acc => flush acc
  | fuel + 1, c :: rest, acc =>
    let keep (n : Nat) : List Piece := flush acc ++
      Piece.kept (String.ofList ((c :: rest).take n)) :: scanGenerated fuel ((c :: rest).drop n) []
    if c == '\\' then
      match rest with
      | d :: tail => scanGenerated fuel tail (d :: c :: acc)
      | [] => flush (c :: acc)
    else if c == '`' then
      let n := 1 + (rest.takeWhile (· == '`')).length
      match codeClose n 0 (rest.drop (n - 1)) with
      | some k => keep (n + k)
      | none => scanGenerated fuel (rest.drop (n - 1)) (List.replicate n '`' ++ acc)
    else if startsUrl (c :: rest) then keep (urlLength (c :: rest))
    else if c == '[' then
      match linkLength rest with
      | some k => keep (k + 1)
      | none => scanGenerated fuel rest (c :: acc)
    else scanGenerated fuel rest (c :: acc)

/-- Generated prose, in the link syntax Markdown and Verso share, with each registered rule ID in
its prose (`scanGenerated`) replaced by `rule` of it. Code spans, inline links and bare URLs are
kept as written. -/
def linkIds (rule : RuleId → String) (text : String) : String :=
  String.join ((scanGenerated (text.length + 1) text.toList []).map fun
    | .prose between => rewriteIds id rule between
    | .kept raw => raw)

/-- Generated Verso prose with each registered rule ID in prose made a link to its page in the
same edition (`relativeCitation`). -/
def linkVerso (text : String) : String := linkIds relativeCitation text

/-! Evaluated controls (observations of the compiled scanners, not proofs). A bare ID in a page's
prose is refused with its file and line; a link to another page is refused; a heading is prose, so
a bare ID in one is refused, except a rule's own ID in the title and top heading of its own page;
and each exempt construct is accepted: code, pasted tool output, a rule index table whose IDs are
links, comments and scripts. -/
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
