import RegulaCore.Prose
import Regula.Decision

/-! # Rule IDs in Markdown documents

Every rule ID that a tracked Markdown document mentions in prose is a link to that rule's page.
This module decides that from what a CommonMark parser reports of the document. It reads no
Markdown itself: `Regula.Markdown.read` (`markdown/RegulaMarkdown.lean`) runs md4c and turns its
parse into the `Piece`s below, so what is a paragraph, a code span or a link in the source is
md4c's decision, and which piece each becomes is that module's (see Boundaries).

## Main declarations

- `Kind`, `Piece`, `Reading`: what the parser reports of a document, in document order: prose,
  code, the edges of each link's text, the constructs the check refuses, the boundaries between
  runs and between source lines, and the start of each block with its kind.
- `Place`, `Standing`, `Found`, `findings`: the rule-ID tokens (`Regula.Prose.tokenAt`) of the
  rendered text, each with how it stands, and the refused constructs. A token is read over the
  whole text of a run, so one that a link's edge or a code span's edge divides is found too.
- `Found.Accepted`, `rejected`, `rejected_nil_iff`: a finding is accepted only when it is a
  registered rule ID all of which lies in the text of one link to that rule's page
  (`Regula.Prose.Mention.Linked`).
- `PiecesAccepted`, `IsRun`, `RunText`, `StandsAfter`, `Closed`, `RunLinked`: what the check
  decides, stated over the list of pieces and the characters of the text. A run is a part of the
  pieces with no piece that ends a run, where the piece before it and the piece after it, if
  any, end a run. Prose stands in the text of the link that is entered last and not yet left.
  Each rule-ID token (`Regula.Prose.TokenAt`) of the text of a run is wholly code, or stands
  wholly in one link to its rule's page.
- `findings_accepted_iff`: the findings of the scan are accepted exactly when the document is
  accepted in that statement.
- `stableDocuments`, `target`, `Target`, `target_iff`, `released`, `released_iff`: the pages a
  Markdown document links a rule to: its development page, or, in a document of `stableDocuments`
  only, its stable address when the rule is in a release. `Target` states them with no test, and
  `target` decides it.
- `auditMarker`: the one form of raw HTML that is read, a fence marker of the documentation audit.
- `Anchor`, `Placed`, `leftmost`, `rightmost`, `leftmost_le`, `le_rightmost`: the source lines of
  a finding. The parser reports text, not positions, so the lines are bracketed: every placement
  of the reported text on the source lines, in order, puts each piece between the lines
  `leftmost` and `rightmost` return for it.
- `documentErrors`, `documentErrors_nil_iff`, `checked_documentErrors`: the executed check of one
  document, reporting the file, the line or lines and the ID or the refused construct; a
  document whose reading cannot be used is reported by file and reason alone, without its IDs.
- `OnSite`, `Stable`, `Stable.not_edition`, `siteLinkErrors`, `siteLinkErrors_nil_iff`,
  `checked_siteLinkErrors`: the executed check of the links of each document of
  `stableDocuments` to the site. Each has a stable address, the site root or an address below a
  `stableRoots` directory with no fragment, so it names no edition.

## What prose is

Prose is every text the parser reports outside code spans and code blocks: paragraphs, headings,
list items, block quotes, table cells, emphasis, link text and image descriptions. A run is the
text of one line of a block, or of one table cell or image description: its prose, the text of
its links and the text of its code spans, in order. A rule-ID token of a run's text is a mention
unless all of it is code. A mention is accepted only when all of it lies in the text of one link
whose destination is the rule's page, whether the link is written inline or as a reference to a
link reference definition; a mention that a link's edge or a code span's edge divides is
refused. Link destinations and titles, code block info strings and link reference definitions
are not prose.

## Boundaries

`rejected_nil_iff` and `documentErrors_nil_iff` are about the pieces they are given. That the
pieces are the document's is not proved, and has two parts: the parser's reading of the
document, which is trusted, and the translation of that reading into pieces (`read` and every
definition it calls in `markdown/RegulaMarkdown.lean`: `block`, `inline`, `flat`, `link` and the
rest), which is project-owned Lean with no theorem. That translation
decides which piece each element the parser reports becomes, and is observed only by that
module's evaluated controls. Both parts are stated there and in the contributor guide.
`siteLinkErrors_nil_iff` is about the link destinations among those pieces: a link that the
parser does not report as a link, an image and a link reference definition that no link uses are
not read. An address of the site is a destination that has `siteAddress`, in that spelling.
That a stable address has a page is not decided here. `target` accepts the stable address of a
rule only in a document of `stableDocuments`, and the site build requires in its artifact each
address that `Regula.Site.siteAnchors` finds in the text of each document of that same list: an
address written as a literal `siteBase`, as that module's boundaries state.
`leftmost_le` and `le_rightmost` bound every placement that `Placed`
admits; that the true lines of the reported text are such a placement rests on the parser
reporting each piece of text as it stands on one source line, in source order, and on a line
break or a new block lying between pieces of different lines. When no placement exists, the
whole document is the bracket.
-/

namespace Regula.Markdown

open Regula.Prose

/-! ## What the parser reports -/

/-- The kind of a block of a document, as far as the checks of its prose tell blocks apart
(`RegulaCore/ControlledProse.lean`). The rule-ID check does not read it. -/
inductive Kind where
  /-- A heading. -/
  | heading
  /-- A paragraph that is in no list item: also such a paragraph of a block quote. -/
  | paragraph
  /-- A paragraph in an item of an ordered list, at each depth: also in an unordered list or a
  block quote in that item. -/
  | step
  /-- A paragraph in items of unordered lists only: also in a block quote there. -/
  | bullet
  /-- A table cell that is in no item of an ordered list. -/
  | cell
  /-- A table cell in an item of an ordered list, at each depth. -/
  | stepCell
  /-- A code block or a raw HTML block, which has no prose. -/
  | code
  deriving DecidableEq, Repr

/-- One piece of a Markdown document as its parser reports it, in document order. -/
inductive Piece where
  /-- Prose: `slice` is the text as the parser reported it from the source and `rendered` what it
  renders as (a character reference decoded). It lies in the text of the link entered last and
  not yet left, if any. -/
  | text (slice rendered : String)
  /-- Text of a code span or code block, as the parser reported it from the source. -/
  | code (slice : String)
  /-- The start of the text of a link that leads to `destination`. -/
  | enter (destination : String)
  /-- The end of a link's text. -/
  | leave
  /-- A construct the check refuses to read, for the reason given. Its place is that of the next
  piece with source text. -/
  | refused (reason : String)
  /-- A boundary between two runs on one source line: the edge of a table cell or of an image's
  description. -/
  | gap
  /-- A line boundary: the pieces after it lie on a later source line than the pieces before
  it. -/
  | line
  /-- The start of a block of `kind`: the pieces from here to the next start are the block's. -/
  | start (kind : Kind)
  deriving DecidableEq, Repr

/-- What the parser reports of one document. -/
inductive Reading where
  /-- The parser's reading cannot be used, for the reason given. -/
  | unread (reason : String)
  /-- The document's pieces, in document order. -/
  | read (pieces : List Piece)
  deriving DecidableEq, Repr

/-! ## Findings -/

/-- `text` has no character other than whitespace, as a proposition. The parser reports the
spaces and line ends it supplies itself as such text, so only other text is located in the
source. It is stated with no test of this module: a function decides it with Lean's own test of
a character. -/
def Blank (text : String) : Prop := ∀ c ∈ text.toList, c.isWhitespace = true

instance (text : String) : Decidable (Blank text) := by
  unfold Blank; infer_instance

/-- The source text that locates a piece: what the parser reported for it, unless it is
`Blank`. -/
def Piece.located? : Piece → Option String
  | .text slice _ | .code slice => if Blank slice then none else some slice
  | .enter _ | .leave | .refused _ | .gap | .line | .start _ => none

/-- Where one character of a run stands. -/
inductive Place where
  /-- In prose outside every link. -/
  | prose
  /-- In the text of the link numbered `index` in the document, which leads to `destination`:
  the innermost link, where a link's text holds another link. -/
  | link (index : Nat) (destination : String)
  /-- In a code span or a code block. -/
  | code
  deriving DecidableEq, Repr

/-- How a rule-ID token of a run stands. -/
inductive Standing where
  /-- All of it is prose outside every link. -/
  | bare
  /-- All of it is in the text of one link, which leads to `destination`. -/
  | linked (destination : String)
  /-- Its characters stand in different places: a link's edge or a code span's edge divides
  it. -/
  | split
  deriving DecidableEq, Repr

/-- What the check finds at one place of a document. -/
inductive Finding where
  /-- A rule-ID token of a run that is not wholly code, such as `RG1001`. -/
  | mention (token : String) (standing : Standing)
  /-- A construct the check refuses to read, with the reason. -/
  | refused (reason : String)
  deriving DecidableEq, Repr

/-- One finding and its place. -/
structure Found where
  /-- What was found. -/
  finding : Finding
  /-- The number of located pieces (`Piece.located?`) before the piece it starts in. -/
  anchor : Nat
  deriving DecidableEq, Repr

/-- One part of a run. -/
structure Part where
  /-- The number of located pieces before its piece. -/
  anchor : Nat
  /-- Where its characters stand. -/
  place : Place
  /-- Its rendered text. -/
  text : String
  deriving DecidableEq, Repr

/-- How a token whose characters stand at `places` stands; `none` when all of it is code, which
is then no mention. -/
def standing : List Place → Option Standing
  | [] => none
  | first :: rest =>
    if rest.all (· == first) then
      match first with
      | .prose => some .bare
      | .link _ destination => some (.linked destination)
      | .code => none
    else some .split

/-- The mentions of one run, whose text is the texts of `parts` in order. Each character of the
text has a tag, the anchor and place of its part; the tags not yet passed are carried along the
text's tokens and the text between them, so the run is read once. -/
def runTokens (parts : List Part) : List Found :=
  let tags : List (Nat × Place) :=
    parts.flatMap fun part => List.replicate part.text.length (part.anchor, part.place)
  ((splitTokens none 0 [] (String.join (parts.map (·.text))).toList).foldl
    (fun (acc : List (Nat × Place) × List Found) piece =>
      match piece with
      | .inl between => (acc.1.drop between.length, acc.2)
      | .inr token =>
        let here := acc.1.take token.length
        (acc.1.drop token.length,
          match standing (here.map (·.2)) with
          | some stands => ⟨.mention token stands, (here.head?.map (·.1)).getD 0⟩ :: acc.2
          | none => acc.2))
    (tags, [])).2.reverse

/-- The state of the scan of a document's pieces. -/
structure Scan where
  /-- The number of located pieces read so far. -/
  anchor : Nat := 0
  /-- The number of links entered so far. -/
  links : Nat := 0
  /-- The links entered and not yet left, the one entered last first, each with its number. -/
  entered : List (Nat × String) := []
  /-- The parts of the run in progress, last first. -/
  run : List Part := []
  /-- The findings so far, last first. -/
  found : List Found := []

/-- End the run in progress and keep its mentions. -/
def Scan.flush (s : Scan) : Scan :=
  { s with run := [], found := (runTokens s.run.reverse).reverse ++ s.found }

/-- The scan after a piece with source text `slice`. -/
def Scan.past (s : Scan) (slice : String) : Scan :=
  if Blank slice then s else { s with anchor := s.anchor + 1 }

/-- Where prose read now stands: in the text of the link entered last and not yet left, if
any. This is how the pieces are read, not a claim about how a link inside a link's text is
rendered: where the pieces are made from md4c's parse, such a link is refused
(`Regula.Markdown.nested` in `markdown/RegulaMarkdown.lean`). -/
def Scan.place (s : Scan) : Place :=
  match s.entered with
  | (index, destination) :: _ => .link index destination
  | [] => .prose

/-- Read one piece. Prose and code continue the run in progress, each character with its place;
the edge of a table cell or of an image's description, a line boundary and the start of a block
end it, so a token is read across the edges of links and code spans and across nothing else. A
link's text may hold
another link: leaving the inner link returns to the outer link's text. md4c reports an autolink
inside a link's text so, a bare URL and `<URL>` alike, and its reading of such a link is
refused where the pieces are made, since GitHub renders neither form that way. -/
def Scan.step (s : Scan) : Piece → Scan
  | .text slice rendered =>
    Scan.past { s with run := ⟨s.anchor, s.place, rendered⟩ :: s.run } slice
  | .code slice => Scan.past { s with run := ⟨s.anchor, .code, slice⟩ :: s.run } slice
  | .enter destination =>
    { s with entered := (s.links, destination) :: s.entered, links := s.links + 1 }
  | .leave => { s with entered := s.entered.tail }
  | .refused reason => { s with found := ⟨.refused reason, s.anchor⟩ :: s.found }
  | .gap | .line | .start _ => s.flush

/-- The findings of a document: the mentions of its runs and its refused constructs, run by run
in document order. Within one run the constructs refused in it come first, then its mentions. -/
def findings (pieces : List Piece) : List Found :=
  (pieces.foldl Scan.step {}).flush.found.reverse

/-- `f` is accepted: it is a rule-ID token, a registered rule ID, all of which lies in the text of
one link whose destination `target` accepts as that rule's page. A refused construct, a bare
mention and a mention that an edge divides are not accepted. -/
def Found.Accepted (target : RuleId → String → Bool) (f : Found) : Prop :=
  ∃ token destination, f.finding = .mention token (.linked destination) ∧
    (⟨0, token, some destination⟩ : Mention).Linked target

/-- `Found.Accepted`, decided. -/
def Found.accepted (target : RuleId → String → Bool) (f : Found) : Bool :=
  match f.finding with
  | .mention token (.linked destination) =>
    (⟨0, token, some destination⟩ : Mention).linked target
  | _ => false

theorem Found.accepted_iff (target : RuleId → String → Bool) (f : Found) :
    f.accepted target = true ↔ f.Accepted target := by
  unfold Found.accepted Found.Accepted
  split
  · rename_i token destination h
    rw [Mention.linked_iff]
    constructor
    · intro hl
      exact ⟨token, destination, h, hl⟩
    · rintro ⟨token', destination', h', hl⟩
      rw [h] at h'
      cases h'
      exact hl
  · rename_i hne
    constructor
    · intro h
      cases h
    · rintro ⟨token, destination, h, _⟩
      exact (hne token destination h).elim

/-- The findings of `pieces` that are not accepted, in the order of `findings`. -/
def rejected (target : RuleId → String → Bool) (pieces : List Piece) : List Found :=
  (findings pieces).filter fun f => !f.accepted target

/-- Nothing is rejected exactly when every finding of the document is accepted: it has no
refused construct, and every rule-ID token of its runs that is not wholly code is a registered
rule ID inside one link to that rule's page. -/
theorem rejected_nil_iff (target : RuleId → String → Bool) (pieces : List Piece) :
    rejected target pieces = [] ↔ ∀ f ∈ findings pieces, f.Accepted target := by
  simp only [rejected, List.filter_eq_nil_iff, Bool.not_eq_true', Bool.not_eq_false]
  exact ⟨fun h f hf => (Found.accepted_iff target f).mp (h f hf),
    fun h f hf => (Found.accepted_iff target f).mpr (h f hf)⟩

/-! ## What the document says -/

/-- A piece ends a run: the edge of a table cell or of an image's description, a line boundary,
or the start of a block. -/
def Piece.EndsRun (piece : Piece) : Prop :=
  piece = .gap ∨ piece = .line ∨ ∃ kind, piece = .start kind

/-- The pieces leave each link that they enter, and they leave no other link: they are pieces
that are no edge of a link's text, and whole links whose text is such pieces. -/
inductive Closed : List Piece → Prop where
  /-- No piece. -/
  | nil : Closed []
  /-- A piece that is no edge of a link's text, and then closed pieces. -/
  | other {piece : Piece} {rest : List Piece} : (∀ destination, piece ≠ .enter destination) →
    piece ≠ .leave → Closed rest → Closed (piece :: rest)
  /-- A whole link whose text is closed, and then closed pieces. -/
  | link {destination : String} {inner rest : List Piece} : Closed inner → Closed rest →
    Closed (.enter destination :: (inner ++ .leave :: rest))

/-- The number of links that the pieces enter. -/
def linksIn (pieces : List Piece) : Nat := pieces.countP fun piece => piece matches .enter _

/-- Prose after the pieces `front` stands at `place`. It stands in the text of a link when
`front` is some pieces, the start of that link and then pieces that leave each link that they
enter (`Closed`): that link is entered last and not yet left, and its number is the number of
links entered before it. It stands outside every link when `front` has no such link. -/
def StandsAfter (front : List Piece) (place : Place) : Prop :=
  (∃ before destination inner, front = before ++ .enter destination :: inner ∧ Closed inner ∧
      place = .link (linksIn before) destination) ∨
    ((∀ before destination inner, front = before ++ .enter destination :: inner → ¬ Closed inner) ∧
      place = .prose)

/-- The characters of one piece, each with its place, where prose stands at `place`: prose
gives the characters of its rendered text at `place`, code gives its characters as code, and
each other piece gives no character. -/
def Piece.chars (place : Place) : Piece → List (Place × Char)
  | .text _ rendered => rendered.toList.map (place, ·)
  | .code slice => slice.toList.map (Place.code, ·)
  | .enter _ | .leave | .refused _ | .gap | .line | .start _ => []

/-- `text` is the text of the pieces `run`, which come after the pieces `front`: the characters
of each piece in order (`Piece.chars`), where the prose of a piece stands at the place that the
pieces before it give (`StandsAfter`). -/
inductive RunText : List Piece → List Piece → List (Place × Char) → Prop where
  /-- No piece has no character. -/
  | nil {front : List Piece} : RunText front [] []
  /-- The characters of the first piece, and then the text of the other pieces. -/
  | cons {front : List Piece} {piece : Piece} {rest : List Piece} {place : Place}
      {tail : List (Place × Char)} : StandsAfter front place →
    RunText (front ++ [piece]) rest tail → RunText front (piece :: rest) (piece.chars place ++ tail)

/-- The pieces `run` are a run of the document `before ++ run ++ after`: no piece of `run` ends
a run, the piece before `run`, if any, ends a run, and the piece after `run`, if any, ends a
run. -/
def IsRun (before run after : List Piece) : Prop :=
  (∀ piece ∈ run, ¬ piece.EndsRun) ∧ (∀ piece, before.getLast? = some piece → piece.EndsRun) ∧
    ∀ piece, after.head? = some piece → piece.EndsRun

instance (piece : Piece) : Decidable piece.EndsRun :=
  match piece with
  | .gap => isTrue (.inl rfl)
  | .line => isTrue (.inr (.inl rfl))
  | .start kind => isTrue (.inr (.inr ⟨kind, rfl⟩))
  | .text _ _ | .code _ | .enter _ | .leave | .refused _ => isFalse (by simp [Piece.EndsRun])

/-- The rule IDs of the text `run` of a run are linked to their pages: each rule-ID token of the
text (`Regula.Prose.TokenAt`) either is wholly code, or stands wholly in the text of one link,
is the spelling of a registered rule ID, and the link leads to that rule's page (`page`). The
statement names no function that reads tokens or decides how a token stands. -/
def RunLinked (page : RuleId → String → Prop) (run : List (Place × Char)) : Prop :=
  ∀ before chars after, run = before ++ chars ++ after →
    TokenAt (before.map (·.2)).getLast? (chars.map (·.2)) (after.map (·.2)) →
      (∀ c ∈ chars, c.1 = .code) ∨
        ∃ index destination id, (∀ c ∈ chars, c.1 = .link index destination) ∧
          String.ofList (chars.map (·.2)) = id.spelling ∧ page id destination

/-- The document with the pieces `pieces` is accepted: it has no construct that the check
refuses to read, and the rule IDs of the text of each of its runs are linked (`IsRun`,
`RunText`, `RunLinked`). The statement is over the list of pieces and the characters of the
text. It names no state of the scan and no function of the scan (`findings`, `Scan.step`,
`runTokens`, `standing`, `Regula.Prose.splitTokens`). -/
def PiecesAccepted (page : RuleId → String → Prop) (pieces : List Piece) : Prop :=
  (∀ reason, Piece.refused reason ∉ pieces) ∧
    ∀ before run after text, pieces = before ++ run ++ after → IsRun before run after →
      RunText before run text → RunLinked page text

/-! ### The scan reads this statement

The definitions and theorems of this part are steps of the proof of `findings_accepted_iff`,
and then `piecesAccepted_nil`, which the contract `checked_documentErrors` uses for the input
that it accepts. No specification names them. -/

/-- The texts of the runs that the scan reads, as one function: a step of the proof of
`findings_accepted_iff`, which no specification names. `links` is the number of links entered
before the pieces, `entered` the places of the links entered and not yet left, the one entered
last first, and `run` the text of the run in progress. -/
private def placed (links : Nat) (entered : List Place) (run : List (Place × Char)) :
    List Piece → List (List (Place × Char))
  | [] => [run]
  | .text _ rendered :: rest =>
    placed links entered (run ++ rendered.toList.map (entered.headD .prose, ·)) rest
  | .code slice :: rest => placed links entered (run ++ slice.toList.map (Place.code, ·)) rest
  | .enter destination :: rest => placed (links + 1) (.link links destination :: entered) run rest
  | .leave :: rest => placed links entered.tail run rest
  | .refused _ :: rest => placed links entered run rest
  | .gap :: rest | .line :: rest | .start _ :: rest => run :: placed links entered [] rest

/-- The characters of the parts of a run, each with the place of its part. -/
private def partChars (parts : List Part) : List (Place × Char) :=
  parts.flatMap fun part => part.text.toList.map (part.place, ·)

private theorem partChars_text (parts : List Part) :
    (partChars parts).map (·.2) = (String.join (parts.map (·.text))).toList := by
  rw [String.toList_join]
  induction parts with
  | nil => rfl
  | cons part parts ih =>
    simp only [partChars, List.flatMap_cons, List.map_append, List.map_map, List.map_cons] at ih ⊢
    rw [ih]
    simp [Function.comp_def]

private theorem partChars_places (parts : List Part) :
    (partChars parts).map (·.1) =
      (parts.flatMap fun part =>
        List.replicate part.text.length (part.anchor, part.place)).map (·.2) := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
    simp only [partChars, List.flatMap_cons, List.map_append, List.map_map,
      List.map_replicate] at ih ⊢
    rw [ih]
    simp [Function.comp_def, List.map_const', String.length_toList]

/-- A token has no standing exactly when each of its characters is code. -/
private theorem standing_eq_none_iff (places : List Place) :
    standing places = none ↔ ∀ place ∈ places, place = .code := by
  cases places with
  | nil => simp [standing]
  | cons first rest =>
    unfold standing
    by_cases same : rest.all (· == first) = true
    · simp only [same, ↓reduceIte]
      simp only [List.all_eq_true, beq_iff_eq] at same
      cases first with
      | prose => simp
      | link index destination => simp
      | code => simpa using same
    · simp only [same]
      simp only [List.all_eq_true, beq_iff_eq, Classical.not_forall] at same
      obtain ⟨place, member, differs⟩ := same
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, List.mem_cons, forall_eq_or_imp,
        false_iff, not_and]
      intro code all
      exact differs (member |> fun m => (all place m).trans code.symm)

/-- A token stands in the text of one link to `destination` exactly when it has a character
and each of its characters stands in the text of that one link. -/
private theorem standing_eq_linked_iff (places : List Place) (destination : String) :
    standing places = some (.linked destination) ↔
      places ≠ [] ∧ ∃ index, ∀ place ∈ places, place = .link index destination := by
  cases places with
  | nil => simp [standing]
  | cons first rest =>
    unfold standing
    by_cases same : rest.all (· == first) = true
    · simp only [same, ↓reduceIte]
      simp only [List.all_eq_true, beq_iff_eq] at same
      cases first with
      | prose => simp
      | code => simp
      | link index destination' =>
        simp only [Option.some.injEq, Standing.linked.injEq, ne_eq, reduceCtorEq,
          not_false_eq_true, List.mem_cons, forall_eq_or_imp, Place.link.injEq, true_and]
        constructor
        · rintro rfl
          exact ⟨index, ⟨rfl, rfl⟩, same⟩
        · rintro ⟨index', ⟨-, rfl⟩, -⟩
          rfl
    · simp only [same]
      simp only [List.all_eq_true, beq_iff_eq, Classical.not_forall] at same
      obtain ⟨place, member, differs⟩ := same
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, reduceCtorEq, ne_eq,
        not_false_eq_true, List.mem_cons, forall_eq_or_imp, true_and, false_iff, not_exists,
        not_and]
      intro index first' all
      exact differs ((all place member).trans first'.symm)

/-- The finding of the token `token` whose characters have the tags `here`: no finding when all
of the token is code. -/
private def tokenFound (here : List (Nat × Place)) (token : String) : Option Found :=
  match standing (here.map (·.2)) with
  | some stands => some ⟨.mention token stands, (here.head?.map (·.1)).getD 0⟩
  | none => none

private theorem tokenFound_of_standing {here : List (Nat × Place)} {stands : Standing}
    (token : String) (stood : standing (here.map (·.2)) = some stands) :
    ∃ anchor, tokenFound here token = some ⟨.mention token stands, anchor⟩ := by
  unfold tokenFound
  rw [stood]
  exact ⟨_, rfl⟩

private theorem standing_of_tokenFound {here : List (Nat × Place)} {token : String} {f : Found}
    (made : tokenFound here token = some f) :
    ∃ stands, standing (here.map (·.2)) = some stands ∧ f.finding = .mention token stands := by
  unfold tokenFound at made
  cases stood : standing (here.map (·.2)) with
  | none =>
    rw [stood] at made
    cases made
  | some stands =>
    rw [stood] at made
    cases made
    exact ⟨stands, rfl, rfl⟩

private theorem runTokens_fold (tags : List (Nat × Place)) (parts : List (String ⊕ String)) :
    ∀ (start : Nat) (found : List Found),
      (parts.foldl (fun (acc : List (Nat × Place) × List Found) piece =>
          match piece with
          | .inl between => (acc.1.drop between.length, acc.2)
          | .inr token =>
            let here := acc.1.take token.length
            (acc.1.drop token.length,
              match standing (here.map (·.2)) with
              | some stands => ⟨.mention token stands, (here.head?.map (·.1)).getD 0⟩ :: acc.2
              | none => acc.2)) (tags.drop start, found)).2 =
        ((tokenOffsets start parts).filterMap fun p =>
          tokenFound ((tags.drop p.1).take p.2.length) p.2).reverse ++ found := by
  induction parts with
  | nil =>
    intro start found
    simp [tokenOffsets]
  | cons part parts ih =>
    intro start found
    cases part with
    | inl between =>
      rw [List.foldl_cons]
      simp only [List.drop_drop]
      rw [ih]
      simp [tokenOffsets]
    | inr token =>
      rw [List.foldl_cons]
      simp only [List.drop_drop]
      rw [ih]
      simp only [tokenOffsets, List.filterMap_cons, tokenFound]
      generalize standing (((tags.drop start).take token.length).map (·.2)) = stood
      cases stood <;> simp

/-- The mentions of a run are the findings of the tokens that `splitTokens` returns for its
text, each with the tags at its place. -/
private theorem runTokens_eq (parts : List Part) :
    runTokens parts =
      (tokenOffsets 0 (splitTokens none 0 [] (String.join (parts.map (·.text))).toList)).filterMap
        fun p => tokenFound (((parts.flatMap fun part =>
          List.replicate part.text.length (part.anchor, part.place)).drop p.1).take p.2.length)
            p.2 := by
  have fold := runTokens_fold
    (parts.flatMap fun part => List.replicate part.text.length (part.anchor, part.place))
    (splitTokens none 0 [] (String.join (parts.map (·.text))).toList) 0 []
  simp only [List.drop_zero, List.append_nil] at fold
  unfold runTokens
  simp only []
  rw [fold, List.reverse_reverse]

/-- A token that `splitTokens` returns for the text of a run, with a finding for the tags at its
place, gives that finding. -/
private theorem mem_runTokens_of {parts : List Part} {o : Nat} {token : String} {f : Found}
    (offset : (o, token) ∈
      tokenOffsets 0 (splitTokens none 0 [] (String.join (parts.map (·.text))).toList))
    (made : tokenFound (((parts.flatMap fun part =>
      List.replicate part.text.length (part.anchor, part.place)).drop o).take token.length)
        token = some f) : f ∈ runTokens parts := by
  rw [runTokens_eq, List.mem_filterMap]
  exact ⟨(o, token), offset, made⟩

/-- The places of the characters of one piece of a run, read from the tags of the run. -/
private theorem places_of_split {parts : List Part} {before chars after : List (Place × Char)}
    (split : partChars parts = before ++ chars ++ after) :
    (((parts.flatMap fun part => List.replicate part.text.length (part.anchor, part.place)).drop
      (before.map (·.2)).length).take (String.ofList (chars.map (·.2))).length).map (·.2) =
      chars.map (·.1) := by
  rw [List.map_take, List.map_drop, ← partChars_places, split, String.length_ofList,
    List.map_append, List.map_append, List.length_map, List.length_map,
    ← List.length_map (f := (·.1)) (as := before), ← List.length_map (f := (·.1)) (as := chars),
    List.append_assoc, List.drop_left, List.take_left]

/-- Each finding of a run is the mention of a rule-ID token of its text, with the standing of
the places of that token. -/
private theorem of_mem_runTokens {parts : List Part} {f : Found} (found : f ∈ runTokens parts) :
    ∃ before chars after stands, partChars parts = before ++ chars ++ after ∧
      TokenAt (before.map (·.2)).getLast? (chars.map (·.2)) (after.map (·.2)) ∧
      standing (chars.map (·.1)) = some stands ∧
      f.finding = .mention (String.ofList (chars.map (·.2))) stands := by
  rw [runTokens_eq, List.mem_filterMap] at found
  obtain ⟨⟨o, token⟩, offset, made⟩ := found
  obtain ⟨before, chars, after, split, rfl, at', rfl⟩ := (mem_tokenOffsets_iff _ _ _).mp offset
  rw [← partChars_text] at split
  obtain ⟨front, after', whole, front', rfl⟩ := List.map_eq_append_iff.mp split
  obtain ⟨before', chars', rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp front'
  obtain ⟨stands, stood, finding⟩ := standing_of_tokenFound made
  rw [places_of_split whole] at stood
  exact ⟨before', chars', after', stands, whole, at', stood, finding⟩

/-- Each rule-ID token of the text of a run that has a standing is a finding of the run. -/
private theorem runTokens_of_token {parts : List Part} {before chars after : List (Place × Char)}
    {stands : Standing} (split : partChars parts = before ++ chars ++ after)
    (token : TokenAt (before.map (·.2)).getLast? (chars.map (·.2)) (after.map (·.2)))
    (stood : standing (chars.map (·.1)) = some stands) :
    ∃ f ∈ runTokens parts, f.finding = .mention (String.ofList (chars.map (·.2))) stands := by
  have text : (String.join (parts.map (·.text))).toList =
      before.map (·.2) ++ chars.map (·.2) ++ after.map (·.2) := by
    rw [← partChars_text, split, List.map_append, List.map_append]
  have offset := (mem_tokenOffsets_iff _ (before.map (·.2)).length
    (String.ofList (chars.map (·.2)))).mpr
    ⟨before.map (·.2), chars.map (·.2), after.map (·.2), text, rfl, token, rfl⟩
  obtain ⟨anchor, made⟩ := tokenFound_of_standing (String.ofList (chars.map (·.2)))
    (here := ((parts.flatMap fun part =>
      List.replicate part.text.length (part.anchor, part.place)).drop
        (before.map (·.2)).length).take (String.ofList (chars.map (·.2))).length)
    (stands := stands) (by rw [places_of_split split]; exact stood)
  exact ⟨⟨.mention (String.ofList (chars.map (·.2))) stands, anchor⟩,
    mem_runTokens_of offset made, rfl⟩

/-- The findings of a run are accepted exactly when the rule IDs of its characters are linked. -/
private theorem runTokens_accepted_iff {target : RuleId → String → Bool}
    {page : RuleId → String → Prop}
    (decides : ∀ id destination, target id destination = true ↔ page id destination)
    (parts : List Part) :
    (∀ f ∈ runTokens parts, f.Accepted target) ↔ RunLinked page (partChars parts) := by
  constructor
  · intro accepted before chars after split token
    cases stood : standing (chars.map (·.1)) with
    | none =>
      exact .inl fun c member =>
        (standing_eq_none_iff _).mp stood c.1 (List.mem_map_of_mem member)
    | some stands =>
      obtain ⟨f, found, finding⟩ := runTokens_of_token split token stood
      obtain ⟨token', destination, finding', id, destination', spelled, link, pages⟩ :=
        accepted f found
      rw [finding] at finding'
      cases finding'
      cases link
      obtain ⟨-, index, all⟩ := (standing_eq_linked_iff _ _).mp stood
      exact .inr ⟨index, destination, id, fun c member => all c.1 (List.mem_map_of_mem member),
        spelled, (decides id destination).mp pages⟩
  · intro linked f found
    obtain ⟨before, chars, after, stands, split, token, stood, finding⟩ := of_mem_runTokens found
    rcases linked before chars after split token with
      code | ⟨index, destination, id, all, spelled, pages⟩
    · have none : standing (chars.map (·.1)) = none :=
        (standing_eq_none_iff _).mpr (by simpa using code)
      rw [none] at stood
      cases stood
    · have some : standing (chars.map (·.1)) = some (.linked destination) :=
        (standing_eq_linked_iff _ _).mpr ⟨by
          obtain ⟨a, b, c, d, six, -⟩ := token
          intro empty
          rw [List.map_eq_nil_iff] at empty
          simp [empty] at six, index, by simpa using all⟩
      rw [some] at stood
      cases stood
      exact ⟨_, destination, finding, id, destination, spelled, rfl,
        (decides id destination).mpr pages⟩

private theorem Scan.past_links (s : Scan) (slice : String) : (s.past slice).links = s.links := by
  unfold Scan.past
  split <;> rfl

private theorem Scan.past_entered (s : Scan) (slice : String) :
    (s.past slice).entered = s.entered := by
  unfold Scan.past
  split <;> rfl

private theorem Scan.past_run (s : Scan) (slice : String) : (s.past slice).run = s.run := by
  unfold Scan.past
  split <;> rfl

private theorem Scan.past_found (s : Scan) (slice : String) : (s.past slice).found = s.found := by
  unfold Scan.past
  split <;> rfl

private theorem Scan.place_eq (s : Scan) :
    s.place = (s.entered.map fun link => Place.link link.1 link.2).headD .prose := by
  unfold Scan.place
  cases s.entered with
  | nil => rfl
  | cons link rest =>
    cases link
    rfl

/-- The scan of the pieces from the state `s` gives accepted findings exactly when the findings
of `s` are accepted, no piece is a refused construct, and the rule IDs of each run that `placed`
gives from the links and the run of `s` are linked. -/
private theorem scan_accepted_iff {target : RuleId → String → Bool}
    {page : RuleId → String → Prop}
    (decides : ∀ id destination, target id destination = true ↔ page id destination)
    (pieces : List Piece) :
    ∀ s : Scan, (∀ f ∈ (pieces.foldl Scan.step s).flush.found, f.Accepted target) ↔
      (∀ f ∈ s.found, f.Accepted target) ∧ (∀ reason, Piece.refused reason ∉ pieces) ∧
        ∀ run ∈ placed s.links (s.entered.map fun link => Place.link link.1 link.2)
          (partChars s.run.reverse) pieces, RunLinked page run := by
  induction pieces with
  | nil =>
    intro s
    simp only [List.foldl_nil, Scan.flush, List.mem_append, List.mem_reverse, placed,
      List.mem_singleton, forall_eq, List.not_mem_nil, not_false_eq_true, implies_true, true_and,
      ← runTokens_accepted_iff decides]
    exact ⟨fun h => ⟨fun f hf => h f (.inr hf), fun f hf => h f (.inl hf)⟩,
      fun h f hf => hf.elim (h.2 f) (h.1 f)⟩
  | cons piece rest ih =>
    intro s
    rw [List.foldl_cons, ih]
    cases piece with
    | text slice rendered =>
      simp only [Scan.step, Scan.past_links, Scan.past_entered, Scan.past_run, Scan.past_found,
        placed, List.reverse_cons, partChars,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Scan.place_eq,
        List.mem_cons, reduceCtorEq, false_or]
    | code slice =>
      simp only [Scan.step, Scan.past_links, Scan.past_entered, Scan.past_run, Scan.past_found,
        placed, List.reverse_cons, partChars,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, reduceCtorEq, false_or]
    | enter destination =>
      simp only [Scan.step, placed, List.map_cons, List.mem_cons, reduceCtorEq, false_or]
    | leave =>
      simp only [Scan.step, placed, List.map_tail, List.mem_cons, reduceCtorEq, false_or]
    | refused reason =>
      simp only [Scan.step, placed, List.mem_cons, forall_eq_or_imp, Piece.refused.injEq]
      constructor
      · rintro ⟨⟨refused, -⟩, -⟩
        obtain ⟨token, destination, finding, -⟩ := refused
        cases finding
      · rintro ⟨-, ⟨impossible, -⟩, -⟩
        exact impossible.elim
    | gap | line | start _ =>
      simp only [Scan.step, Scan.flush, placed, List.mem_append, List.mem_reverse, List.mem_cons,
        forall_eq_or_imp, reduceCtorEq, false_or, List.reverse_nil,
        ← runTokens_accepted_iff decides]
      constructor
      · rintro ⟨accepted, none, runs⟩
        exact ⟨fun f hf => accepted f (.inr hf), none, fun f hf => accepted f (.inl hf), runs⟩
      · rintro ⟨accepted, none, run, runs⟩
        exact ⟨fun f hf => hf.elim (run f) (accepted f), none, runs⟩

theorem Closed.append {first second : List Piece} (closed : Closed first)
    (closed' : Closed second) : Closed (first ++ second) := by
  induction closed with
  | nil => exact closed'
  | other notEnter notLeave _ ih => exact .other notEnter notLeave ih
  | @link destination inner rest closedInner _ _ ihRest =>
    have whole := Closed.link (destination := destination) closedInner ihRest
    simpa [List.append_assoc] using whole

/-- The link state of the scan after one more piece: the number of links entered, and the
places of the links entered and not yet left. -/
private def linkStep (state : Nat × List Place) : Piece → Nat × List Place
  | .enter destination => (state.1 + 1, .link state.1 destination :: state.2)
  | .leave => (state.1, state.2.tail)
  | .text _ _ | .code _ | .refused _ | .gap | .line | .start _ => state

private theorem linkStep_other {piece : Piece}
    (notEnter : ∀ destination, piece ≠ .enter destination)
    (notLeave : piece ≠ .leave) (state : Nat × List Place) : linkStep state piece = state := by
  cases piece <;> first | rfl | exact absurd rfl (notEnter _) | exact absurd rfl notLeave

private theorem linksIn_other {piece : Piece} (notEnter : ∀ destination, piece ≠ .enter destination)
    (rest : List Piece) : linksIn (piece :: rest) = linksIn rest := by
  cases piece <;> first | rfl | exact absurd rfl (notEnter _)

private theorem foldl_closed {inner : List Piece} (closed : Closed inner) :
    ∀ state : Nat × List Place,
      inner.foldl linkStep state = (state.1 + linksIn inner, state.2) := by
  induction closed with
  | nil =>
    intro state
    rfl
  | @other piece rest notEnter notLeave _ ih =>
    intro state
    rw [List.foldl_cons, linkStep_other notEnter notLeave, ih, linksIn_other notEnter]
  | @link destination inner rest _ _ ihInner ihRest =>
    intro state
    simp only [List.foldl_cons, List.foldl_append, linkStep, ihInner, ihRest, List.tail_cons,
      Prod.mk.injEq, and_true]
    simp only [linksIn, List.countP_cons, List.countP_append]
    simp
    omega

private theorem foldl_links (pieces : List Piece) :
    ∀ state : Nat × List Place, (pieces.foldl linkStep state).1 = state.1 + linksIn pieces := by
  induction pieces with
  | nil =>
    intro state
    rfl
  | cons piece rest ih =>
    intro state
    rw [List.foldl_cons, ih]
    cases piece <;> simp [linkStep, linksIn] <;> omega

private theorem foldl_all_links (pieces : List Piece) :
    ∀ state : Nat × List Place,
      (∀ place ∈ state.2, ∃ index destination, place = .link index destination) →
        ∀ place ∈ (pieces.foldl linkStep state).2,
          ∃ index destination, place = .link index destination := by
  induction pieces with
  | nil =>
    intro state links
    exact links
  | cons piece rest ih =>
    intro state links
    rw [List.foldl_cons]
    apply ih
    cases piece with
    | enter destination =>
      intro place member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, _, rfl⟩
      · exact links place member
    | leave => exact fun place member => links place (List.mem_of_mem_tail member)
    | _ => exact links

/-- A link whose text and the pieces after its start are closed is the link entered last and
not yet left. -/
private theorem foldl_open {before inner : List Piece} (destination : String)
    (closed : Closed inner) :
    ((before ++ .enter destination :: inner).foldl linkStep (0, [])).2 =
      .link (linksIn before) destination :: (before.foldl linkStep (0, [])).2 := by
  rw [List.foldl_append, List.foldl_cons, foldl_closed closed]
  simp [linkStep, foldl_links]

/-- The link entered last and not yet left has closed pieces after its start. -/
private theorem open_of_foldl : ∀ (n : Nat) (front : List Piece), front.length = n →
    ∀ (index : Nat) (destination : String) (rest : List Place),
      (front.foldl linkStep (0, [])).2 = .link index destination :: rest →
        ∃ before inner, front = before ++ .enter destination :: inner ∧ Closed inner ∧
          index = linksIn before ∧ (before.foldl linkStep (0, [])).2 = rest := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro front length index destination rest top
    rcases List.eq_nil_or_concat front with rfl | ⟨init, last, rfl⟩
    · simp at top
    · rw [List.concat_eq_append] at length top ⊢
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at top
      have shorter : init.length < n := by
        rw [← length, List.length_append]
        simp
      cases last with
      | enter destination' =>
        simp only [linkStep, List.cons.injEq, Place.link.injEq] at top
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := top
        exact ⟨init, [], rfl, .nil, by simp [foldl_links], rfl⟩
      | leave =>
        simp only [linkStep] at top
        cases stack : (init.foldl linkStep (0, [])).2 with
        | nil =>
          rw [stack] at top
          cases top
        | cons top₀ below =>
          rw [stack, List.tail_cons] at top
          subst top
          obtain ⟨index₀, destination₀, rfl⟩ := foldl_all_links init (0, [])
            (fun _ member => nomatch member) top₀ (by rw [stack]; exact List.mem_cons_self)
          obtain ⟨before₀, inner₀, rfl, closed₀, -, below₀⟩ :=
            ih init.length shorter init rfl index₀ destination₀ _ stack
          obtain ⟨before₁, inner₁, rfl, closed₁, rfl, rest₁⟩ :=
            ih before₀.length (by simp at shorter; omega) before₀ rfl index destination rest below₀
          exact ⟨before₁, inner₁ ++ .enter destination₀ :: (inner₀ ++ [.leave]),
            by simp [List.append_assoc], closed₁.append (.link closed₀ .nil), rfl, rest₁⟩
      | text slice rendered =>
        obtain ⟨before, inner, rfl, closed, rfl, rest'⟩ :=
          ih init.length shorter init rfl index destination rest top
        exact ⟨before, inner ++ [.text slice rendered], by simp [List.append_assoc],
          closed.append (.other (fun _ => nofun) nofun .nil), rfl, rest'⟩
      | code slice =>
        obtain ⟨before, inner, rfl, closed, rfl, rest'⟩ :=
          ih init.length shorter init rfl index destination rest top
        exact ⟨before, inner ++ [.code slice], by simp [List.append_assoc],
          closed.append (.other (fun _ => nofun) nofun .nil), rfl, rest'⟩
      | refused reason =>
        obtain ⟨before, inner, rfl, closed, rfl, rest'⟩ :=
          ih init.length shorter init rfl index destination rest top
        exact ⟨before, inner ++ [.refused reason], by simp [List.append_assoc],
          closed.append (.other (fun _ => nofun) nofun .nil), rfl, rest'⟩
      | gap =>
        obtain ⟨before, inner, rfl, closed, rfl, rest'⟩ :=
          ih init.length shorter init rfl index destination rest top
        exact ⟨before, inner ++ [.gap], by simp [List.append_assoc],
          closed.append (.other (fun _ => nofun) nofun .nil), rfl, rest'⟩
      | line =>
        obtain ⟨before, inner, rfl, closed, rfl, rest'⟩ :=
          ih init.length shorter init rfl index destination rest top
        exact ⟨before, inner ++ [.line], by simp [List.append_assoc],
          closed.append (.other (fun _ => nofun) nofun .nil), rfl, rest'⟩
      | start kind =>
        obtain ⟨before, inner, rfl, closed, rfl, rest'⟩ :=
          ih init.length shorter init rfl index destination rest top
        exact ⟨before, inner ++ [.start kind], by simp [List.append_assoc],
          closed.append (.other (fun _ => nofun) nofun .nil), rfl, rest'⟩

/-- The place that `StandsAfter` states is the place of the link state of the scan. -/
private theorem standsAfter_iff (front : List Piece) (place : Place) :
    StandsAfter front place ↔ place = (front.foldl linkStep (0, [])).2.headD .prose := by
  constructor
  · rintro (⟨before, destination, inner, rfl, closed, rfl⟩ | ⟨none, rfl⟩)
    · rw [foldl_open destination closed]
      rfl
    · cases stack : (front.foldl linkStep (0, [])).2 with
      | nil => rfl
      | cons top below =>
        obtain ⟨index, destination, rfl⟩ := foldl_all_links front (0, [])
          (fun _ member => nomatch member) top (by rw [stack]; exact List.mem_cons_self)
        obtain ⟨before, inner, rfl, closed, -, -⟩ :=
          open_of_foldl _ front rfl index destination below stack
        exact absurd closed (none before destination inner rfl)
  · rintro rfl
    cases stack : (front.foldl linkStep (0, [])).2 with
    | nil =>
      refine .inr ⟨fun before destination inner split closed => ?_, rfl⟩
      rw [split, foldl_open destination closed] at stack
      cases stack
    | cons top below =>
      obtain ⟨index, destination, rfl⟩ := foldl_all_links front (0, [])
        (fun _ member => nomatch member) top (by rw [stack]; exact List.mem_cons_self)
      obtain ⟨before, inner, rfl, closed, rfl, -⟩ :=
        open_of_foldl _ front rfl index destination below stack
      exact .inl ⟨before, destination, inner, rfl, closed, rfl⟩

/-- The text of the pieces `run` from the link state `state`. -/
private def textFrom (state : Nat × List Place) : List Piece → List (Place × Char)
  | [] => []
  | piece :: rest => piece.chars (state.2.headD .prose) ++ textFrom (linkStep state piece) rest

/-- The text of a run is one text only: the one that the link state of the scan gives. -/
private theorem runText_iff (run : List Piece) :
    ∀ (front : List Piece) (text : List (Place × Char)),
    RunText front run text ↔ text = textFrom (front.foldl linkStep (0, [])) run := by
  induction run with
  | nil =>
    intro front text
    constructor
    · intro read
      cases read
      rfl
    · rintro rfl
      exact .nil
  | cons piece rest ih =>
    intro front text
    constructor
    · intro read
      cases read with
      | cons stands tail =>
        rw [(standsAfter_iff _ _).mp stands, (ih _ _).mp tail, List.foldl_append]
        rfl
    · rintro rfl
      have tail := (ih (front ++ [piece]) _).mpr rfl
      rw [List.foldl_append] at tail
      exact .cons ((standsAfter_iff front _).mpr rfl) tail

/-- The scan of pieces that end no run adds their text to the run in progress. -/
private theorem placed_segment {r₁ : List Piece} (free : ∀ piece ∈ r₁, ¬ piece.EndsRun) :
    ∀ (state : Nat × List Place) (acc : List (Place × Char)) (tail : List Piece),
      placed state.1 state.2 acc (r₁ ++ tail) =
        placed (r₁.foldl linkStep state).1 (r₁.foldl linkStep state).2
          (acc ++ textFrom state r₁) tail := by
  induction r₁ with
  | nil =>
    intro state acc tail
    simp [textFrom]
  | cons piece rest ih =>
    intro state acc tail
    have later := ih (fun other member => free other (List.mem_cons_of_mem _ member))
    have first := free piece List.mem_cons_self
    cases piece with
    | gap => exact absurd (.inl rfl) first
    | line => exact absurd (.inr (.inl rfl)) first
    | start kind => exact absurd (.inr (.inr ⟨kind, rfl⟩)) first
    | text slice rendered =>
      simp only [List.cons_append, placed, List.foldl_cons, linkStep, textFrom, Piece.chars]
      rw [later, List.append_assoc]
    | code slice =>
      simp only [List.cons_append, placed, List.foldl_cons, linkStep, textFrom, Piece.chars]
      rw [later, List.append_assoc]
    | enter destination =>
      simp only [List.cons_append, placed, List.foldl_cons, linkStep, textFrom, Piece.chars,
        List.nil_append]
      exact later (state.1 + 1, .link state.1 destination :: state.2) acc tail
    | leave =>
      simp only [List.cons_append, placed, List.foldl_cons, linkStep, textFrom, Piece.chars,
        List.nil_append]
      exact later (state.1, state.2.tail) acc tail
    | refused reason =>
      simp only [List.cons_append, placed, List.foldl_cons, linkStep, textFrom, Piece.chars,
        List.nil_append]
      exact later state acc tail

/-- The pieces have no piece that ends a run, or they are pieces with no such piece, the first
piece that ends a run, and the pieces after it. -/
private theorem split_first (rest : List Piece) :
    (∀ piece ∈ rest, ¬ piece.EndsRun) ∨
      ∃ r₁ piece rest', rest = r₁ ++ piece :: rest' ∧ (∀ other ∈ r₁, ¬ other.EndsRun) ∧
        piece.EndsRun := by
  induction rest with
  | nil => exact .inl fun _ member => nomatch member
  | cons piece rest ih =>
    by_cases ends : piece.EndsRun
    · exact .inr ⟨[], piece, rest, rfl, fun _ member => (nomatch member), ends⟩
    · rcases ih with free | ⟨r₁, piece', rest', rfl, free, ends'⟩
      · refine .inl fun other member => ?_
        rcases List.mem_cons.mp member with rfl | member
        · exact ends
        · exact free other member
      · refine .inr ⟨piece :: r₁, piece', rest', rfl, fun other member => ?_, ends'⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact ends
        · exact free other member

/-- A run of the document that starts at or after the pieces `start`, where the pieces `r₁`
after `start` end no run and the piece after them, if any, ends a run: the run is `r₁`, or it
starts after that piece. -/
private theorem run_of_split {start r₁ tail before run after : List Piece}
    (free : ∀ piece ∈ r₁, ¬ piece.EndsRun)
    (ends : ∀ piece, tail.head? = some piece → piece.EndsRun)
    (split : start ++ (r₁ ++ tail) = before ++ (run ++ after)) (isRun : IsRun before run after)
    (later : start.length ≤ before.length) :
    (before = start ∧ run = r₁ ∧ after = tail) ∨
      ∃ piece rest, tail = piece :: rest ∧ (start ++ r₁ ++ [piece]).length ≤ before.length := by
  obtain ⟨c, rfl, inner⟩ : ∃ c, before = start ++ c ∧ r₁ ++ tail = c ++ (run ++ after) := by
    rcases List.append_eq_append_iff.mp split with ⟨c, rfl, inner⟩ | ⟨c, rfl, inner⟩
    · exact ⟨c, rfl, inner⟩
    · have empty : c = [] := by
        rw [List.length_append] at later
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      exact ⟨[], by simp, by simpa using inner.symm⟩
  rcases List.eq_nil_or_concat c with rfl | ⟨init, last, rfl⟩
  · left
    simp only [List.nil_append, List.append_nil] at inner isRun ⊢
    rcases List.append_eq_append_iff.mp inner with ⟨g, rfl, tailEq⟩ | ⟨g, rfl, afterEq⟩
    · cases g with
      | nil => exact ⟨trivial, by simp, by simpa using tailEq.symm⟩
      | cons piece g =>
        exact absurd (ends piece (by rw [tailEq]; rfl)) (isRun.1 piece (by simp))
    · cases g with
      | nil => exact ⟨trivial, by simp, by simpa using afterEq⟩
      | cons piece g =>
        exact absurd (isRun.2.2 piece (by rw [afterEq]; rfl)) (free piece (by simp))
  · rw [List.concat_eq_append] at inner isRun later ⊢
    have boundary : last.EndsRun :=
      isRun.2.1 last (by rw [← List.append_assoc, List.getLast?_concat])
    rcases List.append_eq_append_iff.mp inner with ⟨e, whole, tailEq⟩ | ⟨e, whole, -⟩
    · cases e with
      | nil =>
        rw [List.append_nil] at whole
        exact absurd boundary (free last (by rw [← whole]; simp))
      | cons piece e =>
        refine .inr ⟨piece, e ++ (run ++ after), by simpa using tailEq, ?_⟩
        rw [whole]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    · exact absurd boundary (free last (by rw [whole]; simp))

/-- A statement holds for each run that the scan gives exactly when it holds for the text of
each run of the document. `start` is the pieces already read, which end with a piece that ends
a run, and the runs are those that start at or after `start`. -/
private theorem forall_placed_iff (P : List (Place × Char) → Prop) :
    ∀ (n : Nat) (rest : List Piece), rest.length = n → ∀ start : List Piece,
      (∀ piece, start.getLast? = some piece → piece.EndsRun) →
        ((∀ text ∈ placed (start.foldl linkStep (0, [])).1 (start.foldl linkStep (0, [])).2 []
            rest, P text) ↔
          ∀ before run after, start ++ rest = before ++ (run ++ after) → IsRun before run after →
            start.length ≤ before.length → P (textFrom (before.foldl linkStep (0, [])) run)) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro rest length start startEnds
    rcases split_first rest with free | ⟨r₁, piece, rest', rfl, free, ends⟩
    · have segment := placed_segment free (start.foldl linkStep (0, [])) [] []
      simp only [List.append_nil, List.nil_append, placed] at segment
      rw [segment]
      simp only [List.mem_singleton, forall_eq]
      constructor
      · intro holds before run after split isRun later
        rcases run_of_split (tail := []) free (fun _ head => nomatch head)
          (by simpa using split) isRun later with ⟨rfl, rfl, rfl⟩ | ⟨piece, rest', impossible, -⟩
        · exact holds
        · cases impossible
      · intro all
        exact all start rest [] (by simp) ⟨free, startEnds, fun _ head => nomatch head⟩
          (Nat.le_refl _)
    · have pieceEnds : ∀ other, (piece :: rest').head? = some other → other.EndsRun := by
        intro other head
        cases head
        exact ends
      have segment := placed_segment free (start.foldl linkStep (0, [])) [] (piece :: rest')
      have state : r₁.foldl linkStep (start.foldl linkStep (0, [])) =
          (start ++ r₁ ++ [piece]).foldl linkStep (0, []) := by
        rw [List.foldl_append, List.foldl_append]
        rcases ends with rfl | rfl | ⟨kind, rfl⟩ <;> rfl
      rw [state, List.nil_append] at segment
      have boundary : ∀ (state : Nat × List Place) (acc : List (Place × Char)),
          placed state.1 state.2 acc (piece :: rest') = acc :: placed state.1 state.2 [] rest' := by
        intro state acc
        rcases ends with rfl | rfl | ⟨kind, rfl⟩ <;> rfl
      rw [segment, boundary]
      have next := ih rest'.length
        (by rw [← length]; simp only [List.length_append, List.length_cons]; omega) rest' rfl
        (start ++ r₁ ++ [piece])
        (by
          intro other last
          rw [List.getLast?_concat] at last
          cases last
          exact ends)
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [next]
      constructor
      · rintro ⟨first, others⟩ before run after split isRun later
        rcases run_of_split free pieceEnds split isRun later with
          ⟨rfl, rfl, rfl⟩ | ⟨piece', rest'', tailEq, far⟩
        · exact first
        · cases tailEq
          exact others before run after (by simpa [List.append_assoc] using split) isRun far
      · intro all
        refine ⟨all start r₁ (piece :: rest') rfl ⟨free, startEnds, pieceEnds⟩ (Nat.le_refl _),
          fun before run after split isRun later => ?_⟩
        refine all before run after (by simpa [List.append_assoc] using split) isRun ?_
        simp only [List.length_append] at later
        omega

/-- The findings of a document are accepted exactly when the document is. `findings` reads the
runs that `IsRun` states and the rule-ID tokens that `Regula.Prose.TokenAt` states, and gives
each token the standing of the places that `RunText` states. `decides` gives the page predicate
its meaning. -/
theorem findings_accepted_iff {target : RuleId → String → Bool} {page : RuleId → String → Prop}
    (decides : ∀ id destination, target id destination = true ↔ page id destination)
    (pieces : List Piece) :
    (∀ f ∈ findings pieces, f.Accepted target) ↔ PiecesAccepted page pieces := by
  have scan := scan_accepted_iff decides pieces {}
  simp only [List.not_mem_nil, false_imp_iff, implies_true, true_and, List.map_nil,
    List.reverse_nil] at scan
  have runs := forall_placed_iff (RunLinked page) pieces.length pieces rfl []
    (fun _ last => nomatch last)
  simp only [List.foldl_nil, List.nil_append, List.length_nil, Nat.zero_le, true_imp_iff] at runs
  unfold findings PiecesAccepted
  simp only [List.mem_reverse]
  refine scan.trans (and_congr_right fun _ => runs.trans ?_)
  constructor
  · intro all before run after text split isRun read
    rw [(runText_iff run before text).mp read]
    exact all before run after (by rw [split, List.append_assoc]) isRun
  · intro all before run after split isRun
    exact all before run after _ (by rw [split, List.append_assoc]) isRun
      ((runText_iff run before _).mpr rfl)

/-- A document with no piece is accepted. -/
theorem piecesAccepted_nil (page : RuleId → String → Prop) : PiecesAccepted page [] := by
  refine ⟨fun reason => List.not_mem_nil, fun before run after text split _ read => ?_⟩
  simp only [List.nil_eq, List.append_eq_nil_iff] at split
  obtain ⟨⟨-, rfl⟩, -⟩ := split
  cases read
  rintro before chars after split ⟨a, b, c, d, six, -⟩
  simp only [List.nil_eq, List.append_eq_nil_iff] at split
  rw [split.1.2] at six
  simp at six

/-! ## The pages of a rule and the audit marker -/

/-- The tracked documents whose links to the site name no edition, so that each link opens the
latest release and a release changes no such document: the root `README.md`. Only in these
documents is the stable address of a rule a link to its page (`target`), and the site build
requires each address of the site in each of them in its artifact (`Regula.Site.siteAnchors`). -/
def stableDocuments : List String := ["README.md"]

/-- Whether rule `id` is in a release: its lifecycle records the release that introduced it. -/
def released (id : RuleId) : Bool := (descriptor id).lifecycle.introduced != .unreleased

/-- A rule is in a release exactly when a listed release introduced it. Each release's edition
has a page for every rule of its build, and a rule is never removed, so the edition of every
later release has the page too; that step is argued, and the site build observes it for the
addresses of each document of `stableDocuments` (`Regula.Site.siteAnchors`), the only documents
in which `target` accepts a stable address. -/
theorem released_iff (id : RuleId) :
    released id = true ↔ ∃ v ∈ versions, (descriptor id).lifecycle.introduced = .release v := by
  have listed := lifecycle_listed id (descriptor id).lifecycle.introduced
    (by cases (descriptor id).lifecycle <;> simp [Lifecycle.introduced, Lifecycle.builds])
  unfold released
  cases h : (descriptor id).lifecycle.introduced with
  | unreleased => simp
  | release v =>
    rw [h] at listed
    simpa [Build.listedIn] using listed

/-- Whether `destination` is a page of rule `id` that the tracked Markdown document `file`
links: the rule's page in the development edition (`Edition.url`), with or without a fragment,
or, only in a document of `stableDocuments` and for a rule that is in a release (`released`), its
stable address (`stableUrl`) with no fragment, which opens the page of the latest release. A
stable route does not keep a fragment. -/
def target (file : String) (id : RuleId) (destination : String) : Bool :=
  destination == Edition.dev.url id.route ||
    destination.startsWith (Edition.dev.url id.route ++ "#") ||
    (stableDocuments.contains file && released id && destination == stableUrl id.route)

/-- `destination` is a page of rule `id` that the document `file` links, as equations over the
text. It is the address of the rule's page in the development edition, or that address, `#` and
then a fragment. Or `file` is one of `stableDocuments`, a listed release introduced the rule, and
it is the rule's stable address. The statement has no test of `target`, which decides it
(`target_iff`), and no test of `released`. -/
def Target (file : String) (id : RuleId) (destination : String) : Prop :=
  destination = Edition.dev.url id.route ∨
    (∃ fragment, destination = Edition.dev.url id.route ++ "#" ++ fragment) ∨
    (file ∈ stableDocuments ∧
      (∃ v ∈ versions, (descriptor id).lifecycle.introduced = .release v) ∧
      destination = stableUrl id.route)

/-- A text starts with `marker` exactly when it is `marker` and then a rest. -/
private theorem startsWith_iff_append (text marker : String) :
    text.startsWith marker = true ↔ ∃ rest, text = marker ++ rest := by
  rw [String.startsWith_string_iff]
  constructor
  · rintro ⟨rest, split⟩
    exact ⟨String.ofList rest, by rw [← String.toList_inj]; simp [← split]⟩
  · rintro ⟨rest, rfl⟩
    exact ⟨rest.toList, by simp⟩

/-- The executed test accepts, for a document, exactly the destinations that are a page of the
rule for that document. -/
theorem target_iff (file : String) (id : RuleId) (destination : String) :
    target file id destination = true ↔ Target file id destination := by
  simp only [target, Target, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    List.contains_iff_mem, startsWith_iff_append, released_iff, or_assoc, and_assoc]

/-- Whether `text`, the text of a raw HTML block, is exactly one fence marker of the
documentation audit, the two forms the standard defines (§7, `Regula.Checker.Documentation`):
`<!-- lean-trusted-compiler -->`, or `<!-- lean-fail: PATTERN -->` on one line with no `>` in
`PATTERN`. Such a block is one HTML comment and nothing else, since a comment ends only at a
`>`, so it renders as nothing. It is the only raw HTML the check reads. -/
def auditMarker (text : String) : Bool :=
  let value := text.trimAscii.toString
  let chars := value.toList
  !chars.contains '\n' &&
    (value == "<!-- lean-trusted-compiler -->" ||
      (value.startsWith "<!-- lean-fail:" && value.endsWith "-->" &&
        !(chars.take (chars.length - 3)).contains '>'))

/-! ## Source lines -/

/-- The source text of one located piece. -/
structure Anchor where
  /-- Whether a line boundary lies between this piece and the located piece before it. -/
  later : Bool
  /-- The text, as it stands on one source line. -/
  slice : String
  deriving DecidableEq, Repr

/-- The located pieces of a document, in order; `later` is whether a line boundary has been
read since the last one. -/
def anchors : Bool → List Piece → List Anchor
  | _, [] => []
  | _, .line :: rest => anchors true rest
  | later, piece :: rest =>
    match piece.located? with
    | some slice => ⟨later, slice⟩ :: anchors false rest
    | none => anchors later rest

/-- Whether the first of `anchors` lies on a later line than the anchor before it. -/
def headLater : List Anchor → Bool
  | anchor :: _ => anchor.later
  | [] => false

/-- `Placed fit n anchors lines places`: `places` gives each anchor a line that its text fits,
with `lines` numbered from `n`, in order: an anchor lies on the line of the anchor before it or
on a later one, and on a later one when a line boundary lies between them. -/
inductive Placed {α : Type} (fit : String → α → Bool) :
    Nat → List Anchor → List α → List Nat → Prop where
  /-- No anchor is left to place. -/
  | done {n : Nat} {lines : List α} : Placed fit n [] lines []
  /-- Nothing more is placed on the first line. -/
  | skip {n : Nat} {anchors : List Anchor} {line : α} {lines : List α} {places : List Nat} :
    Placed fit (n + 1) anchors lines places → Placed fit n anchors (line :: lines) places
  /-- The first anchor is placed on the first line, and the next lies on a later line. -/
  | later {n : Nat} {anchor : Anchor} {rest : List Anchor} {line : α} {lines : List α}
      {places : List Nat} :
    fit anchor.slice line = true → headLater rest = true →
    Placed fit (n + 1) rest lines places →
    Placed fit n (anchor :: rest) (line :: lines) (n :: places)
  /-- The first anchor is placed on the first line, and the next may lie on it too. -/
  | same {n : Nat} {anchor : Anchor} {rest : List Anchor} {line : α} {lines : List α}
      {places : List Nat} :
    fit anchor.slice line = true → headLater rest = false →
    Placed fit n rest (line :: lines) places →
    Placed fit n (anchor :: rest) (line :: lines) (n :: places)

/-- `Below found places`: the lists have the same length, and each element of `found` is at most
the element of `places` at its position. -/
inductive Below : List Nat → List Nat → Prop where
  /-- Two empty lists. -/
  | nil : Below [] []
  /-- A smaller or equal head before lists so related. -/
  | cons {a b : Nat} {as bs : List Nat} : a ≤ b → Below as bs → Below (a :: as) (b :: bs)

theorem Placed.places_nil {α : Type} {fit : String → α → Bool} {n : Nat} {lines : List α}
    {places : List Nat} (h : Placed fit n [] lines places) : places = [] := by
  generalize hanchors : ([] : List Anchor) = anchors at h
  induction h with
  | done => rfl
  | skip _ ih => exact ih hanchors
  | later => cases hanchors
  | same => cases hanchors

theorem Placed.le_head {α : Type} {fit : String → α → Bool} {n : Nat} {anchors : List Anchor}
    {lines : List α} {p : Nat} {ps : List Nat} (h : Placed fit n anchors lines (p :: ps)) :
    n ≤ p := by
  generalize hplaces : p :: ps = places at h
  induction h with
  | done => cases hplaces
  | skip _ ih => exact Nat.le_of_succ_le (ih hplaces)
  | later => cases hplaces; exact Nat.le_refl _
  | same => cases hplaces; exact Nat.le_refl _

/-- What a placement says of its first anchor: its line `p` is one of `lines` that its text
fits, the other anchors are placed too, and the next anchor's line is not before `p`, and is
after it when a line boundary lies between them. -/
theorem Placed.head {α : Type} {fit : String → α → Bool} {n : Nat} {anchor : Anchor}
    {rest : List Anchor} {lines : List α} {places : List Nat}
    (h : Placed fit n (anchor :: rest) lines places) :
    ∃ p ps, places = p :: ps ∧ n ≤ p ∧
      (∃ line, lines[p - n]? = some line ∧ fit anchor.slice line = true) ∧
      Placed fit n rest lines ps ∧
      (headLater rest = true → ∀ q qs, ps = q :: qs → p < q) ∧
      (∀ q qs, ps = q :: qs → p ≤ q) := by
  generalize hanchors : anchor :: rest = all at h
  induction h with
  | done => cases hanchors
  | @skip n _ _ _ _ _ ih =>
    obtain ⟨p, ps, hp, hle, ⟨found, hfound, hfit⟩, hrest, hlater, hsame⟩ := ih hanchors
    have hsub : p - n = (p - (n + 1)) + 1 := by omega
    exact ⟨p, ps, hp, Nat.le_of_succ_le hle,
      ⟨found, by rw [hsub, List.getElem?_cons_succ]; exact hfound, hfit⟩, .skip hrest, hlater,
      hsame⟩
  | @later n _ _ line _ places hfit _ h _ =>
    cases hanchors
    exact ⟨n, places, rfl, Nat.le_refl _, ⟨line, by simp, hfit⟩, .skip h,
      fun _ q qs hq => by subst hq; exact h.le_head,
      fun q qs hq => by subst hq; exact Nat.le_of_succ_le h.le_head⟩
  | @same n _ _ line _ places hfit hl h _ =>
    cases hanchors
    exact ⟨n, places, rfl, Nat.le_refl _, ⟨line, by simp, hfit⟩, h,
      (fun hlater => by simp [hl] at hlater),
      fun q qs hq => by subst hq; exact h.le_head⟩

/-- The first placement: each anchor on the first line, numbering `lines` from `n`, that its
text fits and that the anchors before it allow. -/
def leftmost {α : Type} (fit : String → α → Bool) :
    Nat → List Anchor → List α → Option (List Nat)
  | _, [], _ => some []
  | _, _ :: _, [] => none
  | n, anchor :: rest, line :: lines =>
    if fit anchor.slice line then
      if headLater rest then (leftmost fit (n + 1) rest lines).map (n :: ·)
      else (leftmost fit n rest (line :: lines)).map (n :: ·)
    else leftmost fit (n + 1) (anchor :: rest) lines
termination_by _ anchors lines => anchors.length + lines.length

/-- Every placement puts each anchor on the line `leftmost` returns for it or on a later one, and
`leftmost` returns a line for each anchor whenever a placement exists. -/
theorem leftmost_le {α : Type} (fit : String → α → Bool) {lines : List α} :
    ∀ {n : Nat} {anchors : List Anchor} {places : List Nat}, Placed fit n anchors lines places →
      ∃ found, leftmost fit n anchors lines = some found ∧ Below found places := by
  induction lines with
  | nil =>
    intro n anchors places h
    cases h with
    | done => exact ⟨[], by simp [leftmost], .nil⟩
  | cons line lines ihLines =>
    intro n anchors
    induction anchors with
    | nil =>
      intro places h
      rw [h.places_nil]
      exact ⟨[], by simp [leftmost], .nil⟩
    | cons anchor rest ihAnchors =>
      intro places h
      by_cases hfit : fit anchor.slice line = true
      · by_cases hlater : headLater rest = true
        · have hrest : ∃ p ps, places = p :: ps ∧ n ≤ p ∧ Placed fit (n + 1) rest lines ps := by
            cases h with
            | skip h' =>
              obtain ⟨p, ps, hp, hle, _, hrest, _, _⟩ := h'.head
              exact ⟨p, ps, hp, Nat.le_of_succ_le hle, hrest⟩
            | later _ _ h' => exact ⟨n, _, rfl, Nat.le_refl _, h'⟩
            | same _ hl _ => rw [hlater] at hl; cases hl
          obtain ⟨p, ps, rfl, hle, hrest⟩ := hrest
          obtain ⟨found, hfound, hbelow⟩ := ihLines hrest
          exact ⟨n :: found, by simp [leftmost, hfit, hlater, hfound], .cons hle hbelow⟩
        · have hrest :
              ∃ p ps, places = p :: ps ∧ n ≤ p ∧ Placed fit n rest (line :: lines) ps := by
            cases h with
            | skip h' =>
              obtain ⟨p, ps, hp, hle, _, hrest, _, _⟩ := h'.head
              exact ⟨p, ps, hp, Nat.le_of_succ_le hle, .skip hrest⟩
            | later _ hl _ => exact absurd hl hlater
            | same _ _ h' => exact ⟨n, _, rfl, Nat.le_refl _, h'⟩
          obtain ⟨p, ps, rfl, hle, hrest⟩ := hrest
          obtain ⟨found, hfound, hbelow⟩ := ihAnchors hrest
          exact ⟨n :: found, by simp [leftmost, hfit, hlater, hfound], .cons hle hbelow⟩
      · have hskip : Placed fit (n + 1) (anchor :: rest) lines places := by
          cases h with
          | skip h' => exact h'
          | later hf _ _ => exact absurd hf hfit
          | same hf _ _ => exact absurd hf hfit
        obtain ⟨found, hfound, hbelow⟩ := ihLines hskip
        exact ⟨found, by simp [leftmost, hfit, hfound], hbelow⟩

/-- The last of `lines`, numbered from `n`, that is numbered below `limit` and that `slice`
fits. -/
def lastFit {α : Type} (fit : String → α → Bool) (slice : String) (limit : Nat) :
    Nat → List α → Option Nat
  | _, [] => none
  | n, line :: lines =>
    match lastFit fit slice limit (n + 1) lines with
    | some found => some found
    | none => if n < limit ∧ fit slice line = true then some n else none

theorem lastFit_ge {α : Type} {fit : String → α → Bool} {slice : String} {limit : Nat}
    {lines : List α} :
    ∀ {n found : Nat}, lastFit fit slice limit n lines = some found → n ≤ found := by
  induction lines with
  | nil => intro n found h; simp [lastFit] at h
  | cons line lines ih =>
    intro n found h
    cases hrec : lastFit fit slice limit (n + 1) lines with
    | some later =>
      have hlater := ih hrec
      simp only [lastFit, hrec, Option.some.injEq] at h
      omega
    | none =>
      simp only [lastFit, hrec] at h
      split at h
      · exact Nat.le_of_eq (Option.some.inj h)
      · cases h

/-- `lastFit` returns a line whenever one below `limit` fits, and no fitting line below `limit`
comes after the one it returns. -/
theorem le_lastFit {α : Type} (fit : String → α → Bool) (slice : String) (limit : Nat)
    {lines : List α} :
    ∀ {n p : Nat} {line : α}, n ≤ p → p < limit → lines[p - n]? = some line →
      fit slice line = true → ∃ found, lastFit fit slice limit n lines = some found ∧ p ≤ found := by
  induction lines with
  | nil => intro n p line _ _ h; simp at h
  | cons head lines ih =>
    intro n p line hle hlimit hline hfit
    by_cases hp : p = n
    · subst hp
      have hhead : head = line := by simpa using hline
      subst hhead
      cases hrec : lastFit fit slice limit (p + 1) lines with
      | none => exact ⟨p, by simp [lastFit, hrec, hlimit, hfit], Nat.le_refl _⟩
      | some found =>
        exact ⟨found, by simp [lastFit, hrec], Nat.le_of_succ_le (lastFit_ge hrec)⟩
    · have hsub : p - n = (p - (n + 1)) + 1 := by omega
      rw [hsub, List.getElem?_cons_succ] at hline
      obtain ⟨found, hfound, hle'⟩ := ih (by omega) hlimit hline hfit
      exact ⟨found, by simp [lastFit, hfound], hle'⟩

/-- The last placement: each anchor on the last line, numbering `lines` from `n`, that its text
fits and that the anchors after it allow. -/
def rightmost {α : Type} (fit : String → α → Bool) (n : Nat) (lines : List α) :
    List Anchor → Option (List Nat)
  | [] => some []
  | anchor :: rest =>
    match rightmost fit n lines rest with
    | none => none
    | some [] => (lastFit fit anchor.slice (n + lines.length) n lines).map fun here => [here]
    | some (next :: found) =>
      (lastFit fit anchor.slice (if headLater rest then next else next + 1) n lines).map
        fun here => here :: next :: found

/-- Every placement puts each anchor on the line `rightmost` returns for it or on an earlier
one, and `rightmost` returns a line for each anchor whenever a placement exists. -/
theorem le_rightmost {α : Type} (fit : String → α → Bool) {n : Nat} {lines : List α}
    {anchors : List Anchor} :
    ∀ {places : List Nat}, Placed fit n anchors lines places →
      ∃ found, rightmost fit n lines anchors = some found ∧ Below places found := by
  induction anchors with
  | nil => intro places h; rw [h.places_nil]; exact ⟨[], rfl, .nil⟩
  | cons anchor rest ih =>
    intro places h
    obtain ⟨p, ps, rfl, hle, ⟨line, hline, hfit⟩, hrest, hlater, hsame⟩ := h.head
    obtain ⟨found, hfound, hbelow⟩ := ih hrest
    cases hbelow with
    | nil =>
      have hlimit : p < n + lines.length := by
        have := (List.getElem?_eq_some_iff.mp hline).1
        omega
      obtain ⟨here, hhere, hp⟩ := le_lastFit fit anchor.slice _ hle hlimit hline hfit
      exact ⟨[here], by simp [rightmost, hfound, hhere], .cons hp .nil⟩
    | @cons q next qs found hq hbelow =>
      have hlimit : p < (if headLater rest then next else next + 1) := by
        have hweak := hsame q qs rfl
        split
        · next hl =>
          have := hlater hl q qs rfl
          omega
        · omega
      obtain ⟨here, hhere, hp⟩ := le_lastFit fit anchor.slice _ hle hlimit hline hfit
      exact ⟨here :: next :: found, by simp [rightmost, hfound, hhere],
        .cons hp (.cons hq hbelow)⟩

/-! ## The check of one document -/

/-- Whether the source text `slice` occurs on the source line `line`. -/
def occursOn (slice line : String) : Bool := line.contains slice

/-- What a rejected finding reports: the file, the line or the first and last line it can lie
on, and the ID with why it is refused, or why the construct is refused. -/
def Found.describe (file : String) (first last : Nat) (f : Found) : String :=
  s!"{file}:{first}" ++ (if first == last then "" else s!"-{last}") ++ ": " ++
    match f.finding with
    | .refused reason => reason
    | .mention token .split =>
      s!"{token} is only partly inside a link or a code span; write the whole ID as one link \
        to its rule page"
    | .mention token .bare => s!"{token} " ++ (⟨first, token, none⟩ : Mention).reason
    | .mention token (.linked destination) =>
      s!"{token} " ++ (⟨first, token, some destination⟩ : Mention).reason

/-- What the document `file` with text `source` and pieces `pieces` is refused for: each
construct the check refuses to read and each rule ID in its prose that is not a link to a page
of its rule that `target` accepts for `file`, with the line it lies on, or the first and last
line it can lie on (`leftmost`, `rightmost`, `occursOn`; the whole document when the pieces have
no placement). -/
def errors (file source : String) (pieces : List Piece) : List String :=
  match rejected (target file) pieces with
  | [] => []
  | found =>
    let lines := source.splitOn "\n"
    let located := anchors false pieces
    let first := (leftmost occursOn 1 located lines).getD []
    let last := (rightmost occursOn 1 lines located).getD []
    found.map fun f =>
      f.describe file (first[f.anchor]?.getD 1) (last[f.anchor]?.getD lines.length)

theorem errors_nil_iff (file source : String) (pieces : List Piece) :
    errors file source pieces = [] ↔ rejected (target file) pieces = [] := by
  cases h : rejected (target file) pieces <;> simp [errors, h]

/-- What the document `file` with text `source` is refused for, given the parser's reading of
it: that the reading cannot be used, or the `errors` of its pieces. -/
@[regula_decision]
def documentErrors (file source : String) : Reading → List String
  | .unread reason => [s!"{file}: {reason}"]
  | .read pieces => errors file source pieces

/-- The document check reports nothing exactly when the parser's reading can be used and the
document is accepted (`PiecesAccepted`): it has no construct the check refuses to read, and
every rule-ID token of its runs that is not wholly code is a registered rule ID inside one link
to a page of that rule for the file (`Target`): the stable address of a rule only when the file
is one of `stableDocuments`. The statement names the characters of the runs (`RunText`) and the
tokens (`Regula.Prose.TokenAt`), and not the scan `findings`, which `findings_accepted_iff`
connects to them. -/
theorem documentErrors_nil_iff (file source : String) (reading : Reading) :
    documentErrors file source reading = [] ↔
      ∃ pieces, reading = .read pieces ∧ PiecesAccepted (Target file) pieces := by
  cases reading with
  | unread reason => simp [documentErrors]
  | read pieces =>
    simp [documentErrors, errors_nil_iff, rejected_nil_iff, findings_accepted_iff (target_iff file)]

/-- Registered contract of the executed Markdown document check, as a two-way decision over the
file name, the source and the reading (`documentErrors_nil_iff`): it reports nothing for a
document read as no pieces, and an error for a document that was not read. -/
theorem checked_documentErrors : Regula.ExecutableContract documentErrors (fun run =>
    Regula.Decides (· = [])
      (fun input : (String × String) × Reading =>
        ∃ pieces, input.2 = .read pieces ∧ PiecesAccepted (Target input.1.1) pieces)
      (Function.uncurry (Function.uncurry run))) :=
  ⟨.of_iff (fun input => documentErrors_nil_iff input.1.1 input.1.2 input.2)
    ⟨(("", ""), .read []), (documentErrors_nil_iff "" "" (.read [])).mpr
      ⟨[], rfl, piecesAccepted_nil (Target "")⟩⟩
    ⟨(("", ""), .unread ""), fun accepted => by
      simpa using (documentErrors_nil_iff "" "" (.unread "")).mp accepted⟩⟩

/-! ## Links to the site that name no edition -/

/-- The site's address with no scheme and no final `/`. A link destination that has this text is
read as an address of the site, whatever stands before and after it. -/
def siteAddress : String := "rbeauchamp.github.io/regula"

/-- `destination` is an address of the site: `siteAddress` occurs in it. -/
def OnSite (destination : String) : Prop :=
  ∃ before after, destination = before ++ siteAddress ++ after

/-- `destination` is a stable address: the site root, or an address below a `stableRoots`
directory with no fragment, which a stable route does not keep. -/
def Stable (destination : String) : Prop :=
  destination = siteBase ∨
    ∃ r ∈ stableRoots, ∃ rest, destination = stableUrl r ++ rest ∧ '#' ∉ rest.toList

/-- Whether `part` occurs in `text`. -/
def occurs (part : List Char) : List Char → Bool
  | [] => part.isPrefixOf []
  | c :: rest => part.isPrefixOf (c :: rest) || occurs part rest

theorem occurs_iff (part text : List Char) :
    occurs part text = true ↔ ∃ before after, text = before ++ part ++ after := by
  induction text with
  | nil =>
    simp only [occurs, List.isPrefixOf_iff_prefix, List.prefix_nil]
    constructor
    · rintro rfl; exact ⟨[], [], rfl⟩
    · rintro ⟨before, after, h⟩
      simp at h
      exact h.2.1
  | cons c rest ih =>
    simp only [occurs, Bool.or_eq_true, List.isPrefixOf_iff_prefix, ih]
    constructor
    · rintro (⟨after, h⟩ | ⟨before, after, rfl⟩)
      · exact ⟨[], after, by simpa using h.symm⟩
      · exact ⟨c :: before, after, by simp⟩
    · rintro ⟨before, after, h⟩
      cases before with
      | nil => exact Or.inl ⟨after, by simpa using h.symm⟩
      | cons d before =>
        simp only [List.cons_append, List.cons.injEq] at h
        exact Or.inr ⟨before, after, by simpa using h.2⟩

/-- `OnSite`, decided. -/
def onSite (destination : String) : Bool := occurs siteAddress.toList destination.toList

theorem onSite_iff (destination : String) : onSite destination = true ↔ OnSite destination := by
  simp only [onSite, OnSite, occurs_iff]
  constructor
  · rintro ⟨before, after, h⟩
    exact ⟨String.ofList before, String.ofList after, String.toList_inj.mp (by simpa using h)⟩
  · rintro ⟨before, after, rfl⟩
    exact ⟨before.toList, after.toList, by simp⟩

/-- `Stable`, decided. -/
def stable (destination : String) : Bool :=
  destination == siteBase ||
    (stableRoots.any (fun r => (stableUrl r).toList.isPrefixOf destination.toList) &&
      !destination.toList.contains '#')

/-- No stable address of a `stableRoots` directory has a `#`. -/
theorem stableUrl_no_fragment : ∀ r ∈ stableRoots, '#' ∉ (stableUrl r).toList := by
  decide

theorem stable_iff (destination : String) : stable destination = true ↔ Stable destination := by
  simp only [stable, Stable, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.any_eq_true,
    List.isPrefixOf_iff_prefix, Bool.not_eq_true']
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨⟨r, hr, rest, h⟩, hash⟩
    have hash : '#' ∉ destination.toList := by simpa using hash
    refine ⟨r, hr, String.ofList rest, String.toList_inj.mp (by simpa using h.symm), ?_⟩
    intro hm
    exact hash (by rw [← h]; exact List.mem_append_right _ (by simpa using hm))
  · rintro ⟨r, hr, rest, h, hash⟩
    subst h
    refine ⟨⟨r, hr, rest.toList, by simp⟩, ?_⟩
    have := stableUrl_no_fragment r hr
    simp [this, hash]

theorem Stable.not_edition {destination : String} (h : Stable destination) (e : Edition)
    (route : String) : destination ≠ e.url route := by
  rintro rfl
  rcases h with h | ⟨r, hr, rest, h, -⟩
  · have := congrArg String.toList h
    cases e <;> simp [Edition.url, Edition.root, String.toList_append] at this
  · have := congrArg String.toList h
    simp only [stableRoots, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> cases e <;>
      simp [Edition.url, Edition.root, stableUrl, String.toList_append] at this

/-- The destination of each link of `pieces`, in document order. -/
def destinations (pieces : List Piece) : List String :=
  pieces.filterMap fun
    | .enter destination => some destination
    | _ => none

theorem mem_destinations (pieces : List Piece) (destination : String) :
    destination ∈ destinations pieces ↔ Piece.enter destination ∈ pieces := by
  simp only [destinations, List.mem_filterMap]
  constructor
  · rintro ⟨piece, member, h⟩
    cases piece <;> simp at h
    exact h ▸ member
  · intro member
    exact ⟨_, member, rfl⟩

/-- The link destinations of `pieces` that are addresses of the site and are not stable, in
document order. -/
def unstableLinks (pieces : List Piece) : List String :=
  (destinations pieces).filter fun destination => onSite destination && !stable destination

/-- No link is unstable exactly when every link of the pieces to the site has a stable address. -/
theorem unstableLinks_nil_iff (pieces : List Piece) :
    unstableLinks pieces = [] ↔
      ∀ destination, Piece.enter destination ∈ pieces → OnSite destination →
        Stable destination := by
  simp only [unstableLinks, List.filter_eq_nil_iff, mem_destinations, Bool.and_eq_true,
    Bool.not_eq_true', not_and, Bool.not_eq_false, onSite_iff, stable_iff]

/-- What a link of `file` to `destination` is refused for. -/
def unstableReason (file destination : String) : String :=
  s!"{file}: the link to {destination} is not a stable address of the rule reference. A link of \
    this document to the site names no edition, so that it opens the latest release: write \
    {siteBase}, or an address below {" or ".intercalate (stableRoots.map stableUrl)} with no \
    fragment"

/-- What the document `file` is refused for, given the parser's reading of it: each link of a
document of `stableDocuments` to the site that has no stable address. A reading that cannot be
used reports nothing here; `documentErrors` reports it. -/
@[regula_decision]
def siteLinkErrors (file : String) : Reading → List String
  | .unread _ => []
  | .read pieces =>
    if file ∈ stableDocuments then (unstableLinks pieces).map (unstableReason file) else []

/-- The check of the site links reports nothing exactly when, if the document is one of
`stableDocuments` and its reading can be used, every link of it to the site has a stable
address. By `Stable.not_edition`, such a link names no edition. -/
theorem siteLinkErrors_nil_iff (file : String) (reading : Reading) :
    siteLinkErrors file reading = [] ↔
      ∀ pieces, reading = .read pieces → file ∈ stableDocuments →
        ∀ destination, Piece.enter destination ∈ pieces → OnSite destination →
          Stable destination := by
  cases reading with
  | unread reason => simp [siteLinkErrors]
  | read pieces =>
    by_cases member : file ∈ stableDocuments <;>
      simp [siteLinkErrors, member, unstableLinks_nil_iff]

/-- Registered contract of the executed check of the site links, as a two-way decision over the
file name and the reading (`siteLinkErrors_nil_iff`): it reports nothing for a `README.md` whose
one link is the site root, and an error for a `README.md` whose one link is the root of the
development edition. -/
theorem checked_siteLinkErrors : Regula.ExecutableContract siteLinkErrors (fun run =>
    Regula.Decides (· = [])
      (fun input : String × Reading =>
        ∀ pieces, input.2 = .read pieces → input.1 ∈ stableDocuments →
          ∀ destination, Piece.enter destination ∈ pieces → OnSite destination →
            Stable destination)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => siteLinkErrors_nil_iff input.1 input.2)
    ⟨("README.md", .read [.enter siteBase]),
      (siteLinkErrors_nil_iff _ _).mpr fun pieces read _ destination member _ => by
        cases read
        simp only [List.mem_singleton, Piece.enter.injEq] at member
        exact Or.inl member⟩
    ⟨("README.md", .read [.enter (Edition.dev.url "")]), fun accepted =>
      ((siteLinkErrors_nil_iff _ _).mp accepted _ rfl (by decide) _ (List.mem_singleton.mpr rfl)
        ⟨"https://", "/dev/", by decide⟩).not_edition .dev "" rfl⟩⟩

/-! Evaluated controls (observations of the compiled definitions, not proofs), on pieces written
out by hand; the controls on Markdown text, read by md4c, are in `markdown/RegulaMarkdown.lean`. -/

private def page : String := Edition.dev.url RuleId.sourceBuild.route

private def bare (line : String) : String :=
  s!"a.md:{line}: RG2003 is a bare rule ID in prose; make it a link to its rule page"

-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "x\n\nSee RG2003 and `RG2003`." (.read [.line, .text "x" "x", .line,
    .text "See RG2003 and " "See RG2003 and ", .code "RG2003", .text "." "."]) == [bare "3"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" ("[RG2003]\n\n[RG2003]: " ++ page)
    (.read [.line, .enter (page ++ "#fix"), .text "RG2003" "RG2003", .leave]) == []
-- The same text also stands on a line the parser does not report, so the lines are a bracket.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "*RG2003*\n\n[RG2003]: https://example.org/RG2003"
    (.read [.line, .text "RG2003" "RG2003"]) == [bare "1-3"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "- RG2003\n- RG2003" (.read [.line, .text "RG2003" "RG2003", .line,
    .enter "https://example.org/", .text "RG2003" "RG2003", .leave]) ==
  [bare "1", "a.md:2: RG2003 is linked to https://example.org/, which is not its rule page"]
-- A token is read across the edges of links and code spans: one that an edge divides is refused,
-- also between two links to the rule's page; one that is wholly code is no mention.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "RG2003 RG2003 RG2003 RG2003"
    (.read [.line, .text "RG" "RG", .enter "u", .text "2003" "2003", .leave, .text " " " ",
      .enter page, .text "RG" "RG", .leave, .enter page, .text "2003" "2003", .leave,
      .text " RG" " RG", .code "2003", .text " " " ", .code "RG", .code "2003"]) ==
  List.replicate 3 "a.md:1: RG2003 is only partly inside a link or a code span; write the whole \
    ID as one link to its rule page"
-- A link inside a link's text: once it is left, the text is the outer link's again. That is
-- the reading of these pieces; md4c's parse of such a link is refused where it is read.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "see x and RG2003 then RG2003"
    (.read [.line, .enter page, .text "see " "see ", .enter "https://example.org", .text "x" "x",
      .leave, .text " and RG2003" " and RG2003", .leave, .text " then RG2003" " then RG2003"]) ==
  [bare "1"]
-- Within a run its refused constructs are listed before its mentions.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "RG2003 x" (.read [.line, .text "RG2003 " "RG2003 ",
    .refused "refused", .text "x" "x"]) == ["a.md:1: refused", bare "1"]
-- The edge of a table cell or of an image's description ends a run.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "| RG | 2003 |" (.read [.line, .gap, .text "RG" "RG", .gap,
    .text "2003" "2003"]) == []
-- A refused construct is reported at the next text, whatever the text is.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "x\n\n<p>\ny\n</p>" (.read [.line, .text "x" "x", .line,
    .refused "raw HTML", .code "<p>", .line, .code "y", .line, .code "</p>"]) ==
  ["a.md:3: raw HTML"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "RG9999 and RG2003" (.read [.line, .enter page,
    .text "RG9999 and " "RG9999 and ", .leave, .text "RG2003" "RG2003"]) ==
  ["a.md:1: RG9999 is not a registered rule ID", bare "1"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "" (.unread "no reading") == ["a.md: no reading"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard auditMarker "<!-- lean-trusted-compiler -->\n" && auditMarker "<!-- lean-fail: unknown -->" &&
  !auditMarker "<!-- lean-fail: a --> RG2003 -->" && !auditMarker "<!-- RG2003 -->" &&
  !auditMarker "<!-- lean-fail: a\nb -->" && !auditMarker "<!-->"
-- The stable address of a rule that is in a release is a page of the rule in `README.md` and in
-- no other document; with a fragment, or as the address of another rule, it is not one there
-- either. The development page is a page of the rule in each document.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard target "README.md" .sourceBuild (stableUrl RuleId.sourceBuild.route) &&
  !target "docs/README.md" .sourceBuild (stableUrl RuleId.sourceBuild.route) &&
  !target "README.md" .sourceBuild (stableUrl RuleId.sourceBuild.route ++ "#fix") &&
  !target "README.md" .sourceBuild (stableUrl RuleId.proofHole.route) &&
  target "README.md" .sourceBuild (page ++ "#fix") && target "docs/README.md" .sourceBuild page
-- The same link to the stable address of the rule, in the pieces of two documents: accepted in
-- `README.md`, refused in a document that is not one of `stableDocuments`.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "README.md" "[RG2003]" (.read [.line,
    .enter (stableUrl RuleId.sourceBuild.route), .text "RG2003" "RG2003", .leave]) == [] &&
  documentErrors "docs/README.md" "[RG2003]" (.read [.line,
    .enter (stableUrl RuleId.sourceBuild.route), .text "RG2003" "RG2003", .leave]) ==
  [s!"docs/README.md:1: RG2003 is linked to {stableUrl RuleId.sourceBuild.route}, which is not \
    its rule page"]
-- The site links of `README.md`: the site root, a stable route below each stable root and a link
-- to another site are accepted. An address that names the development edition or a release, a
-- stable route with a fragment, an address with another scheme and an address of the site below
-- no stable root are refused. Another document is not read.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard siteLinkErrors "README.md" (.read [.line, .enter siteBase, .text "a" "a", .leave,
    .enter (stableUrl "rules/"), .leave, .enter (stableUrl RuleId.sourceBuild.route), .leave,
    .enter (stableUrl "standard/8-compliance-audit/"), .leave,
    .enter "https://github.com/rbeauchamp/regula", .leave, .code page]) == []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard siteLinkErrors "README.md" (.read [.enter page, .leave,
    .enter (Edition.url (.release ⟨0, 9, 0⟩) "rules/"), .leave,
    .enter (stableUrl "standard/8-compliance-audit/#DOC-04"), .leave,
    .enter "http://rbeauchamp.github.io/regula/rules/", .leave,
    .enter (stableUrl "versions/"), .leave]) ==
  [page, Edition.url (.release ⟨0, 9, 0⟩) "rules/", stableUrl "standard/8-compliance-audit/#DOC-04",
    "http://rbeauchamp.github.io/regula/rules/", stableUrl "versions/"].map
      (unstableReason "README.md")
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard siteLinkErrors "docs/README.md" (.read [.enter page, .leave]) == [] &&
  siteLinkErrors "README.md" (.unread "no reading") == []

end Regula.Markdown
