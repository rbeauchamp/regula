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
- `target`, `released`, `released_iff`: the pages a Markdown document links a rule to: its
  development page, or its stable address when the rule is in a release.
- `auditMarker`: the one form of raw HTML that is read, a fence marker of the documentation audit.
- `Anchor`, `Placed`, `leftmost`, `rightmost`, `leftmost_le`, `le_rightmost`: the source lines of
  a finding. The parser reports text, not positions, so the lines are bracketed: every placement
  of the reported text on the source lines, in order, puts each piece between the lines
  `leftmost` and `rightmost` return for it.
- `documentErrors`, `documentErrors_nil_iff`, `checked_documentErrors`: the executed check of one
  document, reporting the file, the line or lines and the ID or the refused construct; a
  document whose reading cannot be used is reported by file and reason alone, without its IDs.
- `OnSite`, `Stable`, `Stable.not_edition`, `stableDocuments`, `siteLinkErrors`,
  `siteLinkErrors_nil_iff`, `checked_siteLinkErrors`: the executed check of the links of the root
  `README.md` to the site. Each has a stable address, the site root or an address below a
  `stableRoots` directory with no fragment, so it names no edition and opens the latest release.

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
That a stable address has a page is not decided here: the site build requires each address of
the root `README.md` in its artifact (`Regula.Site.siteAnchors`).
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

/-- Whether `text` has no character other than whitespace. The parser reports the spaces and
line ends it supplies itself as such text, so only other text is located in the source. -/
def blank (text : String) : Bool := text.toList.all Char.isWhitespace

/-- The source text that locates a piece: what the parser reported for it, unless it is
`blank`. -/
def Piece.located? : Piece → Option String
  | .text slice _ | .code slice => if blank slice then none else some slice
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
  if blank slice then s else { s with anchor := s.anchor + 1 }

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

/-- Whether rule `id` is in a release: its lifecycle records the release that introduced it. -/
def released (id : RuleId) : Bool := (descriptor id).lifecycle.introduced != .unreleased

/-- A rule is in a release exactly when a listed release introduced it. Each release's edition
has a page for every rule of its build, and a rule is never removed, so the edition of every
later release has the page too; that step is argued, and the site build observes it for the
addresses of the root `README.md` (`Regula.Site.siteAnchors`). -/
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

/-- Whether `destination` is a page of rule `id` that a tracked Markdown document links: the
rule's page in the development edition (`Edition.url`), with or without a fragment, or, for a
rule that is in a release (`released`), its stable address (`stableUrl`) with no fragment, which
opens the page of the latest release. A stable route does not keep a fragment. -/
def target (id : RuleId) (destination : String) : Bool :=
  destination == Edition.dev.url id.route ||
    destination.startsWith (Edition.dev.url id.route ++ "#") ||
    (released id && destination == stableUrl id.route)

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
construct the check refuses to read and each rule ID in its prose that is not a link to its rule
page (`target`), with the line it lies on, or the first and last line it can lie on (`leftmost`,
`rightmost`, `occursOn`; the whole document when the pieces have no placement). -/
def errors (file source : String) (pieces : List Piece) : List String :=
  match rejected target pieces with
  | [] => []
  | found =>
    let lines := source.splitOn "\n"
    let located := anchors false pieces
    let first := (leftmost occursOn 1 located lines).getD []
    let last := (rightmost occursOn 1 lines located).getD []
    found.map fun f =>
      f.describe file (first[f.anchor]?.getD 1) (last[f.anchor]?.getD lines.length)

theorem errors_nil_iff (file source : String) (pieces : List Piece) :
    errors file source pieces = [] ↔ rejected target pieces = [] := by
  cases h : rejected target pieces <;> simp [errors, h]

/-- What the document `file` with text `source` is refused for, given the parser's reading of
it: that the reading cannot be used, or the `errors` of its pieces. -/
@[regula_decision]
def documentErrors (file source : String) : Reading → List String
  | .unread reason => [s!"{file}: {reason}"]
  | .read pieces => errors file source pieces

/-- The document check reports nothing exactly when the parser's reading can be used and every
finding of it is accepted: it has no construct the check refuses to read, and every rule-ID
token of its runs that is not wholly code is a registered rule ID inside one link to a page of
that rule that `target` accepts. -/
theorem documentErrors_nil_iff (file source : String) (reading : Reading) :
    documentErrors file source reading = [] ↔
      ∃ pieces, reading = .read pieces ∧ ∀ f ∈ findings pieces, f.Accepted target := by
  cases reading with
  | unread reason => simp [documentErrors]
  | read pieces => simp [documentErrors, errors_nil_iff, rejected_nil_iff]

/-- Registered contract of the executed Markdown document check, as a two-way decision over the
file name, the source and the reading (`documentErrors_nil_iff`): it reports nothing for a
document read as no pieces, and an error for a document that was not read. -/
theorem checked_documentErrors : Regula.ExecutableContract documentErrors (fun run =>
    Regula.Decides (· = [])
      (fun input : (String × String) × Reading =>
        ∃ pieces, input.2 = .read pieces ∧ ∀ f ∈ findings pieces, f.Accepted target)
      (Function.uncurry (Function.uncurry run))) :=
  ⟨.of_iff (fun input => documentErrors_nil_iff input.1.1 input.1.2 input.2)
    ⟨(("", ""), .read []), (documentErrors_nil_iff "" "" (.read [])).mpr
      ⟨[], rfl, by simp [(by decide : findings [] = [])]⟩⟩
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

/-- The tracked documents whose links to the site name no edition, so that each link opens the
latest release and a release changes no such document: the root `README.md`. -/
def stableDocuments : List String := ["README.md"]

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
-- The stable address of a rule that is in a release is a page of the rule; with a fragment, or
-- as the address of another rule, it is not.
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard target .sourceBuild (stableUrl RuleId.sourceBuild.route) &&
  !target .sourceBuild (stableUrl RuleId.sourceBuild.route ++ "#fix") &&
  !target .sourceBuild (stableUrl RuleId.proofHole.route) && target .sourceBuild (page ++ "#fix")
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
