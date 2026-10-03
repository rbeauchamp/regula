import RegulaCore.Prose

/-! # Rule IDs in Markdown documents

Every rule ID that a tracked Markdown document mentions in prose is a link to that rule's page.
This module decides that from what a CommonMark parser reports of the document. It reads no
Markdown itself: `Regula.Markdown.read` (`website/RegulaMarkdown.lean`) runs md4c and turns its
parse into the `Piece`s below, so what is prose, code or a link is md4c's decision.

## Main declarations

- `Piece`, `Reading`: what the parser reports of a document, in document order: prose text with
  the link it lies in, code, raw HTML, and the boundaries between runs and between source lines.
- `decodeReference`: the character a numeric character reference renders as.
- `Found`, `mentions`: the rule-ID tokens (`Regula.Prose.tokenAt`) of the prose and of the raw
  HTML.
- `Found.Accepted`, `refused`, `refused_nil_iff`: a mention is accepted when it is not in raw HTML
  and is a registered rule ID inside a link to that rule's page (`Regula.Prose.Mention.Linked`).
- `target`: the page a Markdown document links a rule to, its development page.
- `Anchor`, `Placed`, `leftmost`, `rightmost`, `leftmost_le`, `le_rightmost`: the source lines of
  a mention. The parser reports text, not positions, so the lines are bracketed: every placement
  of the reported text on the source lines, in order, puts each piece between the lines
  `leftmost` and `rightmost` return for it.
- `documentErrors`, `documentErrors_nil_iff`, `checked_documentErrors`: the executed check of one
  document, reporting the file, the line or lines and the ID.

## What prose is

Prose is every text the parser reports outside code spans and code blocks: paragraphs, headings,
list items, block quotes, table cells, emphasis, link text and image descriptions. Text in a link
is linked to that link's destination, whether the link is written inline, as a reference to a
link reference definition or as an autolink. A rule ID in a raw HTML block is refused, since
telling prose from markup there needs an HTML parser. Link destinations and titles, code block
info strings and link reference definitions are not prose.

A rule ID spelled with character references is one too. A numeric reference is decoded
(`decodeReference`). A named reference is kept as written, which refuses `&RG1001;` (not a
character reference of HTML, so rendered as written) and relies on this fact about HTML's named
character references: none expands to text that contains `R`, `G` or an ASCII digit. It was
checked against md4c's table of them, in which only `&fjlig;` expands to ASCII letters or digits.

## Boundaries

`refused_nil_iff` and `documentErrors_nil_iff` are about the pieces they are given: that the
pieces are the document's is the parser's part, stated in `website/RegulaMarkdown.lean` and in
the contributor guide. `leftmost_le` and `le_rightmost` bound every placement that `Placed`
admits; that the true lines of the reported text are such a placement rests on the parser
reporting each piece of text as it stands on one source line, in source order, and on a line
break or a new block lying between pieces of different lines. When no placement exists, the
whole document is the bracket.
-/

namespace Regula.Markdown

open Regula.Prose

/-! ## What the parser reports -/

/-- One piece of a Markdown document as its parser reports it, in document order. -/
inductive Piece where
  /-- Prose: `slice` is the text as the parser reported it from the source, `rendered` what it
  renders as (a character reference decoded) and `link` the destination of the link whose text
  it lies in, if any. -/
  | text (slice rendered : String) (link : Option String)
  /-- Text of a code span or code block, as the parser reported it from the source. -/
  | code (slice : String)
  /-- Text of a raw HTML block, as the parser reported it from the source. -/
  | raw (slice : String)
  /-- A boundary between two runs of prose on one source line, such as a link's edge or the
  edge of a table cell. -/
  | gap
  /-- A line boundary: the pieces after it lie on a later source line than the pieces before
  it. -/
  | line
  deriving DecidableEq, Repr

/-- What the parser reports of one document. -/
inductive Reading where
  /-- The parser's reading cannot be used, for the reason given. -/
  | unread (reason : String)
  /-- The document's pieces, in document order. -/
  | read (pieces : List Piece)
  deriving DecidableEq, Repr

/-- The value of the hexadecimal digit `c`, if it is one. -/
def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The number that `digits` write in base `base`, if every one is a digit of that base. -/
def number? (base : Nat) (digits : List Char) : Option Nat :=
  digits.foldl (fun value c => value.bind fun n =>
    (hexDigit? c).bind fun d => if d < base then some (base * n + d) else none) (some 0)

/-- What the character reference `reference` renders as. A numeric reference, `&#N;` or `&#xN;`,
is the character with that code point, or U+FFFD when there is none or it is zero, as CommonMark
defines. Any other reference is kept as written (see the module documentation). -/
def decodeReference (reference : String) : String :=
  match reference.toList with
  | '&' :: '#' :: rest =>
    let digits := rest.takeWhile (· != ';')
    let value := match digits with
      | 'x' :: hex | 'X' :: hex => number? 16 hex
      | decimal => number? 10 decimal
    match value with
    | some n => if n != 0 && (Char.ofNat n).toNat == n then String.singleton (Char.ofNat n)
      else "�"
    | none => reference
  | _ => reference

/-! ## Mentions -/

/-- Whether `text` has no character other than whitespace. The parser reports the spaces and
line ends it supplies itself as such text, so only other text is located in the source. -/
def blank (text : String) : Bool := text.toList.all Char.isWhitespace

/-- The source text that locates a piece: what the parser reported for it, unless it is
`blank`. -/
def Piece.located? : Piece → Option String
  | .text slice _ _ | .code slice | .raw slice => if blank slice then none else some slice
  | .gap | .line => none

/-- One rule-ID token of a document. -/
structure Found where
  /-- The token, such as `RG1001`. -/
  token : String
  /-- The destination of the link whose text the token lies in, if any. -/
  link : Option String
  /-- Whether the token lies in a raw HTML block. -/
  raw : Bool
  /-- The number of located pieces (`Piece.located?`) before the piece the token starts in. -/
  anchor : Nat
  deriving DecidableEq, Repr

/-- The `anchor` of the part of a run that holds the character at `offset`; `parts` are the
run's parts in order, each with its anchor and its text. -/
def anchorAt : List (Nat × String) → Nat → Nat
  | [], _ => 0
  | [(anchor, _)], _ => anchor
  | (anchor, text) :: rest, offset =>
    if offset < text.length then anchor else anchorAt rest (offset - text.length)

/-- The rule-ID tokens of one run, whose text is the texts of `parts` in order. -/
def runTokens (link : Option String) (raw : Bool) (parts : List (Nat × String)) : List Found :=
  ((splitTokens none 0 [] (String.join (parts.map (·.2))).toList).foldl
    (fun (acc : Nat × List Found) part =>
      match part with
      | .inl between => (acc.1 + between.length, acc.2)
      | .inr token => (acc.1 + token.length, ⟨token, link, raw, anchorAt parts acc.1⟩ :: acc.2))
    (0, [])).2.reverse

/-- The state of the scan of a document's pieces. -/
structure Scan where
  /-- The number of located pieces read so far. -/
  anchor : Nat := 0
  /-- The link of the run in progress. -/
  link : Option String := none
  /-- The parts of the run in progress, last first, each with its anchor. -/
  run : List (Nat × String) := []
  /-- The tokens found so far, last first. -/
  found : List Found := []

/-- End the run in progress and keep its tokens. -/
def Scan.flush (s : Scan) : Scan :=
  { s with run := [], found := (runTokens s.link false s.run.reverse).reverse ++ s.found }

/-- The scan after a piece with source text `slice`. -/
def Scan.past (s : Scan) (slice : String) : Scan :=
  if blank slice then s else { s with anchor := s.anchor + 1 }

/-- Read one piece. Prose with the same link continues the run in progress; any other piece
ends it, so no token spans a code span, a link's edge, a table cell's edge or a line. A piece of
a raw HTML block is a run of its own. -/
def Scan.step (s : Scan) : Piece → Scan
  | .text slice rendered link =>
    let s := if s.link == link then s else { s.flush with link }
    Scan.past { s with run := (s.anchor, rendered) :: s.run } slice
  | .code slice => s.flush.past slice
  | .raw slice =>
    let s := s.flush
    Scan.past { s with found := (runTokens none true [(s.anchor, slice)]).reverse ++ s.found }
      slice
  | .gap | .line => s.flush

/-- The rule-ID tokens of a document's prose and raw HTML, in document order. -/
def mentions (pieces : List Piece) : List Found :=
  (pieces.foldl Scan.step {}).flush.found.reverse

/-- The mention of prose that `f` is, on line `line`. -/
def Found.mention (line : Nat) (f : Found) : Mention := ⟨line, f.token, f.link⟩

/-- `f` is accepted: it is not in raw HTML, its token is a registered rule ID, and it lies in the
text of a link whose destination `target` accepts as that rule's page. -/
def Found.Accepted (target : RuleId → String → Bool) (f : Found) : Prop :=
  f.raw = false ∧ (f.mention 0).Linked target

/-- `Found.Accepted`, decided. -/
def Found.accepted (target : RuleId → String → Bool) (f : Found) : Bool :=
  !f.raw && (f.mention 0).linked target

theorem Found.accepted_iff (target : RuleId → String → Bool) (f : Found) :
    f.accepted target = true ↔ f.Accepted target := by
  simp [Found.accepted, Found.Accepted, Mention.linked_iff]

/-- The mentions of `pieces` that are not accepted, in document order. -/
def refused (target : RuleId → String → Bool) (pieces : List Piece) : List Found :=
  (mentions pieces).filter fun f => !f.accepted target

/-- Nothing is refused exactly when every rule-ID token of the document's prose and raw HTML is
accepted. -/
theorem refused_nil_iff (target : RuleId → String → Bool) (pieces : List Piece) :
    refused target pieces = [] ↔ ∀ f ∈ mentions pieces, f.Accepted target := by
  simp only [refused, List.filter_eq_nil_iff, Bool.not_eq_true', Bool.not_eq_false]
  exact ⟨fun h f hf => (Found.accepted_iff target f).mp (h f hf),
    fun h f hf => (Found.accepted_iff target f).mpr (h f hf)⟩

/-- Whether `destination` is rule `id`'s page in the development edition (`Edition.url`), with
or without a fragment: the link every tracked Markdown document gives a rule. -/
def target (id : RuleId) (destination : String) : Bool :=
  destination == Edition.dev.url id.route ||
    destination.startsWith (Edition.dev.url id.route ++ "#")

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

/-- What a refused mention reports: the file, the line or the first and last line it can lie on,
the ID and why it is refused. -/
def Found.describe (file : String) (first last : Nat) (f : Found) : String :=
  s!"{file}:{first}" ++ (if first == last then "" else s!"-{last}") ++ s!": {f.token} " ++
    if f.raw then
      "is in a raw HTML block, which is not read as prose; write it in Markdown, as a link to \
        its rule page"
    else (f.mention first).reason

/-- What the document `file` with text `source` and pieces `pieces` is refused for: each rule ID
in its prose that is not a link to its rule page (`target`) and each rule ID in a raw HTML block,
with the line it lies on, or the first and last line it can lie on (`leftmost`, `rightmost`,
`occursOn`; the whole document when the pieces have no placement). -/
def errors (file source : String) (pieces : List Piece) : List String :=
  match refused target pieces with
  | [] => []
  | found =>
    let lines := source.splitOn "\n"
    let located := anchors false pieces
    let first := (leftmost occursOn 1 located lines).getD []
    let last := (rightmost occursOn 1 lines located).getD []
    found.map fun f =>
      f.describe file (first[f.anchor]?.getD 1) (last[f.anchor]?.getD lines.length)

theorem errors_nil_iff (file source : String) (pieces : List Piece) :
    errors file source pieces = [] ↔ refused target pieces = [] := by
  cases h : refused target pieces <;> simp [errors, h]

/-- What the document `file` with text `source` is refused for, given the parser's reading of
it: that the reading cannot be used, or the `errors` of its pieces. -/
def documentErrors (file source : String) : Reading → List String
  | .unread reason => [s!"{file}: {reason}"]
  | .read pieces => errors file source pieces

/-- The document check reports nothing exactly when the parser's reading can be used and every
rule-ID token of its prose and raw HTML is accepted: outside raw HTML, a registered rule ID, and
linked to that rule's development page. -/
theorem documentErrors_nil_iff (file source : String) (reading : Reading) :
    documentErrors file source reading = [] ↔
      ∃ pieces, reading = .read pieces ∧ ∀ f ∈ mentions pieces, f.Accepted target := by
  cases reading with
  | unread reason => simp [documentErrors]
  | read pieces => simp [documentErrors, errors_nil_iff, refused_nil_iff]

/-- Registered contract of the executed Markdown document check. -/
theorem checked_documentErrors : Regula.ExecutableContract documentErrors (fun run =>
    ∀ file source reading, run file source reading = [] ↔
      ∃ pieces, reading = .read pieces ∧ ∀ f ∈ mentions pieces, f.Accepted target) :=
  ⟨documentErrors_nil_iff⟩

/-! Evaluated controls (observations of the compiled definitions, not proofs), on pieces written
out by hand; the controls on Markdown text, read by md4c, are in `website/RegulaMarkdown.lean`. -/
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "x\n\nSee RG2003 and `RG2003`." (.read [.line,
    .text "x" "x" none, .line, .text "See RG2003 and " "See RG2003 and " none, .code "RG2003",
    .text "." "." none]) ==
  ["a.md:3: RG2003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" ("[RG2003]\n\n[RG2003]: " ++ Edition.dev.url RuleId.sourceBuild.route)
    (.read [.line, .gap,
      .text "RG2003" "RG2003" (some (Edition.dev.url RuleId.sourceBuild.route ++ "#fix")), .gap]) ==
  []
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "*RG2003*\n\n[RG2003]: https://example.org/RG2003"
    (.read [.line, .text "RG2003" "RG2003" none]) ==
  ["a.md:1-3: RG2003 is a bare rule ID in prose; make it a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "- RG1001\n- RG1001" (.read [.line, .text "RG1001" "RG1001" none,
    .line, .text "RG1001" "RG1001" (some "https://example.org/")]) ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:2: RG1001 is linked to https://example.org/, which is not its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "<p>RG1001</p>" (.read [.line, .raw "<p>RG1001</p>"]) ==
  ["a.md:1: RG1001 is in a raw HTML block, which is not read as prose; write it in Markdown, as \
    a link to its rule page"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "R&#71;1001 &RG1002; RG9999" (.read [.line, .text "R" "R" none,
    .text "&#71;" (decodeReference "&#71;") none, .text "1001 " "1001 " none,
    .text "&RG1002;" (decodeReference "&RG1002;") none, .text " RG9999" " RG9999" none]) ==
  ["a.md:1: RG1001 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG1002 is a bare rule ID in prose; make it a link to its rule page",
    "a.md:1: RG9999 is not a registered rule ID"]
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard decodeReference "&#x47;" == "G" && decodeReference "&#0;" == "�" &&
  decodeReference "&#xD800;" == "�" && decodeReference "&amp;" == "&amp;"
-- Compiled-evaluation observation at build time, not a kernel-checked proof.
#guard documentErrors "a.md" "" (.unread "no reading") == ["a.md: no reading"]

end Regula.Markdown
