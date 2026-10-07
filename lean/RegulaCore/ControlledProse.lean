import RegulaCore.Markdown
import RegulaCore.Vocabulary

/-! # Exact checks of the prose of Markdown documents

The writing guide (`docs/guides/writing.md`) gives the rules for new and changed documents of a
repository. This module decides the rules that a text decides alone, from what a CommonMark
parser reports of a document (`Regula.Markdown.Reading`) and from the vocabulary of the project
(`Regula.Controlled.Vocabulary`). It is a check of a repository's own documents, as the rule-ID
check of `RegulaCore.Markdown` is. It is not a rule of Regula's standard and has no rule ID.

## Main declarations

- `Anchored`, `Atoms`, `Block.Of`, `Blocks`, `blocks`, `blocks_iff`: the blocks of a document and
  the atoms of each one. A block is a maximal run of pieces with no start of a block after its
  first piece.
- `Slot.Marked`, `Marks`, `Slot.Signed`: what a word of a sentence is for a comparison with the
  vocabulary and with the abbreviations, by the one form of a word (`Normal`).
- `EachBlock`, `perBlock`, `perBlock_nil_iff`: a statement about each block of a document with
  the runs of its sentences (`Regula.Controlled.Divided`), and the findings of a function that
  decides that statement block by block.
- `longSentences` (C1), `longSteps` (C2), `longParagraphs` (C3), `semicolons` (C4),
  `contractions` (C5), `replacedNames` (C6), `replacedWords` (C7) and `abbreviations` (C8): the
  findings of each check, with a registered two-way contract for each (`checked_longSentences`
  and the others).
- `Check`, `findings`, `tally`, `tally_zero_iff`: the number of findings of each check in a
  document, which is zero for each check exactly when the document conforms to all eight.

## What a check reads

A block is a heading, a paragraph, a paragraph of a list item, or a table cell, as the parser
reports it (`Regula.Markdown.Kind`). A code block is a block with no prose. The atoms of a block
are those of its pieces (`Atoms`): the rendered characters of its prose, one atom for each
code piece, and one space for each line boundary and each edge of a table cell or of an image's
description. The description of an image is thus prose of its block.

The words and the sentences of a block are those of `RegulaCore.ControlledText`. A sentence does
not continue into the next block, so the text before a list and each list item are counted
apart.

## Specifications

Each specification is stated with relations: `Blocks` and `Divided` for the blocks and the
sentences, `Marks` and `Slot.Signed` for the words that a check compares, and `Normal` for the
form of a word. A function of a check uses the definitions that its specification names, and it
decides the statements of the specification with their `Decidable` instances. No second
definition takes the place of one. The account of each decision registration names the
functions that its two sides share.
`blocks_iff`, `divided_iff`, `marks_iff`, `signed_iff`, `normal_iff`, `words_iff` and
`positions_nil_iff` connect the functions that a check runs with the statements.

## Boundaries

Each contract is about the reading it is given. That the reading is the document's rests on the
parser and on the translation of its parse into pieces (`markdown/RegulaMarkdown.lean`), which
has no theorem. No contract says that a sentence here is a sentence for a reader, or that the
number of words here is the number a reader counts: the writing guide gives the conditions.
-/

namespace Regula.Controlled

open Regula.Markdown (Kind Piece Reading)

/-! ## Blocks -/

/-- `marked` is `pieces`, each with its place: the number of located pieces before it
(`Regula.Markdown.Piece.located?`). -/
def Anchored (pieces : List Piece) (marked : List (Nat × Piece)) : Prop :=
  marked.map (·.2) = pieces ∧
    ∀ before entry after, marked = before ++ entry :: after →
      entry.1 = before.countP fun other => other.2.located?.isSome

/-- `pieces`, each with its place, where `anchor` located pieces are before the first one. -/
def anchorsFrom (anchor : Nat) : List Piece → List (Nat × Piece)
  | [] => []
  | piece :: rest =>
    (anchor, piece) ::
      anchorsFrom (if (Piece.located? piece).isSome then anchor + 1 else anchor) rest

theorem anchorsFrom_nil (anchor : Nat) : anchorsFrom anchor [] = [] := rfl

theorem anchorsFrom_cons (anchor : Nat) (piece : Piece) (rest : List Piece) :
    anchorsFrom anchor (piece :: rest) =
      (anchor, piece) :: anchorsFrom (if piece.located?.isSome then anchor + 1 else anchor) rest :=
  rfl

theorem anchorsFrom_spec (pieces : List Piece) :
    ∀ (anchor : Nat) (marked : List (Nat × Piece)),
      (marked.map (·.2) = pieces ∧
        ∀ before entry after, marked = before ++ entry :: after →
          entry.1 = anchor + before.countP fun other => other.2.located?.isSome) ↔
        marked = anchorsFrom anchor pieces := by
  induction pieces with
  | nil =>
    intro anchor marked
    constructor
    · rintro ⟨hmap, -⟩
      simpa [anchorsFrom_nil] using hmap
    · rintro rfl
      exact ⟨rfl, fun before entry after hsplit => by simp [anchorsFrom_nil] at hsplit⟩
  | cons piece rest ih =>
    intro anchor marked
    constructor
    · rintro ⟨hmap, hplace⟩
      cases marked with
      | nil => simp at hmap
      | cons first more =>
        simp only [List.map_cons, List.cons.injEq] at hmap
        have hfirst : first = (anchor, piece) := by
          have := hplace [] first more rfl
          cases first
          simp_all
        subst hfirst
        have hmore := (ih (if piece.located?.isSome then anchor + 1 else anchor) more).mp
          ⟨hmap.2, fun before entry after hsplit => by
            have := hplace ((anchor, piece) :: before) entry after (by rw [hsplit]; rfl)
            rw [this, List.countP_cons]
            split <;> simp_all <;> omega⟩
        simp [anchorsFrom_cons, hmore]
    · rintro rfl
      obtain ⟨hmap, hplace⟩ :=
        (ih (if piece.located?.isSome then anchor + 1 else anchor) _).mpr rfl
      refine ⟨by simp [anchorsFrom_cons, hmap], fun before entry after hsplit => ?_⟩
      cases before with
      | nil =>
        simp only [anchorsFrom_cons, List.nil_append, List.cons.injEq] at hsplit
        simp [← hsplit.1]
      | cons first before =>
        simp only [anchorsFrom_cons, List.cons_append, List.cons.injEq] at hsplit
        obtain ⟨rfl, hrest⟩ := hsplit
        rw [hplace before entry after hrest, List.countP_cons]
        split <;> simp_all <;> omega

/-- The places of the pieces are those `anchorsFrom` gives. -/
theorem anchored_iff (pieces : List Piece) (marked : List (Nat × Piece)) :
    Anchored pieces marked ↔ marked = anchorsFrom 0 pieces := by
  rw [← anchorsFrom_spec pieces 0 marked]
  simp [Anchored]

/-- `atoms` are the atoms of one piece at the place `anchor`. -/
inductive Atoms (anchor : Nat) : Piece → List Atom → Prop
  /-- Prose gives one atom for each rendered character, where `’` (U+2019) is read as an
  apostrophe. -/
  | text (slice rendered : String) :
    Atoms anchor (.text slice rendered)
      (rendered.toList.map fun c => ⟨anchor, some (if c = '’' then '\'' else c)⟩)
  /-- A piece of code gives one atom of code. -/
  | code (slice : String) : Atoms anchor (.code slice) [⟨anchor, none⟩]
  /-- An edge of a table cell or of an image's description gives one space. -/
  | gap : Atoms anchor .gap [⟨anchor, some ' '⟩]
  /-- A line boundary gives one space. -/
  | line : Atoms anchor .line [⟨anchor, some ' '⟩]
  /-- The start of a link's text gives no atom. -/
  | enter (destination : String) : Atoms anchor (.enter destination) []
  /-- The end of a link's text gives no atom. -/
  | leave : Atoms anchor .leave []
  /-- A refused construct gives no atom. -/
  | refused (reason : String) : Atoms anchor (.refused reason) []
  /-- The start of a block gives no atom. -/
  | start (kind : Kind) : Atoms anchor (.start kind) []

/-- One block of a document: its kind and its atoms, in order. -/
structure Block where
  /-- The kind of the block. -/
  kind : Kind
  /-- The characters of the block's prose and its code pieces. -/
  atoms : List Atom
  deriving DecidableEq, Repr

/-- `block` is the block of the run `part` of pieces with their places. Its kind is the kind
that the first piece starts, or a paragraph when the first piece starts no block. Its atoms are
those of the pieces, in order. -/
structure Block.Of (part : List (Nat × Piece)) (block : Block) : Prop where
  /-- The kind is the one that the first piece starts, or a paragraph. -/
  kind : (∃ anchor rest, part = (anchor, .start block.kind) :: rest) ∨
    (block.kind = .paragraph ∧ ∀ anchor kind rest, part ≠ (anchor, .start kind) :: rest)
  /-- The atoms are those of each piece at its place, in order. -/
  atoms : ∃ lists, Paired (fun entry atoms => Atoms entry.1 entry.2 atoms) part lists ∧
    block.atoms = lists.flatten

/-- Two pieces next to each other are in one block: the second starts no block. -/
def Continues (_ next : Nat × Piece) : Prop := ∀ kind, next.2 ≠ .start kind

/-- `blocks` are the blocks of `pieces`: the pieces with their places, divided into maximal runs
in which no piece after the first starts a block, and the block of each run. -/
def Blocks (pieces : List Piece) (blocks : List Block) : Prop :=
  ∃ marked parts, Anchored pieces marked ∧ Runs Continues marked parts ∧
    Paired Block.Of parts blocks

/-- The kind of the block that a piece starts, if it starts one. -/
def kindOf? : Piece → Option Kind
  | .start kind => some kind
  | _ => none

/-- The atoms of one piece at the place `anchor`. -/
def atomsOf (anchor : Nat) : Piece → List Atom
  | .text _ rendered => rendered.toList.map fun c => ⟨anchor, some (if c = '’' then '\'' else c)⟩
  | .code _ => [⟨anchor, none⟩]
  | .gap | .line => [⟨anchor, some ' '⟩]
  | .enter _ | .leave | .refused _ | .start _ => []

/-- The atoms of a piece are one list only: the computed one. -/
theorem atoms_iff (anchor : Nat) (piece : Piece) (atoms : List Atom) :
    Atoms anchor piece atoms ↔ atoms = atomsOf anchor piece := by
  constructor
  · intro h
    cases h <;> rfl
  · rintro rfl
    cases piece <;> constructor

/-- The block of a run of pieces. -/
def blockOf (part : List (Nat × Piece)) : Block :=
  ⟨(part.head?.bind fun entry => kindOf? entry.2).getD .paragraph,
    part.flatMap fun entry => atomsOf entry.1 entry.2⟩

/-- The block of a run of pieces is one block only: the computed one. -/
theorem blockOf_iff (part : List (Nat × Piece)) (block : Block) :
    Block.Of part block ↔ block = blockOf part := by
  have hatoms := paired_iff (R := fun (entry : Nat × Piece) atoms => Atoms entry.1 entry.2 atoms)
    (f := fun entry => atomsOf entry.1 entry.2) (fun entry atoms => atoms_iff entry.1 entry.2 atoms)
    part
  constructor
  · rintro ⟨hkind, lists, hpaired, hflat⟩
    obtain ⟨kind, atoms⟩ := block
    rw [hatoms] at hpaired
    subst hpaired
    simp only [blockOf, Block.mk.injEq]
    refine ⟨?_, by simpa [List.flatMap_def] using hflat⟩
    rcases hkind with ⟨anchor, rest, rfl⟩ | ⟨hkind, hnone⟩
    · rfl
    · simp only at hkind
      subst hkind
      cases part with
      | nil => rfl
      | cons entry rest =>
        obtain ⟨anchor, piece⟩ := entry
        cases piece with
        | start kind => exact absurd rfl (hnone anchor kind rest)
        | _ => rfl
  · rintro rfl
    refine ⟨?_, _, (hatoms _).mpr rfl, by simp [blockOf, List.flatMap_def]⟩
    cases part with
    | nil => exact .inr ⟨rfl, fun _ _ _ h => by cases h⟩
    | cons entry rest =>
      obtain ⟨anchor, piece⟩ := entry
      cases piece with
      | start kind => exact .inl ⟨anchor, rest, rfl⟩
      | _ => exact .inr ⟨rfl, fun _ _ _ h => by cases h⟩

namespace Exec

/-- Two pieces next to each other are in one block, for the functions (`continues_iff`). -/
abbrev Continues (_ next : Nat × Piece) : Prop := kindOf? next.2 = none

instance : DecidableRel Continues := fun _ _ => inferInstance

theorem continues_iff (previous next : Nat × Piece) :
    Continues previous next ↔ Controlled.Continues previous next := by
  obtain ⟨anchor, piece⟩ := next
  cases piece <;> simp [Continues, Controlled.Continues, kindOf?]

end Exec

/-- The blocks of a document, in order. -/
def blocks (pieces : List Piece) : List Block :=
  (runs Exec.Continues (anchorsFrom 0 pieces)).map blockOf

/-- The blocks of a document are one result only: the computed one. -/
theorem blocks_iff (pieces : List Piece) (result : List Block) :
    Blocks pieces result ↔ result = blocks pieces := by
  have hrel : Continues = Exec.Continues :=
    funext fun previous => funext fun next => propext (Exec.continues_iff previous next).symm
  constructor
  · rintro ⟨marked, parts, hmarked, hparts, hblocks⟩
    rw [anchored_iff] at hmarked
    rw [hrel, runs_iff] at hparts
    rw [paired_iff blockOf_iff] at hblocks
    rw [hblocks, hparts, hmarked, blocks]
  · rintro rfl
    exact ⟨_, _, (anchored_iff _ _).mpr rfl, by rw [hrel]; exact runs_spec _,
      (paired_iff blockOf_iff _ _).mpr rfl⟩

/-- The block starts with `WARNING:` or `CAUTION:`, in uppercase, after the space characters at
its start. -/
abbrev Block.Signal (b : Block) : Prop :=
  ∃ word ∈ ["WARNING:", "CAUTION:"],
    word.toList.map some <+:
      (b.atoms.map (·.char)).dropWhile fun c => c.any fun ch => decide (Spacing ch)

/-- The block is in no item of an ordered list: it is a paragraph in no list item, a paragraph
in items of unordered lists only, or a table cell. -/
abbrev Block.Plain (b : Block) : Prop := b.kind = .paragraph ∨ b.kind = .bullet ∨ b.kind = .cell

/-- The block is a procedure block: a paragraph or a table cell in an item of an ordered list,
or a paragraph, a paragraph of an unordered list item or a table cell that starts with
`WARNING:` or `CAUTION:`. -/
abbrev Block.Procedure (b : Block) : Prop :=
  b.kind = .step ∨ b.kind = .stepCell ∨ (b.Plain ∧ b.Signal)

/-- The block is a description block: a paragraph, a paragraph of an unordered list item or a
table cell that is in no item of an ordered list and does not start with `WARNING:` or
`CAUTION:`. -/
abbrev Block.Description (b : Block) : Prop := b.Plain ∧ ¬b.Signal

/-- The parser reports the block as a paragraph, in a list item or not. -/
abbrev Block.Paragraph (b : Block) : Prop :=
  b.kind = .paragraph ∨ b.kind = .step ∨ b.kind = .bullet

instance : DecidablePred Block.Signal := fun b => by
  unfold Block.Signal
  infer_instance

instance : DecidablePred Block.Plain := fun b => by
  unfold Block.Plain
  infer_instance

instance : DecidablePred Block.Procedure := fun b => by
  unfold Block.Procedure
  infer_instance

instance : DecidablePred Block.Description := fun b => by
  unfold Block.Description
  infer_instance

instance : DecidablePred Block.Paragraph := fun b => by
  unfold Block.Paragraph
  infer_instance

/-! ## Findings -/

/-- One finding of a check. -/
structure Found where
  /-- The place of the piece it is in. -/
  anchor : Nat
  /-- What was found. -/
  detail : String
  deriving DecidableEq, Repr

/-- The runs of the sentences of a block. -/
abbrev Cut := List (List (Option Part))

/-- Each block of a document that was read has `P`, with the runs of its sentences. -/
def EachBlock (P : Block → Cut → Prop) (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ result, Blocks pieces result → ∀ b ∈ result, ∀ cut, Divided b.atoms cut → P b cut

/-- The findings of the blocks of a document, block by block; one finding for a document whose
reading cannot be used. -/
def perBlock (find : Block → Cut → List Found) : Reading → List Found
  | .unread reason => [⟨0, s!"the document was not read: {reason}"⟩]
  | .read pieces => (blocks pieces).flatMap fun b => find b (divide b.atoms)

/-- A function that finds nothing in a block exactly when the block has `P` finds nothing in a
document exactly when each block has `P`. -/
theorem perBlock_nil_iff {find : Block → Cut → List Found} {P : Block → Cut → Prop}
    (h : ∀ b cut, find b cut = [] ↔ P b cut) (reading : Reading) :
    perBlock find reading = [] ↔ EachBlock P reading := by
  cases reading with
  | unread reason => simp [perBlock, EachBlock]
  | read pieces =>
    simp only [perBlock, EachBlock, List.flatMap_eq_nil_iff, h, Reading.read.injEq,
      exists_eq_left', blocks_iff, divided_iff, forall_eq]

/-- The token of a slot that is no quotation, no group and no boundary of a group. -/
def Slot.token? (slot : Option Part) : Option Token := slot.bind Part.token?

/-- The place of the first atom of a token. -/
def Token.anchor (token : Token) : Nat := (token.head?.map (·.anchor)).getD 0

/-- The place of the first atom of an item. -/
def Item.anchor : Item → Nat
  | .one token => Token.anchor token
  | .many first _ _ => Token.anchor first

/-- The place of the first atom of a slot. -/
def Slot.anchor : Option Part → Nat
  | some (.one item) => item.anchor
  | some (.many first _ _) => first.anchor
  | none => 0

/-- The place of the first word of a run. -/
def runAnchor (run : List (Option Part)) : Nat :=
  ((run.find? fun slot => decide (Slot.Word slot)).map Slot.anchor).getD 0

/-! ### C1 and C2: the length of a sentence -/

/-- The runs of `cut` with more than `limit` words. -/
def long (limit : Nat) (cut : Cut) : List Found :=
  (cut.filter fun run => limit < Controlled.wordCount run).map fun run =>
    ⟨runAnchor run, s!"a sentence of {Controlled.wordCount run} words; the maximum is {limit}"⟩

theorem long_nil_iff (limit : Nat) (cut : Cut) :
    long limit cut = [] ↔ ∀ run ∈ cut, wordCount run ≤ limit := by
  simp only [long, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq, Nat.not_lt]

/-- Check C1 (rule 6.3): the sentences of description blocks with more than 25 words. -/
@[regula_decision]
def longSentences : Reading → List Found :=
  perBlock fun b cut => if Block.Description b then long 25 cut else []

/-- A document conforms to C1 when it was read and each sentence of each description block has
25 words or less. -/
def ShortSentences : Reading → Prop :=
  EachBlock fun b cut => b.Description → ∀ run ∈ cut, wordCount run ≤ 25

theorem longSentences_nil_iff (reading : Reading) :
    longSentences reading = [] ↔ ShortSentences reading :=
  perBlock_nil_iff (fun b cut => by
    by_cases h : Block.Description b
    · simp [h, long_nil_iff]
    · simp [h]) reading

/-- Check C2 (rule 5.1): the sentences of procedure blocks with more than 20 words. -/
@[regula_decision]
def longSteps : Reading → List Found :=
  perBlock fun b cut => if Block.Procedure b then long 20 cut else []

/-- A document conforms to C2 when it was read and each sentence of each procedure block has
20 words or less. -/
def ShortSteps : Reading → Prop :=
  EachBlock fun b cut => b.Procedure → ∀ run ∈ cut, wordCount run ≤ 20

theorem longSteps_nil_iff (reading : Reading) : longSteps reading = [] ↔ ShortSteps reading :=
  perBlock_nil_iff (fun b cut => by
    by_cases h : Block.Procedure b
    · simp [h, long_nil_iff]
    · simp [h]) reading

/-! ### C3: the length of a paragraph -/

/-- The number of sentences of a block: its runs that have a word, in parentheses or not. -/
def sentenceCount (cut : Cut) : Nat := cut.countP fun run => decide (Controlled.Worded run)

/-- The place of the first sentence of a block. -/
def cutAnchor (cut : Cut) : Nat :=
  ((cut.find? fun run => decide (Controlled.Worded run)).map runAnchor).getD 0

/-- Check C3 (rule 6.6): the paragraphs with more than six sentences. -/
@[regula_decision]
def longParagraphs : Reading → List Found :=
  perBlock fun b cut =>
    if Block.Paragraph b ∧ 6 < sentenceCount cut then
      [⟨cutAnchor cut, s!"a paragraph of {sentenceCount cut} sentences; the maximum is 6"⟩]
    else []

/-- A document conforms to C3 when it was read and each paragraph has six sentences or less. A
sentence in parentheses is a sentence of its paragraph. -/
def ShortParagraphs : Reading → Prop :=
  EachBlock fun b cut => b.Paragraph → (cut.countP fun run => decide (Worded run)) ≤ 6

theorem longParagraphs_nil_iff (reading : Reading) :
    longParagraphs reading = [] ↔ ShortParagraphs reading :=
  perBlock_nil_iff (fun b cut => by
    show _ ↔ (b.Paragraph → sentenceCount cut ≤ 6)
    by_cases h : Block.Paragraph b
    · by_cases hcount : 6 < sentenceCount cut
      · simp [h, hcount]
      · simp [h, hcount, Nat.le_of_not_lt hcount]
    · simp [h]) reading

/-! ### C4: semicolons -/

/-- The semicolons of the prose of `pieces`, each with the place of its piece; `anchor` is the
number of located pieces before them. -/
def semicolonsFrom (anchor : Nat) : List Piece → List Found
  | [] => []
  | piece :: rest =>
    (match piece with
      | .text _ rendered =>
        (rendered.toList.filter (· == ';')).map fun _ => ⟨anchor, "a semicolon"⟩
      | _ => []) ++
      semicolonsFrom (if piece.located?.isSome then anchor + 1 else anchor) rest

/-- Check C4 (rule 8.1): the semicolons of the prose of a document. -/
@[regula_decision]
def semicolons : Reading → List Found
  | .unread reason => [⟨0, s!"the document was not read: {reason}"⟩]
  | .read pieces => semicolonsFrom 0 pieces

/-- A document conforms to C4 when it was read and no piece of its prose renders a
semicolon. -/
def NoSemicolon (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ slice rendered, Piece.text slice rendered ∈ pieces → ';' ∉ rendered.toList

theorem semicolonsFrom_nil_iff (pieces : List Piece) :
    ∀ anchor, semicolonsFrom anchor pieces = [] ↔
      ∀ slice rendered, Piece.text slice rendered ∈ pieces → ';' ∉ rendered.toList := by
  induction pieces with
  | nil => intro anchor; simp [semicolonsFrom]
  | cons piece rest ih =>
    intro anchor
    simp only [semicolonsFrom, List.append_eq_nil_iff, ih, List.mem_cons]
    cases piece with
    | text slice rendered =>
      simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, Piece.text.injEq, beq_iff_eq]
      constructor
      · rintro ⟨hhead, hrest⟩ s r (⟨_, rfl⟩ | hmem)
        · exact fun hmem => hhead _ hmem rfl
        · exact hrest s r hmem
      · intro h
        exact ⟨fun c hc e => h slice rendered (.inl ⟨rfl, rfl⟩) (e ▸ hc),
          fun s r hmem => h s r (.inr hmem)⟩
    | _ => simp

theorem semicolons_nil_iff (reading : Reading) : semicolons reading = [] ↔ NoSemicolon reading := by
  cases reading with
  | unread reason => simp [semicolons, NoSemicolon]
  | read pieces => simp [semicolons, NoSemicolon, semicolonsFrom_nil_iff]

/-! ### C5: contractions -/

/-- The form of a word for a comparison is a contraction: it ends with `n't`, `'re`, `'ve`,
`'ll`, `'d` or `'m`, or it is one of 11 words that end with `'s`. A possessive form is none. -/
def Contracted (word : List Char) : Prop :=
  (∃ ending ∈ ["n't", "'re", "'ve", "'ll", "'d", "'m"], ending.toList <:+ word) ∨
    ∃ fixed ∈ ["it's", "that's", "there's", "here's", "what's", "who's", "where's", "how's",
      "he's", "she's", "let's"], fixed.toList = word

instance : DecidablePred Contracted := fun word => by
  unfold Contracted
  infer_instance


/-- Check C5 (rule 4.2): the contractions of a document, outside quotations. -/
@[regula_decision]
def contractions : Reading → List Found :=
  perBlock fun _ cut => cut.flatMap fun run => run.filterMap fun slot =>
    match Slot.token? slot with
    | some token =>
      if Controlled.Contracted (normalize (token.filterMap (·.char))) then
        some ⟨Slot.anchor slot,
          s!"the contraction `{String.ofList (normalize (token.filterMap (·.char)))}`"⟩
      else none
    | none => none

/-- A document conforms to C5 when it was read and no token of a sentence has a form for a
comparison (`Normal`) that is a contraction. A quotation has no token: its text is not read. -/
def NoContraction : Reading → Prop :=
  EachBlock fun _ cut => ∀ run ∈ cut, ∀ slot ∈ run, ∀ token ∈ Slot.token? slot, ∀ letters,
    Normal (token.filterMap (·.char)) letters → ¬Contracted letters

theorem contractions_nil_iff (reading : Reading) :
    contractions reading = [] ↔ NoContraction reading :=
  perBlock_nil_iff (fun _ cut => by
    simp only [List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, normal_iff, forall_eq]
    refine forall₂_congr fun run _ => forall₂_congr fun slot _ => ?_
    cases Slot.token? slot with
    | none => simp
    | some token =>
      by_cases h : Controlled.Contracted (normalize (token.filterMap (·.char)))
      · simp [h]
      · simp [h]) reading

/-! ### Phrases at positions -/

/-- `phrase` is at the position `index` of `list`. -/
abbrev At {α : Type} [DecidableEq α] (phrase list : List α) (index : Nat) : Prop :=
  (list.drop index).take phrase.length = phrase

/-- The positions of `list` that have `P`. -/
def positions {α : Type} (list : List α) (P : Nat → Prop) [DecidablePred P] : List Nat :=
  (List.range list.length).filter fun index => decide (P index)

/-- No position has `P` exactly when no number has it, for a `P` that only positions have. -/
theorem positions_nil_iff {α : Type} (list : List α) (P : Nat → Prop) [DecidablePred P]
    (h : ∀ index, P index → index < list.length) :
    positions list P = [] ↔ ∀ index, ¬P index := by
  simp only [positions, List.filter_eq_nil_iff, List.mem_range, decide_eq_true_eq]
  exact ⟨fun hnone index hP => hnone index (h index hP) hP, fun hnone index _ => hnone index⟩

instance {α : Type} [DecidableEq α] (phrase list : List α) : DecidablePred (At phrase list) :=
  fun index => by
    unfold At
    infer_instance

/-- A phrase that is not empty is only at a position of the list. -/
theorem At.lt {α : Type} [DecidableEq α] {phrase list : List α} {index : Nat}
    (hne : phrase ≠ []) (h : At phrase list index) : index < list.length := by
  by_cases hlt : index < list.length
  · exact hlt
  · have : list.drop index = [] := List.drop_eq_nil_iff.mpr (Nat.le_of_not_lt hlt)
    simp only [At, this, List.take_nil] at h
    exact absurd h.symm hne

/-! ### C6 and C7: replaced names and replaced words -/

/-- `words` are the words of the phrase `text`: the text is the words with one space between two
words, and no word has a space. -/
def Words (text : List Char) (words : List (List Char)) : Prop :=
  ∃ first rest, words = first :: rest ∧ text = first ++ rest.flatMap (' ' :: ·) ∧
    ∀ word ∈ words, ' ' ∉ word

/-- The words of a phrase are those `split` gives. -/
theorem words_iff (text : List Char) (words : List (List Char)) :
    Words text words ↔ words = split ' ' text := by
  constructor
  · rintro ⟨first, rest, rfl, rfl, hwords⟩
    rw [split_joined ' ' first rest hwords]
  · rintro rfl
    obtain ⟨first, rest, hsplit, htext⟩ := joined_split ' ' text
    exact ⟨first, rest, hsplit, htext, not_mem_of_mem_split ' ' text⟩

/-- `mark` is what `slot` is for the comparison with the vocabulary. A token that has a letter,
a digit, code or a counted character outside ASCII gives the form of its characters for a
comparison (`Normal`). Each other token, each quotation, each group and each boundary of a group
gives `none`. -/
def Slot.Marked (slot : Option Part) (mark : Option (List Char)) : Prop :=
  (∃ token, Slot.token? slot = some token ∧ (∃ atom ∈ token, atom.role.Counted) ∧
      ∃ letters, Normal (token.filterMap (·.char)) letters ∧ mark = some letters) ∨
    ((∀ token, Slot.token? slot = some token → ¬∃ atom ∈ token, atom.role.Counted) ∧
      mark = none)

/-- The slot is a token of space characters only. -/
abbrev Slot.Blank (slot : Option Part) : Prop :=
  ∃ token ∈ Slot.token? slot, ∀ atom ∈ token, atom.role = .space

/-- `marks` are the marks of a run: what each slot that is not a token of space characters only
is for the comparison with the vocabulary (`Slot.Marked`), in order. Thus two words are next to
each other exactly when only space characters are between them. -/
def Marks (run : List (Option Part)) (marks : List (Option (List Char))) : Prop :=
  Paired Slot.Marked (run.filter fun slot => !decide (Slot.Blank slot)) marks

/-- The phrase of `length` words at `index` is a part of the longer `term`, which is at a
position where it has all the words of the phrase. -/
abbrev PartOf (term : List (List Char)) (length : Nat) (marks : List (Option (List Char)))
    (index : Nat) : Prop :=
  length < term.length ∧
    ∃ offset ∈ List.range (term.length - length + 1), offset ≤ index ∧
      At (term.map some) marks (index - offset)

/-- A run has no place where `phrase` is outside each longer term of `v`. -/
def Avoids (v : Vocabulary) (phrase : List (List Char)) (run : List (Option Part)) : Prop :=
  ∀ marks, Marks run marks → ∀ index, At (phrase.map some) marks index →
    ∃ t ∈ v.draft.rows, ∃ term, Words t.key term ∧ PartOf term phrase.length marks index

instance : DecidablePred Slot.Blank := fun slot => by
  unfold Slot.Blank
  infer_instance

instance (term : List (List Char)) (length : Nat) (marks : List (Option (List Char))) :
    DecidablePred (PartOf term length marks) := fun index => by
  unfold PartOf
  infer_instance

/-- What a slot is for the comparison with the vocabulary. -/
def markOf (slot : Option Part) : Option (List Char) :=
  match Slot.token? slot with
  | some token =>
    if ∃ atom ∈ token, Role.Counted (Atom.role atom) then
      some (normalize (token.filterMap (·.char)))
    else none
  | none => none

/-- What a slot is for the comparison with the vocabulary is one result only: the computed
one. -/
theorem marked_iff (slot : Option Part) (mark : Option (List Char)) :
    Slot.Marked slot mark ↔ mark = markOf slot := by
  have hmark : markOf slot =
      match Slot.token? slot with
      | some token =>
        if ∃ atom ∈ token, atom.role.Counted then some (normalize (token.filterMap (·.char)))
        else none
      | none => none := rfl
  rw [hmark, Slot.Marked]
  cases Slot.token? slot with
  | none => simp
  | some token =>
    dsimp only
    split
    · rename_i h
      constructor
      · rintro (⟨other, hother, -, letters, hletters, rfl⟩ | ⟨hnone, -⟩)
        · cases hother
          rw [(normal_iff _ _).mp hletters]
        · exact absurd h (hnone token rfl)
      · rintro rfl
        exact .inl ⟨token, rfl, h, _, (normal_iff _ _).mpr rfl, rfl⟩
    · rename_i h
      constructor
      · rintro (⟨other, hother, hcounted, -⟩ | ⟨-, rfl⟩)
        · cases hother
          exact absurd hcounted h
        · rfl
      · rintro rfl
        exact .inr ⟨fun other hother => by cases hother; exact h, rfl⟩

/-- The marks of a run. -/
def marks (run : List (Option Part)) : List (Option (List Char)) :=
  (run.filter fun slot => !decide (Slot.Blank slot)).map markOf

/-- The marks of a run are one list only: the computed one. -/
theorem marks_iff (run : List (Option Part)) (result : List (Option (List Char))) :
    Marks run result ↔ result = marks run :=
  paired_iff marked_iff _ _

/-- The positions of `marks` where `phrase` is and is not a part of a longer one of `terms`. -/
def offences (terms : List (List (List Char))) (phrase : List (List Char))
    (marks : List (Option (List Char))) : List Nat :=
  positions marks fun index =>
    Controlled.At (phrase.map some) marks index ∧
      ¬∃ term ∈ terms, Controlled.PartOf term phrase.length marks index

/-- The terms of a vocabulary, each as its words in lowercase. -/
def Vocabulary.terms (v : Vocabulary) : List (List (List Char)) :=
  (Draft.rows v.draft).map fun t => split ' ' (Term.key t)

theorem offences_nil_iff (v : Vocabulary) {phrase : List (List Char)} (hne : phrase ≠ [])
    (run : List (Option Part)) :
    offences v.terms phrase (marks run) = [] ↔ Avoids v phrase run := by
  rw [offences, positions_nil_iff _ _ fun index h =>
    At.lt (by simpa using hne) (show At (phrase.map some) (marks run) index from h.1)]
  show (∀ index, ¬(At (phrase.map some) (marks run) index ∧
    ¬∃ term ∈ (v.draft.rows.map fun t => split ' ' t.key),
      PartOf term phrase.length (marks run) index)) ↔ _
  simp only [Avoids, marks_iff, forall_eq]
  refine forall_congr' fun index => ?_
  simp only [not_and, Classical.not_not, List.mem_map, words_iff]
  constructor
  · rintro h hat
    obtain ⟨term, ⟨t, ht, rfl⟩, hcovers⟩ := h hat
    exact ⟨t, ht, _, rfl, hcovers⟩
  · rintro h hat
    obtain ⟨t, ht, term, rfl, hcovers⟩ := h hat
    exact ⟨_, ⟨t, ht, rfl⟩, hcovers⟩

/-- The findings of one phrase of the vocabulary in the runs of a block. -/
def phraseFindings (v : Vocabulary) (phrase : List (List Char)) (detail : String) (cut : Cut) :
    List Found :=
  cut.flatMap fun run => (offences v.terms phrase (marks run)).map fun index =>
    ⟨((((run.filter fun slot => !decide (Slot.Blank slot))[index]?).map Slot.anchor).getD 0),
      detail⟩

theorem phraseFindings_nil_iff (v : Vocabulary) {phrase : List (List Char)} (hne : phrase ≠ [])
    (detail : String) (cut : Cut) :
    phraseFindings v phrase detail cut = [] ↔ ∀ run ∈ cut, Avoids v phrase run := by
  simp only [phraseFindings, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
    offences_nil_iff v hne]

/-- Check C6 (rules 1.8 and 1.11): the replaced names of the vocabulary in a document, outside
quotations and outside each longer term of the vocabulary. -/
@[regula_decision]
def replacedNames (v : Vocabulary) : Reading → List Found :=
  perBlock fun _ cut => (Draft.rows v.draft).flatMap fun t => t.replaces.flatMap fun name =>
    phraseFindings v (split ' ' (Controlled.lower name))
      s!"`{String.ofList name}` is a replaced name; write: {String.ofList t.term}" cut

/-- A document conforms to C6 when it was read and no words of a sentence are a replaced name
of the vocabulary, unless they are a part of a longer term of the vocabulary. The comparison
ignores case. -/
def NoReplacedName (v : Vocabulary) : Reading → Prop :=
  EachBlock fun _ cut => ∀ t ∈ v.draft.rows, ∀ name ∈ t.replaces, ∀ words,
    Words (lower name) words → ∀ run ∈ cut, Avoids v words run

theorem replacedNames_nil_iff (v : Vocabulary) (reading : Reading) :
    replacedNames v reading = [] ↔ NoReplacedName v reading :=
  perBlock_nil_iff (fun _ cut => by
    simp only [List.flatMap_eq_nil_iff, words_iff, forall_eq]
    refine forall₂_congr fun t _ => forall₂_congr fun name _ => ?_
    exact phraseFindings_nil_iff v (split_ne_nil ' ' _) _ cut) reading

/-- Check C7 (a rule of the project): the words of the table `Replaced words` of the vocabulary
in a document, outside quotations and outside each term of the vocabulary. -/
@[regula_decision]
def replacedWords (v : Vocabulary) : Reading → List Found :=
  perBlock fun _ cut => v.draft.replaced.flatMap fun r =>
    phraseFindings v [Replaced.key r]
      s!"`{String.ofList r.word}` is a replaced word; write: {String.ofList r.write}" cut

/-- A document conforms to C7 when it was read and no word of a sentence is a replaced word of
the vocabulary, unless it is a part of a term of the vocabulary. The comparison ignores case. -/
def NoReplacedWord (v : Vocabulary) : Reading → Prop :=
  EachBlock fun _ cut => ∀ r ∈ v.draft.replaced, ∀ run ∈ cut, Avoids v [r.key] run

theorem replacedWords_nil_iff (v : Vocabulary) (reading : Reading) :
    replacedWords v reading = [] ↔ NoReplacedWord v reading :=
  perBlock_nil_iff (fun _ cut => by
    simp only [List.flatMap_eq_nil_iff]
    exact forall₂_congr fun r _ => phraseFindings_nil_iff v (by simp) _ cut) reading

/-! ### C8: abbreviations that end with a period -/

/-- `sign` is what `slot` is for check C8. A token gives the form for a comparison (`Normal`) of
its characters that are not space characters: thus a period and the space after it give a
period, and a word in apostrophes gives the word. A quotation, a group and a boundary of a group
give `none`. -/
def Slot.Signed (slot : Option Part) (sign : Option (List Char)) : Prop :=
  (∃ token, Slot.token? slot = some token ∧ ∃ letters,
      Normal ((token.filterMap (·.char)).filter fun c => !decide (Spacing c)) letters ∧
        sign = some letters) ∨
    (Slot.token? slot = none ∧ sign = none)

/-- The abbreviations that check C8 refuses, each as the signs of its tokens: `e.g.`, `i.e.`,
`etc.`, `vs.` and `cf.`. -/
def abbreviationSigns : List (String × List (Option (List Char))) :=
  [("e.g.", ["e", ".", "g", "."]), ("i.e.", ["i", ".", "e", "."]), ("etc.", ["etc", "."]),
    ("vs.", ["vs", "."]), ("cf.", ["cf", "."])].map fun (name, signs) =>
    (name, signs.map fun sign => some sign.toList)

/-- What a slot is for check C8. -/
def signOf (slot : Option Part) : Option (List Char) :=
  (Slot.token? slot).map fun token =>
    normalize ((token.filterMap (·.char)).filter fun c => !decide (Spacing c))

/-- What a slot is for check C8 is one result only: the computed one. -/
theorem signed_iff (slot : Option Part) (sign : Option (List Char)) :
    Slot.Signed slot sign ↔ sign = signOf slot := by
  have hsign : signOf slot = (Slot.token? slot).map fun token =>
      normalize ((token.filterMap (·.char)).filter fun c => !decide (Spacing c)) := rfl
  rw [hsign, Slot.Signed]
  cases Slot.token? slot with
  | none => simp
  | some token => simp [normal_iff]

/-- Check C8 (a rule of the project): the abbreviations `e.g.`, `i.e.`, `etc.`, `vs.` and `cf.`
of a document, outside quotations. -/
@[regula_decision]
def abbreviations : Reading → List Found :=
  perBlock fun _ cut => cut.flatMap fun run => abbreviationSigns.flatMap fun abbreviation =>
    (positions (run.map signOf) fun index =>
      Controlled.At abbreviation.2 (run.map signOf) index).map fun index =>
      ⟨((run[index]?).map Slot.anchor).getD 0, s!"the abbreviation `{abbreviation.1}`"⟩

/-- A document conforms to C8 when it was read and the tokens of no sentence are one of the five
abbreviations at a position, by what each slot is for the check (`Slot.Signed`). -/
def NoAbbreviation : Reading → Prop :=
  EachBlock fun _ cut => ∀ run ∈ cut, ∀ signs, Paired Slot.Signed run signs →
    ∀ abbreviation ∈ abbreviationSigns, ∀ index, ¬At abbreviation.2 signs index

theorem abbreviationSigns_ne_nil : ∀ abbreviation ∈ abbreviationSigns, abbreviation.2 ≠ [] := by
  decide

theorem abbreviations_nil_iff (reading : Reading) :
    abbreviations reading = [] ↔ NoAbbreviation reading :=
  perBlock_nil_iff (fun _ cut => by
    simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
      paired_iff signed_iff, forall_eq]
    refine forall₂_congr fun run _ => forall₂_congr fun abbreviation habbreviation => ?_
    exact positions_nil_iff _ _ fun index h =>
      At.lt (abbreviationSigns_ne_nil abbreviation habbreviation)
        (show At abbreviation.2 (run.map signOf) index from h)) reading

/-! ## The registered contracts of C1 to C8 -/

/-- A reading of one paragraph whose text is `text`. -/
def paragraphOf (text : String) : Reading := .read [.start .paragraph, .text text text]

/-- Registered contract of check C1, as a two-way decision: it reports nothing exactly when the
document was read and each sentence of each description block has 25 words or less. It accepts a
document with no piece and refuses a paragraph that is one sentence of 26 words. -/
theorem checked_longSentences : Regula.ExecutableContract longSentences
    (Regula.Decides (· = []) ShortSentences) :=
  ⟨.of_iff longSentences_nil_iff ⟨.read [], by decide⟩
    ⟨paragraphOf "A a a a a a a a a a a a a a a a a a a a a a a a a a.", by decide⟩⟩

/-- Registered contract of check C2, as a two-way decision: it reports nothing exactly when the
document was read and each sentence of each procedure block has 20 words or less. It accepts a
document with no piece and refuses a paragraph of an ordered list item that is one sentence of
21 words. -/
theorem checked_longSteps : Regula.ExecutableContract longSteps
    (Regula.Decides (· = []) ShortSteps) :=
  ⟨.of_iff longSteps_nil_iff ⟨.read [], by decide⟩
    ⟨.read [.start .step, .text "" "A a a a a a a a a a a a a a a a a a a a a."], by decide⟩⟩

/-- Registered contract of check C3, as a two-way decision: it reports nothing exactly when the
document was read and each paragraph has six sentences or less, in parentheses or not. It
accepts a document with no piece and refuses a paragraph of one sentence with seven sentences
in parentheses. -/
theorem checked_longParagraphs : Regula.ExecutableContract longParagraphs
    (Regula.Decides (· = []) ShortParagraphs) :=
  ⟨.of_iff longParagraphs_nil_iff ⟨.read [], by decide⟩
    ⟨paragraphOf "One (A. B. C. D. E. F. G.) ends.", by decide⟩⟩

/-- Registered contract of check C4, as a two-way decision: it reports nothing exactly when the
document was read and no piece of its prose renders a semicolon. It accepts a document with no
piece and refuses a paragraph with a semicolon. -/
theorem checked_semicolons : Regula.ExecutableContract semicolons
    (Regula.Decides (· = []) NoSemicolon) :=
  ⟨.of_iff semicolons_nil_iff ⟨.read [], by decide⟩ ⟨paragraphOf "a; b", by decide⟩⟩

/-- Registered contract of check C5, as a two-way decision: it reports nothing exactly when the
document was read and no token of a sentence is a contraction. It accepts a document with no
piece and refuses a paragraph with `don't`. -/
theorem checked_contractions : Regula.ExecutableContract contractions
    (Regula.Decides (· = []) NoContraction) :=
  ⟨.of_iff contractions_nil_iff ⟨.read [], by decide⟩ ⟨paragraphOf "don't", by decide⟩⟩

/-- A vocabulary with one term, `b`, which replaces the name `a`, and the replaced word `c`. -/
def Vocabulary.pair : Vocabulary :=
  ⟨⟨['1'], none, [], [], [⟨['b'], ['1'], ['B', '.'], [['a']], ['b'], none⟩], [],
    [⟨['c'], ['d']⟩]⟩, (Draft.defects_nil_iff _).mp (by decide)⟩

/-- Registered contract of check C6, as a two-way decision over the vocabulary and the reading:
it reports nothing exactly when the document was read and no replaced name of the vocabulary
is in a sentence outside a longer term. It accepts a document with no piece and refuses a
paragraph with a replaced name. -/
theorem checked_replacedNames : Regula.ExecutableContract replacedNames (fun run =>
    Regula.Decides (· = [])
      (fun input : Vocabulary × Reading => NoReplacedName input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => replacedNames_nil_iff input.1 input.2)
    ⟨(Vocabulary.pair, .read []), by decide⟩
    ⟨(Vocabulary.pair, paragraphOf "an a here"), by decide⟩⟩

/-- Registered contract of check C7, as a two-way decision over the vocabulary and the reading:
it reports nothing exactly when the document was read and no replaced word of the vocabulary is
in a sentence outside a term. It accepts a document with no piece and refuses a paragraph with a
replaced word. -/
theorem checked_replacedWords : Regula.ExecutableContract replacedWords (fun run =>
    Regula.Decides (· = [])
      (fun input : Vocabulary × Reading => NoReplacedWord input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => replacedWords_nil_iff input.1 input.2)
    ⟨(Vocabulary.pair, .read []), by decide⟩
    ⟨(Vocabulary.pair, paragraphOf "a c here"), by decide⟩⟩

/-- Registered contract of check C8, as a two-way decision: it reports nothing exactly when the
document was read and no sentence has one of the five abbreviations. It accepts a document with
no piece and refuses a paragraph with `e.g.`. -/
theorem checked_abbreviations : Regula.ExecutableContract abbreviations
    (Regula.Decides (· = []) NoAbbreviation) :=
  ⟨.of_iff abbreviations_nil_iff ⟨.read [], by decide⟩ ⟨paragraphOf "see e.g. this", by decide⟩⟩

/-! ## The tally of a document -/

/-- The eight checks of a document's prose. -/
inductive Check where
  /-- The length of a sentence of a description. -/
  | c1
  /-- The length of a sentence of a procedure. -/
  | c2
  /-- The length of a paragraph. -/
  | c3
  /-- Semicolons. -/
  | c4
  /-- Contractions. -/
  | c5
  /-- Replaced names. -/
  | c6
  /-- Replaced words. -/
  | c7
  /-- Abbreviations that end with a period. -/
  | c8
  deriving DecidableEq, Repr

/-- The eight checks, in order. -/
def Check.all : List Check := [.c1, .c2, .c3, .c4, .c5, .c6, .c7, .c8]

/-- The name of a check in messages and in the baseline. -/
def Check.name : Check → String
  | .c1 => "C1" | .c2 => "C2" | .c3 => "C3" | .c4 => "C4"
  | .c5 => "C5" | .c6 => "C6" | .c7 => "C7" | .c8 => "C8"

/-- The findings of `check` in a document, for the vocabulary `v`. -/
def findings (v : Vocabulary) : Check → Reading → List Found
  | .c1 => longSentences
  | .c2 => longSteps
  | .c3 => longParagraphs
  | .c4 => semicolons
  | .c5 => contractions
  | .c6 => replacedNames v
  | .c7 => replacedWords v
  | .c8 => abbreviations

/-- The number of findings of each check in a document, in the order of `Check.all`. -/
def tally (v : Vocabulary) (reading : Reading) : List Nat :=
  Check.all.map fun check => (findings v check reading).length

/-- A document has no finding of any check exactly when it conforms to all eight. -/
theorem tally_zero_iff (v : Vocabulary) (reading : Reading) :
    (∀ n ∈ tally v reading, n = 0) ↔
      ShortSentences reading ∧ ShortSteps reading ∧ ShortParagraphs reading ∧
        NoSemicolon reading ∧ NoContraction reading ∧ NoReplacedName v reading ∧
        NoReplacedWord v reading ∧ NoAbbreviation reading := by
  simp only [tally, Check.all, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, findings, List.length_eq_zero_iff,
    longSentences_nil_iff, longSteps_nil_iff, longParagraphs_nil_iff, semicolons_nil_iff,
    contractions_nil_iff, replacedNames_nil_iff, replacedWords_nil_iff, abbreviations_nil_iff]

/-! ## Where a finding is -/

/-- For each place of `pieces`, the first and the last line of `source` that the piece there can
lie on (`Regula.Markdown.leftmost`, `Regula.Markdown.rightmost`); the whole document when the
pieces have no placement. -/
def brackets (source : String) (pieces : List Piece) : Nat → Nat × Nat :=
  let lines := source.splitOn "\n"
  let located := Markdown.anchors false pieces
  let first := (Markdown.leftmost Markdown.occursOn 1 located lines).getD []
  let last := (Markdown.rightmost Markdown.occursOn 1 lines located).getD []
  fun anchor => (first[anchor]?.getD 1, last[anchor]?.getD lines.length)

/-- What a finding of `check` reports: the file, the line or the first and last line it can lie
on, the check and what was found. -/
def Found.describe (file : String) (bracket : Nat → Nat × Nat) (check : Check) (found : Found) :
    String :=
  let (first, last) := bracket found.anchor
  s!"{file}:{first}" ++ (if first == last then "" else s!"-{last}") ++
    s!": {check.name}: {found.detail}"

/-- The findings of all checks in the document `file` with text `source`, each with its line.
The lines are found only for a document that has a finding. -/
def report (v : Vocabulary) (file source : String) (reading : Reading) : List String :=
  let found := Check.all.map fun check => (check, findings v check reading)
  if found.all (·.2.isEmpty) then []
  else
    let bracket : Nat → Nat × Nat :=
      match reading with
      | .read pieces => brackets source pieces
      | .unread _ => fun _ => (1, 1)
    found.flatMap fun (check, list) => list.map (Found.describe file bracket check)

end Regula.Controlled
