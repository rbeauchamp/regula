import RegulaCore.Markdown
import RegulaCore.Vocabulary

/-! # Exact checks of the prose of Markdown documents

The writing guide (`docs/guides/writing.md`) gives the rules for new and changed documents of a
repository. This module decides the rules that a text decides alone, from what a CommonMark
parser reports of a document (`Regula.Markdown.Reading`) and from the vocabulary of the project
(`Regula.Controlled.Vocabulary`). It is a check of a repository's own documents, as the rule-ID
check of `RegulaCore.Markdown` is. It is not a rule of Regula's standard and has no rule ID.

## Main declarations

- `Block`, `blocks`: the blocks of a document and the characters of each one.
- `quote`, `balance`, `Block.tokens`: the tokens of a block, where a quotation is one unit and
  each parenthesis has its partner.
- `Sentence`, `sentences`: the sentences of a block, each with its number of words.
- `longSentences` (C1), `longSteps` (C2), `longParagraphs` (C3), `semicolons` (C4),
  `contractions` (C5), `replacedNames` (C6), `replacedWords` (C7) and `abbreviations` (C8): the
  findings of each check, with a registered two-way contract for each (`checked_longSentences`
  and the others).
- `Check`, `findings`, `tally`, `tally_zero_iff`: the number of findings of each check in a
  document, which is zero for each check exactly when the document conforms to all eight.
- `Ledger`, `Baseline`, `Baseline.write`, `Baseline.parse`, `checked_baselineParse`: the baseline
  file, with the same construction as the vocabulary: one text for each baseline.
- `gate`, `checked_gate`: a repository is accepted when each document has the findings its
  baseline entry permits.
- `ratchet`, `checked_ratchet`: a baseline is accepted in relation to an earlier one when it has
  no new path and no larger number.

## What a check reads

A block is a heading, a paragraph, a paragraph of a list item, or a table cell, as the parser
reports it (`Regula.Markdown.Kind`). A code block is a block with no prose. The text of a block
is its prose in order, with one space for each line boundary and each edge of a table cell or of
an image's description. The description of an image is thus prose of its block. A code span is
one unit.

A word is defined in `RegulaCore.Vocabulary` (`Lexeme.word`). Text between two double quotation
marks in one block is one unit (`quote`). An opening parenthesis and the closing parenthesis
that ends it enclose a group (`balance`), which is one word of the sentence around it and whose
text has sentences of its own.

A sentence ends at a period, a question mark or an exclamation mark that is followed by a space
and then by a word that starts with an ASCII uppercase letter or a digit, by a unit or by an
opening parenthesis. It also ends at the end of its block and at the closing parenthesis of its
group. A sentence does not continue into the next block, so the text before a list and each list
item are counted apart.

## Boundaries

Each contract is about the reading it is given. That the reading is the document's rests on the
parser and on the translation of its parse into pieces (`markdown/RegulaMarkdown.lean`), which
has no theorem. No contract says that a sentence here is a sentence for a reader: an abbreviation
that ends with a period before an uppercase word ends a sentence here. `tally_zero_iff` and
`checked_gate` are about the tallies and digests given: that a digest is the SHA-256 of a file
rests on the tool that computes it, and that the documents given are the tracked ones rests on
Git.
-/

namespace Regula.Controlled

open Regula.Markdown (Kind Piece Reading)

/-! ## Blocks -/

/-- One block of a document: its kind and its characters and code pieces, in order. -/
structure Block where
  /-- The kind of the block. -/
  kind : Kind
  /-- The characters of the block's prose and its code pieces. -/
  atoms : List Atom
  deriving DecidableEq, Repr

/-- The state of the division of a document's pieces into blocks. -/
structure Reader where
  /-- The number of located pieces read so far. -/
  anchor : Nat := 0
  /-- The kind of the block in progress. Pieces before the first start are a paragraph. -/
  kind : Kind := .paragraph
  /-- The atoms of the block in progress, last first. -/
  atoms : List Atom := []
  /-- The blocks read so far, last first. -/
  blocks : List Block := []

/-- End the block in progress and keep it, unless it has no atom. -/
def Reader.close (r : Reader) : Reader :=
  if r.atoms.isEmpty then r
  else { r with atoms := [], blocks := ⟨r.kind, r.atoms.reverse⟩ :: r.blocks }

/-- The reader after a piece with source text `slice`. -/
def Reader.past (r : Reader) (slice : String) : Reader :=
  if Markdown.blank slice then r else { r with anchor := r.anchor + 1 }

/-- Read one piece. A start ends the block in progress. Prose gives its rendered characters,
code one atom, and a line boundary or the edge of a table cell or of an image's description one
space. The edges of links and the refused constructs give nothing. -/
def Reader.step (r : Reader) : Piece → Reader
  | .start kind => { r.close with kind := kind }
  | .text slice rendered =>
    Reader.past { r with
      atoms := (rendered.toList.map fun c => (⟨r.anchor, some c⟩ : Atom)).reverse ++ r.atoms }
      slice
  | .code slice => Reader.past { r with atoms := ⟨r.anchor, none⟩ :: r.atoms } slice
  | .gap | .line => { r with atoms := ⟨r.anchor, some ' '⟩ :: r.atoms }
  | .enter _ | .leave | .refused _ => r

/-- The blocks of a document, in order. -/
def blocks (pieces : List Piece) : List Block :=
  (pieces.foldl Reader.step {}).close.blocks.reverse

/-! ## Quotations and parentheses -/

/-- Whether `tokens` hold a mark that ends a quotation: `"` or `”`. -/
def closes (tokens : List Token) : Bool :=
  tokens.any fun token => token.lexeme == .quote '"' || token.lexeme == .quote '”'

/-- `tokens` with each quotation as one unit: the text from a `"` or a `“` to the next `"` or
`”` of the block. `inside` is whether a quotation is in progress. A quotation mark that starts
no quotation is a mark. -/
def quote : Bool → List Token → List Token
  | _, [] => []
  | false, token :: rest =>
    match token.lexeme with
    | .quote c =>
      if c != '”' && closes rest then ⟨token.anchor, .unit⟩ :: quote true rest
      else ⟨token.anchor, .mark c⟩ :: quote false rest
    | _ => token :: quote false rest
  | true, token :: rest =>
    match token.lexeme with
    | .quote c => if c != '“' then quote false rest else quote true rest
    | _ => quote true rest

/-- `tokens` with each closing parenthesis that no opening parenthesis is before as a mark;
`depth` is the number of opening parentheses not yet closed. -/
def dropClosings (depth : Nat) : List Token → List Token
  | [] => []
  | token :: rest =>
    match token.lexeme with
    | .opening => token :: dropClosings (depth + 1) rest
    | .closing =>
      if depth = 0 then ⟨token.anchor, .mark ')'⟩ :: dropClosings 0 rest
      else token :: dropClosings (depth - 1) rest
    | _ => token :: dropClosings depth rest

/-- `tokens` with each opening parenthesis that no closing parenthesis is after as a mark, and
the number of closing parentheses of the result that no opening one of it is before. -/
def dropOpenings : List Token → List Token × Nat
  | [] => ([], 0)
  | token :: rest =>
    match token.lexeme with
    | .closing => (token :: (dropOpenings rest).1, (dropOpenings rest).2 + 1)
    | .opening =>
      if (dropOpenings rest).2 = 0 then (⟨token.anchor, .mark '('⟩ :: (dropOpenings rest).1, 0)
      else (token :: (dropOpenings rest).1, (dropOpenings rest).2 - 1)
    | _ => (token :: (dropOpenings rest).1, (dropOpenings rest).2)

/-- `tokens` with each parenthesis that has no partner in the block as a mark. -/
def balance (tokens : List Token) : List Token := (dropOpenings (dropClosings 0 tokens)).1

/-- The tokens of a block: quotations are units, and each parenthesis has its partner. -/
def Block.tokens (b : Block) : List Token := balance (quote false (lex b.atoms))

/-! ## Sentences -/

/-- One sentence of a block. -/
structure Sentence where
  /-- The place of the piece its first word is in. -/
  anchor : Nat
  /-- Its number of words: each word, each unit and each group in parentheses is one. -/
  words : Nat
  /-- Whether it is in parentheses. -/
  nested : Bool
  deriving DecidableEq, Repr

/-- Whether a token can start a sentence after a period: a word that starts with an ASCII
uppercase letter or a digit, a unit, or an opening parenthesis. -/
def starter : Lexeme → Bool
  | .word (c :: _) => c.isUpper || c.isDigit
  | .unit | .opening => true
  | _ => false

/-- Whether the tokens after a period, a question mark or an exclamation mark show that it ends
a sentence: they are none, or a space and then nothing or a `starter`. -/
def boundary : List Token → Bool
  | [] => true
  | [token] => token.lexeme == .space
  | token :: next :: _ => token.lexeme == .space && starter next.lexeme

/-- The sentence in progress with one more word; `current` is its place and its number of
words. -/
def bump (anchor : Nat) (current : Nat × Nat) : Nat × Nat :=
  if current.2 = 0 then (anchor, 1) else (current.1, current.2 + 1)

/-- The sentence in progress as a sentence, unless it has no word. -/
def emit (current : Nat × Nat) (nested : Bool) : List Sentence :=
  if current.2 = 0 then [] else [⟨current.1, current.2, nested⟩]

/-- The sentences in progress at the end of the tokens: the current one and those around its
parentheses, the innermost first. -/
def emitAll (current : Nat × Nat) : List (Nat × Nat) → List Sentence
  | [] => emit current false
  | frame :: outer => emit current true ++ emitAll frame outer

/-- The sentences of `tokens`, read after the sentence in progress `current` inside the
sentences in progress `outer`, the innermost first. -/
def sentencesFrom (current : Nat × Nat) (outer : List (Nat × Nat)) : List Token → List Sentence
  | [] => emitAll current outer
  | token :: rest =>
    match token.lexeme with
    | .word _ | .unit => sentencesFrom (bump token.anchor current) outer rest
    | .opening => sentencesFrom (0, 0) (bump token.anchor current :: outer) rest
    | .closing =>
      match outer with
      | [] => sentencesFrom current [] rest
      | frame :: outer => emit current true ++ sentencesFrom frame outer rest
    | .stop _ =>
      if boundary rest then emit current (!outer.isEmpty) ++ sentencesFrom (0, 0) outer rest
      else sentencesFrom current outer rest
    | _ => sentencesFrom current outer rest

/-- The sentences of `tokens`, each when it ends: a sentence in parentheses before the rest of
the sentence around it. -/
def sentences (tokens : List Token) : List Sentence := sentencesFrom (0, 0) [] tokens

/-- Whether `tokens` start with `WARNING:` or `CAUTION:`, in uppercase. -/
def signal : List Token → Bool
  | ⟨_, .word word⟩ :: ⟨_, .mark c⟩ :: _ =>
    c == ':' && (word == "WARNING".toList || word == "CAUTION".toList)
  | ⟨_, .space⟩ :: ⟨_, .word word⟩ :: ⟨_, .mark c⟩ :: _ =>
    c == ':' && (word == "WARNING".toList || word == "CAUTION".toList)
  | _ => false

/-- Whether `b` is a paragraph, a paragraph of an unordered list item or a table cell. -/
def Block.plain (b : Block) : Bool :=
  b.kind == .paragraph || b.kind == .bullet || b.kind == .cell

/-- Whether `b` is a procedure block: a paragraph of an ordered list item, or a paragraph, a
paragraph of an unordered list item or a table cell that starts with `WARNING:` or
`CAUTION:`. -/
def Block.procedure (b : Block) : Bool := b.kind == .step || (b.plain && signal b.tokens)

/-- Whether `b` is a description block: a paragraph, a paragraph of an unordered list item or a
table cell that does not start with `WARNING:` or `CAUTION:`. -/
def Block.description (b : Block) : Bool := b.plain && !signal b.tokens

/-- Whether the parser reports `b` as a paragraph, in a list item or not. -/
def Block.paragraph (b : Block) : Bool :=
  b.kind == .paragraph || b.kind == .step || b.kind == .bullet

/-! ## Findings -/

/-- One finding of a check. -/
structure Found where
  /-- The place of the piece it is in. -/
  anchor : Nat
  /-- What was found. -/
  detail : String
  deriving DecidableEq, Repr

/-- The findings of the blocks of a document, block by block; one finding for a document whose
reading cannot be used. -/
def perBlock (find : Block → List Found) : Reading → List Found
  | .unread reason => [⟨0, s!"the document was not read: {reason}"⟩]
  | .read pieces => (blocks pieces).flatMap find

theorem perBlock_nil_iff (find : Block → List Found) (reading : Reading) :
    perBlock find reading = [] ↔
      ∃ pieces, reading = .read pieces ∧ ∀ b ∈ blocks pieces, find b = [] := by
  cases reading with
  | unread reason => simp [perBlock]
  | read pieces => simp [perBlock, List.flatMap_eq_nil_iff]

/-- The sentences of `b` with more than `limit` words. -/
def Block.long (limit : Nat) (b : Block) : List Found :=
  ((sentences b.tokens).filter fun s => limit < s.words).map fun s =>
    ⟨s.anchor, s!"a sentence of {s.words} words; the maximum is {limit}"⟩

theorem Block.long_nil_iff (limit : Nat) (b : Block) :
    b.long limit = [] ↔ ∀ s ∈ sentences b.tokens, s.words ≤ limit := by
  simp [Block.long, List.filter_eq_nil_iff, Nat.not_lt]

/-! ### C1 and C2: the length of a sentence -/

/-- Check C1 (rule 6.3): the sentences of description blocks with more than 25 words. -/
@[regula_decision]
def longSentences : Reading → List Found :=
  perBlock fun b => if b.description then b.long 25 else []

/-- A document conforms to C1 when it was read and each sentence of each description block has
25 words or less. -/
def ShortSentences (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ b ∈ blocks pieces, b.description = true → ∀ s ∈ sentences b.tokens, s.words ≤ 25

theorem longSentences_nil_iff (reading : Reading) :
    longSentences reading = [] ↔ ShortSentences reading := by
  rw [longSentences, perBlock_nil_iff]
  refine exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ => ?_
  by_cases h : b.description = true <;> simp [h, Block.long_nil_iff]

/-- Check C2 (rule 5.1): the sentences of procedure blocks with more than 20 words. -/
@[regula_decision]
def longSteps : Reading → List Found :=
  perBlock fun b => if b.procedure then b.long 20 else []

/-- A document conforms to C2 when it was read and each sentence of each procedure block has
20 words or less. -/
def ShortSteps (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ b ∈ blocks pieces, b.procedure = true → ∀ s ∈ sentences b.tokens, s.words ≤ 20

theorem longSteps_nil_iff (reading : Reading) : longSteps reading = [] ↔ ShortSteps reading := by
  rw [longSteps, perBlock_nil_iff]
  refine exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ => ?_
  by_cases h : b.procedure = true <;> simp [h, Block.long_nil_iff]

/-! ### C3: the length of a paragraph -/

/-- The sentences of `b` that are not in parentheses. -/
def Block.top (b : Block) : List Sentence := (sentences b.tokens).filter fun s => !s.nested

/-- Check C3 (rule 6.6): the paragraphs with more than six sentences outside parentheses. -/
@[regula_decision]
def longParagraphs : Reading → List Found :=
  perBlock fun b =>
    if b.paragraph && 6 < b.top.length then
      [⟨(b.top.head?.map (·.anchor)).getD 0,
        s!"a paragraph of {b.top.length} sentences; the maximum is 6"⟩]
    else []

/-- A document conforms to C3 when it was read and each paragraph has six sentences or less
outside parentheses. -/
def ShortParagraphs (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ b ∈ blocks pieces, b.paragraph = true → b.top.length ≤ 6

theorem longParagraphs_nil_iff (reading : Reading) :
    longParagraphs reading = [] ↔ ShortParagraphs reading := by
  rw [longParagraphs, perBlock_nil_iff]
  refine exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ => ?_
  by_cases h : b.paragraph = true <;> by_cases hlength : 6 < b.top.length <;>
    simp [h, hlength] <;> omega

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

/-- Whether the lowercase word `word` is a contraction: it ends with `n't`, `'re`, `'ve`, `'ll`,
`'d` or `'m`, or it is one of 11 words that end with `'s`. A possessive form is none. -/
def contracted (word : List Char) : Bool :=
  (["n't", "'re", "'ve", "'ll", "'d", "'m"].any fun suffix => suffix.toList.isSuffixOf word) ||
    ["it's", "that's", "there's", "here's", "what's", "who's", "where's", "how's", "he's",
      "she's", "let's"].any fun fixed => fixed.toList == word

/-- The word of a token, if it is a word. -/
def Token.word? (token : Token) : Option (List Char) :=
  match token.lexeme with
  | .word text => some text
  | _ => none

/-- The contractions among the words of `b` outside quotations. -/
def Block.contractions (b : Block) : List Found :=
  b.tokens.filterMap fun token =>
    match token.word? with
    | some text =>
      if contracted (lower text) then
        some ⟨token.anchor, s!"the contraction `{String.ofList text}`"⟩
      else none
    | none => none

/-- Check C5 (rule 4.2): the contractions of a document. -/
@[regula_decision]
def contractions : Reading → List Found := perBlock Block.contractions

/-- A document conforms to C5 when it was read and no word of a block outside quotations is a
contraction. -/
def NoContraction (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ b ∈ blocks pieces, ∀ token ∈ b.tokens, ∀ text, token.word? = some text →
      contracted (lower text) = false

theorem contractions_nil_iff (reading : Reading) :
    contractions reading = [] ↔ NoContraction reading := by
  rw [contractions, perBlock_nil_iff]
  refine exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ => ?_
  simp only [Block.contractions, List.filterMap_eq_nil_iff]
  refine forall₂_congr fun token _ => ?_
  cases hword : token.word? with
  | none => simp
  | some text => by_cases h : contracted (lower text) = true <;> simp [h]

/-! ### C6 and C7: replaced names and replaced words -/

/-- The runs of words of `tokens`, read after the run in progress `current`, whose words are
last first. -/
def runsFrom (current : List (Nat × List Char)) : List Token → List (List (Nat × List Char))
  | [] => if current.isEmpty then [] else [current.reverse]
  | token :: rest =>
    match token.lexeme with
    | .word text => runsFrom ((token.anchor, lower text) :: current) rest
    | .space =>
      match rest with
      | next :: _ =>
        if next.word?.isSome then runsFrom current rest
        else (if current.isEmpty then [] else [current.reverse]) ++ runsFrom [] rest
      | [] => if current.isEmpty then [] else [current.reverse]
    | _ => (if current.isEmpty then [] else [current.reverse]) ++ runsFrom [] rest

/-- The runs of words of `tokens`: each maximal sequence of words with one space between them,
each word in lowercase with the place of its piece. -/
def runs (tokens : List Token) : List (List (Nat × List Char)) := runsFrom [] tokens

/-- Whether the words of `phrase`, which is not empty, are the words of `run` from position
`index` on. -/
def occurs (phrase run : List (List Char)) (index : Nat) : Bool :=
  !phrase.isEmpty && phrase.isPrefixOf (run.drop index)

/-- Whether the `length` words of `run` from position `index` on are inside a longer term of
`terms` in `run`. -/
def excused (terms : List (List (List Char))) (run : List (List Char)) (index length : Nat) :
    Bool :=
  terms.any fun term =>
    length < term.length && (List.range (index + 1)).any fun start =>
      occurs term run start && index + length ≤ start + term.length

/-- The occurrences in `b` of the phrases `entries` that are not inside a longer term of
`terms`, each reported with `describe`. -/
def Block.phrases {α : Type} (terms : List (List (List Char)))
    (entries : List (List (List Char) × α)) (describe : List (List Char) × α → String)
    (b : Block) : List Found :=
  (runs b.tokens).flatMap fun run =>
    (List.range run.length).flatMap fun index =>
      entries.filterMap fun entry =>
        if occurs entry.1 (run.map (·.2)) index &&
            !excused terms (run.map (·.2)) index entry.1.length then
          some ⟨(run[index]?.map (·.1)).getD 0, describe entry⟩
        else none

/-- No phrase of `entries` occurs in `b` outside a longer term of `terms`. -/
def Block.Avoids {α : Type} (terms : List (List (List Char)))
    (entries : List (List (List Char) × α)) (b : Block) : Prop :=
  ∀ run ∈ runs b.tokens, ∀ index < run.length, ∀ entry ∈ entries,
    occurs entry.1 (run.map (·.2)) index = true →
      excused terms (run.map (·.2)) index entry.1.length = true

theorem Block.phrases_nil_iff {α : Type} (terms : List (List (List Char)))
    (entries : List (List (List Char) × α)) (describe : List (List Char) × α → String)
    (b : Block) : b.phrases terms entries describe = [] ↔ b.Avoids terms entries := by
  simp only [Block.phrases, List.flatMap_eq_nil_iff, List.filterMap_eq_nil_iff, List.mem_range,
    Block.Avoids]
  refine forall₂_congr fun run _ => forall₂_congr fun index _ => forall₂_congr fun entry _ => ?_
  by_cases hoccurs : occurs entry.1 (run.map (·.2)) index = true <;>
    by_cases hexcused : excused terms (run.map (·.2)) index entry.1.length = true <;>
    simp [hoccurs, hexcused]

/-- Check C6 (rules 1.8 and 1.11): the replaced names of `v` in a document, outside a longer
term of `v`. The comparison is of lowercase words. -/
@[regula_decision]
def replacedNames (v : Vocabulary) : Reading → List Found :=
  perBlock (Block.phrases v.terms v.names fun entry =>
    s!"`{String.ofList ([' '].intercalate entry.1)}` is a replaced name; write \
      `{String.ofList entry.2}`")

/-- A document conforms to C6 for `v` when it was read and no replaced name of `v` occurs in a
run of its words outside a longer term of `v`. -/
def NoReplacedName (v : Vocabulary) (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧ ∀ b ∈ blocks pieces, b.Avoids v.terms v.names

theorem replacedNames_nil_iff (v : Vocabulary) (reading : Reading) :
    replacedNames v reading = [] ↔ NoReplacedName v reading := by
  rw [replacedNames, perBlock_nil_iff]
  exact exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ =>
    Block.phrases_nil_iff ..

/-- The replaced words of `v`, each as a phrase of one word, with what to write. -/
def Vocabulary.wordPhrases (v : Vocabulary) : List (List (List Char) × List Char) :=
  v.replaced.map fun entry => ([entry.1], entry.2)

/-- Check C7 (a rule of the project): the replaced words of `v` in a document, outside a longer
term of `v`. The comparison is of lowercase words. -/
@[regula_decision]
def replacedWords (v : Vocabulary) : Reading → List Found :=
  perBlock (Block.phrases v.terms v.wordPhrases fun entry =>
    s!"`{String.ofList ([' '].intercalate entry.1)}` is a replaced word; write: \
      {String.ofList entry.2}")

/-- A document conforms to C7 for `v` when it was read and no replaced word of `v` occurs in a
run of its words outside a longer term of `v`. -/
def NoReplacedWord (v : Vocabulary) (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧ ∀ b ∈ blocks pieces, b.Avoids v.terms v.wordPhrases

theorem replacedWords_nil_iff (v : Vocabulary) (reading : Reading) :
    replacedWords v reading = [] ↔ NoReplacedWord v reading := by
  rw [replacedWords, perBlock_nil_iff]
  exact exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ =>
    Block.phrases_nil_iff ..

/-! ### C8: abbreviations that end with a period -/

/-- The abbreviation `tokens` start with, if they start with one of `e.g.`, `i.e.`, `etc.`,
`vs.` and `cf.`, in any case. -/
def abbreviation : List Token → Option String
  | ⟨_, .word first⟩ :: ⟨_, .stop c⟩ :: rest =>
    if c == '.' && (["etc", "vs", "cf"].any fun fixed => fixed.toList == lower first) then
      some (String.ofList first ++ ".")
    else
      match rest with
      | ⟨_, .word second⟩ :: ⟨_, .stop d⟩ :: _ =>
        if c == '.' && d == '.' &&
            ((lower first == ['e'] && lower second == ['g']) ||
              (lower first == ['i'] && lower second == ['e'])) then
          some (String.ofList first ++ "." ++ String.ofList second ++ ".")
        else none
      | _ => none
  | _ => none

/-- The abbreviations of `tokens`, each with the place of its first word. -/
def abbreviationsIn : List Token → List Found
  | [] => []
  | token :: rest =>
    (match abbreviation (token :: rest) with
      | some text => [⟨token.anchor, s!"the abbreviation `{text}`"⟩]
      | none => []) ++ abbreviationsIn rest

theorem abbreviationsIn_nil_iff (tokens : List Token) :
    abbreviationsIn tokens = [] ↔ ∀ suffix, suffix <:+ tokens → abbreviation suffix = none := by
  induction tokens with
  | nil =>
    simp only [abbreviationsIn, List.suffix_nil, true_iff]
    rintro suffix rfl
    rfl
  | cons token rest ih =>
    simp only [abbreviationsIn, List.append_eq_nil_iff, ih, List.suffix_cons_iff]
    constructor
    · rintro ⟨hhead, hrest⟩ suffix (rfl | hsuffix)
      · cases h : abbreviation (token :: rest) with
        | none => rfl
        | some text => simp [h] at hhead
      · exact hrest suffix hsuffix
    · intro h
      refine ⟨?_, fun suffix hsuffix => h suffix (.inr hsuffix)⟩
      simp [h (token :: rest) (.inl rfl)]

/-- Check C8 (a rule of the project): the abbreviations `e.g.`, `i.e.`, `etc.`, `vs.` and `cf.`
of a document, outside quotations. -/
@[regula_decision]
def abbreviations : Reading → List Found := perBlock fun b => abbreviationsIn b.tokens

/-- A document conforms to C8 when it was read and the tokens of no block hold one of the five
abbreviations. -/
def NoAbbreviation (reading : Reading) : Prop :=
  ∃ pieces, reading = .read pieces ∧
    ∀ b ∈ blocks pieces, ∀ suffix, suffix <:+ b.tokens → abbreviation suffix = none

theorem abbreviations_nil_iff (reading : Reading) :
    abbreviations reading = [] ↔ NoAbbreviation reading := by
  rw [abbreviations, perBlock_nil_iff]
  exact exists_congr fun pieces => and_congr_right fun _ => forall₂_congr fun b _ =>
    abbreviationsIn_nil_iff b.tokens

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
document was read and each paragraph has six sentences or less outside parentheses. It accepts
a document with no piece and refuses a paragraph of seven sentences. -/
theorem checked_longParagraphs : Regula.ExecutableContract longParagraphs
    (Regula.Decides (· = []) ShortParagraphs) :=
  ⟨.of_iff longParagraphs_nil_iff ⟨.read [], by decide⟩
    ⟨paragraphOf "A. A. A. A. A. A. A.", by decide⟩⟩

/-- Registered contract of check C4, as a two-way decision: it reports nothing exactly when the
document was read and no piece of its prose renders a semicolon. It accepts a document with no
piece and refuses a paragraph with a semicolon. -/
theorem checked_semicolons : Regula.ExecutableContract semicolons
    (Regula.Decides (· = []) NoSemicolon) :=
  ⟨.of_iff semicolons_nil_iff ⟨.read [], by decide⟩ ⟨paragraphOf "a; b", by decide⟩⟩

/-- Registered contract of check C5, as a two-way decision: it reports nothing exactly when the
document was read and no word outside quotations is a contraction. It accepts a document with
no piece and refuses a paragraph with `don't`. -/
theorem checked_contractions : Regula.ExecutableContract contractions
    (Regula.Decides (· = []) NoContraction) :=
  ⟨.of_iff contractions_nil_iff ⟨.read [], by decide⟩ ⟨paragraphOf "don't", by decide⟩⟩

/-- A vocabulary with one term, `b`, which replaces the name `a`, and the replaced word `c`. -/
def Vocabulary.sample : Vocabulary :=
  ⟨⟨['1'], none, [], [], [⟨"b".toList, "1".toList, "B.".toList, "a".toList, "`b`".toList⟩], [],
    [⟨"c".toList, "d".toList⟩]⟩, by decide⟩

/-- Registered contract of check C6, as a two-way decision over the vocabulary and the reading:
it reports nothing exactly when the document was read and no replaced name of the vocabulary
occurs outside a longer term. It accepts a document with no piece and refuses a paragraph with
a replaced name. -/
theorem checked_replacedNames : Regula.ExecutableContract replacedNames (fun run =>
    Regula.Decides (· = [])
      (fun input : Vocabulary × Reading => NoReplacedName input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => replacedNames_nil_iff input.1 input.2)
    ⟨(Vocabulary.empty, .read []), by decide⟩
    ⟨(Vocabulary.sample, paragraphOf "a"), by decide⟩⟩

/-- Registered contract of check C7, as a two-way decision over the vocabulary and the reading:
it reports nothing exactly when the document was read and no replaced word of the vocabulary
occurs outside a longer term. It accepts a document with no piece and refuses a paragraph with
a replaced word. -/
theorem checked_replacedWords : Regula.ExecutableContract replacedWords (fun run =>
    Regula.Decides (· = [])
      (fun input : Vocabulary × Reading => NoReplacedWord input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => replacedWords_nil_iff input.1 input.2)
    ⟨(Vocabulary.empty, .read []), by decide⟩
    ⟨(Vocabulary.sample, paragraphOf "c"), by decide⟩⟩

/-- Registered contract of check C8, as a two-way decision: it reports nothing exactly when the
document was read and no block holds one of the five abbreviations outside quotations. It
accepts a document with no piece and refuses a paragraph with `e.g.`. -/
theorem checked_abbreviations : Regula.ExecutableContract abbreviations
    (Regula.Decides (· = []) NoAbbreviation) :=
  ⟨.of_iff abbreviations_nil_iff ⟨.read [], by decide⟩ ⟨paragraphOf "e.g.", by decide⟩⟩

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

/-- The findings of all checks in the document `file` with text `source`, each with its line. -/
def report (v : Vocabulary) (file source : String) (reading : Reading) : List String :=
  let bracket : Nat → Nat × Nat :=
    match reading with
    | .read pieces => brackets source pieces
    | .unread _ => fun _ => (1, 1)
  Check.all.flatMap fun check =>
    (findings v check reading).map (Found.describe file bracket check)

/-! ## The baseline -/

/-- The baseline as written: the fields of each entry. An entry is the path of a document and
then the number of findings of each check, or `frozen` and a digest, or `generated` and the
source of the document. -/
structure Ledger where
  /-- The fields of each entry, in the order of the file. -/
  entries : List (List (List Char))
  deriving DecidableEq, Repr

/-- The lines before the entries. -/
def ledgerHead : List (List Char) :=
  ["{", "  \"version\": 1,",
    "  \"checks\": [\"C1\", \"C2\", \"C3\", \"C4\", \"C5\", \"C6\", \"C7\", \"C8\"],",
    "  \"documents\": ["].map String.toList

/-- The lines after the entries. -/
def ledgerFoot : List (List Char) := ["  ]", "}"].map String.toList

/-- The parts of an entry's line between its double quotation marks, before its last field
ends: `first`, then each field with `, ` before the next one. -/
def fieldParts (first : List Char) : List (List Char) → List (List Char)
  | [] => []
  | field :: fields => first :: field :: fieldParts ", ".toList fields

/-- The line of an entry with `fields`: a JSON array of strings, with a comma after it unless
it is the last entry. -/
def entryLine (last : Bool) (fields : List (List Char)) : List Char :=
  terminated '"' (fieldParts "    [".toList fields) ++ (if last then "]" else "],").toList

/-- The lines of `entries`. -/
def entryLines : List (List (List Char)) → List (List Char)
  | [] => []
  | [fields] => [entryLine true fields]
  | fields :: more => entryLine false fields :: entryLines more

/-- The lines of the print of `l`. -/
def Ledger.lines (l : Ledger) : List (List Char) := ledgerHead ++ entryLines l.entries ++ ledgerFoot

/-- The print of `l`: its lines, each ended by a line feed. -/
def Ledger.render (l : Ledger) : List Char := terminated '\n' l.lines

/-- Each second element of a list. -/
def odds {α : Type} : List α → List α
  | _ :: second :: rest => second :: odds rest
  | _ => []

/-- The fields of an entry's line: its text between double quotation marks. -/
def fieldsOf (line : List Char) : List (List Char) := odds (split '"' line)

/-- The ledger whose print is `text`, if `text` starts with the lines before the entries. -/
def scanLedger (text : List Char) : Option Ledger :=
  (dropPrefix ledgerHead (linesOf text)).map fun rest => ⟨rest.dropLast.dropLast.map fieldsOf⟩

/-- Whether no field of `l` has a double quotation mark or a line feed, which would change the
fields and the lines of the print. -/
def Ledger.clean (l : Ledger) : Bool :=
  l.entries.all fun fields => fields.all fun field =>
    !field.contains '"' && !field.contains '\n'

theorem odds_fieldParts (tail : List Char) (fields : List (List Char)) :
    ∀ first, odds (fieldParts first fields ++ [tail]) = fields := by
  induction fields with
  | nil => intro first; rfl
  | cons field fields ih => intro first; simp [fieldParts, odds, ih]

theorem mem_fieldParts {part first : List Char} {fields : List (List Char)}
    (h : part ∈ fieldParts first fields) :
    part = first ∨ part = ", ".toList ∨ part ∈ fields := by
  induction fields generalizing first with
  | nil => simp [fieldParts] at h
  | cons field fields ih =>
    simp only [fieldParts, List.mem_cons] at h
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inr (by simp [h]))
    · rcases ih h with h | h | h
      · exact .inr (.inl h)
      · exact .inr (.inl h)
      · exact .inr (.inr (List.mem_cons_of_mem _ h))

theorem fieldsOf_entryLine (last : Bool) {fields : List (List Char)}
    (h : ∀ field ∈ fields, '"' ∉ field) : fieldsOf (entryLine last fields) = fields := by
  have hparts : ∀ part ∈ fieldParts "    [".toList fields, '"' ∉ part := by
    intro part hpart
    rcases mem_fieldParts hpart with rfl | rfl | hfield
    · decide
    · decide
    · exact h part hfield
  have htail : split '"' (if last then "]" else "],").toList =
      [(if last then "]" else "],").toList] :=
    split_of_not_mem '"' (by cases last <;> decide)
  rw [fieldsOf, entryLine, split_terminated_append '"' _ hparts, htail, odds_fieldParts]

theorem map_fieldsOf_entryLines {entries : List (List (List Char))}
    (h : ∀ fields ∈ entries, ∀ field ∈ fields, '"' ∉ field) :
    (entryLines entries).map fieldsOf = entries := by
  induction entries with
  | nil => rfl
  | cons fields more ih =>
    have hfields : ∀ last, fieldsOf (entryLine last fields) = fields :=
      fun last => fieldsOf_entryLine last (h fields (List.mem_cons_self ..))
    have hmore := ih (fun f m => h f (List.mem_cons_of_mem _ m))
    cases more with
    | nil => simp [entryLines, hfields]
    | cons next more => simp [entryLines, hfields, hmore]

theorem not_mem_entryLine {last : Bool} {fields : List (List Char)}
    (h : ∀ field ∈ fields, '\n' ∉ field) : '\n' ∉ entryLine last fields := by
  intro hmem
  simp only [entryLine, terminated, List.mem_append, List.mem_flatMap, List.mem_singleton] at hmem
  rcases hmem with ⟨part, hpart, hmem | hmem⟩ | hmem
  · rcases mem_fieldParts hpart with rfl | rfl | hfield
    · revert hmem; decide
    · revert hmem; decide
    · exact h part hfield hmem
  · revert hmem; decide
  · cases last <;> revert hmem <;> decide

theorem not_mem_entryLines {entries : List (List (List Char))}
    (h : ∀ fields ∈ entries, ∀ field ∈ fields, '\n' ∉ field) :
    ∀ line ∈ entryLines entries, '\n' ∉ line := by
  induction entries with
  | nil => intro line hline; simp [entryLines] at hline
  | cons fields more ih =>
    have hfields : ∀ last, '\n' ∉ entryLine last fields :=
      fun _ => not_mem_entryLine (h fields (List.mem_cons_self ..))
    have hmore := ih (fun f m => h f (List.mem_cons_of_mem _ m))
    intro line hline
    cases more with
    | nil =>
      simp only [entryLines, List.mem_singleton] at hline
      exact hline ▸ hfields true
    | cons next more =>
      simp only [entryLines, List.mem_cons] at hline hmore
      rcases hline with rfl | hline
      · exact hfields false
      · exact hmore line (by simpa [entryLines] using hline)

/-- The scanner reads the print of a clean ledger back as that ledger. -/
theorem scanLedger_render (l : Ledger) (h : l.clean = true) : scanLedger l.render = some l := by
  have hclean : ∀ fields ∈ l.entries, ∀ field ∈ fields, '"' ∉ field ∧ '\n' ∉ field := by
    intro fields hfields field hfield
    simp only [Ledger.clean, List.all_eq_true] at h
    simpa using h fields hfields field hfield
  have hlines : ∀ line ∈ l.lines, '\n' ∉ line := by
    intro line hline
    simp only [Ledger.lines, List.mem_append] at hline
    rcases hline with (hline | hline) | hline
    · revert line; decide
    · exact not_mem_entryLines (fun f hf x hx => (hclean f hf x hx).2) line hline
    · revert line; decide
  have hsplit : linesOf l.render = l.lines := by
    simp [linesOf, Ledger.render, split_terminated '\n' hlines]
  have hdrop : ∀ lines : List (List Char),
      (lines ++ ledgerFoot).dropLast.dropLast = lines := by
    intro lines
    have : lines ++ ledgerFoot = (lines ++ ["  ]".toList]) ++ ["}".toList] := by
      simp [ledgerFoot]
    rw [this, List.dropLast_concat, List.dropLast_concat]
  rw [scanLedger, hsplit, Ledger.lines, List.append_assoc, dropPrefix_append]
  simp only [Option.map_some, hdrop,
    map_fieldsOf_entryLines (fun f hf x hx => (hclean f hf x hx).1)]

/-- The number that the decimal digits `digits` write. -/
def value (digits : List Char) : Nat :=
  digits.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- What a baseline permits for one document. -/
inductive Allowance where
  /-- The document has exactly these numbers of findings, one for each check. -/
  | counts (numbers : List Nat)
  /-- The document is recorded evidence: its content has this SHA-256 digest and is not
  checked. -/
  | frozen (digest : String)
  /-- A program writes the document from sources that the checks do not read (`source` names
  them): it is not checked. -/
  | generated (source : String)
  deriving DecidableEq, Repr

/-- What the fields after the path of an entry permit. -/
def allowanceOf (fields : List (List Char)) : Allowance :=
  match fields with
  | [marker, text] =>
    if marker = "frozen".toList then .frozen (String.ofList text)
    else if marker = "generated".toList then .generated (String.ofList text)
    else .counts (fields.map value)
  | _ => .counts (fields.map value)

/-- Whether `text` is 64 lowercase hexadecimal digits. -/
def digest (text : List Char) : Bool :=
  text.length == 64 && text.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- What is wrong with one entry. -/
def entryDefects (fields : List (List Char)) : List String :=
  match fields with
  | [] => ["an entry has no field"]
  | path :: rest =>
    (if !path.isEmpty && path.all fun c => 32 ≤ c.val && c != '\\' then []
      else ["the path is empty or has a character that a JSON string writes with an escape"]) ++
    (match rest with
      | [marker, text] =>
        if marker = "frozen".toList then
          if digest text then [] else ["the digest is not 64 lowercase hexadecimal digits"]
        else if marker = "generated".toList then
          if (split ' ' text).all (!·.isEmpty) && text.all (· != '\\') then []
          else ["the source of a generated document is empty or has a space at an end"]
        else ["an entry has a path and then eight numbers, or `frozen` and a digest, or \
          `generated` and a source"]
      | numbers =>
        if numbers.length == Check.all.length && numbers.all numeral then
          if numbers.all (· == ['0']) then
            ["an entry has no finding: remove it"]
          else []
        else ["an entry has a path and then eight numbers, or `frozen` and a digest, or \
          `generated` and a source"])

/-- The entries whose path is not after the path of the entry before them. -/
def misplaced : List (List (List Char)) → List String
  | first :: second :: rest =>
    (if first.headD [] < second.headD [] then []
      else [s!"the entry `{String.ofList (second.headD [])}` is not after the entry before it \
        in the order of the paths"]) ++ misplaced (second :: rest)
  | _ => []

/-- The defects of `l`. -/
def Ledger.defects (l : Ledger) : List String :=
  (l.entries.flatMap fun fields =>
    (entryDefects fields).map fun reason => s!"{String.ofList (fields.headD [])}: {reason}") ++
    misplaced l.entries

/-- Whether `l` is clean and has no defect. -/
def Ledger.valid (l : Ledger) : Bool := l.clean && l.defects.isEmpty

/-- A baseline: a ledger that is clean and has no defect. Its entries are in the strict order
of their paths, so no path has two entries. -/
structure Baseline where
  /-- The fields of each entry. -/
  ledger : Ledger
  /-- The ledger is clean and has no defect. -/
  valid : ledger.valid = true

/-- The baseline with no entry. -/
def Baseline.empty : Baseline := ⟨⟨[]⟩, by decide⟩

/-- The text of `b`: the one text `Baseline.parse` reads as `b`. -/
def Baseline.write (b : Baseline) : String := String.ofList b.ledger.render

/-- The baseline whose text is `text`, if `text` is the text of one. -/
@[regula_decision]
def Baseline.parse (text : String) : Option Baseline :=
  match scanLedger text.toList with
  | some l => if h : l.valid = true ∧ l.render = text.toList then some ⟨l, h.1⟩ else none
  | none => none

theorem Baseline.parse_write (b : Baseline) : Baseline.parse b.write = some b := by
  have hclean : b.ledger.clean = true := by
    have := b.valid
    simp only [Ledger.valid, Bool.and_eq_true] at this
    exact this.1
  simp only [Baseline.parse, Baseline.write, String.toList_ofList,
    scanLedger_render b.ledger hclean]
  split
  · rfl
  · rename_i hrefused
    exact absurd ⟨b.valid, trivial⟩ hrefused

theorem Baseline.write_of_parse (text : String) (b : Baseline)
    (h : Baseline.parse text = some b) : b.write = text := by
  unfold Baseline.parse at h
  split at h
  · split at h
    · rename_i l _ hl
      cases h
      simp [Baseline.write, hl.2, String.ofList_toList]
    · cases h
  · cases h

/-- Registered contract of the baseline parser, as a two-way decision: it accepts exactly the
texts that are the print of a baseline. It accepts the print of the baseline with no entry and
refuses the empty text. -/
theorem checked_baselineParse : Regula.ExecutableContract Baseline.parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ b : Baseline, text = b.write)) :=
  ⟨.of_roundtrip Baseline.parse_write Baseline.write_of_parse Baseline.empty (unwritten := "")
    (by decide)⟩

/-- Why `text` is not the text of a baseline: each reason, with the number of its line when it
is about one line. -/
def Baseline.explain (text : String) : List (Option Nat × String) :=
  match scanLedger text.toList with
  | none =>
    [(some 1,
      "the text does not start with the four lines that the print of a baseline has first")]
  | some l =>
    if l.render = text.toList then
      if l.valid then []
      else
        (if l.clean then [] else [(none, "a field has a double quotation mark or a line feed")]) ++
          l.defects.map fun reason => (none, reason)
    else
      [(some (firstDifference 1 l.lines (split '\n' text.toList)),
        "the text is not the print of its baseline from this line on")]

/-- `Baseline.explain` reports nothing exactly when `Baseline.parse` accepts the text. -/
theorem Baseline.explain_nil_iff (text : String) :
    Baseline.explain text = [] ↔ (Baseline.parse text).isSome = true := by
  unfold Baseline.explain Baseline.parse
  cases hscan : scanLedger text.toList with
  | none => simp
  | some l =>
    by_cases hrender : l.render = text.toList
    · by_cases hvalid : l.valid = true
      · simp [hrender, hvalid]
      · simp only [hrender, hvalid, Bool.false_eq_true, ite_false, ite_true, and_true,
          dite_false, Option.isSome_none, iff_false, List.append_eq_nil_iff,
          List.map_eq_nil_iff, not_and]
        intro hclean hdefects
        have hc : l.clean = true := by
          by_cases hc : l.clean = true
          · exact hc
          · simp [hc] at hclean
        exact hvalid (by simp [Ledger.valid, hc, hdefects])
    · simp [hrender]

/-- The entries of `b`: the path of each document and what the baseline permits for it. -/
def Baseline.entries (b : Baseline) : List (String × Allowance) :=
  b.ledger.entries.filterMap fun fields =>
    match fields with
    | path :: rest => some (String.ofList path, allowanceOf rest)
    | [] => none

/-- What `b` permits for the document at `path`, if it has an entry for it. -/
def Baseline.find (b : Baseline) (path : String) : Option Allowance :=
  (b.entries.find? fun entry => entry.1 == path).map (·.2)

/-! ## The gate -/

/-- What a run observed of one tracked Markdown document. -/
structure Observed where
  /-- The path of the document. -/
  path : String
  /-- The SHA-256 digest of its content, in lowercase hexadecimal digits. -/
  digest : String
  /-- The number of findings of each check (`tally`). -/
  tally : List Nat
  deriving DecidableEq, Repr

/-- A document is admitted by a baseline: with no entry it has no finding, with an entry of
numbers it has exactly those numbers of findings, with a frozen entry its content has the
entry's digest, and with a generated entry nothing is required of it. -/
def Observed.Admitted (b : Baseline) (d : Observed) : Prop :=
  match b.find d.path with
  | none => ∀ n ∈ d.tally, n = 0
  | some (.counts numbers) => d.tally = numbers
  | some (.frozen digest) => d.digest = digest
  | some (.generated _) => True

/-- Why a document is not admitted by a baseline, if it is not. -/
def Observed.refusal (b : Baseline) (d : Observed) : Option String :=
  match b.find d.path with
  | none =>
    if d.tally.all (· == 0) then none
    else some s!"{d.path}: the document has findings and no entry in the baseline"
  | some (.counts numbers) =>
    if d.tally = numbers then none
    else
      some s!"{d.path}: the document has the numbers of findings {d.tally} and the baseline \
        has {numbers}: correct the new findings, or write the smaller numbers in the baseline"
  | some (.frozen digest) =>
    if d.digest = digest then none
    else some s!"{d.path}: the document is frozen in the baseline and its content changed"
  | some (.generated _) => none

theorem Observed.refusal_none_iff (b : Baseline) (d : Observed) :
    d.refusal b = none ↔ d.Admitted b := by
  unfold Observed.refusal Observed.Admitted
  split
  · by_cases h : d.tally.all (· == 0) = true
    · simp only [h, ite_true, true_iff]
      simpa using h
    · simp only [h, Bool.false_eq_true, ite_false, reduceCtorEq, false_iff]
      simpa using h
  · rename_i numbers _
    by_cases h : d.tally = numbers <;> simp [h]
  · rename_i digest _
    by_cases h : d.digest = digest <;> simp [h]
  · simp

/-- The gate of a repository's documents: why the documents `documents` are not accepted for
the baseline `b`. Each document that is not admitted is reported, and each entry of the baseline
whose path is not the path of one of the documents. -/
@[regula_decision]
def gate (b : Baseline) (documents : List Observed) : List String :=
  documents.filterMap (·.refusal b) ++
    (b.entries.filter fun entry => !documents.any fun d => d.path == entry.1).map fun entry =>
      s!"{entry.1}: the baseline has an entry for a path that is not a tracked Markdown document"

/-- The documents are accepted for a baseline: each one is admitted, and each entry of the
baseline is for one of them. -/
def Accepted (b : Baseline) (documents : List Observed) : Prop :=
  (∀ d ∈ documents, d.Admitted b) ∧ ∀ entry ∈ b.entries, ∃ d ∈ documents, d.path = entry.1

theorem gate_nil_iff (b : Baseline) (documents : List Observed) :
    gate b documents = [] ↔ Accepted b documents := by
  simp only [gate, List.append_eq_nil_iff, List.filterMap_eq_nil_iff, List.map_eq_nil_iff,
    List.filter_eq_nil_iff, Accepted, Observed.refusal_none_iff]
  refine and_congr_right fun _ => forall₂_congr fun entry _ => ?_
  simp

/-- A baseline with one entry: the document `a` with one finding of C1. -/
def Baseline.sample : Baseline :=
  ⟨⟨[["a", "1", "0", "0", "0", "0", "0", "0", "0"].map String.toList]⟩, by decide⟩

/-- Registered contract of the gate, as a two-way decision over the baseline and the observed
documents: it reports nothing exactly when each document is admitted and each entry of the
baseline is for one of the documents. It accepts no document for the baseline with no entry and
refuses a document with a finding for that baseline. -/
theorem checked_gate : Regula.ExecutableContract gate (fun run =>
    Regula.Decides (· = [])
      (fun input : Baseline × List Observed => Accepted input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => gate_nil_iff input.1 input.2)
    ⟨(Baseline.empty, []), by decide⟩
    ⟨(Baseline.empty, [⟨"a", "", [1]⟩]), by decide⟩⟩

/-! ## The ratchet -/

/-- Whether the allowance `after` is no wider than the allowance `before` of an earlier
baseline: numbers of findings that are each not larger, the same digest of a frozen document,
or a generated document as before. A document does not change its class. -/
def covers (before after : Allowance) : Bool :=
  match before, after with
  | .counts earlier, .counts later =>
    earlier.length == later.length && (later.zip earlier).all fun pair => pair.1 ≤ pair.2
  | .frozen earlier, .frozen later => earlier == later
  | .generated _, .generated _ => true
  | _, _ => false

/-- The ratchet of the baseline: why the baseline `head` is not accepted in relation to `base`,
the baseline of the base revision. An entry of `head` whose path has no entry in `base`, or a
wider one, is reported. With no baseline at the base revision nothing is reported. -/
@[regula_decision]
def ratchet (base : Option Baseline) (head : Baseline) : List String :=
  match base with
  | none => []
  | some base =>
    head.entries.filterMap fun entry =>
      match base.find entry.1 with
      | none => some s!"{entry.1}: the baseline has a new entry; a new document has no finding"
      | some before =>
        if covers before entry.2 then none
        else
          some s!"{entry.1}: the entry permits more than the entry of the base revision: a \
            larger number, another class, or another digest of a frozen document"

/-- A baseline does not grow in relation to the baseline of the base revision: each of its
entries has an entry of the same path there that covers it. -/
def Shrinks (base : Option Baseline) (head : Baseline) : Prop :=
  ∀ earlier, base = some earlier → ∀ entry ∈ head.entries,
    ∃ before, earlier.find entry.1 = some before ∧ covers before entry.2 = true

theorem ratchet_nil_iff (base : Option Baseline) (head : Baseline) :
    ratchet base head = [] ↔ Shrinks base head := by
  cases base with
  | none => simp [ratchet, Shrinks]
  | some earlier =>
    simp only [ratchet, List.filterMap_eq_nil_iff, Shrinks, Option.some.injEq, forall_eq']
    refine forall₂_congr fun entry _ => ?_
    cases hfind : earlier.find entry.1 with
    | none => simp
    | some before => by_cases h : covers before entry.2 = true <;> simp [h]

/-- Registered contract of the ratchet, as a two-way decision over the two baselines: it
reports nothing exactly when each entry of the baseline has an entry of the same path in the
baseline of the base revision that covers it, or the base revision has no baseline. It accepts
the baseline with no entry and refuses a baseline with an entry in relation to the baseline
with no entry. -/
theorem checked_ratchet : Regula.ExecutableContract ratchet (fun run =>
    Regula.Decides (· = [])
      (fun input : Option Baseline × Baseline => Shrinks input.1 input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => ratchet_nil_iff input.1 input.2)
    ⟨(none, Baseline.empty), by decide⟩
    ⟨(some Baseline.empty, Baseline.sample), by decide⟩⟩

end Regula.Controlled
