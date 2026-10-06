import Regula.Contract
import Regula.Decision

/-! # The vocabulary of a project

`CONTEXT.md` at the root of a repository gives the technical nouns and technical verbs of the
project, the names each one replaces, and the words the project does not write. This module
defines that file exactly: the type `Vocabulary`, its one text (`write`), and the parser that
accepts a text only when it is that text (`parse`). It also defines what a word is, for the
vocabulary and for the checks of `RegulaCore.ControlledProse`, which read the same tokens.

The writing guide (`docs/guides/writing.md`) states the rules for a writer. Nothing here is a
rule of Regula's standard: this is a check of a repository's own documents.

## Main declarations

- `split`, `terminated`, `split_terminated`: a text divided at a character, and the text that
  division inverts.
- `Atom`, `Lexeme`, `Token`, `lex`, `words`: the tokens of prose. A word is a maximal sequence of
  ASCII letters and digits, continued by a hyphen or an apostrophe between two of them and by a
  period or a comma between two digits.
- `Term`, `Replaced`, `Draft`: the cells of the tables, as written.
- `Draft.render`, `scan`, `scan_render`: the print of a draft, and the scanner that reads every
  print of a clean draft back.
- `Draft.defects`, `Draft.valid`, `Vocabulary`: a vocabulary is a draft with no defect.
- `write`, `parse`, `checked_parse`: the parser is a two-way decision of "is the print of a
  vocabulary" (`Regula.Decides.of_roundtrip`).
- `explain`, `explain_nil_iff`: why a text is refused, by line. It reports nothing exactly when
  `parse` accepts.
- `untracked`, `checked_untracked`: the source paths that are not among the tracked files.
- `adopt`, `checked_adopt`: a project vocabulary together with the `Shared` tables of the
  vocabulary it names.

## The text

A print has a title, two or three head lines, and then up to five tables, each present only when
it has a row: `Shared technical nouns`, `Shared technical verbs`, `Project technical nouns`,
`Project technical verbs` and `Replaced words`, in that order. Each row is one line. A draft
holds the text of each cell, so that the print of a draft is determined cell by cell, and
`Draft.defects` constrains what a cell holds: the views `Term.names`, `Term.path` and
`Term.leanName` read a cell that has no defect.

## Boundaries

`checked_parse` is about the text given to `parse`. That the text is the file's, and that the
tracked paths given to `untracked` are the paths Git tracks, rests on the file system and on
Git, which the executable reads (`markdown/MarkdownMain.lean`). A definition's one-sentence rule
is decided on the cell's characters (`sentence`), without a Markdown parser: the checks of
`RegulaCore.ControlledProse` read the same cell again as part of the document.
-/

namespace Regula.Controlled

/-! ## Text divided at a character -/

/-- `text` divided at each `separator`: one part more than `text` has separators. -/
def split (separator : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    if c = separator then [] :: split separator rest
    else
      match split separator rest with
      | [] => [[c]]
      | part :: parts => (c :: part) :: parts

/-- Each of `parts` with `terminator` after it. -/
def terminated (terminator : Char) (parts : List (List Char)) : List Char :=
  parts.flatMap (· ++ [terminator])

theorem split_append (separator : Char) {part : List Char} (rest : List Char)
    (h : separator ∉ part) :
    split separator (part ++ separator :: rest) = part :: split separator rest := by
  induction part with
  | nil => simp [split]
  | cons c part ih =>
    have hc : c ≠ separator := fun e => h (by simp [e])
    have hrest := ih (fun m => h (List.mem_cons_of_mem _ m))
    simp [split, hc, hrest]

theorem split_of_not_mem (separator : Char) {part : List Char} (h : separator ∉ part) :
    split separator part = [part] := by
  induction part with
  | nil => rfl
  | cons c part ih =>
    have hc : c ≠ separator := fun e => h (by simp [e])
    have hrest := ih (fun m => h (List.mem_cons_of_mem _ m))
    simp [split, hc, hrest]

/-- Dividing at the terminator reads the parts of a terminated text back, and then the parts of
the text after it, when no part holds the terminator. -/
theorem split_terminated_append (terminator : Char) {parts : List (List Char)}
    (rest : List Char) (h : ∀ part ∈ parts, terminator ∉ part) :
    split terminator (terminated terminator parts ++ rest) = parts ++ split terminator rest := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
    have hrest := ih (fun p m => h p (List.mem_cons_of_mem _ m))
    have hpart := h part (List.mem_cons_self ..)
    simp only [terminated, List.flatMap_cons, List.append_assoc, List.cons_append,
      List.nil_append] at hrest ⊢
    rw [split_append terminator _ hpart, hrest]

/-- Dividing at the terminator reads the parts of a terminated text back, with one empty part
after the last terminator, when no part holds the terminator. -/
theorem split_terminated (terminator : Char) {parts : List (List Char)}
    (h : ∀ part ∈ parts, terminator ∉ part) :
    split terminator (terminated terminator parts) = parts ++ [[]] := by
  have := split_terminated_append terminator [] h
  simpa [split] using this

/-- `text` without `pre` at its start, when it starts with `pre`. -/
def dropPrefix {α : Type} [DecidableEq α] : List α → List α → Option (List α)
  | [], text => some text
  | _ :: _, [] => none
  | c :: pre, d :: text => if c = d then dropPrefix pre text else none

theorem dropPrefix_append {α : Type} [DecidableEq α] (pre text : List α) :
    dropPrefix pre (pre ++ text) = some text := by
  induction pre with
  | nil => rfl
  | cons c pre ih => simp [dropPrefix, ih]

/-- `text` in lowercase (ASCII letters). -/
def lower (text : List Char) : List Char := text.map Char.toLower

/-! ## Words -/

/-- One character of prose (`some`), or one piece of code (`none`), with the place of its piece:
the number of located pieces before it (`Regula.Markdown.Piece.located?`). -/
structure Atom where
  /-- The place of the piece the character or the code comes from. -/
  anchor : Nat
  /-- The character, or `none` for code. -/
  char : Option Char
  deriving DecidableEq, Repr

/-- What one token of prose is. -/
inductive Lexeme where
  /-- A word, as written: a maximal sequence of ASCII letters and digits, continued by a hyphen
  or an apostrophe between two of them and by a period or a comma between two digits; or one
  character outside ASCII that is not a known space or mark. -/
  | word (text : List Char)
  /-- One unit that is read as one word and whose text is not read: a maximal sequence of code
  pieces, or a quotation (`Regula.Controlled.quote`). -/
  | unit
  /-- A maximal sequence of space characters. -/
  | space
  /-- A period, a question mark or an exclamation mark. -/
  | stop (c : Char)
  /-- An opening parenthesis. -/
  | opening
  /-- A closing parenthesis. -/
  | closing
  /-- A double quotation mark: `"`, `“` or `”`. -/
  | quote (c : Char)
  /-- Any other character. -/
  | mark (c : Char)
  deriving DecidableEq, Repr

/-- One token of prose and the place of the piece it starts in. -/
structure Token where
  /-- The place of the piece the token starts in. -/
  anchor : Nat
  /-- What the token is. -/
  lexeme : Lexeme
  deriving DecidableEq, Repr

/-- Whether `c` is an apostrophe: `'` or `’` (U+2019). -/
def apostrophe (c : Char) : Bool := c = '\'' || c = '’'

/-- Whether `c` is a space character: ASCII white space, or one of the space characters outside
ASCII that are known here (U+00A0, U+1680, U+2000 to U+200A, U+2028, U+2029, U+202F, U+205F and
U+3000). -/
def spacing (c : Char) : Bool :=
  c.isWhitespace || c.val = 0xA0 || c.val = 0x1680 || (0x2000 ≤ c.val && c.val ≤ 0x200A) ||
    c.val = 0x2028 || c.val = 0x2029 || c.val = 0x202F || c.val = 0x205F || c.val = 0x3000

/-- Whether `c` continues a word between `before` and `after`: a hyphen or an apostrophe between
two ASCII letters or digits, or a period or a comma between two digits. -/
def joins (before c after : Char) : Bool :=
  ((c = '-' || apostrophe c) && before.isAlphanum && after.isAlphanum) ||
    ((c = '.' || c = ',') && before.isDigit && after.isDigit)

/-- What a character that is not part of a longer word is. A character outside ASCII that is
not a known space or mark (`‘`, `’`, `“`, `”`, `–`, `—`, `…`) is a word of its own, so that no
text has fewer words here than a reader counts. -/
def classify (c : Char) : Lexeme :=
  if spacing c then .space
  else if c = '.' || c = '?' || c = '!' then .stop c
  else if c = '(' then .opening
  else if c = ')' then .closing
  else if c = '"' || c = '“' || c = '”' then .quote c
  else if c.val < 128 || c = '‘' || c = '’' || c = '–' || c = '—' || c = '…' then .mark c
  else .word [c]

/-- The token of the word in progress, whose characters `current` holds last first. -/
def flush : Option (Nat × List Char) → List Token
  | none => []
  | some (anchor, reversed) => [⟨anchor, .word reversed.reverse⟩]

/-- The tokens of `atoms`, read after the word in progress `current`. -/
def lexFrom (current : Option (Nat × List Char)) : List Atom → List Token
  | [] => flush current
  | atom :: rest =>
    match atom.char with
    | none => flush current ++ ⟨atom.anchor, .unit⟩ :: lexFrom none rest
    | some c =>
      if c.isAlphanum then
        match current with
        | none => lexFrom (some (atom.anchor, [c])) rest
        | some (anchor, reversed) => lexFrom (some (anchor, c :: reversed)) rest
      else
        match current, rest with
        | some (anchor, last :: reversed), ⟨_, some next⟩ :: _ =>
          if joins last c next then
            lexFrom (some (anchor, (if apostrophe c then '\'' else c) :: last :: reversed)) rest
          else flush current ++ ⟨atom.anchor, classify c⟩ :: lexFrom none rest
        | _, _ => flush current ++ ⟨atom.anchor, classify c⟩ :: lexFrom none rest

/-- `tokens` with each sequence of spaces as one space and each sequence of code pieces as one
unit; `previous` is the token before them. -/
def squeeze (previous : Option Lexeme) : List Token → List Token
  | [] => []
  | token :: rest =>
    if (token.lexeme = .space ∨ token.lexeme = .unit) ∧ previous = some token.lexeme then
      squeeze previous rest
    else token :: squeeze (some token.lexeme) rest

/-- The tokens of `atoms`, in order. An apostrophe inside a word is written `'`. -/
def lex (atoms : List Atom) : List Token := squeeze none (lexFrom none atoms)

/-- The words of `text`, in order, as written. -/
def words (text : List Char) : List (List Char) :=
  (lex (text.map fun c => ⟨0, some c⟩)).filterMap fun token =>
    match token.lexeme with
    | .word word => some word
    | _ => none

/-- Whether `text` is one or more words with one space between them and nothing else. -/
def phrase (text : List Char) : Bool :=
  !(words text).isEmpty && text == [' '].intercalate (words text)

/-! ## The tables as written -/

/-- One row of a table of terms: the text of its five cells. -/
structure Term where
  /-- The term: one to three words. -/
  term : List Char
  /-- The category of rule 1.5 (a noun) or of rule 1.12 (a verb), as a number or a number and a
  letter. -/
  category : List Char
  /-- The definition: one sentence. -/
  definition : List Char
  /-- The names the term replaces, with `, ` between them, or `-`. -/
  replaces : List Char
  /-- The tracked file that defines the term, in backticks, and optionally a Lean name. -/
  source : List Char
  deriving DecidableEq, Repr

/-- One row of the table of replaced words: the text of its two cells. -/
structure Replaced where
  /-- The word the project does not write. -/
  word : List Char
  /-- What to write. -/
  write : List Char
  deriving DecidableEq, Repr

/-- A vocabulary as written, before its defects are decided: the text of each cell. -/
structure Draft where
  /-- The vocabulary version, in decimal digits. -/
  version : List Char
  /-- The package whose `Shared` tables this vocabulary uses, if it names one. -/
  shared : Option (List Char)
  /-- The rows of `Shared technical nouns`. -/
  sharedNouns : List Term
  /-- The rows of `Shared technical verbs`. -/
  sharedVerbs : List Term
  /-- The rows of `Project technical nouns`. -/
  projectNouns : List Term
  /-- The rows of `Project technical verbs`. -/
  projectVerbs : List Term
  /-- The rows of `Replaced words`. -/
  replaced : List Replaced
  deriving DecidableEq, Repr

/-- The cells of a row of terms. -/
def Term.cells (t : Term) : List (List Char) :=
  [t.term, t.category, t.definition, t.replaces, t.source]

/-- The row of terms with these cells. -/
def Term.ofCells : List (List Char) → Option Term
  | [term, category, definition, replaces, source] =>
    some ⟨term, category, definition, replaces, source⟩
  | _ => none

/-- The cells of a row of replaced words. -/
def Replaced.cells (r : Replaced) : List (List Char) := [r.word, r.write]

/-- The row of replaced words with these cells. -/
def Replaced.ofCells : List (List Char) → Option Replaced
  | [word, write] => some ⟨word, write⟩
  | _ => none

/-! ## The print -/

/-- The line of a table row with `cells`: `| a | b |`. -/
def row (cells : List (List Char)) : List Char :=
  '|' :: terminated '|' (cells.map fun cell => ' ' :: cell ++ [' '])

/-- The cells of a table row's line. -/
def cellsOf (line : List Char) : Option (List (List Char)) :=
  match split '|' line with
  | [] :: parts => some (parts.dropLast.map fun part => (part.drop 1).dropLast)
  | _ => none

theorem cellsOf_row {cells : List (List Char)} (h : ∀ cell ∈ cells, '|' ∉ cell) :
    cellsOf (row cells) = some cells := by
  have hparts : ∀ part ∈ cells.map (fun cell => ' ' :: cell ++ [' ']), '|' ∉ part := by
    intro part hpart
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hpart
    have := h cell hcell
    simp [this]
  have hhead : ∀ rest, split '|' ('|' :: rest) = [] :: split '|' rest := fun rest => by
    simp [split]
  have hsplit : split '|' (row cells) =
      [] :: (cells.map (fun cell => ' ' :: cell ++ [' ']) ++ [[]]) := by
    rw [row, hhead, split_terminated '|' hparts]
  simp [cellsOf, hsplit, Function.comp_def]

/-- The title and the column names of a table. -/
structure Heading where
  /-- The line of the title. -/
  title : List Char
  /-- The names of the columns. -/
  columns : List (List Char)
  deriving DecidableEq, Repr

/-- The line under the column names: one `---` for each column. -/
def Heading.rule (heading : Heading) : List Char :=
  row (heading.columns.map fun _ => "---".toList)

/-- The lines of a table with `rows`: nothing when it has no row, and otherwise an empty line,
its title, an empty line, the column names, the rule and one line for each row. -/
def table (heading : Heading) (rows : List (List (List Char))) : List (List Char) :=
  if rows.isEmpty then []
  else [] :: heading.title :: [] :: row heading.columns :: heading.rule :: rows.map row

/-- The lines of `tables`, each under the heading at its position. -/
def printTables : List Heading → List (List (List (List Char))) → List (List Char)
  | heading :: headings, rows :: tables => table heading rows ++ printTables headings tables
  | _, _ => []

/-- The columns of a table of terms. -/
def termColumns : List (List Char) :=
  ["Term", "Category", "Definition", "Replaces", "Source"].map String.toList

/-- The five tables, in the order of the print. -/
def headings : List Heading := [
  ⟨"## Shared technical nouns".toList, termColumns⟩,
  ⟨"## Shared technical verbs".toList, termColumns⟩,
  ⟨"## Project technical nouns".toList, termColumns⟩,
  ⟨"## Project technical verbs".toList, termColumns⟩,
  ⟨"## Replaced words".toList, ["Do not write", "Write"].map String.toList⟩]

/-- The first line of the print. -/
def titleLine : List Char := "# CONTEXT".toList

/-- The text before the version on its line. -/
def versionLabel : List Char := "Vocabulary version: ".toList

/-- The line that names the edition the vocabulary is written to. The name identifies the
standard and is used for nothing else. -/
def standardLine : List Char := "Standard: ASD-STE100 Issue 9".toList

/-- The text before the package on the line that names a shared vocabulary. -/
def sharedLabel : List Char := "Shared vocabulary: ".toList

/-- The rows of the five tables, as cells. -/
def Draft.tables (d : Draft) : List (List (List (List Char))) :=
  [d.sharedNouns.map Term.cells, d.sharedVerbs.map Term.cells, d.projectNouns.map Term.cells,
    d.projectVerbs.map Term.cells, d.replaced.map Replaced.cells]

/-- The lines of the print of `d`: the title, an empty line, the version, the edition, the
shared package if `d` names one, and the tables that have a row. -/
def Draft.lines (d : Draft) : List (List Char) :=
  titleLine :: [] :: (versionLabel ++ d.version) :: standardLine ::
    ((match d.shared with
      | none => []
      | some package => [sharedLabel ++ package]) ++ printTables headings d.tables)

/-- The print of `d`: its lines, each ended by a line feed. -/
def Draft.render (d : Draft) : List Char := terminated '\n' d.lines

/-! ## The scanner -/

/-- The result of a scan: a value, or the number of lines from the refused line to the end of
the text together with the reason. -/
abbrev Scan := Except (Nat × String)

/-- The rows of `lines`, as cells. -/
def readRows : List (List Char) → Option (List (List (List Char)))
  | [] => some []
  | line :: lines =>
    match cellsOf line, readRows lines with
    | some cells, some rows => some (cells :: rows)
    | _, _ => none

theorem readRows_rows {rows : List (List (List Char))}
    (h : ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell) : readRows (rows.map row) = some rows := by
  induction rows with
  | nil => rfl
  | cons cells rows ih =>
    have hrest := ih (fun c m => h c (List.mem_cons_of_mem _ m))
    simp [readRows, cellsOf_row (h cells (List.mem_cons_self ..)), hrest]

/-- The number of `lines` from the first one that is not a table row to the last. -/
def unreadFrom : List (List Char) → Nat
  | [] => 0
  | line :: lines => if (cellsOf line).isSome then unreadFrom lines else lines.length + 1

/-- The rows of the table under `heading` at the start of `lines`, and the lines after it. A
table starts with an empty line and its title, and its rows end at the next empty line or at
the end of the text. Lines that do not start so hold no such table: its rows are none. -/
def takeTable (heading : Heading) (lines : List (List Char)) :
    Scan (List (List (List Char)) × List (List Char)) :=
  match lines with
  | [] :: title :: rest =>
    if title = heading.title then
      match rest with
      | [] :: columns :: rule :: rest =>
        if columns = row heading.columns ∧ rule = heading.rule then
          match readRows (rest.takeWhile fun line => !line.isEmpty) with
          | some rows =>
            if rows.isEmpty then throw (rest.length + 1, "the table has no row")
            else if rows.all fun cells => cells.length == heading.columns.length then
              pure (rows, rest.dropWhile fun line => !line.isEmpty)
            else
              throw (rest.length -
                  (rows.takeWhile fun cells => cells.length == heading.columns.length).length,
                "this row has another number of cells than its table has columns")
          | none =>
            throw (unreadFrom (rest.takeWhile fun line => !line.isEmpty) +
                (rest.dropWhile fun line => !line.isEmpty).length,
              "this line of the table is not a row")
        else
          throw (rest.length + 2,
            s!"the table has other column names or another rule than `{String.ofList
              (row heading.columns)}` and `{String.ofList heading.rule}`")
      | _ =>
        throw (rest.length,
          "the title of a table has no empty line, column names and rule after it")
    else pure ([], lines)
  | _ => pure ([], lines)

/-- The rows of the tables under `headings` at the start of `lines`, in order, and the lines
after them. -/
def takeTables : List Heading → List (List Char) →
    Scan (List (List (List (List Char))) × List (List Char))
  | [], lines => pure ([], lines)
  | heading :: headings, lines => do
    let (rows, rest) ← takeTable heading lines
    let (tables, rest) ← takeTables headings rest
    pure (rows :: tables, rest)

/-- Each of `rows` read by `read`. -/
def readAll {α : Type} (read : List (List Char) → Option α) :
    List (List (List Char)) → Option (List α)
  | [] => some []
  | cells :: rows =>
    match read cells, readAll read rows with
    | some value, some values => some (value :: values)
    | _, _ => none

theorem readAll_map {α : Type} {read : List (List Char) → Option α}
    {cells : α → List (List Char)} (h : ∀ value, read (cells value) = some value)
    (values : List α) : readAll read (values.map cells) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [readAll, h, ih]

/-- What a text that does not start with the head lines is refused for. -/
def headReason : String :=
  s!"expected the lines `{String.ofList titleLine}`, an empty line, \
    `{String.ofList versionLabel}` with the version, and `{String.ofList standardLine}`"

/-- The draft whose print has `lines`. -/
def scanLines (lines : List (List Char)) : Scan Draft :=
  match lines with
  | first :: [] :: version :: standard :: rest =>
    if first = titleLine ∧ standard = standardLine then
      match dropPrefix versionLabel version with
      | none => throw (lines.length, headReason)
      | some version =>
        let (shared, rest) : Option (List Char) × List (List Char) :=
          match rest with
          | line :: more =>
            match dropPrefix sharedLabel line with
            | some package => (some package, more)
            | none => (none, rest)
          | [] => (none, rest)
        do
          let (tables, rest) ← takeTables headings rest
          match tables, rest with
          | [sharedNouns, sharedVerbs, projectNouns, projectVerbs, replaced], [] =>
            match readAll Term.ofCells sharedNouns, readAll Term.ofCells sharedVerbs,
                readAll Term.ofCells projectNouns, readAll Term.ofCells projectVerbs,
                readAll Replaced.ofCells replaced with
            | some sharedNouns, some sharedVerbs, some projectNouns, some projectVerbs,
                some replaced =>
              pure ⟨version, shared, sharedNouns, sharedVerbs, projectNouns, projectVerbs,
                replaced⟩
            | _, _, _, _, _ =>
              throw (lines.length, "a row has another number of cells than its table has columns")
          | _, _ =>
            throw (rest.length,
              s!"expected `{String.ofList sharedLabel}` with a package directly after the head \
                lines, or an empty line and the title of a table that is not yet read, in the \
                order of the tables, or the end of the text")
    else throw (lines.length, headReason)
  | _ => throw (lines.length, headReason)

/-- The lines of `text`: its parts between line feeds, without the part after the last one. -/
def linesOf (text : List Char) : List (List Char) := (split '\n' text).dropLast

/-- The draft whose print is `text`, if `text` has the form of a print. -/
def scan (text : List Char) : Scan Draft := scanLines (linesOf text)

/-! ## The scanner reads every print back -/

/-- Whether no cell and no head field of `d` has a `|` character or a line feed, which would
change the rows and the lines of the print. -/
def Draft.clean (d : Draft) : Bool :=
  !d.version.contains '\n' && (d.shared.all fun package => !package.contains '\n') &&
    d.tables.all fun rows => rows.all fun cells => cells.all fun cell =>
      !cell.contains '|' && !cell.contains '\n'

/-- `lines` is empty or starts with an empty line: where the rows of a table end. -/
def Ends (lines : List (List Char)) : Prop := ∀ line, lines.head? = some line → line = []

theorem row_ne_nil (cells : List (List Char)) : (row cells).isEmpty = false := rfl

theorem takeWhile_rows (rows : List (List (List Char))) {rest : List (List Char)}
    (h : Ends rest) :
    (rows.map row ++ rest).takeWhile (fun line => !line.isEmpty) = rows.map row := by
  induction rows with
  | nil =>
    cases rest with
    | nil => rfl
    | cons line rest => simp [h line rfl]
  | cons cells rows ih => simpa [List.takeWhile_cons, row_ne_nil] using ih

theorem dropWhile_rows (rows : List (List (List Char))) {rest : List (List Char)}
    (h : Ends rest) :
    (rows.map row ++ rest).dropWhile (fun line => !line.isEmpty) = rest := by
  induction rows with
  | nil =>
    cases rest with
    | nil => rfl
    | cons line rest => simp [h line rfl]
  | cons cells rows ih => simpa [List.dropWhile_cons, row_ne_nil] using ih

theorem takeTable_table (heading : Heading) {rows : List (List (List Char))}
    {rest : List (List Char)} (hrest : Ends rest) (hrows : rows ≠ [])
    (hclean : ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell)
    (hfit : ∀ cells ∈ rows, cells.length = heading.columns.length) :
    takeTable heading (table heading rows ++ rest) = pure (rows, rest) := by
  have hempty : rows.isEmpty = false := by simpa using hrows
  have hall : (rows.all fun cells => cells.length == heading.columns.length) = true := by
    simpa using hfit
  simp [table, hempty, takeTable, takeWhile_rows rows hrest, dropWhile_rows rows hrest,
    readRows_rows hclean, hall]

/-- Each row of each table has as many cells as the heading at the table's position has
columns. -/
def Fit : List Heading → List (List (List (List Char))) → Prop
  | heading :: headings, rows :: tables =>
    (∀ cells ∈ rows, cells.length = heading.columns.length) ∧ Fit headings tables
  | _, _ => True

/-- `lines` is empty, or starts with an empty line and one of `titles`: what the lines of
tables are. -/
def Starts (titles : List (List Char)) (lines : List (List Char)) : Prop :=
  lines = [] ∨ ∃ title ∈ titles, ∃ rest, lines = [] :: title :: rest

theorem Starts.ends {titles : List (List Char)} {lines : List (List Char)}
    (h : Starts titles lines) : Ends lines := by
  rcases h with rfl | ⟨title, _, rest, rfl⟩
  · intro line hline; simp at hline
  · intro line hline; simpa using hline.symm

theorem takeTable_other (heading : Heading) {titles : List (List Char)}
    {lines : List (List Char)} (h : Starts titles lines) (hother : heading.title ∉ titles) :
    takeTable heading lines = pure ([], lines) := by
  rcases h with rfl | ⟨title, htitle, rest, rfl⟩
  · rfl
  · have hne : title ≠ heading.title := fun e => hother (e ▸ htitle)
    simp [takeTable, hne]

theorem starts_printTables (headings : List Heading) :
    ∀ (tables : List (List (List (List Char)))),
      Starts (headings.map (·.title)) (printTables headings tables) := by
  induction headings with
  | nil => intro tables; exact .inl (by simp [printTables])
  | cons heading headings ih =>
    intro tables
    cases tables with
    | nil => exact .inl (by simp [printTables])
    | cons rows tables =>
      by_cases hrows : rows.isEmpty = true
      · rcases ih tables with hnil | ⟨title, htitle, rest, hrest⟩
        · exact .inl (by simp [printTables, table, hrows, hnil])
        · exact .inr ⟨title, List.mem_cons_of_mem _ htitle, rest, by
            simp [printTables, table, hrows, hrest]⟩
      · exact .inr ⟨heading.title, List.mem_cons_self ..,
          [] :: row heading.columns :: heading.rule ::
            (rows.map row ++ printTables headings tables), by
          simp [printTables, table, hrows]⟩

/-- The scanner reads the tables of a print back, when the titles differ, no cell holds a `|`
character and each row has one cell for each column. -/
theorem takeTables_printTables (headings : List Heading) :
    ∀ (tables : List (List (List (List Char)))), tables.length = headings.length →
      (headings.map (·.title)).Nodup →
      (∀ rows ∈ tables, ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell) →
      Fit headings tables →
      takeTables headings (printTables headings tables) = pure (tables, []) := by
  induction headings with
  | nil =>
    intro tables hlength _ _ _
    have : tables = [] := List.eq_nil_of_length_eq_zero hlength
    subst this
    rfl
  | cons heading headings ih =>
    intro tables hlength hnodup hclean hfit
    cases tables with
    | nil => simp at hlength
    | cons rows tables =>
      have hrest := ih tables (by simpa using hlength) (List.nodup_cons.mp hnodup).2
        (fun r m => hclean r (List.mem_cons_of_mem _ m)) hfit.2
      have hstarts := starts_printTables headings tables
      by_cases hrows : rows = []
      · subst hrows
        have hother := takeTable_other heading hstarts (List.nodup_cons.mp hnodup).1
        simp only [printTables, table, List.isEmpty_nil, ite_true, List.nil_append, takeTables,
          hother, pure_bind, hrest]
      · simp only [printTables, takeTables,
          takeTable_table heading hstarts.ends hrows (hclean rows (List.mem_cons_self ..))
            hfit.1,
          pure_bind, hrest]

theorem headings_nodup : (headings.map (·.title)).Nodup := by decide

theorem Draft.clean_cells {d : Draft} (h : d.clean = true) :
    ∀ rows ∈ d.tables, ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell ∧ '\n' ∉ cell := by
  intro rows hrows cells hcells cell hcell
  simp only [Draft.clean, Bool.and_eq_true, List.all_eq_true] at h
  simpa using h.2 rows hrows cells hcells cell hcell

/-- The lines of tables do not start with the line that names a shared vocabulary. -/
theorem dropPrefix_printTables (tables : List (List (List (List Char)))) :
    (match printTables headings tables with
      | line :: more =>
        match dropPrefix sharedLabel line with
        | some package => (some package, more)
        | none => (none, printTables headings tables)
      | [] => (none, printTables headings tables)) =
    ((none : Option (List Char)), printTables headings tables) := by
  rcases starts_printTables headings tables with hnil | ⟨title, _, rest, hrest⟩
  · simp [hnil]
  · simp only [hrest]
    rfl

/-- The scanner reads the lines of the print of a clean draft back as that draft. -/
theorem scanLines_lines (d : Draft) (h : d.clean = true) : scanLines d.lines = pure d := by
  have htables := takeTables_printTables headings d.tables rfl headings_nodup
    (fun rows hrows cells hcells cell hcell =>
      (d.clean_cells h rows hrows cells hcells cell hcell).1)
    (by simp [Fit, headings, Draft.tables, Term.cells, Replaced.cells, termColumns])
  have hterms : ∀ terms : List Term, readAll Term.ofCells (terms.map Term.cells) = some terms :=
    readAll_map (fun _ => rfl)
  have hreplaced : ∀ rows : List Replaced,
      readAll Replaced.ofCells (rows.map Replaced.cells) = some rows :=
    readAll_map (fun _ => rfl)
  cases hpackage : d.shared with
  | none =>
    simp only [Draft.lines, hpackage, scanLines, and_self, ite_true, dropPrefix_append,
      List.nil_append, dropPrefix_printTables, htables, pure_bind]
    simp only [Draft.tables, hterms, hreplaced]
    cases d
    simp_all
  | some package =>
    simp only [Draft.lines, hpackage, scanLines, and_self, ite_true, dropPrefix_append,
      List.singleton_append, htables, pure_bind]
    simp only [Draft.tables, hterms, hreplaced]
    cases d
    simp_all

theorem not_mem_row {c : Char} {cells : List (List Char)} (hc : c ≠ '|') (hspace : c ≠ ' ')
    (h : ∀ cell ∈ cells, c ∉ cell) : c ∉ row cells := by
  intro hmem
  simp only [row, terminated, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_append]
    at hmem
  rcases hmem with hmem | ⟨part, ⟨cell, hcell, rfl⟩, hmem | hmem⟩
  · exact hc hmem
  · simp [hspace, h cell hcell] at hmem
  · simp [hc] at hmem

theorem not_mem_printTables (headings : List Heading)
    (hheadings : ∀ heading ∈ headings, '\n' ∉ heading.title ∧ '\n' ∉ row heading.columns ∧
      '\n' ∉ heading.rule) :
    ∀ (tables : List (List (List (List Char)))),
      (∀ rows ∈ tables, ∀ cells ∈ rows, ∀ cell ∈ cells, '\n' ∉ cell) →
      ∀ line ∈ printTables headings tables, '\n' ∉ line := by
  induction headings with
  | nil => intro tables _ line hline; simp [printTables] at hline
  | cons heading headings ih =>
    intro tables hclean line hline
    cases tables with
    | nil => simp [printTables] at hline
    | cons rows tables =>
      have hheading := hheadings heading (List.mem_cons_self ..)
      simp only [printTables, List.mem_append] at hline
      rcases hline with hline | hline
      · by_cases hrows : rows.isEmpty = true
        · simp [table, hrows] at hline
        · simp only [table, hrows, Bool.false_eq_true, ite_false, List.mem_cons, List.mem_map]
            at hline
          rcases hline with rfl | rfl | rfl | rfl | rfl | ⟨cells, hcells, rfl⟩
          · simp
          · exact hheading.1
          · simp
          · exact hheading.2.1
          · exact hheading.2.2
          · exact not_mem_row (by decide) (by decide)
              (hclean rows (List.mem_cons_self ..) cells hcells)
      · exact ih (fun h m => hheadings h (List.mem_cons_of_mem _ m)) tables
          (fun r m => hclean r (List.mem_cons_of_mem _ m)) line hline

theorem headings_lines : ∀ heading ∈ headings,
    '\n' ∉ heading.title ∧ '\n' ∉ row heading.columns ∧ '\n' ∉ heading.rule := by decide

/-- The scanner reads the print of a clean draft back as that draft. -/
theorem scan_render (d : Draft) (h : d.clean = true) : scan d.render = pure d := by
  have hlines : ∀ line ∈ d.lines, '\n' ∉ line := by
    intro line hline
    have hfields := h
    simp only [Draft.clean, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at hfields
    simp only [Draft.lines, List.mem_cons, List.mem_append] at hline
    rcases hline with rfl | rfl | rfl | rfl | hline | hline
    · decide
    · simp
    · simp only [List.mem_append, not_or]
      exact ⟨by decide, hfields.1.1⟩
    · decide
    · cases hpackage : d.shared with
      | none => simp [hpackage] at hline
      | some package =>
        simp only [hpackage, List.mem_singleton] at hline
        subst hline
        have := hfields.1.2
        simp only [hpackage, Option.all_some, Bool.not_eq_true', decide_eq_false_iff_not]
          at this
        simp only [List.mem_append, not_or]
        exact ⟨by decide, this⟩
    · exact not_mem_printTables headings headings_lines d.tables
        (fun rows hrows cells hcells cell hcell =>
          (d.clean_cells h rows hrows cells hcells cell hcell).2) line hline
  simp [scan, linesOf, Draft.render, split_terminated '\n' hlines, scanLines_lines d h]

/-! ## Defects -/

/-- The categories of rule 1.5, for a noun: `1` to `22`. -/
def nounCategories : List (List Char) :=
  ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17",
    "18", "19", "20", "21", "22"].map String.toList

/-- The categories of rule 1.12, for a verb: `1a` to `1f`, `2a` to `2c`, `3a` to `3f` and
`4`. -/
def verbCategories : List (List Char) :=
  ["1a", "1b", "1c", "1d", "1e", "1f", "2a", "2b", "2c", "3a", "3b", "3c", "3d", "3e", "3f",
    "4"].map String.toList

/-- Whether `text` is a number in decimal digits with no zero before it. -/
def numeral (text : List Char) : Bool :=
  !text.isEmpty && text.all Char.isDigit && (text.head? != some '0' || text.length == 1)

/-- Whether `text` is one sentence, as the vocabulary decides it on a cell's characters: it has
1 to 25 parts between single spaces, none of them empty, its last character is a period, and no
part before the last one ends with a period, a question mark or an exclamation mark. -/
def sentence (text : List Char) : Bool :=
  let parts := split ' ' text
  parts.all (!·.isEmpty) && parts.length ≤ 25 && text.getLast? == some '.' &&
    parts.dropLast.all fun part =>
      part.getLast? != some '.' && part.getLast? != some '?' && part.getLast? != some '!'

/-- The names in a `Replaces` cell: none for `-`, and otherwise its parts between commas, each
without the space after the comma. -/
def namesOf (cell : List Char) : List (List Char) :=
  if cell = ['-'] then []
  else (split ',' cell).map fun part => if part.head? = some ' ' then part.drop 1 else part

/-- The text of a `Replaces` cell with `names`. -/
def printNames (names : List (List Char)) : List Char :=
  if names.isEmpty then ['-'] else [',', ' '].intercalate names

/-- The path in a `Source` cell: its text between the first two backticks. -/
def pathOf (cell : List Char) : List Char := (cell.drop 1).takeWhile (· != '`')

/-- The Lean name in a `Source` cell, when text follows the path. -/
def leanNameOf (cell : List Char) : Option (List Char) :=
  match ((cell.drop 1).dropWhile (· != '`')).drop 1 with
  | [] => none
  | after => some ((after.drop 3).takeWhile (· != '`'))

/-- The text of a `Source` cell with `path` and `name`. -/
def printSource (path : List Char) (name : Option (List Char)) : List Char :=
  '`' :: path ++ '`' ::
    match name with
    | none => []
    | some name => " (`".toList ++ name ++ "`)".toList

/-- Whether `text` is not empty and has no space character and no backtick. -/
def solid (text : List Char) : Bool :=
  !text.isEmpty && text.all fun c => !spacing c && c != '`'

/-- The words of the term of `t`, in lowercase. -/
def Term.words (t : Term) : List (List Char) := (Controlled.words t.term).map lower

/-- The names `t` replaces, each as its words in lowercase. -/
def Term.names (t : Term) : List (List (List Char)) :=
  (namesOf t.replaces).map fun name => (Controlled.words name).map lower

/-- The path of the tracked file that defines `t`. -/
def Term.path (t : Term) : List Char := pathOf t.source

/-- The Lean name that defines `t`, if its row gives one. -/
def Term.leanName (t : Term) : Option (List Char) := leanNameOf t.source

/-- What is wrong with one row of terms whose category must be one of `categories`. -/
def Term.defects (categories : List (List Char)) (t : Term) : List String :=
  (if phrase t.term && (Controlled.words t.term).length ≤ 3 then []
    else ["the term is not one to three words with one space between them"]) ++
  (if categories.contains t.category then []
    else [s!"the category is not one of {", ".intercalate (categories.map String.ofList)}"]) ++
  (if sentence t.definition then []
    else ["the definition is not one sentence of 25 words or less that ends with a period"]) ++
  (if t.replaces == printNames (namesOf t.replaces) && (namesOf t.replaces).all phrase then []
    else ["the replaced names are not `-` or names with `, ` between them"]) ++
  (if t.source == printSource (pathOf t.source) (leanNameOf t.source) && solid (pathOf t.source) &&
      (leanNameOf t.source).all solid then []
    else ["the source is not a path in backticks, with or without a Lean name in backticks \
      and parentheses after it"])

/-- What is wrong with one row of replaced words. -/
def Replaced.defects (r : Replaced) : List String :=
  (if phrase r.word && (words r.word).length == 1 then []
    else ["the replaced word is not one word"]) ++
  (if (split ' ' r.write).all (!·.isEmpty) then []
    else ["the text to write is empty, or has a space at its start, at its end or after a space"])

/-- The lines whose keys are not after the key of the line before them, each with that key. -/
def unordered : List (List Char × List Char) → List (List Char × String)
  | (_, first) :: (line, second) :: rest =>
    (if first < second then []
      else [(line, s!"this row is not after the row `{String.ofList first}` in the order of \
        the lowercase terms")]) ++ unordered ((line, second) :: rest)
  | _ => []

/-- The lines whose key is also the key of an earlier line. -/
def repeated (seen : List (List Char)) : List (List Char × List Char) → List (List Char × String)
  | [] => []
  | (line, key) :: rest =>
    (if seen.contains key then [(line, s!"`{String.ofList key}` is given two times")] else []) ++
      repeated (key :: seen) rest

/-- The rows of terms of `d` with the line of each, in the order of the print. -/
def Draft.terms (d : Draft) : List Term :=
  d.sharedNouns ++ d.sharedVerbs ++ d.projectNouns ++ d.projectVerbs

/-- Each name that a row of `d` replaces, in lowercase with one space between its words, with
the line of its row. -/
def Draft.names (d : Draft) : List (List Char × List Char) :=
  d.terms.flatMap fun t => (namesOf t.replaces).map fun name => (row t.cells, lower name)

/-- The defects of `d`, each with the line of the print it is about, if it is about one. -/
def Draft.defects (d : Draft) : List (Option (List Char) × String) :=
  let keyed (terms : List Term) : List (List Char × List Char) :=
    terms.map fun t => (row t.cells, lower t.term)
  let nouns := keyed (d.sharedNouns ++ d.projectNouns)
  let verbs := keyed (d.sharedVerbs ++ d.projectVerbs)
  let replaced := d.replaced.map fun r => (row r.cells, lower r.word)
  let taken := d.names.map (·.2) ++ replaced.map (·.2)
  (if numeral d.version then [] else [(none, "the vocabulary version is not a number")]) ++
  (match d.shared with
    | none => []
    | some package =>
      (if solid package then []
        else [(none, "the package of the shared vocabulary is not a name without spaces")]) ++
      (if d.sharedNouns.isEmpty && d.sharedVerbs.isEmpty then []
        else [(none, "a vocabulary that names a shared vocabulary has no `Shared` table")])) ++
  ((d.sharedNouns ++ d.projectNouns).flatMap fun t =>
    (t.defects nounCategories).map fun reason => (some (row t.cells), reason)) ++
  ((d.sharedVerbs ++ d.projectVerbs).flatMap fun t =>
    (t.defects verbCategories).map fun reason => (some (row t.cells), reason)) ++
  (d.replaced.flatMap fun r => r.defects.map fun reason => (some (row r.cells), reason)) ++
  ((unordered (keyed d.sharedNouns) ++ unordered (keyed d.sharedVerbs) ++
      unordered (keyed d.projectNouns) ++ unordered (keyed d.projectVerbs) ++
      unordered replaced ++ repeated [] nouns ++ repeated [] verbs ++
      repeated [] d.names).map fun (line, reason) => (some line, reason)) ++
  ((nouns ++ verbs).filterMap fun (line, term) =>
    if taken.contains term then
      some (some line, s!"the term `{String.ofList term}` is also a replaced name or a \
        replaced word")
    else none) ++
  (d.names.filterMap fun (line, name) =>
    if (replaced.map (·.2)).contains name then
      some (some line, s!"the replaced name `{String.ofList name}` is also a replaced word")
    else none)

/-- Whether `d` is clean and has no defect. -/
def Draft.valid (d : Draft) : Bool := d.clean && d.defects.isEmpty

/-! ## Vocabularies -/

/-- The vocabulary of a project: a draft that is clean and has no defect. -/
structure Vocabulary where
  /-- The cells of the tables. -/
  draft : Draft
  /-- The draft is clean and has no defect. -/
  valid : draft.valid = true

theorem Vocabulary.ext {v w : Vocabulary} (h : v.draft = w.draft) : v = w := by
  cases v; cases w; cases h; rfl

/-- The text of `v`: the one text `parse` reads as `v`. -/
def write (v : Vocabulary) : String := String.ofList v.draft.render

/-- The vocabulary whose text is `text`, if `text` is the text of one. -/
@[regula_decision]
def parse (text : String) : Option Vocabulary :=
  match scan text.toList with
  | .ok d => if h : d.valid = true ∧ d.render = text.toList then some ⟨d, h.1⟩ else none
  | .error _ => none

theorem parse_write (v : Vocabulary) : parse (write v) = some v := by
  have hclean : v.draft.clean = true := by
    have := v.valid
    simp only [Draft.valid, Bool.and_eq_true] at this
    exact this.1
  have hscan : scan v.draft.render = .ok v.draft := scan_render v.draft hclean
  simp only [parse, write, String.toList_ofList, hscan]
  split
  · rfl
  · rename_i hrefused
    exact absurd ⟨v.valid, trivial⟩ hrefused

theorem write_of_parse (text : String) (v : Vocabulary) (h : parse text = some v) :
    write v = text := by
  unfold parse at h
  split at h
  · split at h
    · rename_i d _ hd
      cases h
      simp [write, hd.2, String.ofList_toList]
    · cases h
  · cases h

/-- The vocabulary with version 1 and no row. -/
def Vocabulary.empty : Vocabulary := ⟨⟨['1'], none, [], [], [], [], []⟩, by decide⟩

/-- Registered contract of the vocabulary parser (check C9), as a two-way decision: it accepts
exactly the texts that are the print of a vocabulary. It accepts the print of the vocabulary
with no row and refuses the empty text. -/
theorem checked_parse : Regula.ExecutableContract parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ v, text = write v)) :=
  ⟨.of_roundtrip parse_write write_of_parse Vocabulary.empty (unwritten := "") (by decide)⟩

/-- The terms of `v`, each as its words in lowercase. -/
def Vocabulary.terms (v : Vocabulary) : List (List (List Char)) := v.draft.terms.map Term.words

/-- The names `v` replaces, each as its words in lowercase, with the term to write. -/
def Vocabulary.names (v : Vocabulary) : List (List (List Char) × List Char) :=
  v.draft.terms.flatMap fun t => t.names.map fun name => (name, t.term)

/-- The words `v` does not write, each in lowercase, with what to write. -/
def Vocabulary.replaced (v : Vocabulary) : List (List Char × List Char) :=
  v.draft.replaced.map fun r => (lower r.word, r.write)

/-! ## Why a text is refused -/

/-- The number of the first line at which `left` and `right` differ, counting from `n`. -/
def firstDifference (n : Nat) : List (List Char) → List (List Char) → Nat
  | a :: left, b :: right => if a = b then firstDifference (n + 1) left right else n
  | _, _ => n

/-- Why `text` is not the text of a vocabulary: each reason, with the number of its line when
it is about one line. -/
def explain (text : String) : List (Option Nat × String) :=
  match scan text.toList with
  | .error (remaining, reason) => [(some ((linesOf text.toList).length + 1 - remaining), reason)]
  | .ok d =>
    if d.render = text.toList then
      if d.valid then []
      else
        (if d.clean then [] else [(none, "a cell has a `|` character or a line feed")]) ++
          d.defects.map fun (line, reason) => (line.map fun line => d.lines.idxOf line + 1, reason)
    else
      [(some (firstDifference 1 d.lines (split '\n' text.toList)),
        "the text is not the print of its vocabulary from this line on (a missing line feed \
          at the end of the text, or a line that the print writes otherwise)")]

/-- `explain` reports nothing exactly when `parse` accepts the text. -/
theorem explain_nil_iff (text : String) : explain text = [] ↔ (parse text).isSome = true := by
  unfold explain parse
  cases hscan : scan text.toList with
  | error refusal => simp
  | ok d =>
    by_cases hrender : d.render = text.toList
    · by_cases hvalid : d.valid = true
      · simp [hrender, hvalid]
      · simp only [hrender, hvalid, Bool.false_eq_true, ite_false, ite_true, and_true, dite_false,
          Option.isSome_none, iff_false, List.append_eq_nil_iff, List.map_eq_nil_iff, not_and]
        intro hclean hdefects
        have hc : d.clean = true := by
          by_cases hc : d.clean = true
          · exact hc
          · simp [hc] at hclean
        exact hvalid (by simp [Draft.valid, hc, hdefects])
    · simp [hrender]

/-! ## Sources and shared tables -/

/-- The source paths of `v` that are not among `tracked`, in the order of the print. -/
@[regula_decision]
def untracked (tracked : List String) (v : Vocabulary) : List String :=
  (v.draft.terms.map fun t => String.ofList t.path).filter fun path => !tracked.contains path

/-- Registered contract of the check of source paths (a part of check C9), as a two-way
decision: no path is reported exactly when the source path of every row is one of the tracked
paths. The vocabulary with no row is accepted for no tracked path, and a vocabulary with one row
is refused for no tracked path. -/
theorem checked_untracked : Regula.ExecutableContract untracked (fun run =>
    Regula.Decides (· = [])
      (fun input : List String × Vocabulary =>
        ∀ t ∈ input.2.draft.terms, String.ofList t.path ∈ input.1)
      (Function.uncurry run)) :=
  ⟨.of_iff
    (fun input => by
      simp [Function.uncurry, untracked, List.filter_eq_nil_iff])
    ⟨([], Vocabulary.empty), by decide⟩
    ⟨([], ⟨⟨['1'], none, [⟨"a".toList, "1".toList, "A.".toList, "-".toList, "`a`".toList⟩], [], [],
        [], []⟩, by decide⟩), by decide⟩⟩

/-- The draft of `project` with the `Shared` tables of `shared` and no shared package. -/
def Draft.adopt (shared project : Draft) : Draft :=
  { project with
    shared := none, sharedNouns := shared.sharedNouns, sharedVerbs := shared.sharedVerbs }

/-- The vocabulary `project` together with the `Shared` tables of `shared`, the vocabulary of
the package it names: defined when `project` names a shared vocabulary, `shared` names none, and
the tables together have no defect. -/
@[regula_decision]
def adopt (shared project : Vocabulary) : Option Vocabulary :=
  if h : (project.draft.shared.isSome ∧ shared.draft.shared.isNone) ∧
      (shared.draft.adopt project.draft).valid = true then
    some ⟨shared.draft.adopt project.draft, h.2⟩
  else none

/-- Registered contract of the adoption of shared tables (a part of check C9), as a two-way
decision: it succeeds exactly when the project vocabulary names a shared vocabulary, the shared
one names none, and the tables together are clean and have no defect. It refuses a project
vocabulary that names no shared vocabulary and accepts one that does. -/
theorem checked_adopt : Regula.ExecutableContract adopt (fun run =>
    Regula.Decides (·.isSome = true)
      (fun input : Vocabulary × Vocabulary =>
        (input.2.draft.shared.isSome ∧ input.1.draft.shared.isNone) ∧
          (input.1.draft.adopt input.2.draft).valid = true)
      (Function.uncurry run)) :=
  ⟨.of_iff
    (fun input => by
      simp only [Function.uncurry, adopt]
      split <;> simp_all)
    ⟨(Vocabulary.empty, ⟨⟨['1'], some ['a'], [], [], [], [], []⟩, by decide⟩), by decide⟩
    ⟨(Vocabulary.empty, Vocabulary.empty), by decide⟩⟩

end Regula.Controlled
