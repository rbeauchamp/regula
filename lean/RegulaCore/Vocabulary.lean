import Regula.Contract
import Regula.Decision
import RegulaCore.ControlledText

/-! # The vocabulary of a project

`CONTEXT.md` at the root of a repository gives the technical nouns and technical verbs of the
project, the names each one replaces, and the words the project does not write. This module
defines that file exactly: the type `Vocabulary`, its one text (`write`), and the parser that
accepts a text only when it is that text (`parse`).

The writing guide (`docs/guides/writing.md`) states the rules for a writer. Nothing here is a
rule of Regula's standard: this is a check of a repository's own documents (check C9).

## Main declarations

- `split`, `split_joined`, `joined_split`: a text divided at a character, and the text that
  division inverts.
- `Separated`, `separated_iff`: a text that is parts with one separator between two parts.
- `Word`, `Phrase`, `OneSentence`: a word and a phrase of the vocabulary, and a definition that
  is one sentence by the definition of `RegulaCore.ControlledText`. A word of the vocabulary is
  a word whose form for a comparison (`Normal`) is its lowercase.
- `Term`, `Replaced`, `Draft`: the rows of the tables.
- `Draft.render`, `scan`, `scan_render`: the print of a draft, and the scanner that reads every
  print of a clean draft back.
- `Term.Sound`, `Replaced.Sound`, `Draft.WellFormed`: what a vocabulary is, stated on its rows.
- `Draft.defects`, `Draft.defects_nil_iff`: the defects of a draft, each with the line of the
  print it is about. A draft has none exactly when it is well formed.
- `Vocabulary`, `write`, `parse`, `checked_parse`: the parser is a two-way decision of "is the
  print of a vocabulary" (`Regula.Decides.of_roundtrip`).
- `explain`, `explain_nil_iff`: why a text is refused, by line. It reports nothing exactly when
  `parse` accepts.
- `untracked`, `checked_untracked`: the rows whose source path is not among the tracked files of
  their repository.
- `adopt`, `checked_adopt`, `clashes`: a project vocabulary together with the `Shared` tables of
  the vocabulary it names.

## The text

A print has a title, two or three head lines, and then up to five tables, each present only when
it has a row: `Shared technical nouns`, `Shared technical verbs`, `Project technical nouns`,
`Project technical verbs` and `Replaced words`, in that order. Each row is one line. `write` is
the definition of the grammar: `Term.cells`, `printNames` and `printSource` give the text of each
cell. The scanner is proved against that print (`scan_render`), and `parse` accepts a text only
when the print of what it reads is that text.

## Specifications

`Draft.WellFormed` is a statement about the rows, with no call of a function that searches or
recurses. `Draft.defects` and the other functions of a decision use no definition that a
specification uses: where a function needs one, it has a second definition in the namespace
`Exec`, with a theorem that the two are equal, as in `RegulaCore.ControlledText`. The data types
are the only declarations that a specification and its function share. A clause that needs a
search has a theorem that says its function is exact: `separated_iff` for the words of a term
and of a name, `normal_iff` for the form of a word, and `oneSentence_iff` for a definition.

## Boundaries

`checked_parse` is about the text given to `parse`. That the text is the file's, and that the
paths given to `untracked` are the paths Git tracks, rests on the file system and on Git, which
the executable reads (`markdown/MarkdownMain.lean`). A definition's one-sentence rule is decided
on the characters of the cell, without a Markdown parser: a check of the document reads the same
cell again as a part of the document.
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

theorem split_ne_nil (separator : Char) (text : List Char) : split separator text ≠ [] := by
  cases text with
  | nil => simp [split]
  | cons c rest =>
    simp only [split]
    split
    · simp
    · split <;> simp

/-- No part of a divided text has the separator. -/
theorem not_mem_of_mem_split (separator : Char) :
    ∀ (text : List Char), ∀ part ∈ split separator text, separator ∉ part
  | [] => by simp [split]
  | c :: rest => by
    intro part hpart
    have ih := not_mem_of_mem_split separator rest
    simp only [split] at hpart
    split at hpart
    · rcases List.mem_cons.mp hpart with rfl | hpart
      · simp
      · exact ih part hpart
    · rename_i hc
      split at hpart
      · simp only [List.mem_singleton] at hpart
        subst hpart
        simpa using Ne.symm hc
      · rename_i first parts hsplit
        rcases List.mem_cons.mp hpart with rfl | hpart
        · have := ih first (by rw [hsplit]; exact List.mem_cons_self ..)
          simpa [this] using Ne.symm hc
        · exact ih part (by rw [hsplit]; exact List.mem_cons_of_mem _ hpart)

/-- Dividing at the separator reads the parts of a text back, when no part has the separator:
the first part, and then each other part after one separator. -/
theorem split_joined (separator : Char) (first : List Char) (rest : List (List Char))
    (h : ∀ part ∈ first :: rest, separator ∉ part) :
    split separator (first ++ rest.flatMap (separator :: ·)) = first :: rest := by
  induction rest generalizing first with
  | nil => simpa using split_of_not_mem separator (h first (List.mem_cons_self ..))
  | cons part rest ih =>
    have hfirst := h first (List.mem_cons_self ..)
    have hrest := ih part (fun p hp => h p (List.mem_cons_of_mem _ hp))
    simp only [List.flatMap_cons, List.cons_append]
    rw [split_append separator _ hfirst, hrest]

/-- A text is the parts of its division: the first part, and then each other part after one
separator. -/
theorem joined_split (separator : Char) (text : List Char) :
    ∃ first rest, split separator text = first :: rest ∧
      text = first ++ rest.flatMap (separator :: ·) := by
  induction text with
  | nil => exact ⟨[], [], rfl, rfl⟩
  | cons c text ih =>
    obtain ⟨first, rest, hsplit, htext⟩ := ih
    by_cases hc : c = separator
    · subst hc
      exact ⟨[], first :: rest, by simp [split, hsplit], by simp [← htext]⟩
    · exact ⟨c :: first, rest, by simp [split, hc, hsplit], by simp [← htext]⟩

/-! ## Parts with a separator -/

/-- `text` is one part or more with one `separator` between two parts: the first part, and then
each other part after one separator. No part has the separator, and the parts in order have
`P`. -/
def Separated (separator : Char) (P : List (List Char) → Prop) (text : List Char) : Prop :=
  ∃ first rest, text = first ++ rest.flatMap (separator :: ·) ∧
    (∀ part ∈ first :: rest, separator ∉ part) ∧ P (first :: rest)

/-- A text is separated parts with `P` exactly when its division at the separator has `P`. -/
theorem separated_iff (separator : Char) (P : List (List Char) → Prop) (text : List Char) :
    Separated separator P text ↔ P (split separator text) := by
  constructor
  · rintro ⟨first, rest, rfl, hparts, hP⟩
    rwa [split_joined separator first rest hparts]
  · intro hP
    obtain ⟨first, rest, hsplit, htext⟩ := joined_split separator text
    refine ⟨first, rest, htext, fun part hpart => ?_, hsplit ▸ hP⟩
    exact not_mem_of_mem_split separator text part (hsplit ▸ hpart)

/-! ## Words, phrases and sentences of the vocabulary -/

/-- A word of the vocabulary: ASCII letters, digits, hyphens and apostrophes, one or more, whose
form for a comparison (`Normal`) is its lowercase. Thus it has no hyphen and no apostrophe at
its start or at its end, and a comparison of its lowercase with the form of a word of prose is a
comparison of two forms. Between two characters that are none of these, it is one word of prose
(`Regula.Controlled.Part.Word`). -/
def Word (word : List Char) : Prop :=
  word ≠ [] ∧ (∀ c ∈ word, (roleOf c).Wordy) ∧ Normal word (word.map Char.toLower)

/-- One word or more, with one space between two words. -/
abbrev Phrase (text : List Char) : Prop :=
  Separated ' ' (fun words => ∀ word ∈ words, Word word) text

/-- A number in decimal digits with no zero before it. -/
abbrev Numeral (text : List Char) : Prop :=
  text ≠ [] ∧ (∀ c ∈ text, c.isDigit = true) ∧ (text.head? = some '0' → text = ['0'])

/-- A text that is not empty and has no space character, no backtick and no `|` character. -/
abbrev Solid (text : List Char) : Prop :=
  text ≠ [] ∧ ∀ c ∈ text, spacing c = false ∧ c ≠ '`' ∧ c ≠ '|'

/-- `text` is one sentence of 25 words or less that ends with a period: its last character is a
period, and the division of its characters into the runs that sentences are (`Divided`) has
exactly one run with a word, of 25 words or less. -/
def OneSentence (text : List Char) : Prop :=
  text.getLast? = some '.' ∧
    ∃ cut sentence, Divided (text.map Atom.plain) cut ∧
      cut.filter (fun run => decide (Worded run)) = [sentence] ∧ wordCount sentence ≤ 25

/-- Whether `text` is one sentence of 25 words or less that ends with a period. -/
def oneSentence (text : List Char) : Bool :=
  text.getLast? = some '.' &&
    match (divide (text.map Exec.plain)).filter fun run => decide (Exec.Worded run) with
    | [sentence] => Exec.wordCount sentence ≤ 25
    | _ => false

/-- `oneSentence` is exact for `OneSentence`. -/
theorem oneSentence_iff (text : List Char) : oneSentence text = true ↔ OneSentence text := by
  constructor
  · intro h
    simp only [oneSentence, Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨h.1, divide (text.map Atom.plain), ?_⟩
    split at h
    · rename_i sentence hfilter
      exact ⟨sentence, (divided_iff _ _).mpr rfl, hfilter, of_decide_eq_true h.2⟩
    · exact absurd h.2 (by simp)
  · rintro ⟨hlast, cut, sentence, hcut, hfilter, hcount⟩
    rw [divided_iff] at hcut
    subst hcut
    have hfilter' : (divide (text.map Exec.plain)).filter (fun run => decide (Exec.Worded run)) =
        [sentence] := hfilter
    have hcount' : Exec.wordCount sentence ≤ 25 := hcount
    simp [oneSentence, hlast, hfilter', hcount']

/-! ## The tables as written -/

/-- One row of a table of terms. -/
structure Term where
  /-- The term: one to three words. -/
  term : List Char
  /-- The category of rule 1.5 (a noun) or of rule 1.12 (a verb), as a number or a number and a
  letter. -/
  category : List Char
  /-- The definition: one sentence. -/
  definition : List Char
  /-- The names the term replaces. -/
  replaces : List (List Char)
  /-- The path of the tracked file that defines the term. -/
  path : List Char
  /-- The Lean name that defines the term, if the row gives one. -/
  name : Option (List Char)
  deriving DecidableEq, Repr

/-- One row of the table of replaced words: the text of its two cells. -/
structure Replaced where
  /-- The word the project does not write. -/
  word : List Char
  /-- What to write. -/
  write : List Char
  deriving DecidableEq, Repr

/-- A vocabulary as written, before its defects are decided. -/
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

/-- The rows of terms of `d`, in the order of the print. -/
def Draft.rows (d : Draft) : List Term :=
  d.sharedNouns ++ d.sharedVerbs ++ d.projectNouns ++ d.projectVerbs

/-- The text of a `Replaces` cell: `-` for no name, and otherwise the names with a comma and a
space between two names. -/
def printNames : List (List Char) → List Char
  | [] => ['-']
  | first :: rest => first ++ rest.flatMap fun name => ',' :: ' ' :: name

/-- The names in a `Replaces` cell: none for `-`, and otherwise its parts between commas, each
part after the first without its first character. -/
def namesOf (cell : List Char) : List (List Char) :=
  if cell = ['-'] then []
  else
    match split ',' cell with
    | [] => []
    | first :: rest => first :: rest.map (·.drop 1)

/-- The names of a printed `Replaces` cell are read back, when no name has a comma and the names
are not the one name `-`. -/
theorem namesOf_printNames {names : List (List Char)} (hcomma : ∀ name ∈ names, ',' ∉ name)
    (hdash : names ≠ [['-']]) : namesOf (printNames names) = names := by
  cases names with
  | nil => rfl
  | cons first rest =>
    have hform : printNames (first :: rest) =
        first ++ (rest.map (' ' :: ·)).flatMap (',' :: ·) := by
      simp [printNames, List.flatMap_map]
    have hparts : ∀ part ∈ first :: rest.map (' ' :: ·), ',' ∉ part := by
      intro part hpart
      rcases List.mem_cons.mp hpart with rfl | hpart
      · exact hcomma _ (List.mem_cons_self ..)
      · obtain ⟨name, hname, rfl⟩ := List.mem_map.mp hpart
        have := hcomma name (List.mem_cons_of_mem _ hname)
        simp [this]
    have hne : printNames (first :: rest) ≠ ['-'] := by
      intro heq
      cases rest with
      | nil =>
        simp only [printNames, List.flatMap_nil, List.append_nil] at heq
        exact hdash (by rw [heq])
      | cons name rest =>
        have : ',' ∈ printNames (first :: name :: rest) := by simp [printNames]
        rw [heq] at this
        simp at this
    have hsplit := split_joined ',' first _ hparts
    rw [← hform] at hsplit
    simp [namesOf, hne, hsplit, List.map_map, Function.comp_def]

/-- The text of a `Source` cell: the path in backticks, and then the Lean name, if there is one,
in backticks and parentheses. -/
def printSource (path : List Char) (name : Option (List Char)) : List Char :=
  '`' :: path ++ '`' ::
    match name with
    | none => []
    | some name => ' ' :: '(' :: '`' :: name ++ ['`', ')']

/-- The path and the Lean name in a `Source` cell. A cell that is not the print of a source is
read as a path, which its print then differs from. -/
def sourceOf (cell : List Char) : List Char × Option (List Char) :=
  match split '`' cell with
  | [[], path, []] => (path, none)
  | [[], path, [' ', '('], name, [')']] => (path, some name)
  | _ => (cell, none)

/-- The path and the Lean name of a printed `Source` cell are read back, when neither has a
backtick. -/
theorem sourceOf_printSource {path : List Char} {name : Option (List Char)}
    (hpath : '`' ∉ path) (hname : ∀ n ∈ name, '`' ∉ n) :
    sourceOf (printSource path name) = (path, name) := by
  cases name with
  | none =>
    have hform : printSource path none = [] ++ [path, []].flatMap ('`' :: ·) := by
      simp [printSource]
    rw [sourceOf, hform, split_joined '`' [] [path, []] (by simp [hpath])]
  | some n =>
    have hn := hname n rfl
    have hform : printSource path (some n) =
        [] ++ [path, [' ', '('], n, [')']].flatMap ('`' :: ·) := by
      simp [printSource]
    have hsplit := split_joined '`' [] [path, [' ', '('], n, [')']] (by simp [hpath, hn])
    rw [← hform] at hsplit
    simp [sourceOf, hsplit]

/-- The cells of a row of terms. -/
def Term.cells (t : Term) : List (List Char) :=
  [t.term, t.category, t.definition, printNames t.replaces, printSource t.path t.name]

/-- The row of terms with these cells. -/
def Term.ofCells : List (List Char) → Option Term
  | [term, category, definition, replaces, source] =>
    some ⟨term, category, definition, namesOf replaces, (sourceOf source).1, (sourceOf source).2⟩
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

/-! ## The definitions that the functions use

The parser reads a text and then compares it with the print of what it read. The functions
that follow use the second definitions of the namespace `Exec`, as in
`RegulaCore.ControlledText`: a change to a definition of the print does not change the print
that the parser compares, and it makes the theorem that the two are equal fail. -/

namespace Exec

/-- Each of `parts` with `terminator` after it, for the functions (`terminated_eq`). -/
def terminated (terminator : Char) (parts : List (List Char)) : List Char :=
  parts.flatMap (· ++ [terminator])

/-- `text` in lowercase, for the functions (`lower_eq`). -/
def lower (text : List Char) : List Char := text.map Char.toLower

/-- The text of a `Replaces` cell, for the functions (`printNames_eq`). -/
def printNames : List (List Char) → List Char
  | [] => ['-']
  | first :: rest => first ++ rest.flatMap fun name => ',' :: ' ' :: name

/-- The text of a `Source` cell, for the functions (`printSource_eq`). -/
def printSource (path : List Char) (name : Option (List Char)) : List Char :=
  '`' :: path ++ '`' ::
    match name with
    | none => []
    | some name => ' ' :: '(' :: '`' :: name ++ ['`', ')']

/-- The cells of a row of terms, for the functions (`termCells_eq`). -/
def termCells (t : Term) : List (List Char) :=
  [t.term, t.category, t.definition, printNames t.replaces, printSource t.path t.name]

/-- The cells of a row of replaced words, for the functions (`replacedCells_eq`). -/
def replacedCells (r : Replaced) : List (List Char) := [r.word, r.write]

/-- The line of a table row, for the functions (`row_eq`). -/
def row (cells : List (List Char)) : List Char :=
  '|' :: terminated '|' (cells.map fun cell => ' ' :: cell ++ [' '])

/-- The line under the column names, for the functions (`rule_eq`). -/
def rule (heading : Heading) : List Char :=
  row (heading.columns.map fun _ => "---".toList)

/-- The lines of a table, for the functions (`table_eq`). -/
def table (heading : Heading) (rows : List (List (List Char))) : List (List Char) :=
  if rows.isEmpty then []
  else [] :: heading.title :: [] :: row heading.columns :: rule heading :: rows.map row

/-- The lines of tables, for the functions (`printTables_eq`). -/
def printTables : List Heading → List (List (List (List Char))) → List (List Char)
  | heading :: headings, rows :: tables => table heading rows ++ printTables headings tables
  | _, _ => []

/-- The columns of a table of terms, for the functions (`termColumns_eq`). -/
def termColumns : List (List Char) :=
  ["Term", "Category", "Definition", "Replaces", "Source"].map String.toList

/-- The five tables, for the functions (`headings_eq`). -/
def headings : List Heading := [
  ⟨"## Shared technical nouns".toList, termColumns⟩,
  ⟨"## Shared technical verbs".toList, termColumns⟩,
  ⟨"## Project technical nouns".toList, termColumns⟩,
  ⟨"## Project technical verbs".toList, termColumns⟩,
  ⟨"## Replaced words".toList, ["Do not write", "Write"].map String.toList⟩]

/-- The first line of the print, for the functions (`titleLine_eq`). -/
def titleLine : List Char := "# CONTEXT".toList

/-- The text before the version, for the functions (`versionLabel_eq`). -/
def versionLabel : List Char := "Vocabulary version: ".toList

/-- The line that names the edition, for the functions (`standardLine_eq`). -/
def standardLine : List Char := "Standard: ASD-STE100 Issue 9".toList

/-- The text before the shared package, for the functions (`sharedLabel_eq`). -/
def sharedLabel : List Char := "Shared vocabulary: ".toList

/-- The rows of terms of a draft, for the functions (`rows_eq`). -/
def rows (d : Draft) : List Term :=
  d.sharedNouns ++ d.sharedVerbs ++ d.projectNouns ++ d.projectVerbs

/-- The rows of the five tables as cells, for the functions (`tables_eq`). -/
def tables (d : Draft) : List (List (List (List Char))) :=
  [d.sharedNouns.map termCells, d.sharedVerbs.map termCells, d.projectNouns.map termCells,
    d.projectVerbs.map termCells, d.replaced.map replacedCells]

/-- The lines of the print of a draft, for the functions (`lines_eq`). -/
def lines (d : Draft) : List (List Char) :=
  titleLine :: [] :: (versionLabel ++ d.version) :: standardLine ::
    ((match d.shared with
      | none => []
      | some package => [sharedLabel ++ package]) ++ printTables headings (tables d))

/-- The print of a draft, for the functions (`render_eq`). -/
def render (d : Draft) : List Char := terminated '\n' (lines d)

/-- A word of the vocabulary, for the functions (`word_iff`). -/
def Word (word : List Char) : Prop :=
  word ≠ [] ∧ (∀ c ∈ word, Wordy (roleOf c)) ∧ word.map Char.toLower = normalize word

instance : DecidablePred Word := fun word => by
  unfold Word
  infer_instance

/-- A number in decimal digits with no zero before it, for the functions (`Numeral_eq`). -/
def Numeral (text : List Char) : Prop :=
  text ≠ [] ∧ (∀ c ∈ text, c.isDigit = true) ∧ (text.head? = some '0' → text = ['0'])

instance : DecidablePred Numeral := fun text => by
  unfold Numeral
  infer_instance

/-- A text that is not empty and has no space character, no backtick and no `|` character, for
the functions (`Solid_eq`). -/
def Solid (text : List Char) : Prop :=
  text ≠ [] ∧ ∀ c ∈ text, spacing c = false ∧ c ≠ '`' ∧ c ≠ '|'

instance : DecidablePred Solid := fun text => by
  unfold Solid
  infer_instance

theorem terminated_eq : @terminated = @Controlled.terminated := rfl
theorem lower_eq : @lower = @Controlled.lower := rfl
theorem printNames_eq : @printNames = @Controlled.printNames := rfl
theorem printSource_eq : @printSource = @Controlled.printSource := rfl
theorem termCells_eq : @termCells = @Term.cells := rfl
theorem replacedCells_eq : @replacedCells = @Replaced.cells := rfl
theorem row_eq : @row = @Controlled.row := rfl
theorem rule_eq : @rule = @Heading.rule := rfl
theorem table_eq : @table = @Controlled.table := rfl
theorem printTables_eq : @printTables = @Controlled.printTables := by
  funext headings tables
  induction headings generalizing tables with
  | nil => rfl
  | cons heading headings ih =>
    cases tables with
    | nil => rfl
    | cons rows tables =>
      show table heading rows ++ printTables headings tables =
        Controlled.table heading rows ++ Controlled.printTables headings tables
      rw [ih]
      rfl
theorem termColumns_eq : @termColumns = @Controlled.termColumns := rfl
theorem headings_eq : @headings = @Controlled.headings := rfl
theorem titleLine_eq : @titleLine = @Controlled.titleLine := rfl
theorem versionLabel_eq : @versionLabel = @Controlled.versionLabel := rfl
theorem standardLine_eq : @standardLine = @Controlled.standardLine := rfl
theorem sharedLabel_eq : @sharedLabel = @Controlled.sharedLabel := rfl
theorem rows_eq : @rows = @Draft.rows := rfl
theorem tables_eq : @tables = @Draft.tables := rfl
theorem lines_eq : @lines = @Draft.lines := rfl
theorem render_eq : @render = @Draft.render := rfl
theorem Numeral_eq : @Numeral = @Controlled.Numeral := rfl
theorem Solid_eq : @Solid = @Controlled.Solid := rfl

/-- The word of the functions is the word of the vocabulary. -/
theorem word_iff (word : List Char) : Word word ↔ Controlled.Word word :=
  and_congr_right fun _ => and_congr_right fun _ => (normal_iff _ _).symm

end Exec

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
        if columns = Exec.row heading.columns ∧ rule = Exec.rule heading then
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
              (Exec.row heading.columns)}` and `{String.ofList (Exec.rule heading)}`")
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
    {cells : α → List (List Char)} (values : List α)
    (h : ∀ value ∈ values, read (cells value) = some value) :
    readAll read (values.map cells) = some values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp [readAll, h value (List.mem_cons_self ..),
      ih fun v hv => h v (List.mem_cons_of_mem _ hv)]

/-- What a text that does not start with the head lines is refused for. -/
def headReason : String :=
  s!"expected the lines `{String.ofList Exec.titleLine}`, an empty line, \
    `{String.ofList Exec.versionLabel}` with the version, and \
    `{String.ofList Exec.standardLine}`"

/-- The draft whose print has `lines`. -/
def scanLines (lines : List (List Char)) : Scan Draft :=
  match lines with
  | first :: [] :: version :: standard :: rest =>
    if first = Exec.titleLine ∧ standard = Exec.standardLine then
      match dropPrefix Exec.versionLabel version with
      | none => throw (lines.length, headReason)
      | some version =>
        let (shared, rest) : Option (List Char) × List (List Char) :=
          match rest with
          | line :: more =>
            match dropPrefix Exec.sharedLabel line with
            | some package => (some package, more)
            | none => (none, rest)
          | [] => (none, rest)
        do
          let (tables, rest) ← takeTables Exec.headings rest
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
              s!"expected `{String.ofList Exec.sharedLabel}` with a package directly after the head \
                lines, or an empty line and the title of a table that is not yet read, in the \
                order of the tables, or the end of the text")
    else throw (lines.length, headReason)
  | _ => throw (lines.length, headReason)

/-- The lines of `text`: its parts between line feeds, without the part after the last one. -/
def linesOf (text : List Char) : List (List Char) := (split '\n' text).dropLast

/-- The draft whose print is `text`, if `text` has the form of a print. -/
def scan (text : List Char) : Scan Draft := scanLines (linesOf text)


/-! ## The scanner reads every print back -/

/-- What the scanner needs to read the print of `d` back. No cell and no head field has a `|`
character or a line feed, which would change the rows and the lines of the print. No replaced
name has a comma, and the names of a row are not the one name `-`. No path and no Lean name has
a backtick. -/
structure Draft.Clean (d : Draft) : Prop where
  /-- The version has no line feed. -/
  version : '\n' ∉ d.version
  /-- The package has no line feed. -/
  package : ∀ package ∈ d.shared, '\n' ∉ package
  /-- No cell has a `|` character or a line feed. -/
  cells : ∀ rows ∈ d.tables, ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell ∧ '\n' ∉ cell
  /-- The names and the source of each row are read back from their cells. -/
  rows : ∀ t ∈ d.rows, (∀ name ∈ t.replaces, ',' ∉ name) ∧ t.replaces ≠ [['-']] ∧
    '`' ∉ t.path ∧ ∀ name ∈ t.name, '`' ∉ name

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
  simp [table, hempty, takeTable, Exec.row_eq, Exec.rule_eq, takeWhile_rows rows hrest,
    dropWhile_rows rows hrest, readRows_rows hclean, hall]

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
theorem scanLines_lines (d : Draft) (h : d.Clean) : scanLines d.lines = pure d := by
  have htables := takeTables_printTables headings d.tables rfl headings_nodup
    (fun rows hrows cells hcells cell hcell => (h.cells rows hrows cells hcells cell hcell).1)
    (by simp [Fit, headings, Draft.tables, Term.cells, Replaced.cells, termColumns])
  have hterms : ∀ terms : List Term, (∀ t ∈ terms, t ∈ d.rows) →
      readAll Term.ofCells (terms.map Term.cells) = some terms := by
    intro terms hsub
    refine readAll_map terms fun t ht => ?_
    have hrow := h.rows t (hsub t ht)
    cases t with
    | mk term category definition replaces path name =>
      obtain ⟨hcomma, hdash, hpath, hname⟩ := hrow
      simp only [Term.ofCells, Term.cells, namesOf_printNames hcomma hdash,
        sourceOf_printSource hpath hname]
  have h1 := hterms d.sharedNouns fun t ht => by simp [Draft.rows, ht]
  have h2 := hterms d.sharedVerbs fun t ht => by simp [Draft.rows, ht]
  have h3 := hterms d.projectNouns fun t ht => by simp [Draft.rows, ht]
  have h4 := hterms d.projectVerbs fun t ht => by simp [Draft.rows, ht]
  have hreplaced : readAll Replaced.ofCells (d.replaced.map Replaced.cells) = some d.replaced :=
    readAll_map _ fun _ _ => rfl
  cases hpackage : d.shared with
  | none =>
    simp only [Draft.lines, hpackage, scanLines, Exec.titleLine_eq, Exec.standardLine_eq,
      Exec.versionLabel_eq, Exec.sharedLabel_eq, Exec.headings_eq, and_self, ite_true,
      dropPrefix_append, List.nil_append, dropPrefix_printTables, htables, pure_bind]
    simp only [Draft.tables, h1, h2, h3, h4, hreplaced]
    cases d
    simp_all
  | some package =>
    simp only [Draft.lines, hpackage, scanLines, Exec.titleLine_eq, Exec.standardLine_eq,
      Exec.versionLabel_eq, Exec.sharedLabel_eq, Exec.headings_eq, and_self, ite_true,
      dropPrefix_append, List.singleton_append, htables, pure_bind]
    simp only [Draft.tables, h1, h2, h3, h4, hreplaced]
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
theorem scan_render (d : Draft) (h : d.Clean) : scan d.render = pure d := by
  have hlines : ∀ line ∈ d.lines, '\n' ∉ line := by
    intro line hline
    simp only [Draft.lines, List.mem_cons, List.mem_append] at hline
    rcases hline with rfl | rfl | rfl | rfl | hline | hline
    · decide
    · simp
    · simp only [List.mem_append, not_or]
      exact ⟨by decide, h.version⟩
    · decide
    · cases hpackage : d.shared with
      | none => simp [hpackage] at hline
      | some package =>
        simp only [hpackage, List.mem_singleton] at hline
        subst hline
        simp only [List.mem_append, not_or]
        exact ⟨by decide, h.package package hpackage⟩
    · exact not_mem_printTables headings headings_lines d.tables
        (fun rows hrows cells hcells cell hcell =>
          (h.cells rows hrows cells hcells cell hcell).2) line hline
  simp [scan, linesOf, Draft.render, split_terminated '\n' hlines, scanLines_lines d h]


/-! ## What a vocabulary is -/

/-- The categories of rule 1.5, for a noun: `1` to `22`. -/
def nounCategories : List (List Char) :=
  ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17",
    "18", "19", "20", "21", "22"].map String.toList

/-- The categories of rule 1.12, for a verb: `1a` to `1f`, `2a` to `2c`, `3a` to `3f` and
`4`. -/
def verbCategories : List (List Char) :=
  ["1a", "1b", "1c", "1d", "1e", "1f", "2a", "2b", "2c", "3a", "3b", "3c", "3d", "3e", "3f",
    "4"].map String.toList

/-- The key of a row of terms: its term in lowercase. Rows are compared and put in sequence by
their keys. -/
def Term.key (t : Term) : List Char := lower t.term

/-- The key of a row of replaced words: its word in lowercase. -/
def Replaced.key (r : Replaced) : List Char := lower r.word

/-- The line of a row of terms in the print. -/
def Term.line (t : Term) : List Char := Exec.row (Exec.termCells t)

/-- The line of a row of replaced words in the print. -/
def Replaced.line (r : Replaced) : List Char := Exec.row (Exec.replacedCells r)

/-- The names that the rows of `d` replace, in lowercase, in the order of the print. -/
def Draft.replacedNames (d : Draft) : List (List Char) :=
  d.rows.flatMap fun t => t.replaces.map lower

/-- The words of the table of replaced words of `d`, in lowercase. -/
def Draft.replacedWords (d : Draft) : List (List Char) := d.replaced.map Replaced.key

/-- The rows are in the sequence of their keys: the key of each row is before the key of the
next row. -/
abbrev Ascending {α : Type} (key : α → List Char) (rows : List α) : Prop :=
  ∀ pair ∈ rows.zip rows.tail, key pair.1 < key pair.2

/-- A row of terms that has no defect of its own, in a table whose categories are
`categories`. -/
structure Term.Sound (categories : List (List Char)) (t : Term) : Prop where
  /-- The term is one to three words, with one space between two words. -/
  term : Separated ' ' (fun words => (∀ word ∈ words, Word word) ∧ words.length ≤ 3) t.term
  /-- The category is one of the categories of the table. -/
  category : t.category ∈ categories
  /-- The definition is one sentence of 25 words or less that ends with a period. -/
  definition : OneSentence t.definition
  /-- Each replaced name is one word or more, with one space between two words. -/
  replaces : ∀ name ∈ t.replaces, Phrase name
  /-- The path is not empty and has no space character, no backtick and no `|` character. -/
  path : Solid t.path
  /-- The Lean name, if the row gives one, is such a text too. -/
  name : ∀ name ∈ t.name, Solid name

/-- A row of replaced words that has no defect of its own. -/
structure Replaced.Sound (r : Replaced) : Prop where
  /-- The replaced word is one word. -/
  word : Word r.word
  /-- The text to write is parts that are not empty, with one space between two parts. -/
  write : Separated ' ' (fun parts => ∀ part ∈ parts, part ≠ []) r.write

/-- What a vocabulary is: a draft with none of the defects. -/
structure Draft.WellFormed (d : Draft) : Prop where
  /-- No cell has a `|` character or a line feed. -/
  plain : ∀ rows ∈ d.tables, ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell ∧ '\n' ∉ cell
  /-- The version is a number. -/
  version : Numeral d.version
  /-- A vocabulary that names a shared vocabulary names its package and has no `Shared`
  table. -/
  package : ∀ package ∈ d.shared, Solid package ∧ d.sharedNouns = [] ∧ d.sharedVerbs = []
  /-- Each row of a table of nouns is sound, with a category of rule 1.5. -/
  nouns : ∀ t ∈ d.sharedNouns ++ d.projectNouns, t.Sound nounCategories
  /-- Each row of a table of verbs is sound, with a category of rule 1.12. -/
  verbs : ∀ t ∈ d.sharedVerbs ++ d.projectVerbs, t.Sound verbCategories
  /-- Each row of the table of replaced words is sound. -/
  words : ∀ r ∈ d.replaced, r.Sound
  /-- The rows of `Shared technical nouns` are in the sequence of their terms. -/
  sharedNouns : Ascending Term.key d.sharedNouns
  /-- The rows of `Shared technical verbs` are in the sequence of their terms. -/
  sharedVerbs : Ascending Term.key d.sharedVerbs
  /-- The rows of `Project technical nouns` are in the sequence of their terms. -/
  projectNouns : Ascending Term.key d.projectNouns
  /-- The rows of `Project technical verbs` are in the sequence of their terms. -/
  projectVerbs : Ascending Term.key d.projectVerbs
  /-- The rows of `Replaced words` are in the sequence of their words. -/
  replaced : Ascending Replaced.key d.replaced
  /-- No two rows of terms have the same term, in one table or in two tables. -/
  distinct : (d.rows.map Term.key).Nodup
  /-- No name is replaced two times, by one row or by two rows. -/
  names : d.replacedNames.Nodup
  /-- No term is a replaced name or a replaced word. -/
  kept : ∀ t ∈ d.rows, t.key ∉ d.replacedNames ∧ t.key ∉ d.replacedWords
  /-- No replaced name is a replaced word. -/
  apart : ∀ name ∈ d.replacedNames, name ∉ d.replacedWords

/-! ## Defects -/

namespace Exec

/-- The categories of a noun, for the functions (`nounCategories_eq`). -/
def nounCategories : List (List Char) :=
  ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17",
    "18", "19", "20", "21", "22"].map String.toList

/-- The categories of a verb, for the functions (`verbCategories_eq`). -/
def verbCategories : List (List Char) :=
  ["1a", "1b", "1c", "1d", "1e", "1f", "2a", "2b", "2c", "3a", "3b", "3c", "3d", "3e", "3f",
    "4"].map String.toList

/-- The key of a row of terms, for the functions (`termKey_eq`). -/
def termKey (t : Term) : List Char := lower t.term

/-- The key of a row of replaced words, for the functions (`replacedKey_eq`). -/
def replacedKey (r : Replaced) : List Char := lower r.word

/-- The names that the rows of a draft replace, for the functions (`replacedNames_eq`). -/
def replacedNames (d : Draft) : List (List Char) :=
  (rows d).flatMap fun t => t.replaces.map lower

/-- The words of the table of replaced words, for the functions (`replacedWords_eq`). -/
def replacedWords (d : Draft) : List (List Char) := d.replaced.map replacedKey

theorem nounCategories_eq : @nounCategories = @Controlled.nounCategories := rfl
theorem verbCategories_eq : @verbCategories = @Controlled.verbCategories := rfl
theorem termKey_eq : @termKey = @Term.key := rfl
theorem replacedKey_eq : @replacedKey = @Replaced.key := rfl
theorem replacedNames_eq : @replacedNames = @Draft.replacedNames := rfl
theorem replacedWords_eq : @replacedWords = @Draft.replacedWords := rfl

end Exec

theorem ite_nil_iff {α : Type} {p : Prop} [Decidable p] {x : α} :
    (if p then [] else [x]) = [] ↔ p := by
  by_cases h : p <;> simp [h]

/-- What is wrong with one row of terms whose category must be one of `categories`. -/
def Term.defects (categories : List (List Char)) (t : Term) : List String :=
  (if (∀ word ∈ split ' ' t.term, Exec.Word word) ∧ (split ' ' t.term).length ≤ 3 then []
    else ["the term is not one to three words with one space between them"]) ++
  (if t.category ∈ categories then []
    else [s!"the category is not one of {", ".intercalate (categories.map String.ofList)}"]) ++
  (if oneSentence t.definition = true then []
    else ["the definition is not one sentence of 25 words or less that ends with a period"]) ++
  (if ∀ name ∈ t.replaces, ∀ word ∈ split ' ' name, Exec.Word word then []
    else ["a replaced name is not one word or more with one space between them"]) ++
  (if Exec.Solid t.path then []
    else ["the path of the source is empty, or has a space character, a backtick or a `|` \
      character"]) ++
  (if ∀ name ∈ t.name, Exec.Solid name then []
    else ["the Lean name of the source is empty, or has a space character, a backtick or a \
      `|` character"])

/-- A row of terms has no defect exactly when it is sound. -/
theorem Term.defects_nil_iff (categories : List (List Char)) (t : Term) :
    t.defects categories = [] ↔ t.Sound categories := by
  simp only [Term.defects, List.append_eq_nil_iff, ite_nil_iff]
  simp only [Exec.word_iff, Exec.Solid_eq, oneSentence_iff]
  exact ⟨fun ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ =>
      ⟨(separated_iff ' ' _ _).mpr a, b, c, fun name h => (separated_iff ' ' _ _).mpr (d name h),
        e, f⟩,
    fun ⟨a, b, c, d, e, f⟩ =>
      ⟨⟨⟨⟨⟨(separated_iff ' ' _ _).mp a, b⟩, c⟩,
        fun name h => (separated_iff ' ' _ _).mp (d name h)⟩, e⟩, f⟩⟩

/-- What is wrong with one row of replaced words. -/
def Replaced.defects (r : Replaced) : List String :=
  (if Exec.Word r.word then [] else ["the replaced word is not one word"]) ++
  (if ∀ part ∈ split ' ' r.write, part ≠ [] then []
    else ["the text to write is empty, or has a space at its start, at its end or after a space"])

/-- A row of replaced words has no defect exactly when it is sound. -/
theorem Replaced.defects_nil_iff (r : Replaced) : r.defects = [] ↔ r.Sound := by
  simp only [Replaced.defects, List.append_eq_nil_iff, ite_nil_iff]
  simp only [Exec.word_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, (separated_iff ' ' _ _).mpr b⟩,
    fun ⟨a, b⟩ => ⟨a, (separated_iff ' ' _ _).mp b⟩⟩

/-- The rows whose key is not after the key of the row before them, each with its line. -/
def unordered {α : Type} (line key : α → List Char) (rows : List α) :
    List (List Char × String) :=
  (rows.zip rows.tail).filterMap fun pair =>
    if key pair.1 < key pair.2 then none
    else some (line pair.2, s!"this row is not after the row `{String.ofList (key pair.1)}` in \
      the order of the lowercase terms")

/-- No row is reported exactly when the rows are in the sequence of their keys. -/
theorem unordered_nil_iff {α : Type} (line key : α → List Char) (rows : List α) :
    unordered line key rows = [] ↔ Ascending key rows := by
  simp [unordered, List.filterMap_eq_nil_iff]

/-- The lines whose key is also the key of an earlier line or one of `seen`. -/
def repeated (what : String) (seen : List (List Char)) :
    List (List Char × List Char) → List (List Char × String)
  | [] => []
  | (line, key) :: rest =>
    (if key ∈ seen then [(line, s!"the {what} `{String.ofList key}` is given two times")]
      else []) ++ repeated what (key :: seen) rest

theorem repeated_nil_iff (what : String) (seen : List (List Char))
    (rows : List (List Char × List Char)) :
    repeated what seen rows = [] ↔ (∀ row ∈ rows, row.2 ∉ seen) ∧ (rows.map (·.2)).Nodup := by
  induction rows generalizing seen with
  | nil => simp [repeated]
  | cons row rows ih =>
    obtain ⟨line, key⟩ := row
    simp only [repeated, List.append_eq_nil_iff, ih, List.mem_cons, not_or, List.map_cons,
      List.nodup_cons, List.mem_map, forall_eq_or_imp]
    constructor
    · rintro ⟨hkey, hrows, hnodup⟩
      have hseen : key ∉ seen := by
        by_cases h : key ∈ seen
        · simp [h] at hkey
        · exact h
      refine ⟨⟨hseen, fun row hrow => (hrows row hrow).2⟩, ?_, hnodup⟩
      rintro ⟨row, hrow, heq⟩
      exact (hrows row hrow).1 heq
    · rintro ⟨⟨hseen, hrows⟩, hfresh, hnodup⟩
      exact ⟨by simp [hseen], fun row hrow => ⟨fun heq => hfresh ⟨row, hrow, heq⟩, hrows row hrow⟩,
        hnodup⟩

/-- No line is reported for no earlier key exactly when the keys are pairwise different. -/
theorem repeated_nil (what : String) (rows : List (List Char × List Char)) :
    repeated what [] rows = [] ↔ (rows.map (·.2)).Nodup := by
  simp [repeated_nil_iff]

/-- The defects of the head lines and of the cells of `d`. -/
def Draft.headDefects (d : Draft) : List (List Char × String) :=
  (if ∀ rows ∈ Exec.tables d, ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell ∧ '\n' ∉ cell then []
    else [(Exec.titleLine, "a cell has a `|` character or a line feed")]) ++
  (if Exec.Numeral d.version then []
    else [(Exec.versionLabel ++ d.version, "the vocabulary version is not a number")]) ++
  (match d.shared with
    | none => []
    | some package =>
      (if Exec.Solid package then []
        else [(Exec.sharedLabel ++ package,
          "the package of the shared vocabulary is not a name without spaces")]) ++
      (if d.sharedNouns = [] ∧ d.sharedVerbs = [] then []
        else [(Exec.sharedLabel ++ package,
          "a vocabulary that names a shared vocabulary has a `Shared` table")]))

theorem Draft.headDefects_nil_iff (d : Draft) :
    d.headDefects = [] ↔
      (∀ rows ∈ d.tables, ∀ cells ∈ rows, ∀ cell ∈ cells, '|' ∉ cell ∧ '\n' ∉ cell) ∧
        Numeral d.version ∧
        ∀ package ∈ d.shared, Solid package ∧ d.sharedNouns = [] ∧ d.sharedVerbs = [] := by
  simp only [Draft.headDefects, List.append_eq_nil_iff, ite_nil_iff]
  refine Iff.trans and_assoc (and_congr_right fun _ => and_congr_right fun _ => ?_)
  cases d.shared with
  | none => simp
  | some package =>
    simp only [List.append_eq_nil_iff, ite_nil_iff, Option.mem_def, Option.some.injEq]
    simp only [Exec.Solid_eq]
    exact ⟨fun ⟨a, b⟩ p hp => hp ▸ ⟨a, b⟩, fun h => ⟨(h package rfl).1, (h package rfl).2⟩⟩

/-- The defects of the rows of `d`, each row alone. -/
def Draft.rowDefects (d : Draft) : List (List Char × String) :=
  ((d.sharedNouns ++ d.projectNouns).flatMap fun t =>
    (t.defects Exec.nounCategories).map fun reason => (t.line, reason)) ++
  ((d.sharedVerbs ++ d.projectVerbs).flatMap fun t =>
    (t.defects Exec.verbCategories).map fun reason => (t.line, reason)) ++
  (d.replaced.flatMap fun r => r.defects.map fun reason => (r.line, reason))

theorem Draft.rowDefects_nil_iff (d : Draft) :
    d.rowDefects = [] ↔
      (∀ t ∈ d.sharedNouns ++ d.projectNouns, t.Sound nounCategories) ∧
        (∀ t ∈ d.sharedVerbs ++ d.projectVerbs, t.Sound verbCategories) ∧
        ∀ r ∈ d.replaced, r.Sound := by
  simp only [Draft.rowDefects, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
    List.map_eq_nil_iff, Term.defects_nil_iff, Replaced.defects_nil_iff, Exec.nounCategories_eq,
    Exec.verbCategories_eq]
  exact and_assoc

/-- The rows of `d` that are not in the sequence of their table. -/
def Draft.orderDefects (d : Draft) : List (List Char × String) :=
  unordered Term.line Exec.termKey d.sharedNouns ++
    unordered Term.line Exec.termKey d.sharedVerbs ++
    unordered Term.line Exec.termKey d.projectNouns ++
    unordered Term.line Exec.termKey d.projectVerbs ++
    unordered Replaced.line Exec.replacedKey d.replaced

theorem Draft.orderDefects_nil_iff (d : Draft) :
    d.orderDefects = [] ↔
      Ascending Term.key d.sharedNouns ∧ Ascending Term.key d.sharedVerbs ∧
        Ascending Term.key d.projectNouns ∧ Ascending Term.key d.projectVerbs ∧
        Ascending Replaced.key d.replaced := by
  simp only [Draft.orderDefects, List.append_eq_nil_iff, unordered_nil_iff, Exec.termKey_eq,
    Exec.replacedKey_eq]
  exact ⟨fun ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩⟩

/-- The rows of `d` whose term or whose replaced name is given a second time. -/
def Draft.repeatDefects (d : Draft) : List (List Char × String) :=
  repeated "term" [] ((Exec.rows d).map fun t => (t.line, Exec.termKey t)) ++
    repeated "replaced name" []
      ((Exec.rows d).flatMap fun t => t.replaces.map fun name => (t.line, Exec.lower name))

theorem Draft.repeatDefects_nil_iff (d : Draft) :
    d.repeatDefects = [] ↔ (d.rows.map Term.key).Nodup ∧ d.replacedNames.Nodup := by
  have hkeys : (d.rows.map fun t => (t.line, t.key)).map (·.2) = d.rows.map Term.key := by
    simp [List.map_map, Function.comp_def]
  have hnames : (d.rows.flatMap fun t => t.replaces.map fun name => (t.line, lower name)).map
      (·.2) = d.replacedNames := by
    simp [Draft.replacedNames, List.map_flatMap, List.map_map, Function.comp_def]
  simp only [Draft.repeatDefects, Exec.rows_eq, Exec.termKey_eq, Exec.lower_eq,
    List.append_eq_nil_iff, repeated_nil, hkeys, hnames]

/-- The rows of `d` whose term is also a replaced name or a replaced word, and the rows with a
replaced name that is also a replaced word. -/
def Draft.clashDefects (d : Draft) : List (List Char × String) :=
  ((Exec.rows d).filterMap fun t =>
    if Exec.termKey t ∈ Exec.replacedNames d ∨ Exec.termKey t ∈ Exec.replacedWords d then
      some (t.line, s!"the term `{String.ofList (Exec.termKey t)}` is also a replaced name or a \
        replaced word")
    else none) ++
  ((Exec.rows d).flatMap fun t => t.replaces.filterMap fun name =>
    if Exec.lower name ∈ Exec.replacedWords d then
      some (t.line,
        s!"the replaced name `{String.ofList (Exec.lower name)}` is also a replaced word")
    else none)

theorem Draft.clashDefects_nil_iff (d : Draft) :
    d.clashDefects = [] ↔
      (∀ t ∈ d.rows, t.key ∉ d.replacedNames ∧ t.key ∉ d.replacedWords) ∧
        ∀ name ∈ d.replacedNames, name ∉ d.replacedWords := by
  simp only [Draft.clashDefects, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
    List.flatMap_eq_nil_iff, ite_eq_right_iff, reduceCtorEq, imp_false, not_or]
  simp only [Exec.rows_eq, Exec.termKey_eq, Exec.lower_eq, Exec.replacedNames_eq,
    Exec.replacedWords_eq]
  refine and_congr_right fun _ => ?_
  simp only [Draft.replacedNames, List.mem_flatMap, List.mem_map]
  constructor
  · rintro h name ⟨t, ht, raw, hraw, rfl⟩
    exact h t ht raw hraw
  · intro h t ht raw hraw
    exact h (lower raw) ⟨t, ht, raw, hraw, rfl⟩

/-- The defects of `d`, each with the line of the print it is about. -/
def Draft.defects (d : Draft) : List (List Char × String) :=
  d.headDefects ++ d.rowDefects ++ d.orderDefects ++ d.repeatDefects ++ d.clashDefects

/-- A draft has no defect exactly when it is well formed. -/
theorem Draft.defects_nil_iff (d : Draft) : d.defects = [] ↔ d.WellFormed := by
  simp only [Draft.defects, List.append_eq_nil_iff, d.headDefects_nil_iff, d.rowDefects_nil_iff,
    d.orderDefects_nil_iff, d.repeatDefects_nil_iff, d.clashDefects_nil_iff]
  exact ⟨fun ⟨⟨⟨⟨⟨a, b, c⟩, d, e, f⟩, g, h, i, j, k⟩, l, m⟩, n, o⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ =>
      ⟨⟨⟨⟨⟨a, b, c⟩, d, e, f⟩, g, h, i, j, k⟩, l, m⟩, n, o⟩⟩

/-! ## Vocabularies -/

/-- A phrase has no comma. -/
theorem Phrase.not_mem_comma {text : List Char} (h : Phrase text) : ',' ∉ text := by
  obtain ⟨first, rest, rfl, -, hwords⟩ := h
  intro hmem
  have hfree : ∀ word ∈ first :: rest, ',' ∉ word := fun word hword hcomma =>
    absurd ((hwords word hword).2.1 ',' hcomma) (by decide)
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons] at hmem
  rcases hmem with hmem | ⟨word, hword, hmem | hmem⟩
  · exact hfree first (List.mem_cons_self ..) hmem
  · exact absurd hmem (by decide)
  · exact hfree word (List.mem_cons_of_mem _ hword) hmem

/-- The scanner reads the print of a well-formed draft back. -/
theorem Draft.WellFormed.clean {d : Draft} (h : d.WellFormed) : d.Clean where
  version := fun hmem => absurd (h.version.2.1 '\n' hmem) (by decide)
  package := fun package hpackage hmem =>
    absurd ((h.package package hpackage).1.2 '\n' hmem).1 (by decide)
  cells := h.plain
  rows := by
    intro t ht
    have hsound : ∃ categories, t.Sound categories := by
      simp only [Draft.rows, List.mem_append] at ht
      rcases ht with ((ht | ht) | ht) | ht
      · exact ⟨_, h.nouns t (List.mem_append_left _ ht)⟩
      · exact ⟨_, h.verbs t (List.mem_append_left _ ht)⟩
      · exact ⟨_, h.nouns t (List.mem_append_right _ ht)⟩
      · exact ⟨_, h.verbs t (List.mem_append_right _ ht)⟩
    obtain ⟨categories, hsound⟩ := hsound
    refine ⟨fun name hname => (hsound.replaces name hname).not_mem_comma, ?_,
      fun hmem => (hsound.path.2 '`' hmem).2.1 rfl,
      fun name hname hmem => ((hsound.name name hname).2 '`' hmem).2.1 rfl⟩
    intro heq
    have hword : Word ['-'] :=
      (separated_iff ' ' _ _).mp (hsound.replaces ['-'] (by rw [heq]; exact List.mem_cons_self ..))
        ['-'] (by decide)
    exact absurd ((Exec.word_iff _).mpr hword) (by decide)

/-- The vocabulary of a project: a draft that is well formed. -/
structure Vocabulary where
  /-- The rows of the tables. -/
  draft : Draft
  /-- The draft has none of the defects. -/
  wellFormed : draft.WellFormed

theorem Vocabulary.ext {v w : Vocabulary} (h : v.draft = w.draft) : v = w := by
  cases v; cases w; cases h; rfl

/-- No two rows of terms of a vocabulary have the same term, in one table or in two tables. The
comparison ignores case. -/
theorem Vocabulary.distinct (v : Vocabulary) : (v.draft.rows.map Term.key).Nodup :=
  v.wellFormed.distinct

/-- Each definition of a vocabulary is one sentence of 25 words or less that ends with a
period, by the one definition of a sentence (`Regula.Controlled.Divided`). -/
theorem Vocabulary.definitions (v : Vocabulary) : ∀ t ∈ v.draft.rows, OneSentence t.definition := by
  intro t ht
  simp only [Draft.rows, List.mem_append] at ht
  rcases ht with ((ht | ht) | ht) | ht
  · exact (v.wellFormed.nouns t (List.mem_append_left _ ht)).definition
  · exact (v.wellFormed.verbs t (List.mem_append_left _ ht)).definition
  · exact (v.wellFormed.nouns t (List.mem_append_right _ ht)).definition
  · exact (v.wellFormed.verbs t (List.mem_append_right _ ht)).definition

/-- The text of `v`: the one text `parse` reads as `v`. -/
def write (v : Vocabulary) : String := String.ofList v.draft.render

/-- The vocabulary whose text is `text`, if `text` is the text of one. -/
@[regula_decision]
def parse (text : String) : Option Vocabulary :=
  match scan text.toList with
  | .ok d =>
    if h : d.defects = [] ∧ Exec.render d = text.toList then some ⟨d, d.defects_nil_iff.mp h.1⟩
    else none
  | .error _ => none

theorem parse_write (v : Vocabulary) : parse (write v) = some v := by
  have hscan : scan v.draft.render = .ok v.draft := scan_render v.draft v.wellFormed.clean
  simp only [parse, write, String.toList_ofList, hscan, Exec.render_eq]
  split
  · rfl
  · rename_i hrefused
    exact absurd ⟨v.draft.defects_nil_iff.mpr v.wellFormed, trivial⟩ hrefused

theorem write_of_parse (text : String) (v : Vocabulary) (h : parse text = some v) :
    write v = text := by
  unfold parse at h
  split at h
  · split at h
    · rename_i d _ hd
      cases h
      have hrender : d.render = text.toList := hd.2
      simp [write, hrender, String.ofList_toList]
    · cases h
  · cases h

/-- The vocabulary with version 1 and no row. -/
def Vocabulary.empty : Vocabulary :=
  ⟨⟨['1'], none, [], [], [], [], []⟩, (Draft.defects_nil_iff _).mp (by decide)⟩

/-- A vocabulary with one row, whose source is the path `a`. -/
def Vocabulary.sample : Vocabulary :=
  ⟨⟨['1'], none, [⟨['a'], ['1'], ['A', '.'], [], ['a'], none⟩], [], [], [], []⟩,
    (Draft.defects_nil_iff _).mp (by decide)⟩

/-- Registered contract of the vocabulary parser (check C9), as a two-way decision: it accepts
exactly the texts that are the print of a vocabulary. It accepts the print of the vocabulary
with no row and refuses the empty text. -/
theorem checked_parse : Regula.ExecutableContract parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ v, text = write v)) :=
  ⟨.of_roundtrip parse_write write_of_parse Vocabulary.empty (unwritten := "") (by decide)⟩

/-! ## Why a text is refused -/

/-- The number of the first line at which `left` and `right` differ, counting from `n`. -/
def firstDifference (n : Nat) : List (List Char) → List (List Char) → Nat
  | a :: left, b :: right => if a = b then firstDifference (n + 1) left right else n
  | _, _ => n

/-- The number of the first line of the print of `d` that is `line`, counting from 1. -/
def Draft.lineOf (d : Draft) (line : List Char) : Nat := (Exec.lines d).idxOf line + 1

/-- The line that `lineOf` gives for a line of the print is that line. -/
theorem Draft.lineOf_spec (d : Draft) {line : List Char} (h : line ∈ d.lines) :
    d.lines[d.lineOf line - 1]? = some line := by
  have hlt : d.lines.idxOf line < d.lines.length := List.idxOf_lt_length_iff.mpr h
  simp [Draft.lineOf, Exec.lines_eq, List.getElem?_eq_getElem hlt, List.getElem_idxOf hlt]

/-- Why `text` is not the text of a vocabulary: each reason, with the number of its line. -/
def explain (text : String) : List (Nat × String) :=
  if text.toList.getLast? = some '\n' then
    match scan text.toList with
    | .error (remaining, reason) => [((linesOf text.toList).length + 1 - remaining, reason)]
    | .ok d =>
      if Exec.render d = text.toList then
        d.defects.map fun (line, reason) => (d.lineOf line, reason)
      else
        [(firstDifference 1 (Exec.lines d) (split '\n' text.toList),
          "the text is not the print of its vocabulary from this line on: a cell that the \
            print writes with other spaces, a `Replaces` cell that is not `-` or names with \
            `, ` between them, or a `Source` cell that is not a path in backticks with or \
            without a Lean name in backticks and parentheses after it")]
  else [((split '\n' text.toList).length, "the text has no line feed at its end")]

/-- A text with one terminated part or more ends with the terminator. -/
theorem terminated_getLast? (terminator : Char) {parts : List (List Char)} (h : parts ≠ []) :
    (terminated terminator parts).getLast? = some terminator := by
  rcases List.eq_nil_or_concat parts with rfl | ⟨init, last, rfl⟩
  · exact absurd rfl h
  · simp [terminated, List.concat_eq_append, List.flatMap_append]

/-- The print of a draft ends with a line feed. -/
theorem Draft.render_getLast? (d : Draft) : d.render.getLast? = some '\n' :=
  terminated_getLast? '\n' (by simp [Draft.lines])

/-- `explain` reports nothing exactly when `parse` accepts the text. -/
theorem explain_nil_iff (text : String) : explain text = [] ↔ (parse text).isSome = true := by
  unfold explain parse
  by_cases hlast : text.toList.getLast? = some '\n'
  · cases hscan : scan text.toList with
    | error refusal => simp [hlast]
    | ok d =>
      by_cases hrender : Exec.render d = text.toList
      · by_cases hdefects : d.defects = [] <;> simp [hlast, hrender, hdefects]
      · simp [hlast, hrender]
  · cases hscan : scan text.toList with
    | error refusal => simp [hlast]
    | ok d =>
      have hrender : Exec.render d ≠ text.toList := fun heq =>
        hlast ((show d.render = text.toList from heq) ▸ d.render_getLast?)
      simp [hlast, hrender]

/-! ## Sources and shared tables -/

/-- The rows of `v` whose source path is not a tracked path of their repository: `shared` holds
the tracked paths for the rows of the `Shared` tables and `project` those for the rows of the
`Project` tables. Each row is given with whether it is a row of a `Shared` table, with its line
and with its path. -/
@[regula_decision]
def untracked (shared project : List String) (v : Vocabulary) :
    List (Bool × List Char × String) :=
  ((v.draft.sharedNouns ++ v.draft.sharedVerbs).filterMap fun t =>
    if String.ofList t.path ∈ shared then none
    else some (true, t.line, String.ofList t.path)) ++
  ((v.draft.projectNouns ++ v.draft.projectVerbs).filterMap fun t =>
    if String.ofList t.path ∈ project then none
    else some (false, t.line, String.ofList t.path))

/-- Registered contract of the check of source paths (a part of check C9), as a two-way
decision: no row is reported exactly when the source path of each row of a `Shared` table is one
of the first paths and the source path of each row of a `Project` table is one of the second
paths. The vocabulary with no row is accepted for no path, and a vocabulary with one row is
refused for no path. -/
theorem checked_untracked : Regula.ExecutableContract untracked (fun run =>
    Regula.Decides (· = [])
      (fun input : (List String × List String) × Vocabulary =>
        (∀ t ∈ input.2.draft.sharedNouns ++ input.2.draft.sharedVerbs,
          String.ofList t.path ∈ input.1.1) ∧
        ∀ t ∈ input.2.draft.projectNouns ++ input.2.draft.projectVerbs,
          String.ofList t.path ∈ input.1.2)
      (Function.uncurry (Function.uncurry run))) :=
  ⟨.of_iff
    (fun input => by
      simp [Function.uncurry, untracked, List.filterMap_eq_nil_iff, or_imp, forall_and,
        and_assoc])
    ⟨(([], []), Vocabulary.empty), by decide⟩
    ⟨(([], []), Vocabulary.sample), by decide⟩⟩

/-- The draft of `project` with the `Shared` tables of `shared` and no shared package. -/
def Draft.adopt (shared project : Draft) : Draft :=
  { project with
    shared := none, sharedNouns := shared.sharedNouns, sharedVerbs := shared.sharedVerbs }

/-- The vocabulary `project` together with the `Shared` tables of `shared`, the vocabulary of
the package it names: defined when `project` names a shared vocabulary, `shared` names none, and
the rows together have no defect. -/
@[regula_decision]
def adopt (shared project : Vocabulary) : Option Vocabulary :=
  if h : project.draft.shared.isSome = true ∧ shared.draft.shared.isNone = true ∧
      (shared.draft.adopt project.draft).defects = [] then
    some ⟨shared.draft.adopt project.draft, (Draft.defects_nil_iff _).mp h.2.2⟩
  else none

/-- Registered contract of the adoption of shared tables (a part of check C9), as a two-way
decision: it succeeds exactly when the project vocabulary names a shared vocabulary, the shared
one names none, and the rows of the project vocabulary with the `Shared` tables of the shared
one are well formed. Thus a row of a `Project` table cannot have the term of a row of a `Shared`
table (`Draft.WellFormed.distinct`). It refuses a project vocabulary that names no shared
vocabulary and accepts one that does. -/
theorem checked_adopt : Regula.ExecutableContract adopt (fun run =>
    Regula.Decides (·.isSome = true)
      (fun input : Vocabulary × Vocabulary =>
        input.2.draft.shared.isSome = true ∧ input.1.draft.shared.isNone = true ∧
          Draft.WellFormed { input.2.draft with
            shared := none
            sharedNouns := input.1.draft.sharedNouns
            sharedVerbs := input.1.draft.sharedVerbs })
      (Function.uncurry run)) :=
  ⟨.of_iff
    (fun input => by
      have hiff := Draft.defects_nil_iff (input.1.draft.adopt input.2.draft)
      simp only [Function.uncurry, adopt]
      split
      · rename_i h
        exact ⟨fun _ => ⟨h.1, h.2.1, hiff.mp h.2.2⟩, fun _ => rfl⟩
      · rename_i h
        exact ⟨fun hsome => absurd hsome (by simp),
          fun ⟨a, b, c⟩ => absurd ⟨a, b, hiff.mpr c⟩ h⟩)
    ⟨(Vocabulary.empty, ⟨⟨['1'], some ['a'], [], [], [], [], []⟩,
      (Draft.defects_nil_iff _).mp (by decide)⟩), by decide⟩
    ⟨(Vocabulary.empty, Vocabulary.empty), by decide⟩⟩

/-- Why `project` cannot use the `Shared` tables of `shared`: each reason, with whether it is
about the print of `shared` and not about the print of `project`, and with the number of its
line in that print. A defect of the rows together is about the print of `project` when that
print has its line. -/
def clashes (shared project : Vocabulary) : List (Bool × Nat × String) :=
  (if project.draft.shared.isSome then []
    else [(false, 1, "the vocabulary names no shared vocabulary")]) ++
  (if shared.draft.shared.isNone then []
    else [(true, shared.draft.lineOf (Exec.sharedLabel ++ shared.draft.shared.getD []),
      "the shared vocabulary names a shared vocabulary of its own")]) ++
  (shared.draft.adopt project.draft).defects.map fun (line, reason) =>
    if line ∈ Exec.lines project.draft then (false, project.draft.lineOf line, reason)
    else (true, shared.draft.lineOf line, reason)

/-- `clashes` reports nothing exactly when `adopt` succeeds. -/
theorem clashes_nil_iff (shared project : Vocabulary) :
    clashes shared project = [] ↔ (adopt shared project).isSome = true := by
  have hclashes : clashes shared project = [] ↔
      project.draft.shared.isSome = true ∧ shared.draft.shared.isNone = true ∧
        (shared.draft.adopt project.draft).defects = [] := by
    simp only [clashes, List.append_eq_nil_iff, List.map_eq_nil_iff, ite_nil_iff, and_assoc]
  rw [hclashes]
  unfold adopt
  split
  · rename_i h
    simpa using h
  · rename_i h
    simpa using h

end Regula.Controlled
