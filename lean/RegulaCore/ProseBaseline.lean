import RegulaCore.ControlledProse

/-! # The baseline of the prose checks

A repository that has documents with findings of the checks of `RegulaCore.ControlledProse` keeps
a baseline: the file `prose-baseline.json`, which gives for each such document what the checks
permit. This module defines that file exactly, as `RegulaCore.Vocabulary` defines `CONTEXT.md`,
and the two decisions about it.

## Main declarations

- `Ledger`, `Ledger.render`, `scanLedger`, `scanLedger_render`: the text of a baseline, a JSON
  document with one entry on each line, and the scanner that reads every such text back.
- `Allowance`, `Entry`, `WellFormed`, `defects`, `defects_nil_iff`: the entries of a baseline and
  what a baseline is, stated on its entries.
- `Baseline`, `Baseline.write`, `Baseline.parse`, `checked_baselineParse`: the parser is a
  two-way decision of "is the print of a baseline" (`Regula.Decides.of_roundtrip`).
- `Observed`, `Observed.Admitted`, `Baseline.Documented`, `gate`, `checked_gate` (check B1): a
  repository is accepted when each document has the findings its entry permits, and no finding
  without an entry, and when each entry has a document. Thus a change that removes a document
  must remove its entry.
- `Reference`, `Covers`, `Allowance.Within`, `Keeps`, `Shrinks`, `ratchet`, `checked_ratchet`
  (check B2): a baseline is accepted in relation to the reference of a base revision. The
  reference is the baseline of the base revision, or, when the base revision has none, what the
  checks observe of each of its documents. The baseline has no new path, no larger number and
  no other class, each frozen entry of a tracked document is kept, and the baseline is not
  removed.
- `Shrinks.paths`, `ratchet_removed`, `frozen_unchanged`, `entry_has_base_document`: no entry
  has a path that the reference does not have, a removed baseline is refused, and the two
  decisions together keep the digest of each frozen document and give no entry to a new
  document.
- `lineOf`, `lineOf_spec`: the line of the entry of a path in the print.
- `Start`, `History`, `Start.Base`, `baseOf`, `checked_baseOf`: the base revision of check B2
  for the start of a check, with what Git gives. Only the run of a developer takes a merge base
  (`baseOf_before`). `Start.read` reads the start from the environment variable of the
  executable.

## Specifications

`Observed.Admitted`, `Baseline.Documented` and `Shrinks` are statements about the entries, with
no call of a recursive function of the project. A function of a decision uses the definitions
that its specification names, such as the print of a ledger, and it decides the statements of
the specification with their `Decidable` instances. No second definition takes the place of
one. A number of an entry is a
text of decimal digits: two numbers are compared as such texts (`NotMore`), and a number of
findings is compared with the text that `Nat.repr` gives for it.

## Boundaries

`checked_gate` is about the paths, tallies and digests given: that a digest is the SHA-256 of a
file rests on the tool that computes it, that the documents given are the tracked Markdown
documents rests on Git, and that a tally is the document's rests on the reading of the document
(`RegulaCore.ControlledProse`). `checked_ratchet` is about the reference, the baseline and the
paths given: that the reference is the baseline or the documents of the base revision rests on
Git and on the reading of those documents. `entry_has_base_document` has the hypothesis that the
gate accepted the base revision: a run does not examine the documents of a base revision that
has a baseline.
-/

namespace Regula.Controlled

/-! ## The text of a baseline -/

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
  (dropPrefix Controlled.ledgerHead (linesOf text)).map fun rest =>
    ⟨rest.dropLast.dropLast.map fieldsOf⟩

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

/-! ## Entries -/

/-- What a baseline permits for one document. -/
inductive Allowance where
  /-- The document has exactly these numbers of findings, one for each check, each as a text of
  decimal digits. -/
  | counts (numbers : List (List Char))
  /-- The document is recorded evidence: its content has this SHA-256 digest and is not
  checked. -/
  | frozen (digest : List Char)
  /-- A program writes the document from sources that the checks do not read (`source` names
  them): it is not checked. -/
  | generated (source : List Char)
  deriving DecidableEq, Repr

/-- One entry of a baseline: the path of a document and what the baseline permits for it. -/
structure Entry where
  /-- The path of the document, relative to the repository root. -/
  path : List Char
  /-- What the baseline permits for the document. -/
  allowance : Allowance
  deriving DecidableEq, Repr

/-- The word that marks a frozen entry. -/
def frozenMarker : List Char := "frozen".toList

/-- The word that marks a generated entry. -/
def generatedMarker : List Char := "generated".toList

/-- The fields of an entry in the print: its path, and then its numbers, or `frozen` and its
digest, or `generated` and its source. -/
def Entry.fields (e : Entry) : List (List Char) :=
  e.path ::
    match e.allowance with
    | .counts numbers => numbers
    | .frozen digest => [frozenMarker, digest]
    | .generated source => [generatedMarker, source]

/-- The entry with these fields. -/
def Entry.ofFields : List (List Char) → Entry
  | [] => ⟨[], .counts []⟩
  | [path, marker, text] =>
    if marker = Controlled.frozenMarker then ⟨path, .frozen text⟩
    else if marker = Controlled.generatedMarker then ⟨path, .generated text⟩
    else ⟨path, .counts [marker, text]⟩
  | path :: numbers => ⟨path, .counts numbers⟩

/-- A SHA-256 digest: 64 lowercase hexadecimal digits. -/
abbrev Digest (text : List Char) : Prop :=
  text.length = 64 ∧ ∀ c ∈ text, c.isDigit = true ∨ ('a' ≤ c ∧ c ≤ 'f')

/-- A text that a JSON string writes as it is: no control character, no double quotation mark
and no backslash. -/
abbrev Bare (text : List Char) : Prop := ∀ c ∈ text, 32 ≤ c.val ∧ c ≠ '"' ∧ c ≠ '\\'

/-- What an entry permits has no defect: eight numbers of which one is not zero, or a digest, or
a source that is not empty. -/
def Allowance.Sound : Allowance → Prop
  | .counts numbers =>
    numbers.length = Check.all.length ∧ (∀ number ∈ numbers, Numeral number) ∧
      ∃ number ∈ numbers, number ≠ ['0']
  | .frozen digest => Digest digest
  | .generated source => source ≠ [] ∧ Bare source


/-- An entry that has no defect of its own. -/
structure Entry.Sound (e : Entry) : Prop where
  /-- The path is not empty and is written as it is. -/
  path : e.path ≠ [] ∧ Bare e.path
  /-- What the entry permits has no defect. -/
  allowance : e.allowance.Sound

/-- What a baseline is: entries with no defect, in the sequence of their paths. Thus no two
entries have the same path. -/
structure WellFormed (entries : List Entry) : Prop where
  /-- Each entry is sound. -/
  sound : ∀ e ∈ entries, e.Sound
  /-- The entries are in the sequence of their paths. -/
  ordered : Ascending Entry.path entries

/-- The ledger of `entries`: the fields of each entry. -/
def ledgerOf (entries : List Entry) : Ledger := ⟨entries.map Entry.fields⟩

instance : DecidablePred Digest := fun text => by
  unfold Digest
  infer_instance

instance : DecidablePred Bare := fun text => by
  unfold Bare
  infer_instance

instance : DecidablePred Allowance.Sound := fun allowance => by
  cases allowance <;> simp only [Allowance.Sound] <;> infer_instance

/-- The entries of a ledger. -/
def entriesOf (l : Ledger) : List Entry := l.entries.map Entry.ofFields

/-- The lines of the print of `entries`. -/
def linesOfEntries (entries : List Entry) : List (List Char) :=
  Ledger.lines (Controlled.ledgerOf entries)

/-- The number of the line of the print of `entries` that has the entry of `path`, counting
from 1: the line of the first entry with that path. -/
def lineOf (entries : List Entry) (path : List Char) : Nat :=
  Controlled.ledgerHead.length + (entries.map Entry.path).idxOf path + 1

/-- The number of the line of the print of `entries` where an entry of `path` would be: the
line after the entries whose paths are before `path`. -/
def lineFor (entries : List Entry) (path : List Char) : Nat :=
  Controlled.ledgerHead.length + (entries.takeWhile fun e => e.path < path).length + 1

theorem entryLines_getElem? :
    ∀ (rows : List (List (List Char))) (i : Nat), i < rows.length →
      (entryLines rows)[i]? = (rows[i]?).map (entryLine (decide (i + 1 = rows.length)))
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | [fields], 0, _ => rfl
  | [fields], i + 1, h => absurd h (by simp)
  | fields :: second :: more, 0, _ => by simp [entryLines]
  | fields :: second :: more, i + 1, h => by
    have := entryLines_getElem? (second :: more) i (by simpa using h)
    simpa [entryLines] using this

/-- The line that `lineOf` gives for the path of an entry is the line of an entry with that
path. -/
theorem lineOf_spec (entries : List Entry) {path : List Char}
    (h : path ∈ entries.map Entry.path) :
    ∃ e ∈ entries, e.path = path ∧ ∃ last,
      (linesOfEntries entries)[lineOf entries path - 1]? = some (entryLine last e.fields) := by
  have hlt : (entries.map Entry.path).idxOf path < (entries.map Entry.path).length :=
    List.idxOf_lt_length_iff.mpr h
  have hpath := List.getElem_idxOf hlt
  simp only [List.length_map] at hlt
  simp only [List.getElem_map] at hpath
  refine ⟨entries[(entries.map Entry.path).idxOf path], List.getElem_mem hlt, hpath,
    decide ((entries.map Entry.path).idxOf path + 1 = (entries.map Entry.fields).length), ?_⟩
  have hrow := entryLines_getElem? (entries.map Entry.fields) _ (by simpa using hlt)
  simp only [linesOfEntries, ledgerOf,
    Ledger.lines, lineOf, Nat.add_sub_cancel, List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left (by
      rw [show (entryLines (entries.map Entry.fields)).length = entries.length from ?_]
      · exact hlt
      · have : ∀ rows : List (List (List Char)), (entryLines rows).length = rows.length := by
          intro rows
          induction rows with
          | nil => rfl
          | cons fields more ih => cases more <;> simp_all [entryLines]
        simpa using this (entries.map Entry.fields)), hrow]
  simp [List.getElem?_eq_getElem hlt]

/-! ## Defects -/

/-- What is wrong with one entry. -/
def Entry.defects (e : Entry) : List String :=
  (if e.path ≠ [] ∧ Controlled.Bare e.path then []
    else ["the path is empty or has a character that a JSON string writes with an escape"]) ++
  (if Allowance.Sound e.allowance then []
    else ["an entry has a path and then eight numbers of which one is not zero, or `frozen` \
      and a digest of 64 lowercase hexadecimal digits, or `generated` and a source"])

theorem Entry.defects_nil_iff (e : Entry) : e.defects = [] ↔ e.Sound := by
  simp only [Entry.defects, List.append_eq_nil_iff, ite_nil_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- The reason for an entry whose path is not after `before`, the path of the entry before it.
The sequence of two paths is the sequence of the code points of their characters. -/
def entryOrder (before : List Char) : String :=
  s!"this entry is not after the entry `{String.ofList before}` in the sequence of the paths: \
    the code points of the characters give that sequence, thus each of the letters `A` to `Z` \
    is before each of the letters `a` to `z`"

/-- The defects of `entries`, each with the line of the print it is about. -/
def defects (entries : List Entry) : List (Nat × String) :=
  (entries.flatMap fun e => e.defects.map fun reason => (lineOf entries e.path, reason)) ++
    (unordered entryOrder Entry.path Entry.path entries).map fun (path, reason) =>
      (lineOf entries path, reason)

/-- Entries have no defect exactly when they are well formed. -/
theorem defects_nil_iff (entries : List Entry) : defects entries = [] ↔ WellFormed entries := by
  simp only [defects, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.map_eq_nil_iff,
    Entry.defects_nil_iff, unordered_nil_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-! ## Baselines -/

/-- A baseline: entries that are well formed. -/
structure Baseline where
  /-- The entries, in the order of the file. -/
  entries : List Entry
  /-- The entries have no defect. -/
  wellFormed : WellFormed entries

/-- The baseline with no entry. -/
def Baseline.empty : Baseline := ⟨[], (defects_nil_iff _).mp (by decide)⟩

/-- The text of `b`: the one text `Baseline.parse` reads as `b`. -/
def Baseline.write (b : Baseline) : String := String.ofList (ledgerOf b.entries).render

/-- The baseline whose text is `text`, if `text` is the text of one. -/
@[regula_decision]
def Baseline.parse (text : String) : Option Baseline :=
  match scanLedger text.toList with
  | some l =>
    if h : defects (entriesOf l) = [] ∧
        Ledger.render (Controlled.ledgerOf (entriesOf l)) = text.toList then
      some ⟨entriesOf l, (defects_nil_iff _).mp h.1⟩
    else none
  | none => none

/-- The fields of a sound entry are read back as that entry. -/
theorem Entry.ofFields_fields {e : Entry} (h : e.Sound) : Entry.ofFields e.fields = e := by
  obtain ⟨path, allowance⟩ := e
  cases allowance with
  | counts numbers =>
    have hsound := h.allowance
    simp only [Allowance.Sound] at hsound
    match numbers, hsound with
    | [marker, text], hsound =>
      have hmarker := hsound.2.1 marker (List.mem_cons_self ..)
      have hfrozen : marker ≠ Controlled.frozenMarker := fun heq =>
        absurd (heq ▸ hmarker) (by decide)
      have hgenerated : marker ≠ Controlled.generatedMarker := fun heq =>
        absurd (heq ▸ hmarker) (by decide)
      simp [Entry.fields, Entry.ofFields, hfrozen, hgenerated]
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _ :: _, _ => rfl
  | frozen digest => simp [Entry.fields, Entry.ofFields]
  | generated source =>
    simp [Entry.fields, Entry.ofFields,       show generatedMarker ≠ frozenMarker by decide]

/-- No field of a sound entry has a double quotation mark or a line feed. -/
theorem Entry.Sound.clean {e : Entry} (h : e.Sound) :
    ∀ field ∈ e.fields, '"' ∉ field ∧ '\n' ∉ field := by
  have hbare : ∀ {text : List Char}, Bare text → '"' ∉ text ∧ '\n' ∉ text := fun hb =>
    ⟨fun hmem => (hb '"' hmem).2.1 rfl, fun hmem => absurd (hb '\n' hmem).1 (by decide)⟩
  have hdigits : ∀ {text : List Char}, (∀ c ∈ text, c.isDigit = true ∨ ('a' ≤ c ∧ c ≤ 'f')) →
      '"' ∉ text ∧ '\n' ∉ text := fun hd =>
    ⟨fun hmem => absurd (hd '"' hmem) (by decide), fun hmem => absurd (hd '\n' hmem) (by decide)⟩
  obtain ⟨path, allowance⟩ := e
  intro field hfield
  have hsound := h.allowance
  cases allowance with
  | counts numbers =>
    simp only [Entry.fields, List.mem_cons] at hfield
    rcases hfield with rfl | hfield
    · exact hbare h.path.2
    · simp only [Allowance.Sound] at hsound
      exact hdigits fun c hc => .inl ((hsound.2.1 field hfield).2.1 c hc)
  | frozen digest =>
    simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false] at hfield
    rcases hfield with rfl | rfl | rfl
    · exact hbare h.path.2
    · decide
    · exact hdigits hsound.2
  | generated source =>
    simp only [Entry.fields, List.mem_cons, List.not_mem_nil, or_false] at hfield
    rcases hfield with rfl | rfl | rfl
    · exact hbare h.path.2
    · decide
    · exact hbare hsound.2

theorem Baseline.parse_write (b : Baseline) : Baseline.parse b.write = some b := by
  have hclean : (ledgerOf b.entries).clean = true := by
    simp only [ledgerOf, Ledger.clean, List.all_eq_true, List.mem_map, Bool.and_eq_true,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    rintro fields ⟨e, he, rfl⟩ field hfield
    exact (b.wellFormed.sound e he).clean field hfield
  have hback : entriesOf (ledgerOf b.entries) = b.entries := by
    rw [entriesOf, ledgerOf, List.map_map]
    conv => rhs; rw [← List.map_id b.entries]
    exact List.map_congr_left fun e he => Entry.ofFields_fields (b.wellFormed.sound e he)
  simp only [Baseline.parse, Baseline.write, String.toList_ofList, scanLedger_render _ hclean,
    hback]
  split
  · rfl
  · rename_i hrefused
    exact absurd ⟨(defects_nil_iff _).mpr b.wellFormed, trivial⟩ hrefused

theorem Baseline.write_of_parse (text : String) (b : Baseline)
    (h : Baseline.parse text = some b) : b.write = text := by
  unfold Baseline.parse at h
  split at h
  · split at h
    · rename_i l _ hl
      cases h
      have hrender : (ledgerOf (entriesOf l)).render = text.toList := by
        exact hl.2
      simp [Baseline.write, hrender, String.ofList_toList]
    · cases h
  · cases h

/-- Registered contract of the baseline parser, as a two-way decision: it accepts exactly the
texts that are the print of a baseline. It accepts the print of the baseline with no entry and
refuses the empty text. -/
theorem checked_baselineParse : Regula.ExecutableContract Baseline.parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ b, text = Baseline.write b)) :=
  ⟨.of_roundtrip Baseline.parse_write Baseline.write_of_parse Baseline.empty (unwritten := "")
    (by decide)⟩

/-- Why `text` is not the text of a baseline: each reason, with the number of its line. -/
def Baseline.explain (text : String) : List (Nat × String) :=
  match scanLedger text.toList with
  | none => [(1, "the text does not start with the lines before the entries of a baseline")]
  | some l =>
    if Ledger.render (Controlled.ledgerOf (entriesOf l)) = text.toList then defects (entriesOf l)
    else
      [(firstDifference 1 (linesOfEntries (entriesOf l)) (split '\n' text.toList),
        "the text is not the print of its baseline from this line on: a missing line feed at \
          the end of the text, or a line that the print writes otherwise")]

/-- `Baseline.explain` reports nothing exactly when `Baseline.parse` accepts the text. -/
theorem Baseline.explain_nil_iff (text : String) :
    Baseline.explain text = [] ↔ (Baseline.parse text).isSome = true := by
  unfold Baseline.explain Baseline.parse
  cases hscan : scanLedger text.toList with
  | none => simp
  | some l =>
    by_cases hrender : Ledger.render (Controlled.ledgerOf (entriesOf l)) = text.toList
    · by_cases hdefects : defects (entriesOf l) = [] <;> simp [hrender, hdefects]
    · simp [hrender]

/-! ## The gate (check B1) -/

/-- What a run observes of one tracked document. -/
structure Observed where
  /-- The path of the document. -/
  path : String
  /-- The SHA-256 digest of its content, in lowercase hexadecimal digits. Only a frozen entry
  reads it. -/
  digest : String
  /-- Its number of findings for each check, in the order of `Check.all`. Only an entry of
  numbers and a document with no entry read it. -/
  tally : List Nat
  deriving DecidableEq, Repr

/-- What an entry permits is what the run observes of its document: the numbers of findings
are the numbers of the entry, as `Nat.repr` writes them, or the digest is the digest of the
entry. A generated document is not read. -/
def Allowance.Permits (d : Observed) : Allowance → Prop
  | .counts numbers => numbers = d.tally.map fun n => (Nat.repr n).toList
  | .frozen digest => digest = d.digest.toList
  | .generated _ => True

/-- The baseline admits a document: each entry of its path permits what the run observes, and
a document with no entry of its path has no finding. -/
def Observed.Admitted (b : Baseline) (d : Observed) : Prop :=
  (∀ e ∈ b.entries, e.path = d.path.toList → e.allowance.Permits d) ∧
    ((∀ e ∈ b.entries, e.path ≠ d.path.toList) → ∀ n ∈ d.tally, n = 0)

/-- Each entry of the baseline has a document: a document, among `documents`, with the path of
the entry. -/
def Baseline.Documented (b : Baseline) (documents : List Observed) : Prop :=
  ∀ e ∈ b.entries, ∃ d ∈ documents, d.path.toList = e.path

instance (d : Observed) : DecidablePred (Allowance.Permits d) := fun allowance => by
  cases allowance <;> simp only [Allowance.Permits] <;> infer_instance

instance (b : Baseline) : DecidablePred (Observed.Admitted b) := fun d => by
  unfold Observed.Admitted
  infer_instance

/-- Check B1: the documents that the baseline does not admit, each with the line of its entry in
the print of the baseline, or the line where its entry would be, and with the reason. Then the
entries that have no document among `documents`, each with its line in the print of the
baseline and with the reason. -/
@[regula_decision]
def gate (b : Baseline) (documents : List Observed) : List (Nat × String) :=
  ((documents.filter fun d => !decide (Observed.Admitted b d)).map fun d =>
    if d.path.toList ∈ b.entries.map Entry.path then
      (lineOf b.entries d.path.toList,
        s!"{d.path} has other findings or another content than its entry permits: it has the \
          numbers {d.tally} and the digest `{d.digest}`")
    else
      (lineFor b.entries d.path.toList,
        s!"{d.path} has findings and no entry: it has the numbers {d.tally}")) ++
  (b.entries.filter fun e => !decide (∃ d ∈ documents, d.path.toList = e.path)).map fun e =>
    (lineOf b.entries e.path,
      s!"{String.ofList e.path}: the entry has no tracked Markdown document; remove the entry, \
        because a change that removes a document must remove its entry")

theorem gate_nil_iff (b : Baseline) (documents : List Observed) :
    gate b documents = [] ↔ (∀ d ∈ documents, d.Admitted b) ∧ b.Documented documents := by
  have h : gate b documents = [] ↔
      (∀ d ∈ documents, Observed.Admitted b d) ∧
        ∀ e ∈ b.entries, ∃ d ∈ documents, d.path.toList = e.path := by
    simp [gate, List.filter_eq_nil_iff]
  unfold Baseline.Documented
  rw [h]

/-- A digest for the witnesses of the contracts. -/
def sampleDigest : List Char := List.replicate 64 'a'

/-- A baseline with one entry of numbers, for the document `a`, and one frozen entry, for the
document `b`. -/
def Baseline.sample : Baseline :=
  ⟨[⟨['a'], .counts [['1'], ['0'], ['0'], ['0'], ['0'], ['0'], ['0'], ['0']]⟩,
      ⟨['b'], .frozen sampleDigest⟩],
    (defects_nil_iff _).mp (by decide)⟩

/-- Registered contract of the gate (check B1), as a two-way decision over the baseline and the
documents: it reports nothing exactly when the baseline admits each document
(`Observed.Admitted`) and each entry has a document (`Baseline.Documented`). It accepts the
sample baseline with the two documents of its entries. It refuses the sample baseline with no
document: no document is refused, and each entry has no document. -/
theorem checked_gate : Regula.ExecutableContract gate (fun run =>
    Regula.Decides (· = [])
      (fun input : Baseline × List Observed =>
        (∀ d ∈ input.2, d.Admitted input.1) ∧ input.1.Documented input.2)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => gate_nil_iff input.1 input.2)
    ⟨(Baseline.sample,
        [⟨"a", "", [1, 0, 0, 0, 0, 0, 0, 0]⟩, ⟨"b", String.ofList sampleDigest, []⟩]),
      by decide⟩
    ⟨(Baseline.sample, []), by decide⟩⟩

/-! ## The ratchet (check B2) -/

/-- The number `after` is not more than the number `before`, for two numbers in decimal digits
with no zero before them: it has fewer digits, or as many digits and no larger first digit that
differs. -/
abbrev NotMore (after before : List Char) : Prop :=
  after.length < before.length ∨ (after.length = before.length ∧ ¬before < after)

/-- What an entry permitted `before` covers what it permits `after`: the same class, with as
many numbers and no larger number, or with the same digest, or with the same source. -/
def Covers : Allowance → Allowance → Prop
  | .counts before, .counts after =>
    before.length = after.length ∧ ∀ pair ∈ before.zip after, NotMore pair.2 pair.1
  | .frozen before, .frozen after => before = after
  | .generated before, .generated after => before = after
  | _, _ => False

/-- What the ratchet compares a baseline with: the reference of the base revision. -/
inductive Reference where
  /-- The baseline of the base revision. -/
  | baseline (base : Baseline)
  /-- The base revision has no baseline: what the checks observe of each of its Markdown
  documents, with the vocabulary of the revision that is examined. -/
  | measured (documents : List Observed)

/-- What an entry permits is within what the checks observe of the document `d` of the base
revision: as many numbers and no number larger than the number of findings, as `Nat.repr`
writes it, or the digest of the document. A generated document is not read. -/
def Allowance.Within (d : Observed) : Allowance → Prop
  | .counts numbers =>
    numbers.length = d.tally.length ∧
      ∀ pair ∈ numbers.zip (d.tally.map fun n => (Nat.repr n).toList), NotMore pair.1 pair.2
  | .frozen digest => digest = d.digest.toList
  | .generated _ => True

/-- The baseline `head` keeps the baseline `base` of the base revision, for the tracked
documents `tracked`. Each entry of `head` has an entry of `base` with its path that covers it: no
new path, no larger number and no other class. Each frozen entry of `base` whose document is
tracked is an entry of `head` with the same digest. -/
def Keeps (base head : Baseline) (tracked : List String) : Prop :=
  (∀ e ∈ head.entries, ∃ f ∈ base.entries, f.path = e.path ∧ Covers f.allowance e.allowance) ∧
    ∀ f ∈ base.entries, ∀ digest ∈ (match f.allowance with
        | .frozen digest => some digest
        | _ => none),
      String.ofList f.path ∈ tracked →
        ∃ e ∈ head.entries, e.path = f.path ∧ e.allowance = .frozen digest

/-- The baseline `head` shrinks in relation to the reference of the base revision, for the
tracked documents `tracked`.

* The base revision has a baseline: the revision that is examined has a baseline, and that
  baseline keeps the baseline of the base revision (`Keeps`). A removed baseline does not shrink.
* The base revision has no baseline: each entry of `head`, if there is a baseline, has a
  document of the base revision with its path, and it is within what the checks observe of that
  document (`Allowance.Within`). Thus no entry is for a new document, and no entry permits more
  findings than the document of the base revision has. -/
def Shrinks (reference : Reference) (head : Option Baseline) (tracked : List String) : Prop :=
  match reference with
  | .baseline base => ∃ h ∈ head, Keeps base h tracked
  | .measured documents =>
    ∀ h ∈ head, ∀ e ∈ h.entries, ∃ d ∈ documents, d.path.toList = e.path ∧ e.allowance.Within d

instance : DecidableRel NotMore := fun after before => by
  unfold NotMore
  infer_instance

instance : DecidableRel Covers := fun before after => by
  cases before <;> cases after <;> simp only [Covers] <;> infer_instance

instance (d : Observed) : DecidablePred (Allowance.Within d) := fun allowance => by
  cases allowance <;> simp only [Allowance.Within] <;> infer_instance

/-- The digest of a frozen entry. -/
def Allowance.digest? : Allowance → Option (List Char)
  | .frozen digest => some digest
  | _ => none

/-- Check B2: what in `head` does not shrink in relation to the reference of the base revision,
each with its line in the print of `head`, or the line where it would be, and with the reason.
For a baseline of the base revision: the entries of `head` that no entry of the base revision
covers, the frozen entries of the base revision for tracked documents that `head` does not keep,
and the removal of the baseline. For a base revision with no baseline: the entries of `head`
that are not within what the checks observe of a document of the base revision. -/
@[regula_decision]
def ratchet (reference : Reference) (head : Option Baseline) (tracked : List String) :
    List (Nat × String) :=
  match reference, head with
  | .baseline _, none =>
    [(1, "the baseline of the base revision is removed: keep the file, with no entry when no \
      document has a finding")]
  | .baseline base, some head =>
    ((head.entries.filter fun e =>
        !decide (∃ f ∈ base.entries, f.path = e.path ∧
          Controlled.Covers f.allowance e.allowance)).map fun e =>
      (lineOf head.entries e.path,
        s!"{String.ofList e.path}: the entry is new, or it permits more than the entry of the \
          base revision or has another class")) ++
    (base.entries.flatMap fun f =>
      match f.allowance.digest? with
      | some digest =>
        if String.ofList f.path ∈ tracked →
            ∃ e ∈ head.entries, e.path = f.path ∧ e.allowance = .frozen digest then []
        else
          [(lineFor head.entries f.path,
            s!"{String.ofList f.path}: the frozen entry of the base revision is removed or \
              changed, and the document is tracked")]
      | none => [])
  | .measured _, none => []
  | .measured documents, some head =>
    (head.entries.filter fun e =>
        !decide (∃ d ∈ documents, d.path.toList = e.path ∧
          Allowance.Within d e.allowance)).map fun e =>
      (lineOf head.entries e.path,
        s!"{String.ofList e.path}: the base revision has no baseline, and it has no document \
          with this path, or the entry permits more than that document has in the base revision")

theorem ratchet_nil_iff (reference : Reference) (head : Option Baseline)
    (tracked : List String) :
    ratchet reference head tracked = [] ↔ Shrinks reference head tracked := by
  cases reference with
  | baseline base =>
    cases head with
    | none => simp [ratchet, Shrinks]
    | some head =>
      have h : ratchet (.baseline base) (some head) tracked = [] ↔
          (∀ e ∈ head.entries, ∃ f ∈ base.entries, f.path = e.path ∧
            Controlled.Covers f.allowance e.allowance) ∧
          ∀ f ∈ base.entries, ∀ digest ∈ (match f.allowance with
              | .frozen digest => some digest
              | _ => none),
            String.ofList f.path ∈ tracked →
              ∃ e ∈ head.entries, e.path = f.path ∧ e.allowance = .frozen digest := by
        simp only [ratchet, List.append_eq_nil_iff, List.map_eq_nil_iff,
          List.filter_eq_nil_iff, List.flatMap_eq_nil_iff, Option.mem_def, Bool.not_eq_true',
          decide_eq_false_iff_not, Classical.not_not]
        refine and_congr_right fun _ => forall₂_congr fun f _ => ?_
        cases hallowance : f.allowance with
        | frozen digest => simp [Allowance.digest?]
        | counts numbers => simp [Allowance.digest?]
        | generated source => simp [Allowance.digest?]
      rw [h]
      simp only [Shrinks, Keeps, Option.mem_def, Option.some.injEq, exists_eq_left']
  | measured documents =>
    cases head with
    | none => simp [ratchet, Shrinks]
    | some head =>
      have h : ratchet (.measured documents) (some head) tracked = [] ↔
          ∀ e ∈ head.entries, ∃ d ∈ documents, d.path.toList = e.path ∧
            Allowance.Within d e.allowance := by
        simp [ratchet, List.filter_eq_nil_iff]
      rw [h]
      simp only [Shrinks, Option.mem_def, Option.some.injEq, forall_eq']

/-- Registered contract of the ratchet (check B2), as a two-way decision over the reference of
the base revision, the baseline and the tracked paths: it reports nothing exactly when the
baseline shrinks in relation to the reference (`Shrinks`). It accepts the sample baseline in
relation to itself. It refuses the sample baseline for a base revision that has no baseline and
no document: each entry is for a new document. -/
theorem checked_ratchet : Regula.ExecutableContract ratchet (fun run =>
    Regula.Decides (· = [])
      (fun input : (Reference × Option Baseline) × List String =>
        Shrinks input.1.1 input.1.2 input.2)
      (Function.uncurry (Function.uncurry run))) :=
  ⟨.of_iff (fun input => ratchet_nil_iff input.1.1 input.1.2 input.2)
    ⟨((.baseline Baseline.sample, some Baseline.sample), ["b"]), by decide⟩
    ⟨((.measured [], some Baseline.sample), []), by decide⟩⟩

/-- The paths that a reference has: the paths of the entries of the baseline of the base
revision, or the paths of the documents of the base revision. -/
def Reference.paths : Reference → List (List Char)
  | .baseline base => base.entries.map Entry.path
  | .measured documents => documents.map fun d => d.path.toList

/-- A baseline that shrinks has no new path: the path of each entry is a path of the
reference. -/
theorem Shrinks.paths {reference : Reference} {head : Baseline} {tracked : List String}
    (h : Shrinks reference (some head) tracked) : ∀ e ∈ head.entries, e.path ∈ reference.paths := by
  intro e he
  cases reference with
  | baseline base =>
    obtain ⟨kept, hkept, hkeeps⟩ := h
    cases hkept
    obtain ⟨f, hf, hpath, -⟩ := hkeeps.1 e he
    exact List.mem_map.mpr ⟨f, hf, hpath⟩
  | measured documents =>
    obtain ⟨d, hd, hpath, -⟩ := h head rfl e he
    exact List.mem_map.mpr ⟨d, hd, hpath⟩

/-- The ratchet refuses the removal of a baseline: when the base revision has a baseline, a
revision with no baseline is refused, for each baseline and each list of tracked paths. -/
theorem ratchet_removed (base : Baseline) (tracked : List String) :
    ratchet (.baseline base) none tracked ≠ [] := by
  intro h
  obtain ⟨kept, hkept, -⟩ := (ratchet_nil_iff _ _ _).mp h
  cases hkept

/-- The two decisions together keep each frozen document: when the gate accepts the documents
for `head`, and the ratchet accepts `head` in relation to the baseline `base` for the paths of
those documents, a document with a frozen entry in `base` has the digest of that entry. Thus the
removal of a frozen entry does not let the document change. -/
theorem frozen_unchanged {base head : Baseline} {documents : List Observed}
    (hgate : gate head documents = [])
    (hratchet : ratchet (.baseline base) (some head) (documents.map (·.path)) = []) :
    ∀ d ∈ documents, ∀ f ∈ base.entries, ∀ digest, f.path = d.path.toList →
      f.allowance = .frozen digest → d.digest.toList = digest := by
  intro d hd f hf digest hpath hfrozen
  have hadmitted := ((gate_nil_iff head documents).mp hgate).1 d hd
  obtain ⟨kept, hkept, hkeeps⟩ := (ratchet_nil_iff (.baseline base) (some head) _).mp hratchet
  cases hkept
  have htracked : String.ofList f.path ∈ documents.map (·.path) := by
    rw [hpath, String.ofList_toList]
    exact List.mem_map_of_mem hd
  obtain ⟨e, he, hepath, heallowance⟩ :=
    hkeeps.2 f hf digest (by rw [hfrozen]; rfl) htracked
  have hpermits := hadmitted.1 e he (hepath.trans hpath)
  rw [heallowance] at hpermits
  exact hpermits.symm

/-- The two decisions together give no entry to a new document: when the gate accepted the
documents `before` of the base revision for its baseline `base`, and the ratchet accepts `head`
in relation to `base`, each entry of `head` has a document of `before` with its path. -/
theorem entry_has_base_document {base head : Baseline} {before : List Observed}
    {tracked : List String} (hgate : gate base before = [])
    (hratchet : ratchet (.baseline base) (some head) tracked = []) :
    ∀ e ∈ head.entries, ∃ d ∈ before, d.path.toList = e.path := by
  intro e he
  have hmem : e.path ∈ base.entries.map Entry.path :=
    ((ratchet_nil_iff _ _ _).mp hratchet).paths e he
  obtain ⟨f, hf, hpath⟩ := List.mem_map.mp hmem
  obtain ⟨d, hd, hdocument⟩ := ((gate_nil_iff base before).mp hgate).2 f hf
  exact ⟨d, hd, hdocument.trans hpath⟩

/-! ## The base revision of check B2

Check B2 compares the baseline with the state of a base revision. Which commit that is depends on
how the check was started (`Start`) and on what Git gives for the checked commit (`History`).
`Start.Base` states it, and `baseOf` decides it. Only the run of a developer takes a merge base.
A start that gives the commit before the change takes that commit itself, and a pull request
takes the first parent of the checked merge commit. No start replaces a base that Git does not
give. -/

/-- How a check of a repository was started, as far as the base revision reads it. -/
inductive Start where
  /-- The run of a developer, for a change to the branch that `revision` names: the base
  revision is the merge base of the checked commit and `revision`. -/
  | target (revision : String)
  /-- A start that gives the commit before the change, `commit`: the base revision is that
  commit itself, and no merge base is taken. -/
  | before (commit : String)
  /-- A pull request whose head is the commit `head`: the checked commit is the merge of `head`
  into the target branch, and the base revision is its first parent. -/
  | pull (head : String)
  /-- A start that gives no base revision, with the text that it gave. -/
  | unknown (text : String)
  deriving DecidableEq, Repr

/-- What Git gives for the checked commit and for the revision of a start. -/
structure History where
  /-- The full names of the parents of the checked commit, in order. -/
  parents : List String
  /-- The full name of the commit that the revision of the start names, if it names a commit. -/
  named : Option String
  /-- The merge base of the checked commit and that revision, if Git gives one. -/
  merged : Option String
  deriving DecidableEq, Repr

/-- `base` is the base revision of check B2 for `start`, with what Git gives.

* For the run of a developer, it is the merge base that Git gives.
* For a start that gives the commit before the change, it is the commit that the start names.
  What Git gives as a merge base has no effect.
* For a pull request, the checked commit has exactly two parents, the second parent is the head
  of the pull request, and `base` is the first parent.
* A start that gives no base revision has none. -/
def Start.Base (start : Start) (history : History) (base : String) : Prop :=
  match start with
  | .target _ => history.merged = some base
  | .before _ => history.named = some base
  | .pull head => history.parents = [base, head]
  | .unknown _ => False

/-- The base revision of check B2 for `start`, with what Git gives, if there is one. -/
@[regula_decision]
def baseOf (start : Start) (history : History) : Option String :=
  match start, history.parents with
  | .target _, _ => history.merged
  | .before _, _ => history.named
  | .pull head, [first, second] => if second = head then some first else none
  | _, _ => none

/-- `baseOf` gives exactly the base revision that `Start.Base` states. -/
theorem baseOf_eq_some_iff (start : Start) (history : History) (base : String) :
    baseOf start history = some base ↔ start.Base history base := by
  obtain ⟨parents, named, merged⟩ := history
  cases start with
  | target revision => exact Iff.rfl
  | before commit => exact Iff.rfl
  | unknown text => simp [baseOf, Start.Base]
  | pull head =>
    match parents with
    | [] => simp [baseOf, Start.Base]
    | [_] => simp [baseOf, Start.Base]
    | _ :: _ :: _ :: _ => simp [baseOf, Start.Base]
    | [first, second] =>
      by_cases h : second = head
      · simp [baseOf, Start.Base, h, eq_comm]
      · simp [baseOf, Start.Base, h]

/-- Registered contract of the base revision of check B2, as a two-way decision over the start
and what Git gives: `baseOf` gives a base revision exactly when `Start.Base` states one
(`baseOf_eq_some_iff` says which). It gives one for a start with the commit before the change
that Git has, and none for a start that gives no base revision. -/
theorem checked_baseOf : Regula.ExecutableContract baseOf (fun run =>
    Regula.Decides (·.isSome = true)
      (fun input : Start × History => ∃ base, input.1.Base input.2 base)
      (Function.uncurry run)) :=
  ⟨.of_iff
    (fun input => by
      simp only [Function.uncurry, Option.isSome_iff_exists, baseOf_eq_some_iff])
    ⟨(.before "a", ⟨[], some "a", none⟩), by decide⟩
    ⟨(.unknown "", ⟨[], none, none⟩), by decide⟩⟩

/-- A start that gives the commit before the change takes no merge base: its base revision is
the commit that it names, for each merge base and each list of parents that Git gives. Thus a
push that moves a branch back to an ancestor is compared with the commit before the push, not
with that ancestor. -/
theorem baseOf_before (commit : String) (history : History) :
    baseOf (.before commit) history = history.named := rfl

/-- The revision that a developer's run takes the merge base with. -/
def defaultTarget : String := "origin/main"

/-- The start that the environment variable of the check gives.

* The variable is not set: the run of a developer for `origin/main`.
* The variable is set: `before:` and a commit, or `pull:` and the head of a pull request. Each
  other text, also the empty text, gives no base revision. -/
def Start.read (environment : Option String) : Start :=
  match environment with
  | none => .target defaultTarget
  | some text =>
    match dropPrefix "before:".toList text.toList with
    | some commit => .before (String.ofList commit)
    | none =>
      match dropPrefix "pull:".toList text.toList with
      | some head => .pull (String.ofList head)
      | none => .unknown text

theorem Start.read_default : Start.read none = .target defaultTarget := rfl

/-- The variable `before:` with a commit gives that commit as the commit before the change. -/
theorem Start.read_before (commit : String) :
    Start.read (some ("before:" ++ commit)) = .before commit := by
  have hbefore : dropPrefix "before:".toList ("before:" ++ commit).toList = some commit.toList := by
    rw [String.toList_append]
    exact dropPrefix_append _ _
  simp only [Start.read, hbefore, String.ofList_toList]

/-- The variable `pull:` with a commit gives that commit as the head of a pull request. -/
theorem Start.read_pull (head : String) :
    Start.read (some ("pull:" ++ head)) = .pull head := by
  have hbefore : dropPrefix "before:".toList ("pull:" ++ head).toList = none := by
    simp [dropPrefix]
  have hpull : dropPrefix "pull:".toList ("pull:" ++ head).toList = some head.toList := by
    rw [String.toList_append]
    exact dropPrefix_append _ _
  simp only [Start.read, hbefore, hpull, String.ofList_toList]

/-- The empty variable gives no base revision: `origin/main` does not replace it. -/
theorem Start.read_empty : Start.read (some "") = .unknown "" := by decide

end Regula.Controlled
