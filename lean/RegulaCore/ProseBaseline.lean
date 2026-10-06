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
- `Observed`, `Observed.Admitted`, `gate`, `checked_gate` (check B1): a repository is accepted
  when each document has the findings its entry permits, and no finding without an entry.
- `Covers`, `Shrinks`, `ratchet`, `checked_ratchet` (check B2): a baseline is accepted in
  relation to the baseline of a base revision when it has no new path, no larger number and no
  other class, and when each frozen entry of a tracked document is kept.
- `frozen_unchanged`: the two decisions together keep the digest of each frozen document.
- `lineOf`, `lineOf_spec`: the line of the entry of a path in the print.

## Specifications

`Observed.Admitted` and `Shrinks` are statements about the entries, with no call of a recursive
function of the project. They are decidable by their form, and the two decisions evaluate them.
A number of an entry is a text of decimal digits: two numbers are compared as such texts
(`NotMore`), and a number of findings is compared with the text that `Nat.repr` gives for it.

## Boundaries

`checked_gate` is about the tallies and digests given: that a digest is the SHA-256 of a file
rests on the tool that computes it, that the documents given are the tracked ones rests on Git,
and that a tally is the document's rests on the reading of the document
(`RegulaCore.ControlledProse`). `checked_ratchet` is about the two baselines and the paths
given: that the first is the baseline of the base revision rests on Git.
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
    if marker = frozenMarker then ⟨path, .frozen text⟩
    else if marker = generatedMarker then ⟨path, .generated text⟩
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

instance : DecidablePred Allowance.Sound := fun allowance => by
  cases allowance <;> simp only [Allowance.Sound] <;> infer_instance

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

/-- The entries of a ledger. -/
def entriesOf (l : Ledger) : List Entry := l.entries.map Entry.ofFields

/-- The lines of the print of `entries`. -/
def linesOfEntries (entries : List Entry) : List (List Char) := (ledgerOf entries).lines

/-- The number of the line of the print of `entries` that has the entry of `path`, counting
from 1: the line of the first entry with that path. -/
def lineOf (entries : List Entry) (path : List Char) : Nat :=
  ledgerHead.length + (entries.map Entry.path).idxOf path + 1

/-- The number of the line of the print of `entries` where an entry of `path` would be: the
line after the entries whose paths are before `path`. -/
def lineFor (entries : List Entry) (path : List Char) : Nat :=
  ledgerHead.length + (entries.takeWhile fun e => e.path < path).length + 1

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
  simp only [linesOfEntries, ledgerOf, Ledger.lines, lineOf, Nat.add_sub_cancel,
    List.append_assoc]
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
  (if e.path ≠ [] ∧ Bare e.path then []
    else ["the path is empty or has a character that a JSON string writes with an escape"]) ++
  (if e.allowance.Sound then []
    else ["an entry has a path and then eight numbers of which one is not zero, or `frozen` \
      and a digest of 64 lowercase hexadecimal digits, or `generated` and a source"])

theorem Entry.defects_nil_iff (e : Entry) : e.defects = [] ↔ e.Sound := by
  simp only [Entry.defects, List.append_eq_nil_iff, ite_nil_iff]
  exact ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

/-- The defects of `entries`, each with the line of the print it is about. -/
def defects (entries : List Entry) : List (Nat × String) :=
  (entries.flatMap fun e => e.defects.map fun reason => (lineOf entries e.path, reason)) ++
    (unordered Entry.path Entry.path entries).map fun (path, reason) =>
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
    if h : defects (entriesOf l) = [] ∧ (ledgerOf (entriesOf l)).render = text.toList then
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
      have hfrozen : marker ≠ frozenMarker := fun heq => absurd (heq ▸ hmarker) (by decide)
      have hgenerated : marker ≠ generatedMarker := fun heq =>
        absurd (heq ▸ hmarker) (by decide)
      simp [Entry.fields, Entry.ofFields, hfrozen, hgenerated]
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _ :: _, _ => rfl
  | frozen digest => simp [Entry.fields, Entry.ofFields]
  | generated source =>
    simp [Entry.fields, Entry.ofFields, show generatedMarker ≠ frozenMarker by decide]

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
      simp [Baseline.write, hl.2, String.ofList_toList]
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
    if (ledgerOf (entriesOf l)).render = text.toList then defects (entriesOf l)
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
    by_cases hrender : (ledgerOf (entriesOf l)).render = text.toList
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

instance (d : Observed) : DecidablePred (Allowance.Permits d) := fun allowance => by
  cases allowance <;> simp only [Allowance.Permits] <;> infer_instance

/-- The baseline admits a document: each entry of its path permits what the run observes, and
a document with no entry of its path has no finding. -/
def Observed.Admitted (b : Baseline) (d : Observed) : Prop :=
  (∀ e ∈ b.entries, e.path = d.path.toList → e.allowance.Permits d) ∧
    ((∀ e ∈ b.entries, e.path ≠ d.path.toList) → ∀ n ∈ d.tally, n = 0)

instance (b : Baseline) : DecidablePred (Observed.Admitted b) := fun d => by
  unfold Observed.Admitted
  infer_instance

/-- Check B1: the documents that the baseline does not admit, each with the line of its entry in
the print of the baseline, or the line where its entry would be, and with the reason. -/
@[regula_decision]
def gate (b : Baseline) (documents : List Observed) : List (Nat × String) :=
  (documents.filter fun d => !decide (d.Admitted b)).map fun d =>
    if d.path.toList ∈ b.entries.map Entry.path then
      (lineOf b.entries d.path.toList,
        s!"{d.path} has other findings or another content than its entry permits: it has the \
          numbers {d.tally} and the digest `{d.digest}`")
    else
      (lineFor b.entries d.path.toList,
        s!"{d.path} has findings and no entry: it has the numbers {d.tally}")

theorem gate_nil_iff (b : Baseline) (documents : List Observed) :
    gate b documents = [] ↔ ∀ d ∈ documents, d.Admitted b := by
  simp [gate, List.filter_eq_nil_iff]

/-- A digest for the witnesses of the contracts. -/
def sampleDigest : List Char := List.replicate 64 'a'

/-- A baseline with one entry of numbers, for the document `a`, and one frozen entry, for the
document `b`. -/
def Baseline.sample : Baseline :=
  ⟨[⟨['a'], .counts [['1'], ['0'], ['0'], ['0'], ['0'], ['0'], ['0'], ['0']]⟩,
      ⟨['b'], .frozen sampleDigest⟩],
    (defects_nil_iff _).mp (by decide)⟩

/-- Registered contract of the gate (check B1), as a two-way decision over the baseline and the
documents: it reports nothing exactly when the baseline admits each document. It accepts no
document and refuses a document with one finding and no entry. -/
theorem checked_gate : Regula.ExecutableContract gate (fun run =>
    Regula.Decides (· = [])
      (fun input : Baseline × List Observed => ∀ d ∈ input.2, d.Admitted input.1)
      (Function.uncurry run)) :=
  ⟨.of_iff (fun input => gate_nil_iff input.1 input.2)
    ⟨(Baseline.empty, []), by decide⟩
    ⟨(Baseline.empty, [⟨"a", "", [1]⟩]), by decide⟩⟩

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

instance : DecidableRel Covers := fun before after => by
  cases before <;> cases after <;> simp only [Covers] <;> infer_instance

/-- The baseline `head` shrinks in relation to the baseline `base` of the base revision, for the
tracked documents `tracked`. Each entry of `head` has an entry of `base` with its path that
covers it: no new path, no larger number and no other class. Each frozen entry of `base` whose
document is tracked is an entry of `head` with the same digest. A base revision with no baseline
permits each baseline. -/
def Shrinks (base : Option Baseline) (head : Baseline) (tracked : List String) : Prop :=
  ∀ b ∈ base,
    (∀ e ∈ head.entries, ∃ f ∈ b.entries, f.path = e.path ∧ Covers f.allowance e.allowance) ∧
      ∀ f ∈ b.entries, ∀ digest ∈ (match f.allowance with
          | .frozen digest => some digest
          | _ => none),
        String.ofList f.path ∈ tracked →
          ∃ e ∈ head.entries, e.path = f.path ∧ e.allowance = .frozen digest

/-- The digest of a frozen entry. -/
def Allowance.digest? : Allowance → Option (List Char)
  | .frozen digest => some digest
  | _ => none

/-- Check B2: the entries of `head` that no entry of `base` covers, and the frozen entries of
`base` for tracked documents that `head` does not keep, each with its line in the print of
`head`, or the line where it would be, and with the reason. -/
@[regula_decision]
def ratchet (base : Option Baseline) (head : Baseline) (tracked : List String) :
    List (Nat × String) :=
  match base with
  | none => []
  | some b =>
    ((head.entries.filter fun e =>
        !decide (∃ f ∈ b.entries, f.path = e.path ∧ Covers f.allowance e.allowance)).map fun e =>
      (lineOf head.entries e.path,
        s!"{String.ofList e.path}: the entry is new, or it permits more than the entry of the \
          base revision or has another class")) ++
    (b.entries.flatMap fun f =>
      match f.allowance.digest? with
      | some digest =>
        if String.ofList f.path ∈ tracked →
            ∃ e ∈ head.entries, e.path = f.path ∧ e.allowance = .frozen digest then []
        else
          [(lineFor head.entries f.path,
            s!"{String.ofList f.path}: the frozen entry of the base revision is removed or \
              changed, and the document is tracked")]
      | none => [])

theorem ratchet_nil_iff (base : Option Baseline) (head : Baseline) (tracked : List String) :
    ratchet base head tracked = [] ↔ Shrinks base head tracked := by
  cases base with
  | none => simp [ratchet, Shrinks]
  | some b =>
    simp only [ratchet, Shrinks, List.append_eq_nil_iff, List.map_eq_nil_iff,
      List.filter_eq_nil_iff, List.flatMap_eq_nil_iff, Option.mem_def, Option.some.injEq,
      forall_eq', Bool.not_eq_true', decide_eq_false_iff_not, Classical.not_not]
    refine and_congr_right fun _ => forall₂_congr fun f _ => ?_
    cases hallowance : f.allowance with
    | frozen digest => simp [Allowance.digest?]
    | counts numbers => simp [Allowance.digest?]
    | generated source => simp [Allowance.digest?]

/-- Registered contract of the ratchet (check B2), as a two-way decision over the two baselines
and the tracked paths: it reports nothing exactly when the baseline shrinks in relation to the
baseline of the base revision. It accepts the sample baseline in relation to itself and refuses
it in relation to the baseline with no entry. -/
theorem checked_ratchet : Regula.ExecutableContract ratchet (fun run =>
    Regula.Decides (· = [])
      (fun input : (Option Baseline × Baseline) × List String =>
        Shrinks input.1.1 input.1.2 input.2)
      (Function.uncurry (Function.uncurry run))) :=
  ⟨.of_iff (fun input => ratchet_nil_iff input.1.1 input.1.2 input.2)
    ⟨((some Baseline.sample, Baseline.sample), ["b"]), by decide⟩
    ⟨((some Baseline.empty, Baseline.sample), []), by decide⟩⟩

/-- The two decisions together keep each frozen document: when the gate accepts the documents
for `head`, and the ratchet accepts `head` in relation to `base` for the paths of those
documents, a document with a frozen entry in `base` has the digest of that entry. Thus the
removal of a frozen entry does not let the document change. -/
theorem frozen_unchanged {base head : Baseline} {documents : List Observed}
    (hgate : gate head documents = [])
    (hratchet : ratchet (some base) head (documents.map (·.path)) = []) :
    ∀ d ∈ documents, ∀ f ∈ base.entries, ∀ digest, f.path = d.path.toList →
      f.allowance = .frozen digest → d.digest.toList = digest := by
  intro d hd f hf digest hpath hfrozen
  have hadmitted := (gate_nil_iff head documents).mp hgate d hd
  have hshrinks := (ratchet_nil_iff (some base) head _).mp hratchet base rfl
  have htracked : String.ofList f.path ∈ documents.map (·.path) := by
    rw [hpath, String.ofList_toList]
    exact List.mem_map_of_mem hd
  obtain ⟨e, he, hepath, heallowance⟩ :=
    hshrinks.2 f hf digest (by rw [hfrozen]; rfl) htracked
  have hpermits := hadmitted.1 e he (hepath.trans hpath)
  rw [heallowance] at hpermits
  exact hpermits.symm

end Regula.Controlled
