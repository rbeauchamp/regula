module

public import Regula.Contract
meta import Regula.Decision

/-! # Intent section presence

Presence of a labelled Intent section in a registered material declaration's
docstring (standard §5.2; rules RG5002 and RG5003).

A docstring is read as its line-feed-separated lines (`docLines`). An *Intent section*
is a Markdown ATX heading line whose text is exactly `Intent`, followed by the lines
before the next heading line of equal or higher level (at most as many `#`) or the end
of the docstring, following CommonMark section nesting: deeper subsection headings stay
inside the section. The section is *nonempty* when one of its non-heading lines contains
a non-whitespace character; a subsection heading line is not content, but text under it is.

Heading lines follow CommonMark's ATX form without a closing sequence: after trailing
whitespace (including a carriage return) is removed, at most three spaces of indentation,
one to six `#`, then a space or tab (or the end of the line); the heading text is the
remainder with surrounding whitespace removed. Setext headings and closing sequences
(`# Intent #`) are not recognized. This line grammar is a definition: the theorems below
characterize the section structure over it, and `intentHeading_examples` checks
instances. Fenced code blocks are not tracked, so a heading-shaped line inside a fence
still counts as a heading. The recognition is case-sensitive.

This is presence and linkage only. The docstring is linked to its declaration by
Lean's `findDocString?`; nothing here judges whether the intent is adequate, whether
it matches the explanation or the elaborated declaration, or whether registration is
complete. Those comparisons remain the R-INTENT and R-DOC semantic-review obligations. -/

@[expose] public section

namespace RegulaPolicy.Intent

/-- Remove leading and trailing whitespace from one line. -/
def trim (line : List Char) : List Char :=
  ((line.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Remove trailing whitespace, including a carriage return before the line feed. -/
def trimEnd (line : List Char) : List Char :=
  (line.reverse.dropWhile Char.isWhitespace).reverse

/-- Remove at most `n` leading spaces (CommonMark permits three before a heading). -/
def dropIndent : Nat → List Char → List Char
  | n + 1, ' ' :: rest => dropIndent n rest
  | _, line => line

/-- The level and text of an ATX heading line, or `none` when the line is not a heading. -/
def heading? (line : List Char) : Option (Nat × List Char) :=
  let body := dropIndent 3 (trimEnd line)
  let level := (body.takeWhile (· == '#')).length
  if 1 ≤ level ∧ level ≤ 6 then
    match body.dropWhile (· == '#') with
    | [] => some (level, [])
    | c :: text => if c == ' ' || c == '\t' then some (level, trim text) else none
  else none

/-- The level (number of `#`) of an ATX heading line. -/
def headingLevel? (line : List Char) : Option Nat := (heading? line).map (·.1)

/-- The text of an ATX heading line. -/
def headingText? (line : List Char) : Option (List Char) := (heading? line).map (·.2)

/-- A heading line of any level. -/
def isHeading (line : List Char) : Bool := (heading? line).isSome

/-- A heading line labelled exactly `Intent`. -/
def isIntentHeading (line : List Char) : Bool := headingText? line == some "Intent".toList

/-- A heading of level at most `level`; it ends a section opened by a level-`level` heading. -/
def endsSection (level : Nat) (line : List Char) : Bool :=
  (headingLevel? line).any (decide <| · ≤ level)

/-- A line with at least one non-whitespace character. -/
def isContent (line : List Char) : Bool := line.any (!Char.isWhitespace ·)

/-- A non-heading line with content; a subsection heading line itself is not content. -/
def isText (line : List Char) : Bool := !isHeading line && isContent line

/-- Split at every line feed: the current (first) line and the lines after it. -/
def splitLinesAux : List Char → List Char × List (List Char)
  | [] => ([], [])
  | c :: rest =>
    let (line, lines) := splitLinesAux rest
    if c == '\n' then ([], line :: lines) else (c :: line, lines)

/-- Split characters at every line feed; a trailing line feed yields a final empty line.
A carriage return before it stays in the line and counts as whitespace. -/
def splitLines (cs : List Char) : List (List Char) :=
  (splitLinesAux cs).1 :: (splitLinesAux cs).2

/-- The docstring's lines, as characters. -/
def docLines (doc : String) : List (List Char) := splitLines doc.toList

/-- The specification: some level-`level` Intent heading is followed, before any heading
of level at most `level`, by a text line. `body` is an initial run of the section's lines.

It is stated over the line grammar `heading?` and Lean's `Char.isWhitespace`, with no test that
the scan calls: the heading is one that the grammar reads at `level` with the text `Intent`, no
line of `body` is a heading of level at most `level`, and a line of `body` is no heading and has
a character that is not whitespace. `intentSection_iff_scanned` connects these statements to
the tests of the scan. -/
def IntentSection (lines : List (List Char)) : Prop :=
  ∃ before heading level body after, lines = before ++ heading :: (body ++ after) ∧
    heading? heading = some (level, "Intent".toList) ∧
    (∀ line ∈ body, ∀ found, heading? line = some found → level < found.1) ∧
    ∃ line ∈ body, heading? line = none ∧ ∃ c ∈ line, c.isWhitespace = false

/-- The section structure as the tests of the scan state it: the form that the scan decides
directly (`hasIntentLines_iff_scanned`). It is a step of the proof of `hasIntentLines_iff`, and
no specification names it. -/
def ScannedSection (lines : List (List Char)) : Prop :=
  ∃ before heading level body after, lines = before ++ heading :: (body ++ after) ∧
    isIntentHeading heading = true ∧ headingLevel? heading = some level ∧
    (∀ line ∈ body, endsSection level line = false) ∧ ∃ line ∈ body, isText line = true

/-- A line is a heading labelled `Intent` whose level is `level` exactly when the line grammar
reads that level and that text. -/
theorem intentHeading_iff (line : List Char) (level : Nat) :
    (isIntentHeading line = true ∧ headingLevel? line = some level) ↔
      heading? line = some (level, "Intent".toList) := by
  unfold isIntentHeading headingLevel? headingText?
  cases heading? line with
  | none => simp
  | some found =>
    obtain ⟨foundLevel, text⟩ := found
    simp [and_comm]

/-- A line does not end a section of level `level` exactly when it is no heading of level at
most `level`. -/
theorem endsSection_eq_false_iff (level : Nat) (line : List Char) :
    endsSection level line = false ↔ ∀ found, heading? line = some found → level < found.1 := by
  unfold endsSection headingLevel?
  cases heading? line with
  | none => simp
  | some found => simp [Nat.not_le]

/-- A line is text exactly when it is no heading and has a character that is not whitespace. -/
theorem isText_iff (line : List Char) :
    isText line = true ↔ heading? line = none ∧ ∃ c ∈ line, c.isWhitespace = false := by
  simp [isText, isHeading, isContent]

/-- The specification holds exactly when the tests of the scan state the section. -/
theorem intentSection_iff_scanned (lines : List (List Char)) :
    IntentSection lines ↔ ScannedSection lines := by
  constructor
  · rintro ⟨before, heading, level, body, after, split, labelled, deeper, line, member, text⟩
    exact ⟨before, heading, level, body, after, split,
      ((intentHeading_iff heading level).mpr labelled).1,
      ((intentHeading_iff heading level).mpr labelled).2,
      fun l hl => (endsSection_eq_false_iff level l).mpr (deeper l hl),
      line, member, (isText_iff line).mpr text⟩
  · rintro ⟨before, heading, level, body, after, split, labelled, lvl, deeper, line, member, text⟩
    exact ⟨before, heading, level, body, after, split,
      (intentHeading_iff heading level).mp ⟨labelled, lvl⟩,
      fun l hl => (endsSection_eq_false_iff level l).mp (deeper l hl),
      line, member, (isText_iff line).mp text⟩

/-- Scan a section opened at `level`: text occurs before a heading that ends it. -/
def sectionHasContent (level : Nat) : List (List Char) → Bool
  | [] => false
  | line :: rest => !endsSection level line && (isText line || sectionHasContent level rest)

/-- Scan every line for an Intent heading whose section has text. -/
def hasIntentLines : List (List Char) → Bool
  | [] => false
  | line :: rest =>
    (isIntentHeading line && (headingLevel? line).any (sectionHasContent · rest)) ||
      hasIntentLines rest

/-- The executed decision for one docstring. -/
@[regula_decision]
def hasIntentSection (doc : String) : Bool := hasIntentLines (docLines doc)

theorem sectionHasContent_iff (level : Nat) (lines : List (List Char)) :
    sectionHasContent level lines = true ↔ ∃ body after, lines = body ++ after ∧
      (∀ line ∈ body, endsSection level line = false) ∧ ∃ line ∈ body, isText line = true := by
  induction lines with
  | nil => simp [sectionHasContent]
  | cons line rest ih =>
    simp only [sectionHasContent, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, ih]
    constructor
    · rintro ⟨heading, content | ⟨body, after, split, headings, found⟩⟩
      · exact ⟨[line], rest, rfl, by simpa using heading, line, by simp, content⟩
      · refine ⟨line :: body, after, by simp [split], ?_, ?_⟩
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact heading
          · exact headings l hl
        · obtain ⟨l, hl, hc⟩ := found
          exact ⟨l, List.mem_cons_of_mem _ hl, hc⟩
    · rintro ⟨body, after, split, headings, l, hl, hc⟩
      cases body with
      | nil => simp at hl
      | cons first body =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        refine ⟨headings line (by simp), ?_⟩
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Or.inl hc
        · exact Or.inr ⟨body, after, rfl, fun m hm => headings m (List.mem_cons_of_mem _ hm),
            l, hl, hc⟩

/-- The line scanner decides exactly the section that its tests state. -/
theorem hasIntentLines_iff_scanned (lines : List (List Char)) :
    hasIntentLines lines = true ↔ ScannedSection lines := by
  induction lines with
  | nil => simp [hasIntentLines, ScannedSection]
  | cons line rest ih =>
    simp only [hasIntentLines, Bool.or_eq_true, Bool.and_eq_true, Option.any_eq_true,
      sectionHasContent_iff, ih, ScannedSection]
    constructor
    · rintro (⟨heading, level, lvl, body, after, split, headings, found⟩ |
          ⟨before, h, level, body, after, split, rest'⟩)
      · exact ⟨[], line, level, body, after, by simp [split], heading, lvl, headings, found⟩
      · exact ⟨line :: before, h, level, body, after, by simp [split], rest'⟩
    · rintro ⟨before, h, level, body, after, split, heading, lvl, headings, found⟩
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        exact Or.inl ⟨heading, level, lvl, body, after, rfl, headings, found⟩
      | cons first before =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, rfl⟩ := split
        exact Or.inr ⟨before, h, level, body, after, rfl, heading, lvl, headings, found⟩

/-- The line scanner decides exactly `IntentSection`. -/
theorem hasIntentLines_iff (lines : List (List Char)) :
    hasIntentLines lines = true ↔ IntentSection lines :=
  (hasIntentLines_iff_scanned lines).trans (intentSection_iff_scanned lines).symm

/-- The executed docstring decision accepts exactly the docstrings with a nonempty
labelled Intent section. -/
theorem hasIntentSection_iff (doc : String) :
    hasIntentSection doc = true ↔ IntentSection (docLines doc) :=
  hasIntentLines_iff _

instance (lines : List (List Char)) : Decidable (IntentSection lines) :=
  decidable_of_iff _ (hasIntentLines_iff lines)

/-- Splitting loses no character and invents none: rejoining the lines with line feeds
restores the docstring's characters. -/
theorem splitLines_intercalate (cs : List Char) : ['\n'].intercalate (splitLines cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    unfold splitLines at ih ⊢
    simp only [splitLinesAux]
    generalize splitLinesAux rest = p at ih ⊢
    obtain ⟨line, lines⟩ := p
    by_cases hc : c = '\n'
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [List.intercalate_cons_cons, ih]
      rfl
    · simp only [beq_iff_eq, hc, ↓reduceIte]
      cases lines with
      | nil => simpa [List.intercalate] using ih
      | cons l ls =>
        rw [List.intercalate_cons_cons] at ih ⊢
        rw [← ih]
        rfl

/-- No line contains a line feed. -/
theorem newline_not_mem_splitLines (cs : List Char) : ∀ line ∈ splitLines cs, '\n' ∉ line := by
  induction cs with
  | nil => simp [splitLines, splitLinesAux]
  | cons c rest ih =>
    unfold splitLines at ih ⊢
    simp only [splitLinesAux]
    generalize splitLinesAux rest = p at ih ⊢
    obtain ⟨line, lines⟩ := p
    by_cases hc : c = '\n'
    · subst hc
      simp only [beq_self_eq_true, ↓reduceIte]
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · simp
      · exact ih l hl
    · simp only [beq_iff_eq, hc, ↓reduceIte]
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · simp only [List.mem_cons, not_or]
        exact ⟨fun h => hc h.symm, ih _ (by simp)⟩
      · exact ih l (List.mem_cons_of_mem _ hl)

/-- Non-vacuity: a docstring with an Intent section is accepted. -/
theorem intentSection_example :
    IntentSection (docLines "Claim.\n\n## Intent\nWhy the claim is required.") :=
  (hasIntentSection_iff _).mp (by decide)

/-- Non-vacuity: text under a subsection of the Intent section is accepted. -/
theorem structured_intentSection_example :
    IntentSection (docLines "Claim.\n\n# Intent\n## Requirement\nWhy the claim is required.") :=
  (hasIntentSection_iff _).mp (by decide)

/-- Kernel-checked instances of the documented line grammar (not a universal
characterization of it): any level from one to six (the number of `#`), trailing
whitespace and a CRLF carriage return are accepted; a missing separator, four spaces of
indentation, a closing sequence, and a different case are refused. -/
theorem intentHeading_examples :
    isIntentHeading "# Intent".toList = true ∧ isIntentHeading "###### Intent  ".toList = true ∧
    headingLevel? "###### Intent  ".toList = some 6 ∧
    isIntentHeading "   # Intent\r".toList = true ∧ isHeading "#\r".toList = true ∧
    isIntentHeading "#Intent".toList = false ∧ isIntentHeading "    # Intent".toList = false ∧
    isIntentHeading "# Intent #".toList = false ∧ isIntentHeading "# intent".toList = false := by
  decide

/-- An Intent heading followed directly by another heading has an empty section. -/
theorem empty_intentSection_refused :
    ¬ IntentSection (docLines "Claim.\n\n## Intent\n\n## Notes\nOther text.") :=
  fun h => absurd ((hasIntentSection_iff _).mpr h) (by decide)

/-- A higher-level heading ends the Intent section, so text after it does not count. -/
theorem higher_heading_ends_intentSection :
    ¬ IntentSection (docLines "Claim.\n\n## Intent\n# Next\nOther text.") :=
  fun h => absurd ((hasIntentSection_iff _).mpr h) (by decide)

/-- A subsection heading line alone is not Intent content. -/
theorem subsection_heading_alone_refused :
    ¬ IntentSection (docLines "Claim.\n\n# Intent\n## Requirement") :=
  fun h => absurd ((hasIntentSection_iff _).mpr h) (by decide)

end RegulaPolicy.Intent

namespace RegulaPolicy
open Intent

/-- The documentation obligations a registered public material declaration can fail. -/
inductive MaterialDocumentationFailure where
  /-- No docstring is attached (RG5002). -/
  | missingDocstring
  /-- A docstring is attached, but it has no nonempty Intent section (RG5003). -/
  | missingIntent
  deriving Repr, DecidableEq

/-- A registered public material declaration has a docstring carrying a nonempty
labelled Intent section. Adequacy of either text remains semantic review. -/
def MaterialDocumentationOK (docstring : Option String) : Prop :=
  ∃ doc, docstring = some doc ∧ IntentSection (docLines doc)

/-- The executed classification of one observed docstring. -/
@[regula_decision]
def materialDocumentationFailure : Option String → Option MaterialDocumentationFailure
  | none => some .missingDocstring
  | some doc => if hasIntentSection doc then none else some .missingIntent

/-- No failure is reported exactly when the obligation holds. -/
theorem materialDocumentationFailure_eq_none_iff (docstring : Option String) :
    materialDocumentationFailure docstring = none ↔ MaterialDocumentationOK docstring := by
  cases docstring with
  | none => simp [materialDocumentationFailure, MaterialDocumentationOK]
  | some doc =>
    by_cases h : hasIntentSection doc = true
    · simp [materialDocumentationFailure, MaterialDocumentationOK, h, ← hasIntentSection_iff]
    · simp [materialDocumentationFailure, MaterialDocumentationOK, h, ← hasIntentSection_iff]

/-- RG5002 is reported exactly for a missing docstring. -/
theorem materialDocumentationFailure_eq_missingDocstring_iff (docstring : Option String) :
    materialDocumentationFailure docstring = some .missingDocstring ↔ docstring = none := by
  cases docstring with
  | none => simp [materialDocumentationFailure]
  | some doc =>
    by_cases h : hasIntentSection doc = true <;> simp [materialDocumentationFailure, h]

/-- RG5003 is reported exactly for a present docstring without a nonempty Intent section. -/
theorem materialDocumentationFailure_eq_missingIntent_iff (docstring : Option String) :
    materialDocumentationFailure docstring = some .missingIntent ↔
      ∃ doc, docstring = some doc ∧ ¬ IntentSection (docLines doc) := by
  cases docstring with
  | none => simp [materialDocumentationFailure]
  | some doc =>
    by_cases h : hasIntentSection doc = true
    · simp [materialDocumentationFailure, h, ← hasIntentSection_iff]
    · simp [materialDocumentationFailure, h, ← hasIntentSection_iff]

instance (docstring : Option String) : Decidable (MaterialDocumentationOK docstring) :=
  decidable_of_iff _ (materialDocumentationFailure_eq_none_iff docstring)

/-- `hasIntentSection` accepts exactly the docstrings whose lines have a nonempty Intent section
(`hasIntentSection_iff`): it accepts one with such a section and refuses the empty docstring.
`IntentSection` is stated over the line structure and the line grammar `heading?`, without the
executed scan and without the tests that the scan calls. -/
theorem checked_hasIntentSection : Regula.ExecutableContract hasIntentSection
    (Regula.Decides (· = true) fun doc => IntentSection (docLines doc)) :=
  ⟨.of_iff hasIntentSection_iff
    ⟨"Claim.\n\n## Intent\nWhy the claim is required.", by decide⟩ ⟨"", by decide⟩⟩

/-- `materialDocumentationFailure` reports no failure exactly when the documentation obligation
holds (`materialDocumentationFailure_eq_none_iff`): none for a docstring with an Intent section,
and a failure for a missing docstring. -/
theorem checked_materialDocumentationFailure :
    Regula.ExecutableContract materialDocumentationFailure
      (Regula.Decides (· = none) MaterialDocumentationOK) :=
  ⟨.of_iff materialDocumentationFailure_eq_none_iff
    ⟨some "Claim.\n\n## Intent\nWhy the claim is required.", by decide⟩ ⟨none, by decide⟩⟩

end RegulaPolicy
