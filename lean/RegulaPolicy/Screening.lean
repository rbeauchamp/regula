module

public import RegulaPolicy.Intent
public import Regula.Contract

/-! # Intent screen decisions

Pure decisions of the opt-in probabilistic intent screen (`intentScreen`,
`docs/guides/intent-screening.md`).

A screen asks a pinned judgment model narrow questions about one material claim: whether the
formal claim guarantees each clause of its written Intent section (standard §5.2), how its
strength compares with the intent, and three targeted checks. Each answer is a probability.
This module owns everything about those answers that is not a judgment:

* `Decimal` compares the service's decimal probabilities exactly; no binary floating point
  touches a threshold decision.
* `Thresholds` is the user's severity mapping, well formed by construction
  (`error ≤ warning ≤ information`); `classify` maps a support probability to a finding
  severity in the rule-severity vocabulary, and
  `route` decides whether a result escalates to review.
* `intentClauses` splits a docstring's Intent section into clauses, and `discharge?` reads a
  clause's reference to a kernel-checked discharge theorem.
* `PinnedModel` admits only an exact versioned model identifier, never a moving alias.

Nothing here judges a clause, and no definition here can record a claim as checked or its
R-INTENT review as completed: a screened result is its own evidence class
(`RegulaCore.Screening`). The operational adapter in `Regula.Screen` runs these definitions
through their `ExecutableContract` registrations; network, process and service behavior stay
outside these proofs. -/

@[expose] public section

namespace RegulaPolicy.Screening
open RegulaPolicy.Intent

/-! ## Exact decimal probabilities -/

/-- A nonnegative decimal number with value `mantissa / 10 ^ exponent`. JSON numbers are
decimal text, so the service's probabilities are represented without rounding. -/
structure Decimal where
  mantissa : Nat
  exponent : Nat
  deriving Repr, DecidableEq

namespace Decimal

/-- Exact order by cross-multiplication: `a / 10^i ≤ b / 10^j` iff `a * 10^j ≤ b * 10^i`. -/
protected def Le (a b : Decimal) : Prop :=
  a.mantissa * 10 ^ b.exponent ≤ b.mantissa * 10 ^ a.exponent

instance : LE Decimal := ⟨Decimal.Le⟩

instance (a b : Decimal) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.mantissa * 10 ^ b.exponent ≤ b.mantissa * 10 ^ a.exponent))

/-- Strict order is the negation of the reverse order (the order is total). -/
instance : LT Decimal := ⟨fun a b => ¬ b ≤ a⟩

instance (a b : Decimal) : Decidable (a < b) := inferInstanceAs (Decidable (¬ b ≤ a))

theorem pow_ten_pos (e : Nat) : 0 < 10 ^ e := Nat.pow_pos (by decide)

theorem le_refl (a : Decimal) : a ≤ a := Nat.le_refl _

theorem le_trans {a b c : Decimal} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  have h1 : a.mantissa * 10 ^ b.exponent ≤ b.mantissa * 10 ^ a.exponent := hab
  have h2 : b.mantissa * 10 ^ c.exponent ≤ c.mantissa * 10 ^ b.exponent := hbc
  change a.mantissa * 10 ^ c.exponent ≤ c.mantissa * 10 ^ a.exponent
  apply Nat.le_of_mul_le_mul_right (c := 10 ^ b.exponent) _ (pow_ten_pos _)
  calc a.mantissa * 10 ^ c.exponent * 10 ^ b.exponent
      = a.mantissa * 10 ^ b.exponent * 10 ^ c.exponent := Nat.mul_right_comm ..
    _ ≤ b.mantissa * 10 ^ a.exponent * 10 ^ c.exponent := Nat.mul_le_mul_right _ h1
    _ = b.mantissa * 10 ^ c.exponent * 10 ^ a.exponent := Nat.mul_right_comm ..
    _ ≤ c.mantissa * 10 ^ b.exponent * 10 ^ a.exponent := Nat.mul_le_mul_right _ h2
    _ = c.mantissa * 10 ^ a.exponent * 10 ^ b.exponent := Nat.mul_right_comm ..

theorem le_total (a b : Decimal) : a ≤ b ∨ b ≤ a := Nat.le_total _ _

theorem lt_iff_not_le {a b : Decimal} : a < b ↔ ¬ b ≤ a := Iff.rfl

theorem le_of_lt {a b : Decimal} (h : a < b) : a ≤ b := (le_total a b).resolve_right h

theorem lt_of_lt_of_le {a b c : Decimal} (hab : a < b) (hbc : b ≤ c) : a < c :=
  fun hca => hab (le_trans hbc hca)

theorem lt_of_le_of_lt {a b c : Decimal} (hab : a ≤ b) (hbc : b < c) : a < c :=
  fun hca => hbc (le_trans hca hab)

/-- The value one. -/
def one : Decimal := ⟨1, 0⟩

/-- Exact sum: `a / 10^i + b / 10^j = (a * 10^j + b * 10^i) / 10^(i+j)`. -/
def add (a b : Decimal) : Decimal :=
  ⟨a.mantissa * 10 ^ b.exponent + b.mantissa * 10 ^ a.exponent, a.exponent + b.exponent⟩

/-- Decimal text of the exact value, without trailing fractional zeros, for evidence records
(`0.93`, `1`, `0.05`). -/
def render (d : Decimal) : String :=
  let whole := d.mantissa / 10 ^ d.exponent
  let digits := toString (d.mantissa % 10 ^ d.exponent)
  let fraction := (("".pushn '0' (d.exponent - digits.length) ++ digits).toList.reverse.dropWhile (· == '0')).reverse
  if fraction.isEmpty then toString whole else s!"{whole}.{String.ofList fraction}"

/-- Instances of the exact order and of rescaling invariance. -/
theorem order_examples :
    (⟨93, 2⟩ : Decimal) ≤ ⟨930, 3⟩ ∧ (⟨930, 3⟩ : Decimal) ≤ ⟨93, 2⟩ ∧
    (⟨2, 1⟩ : Decimal) < ⟨21, 2⟩ ∧ ¬ (⟨6, 1⟩ : Decimal) < ⟨6, 1⟩ ∧
    add ⟨12, 2⟩ ⟨3, 1⟩ = ⟨420, 3⟩ ∧ (add ⟨12, 2⟩ ⟨3, 1⟩) ≤ ⟨42, 2⟩ := by
  decide

end Decimal

/-- A probability: an exact decimal in `[0, 1]`. -/
abbrev Probability := { p : Decimal // p ≤ Decimal.one }

/-- Admit a JSON number (an integer mantissa and a decimal exponent, as `Lean.JsonNumber`
stores it) as a probability. Negative or greater-than-one values are refused. -/
def probability? (mantissa : Int) (exponent : Nat) : Option Probability :=
  match mantissa with
  | .ofNat m => if h : (⟨m, exponent⟩ : Decimal) ≤ Decimal.one then some ⟨⟨m, exponent⟩, h⟩ else none
  | .negSucc _ => none

/-- Admission is exact: a value is admitted exactly when it is nonnegative and at most one,
and it is admitted unchanged. -/
theorem probability?_eq_some_iff (mantissa : Int) (exponent : Nat) (p : Probability) :
    probability? mantissa exponent = some p ↔
      ∃ m : Nat, mantissa = m ∧ p.val = ⟨m, exponent⟩ := by
  cases mantissa with
  | ofNat m =>
    simp only [probability?]
    split
    · constructor
      · intro h; cases h; exact ⟨m, rfl, rfl⟩
      · rintro ⟨m', hm, hp⟩
        cases Int.ofNat.inj hm
        exact congrArg some (Subtype.ext hp.symm)
    · rename_i hle
      simp only [reduceCtorEq, false_iff, not_exists, not_and]
      intro m' hm hp
      cases Int.ofNat.inj hm
      exact hle (hp ▸ p.property)
  | negSucc n =>
    simp only [probability?, reduceCtorEq, false_iff, not_exists, not_and]
    intro m hm
    cases hm

/-! ## Severity mapping and routing -/

/-- Severity of a screening finding, in the rule-severity vocabulary (`Regula.Severity`:
error, warning, information). A screen never produces a checked or passing verdict. -/
inductive ScreenSeverity where
  | information | warning | error
  deriving Repr, DecidableEq

/-- Order of findings: no finding, then information, then warning, then error. -/
def rank : Option ScreenSeverity → Nat
  | none => 0
  | some .information => 1
  | some .warning => 2
  | some .error => 3

/-- The user's severity mapping for one judgment: a support probability below `error` is an
error, below `warning` a warning, below `information` information. Well formed by
construction. -/
structure Thresholds where
  error : Decimal
  warning : Decimal
  information : Decimal
  error_le_warning : error ≤ warning
  warningLeInformation : warning ≤ information

/-- The executed severity decision. -/
def classifyImpl (t : Thresholds) (support : Decimal) : Option ScreenSeverity :=
  if support < t.error then some .error
  else if support < t.warning then some .warning
  else if support < t.information then some .information
  else none

/-- Exact meaning of the severity decision: error below the error threshold, warning and
information in the bands above it, and no finding at or above the information threshold. -/
def ClassifyContract (classify : Thresholds → Decimal → Option ScreenSeverity) : Prop :=
  ∀ t s, (classify t s = some .error ↔ s < t.error) ∧
    (classify t s = some .warning ↔ t.error ≤ s ∧ s < t.warning) ∧
    (classify t s = some .information ↔ t.warning ≤ s ∧ s < t.information) ∧
    (classify t s = none ↔ t.information ≤ s)

theorem checked_classify : Regula.ExecutableContract classifyImpl ClassifyContract := by
  refine ⟨fun t s => ?_⟩
  unfold classifyImpl
  by_cases he : s < t.error
  · have hw : s < t.warning := Decimal.lt_of_lt_of_le he t.error_le_warning
    have hi : s < t.information := Decimal.lt_of_lt_of_le hw t.warningLeInformation
    simp [he, hw, hi, Decimal.lt_iff_not_le.mp he, Decimal.lt_iff_not_le.mp hw,
      Decimal.lt_iff_not_le.mp hi]
  · have hle : t.error ≤ s := Decidable.of_not_not he
    by_cases hw : s < t.warning
    · have hi : s < t.information := Decimal.lt_of_lt_of_le hw t.warningLeInformation
      simp [he, hw, hle, Decimal.lt_iff_not_le.mp hw, Decimal.lt_iff_not_le.mp hi]
    · have hwle : t.warning ≤ s := Decidable.of_not_not hw
      by_cases hi : s < t.information
      · simp [he, hw, hi, hwle, Decimal.lt_iff_not_le.mp hi]
      · simp [he, hw, hi, Decidable.of_not_not hi]

/-- The severity decision the screen runs. -/
def classify : Thresholds → Decimal → Option ScreenSeverity := checked_classify.run

/-- A lower support probability never yields a less severe finding. -/
theorem classify_antitone (t : Thresholds) {s s' : Decimal} (h : s ≤ s') :
    rank (classify t s') ≤ rank (classify t s) := by
  have c := checked_classify.evidence t s
  have c' := checked_classify.evidence t s'
  change rank (classifyImpl t s') ≤ rank (classifyImpl t s)
  cases hs' : classifyImpl t s' with
  | none => exact Nat.zero_le _
  | some sev' =>
    cases sev' with
    | error =>
      have : s < t.error := Decimal.lt_of_le_of_lt h (c'.1.mp hs')
      rw [c.1.mpr this]; exact Nat.le_refl _
    | warning =>
      have hw : s < t.warning := Decimal.lt_of_le_of_lt h (c'.2.1.mp hs').2
      have hi : s < t.information := Decimal.lt_of_lt_of_le hw t.warningLeInformation
      cases hs : classifyImpl t s with
      | none => exact absurd (c.2.2.2.mp hs) (Decimal.lt_iff_not_le.mp hi)
      | some sev =>
        cases sev with
        | information => exact absurd (c.2.2.1.mp hs).1 (Decimal.lt_iff_not_le.mp hw)
        | warning | error => decide
    | information =>
      have hi : s < t.information := Decimal.lt_of_le_of_lt h (c'.2.2.1.mp hs').2
      cases hs : classifyImpl t s with
      | none => exact absurd (c.2.2.2.mp hs) (Decimal.lt_iff_not_le.mp hi)
      | some sev => cases sev <;> decide

/-- What happens to one judged result after its severity is decided. -/
inductive Route where
  /-- No escalation: the result is recorded as screened, which is never checked or reviewed. -/
  | screened
  /-- Escalate to a reasoning model or human review. -/
  | escalate
  deriving Repr, DecidableEq

/-- The user's policy for one judgment: an optional severity mapping (without one, no finding
is raised and every result escalates) and an optional minimum distribution confidence,
applied only to answers that report one (Choice). -/
structure JudgmentPolicy where
  thresholds : Option Thresholds := none
  minConfidence : Option Decimal := none

/-- Whether a reported confidence meets the policy's minimum. -/
def confident (minimum confidence : Option Decimal) : Bool :=
  match minimum, confidence with
  | some m, some c => decide (m ≤ c)
  | _, _ => true

/-- The executed routing decision. -/
def routeImpl (p : JudgmentPolicy) (support : Decimal) (confidence : Option Decimal) : Route :=
  match p.thresholds with
  | none => .escalate
  | some t => if classify t support = none && confident p.minConfidence confidence
      then .screened else .escalate

/-- A result is left screened exactly when the user configured thresholds for its judgment,
it raises no finding, and any reported confidence meets the configured minimum. Every other
result escalates. -/
def RouteContract (route : JudgmentPolicy → Decimal → Option Decimal → Route) : Prop :=
  ∀ p s c, route p s c = .screened ↔ ∃ t, p.thresholds = some t ∧ t.information ≤ s ∧
    ∀ m k, p.minConfidence = some m → c = some k → m ≤ k

theorem checked_route : Regula.ExecutableContract routeImpl RouteContract := by
  refine ⟨fun p s c => ?_⟩
  unfold routeImpl confident
  cases ht : p.thresholds with
  | none => simp
  | some t =>
    have hc := (checked_classify.evidence t s).2.2.2
    simp only [classify, Regula.ExecutableContract.run] at *
    cases hm : p.minConfidence <;> cases c <;>
      simp [hc, reduceCtorEq]

/-- The routing decision the screen runs. -/
def route : JudgmentPolicy → Decimal → Option Decimal → Route := checked_route.run

/-! ## Pinned model identifiers -/

/-- A nonempty run of ASCII digits. -/
def isNumeral (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

/-- Split at every occurrence of `sep`. -/
def splitOn (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
    match splitOn sep rest with
    | [] => [[c]]
    | first :: others => if c == sep then [] :: first :: others else (c :: first) :: others

/-- A version is exactly three dot-separated numerals, such as `1.13.0`. -/
def isVersion (cs : List Char) : Bool :=
  match splitOn '.' cs with
  | [a, b, c] => isNumeral a && isNumeral b && isNumeral c
  | _ => false

/-- A pinned model identifier is `<name>-<major>.<minor>.<patch>` with a nonempty name:
an exact versioned model, never a moving alias such as `jev-latest` or `jev-preview`. -/
def isPinned (model : String) : Bool :=
  match (splitOn '-' model.toList).reverse with
  | version :: name :: rest => isVersion version && !(name :: rest).all List.isEmpty
  | _ => false

/-- A model identifier admitted for screening. -/
abbrev PinnedModel := { model : String // isPinned model = true }

theorem pinned_examples :
    isPinned "jev-1.13.0" = true ∧ isPinned "jev-latest" = false ∧
    isPinned "jev-preview" = false ∧ isPinned "jev-1.13" = false ∧
    isPinned "1.13.0" = false ∧ isPinned "-1.13.0" = false ∧ isPinned "jev-1.13.x" = false := by
  decide

/-! ## Intent clauses -/

/-- Lines of the section a level-`level` heading opens, up to the heading that ends it. -/
def sectionBody (level : Nat) : List (List Char) → List (List Char)
  | [] => []
  | line :: rest => if endsSection level line then [] else line :: sectionBody level rest

/-- The body of the first Intent section with content, the one RG5003's scanner finds first. -/
def intentBody? : List (List Char) → Option (List (List Char))
  | [] => none
  | line :: rest =>
    match headingLevel? line with
    | some level =>
      if isIntentHeading line && sectionHasContent level rest then some (sectionBody level rest)
      else intentBody? rest
    | none => intentBody? rest

/-- A body is found exactly for the docstrings RG5003 accepts. -/
theorem intentBody?_isSome_iff (lines : List (List Char)) :
    (intentBody? lines).isSome ↔ IntentSection lines := by
  rw [← hasIntentLines_iff]
  induction lines with
  | nil => simp [intentBody?, hasIntentLines]
  | cons line rest ih =>
    simp only [intentBody?, hasIntentLines]
    cases hl : headingLevel? line with
    | none => simp [ih]
    | some level =>
      simp only [Option.any_some]
      by_cases h : (isIntentHeading line && sectionHasContent level rest) = true
      · simp [h]
      · simp only [Bool.not_eq_true] at h
        simp [h, ih]

/-- A bullet-list marker (`-`, `*` or `+`) then a space or tab; returns the item text. -/
def bulletText? : List Char → Option (List Char)
  | m :: s :: text =>
    if (m == '-' || m == '*' || m == '+') && (s == ' ' || s == '\t') then some text else none
  | _ => none

/-- An ordered-list marker (a numeral, then `.` or `)`) then a space or tab. -/
def orderedText? (body : List Char) : Option (List Char) :=
  let digits := body.takeWhile Char.isDigit
  match body.drop digits.length with
  | d :: s :: text =>
    if !digits.isEmpty && (d == '.' || d == ')') && (s == ' ' || s == '\t') then some text
    else none
  | _ => none

/-- A list-item line, after at most three spaces of indentation; returns the item text. -/
def itemText? (line : List Char) : Option (List Char) :=
  let body := dropIndent 3 line
  (bulletText? body).orElse fun _ => orderedText? body

/-- Group section lines into clauses. A list item starts a clause; any other text line
continues the current clause or starts one after a blank line or subsection heading; blank
and heading lines end the current clause. `current` holds the open clause's lines. -/
def clauseLines (current : List (List Char)) : List (List Char) → List (List (List Char))
  | [] => [current]
  | line :: rest =>
    if isHeading line || !isContent line then current :: clauseLines [] rest
    else match itemText? line with
      | some text => current :: clauseLines [text] rest
      | none => clauseLines (current ++ [line]) rest

/-- One clause's text: its lines trimmed and joined with single spaces. -/
def joinClause (lines : List (List Char)) : List Char :=
  [' '].intercalate ((lines.map trim).filter (!·.isEmpty))

/-- The executed clause split of a docstring's first nonempty Intent section: every
nonblank clause text, in order. -/
def intentClausesImpl (doc : String) : List String :=
  match intentBody? (docLines doc) with
  | none => []
  | some body => ((clauseLines [] body).map joinClause).filter (!·.isEmpty) |>.map String.ofList

/-- The split finds no clause outside RG5003's accepted docstrings, and never returns a
blank clause. -/
def ClausesContract (split : String → List String) : Prop :=
  ∀ doc, (split doc ≠ [] → IntentSection (docLines doc)) ∧ ∀ c ∈ split doc, c ≠ ""

theorem checked_clauses : Regula.ExecutableContract intentClausesImpl ClausesContract := by
  refine ⟨fun doc => ⟨fun h => ?_, fun c hc => ?_⟩⟩
  · apply (intentBody?_isSome_iff _).mp
    unfold intentClausesImpl at h
    cases hb : intentBody? (docLines doc) with
    | none => simp [hb] at h
    | some _ => rfl
  · unfold intentClausesImpl at hc
    cases hb : intentBody? (docLines doc) with
    | none => simp [hb] at hc
    | some body =>
      simp only [hb, List.mem_map, List.mem_filter] at hc
      obtain ⟨cs, ⟨_, hne⟩, rfl⟩ := hc
      intro h
      have := congrArg String.toList h
      simp only [String.toList_ofList] at this
      simp [this] at hne

/-- The clause split the screen runs. -/
def intentClauses : String → List String := checked_clauses.run

theorem clauses_examples :
    intentClauses "Claim.\n\n# Intent\n- Sorted output.\n- Same elements,\n  with multiplicity.\n\n# Notes\nx" =
      ["Sorted output.", "Same elements, with multiplicity."] ∧
    intentClauses "Claim.\n\n# Intent\nOne requirement\nover two lines." =
      ["One requirement over two lines."] ∧
    intentClauses "Claim.\n\n# Intent\n1. First.\n2) Second.\n\nA closing paragraph." =
      ["First.", "Second.", "A closing paragraph."] ∧
    intentClauses "Claim without intent." = [] := by
  decide

/-- Docstring lines before the Intent section that `intentBody?` selects: the §5.2
explanation of the formal statement. Text after that section is not included. -/
def explanationLines : List (List Char) → List (List Char)
  | [] => []
  | line :: rest =>
    match headingLevel? line with
    | some level =>
      if isIntentHeading line && sectionHasContent level rest then [] else line :: explanationLines rest
    | none => line :: explanationLines rest

/-- The explanation text of a docstring, trimmed. -/
def explanation (doc : String) : String :=
  String.ofList (trim (['\n'].intercalate (explanationLines (docLines doc))))

theorem explanation_example :
    explanation "For every list, the result is sorted.\n\n# Intent\n- Sorted.\n" =
      "For every list, the result is sorted." := by
  decide

/-! ## Formal discharge references -/

/-- The text that opens every discharge marker, well formed or not. -/
def dischargeOpening : List Char := "(discharged by".toList

/-- The marker that ends a formally discharged clause: ``(discharged by `Name`)``. -/
def dischargeMarker : List Char := dischargeOpening ++ " `".toList

/-- Split a clause at the first occurrence of `marker`. -/
def splitMarker (marker : List Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if marker.isPrefixOf (c :: rest) then some ([], (c :: rest).drop marker.length)
    else (splitMarker marker rest).map fun (before, after) => (c :: before, after)

/-- A text containing a marker contains every prefix of that marker. -/
theorem splitMarker_isSome_of_append {m t : List Char} :
    ∀ {s}, (splitMarker (m ++ t) s).isSome → (splitMarker m s).isSome
  | [], h => by simp [splitMarker] at h
  | c :: rest, h => by
    unfold splitMarker at h ⊢
    by_cases hm : m.isPrefixOf (c :: rest) = true
    · simp [hm]
    · have hmt : ¬ (m ++ t).isPrefixOf (c :: rest) = true := fun hmt =>
        hm (List.isPrefixOf_iff_prefix.mpr
          ((List.prefix_append m t).trans (List.isPrefixOf_iff_prefix.mp hmt)))
      simp only [hm, hmt, Bool.false_eq_true, ↓reduceIte, Option.isSome_map] at h ⊢
      exact splitMarker_isSome_of_append h

/-- A clause that ends with ``(discharged by `Name`)`` names the theorem that proves the claim
implies the clause's formal statement. Returns the English text before the marker and the
name; the name is nonempty and contains no whitespace or backtick. -/
def discharge? (clause : String) : Option (String × String) := do
  let (english, after) ← splitMarker dischargeMarker (trim clause.toList)
  let name := after.takeWhile (· != '`')
  if !name.isEmpty && name.all (fun c => !c.isWhitespace) && after.drop name.length == ['`', ')']
  then some (String.ofList (trim english), String.ofList name)
  else none

theorem discharge_examples :
    discharge? "Same elements. (discharged by `Demo.sort_perm`)" = some ("Same elements.", "Demo.sort_perm") ∧
    discharge? "Same elements." = none ∧
    discharge? "Same elements. (discharged by `a b`)" = none ∧
    discharge? "(discharged by `x`) trailing" = none := by
  decide

/-- A clause that contains the text `(discharged by`, well formed or not: the English text
before its first occurrence and the trimmed reference text after it. A marked clause that
`discharge?` does not read is a malformed reference, never an unmarked clause. -/
def dischargeMarked? (clause : String) : Option (String × String) :=
  (splitMarker dischargeOpening (trim clause.toList)).map fun (english, after) =>
    (String.ofList (trim english), String.ofList (trim after))

/-- Every clause `discharge?` reads is marked. -/
theorem dischargeMarked?_of_discharge? {clause : String} {p : String × String}
    (h : discharge? clause = some p) : (dischargeMarked? clause).isSome := by
  unfold discharge? at h
  unfold dischargeMarked?
  rw [Option.isSome_map]
  apply splitMarker_isSome_of_append (t := " `".toList)
  change (splitMarker dischargeMarker (trim clause.toList)).isSome
  cases hs : splitMarker dischargeMarker (trim clause.toList) with
  | none => simp [hs] at h
  | some _ => rfl

theorem dischargeMarked_examples :
    dischargeMarked? "Same elements. (discharged by `Demo.sort_perm`)." =
      some ("Same elements.", "`Demo.sort_perm`).") ∧
    dischargeMarked? "Same elements. (discharged by `a b`)" = some ("Same elements.", "`a b`)") ∧
    dischargeMarked? "Same elements. (discharged by Demo.sort_perm)" =
      some ("Same elements.", "Demo.sort_perm)") ∧
    discharge? "Same elements. (discharged by Demo.sort_perm)" = none ∧
    dischargeMarked? "Same elements." = none := by
  decide

/-! ## Judgments -/

/-- The judgments a screen asks. `correspondence` asks whether the formal statement of a
discharged clause states its English text. -/
inductive Judgment where
  | coverage | correspondence | strength | quantifierOrder | totalization | exclusions
  deriving Repr, DecidableEq

def Judgment.all : List Judgment :=
  [.coverage, .correspondence, .strength, .quantifierOrder, .totalization, .exclusions]

theorem Judgment.mem_all (j : Judgment) : j ∈ all := by cases j <;> decide

def Judgment.spelling : Judgment → String
  | .coverage => "coverage" | .correspondence => "correspondence" | .strength => "strength"
  | .quantifierOrder => "quantifier-order" | .totalization => "totalization"
  | .exclusions => "exclusions"

theorem Judgment.spelling_injective : Function.Injective Judgment.spelling := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Whether a judgment's answer reports a distribution confidence: only the strength Choice
does; every other judgment is a Noul. -/
def Judgment.reportsConfidence : Judgment → Bool
  | .strength => true
  | _ => false

/-- Strength of the formal claim relative to the intent (the options of the strength Choice). -/
inductive Strength where
  | equivalent | stronger | weaker | incomparable
  deriving Repr, DecidableEq

/-- Support for the intent from a strength distribution: the probability that the claim
guarantees the whole intent (equivalent or stronger). -/
def strengthSupport (equivalent stronger : Decimal) : Decimal := equivalent.add stronger

end RegulaPolicy.Screening
