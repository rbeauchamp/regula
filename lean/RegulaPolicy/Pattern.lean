import RegulaPolicy.Collections
import Regula.Contract
import Regula.Decision

/-! # Diagnostic pattern language

The existing documentation diagnostic language, now structurally terminating and
linked to explicit grammar and ordered-split relations. A match concerns one effective
error message; message severity and producer completion are operational observations. -/
namespace RegulaPolicy

/-- The pattern without its optional leading `(?s)` marker. -/
def patternBody (pattern : String) : String :=
  if pattern.startsWith "(?s)" then pattern.drop 4 |>.toString else pattern

/-- The pattern body split at `|` into alternatives, each split at `.*` into the literals that
must occur in order. -/
def patternAlternatives (pattern : String) : List (List String) :=
  (patternBody pattern).splitOn "|" |>.map (·.splitOn ".*")

/-- A text starts with `marker` exactly when it is `marker` and then a rest. -/
private theorem startsWith_iff_append (text marker : String) :
    text.startsWith marker = true ↔ ∃ rest, text = marker ++ rest := by
  rw [String.startsWith_string_iff]
  constructor
  · rintro ⟨rest, split⟩
    exact ⟨String.ofList rest, by rw [← String.toList_inj]; simp [← split]⟩
  · rintro ⟨rest, rfl⟩
    exact ⟨rest.toList, by simp⟩

/-- `body` is `pattern` without its optional leading `(?s)` marker, as equations over the two
texts: `pattern` is the marker and then `body`, or `pattern` does not start with the marker and
`body` is `pattern`. The statement has no test and no operation of `patternBody`, which computes
the body (`patternBody_iff`). -/
def PatternBody (pattern body : String) : Prop :=
  pattern = "(?s)" ++ body ∨ ((∀ rest, pattern ≠ "(?s)" ++ rest) ∧ body = pattern)

/-- The body of a pattern is one text only: the computed one. -/
theorem patternBody_iff (pattern body : String) :
    PatternBody pattern body ↔ body = patternBody pattern := by
  unfold PatternBody patternBody
  by_cases marked : pattern.startsWith "(?s)" = true
  · obtain ⟨rest, rfl⟩ := (startsWith_iff_append pattern "(?s)").mp marked
    have dropped : (("(?s)" ++ rest).drop 4).toString = rest := by
      rw [← String.toList_inj, String.Slice.toString_eq, String.toList_copy_drop]
      simp
    simp only [marked, ↓reduceIte, dropped]
    constructor
    · rintro (same | ⟨unmarked, -⟩)
      · rw [← String.toList_inj] at same ⊢
        simpa using same.symm
      · exact absurd rfl (unmarked rest)
    · rintro rfl
      exact Or.inl rfl
  · simp only [marked]
    have unmarked : ∀ rest, pattern ≠ "(?s)" ++ rest := fun rest same =>
      marked ((startsWith_iff_append pattern "(?s)").mpr ⟨rest, same⟩)
    constructor
    · rintro (same | ⟨-, same⟩)
      · exact absurd same (unmarked body)
      · exact same
    · rintro rfl
      exact Or.inr ⟨unmarked, rfl⟩

/-- A pattern body in the supported language: alternation and ordered literals. The remaining
regex metacharacters, a stray star, and empty literals are refused. -/
def BodyValid (body : String) : Prop :=
  body ≠ "" ∧
  ∀ alternative ∈ body.splitOn "|", alternative ≠ "" ∧
    ∀ literal ∈ alternative.splitOn ".*", literal ≠ "" ∧
      ∀ ch ∈ literal.toList, ch ∉ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\', '*']
instance (body : String) : Decidable (BodyValid body) := by unfold BodyValid; infer_instance

/-- Only alternation, ordered literals and the optional leading (?s) marker are supported: the
body of the pattern (`PatternBody`) is valid (`BodyValid`). -/
def PatternValid (pattern : String) : Prop :=
  ∃ body, PatternBody pattern body ∧ BodyValid body

/-- A pattern is valid exactly when its computed body is. -/
theorem patternValid_iff (pattern : String) :
    PatternValid pattern ↔ BodyValid (patternBody pattern) := by
  simp [PatternValid, patternBody_iff]

instance (p : String) : Decidable (PatternValid p) :=
  decidable_of_iff _ (patternValid_iff p).symm

/-- Exact successful decomposition at successive leftmost literal occurrences. String's
split operation supplies the prefix and remaining suffix; no cross-message concatenation
occurs. Consuming the leftmost occurrence leaves every later possible occurrence available. -/
def OrderedLiteralMatch : List String → String → Prop
  | [], _ => True
  | literal :: rest, text =>
    match text.splitOn literal with
    | _ :: suffix :: suffixes => OrderedLiteralMatch rest (literal.intercalate (suffix :: suffixes))
    | _ => False

/-- The supported expected-error relation is one alternative's ordered literal sequence: the
body of the pattern is valid, and `text` matches the literals of one alternative of the body,
which are the body split at `|` and then at `.*`. -/
def PatternMatch (pattern text : String) : Prop :=
  ∃ body, PatternBody pattern body ∧ BodyValid body ∧
    ∃ alternative ∈ body.splitOn "|", OrderedLiteralMatch (alternative.splitOn ".*") text

/-- Same greedy literal consumer as the existing checker, with structural recursion on
fragments instead of the unnecessary partial declaration previously used by the adapter. -/
def orderedLiterals : List String → String → Bool
  | [], _ => true
  | literal :: rest, text =>
    match text.splitOn literal with
    | _ :: suffix :: suffixes => orderedLiterals rest (literal.intercalate (suffix :: suffixes))
    | _ => false

/-- Universal implementation linkage for the literal consumer. -/
theorem orderedLiterals_iff (literals : List String) (text : String) :
    orderedLiterals literals text = true ↔ OrderedLiteralMatch literals text := by
  induction literals generalizing text with
  | nil => simp [orderedLiterals, OrderedLiteralMatch]
  | cons literal rest ih =>
    simp only [orderedLiterals, OrderedLiteralMatch]
    split <;> simp_all

/-- Invalid patterns are refused even when a direct caller omits scanner validation. -/
@[regula_decision]
def matchesPattern (pattern text : String) : Bool :=
  decide (PatternValid pattern) && (patternAlternatives pattern).any
      (fun ls => orderedLiterals ls text)

/-- All and only the declared valid ordered-split relations are recognized. -/
theorem matchesPattern_iff (pattern text : String) :
    matchesPattern pattern text = true ↔ PatternMatch pattern text := by
  simp [matchesPattern, PatternMatch, orderedLiterals_iff, patternBody_iff, patternValid_iff,
    patternAlternatives]
end RegulaPolicy

namespace RegulaPolicy
instance (pattern text : String) : Decidable (PatternMatch pattern text) :=
  decidable_of_iff (matchesPattern pattern text = true) (matchesPattern_iff pattern text)
end RegulaPolicy

namespace RegulaPolicy

/-- `matchesPattern` is a complete decision of `PatternMatch` on a pattern and a text: it
accepts every pair the relation holds of, and it refuses the empty pattern on the empty text.
Soundness also holds (`matchesPattern_iff`), but the kind is one-way because a sound kind
requires a pair the function accepts, and accepting evaluates `String.splitOn`, which the kernel
does not reduce; accepted patterns are observed by the documentation fence corpus. -/
theorem checked_matchesPattern : Regula.ExecutableContract matchesPattern (fun run =>
    Regula.DecidesCompletely (· = true)
      (fun input : String × String => PatternMatch input.1 input.2) (Function.uncurry run)) :=
  ⟨{ complete := fun input holds => (matchesPattern_iff input.1 input.2).mpr holds
     refused := ⟨("", ""), (by decide : ¬ matchesPattern "" "" = true)⟩ }⟩

end RegulaPolicy
