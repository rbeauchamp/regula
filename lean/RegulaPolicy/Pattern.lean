import RegulaPolicy.Collections

/-! # Diagnostic pattern language

The existing documentation diagnostic language, now structurally terminating and
linked to explicit grammar and ordered-split relations. A match concerns one effective
error message; message severity and producer completion are operational observations. -/
namespace RegulaPolicy

def patternBody (pattern : String) : String :=
  if pattern.startsWith "(?s)" then pattern.drop 4 |>.toString else pattern

def patternAlternatives (pattern : String) : List (List String) :=
  (patternBody pattern).splitOn "|" |>.map (·.splitOn ".*")

/-- Only alternation, ordered literals and the optional leading (?s) marker are supported.
The remaining regex metacharacters, a stray star, and empty literals are refused. -/
def PatternValid (pattern : String) : Prop :=
  patternBody pattern ≠ "" ∧
  ∀ alternative ∈ (patternBody pattern).splitOn "|", alternative ≠ "" ∧
    ∀ literal ∈ alternative.splitOn ".*", literal ≠ "" ∧
      ∀ ch ∈ literal.toList, ch ∉ ['[', ']', '(', ')', '{', '}', '?', '+', '^', '$', '\\', '*']
instance (p : String) : Decidable (PatternValid p) := by unfold PatternValid; infer_instance

/-- Exact successful decomposition at successive leftmost literal occurrences. String's
split operation supplies the prefix and remaining suffix; no cross-message concatenation
occurs. Consuming the leftmost occurrence leaves every later possible occurrence available. -/
def OrderedLiteralMatch : List String → String → Prop
  | [], _ => True
  | literal :: rest, text =>
    match text.splitOn literal with
    | _ :: suffix :: suffixes => OrderedLiteralMatch rest (literal.intercalate (suffix :: suffixes))
    | _ => False

/-- The supported expected-error relation is one alternative's ordered literal sequence. -/
def PatternMatch (pattern text : String) : Prop :=
  PatternValid pattern ∧ ∃ literals ∈ patternAlternatives pattern, OrderedLiteralMatch literals text

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
def matchesPattern (pattern text : String) : Bool :=
  decide (PatternValid pattern) && (patternAlternatives pattern).any (fun ls => orderedLiterals ls text)

/-- All and only the declared valid ordered-split relations are recognized. -/
theorem matchesPattern_iff (pattern text : String) :
    matchesPattern pattern text = true ↔ PatternMatch pattern text := by
  simp [matchesPattern, PatternMatch, orderedLiterals_iff]
end RegulaPolicy

namespace RegulaPolicy
instance (pattern text : String) : Decidable (PatternMatch pattern text) :=
  decidable_of_iff (matchesPattern pattern text = true) (matchesPattern_iff pattern text)
end RegulaPolicy
