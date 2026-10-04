import RegulaQualification.Checks
import Regula.Decision

/-! # Native diagnostic observation contract

Pure native-diagnostic observation contract. The driver decodes actual JSON messages
into these records. Validation preserves multiplicity and compiler-message order; it
checks diagnostic identity, severity, source attribution, and help-link ownership.
It proves properties of supplied records, not collector scheduling or IO authenticity. -/

namespace RegulaQualification.Native

/-- Fields consumed from a native compiler diagnostic. Additional JSON fields are not
used by this general oracle; case-specific range checks inspect the original JSON. -/
structure Message where
  /-- The message kind Lean serializes, its top-level tag: for example
  `Regula.<id>._namedError` for a native diagnostic and `[anonymous]` for an untagged message. -/
  kind : String
  /-- The message's severity, such as `warning` or `error`. -/
  severity : String
  /-- The message text. -/
  data : String
  /-- The file the message is attributed to. -/
  fileName : String
  deriving Repr

/-- Expected compiler messages are ordered and matched by severity and text fragment. -/
structure CompilerMessage where
  /-- The severity the compiler message must have. -/
  severity : String
  /-- A fragment the compiler message's text must contain. -/
  text : String

/-- Exact observation requirements selected before running a source control. -/
structure Expected where
  /-- The kinds of the expected Regula messages, as a multiset. -/
  kinds : List String
  /-- The file every Regula message must be attributed to. -/
  fileName : String
  /-- The rule-reference prefix every Regula message's help link must contain: the rules route of
  the installed build's edition (`dev/rules/` unreleased, `v/<version>/rules/` for a release). -/
  helpPrefix : String
  /-- Whether the compiler must exit with a nonzero code. -/
  errors : Bool := false
  /-- The severity every Regula message must have. -/
  severity : String := "warning"
  /-- The expected non-Regula compiler messages, in order. -/
  compiler : List CompilerMessage := []
  /-- When set, text some Regula message must contain. -/
  detail : Option String := none

/-- Regula owns precisely the native named-error prefix used by the old harness. -/
def isNative (message : Message) : Bool := message.kind.startsWith "Regula.RG"

/-- Successful native-message shape, separate from kind multiplicity. -/
def nativeMatches (expected : Expected) (message : Message) : Bool :=
  message.fileName == expected.fileName &&
  !(message.data.contains "lean-lang.org/doc/reference") &&
  message.data.contains expected.helpPrefix &&
  message.severity == expected.severity

/-- Independent relational meaning of the native message fields. -/
def NativeMatches (expected : Expected) (message : Message) : Prop :=
  message.fileName = expected.fileName ∧
  message.data.contains "lean-lang.org/doc/reference" = false ∧
  message.data.contains expected.helpPrefix = true ∧
  message.severity = expected.severity

/-- Every message is admitted exactly under the specified file, severity, and link checks. -/
theorem nativeMatches_exact (expected : Expected) (message : Message) :
    nativeMatches expected message = true ↔ NativeMatches expected message := by
  simp [nativeMatches, NativeMatches, and_assoc]

/-- Ordered, length-exact matching; zipping alone would silently truncate omissions. -/
def compilerMatches : List Message → List CompilerMessage → Bool
  | [], [] => true
  | message :: messages, expected :: expectations =>
    message.severity == expected.severity && message.data.contains expected.text &&
      compilerMatches messages expectations
  | _, _ => false

/-- Compiler expectation relation retains order, multiplicity, and exact list length. -/
def CompilerMatches : List Message → List CompilerMessage → Prop
  | [], [] => True
  | message :: messages, expected :: expectations =>
    message.severity = expected.severity ∧ message.data.contains expected.text = true ∧
      CompilerMatches messages expectations
  | _, _ => False

/-- The executable recursion admits exactly the ordered compiler-message relation. -/
theorem compilerMatches_exact (messages : List Message) (expectations : List CompilerMessage) :
    compilerMatches messages expectations = true ↔ CompilerMatches messages expectations := by
  induction messages generalizing expectations with
  | nil => cases expectations <;> simp [compilerMatches, CompilerMatches]
  | cons message messages ih =>
    cases expectations <;> simp [compilerMatches, CompilerMatches, ih, and_assoc]

/-- All required checks on one process observation. Sorting compares multisets, not
sets: repeated diagnostic IDs must appear the expected number of times. -/
def checks (expected : Expected) (exitCode : Nat) (stderr : String)
    (messages : List Message) : List Check :=
  let native := messages.filter isNative
  let compiler := messages.filter (fun message => !isNative message)
  [⟨"unexpected compiler diagnostics", compilerMatches compiler expected.compiler⟩,
   ⟨"native diagnostic multiplicity/identity mismatch",
      (native.map (·.kind)).mergeSort (· ≤ ·) == expected.kinds.mergeSort (· ≤ ·)⟩,
   ⟨"exit outcome mismatch", (exitCode != 0) == expected.errors⟩,
   ⟨"unexpected standard error", stderr == ""⟩,
   ⟨"native attribution/severity/help mismatch", native.all (nativeMatches expected)⟩,
   ⟨"missing required diagnostic detail",
      expected.detail.all (fun detail => native.any (fun message => message.data.contains detail))⟩]

/-- Full relation on supplied diagnostics. String containment and sorting refer to
the pinned Lean definitions; no alternate text normalization is promised. -/
def Matches (expected : Expected) (exitCode : Nat) (stderr : String)
    (messages : List Message) : Prop :=
  let native := messages.filter isNative
  CompilerMatches (messages.filter (fun message => !isNative message)) expected.compiler ∧
  (native.map (·.kind)).mergeSort (· ≤ ·) = expected.kinds.mergeSort (· ≤ ·) ∧
  (exitCode != 0) = expected.errors ∧ stderr = "" ∧
  (∀ message ∈ native, NativeMatches expected message) ∧
  expected.detail.all
      (fun detail => native.any (fun message => message.data.contains detail)) = true

/-- The actual adapter oracle uses the registered proof-backed evaluator. -/
@[regula_decision]
def validate (expected : Expected) (exitCode : Nat) (stderr : String)
    (messages : List Message) : Except String Unit :=
  checked_evaluation.run (checks expected exitCode stderr messages)

/-- Soundness and completeness of the whole supplied-observation contract. -/
theorem validate_exact (expected : Expected) (exitCode : Nat) (stderr : String)
    (messages : List Message) :
    validate expected exitCode stderr messages = .ok () ↔
        Matches expected exitCode stderr messages := by
  simp only [validate, Regula.ExecutableContract.run, checks, List.all_filter, List.any_filter,
    evaluate_success, Satisfied, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    compilerMatches_exact, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, nativeMatches_exact, forall_eq, Matches, List.mem_filter, and_imp,
    and_congr_right_iff, and_congr_left_iff]
  intro _ _ _ _ _
  constructor
  · intro h message hm hn
    exact (h message hm).resolve_left (by simp [hn])
  · intro h message hm
    cases hn : isNative message with
    | false => exact Or.inl rfl
    | true => exact Or.inr (h message hm hn)

/-- An empty successful observation with no requested diagnostics is admissible. -/
theorem positive_control :
    validate { kinds := [], fileName := "Control.lean", helpPrefix := "" } 0 "" [] = .ok () := by
  rw [validate_exact]
  simp [Matches, CompilerMatches]

/-- Proof requirement consumed by the native driver, as a two-way decision (`validate_exact`):
it accepts the empty successful observation of `positive_control`, and refuses the same
observation with a nonzero exit. -/
theorem checked_validation : Regula.ExecutableContract validate (fun run =>
    Regula.Decides (· = .ok ())
      (fun input : ((Expected × Nat) × String) × List Message =>
        Matches input.1.1.1 input.1.1.2 input.1.2 input.2)
      (Function.uncurry (Function.uncurry (Function.uncurry run)))) :=
  ⟨.of_iff (fun input => validate_exact input.1.1.1 input.1.1.2 input.1.2 input.2)
    ⟨((({ kinds := [], fileName := "Control.lean", helpPrefix := "" }, 0), ""), []),
      positive_control⟩
    ⟨((({ kinds := [], fileName := "Control.lean", helpPrefix := "" }, 1), ""), []),
      fun accepted => absurd (congrArg Except.isOk accepted) (by decide +kernel)⟩⟩

end RegulaQualification.Native
