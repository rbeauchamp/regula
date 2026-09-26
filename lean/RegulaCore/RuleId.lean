module


@[expose] public section
/-!
Closed public rule identity. Canonical construction is inspired by con-leche's
`PropWhen.lean` and `Cached/Installed.lean`, revision
c431b1ca1b7a93486dd3e0440d3ee82abe90ccd0 (Lean FRO, Joachim Breitner and contributors).
No upstream code or proof is copied. Normative predicates remain in the standard (`website/RegulaStandard`).
-/
namespace Regula

/-- Reserved initial vocabulary; identity is independent of policy categories. -/
inductive RuleId where
  | projectAxiom
  | proofHole
  | unknownAxiom
  | compilerTrusting
  | profileExceeded
  | escapeHatch
  | executableContract
  | environment
  | configuration
  | sourceBuild
  | coverage
  | admission
  | executionUnresolved
  | executionBoundary
  | fenceStructure
  | positiveExample
  | negativeExample
  | trustedExample
  | moduleDocumentation
  | materialDocumentation
  | materialIntent
  deriving Repr, BEq, DecidableEq, Inhabited

namespace RuleId

def spelling : RuleId → String
  | .projectAxiom => "RG1001"
  | .proofHole => "RG1002"
  | .unknownAxiom => "RG1003"
  | .compilerTrusting => "RG1004"
  | .profileExceeded => "RG1005"
  | .escapeHatch => "RG1006"
  | .executableContract => "RG1007"
  | .environment => "RG2001"
  | .configuration => "RG2002"
  | .sourceBuild => "RG2003"
  | .coverage => "RG2004"
  | .admission => "RG2005"
  | .executionUnresolved => "RG3001"
  | .executionBoundary => "RG3002"
  | .fenceStructure => "RG4001"
  | .positiveExample => "RG4002"
  | .negativeExample => "RG4003"
  | .trustedExample => "RG4004"
  | .moduleDocumentation => "RG5001"
  | .materialDocumentation => "RG5002"
  | .materialIntent => "RG5003"

def parse? : String → Option RuleId
  | "RG1001" => some .projectAxiom
  | "RG1002" => some .proofHole
  | "RG1003" => some .unknownAxiom
  | "RG1004" => some .compilerTrusting
  | "RG1005" => some .profileExceeded
  | "RG1006" => some .escapeHatch
  | "RG1007" => some .executableContract
  | "RG2001" => some .environment
  | "RG2002" => some .configuration
  | "RG2003" => some .sourceBuild
  | "RG2004" => some .coverage
  | "RG2005" => some .admission
  | "RG3001" => some .executionUnresolved
  | "RG3002" => some .executionBoundary
  | "RG4001" => some .fenceStructure
  | "RG4002" => some .positiveExample
  | "RG4003" => some .negativeExample
  | "RG4004" => some .trustedExample
  | "RG5001" => some .moduleDocumentation
  | "RG5002" => some .materialDocumentation
  | "RG5003" => some .materialIntent
  | _ => none

def all : List RuleId := [.projectAxiom, .proofHole, .unknownAxiom, .compilerTrusting, .profileExceeded, .escapeHatch, .executableContract, .environment, .configuration, .sourceBuild, .coverage, .admission, .executionUnresolved, .executionBoundary, .fenceStructure, .positiveExample, .negativeExample, .trustedExample, .moduleDocumentation, .materialDocumentation, .materialIntent]

theorem parse_spelling (id : RuleId) : parse? id.spelling = some id := by
  cases id <;> rfl

/-- Parsing succeeds only on a rule's exact spelling. -/
theorem spelling_of_parse {s : String} {id : RuleId} (h : parse? s = some id) : id.spelling = s := by
  unfold parse? at h
  split at h <;> first | cases h; rfl | cases h

theorem spelling_injective {a b : RuleId} (h : a.spelling = b.spelling) : a = b := by
  have e := congrArg parse? h
  simpa only [parse_spelling, Option.some.injEq] using e

theorem mem_all (id : RuleId) : id ∈ all := by
  cases id <;> simp [all]

theorem all_nodup : all.Nodup := by decide

/-- The derived `==` is equality, so list lemmas stated for lawful `BEq` apply to rule IDs. -/
instance : LawfulBEq RuleId where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | cases h
  rfl {a} := by cases a <;> rfl

/-- Routes derive solely from the stable ID, with no independently writable slug. -/
def route (id : RuleId) : String := "rules/" ++ id.spelling ++ "/"

theorem route_injective {a b : RuleId} (h : a.route = b.route) : a = b := by
  apply spelling_injective
  exact (String.append_right_inj "rules/").mp ((String.append_left_inj "/").mp h)

instance : ToString RuleId := ⟨spelling⟩
end RuleId
end Regula
