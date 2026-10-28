import RegulaCore.RuleId

/-!
# The fate of each rule of Regula's registry

`fate` matches Regula's own closed rule identity (`Regula.RuleId`) exhaustively, so Lean checks
that each rule the registry defines has exactly one fate, and a rule the registry gains fails this
build until the table gives it one. The new rules are not in the registry yet; `NewRule` lists
them with the identifiers the specification proposes.
-/

namespace RegulaSpecification

/-- The Lean tool that takes over a rule handed to Lean. -/
inductive LeanTool where
  /-- `lake build --wfail`: a warning or an error that Lake logs fails the build. -/
  | wfail
  /-- `lake check` of Lean `v4.35.0`: Lean's kernel replays an export of the default targets, and
  each axiom outside `propext`, `Classical.choice` and `Quot.sound` that it mentions is refused. -/
  | lakeCheck
  deriving DecidableEq, Repr

/-- What happens to a rule. -/
inductive Fate where
  /-- Kept, as a pure function over the closed input with the intent record the specification
  gives. -/
  | kept
  /-- Handed to a Lean tool, which decides it from then on. -/
  | handedToLean (tool : LeanTool)
  /-- Retired to written guidance, with no check. -/
  | retired
  deriving DecidableEq, Repr

open Regula in
/-- The fate of each rule of the registry. -/
def fate : RuleId → Fate
  | .projectAxiom | .proofHole | .unknownAxiom | .compilerTrusting | .profileExceeded => .kept
  | .escapeHatch | .executableContract | .decisionContract | .sharedTest => .kept
  | .environment | .configuration | .coverage | .communityConfiguration => .kept
  | .sourceBuild => .handedToLean .wfail
  | .admission => .handedToLean .lakeCheck
  | .executionUnresolved | .executionBoundary => .kept
  | .fenceStructure | .positiveExample | .negativeExample | .trustedExample => .retired
  | .moduleDocumentation | .materialDocumentation | .materialIntent => .retired

/-- The rules the specification adds. -/
inductive NewRule where
  /-- `RG2007`: claimed modules have no entries of an extension outside the closed allowlist. -/
  | closedSubset
  /-- `RG6001`: each declared deliverable meets its lean-intent obligations. -/
  | intentObligations
  deriving DecidableEq, Repr

/-- The identifier the specification proposes for each new rule. -/
def NewRule.spelling : NewRule → String
  | .closedSubset => "RG2007"
  | .intentObligations => "RG6001"

/-- No proposed identifier is already a registered rule. -/
theorem new_not_registered (n : NewRule) : Regula.RuleId.parse? n.spelling = none := by
  cases n <;> rfl

/-- The counts the specification states: 15 kept, 2 handed to Lean, 7 retired. -/
theorem fate_counts :
    (Regula.RuleId.all.filter (fate · == .kept)).length = 15 ∧
      (Regula.RuleId.all.filter (fun r => match fate r with
        | .handedToLean _ => true | _ => false)).length = 2 ∧
      (Regula.RuleId.all.filter (fate · == .retired)).length = 7 := by
  decide

end RegulaSpecification
