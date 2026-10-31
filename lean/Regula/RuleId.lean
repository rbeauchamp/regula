/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

/-!
# The rules

The closed identity of Regula's checks. `RuleId.all` lists each once, and
`Regula.Closed.Tables.check` matches this type exhaustively, so a rule added here stops the build
until it has a function.
-/

public section

namespace Regula

/-- The checks of Regula. -/
inductive RuleId where
  /-- RG1001: a claimed module declares an `axiom`. -/
  | projectAxiom
  /-- RG1002: a constant of a claimed module depends on `sorryAx`. -/
  | proofHole
  /-- RG1003: a constant of a claimed module depends on an axiom that is not one of Lean's three
  logical axioms, and that RG1002 and RG1004 do not name. -/
  | unknownAxiom
  /-- RG1004: a constant of a claimed module depends on an axiom with the name form that
  `native_decide` gives. -/
  | nativeProof
  /-- RG1005: a constant of a claimed module depends on an axiom that the project's profile does not
  admit. -/
  | profileExceeded
  /-- RG1006: a claimed module holds a constant that is `unsafe`, `partial` or named as a recursion
  helper, without the form of Lean's recursion helper, or a constant whose value mentions a loop
  construct of Lean. -/
  | escapeHatch
  /-- RG1010, a name that no released version used: a Lean file or the Lake configuration of the project holds something outside the closed
  set that the language check admits (`Regula.Language`). -/
  | language
  /-- RG2001: the build cannot be loaded, or the input does not have the closed form. -/
  | environment
  deriving Repr, DecidableEq

namespace RuleId

/-- The stable name of a rule, which a finding prints. -/
def spelling : RuleId → String
  | .projectAxiom => "RG1001"
  | .proofHole => "RG1002"
  | .unknownAxiom => "RG1003"
  | .nativeProof => "RG1004"
  | .profileExceeded => "RG1005"
  | .escapeHatch => "RG1006"
  | .language => "RG1010"
  | .environment => "RG2001"

/-- Each rule once. -/
def all : List RuleId :=
  [.projectAxiom, .proofHole, .unknownAxiom, .nativeProof, .profileExceeded, .escapeHatch,
    .language, .environment]

/-- `all` lists each rule. -/
theorem mem_all (id : RuleId) : id ∈ all := by
  cases id <;> simp [all]

/-- `all` lists no rule twice. -/
theorem all_nodup : all.Nodup := by decide

/-- Distinct rules have distinct names. -/
theorem spelling_injective : Function.Injective spelling := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

end RuleId

end Regula
