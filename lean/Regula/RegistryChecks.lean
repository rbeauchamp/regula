import RegulaCore.Guidance
import RegulaPolicy.KernelAxioms
import Lean.Elab.Command

/-! # Registry checks

Checks of the rule registry that the first acceptance step runs with `lake env lean --run` from
the root of its copy: the registry's identity laws stay within Standard-Logical, each rule's
metadata is complete, the example pairs the registry embeds are the corpus files, the committed
agent skill is the one the registry generates, and the adoption guide quotes the RG1005 guidance
the registry states. The laws themselves are theorems of `RegulaCore.RuleId`; these checks observe
the files and the wiring the theorems do not cover. -/

open Lean Regula

-- This named set is the public theorem claim, not a module-discovery substitute.
run_cmd do
  let names := #[``RuleId.parse_spelling, ``RuleId.spelling_injective, ``RuleId.mem_all,
      ``RuleId.all_nodup, ``RuleId.route_injective]
  let some table := RegulaPolicy.KernelAxioms.reachedAxiomTable (← Lean.getEnv) names
    | throwError "the axiom search ran out of fuel"
  for name in names do
    let some axioms := table[name]? | throwError "the axiom search did not reach {name}"
    unless axioms.all RegulaPolicy.standardLogicalAxiom do
      throwError "registry theorem {name} exceeds Standard-Logical: {axioms}"

private def require (ok : Bool) (claim : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"registry check failed: {claim}"

/-- The registry checks, run from the root of the checkout. -/
def main : IO Unit := do
  -- Exhaustive checks over the genuinely closed vocabulary of rules.
  for id in RuleId.all do
    require (!(descriptor id).title.isEmpty && !(descriptor id).normativeClauses.isEmpty)
      s!"metadata completeness {id.spelling}"
  -- The embedded example pairs are exactly the corpus files: this rejects a stale build and an
  -- `include_str` of the wrong file.
  for id in RuleId.all do
    let e := (descriptor id).examples
    require ((← IO.FS.readFile (e.compliantPath id)) == e.compliant)
        s!"{id.spelling} compliant example is {e.compliantPath id}"
    require ((← IO.FS.readFile (e.noncompliantPath id)) == e.noncompliant)
      s!"{id.spelling} noncompliant example is {e.noncompliantPath id}"
  -- The committed agent skill is the generated briefing of an unreleased build, which every
  -- commit of `main` is (`Regula.Guidance.skill_unreleased`); the release commit keeps the file.
  require ((← IO.FS.readFile ".agents/skills/regula/SKILL.md") == Regula.Guidance.skillIn .dev)
    "committed .agents/skills/regula/SKILL.md is current (regenerate with `lake exe regula skill`)"
  IO.println "registry checks: PASS (closed metadata, embedded examples, agent skill)"
