/-
Positive control for item 7 of issue #285 (https://github.com/rbeauchamp/regula/issues/285): the
axioms of a constant of an imported cycle. Each constructor of `FixturesCycle` uses the type,
whose declaration holds both constructors, so each member of the cycle rests on both
`Classical.choice` and `propext`. The first check is the counterexample: Lean's `collectAxioms`
reads the imported module's table, where at least one member of the cycle lacks one of them. The
second requires the checker's own search (`RegulaPolicy.KernelAxioms.reachedAxioms`), which the
editor's records and the in-module axiom ceilings read, to give each member both. Before the fix,
those read `collectAxioms`, so the second check failed with the first.
-/
import Fixtures.Positive.CycleAxiomTable
import RegulaPolicy.KernelAxioms
import Lean.Elab.Command

open Lean in
run_cmd do
  let members := [``FixturesCycle, ``FixturesCycle.chosen, ``FixturesCycle.extensional]
  let both := fun (axioms : Array Name) =>
    axioms.contains ``Classical.choice && axioms.contains ``propext
  unless ← members.anyM fun name => return !both (← collectAxioms name) do
    throwError "collectAxioms gives every member of the imported cycle both axioms"
  for name in members do
    let some axioms := RegulaPolicy.KernelAxioms.reachedAxioms (← getEnv) name
      | throwError "the axiom search from {name} ran out of fuel"
    unless both axioms do
      throwError "the axioms {name} reaches are {axioms}, not both"

theorem fixtures_cycle_reading : Nonempty FixturesCycle := fixtures_cycle_extensional
