/-
Positive control, the dependency of `Fixtures.Positive.CycleAxiomReading` for item 7 of issue #285
(https://github.com/rbeauchamp/regula/issues/285): an inductive type whose two constructors reach
different axioms, `Classical.choice` through one and `propext` through the other. The type, each
constructor and each declaration that uses one of them rests on both. When Lean writes this
module's axiom table, its `collectAxioms` reads the empty entry it inserted for a member of the
cycle it is still expanding, so the entry of at least one member of the cycle lacks one of the two.
-/

theorem fixtures_true_and_true : (True ∧ True) = True :=
  propext ⟨fun h => h.1, fun _ => ⟨trivial, trivial⟩⟩

inductive FixturesCycle where
  | chosen (n : Nat) : n = Classical.choice ⟨0⟩ → FixturesCycle
  | extensional (h : (True ∧ True) = True) : h = fixtures_true_and_true → FixturesCycle

def fixtures_cycle_type : Type := FixturesCycle

theorem fixtures_cycle_chosen (h : 0 = Classical.choice ⟨0⟩) : Nonempty FixturesCycle :=
  ⟨.chosen 0 h⟩

theorem fixtures_cycle_extensional : Nonempty FixturesCycle :=
  ⟨.extensional fixtures_true_and_true rfl⟩
