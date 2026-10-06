/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary, for the second
review's first finding: the registration supplies an erasure of its own, which reads the payload
type and not the result. The function refuses every input, and "the payload type has a value" is
its specification, so Lean accepts a two-way kind about the erased function. The checker reads
only the two erasures of `Regula.Contract`, so it must refuse the registration under RG1007
and name the function the kind decides.
-/
import Regula.Contract

/-- Refuses every input; its result type would carry the number with a proof. -/
def refuseAll (n : Nat) : Option {m : Nat // m = n ∧ 0 < m} := none

/-- An erasure that ignores the result: whether the payload type has a value. -/
noncomputable def hasPayload {payload : Nat → Type} (_ : ∀ n, Option (payload n)) (n : Nat) :
    Bool :=
  @decide (Nonempty (payload n)) (Classical.propDecidable _)

theorem refuseAll_decides :
    Regula.ExecutableContract refuseAll (fun parse =>
      Regula.Decides (· = true) (fun n => 0 < n) (hasPayload parse)) :=
  have iff (n : Nat) : hasPayload refuseAll n = true ↔ 0 < n := by
    unfold hasPayload
    rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
    exact ⟨fun ⟨⟨_, same, positive⟩⟩ => same ▸ positive, fun positive => ⟨⟨n, rfl, positive⟩⟩⟩
  ⟨.of_iff iff ⟨1, (iff 1).mpr (by decide)⟩
    ⟨0, fun accepted => absurd ((iff 0).mp accepted) (by decide)⟩⟩
