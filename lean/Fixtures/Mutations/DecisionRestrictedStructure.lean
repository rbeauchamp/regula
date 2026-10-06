/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary: the kind is
stated about the implementation applied to two of the three fields of a structure. The third
field is a proof that restricts the structure to the pairs in order, so the kind says nothing of
the other pairs. Lean accepts the proof; the checker must refuse the registration under RG1007
and name the function the kind decides.
-/
import Regula.Contract

def within (low high : Nat) : Bool := decide (high - low < 3)

/-- Two numbers in order. -/
structure Ordered where
  /-- The lower number. -/
  low : Nat
  /-- The higher number. -/
  high : Nat
  /-- The numbers are in order. -/
  ordered : low ≤ high

theorem within_decides :
    Regula.ExecutableContract within (fun check =>
      Regula.Decides (· = true) (fun input : Ordered => input.high < input.low + 3)
        (fun input => check input.low input.high)) :=
  ⟨.of_iff (fun input => by simp only [within, decide_eq_true_eq]; have := input.ordered; omega)
    ⟨⟨0, 0, Nat.le_refl 0⟩, by decide⟩ ⟨⟨0, 3, by decide⟩, by decide⟩⟩
