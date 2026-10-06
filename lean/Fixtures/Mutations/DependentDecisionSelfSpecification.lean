/-
Mutation of `Fixtures.Positive.DependentDecisionKinds`, at the toolchain boundary: the
specification of a kind of `Regula.Dependent` is the implementation's own verdict, so both
directions hold by reflexivity. Lean accepts the proof; the checker must read the kind and refuse
the registration under RG1007 for the mention, as it does for a kind of `Regula`.
-/
import Regula.Contract

def positive? (n : Nat) : Option {m : Nat // m = n ∧ 0 < m} :=
  if h : 0 < n then some ⟨n, rfl, h⟩ else none

theorem positive?_decides :
    Regula.ExecutableContract positive?
      (Regula.Dependent.Decides (·.isSome = true) fun n => (positive? n).isSome = true) :=
  ⟨.of_iff (fun _ => Iff.rfl) ⟨1, by simp [positive?]⟩ ⟨0, by simp [positive?]⟩⟩
