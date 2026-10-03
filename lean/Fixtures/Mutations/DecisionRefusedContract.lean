/-
Mutation of `Fixtures.Positive.DecisionRegistration`: the registered decision's only decision
contract is refused under RG1007, because its specification is the implementation's own verdict.
A refused registration decides nothing, so the checker must report the registration under RG1007
and the function under RG1008.
-/
import Regula.Contract
import Regula.Decision

@[regula_decision] def positive (n : Nat) : Bool := decide (0 < n)

theorem positive_decides :
    Regula.ExecutableContract positive (Regula.Decides (· = true) fun n => positive n = true) :=
  ⟨{ sound := fun _ accepted => accepted
     accepted := ⟨1, by decide⟩
     complete := fun _ holds => holds
     refused := ⟨0, by decide⟩ }⟩
