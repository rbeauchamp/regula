/-
Mutation of `Fixtures.Positive.DecisionKinds`: the specification is the implementation's own
verdict, reached through a definition, so both directions hold by reflexivity. Lean accepts the
proof; the checker must refuse the registration under RG1007 and name the definition through
which the specification mentions the implementation.
-/
import Regula.Contract

def positive (n : Nat) : Bool := decide (0 < n)

def Accepted (n : Nat) : Prop := positive n = true

theorem positive_decides : Regula.ExecutableContract positive (Regula.Decides (· = true) Accepted) :=
  ⟨{ sound := fun _ accepted => accepted
     accepted := ⟨1, by decide⟩
     complete := fun _ holds => holds
     refused := ⟨0, by decide⟩ }⟩
