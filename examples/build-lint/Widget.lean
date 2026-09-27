import Regula.Contract

/-! Minimal executable witness with an exact, proof-required relation. -/

namespace Widget

/-- Return the next natural number. `Nat.succ` already computes this; this
named implementation is retained to demonstrate contract registration. -/
def successor (n : Nat) : Nat := n + 1

/-- The unchanged requirement demands this exact relation for every input; it is
not carried by the return type; an implementation with different input-output
behavior cannot satisfy it. -/
def SuccessorSpec (f : Nat → Nat) : Prop :=
  ∀ n, f n = n + 1

/-- A contract is evidence of the exact predicate applied to `successor`. -/
theorem successor_contract :
    Regula.ExecutableContract successor SuccessorSpec :=
  ⟨fun _ => rfl⟩

/-- The public API consumes the requirement's evidence. -/
def next (n : Nat) : Nat := successor_contract.run n

end Widget
