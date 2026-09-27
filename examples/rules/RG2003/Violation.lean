/-! Identity on natural numbers. -/
/-- The identity function on natural numbers. -/
def identity (n : Nat) : Nat := (fun unused : Nat => n) 0
