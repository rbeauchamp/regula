import Lean
/-! Identity and its extensionally equal replacement. -/
/-- The replacement code for `identity`: it computes `0 + n`. -/
def alternative (n : Nat) : Nat := 0 + n
/-- The identity on natural numbers; compiled code runs `alternative` instead. -/
@[implemented_by alternative] def identity (n : Nat) : Nat := n
theorem correspondence (n : Nat) : identity n = alternative n := (Nat.zero_add n).symm
run_cmd pure ()
