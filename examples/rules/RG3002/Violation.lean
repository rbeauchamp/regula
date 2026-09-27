/-! The identity specification is replaced with extensionally equal code. -/
/-- The replacement code for `identity`: it computes `0 + n`. -/
def alternative (n : Nat) : Nat := 0 + n
/-- The identity on natural numbers; compiled code runs `alternative` instead. -/
@[implemented_by alternative] def identity (n : Nat) : Nat := n
