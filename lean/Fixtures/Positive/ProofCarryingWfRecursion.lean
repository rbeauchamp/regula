/-
Positive control (issues #126 and #125): well-founded recursion that passes a
tactic proof to its recursive call. Lean elaborates it without error; the
declaration-report worker must complete its report instead of failing with
Lean's maximum recursion depth while comparing the generated helper with its
predefinition. Exact match admits the helper: Lean's well-founded recursion
compiler, rerun on the helper with every decreasing proof elided, regenerates
the observed base up to compilation erasure, the passed proof included.
-/

def allSmall (bytes : ByteArray) (start : Nat)
    (checked : ∀ (index : Nat), index < start → ∀ (bound : index < bytes.size),
      bytes[index].toNat < 8) : Bool :=
  if bound : start < bytes.size then
    if small : bytes[start].toNat < 8 then
      allSmall bytes (start + 1) (by
        intro index upper inside
        by_cases same : index = start
        · subst index; exact small
        · exact checked index (by omega) inside)
    else false
  else true
termination_by bytes.size - start
