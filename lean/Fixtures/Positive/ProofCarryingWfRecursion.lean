/-
Positive control (issues #126 and #125): well-founded recursion that passes a
tactic proof to its recursive call. Lean elaborates it without error; the
declaration-report worker must complete its report instead of failing with
Lean's maximum recursion depth while comparing the generated helper with its
predefinition. Lean abstracts the nested proof into an auxiliary theorem in
the stored predefinition but keeps it inline in the helper, so the helper
equals the compiler transformation only up to proofs, which the checker's
comparison admits; the proof's own `intro`, `·` and sequence tactic nodes,
recorded under their dispatching built-in elaborators, are pinned.
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
