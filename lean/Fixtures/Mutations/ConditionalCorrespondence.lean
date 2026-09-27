import Init
/-! A theorem-only impossible premise cannot establish unconditional agreement. -/
/-- The successor, which the compiler runs in place of `falseReference`. -/
def falseReplacement (n : Nat) : Nat := n + 1
/-- A reference whose compiled code is `falseReplacement`. -/
@[implemented_by falseReplacement]
def falseReference (n : Nat) : Nat := n
theorem falseCorrespondence (n : Nat) (h : False) :
    falseReference n = falseReplacement n := False.elim h
