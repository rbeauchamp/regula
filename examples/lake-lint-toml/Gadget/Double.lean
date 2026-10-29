/-! Doubling with its specification. -/

namespace Gadget

/-- Doubling by addition. -/
def double (n : Nat) : Nat := n + n

/-- The executed definition equals multiplication by two. -/
theorem double_eq (n : Nat) : double n = 2 * n := (Nat.two_mul n).symm

end Gadget
