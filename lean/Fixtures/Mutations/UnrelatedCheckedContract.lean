/-
Intended failure: a checked operation whose contract is a theorem about another constant.
`other_bounded` is a theorem, but its statement does not use `step`, so it states no postcondition
of `step`, and `@[regula_checked]` refuses it.
-/
import Regula.Assumption

namespace Fixtures.UnrelatedCheckedContract

def step (n : Nat) : Option Nat := if n < 10 then some (n + 1) else none

def other (n : Nat) : Nat := n

theorem other_bounded (n : Nat) : other n ≤ n := Nat.le_refl n

attribute [regula_checked filesystem other_bounded
  (trusted "control: a theorem about another constant")] step

end Fixtures.UnrelatedCheckedContract
