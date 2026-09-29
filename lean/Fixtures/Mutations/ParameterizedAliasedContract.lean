/-
Mutation of `Fixtures.Positive.AliasedContract`: the alias takes the point the
implementation is applied at, so the registration reached through it has a
parameter and is not closed. The executable-contract gate must still find the
contract type behind the parameterized alias, and the checker must report
RG1007.
-/
import Regula.Contract

def pointIdentity (n : Nat) : Nat := n

def PointIdentityContract (n : Nat) : Prop :=
  Regula.ExecutableContract (pointIdentity n) (fun value => value = n)

theorem pointIdentity_contract (n : Nat) : PointIdentityContract n := ⟨rfl⟩
