/-
Positive control for the executable-contract gate (`ContractScope.mayReach`),
in a module that imports `Regula.Contract`, so the gate searches each
declared type's unfolding closure. A registration whose declared type reaches
`Regula.ExecutableContract` only through an alias must still be recognized.
A proposition computed from a 64-bit literal, which Lean elaborates without
reducing it but whose reduction at `.all` transparency exhausts Lean's
recursion depth, is not a registration and must be recorded without that
reduction.
-/
import Regula.Contract

def aliasedIdentity (n : Nat) : Nat := n

def AliasedIdentityContract : Prop :=
  Regula.ExecutableContract aliasedIdentity (fun f => ∀ n, f n = n)

theorem aliasedIdentity_contract : AliasedIdentityContract := ⟨fun _ => rfl⟩

@[irreducible] noncomputable def Chain : Nat → Prop
  | 0 => True
  | n + 1 => Chain n

theorem chain_all (n : Nat) : Chain n := by
  induction n with
  | zero => unfold Chain; trivial
  | succ n ih => unfold Chain; exact ih

theorem chain_large : Chain 18446744073709551615 := chain_all _
