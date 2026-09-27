module

/-!
Proof requirements for a named executable definition. `ExecutableContract f R`
requires a proof of `R f`; it does not infer whether `R` expresses the intended
behavior. The build linter separately checks that the registered `f` is an
executable constant and accounts for its compiler/runtime boundaries.
-/

@[expose] public section

namespace Regula

universe u

/-- Required evidence about the exact implementation, not a similarly named model.
The linter recognizes closed declarations of this type as executable promises.
Use a named constant as `implementation`; put its complete domain inside `condition`.
Classical evidence is permitted under the selected Standard-Logical profile. -/
structure ExecutableContract {α : Type u} (implementation : α)
    (condition : α → Prop) : Prop where
  evidence : condition implementation

/-- Consume the required proof and return exactly the registered implementation.
The proof is erased by compilation; this does not certify the native runtime. -/
@[inline] def ExecutableContract.run {α : Type u} {implementation : α}
    {condition : α → Prop} (_ : ExecutableContract implementation condition) : α :=
  implementation

/-- Kernel reduction connects the proof-requiring entrypoint to its implementation. -/
theorem ExecutableContract.run_eq {α : Type u} {implementation : α}
    {condition : α → Prop} (contract : ExecutableContract implementation condition) :
    contract.run = implementation := rfl

end Regula
