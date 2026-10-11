import Std.Do

/-! # Triples over a state monad with exceptions, read through its runs

The models of external systems (`Regula.Filesystem.Model`) give their operations in
`EStateM ε σ`, and their assumptions and claims are `Std.Do` triples over it. `triple_iff` reads
such a triple, with a precondition and postconditions that are propositions about the state, as a
statement about the run of the action from each state; the `run_*` equations give the runs of the
monad's operations. Proofs about the code of a model's operations go through them.

`Std.Do`'s tactic `mvcgen` would discharge these triples, but in Lean 4.34.1 it warns that it is
experimental, and a claimed module keeps every default warning ([RG2003]); so the proofs reason
about runs instead.

[RG2003]: https://rbeauchamp.github.io/regula/dev/rules/RG2003/ -/

namespace Regula.StateTriple

open Std.Do

variable {ε σ α β : Type}

/-- The outcome of a run satisfies `Q` when it is a result and `E` when it is an error, each read
with the state the run ends in. -/
def Satisfies (outcome : EStateM.Result ε σ α) (Q : α → σ → Prop) (E : ε → σ → Prop) : Prop :=
  match outcome with
  | .ok a s => Q a s
  | .error e s => E e s

/-- A triple over `EStateM ε σ` whose precondition and postconditions are propositions about the
state holds exactly when every run from a state that satisfies the precondition ends in a state
that satisfies the postcondition of its outcome: `Q` for a result, `E` for an error. -/
theorem triple_iff (x : EStateM ε σ α) (P : σ → Prop) (Q : α → σ → Prop) (E : ε → σ → Prop) :
    ⦃fun s => ⌜P s⌝⦄ x ⦃post⟨fun a s => ⌜Q a s⌝, fun e s => ⌜E e s⌝⟩⦄ ↔
      ∀ s, P s → Satisfies (x s) Q E := by
  simp only [Triple, wp, PredTrans.apply, SPred.entails_cons, SPred.entails_nil, EStateM.run,
    Satisfies]
  constructor
  · intro h s p
    have := h s p
    split at this <;> rename_i heq <;> simp [heq] at this ⊢ <;> exact this
  · intro h s p
    have := h s p
    split <;> rename_i heq <;> simp [heq] at this ⊢ <;> exact this

/-- A run of `x >>= f` runs `x`, then `f` on its result, and stops at an error of `x`. -/
theorem run_bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f) s = match x s with
      | .ok a s' => f a s'
      | .error e s' => .error e s' := rfl

/-- A run of `pure a` gives `a` and leaves the state. -/
theorem run_pure (a : α) (s : σ) : (pure a : EStateM ε σ α) s = .ok a s := rfl

/-- A run of `throw e` fails with `e` and leaves the state. -/
theorem run_throw (e : ε) (s : σ) : (throw e : EStateM ε σ α) s = .error e s := rfl

/-- A run of `tryCatchThe ε x handle` gives the result of `x`, or runs `handle` on the error of
`x` from the state where `x` failed: the state is not restored, which is what the default
`Backtrackable` instance of a state type does. -/
theorem run_tryCatch (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) (s : σ) :
    tryCatchThe ε x handle s = match x s with
      | .ok a s' => .ok a s'
      | .error e s' => handle e s' := by
  show EStateM.tryCatch x handle s = _
  unfold EStateM.tryCatch
  cases x s <;> rfl

end Regula.StateTriple
