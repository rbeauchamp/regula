import Std.Do

/-! # Triples over a state monad with exceptions, and `IO` run as a model

The models of external systems (`Regula.Filesystem.Model`) give their operations in
`EStateM ε σ`, and their assumptions and claims are `Std.Do` triples over it. `triple_iff` reads
such a triple, with a precondition and postconditions that are propositions about the state, as a
statement about the run of the action from each state. The toolchain's `EStateM.run_bind` and
`EStateM.run_pure` give the runs of `bind` and `pure`; `run_throw` and `run_tryCatch` give those of
`throw` and `tryCatchThe`, which Lean 4.35.0 states for `throw` at `PUnit` only and for
`tryCatchThe` not at all. Proofs about the code of a model's operations go through them.

`Std.Do`'s tactic `mvcgen` would discharge these triples, but in Lean 4.35.0 it warns that it is
deprecated in favour of `vcgen`, which warns that it is experimental, and a claimed module keeps
every default warning ([RG2003]); so the proofs reason about runs instead.

## `IO` run as a model

An `IO` action is a function from a world (`Void IO.RealWorld`) to its outcome and the world after
it (`EST`, `Init/System/ST.lean`). `Agrees view x y` states that the `IO` action `x` runs as the
model action `y`, with `view` reading each world as a model state: from each world, both have the
same outcome, and the view of the world `x` ends in is the state `y` ends in. Agreement is kept by
`pure`, `bind`, `throw` and `tryCatchThe` (`Agrees.pure`, `Agrees.bind`, `Agrees.throw`,
`Agrees.tryCatch`), from the runs of those in `EIO`, which hold case by case (`eio_pure`,
`eio_throw`, `eio_bind_ok`, `eio_bind_error`, `eio_tryCatch_ok`, `eio_tryCatch_error`). So code
written once for any monad agrees with itself at two sets of operations when each pair of
operations agrees. `io_ofExcept`, `io_toBaseIO_ok` and `io_toBaseIO_error` give the runs of
`MonadExcept.ofExcept` and of a `toBaseIO` lifted back to `IO`. `Agrees.transfer` carries what a
run of the model action satisfies to the run of the `IO` action. Agreement is a relation between
two runs, not a property of the real system: at the model whose states are the worlds, every set
of operations agrees with the model's (`Regula.Filesystem.corresponds_ofIO`), and what the real
system does is stated by the assumptions at that model.

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
      ∀ s, P s → Satisfies (x.run s) Q E := by
  simp only [Triple, wp, PredTrans.apply, SPred.entails_cons, SPred.entails_nil, EStateM.run,
    Satisfies]
  constructor
  · intro h s p
    have := h s p
    split at this <;> rename_i heq <;> simp [heq] at this ⊢ <;> exact this
  · intro h s p
    have := h s p
    split <;> rename_i heq <;> simp [heq] at this ⊢ <;> exact this

/-- A run of `throw e` fails with `e` and leaves the state. -/
theorem run_throw (e : ε) (s : σ) : (throw e : EStateM ε σ α).run s = .error e s := rfl

/-- An outcome that satisfies `Q` and `E` satisfies each pair that they imply. -/
theorem Satisfies.mono {outcome : EStateM.Result ε σ α} {Q Q' : α → σ → Prop}
    {E E' : ε → σ → Prop} (holds : Satisfies outcome Q E) (results : ∀ a s, Q a s → Q' a s)
    (errors : ∀ e s, E e s → E' e s) : Satisfies outcome Q' E' := by
  cases outcome with
  | ok a s => exact results a s holds
  | error e s => exact errors e s holds

/-- A run of `x >>= f` satisfies `Q` and `E` when the run of `x` gives a result of `P` or an error
of `E`, and the run of `f a` from each result `a` of `P` and the state it ends in satisfies `Q` and
`E`. -/
theorem Satisfies.bind {x : EStateM ε σ α} {f : α → EStateM ε σ β} {s : σ} {P : α → σ → Prop}
    {Q : β → σ → Prop} {E : ε → σ → Prop} (first : Satisfies (x.run s) P E)
    (rest : ∀ a s', P a s' → Satisfies ((f a).run s') Q E) : Satisfies ((x >>= f).run s) Q E := by
  rw [EStateM.run_bind]
  revert first
  cases x.run s with
  | ok a s' => exact rest a s'
  | error e s' => exact id

/-- A run of `tryCatchThe ε x handle` gives the result of `x`, or runs `handle` on the error of
`x` from the state where `x` failed: the state is not restored, which is what the default
`Backtrackable` instance of a state type does. -/
theorem run_tryCatch (x : EStateM ε σ α) (handle : ε → EStateM ε σ α) (s : σ) :
    (tryCatchThe ε x handle).run s = match x.run s with
      | .ok a s' => .ok a s'
      | .error e s' => (handle e).run s' := by
  show EStateM.tryCatch x handle s = match x s with
    | .ok a s' => .ok a s'
    | .error e s' => handle e s'
  unfold EStateM.tryCatch
  cases x s <;> rfl

/-! ## `IO` run as a model -/

/-- The `EIO` action `x` runs as the model action `y` when each world is read as the model state
`view` gives: from each world, both have the same outcome, and the view of the world `x` ends in
is the state `y` ends in. -/
def Agrees (view : Void IO.RealWorld → σ) (x : EIO ε α) (y : EStateM ε σ α) : Prop :=
  ∀ w, match x w with
    | .ok a w' => y.run (view w) = .ok a (view w')
    | .error e w' => y.run (view w) = .error e (view w')

/-- The outcome of a run of an `EIO` action satisfies `Q` when it is a result and `E` when it is
an error, each read with the model state that `view` gives for the world the run ends in. -/
def RunsTo (view : Void IO.RealWorld → σ) (outcome : EST.Out ε IO.RealWorld α)
    (Q : α → σ → Prop) (E : ε → σ → Prop) : Prop :=
  match outcome with
  | .ok a w => Q a (view w)
  | .error e w => E e (view w)

/-- What the run of the model action satisfies from the view of a world, the run of an agreeing
`EIO` action from that world satisfies. -/
theorem Agrees.transfer {view : Void IO.RealWorld → σ} {x : EIO ε α} {y : EStateM ε σ α}
    (agrees : Agrees view x y) (w : Void IO.RealWorld) {Q : α → σ → Prop} {E : ε → σ → Prop}
    (model : Satisfies (y.run (view w)) Q E) : RunsTo view (x w) Q E := by
  have h := agrees w
  revert h
  unfold RunsTo
  split <;> (intro h; rw [h] at model; exact model)

/-- A run of `pure a` in `EIO` gives `a` and leaves the world. -/
theorem eio_pure (a : α) (w : Void IO.RealWorld) : (Pure.pure a : EIO ε α) w = .ok a w := by
  show EST.pure a w = _
  unfold EST.pure
  rfl

/-- A run of `throw e` in `EIO` fails with `e` and leaves the world. -/
theorem eio_throw (e : ε) (w : Void IO.RealWorld) :
    (MonadExcept.throw e : EIO ε α) w = .error e w := by
  show EST.throw e w = _
  unfold EST.throw
  rfl

/-- A run of `x >>= f` in `EIO` where `x` gives `a` runs `f a` from the world `x` ends in. -/
theorem eio_bind_ok {x : EIO ε α} {w w' : Void IO.RealWorld} {a : α} (ran : x w = .ok a w')
    (f : α → EIO ε β) : (x >>= f) w = f a w' := by
  show EST.bind x f w = _
  unfold EST.bind
  rw [ran]

/-- A run of `x >>= f` in `EIO` where `x` fails stops with the error of `x`. -/
theorem eio_bind_error {x : EIO ε α} {w w' : Void IO.RealWorld} {e : ε} (ran : x w = .error e w')
    (f : α → EIO ε β) : (x >>= f) w = .error e w' := by
  show EST.bind x f w = _
  unfold EST.bind
  rw [ran]

/-- A run of `tryCatchThe ε x f` in `EIO` where `x` gives `a` gives `a`. -/
theorem eio_tryCatch_ok {x : EIO ε α} {w w' : Void IO.RealWorld} {a : α} (ran : x w = .ok a w')
    (f : ε → EIO ε α) : tryCatchThe ε x f w = .ok a w' := by
  show EST.tryCatch x f w = _
  unfold EST.tryCatch
  rw [ran]

/-- A run of `tryCatchThe ε x f` in `EIO` where `x` fails runs `f` on the error from the world
`x` ends in. -/
theorem eio_tryCatch_error {x : EIO ε α} {w w' : Void IO.RealWorld} {e : ε}
    (ran : x w = .error e w') (f : ε → EIO ε α) : tryCatchThe ε x f w = f e w' := by
  show EST.tryCatch x f w = _
  unfold EST.tryCatch
  rw [ran]

/-- A run of `MonadExcept.ofExcept r` in `IO` gives the value of `r`, or fails with its error, and
leaves the world. -/
theorem io_ofExcept (r : Except IO.Error α) (w : Void IO.RealWorld) :
    (MonadExcept.ofExcept r : IO α) w = match r with
      | .ok a => .ok a w
      | .error e => .error e w := by
  cases r with
  | ok a => exact eio_pure a w
  | error e => exact eio_throw e w

/-- A run in `IO` of `x.toBaseIO`, lifted from `BaseIO`, where `x` gives `a`, gives `.ok a` and
ends where `x` ends. -/
theorem io_toBaseIO_ok {x : IO α} {w w' : Void IO.RealWorld} {a : α}
    (ran : x w = .ok a w') :
    (liftM (m := BaseIO) (n := IO) x.toBaseIO) w = .ok (.ok a) w' := by
  show BaseIO.toEIO (EIO.toBaseIO x) w = _
  unfold BaseIO.toEIO EIO.toBaseIO
  simp [ran]

/-- A run in `IO` of `x.toBaseIO`, lifted from `BaseIO`, where `x` fails with `e`, gives
`.error e` and ends where `x` ends. -/
theorem io_toBaseIO_error {x : IO α} {w w' : Void IO.RealWorld} {e : IO.Error}
    (ran : x w = .error e w') :
    (liftM (m := BaseIO) (n := IO) x.toBaseIO) w = .ok (.error e) w' := by
  show BaseIO.toEIO (EIO.toBaseIO x) w = _
  unfold BaseIO.toEIO EIO.toBaseIO
  simp [ran]

/-- `pure a` in `EIO` runs as `pure a` in the model. -/
theorem Agrees.pure (view : Void IO.RealWorld → σ) (a : α) :
    Agrees view (Pure.pure a : EIO ε α) (Pure.pure a : EStateM ε σ α) := by
  intro w
  rw [eio_pure]
  rfl

/-- `throw e` in `EIO` runs as `throw e` in the model. -/
theorem Agrees.throw (view : Void IO.RealWorld → σ) (e : ε) :
    Agrees view (MonadExcept.throw e : EIO ε α) (MonadExcept.throw e : EStateM ε σ α) := by
  intro w
  rw [eio_throw]
  rfl

/-- A `bind` of agreeing actions agrees. -/
theorem Agrees.bind {view : Void IO.RealWorld → σ} {x : EIO ε α} {y : EStateM ε σ α}
    {f : α → EIO ε β} {g : α → EStateM ε σ β} (first : Agrees view x y)
    (rest : ∀ a, Agrees view (f a) (g a)) : Agrees view (x >>= f) (y >>= g) := by
  intro w
  have h := first w
  revert h
  cases ran : x w with
  | ok a w' =>
    intro h
    rw [eio_bind_ok ran]
    have := rest a w'
    simp only [EStateM.run_bind, h]
    exact this
  | error e w' =>
    intro h
    rw [eio_bind_error ran]
    simp only [EStateM.run_bind, h]

/-- A `tryCatchThe` of agreeing actions agrees. -/
theorem Agrees.tryCatch {view : Void IO.RealWorld → σ} {x : EIO ε α} {y : EStateM ε σ α}
    {f : ε → EIO ε α} {g : ε → EStateM ε σ α} (first : Agrees view x y)
    (handle : ∀ e, Agrees view (f e) (g e)) :
    Agrees view (tryCatchThe ε x f) (tryCatchThe ε y g) := by
  intro w
  have h := first w
  revert h
  cases ran : x w with
  | ok a w' =>
    intro h
    rw [eio_tryCatch_ok ran]
    simp only [run_tryCatch, h]
  | error e w' =>
    intro h
    rw [eio_tryCatch_error ran]
    have := handle e w'
    simp only [run_tryCatch, h]
    exact this

end Regula.StateTriple
