module

/-!
# Executable contracts

Proof requirements for a named executable definition. `ExecutableContract f R` requires a proof of
`R f` and does not establish whether `R` expresses the intended behavior. This module is a library
and gives no verdict: no check of Regula reads it.

A function that acts as a checker (a parser, decoder, validator or admission function) is a
decision: some of its results accept the input and the others refuse it. `DecidesSoundly`,
`DecidesCompletely` and `Decides` state which directions of a decision are proved against a
specification. Each direction is a field, so Lean's kernel checks it, and a one-way guarantee can be
registered only under the structure that names it. Each kind also carries a witness about `f`
itself, so the function that refuses every input has no sound kind and the function that accepts
every input has no complete kind. `DecisionEquivalence` states the two directions with no witness,
and it is not a kind, because an equivalence holds on an empty domain, where `f` gives no outcome.

A function of several arguments is decided on the product of its arguments. One form is
`Function.uncurry f`, so that the registered implementation stays the constant its callers run.
The other is the function that applies `f` to the fields of one structure, which also admits an
argument whose type depends on an earlier one, or a type, instance or proof argument. The kind
about that function is the kind about `f` when every tuple of arguments is the fields of some
value, which a type with one constructor and no index gives. No other way of supplying the
arguments has this form. A function that fixes an argument or gives a field twice, a structure
with a field that `f` does not take, and a type with an index each decide `f` on part of its
domain. Nested dependent pairs are not a form for three or more arguments: each projection carries
the pair's type, so the elaborated statement grows by a large factor with each argument, while a
structure declared for the arguments has projections of constant size.

A result type that depends on the input is decided through `Dependent.isSome` or
`Dependent.isOk`, which forget the part of the result whose type depends on the input. An
acceptance predicate or an erasure stated for every payload type can still read the payload type:
"the payload type has a value" is then the specification of a proof-carrying payload, whatever the
function returns. A result type whose dependency on the input neither erasure removes, such as an
inductive family indexed by the input, has no kind: return `Decidable _`, or state an ordinary
requirement. A subtype `{r : ρ // P x r}` is such a type, because an erasure that returns its value
would keep a free acceptance predicate on a data value.

A kind is stated about the function applied to every one of its arguments, and no hypothesis can
say so: that a result type is not a function type is not a proposition of Lean's logic. With an
argument left, an acceptance predicate that reads the result at one value `b` of that argument
gives the kind of the slice at `b` (`Decides.iff_slice`), which says nothing of the function at
another value. Supply the remaining argument instead, with one more `Function.uncurry` or as a
field of the structure. A kind about a function with universe parameters is stated at those
parameters, so that it holds of every instance.

A kind compares `accepts (f x)` with `spec x` for the present definitions. When `spec` and `f`, or
`spec` and `accepts`, both call a function, a change of that function changes the two sides
together, and a proof through it can stay valid although the meaning changed. So the kind does not
establish that the shared function is the intended one. A proposition can take the place of a
shared test in `spec`, with a theorem that connects it to the function, or with a function that
decides it with `decide`. No kind says that `spec` is the intended specification, that `accepts`
is the intended reading of a result, that every caller acts on the verdict, or which value an
accepting result carries. When the result of `f` determines its input, as the identity's does, an
acceptance predicate can restate the specification: `Decides spec spec id` holds of every
specification that some input satisfies and some input does not.
-/

public section

namespace Regula

universe u v w

/-- Required evidence about the exact implementation. Use a named constant as `implementation`, and
put its complete domain inside `condition`. -/
structure ExecutableContract {α : Type u} (implementation : α)
    (condition : α → Prop) : Prop where
  /-- A proof of `condition` about exactly `implementation`. -/
  evidence : condition implementation

/-- Return the registered implementation, given the required proof. Compilation erases the proof,
and this does not certify the native runtime. The body is exposed because importers rely on
`run_eq`, which is proved by `rfl`. -/
@[expose, inline] def ExecutableContract.run {α : Type u} {implementation : α}
    {condition : α → Prop} (_ : ExecutableContract implementation condition) : α :=
  implementation

theorem ExecutableContract.run_eq {α : Type u} {implementation : α}
    {condition : α → Prop} (contract : ExecutableContract implementation condition) :
    contract.run = implementation := rfl

/-- A sound decision: `f` accepts only inputs that satisfy `spec`, and accepts at least one input.
`accepts` says which results are acceptances, such as `(· = true)` for a Boolean check or
`(·.isSome)` for a parser. It does not claim completeness (`f` may refuse inputs that satisfy
`spec`), that `spec` is the intended specification, or which value an accepting result carries. -/
structure DecidesSoundly {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  /-- Soundness: every input `f` accepts satisfies the specification. -/
  sound : ∀ x, accepts (f x) → spec x
  /-- `f` accepts some input. Without it the function that refuses every input would be sound for
  every specification, and a satisfiable `spec` alone does not exclude that function. -/
  accepted : ∃ x, accepts (f x)

/-- A complete decision: `f` accepts every input that satisfies `spec`, and refuses at least one
input. It does not claim soundness (`f` may accept inputs that do not satisfy `spec`), that `spec`
is the intended specification, or which value an accepting result carries. -/
structure DecidesCompletely {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  /-- Completeness: `f` accepts every input that satisfies the specification. -/
  complete : ∀ x, spec x → accepts (f x)
  /-- `f` refuses some input. Without it the function that accepts every input would be complete for
  every specification. -/
  refused : ∃ x, ¬ accepts (f x)

/-- A sound and complete decision: `f` accepts exactly the inputs that satisfy `spec`, and both
outcomes occur. It does not claim that `spec` is the intended specification, that it is stated
independently of `f` in substance, or which value an accepting result carries. -/
structure Decides {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop
    extends DecidesSoundly accepts spec f, DecidesCompletely accepts spec f

/-- A decision law: `f` accepts exactly the inputs that satisfy `spec`. It has neither witness, so it
is not a decision kind: it holds on an empty domain, where `f` neither accepts nor refuses an input.
It does not claim that `f` accepts or refuses some input, that `spec` holds or fails of some input,
that `spec` is the intended specification, or which value an accepting result carries. -/
structure DecisionEquivalence {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  /-- `f` accepts an input exactly when the input satisfies the specification. -/
  iff : ∀ x, accepts (f x) ↔ spec x

section
variable {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop} {f : α → ρ}

theorem Decides.iff (decides : Decides accepts spec f) (x : α) : accepts (f x) ↔ spec x :=
  ⟨decides.sound x, decides.complete x⟩

theorem Decides.of_iff (iff : ∀ x, accepts (f x) ↔ spec x) (accepted : ∃ x, accepts (f x))
    (refused : ∃ x, ¬ accepts (f x)) : Decides accepts spec f :=
  { sound := fun x => (iff x).mp, accepted, complete := fun x => (iff x).mpr, refused }

theorem Decides.toEquivalence (decides : Decides accepts spec f) :
    DecisionEquivalence accepts spec f :=
  ⟨decides.iff⟩

theorem DecisionEquivalence.sound (law : DecisionEquivalence accepts spec f) (x : α) :
    accepts (f x) → spec x :=
  (law.iff x).mp

theorem DecisionEquivalence.complete (law : DecisionEquivalence accepts spec f) (x : α) :
    spec x → accepts (f x) :=
  (law.iff x).mpr

theorem DecisionEquivalence.toSoundly (law : DecisionEquivalence accepts spec f)
    (accepted : ∃ x, accepts (f x)) : DecidesSoundly accepts spec f :=
  { sound := law.sound, accepted }

theorem DecisionEquivalence.toCompletely (law : DecisionEquivalence accepts spec f)
    (refused : ∃ x, ¬ accepts (f x)) : DecidesCompletely accepts spec f :=
  { complete := law.complete, refused }

theorem DecisionEquivalence.of_empty (empty : α → False) :
    DecisionEquivalence accepts spec f ∧ ¬ (∃ x, accepts (f x)) ∧ ¬ ∃ x, ¬ accepts (f x) :=
  ⟨⟨fun x => (empty x).elim⟩, fun ⟨x, _⟩ => empty x, fun ⟨x, _⟩ => empty x⟩

theorem Decides.of_roundtrip {β : Type u} {σ : Sort v} {write : β → σ} {parse : σ → Option β}
    (roundtrip : ∀ x, parse (write x) = some x)
    (canonical : ∀ s x, parse s = some x → write x = s)
    (value : β) {unwritten : σ} (refuses : parse unwritten = none) :
    Decides (·.isSome = true) (fun s => ∃ x, s = write x) parse :=
  { sound := fun s accepted => by
      cases h : parse s with
      | some x => exact ⟨x, (canonical s x h).symm⟩
      | none => rw [h] at accepted; exact absurd accepted Bool.false_ne_true
    accepted := ⟨write value, by rw [roundtrip]; rfl⟩
    complete := fun s ⟨x, written⟩ => by rw [written, roundtrip]; rfl
    refused := ⟨unwritten, by rw [refuses]; exact Bool.false_ne_true⟩ }

theorem DecidesSoundly.satisfiable (decides : DecidesSoundly accepts spec f) : ∃ x, spec x :=
  decides.accepted.elim fun x h => ⟨x, decides.sound x h⟩

theorem DecidesCompletely.refutable (decides : DecidesCompletely accepts spec f) :
    ∃ x, ¬ spec x :=
  decides.refused.elim fun x h => ⟨x, fun holds => h (decides.complete x holds)⟩

theorem DecidesSoundly.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x)) :
    ¬ DecidesSoundly accepts spec f :=
  fun decides => decides.accepted.elim refuses

theorem DecidesCompletely.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x))
    (satisfiable : ∃ x, spec x) : ¬ DecidesCompletely accepts spec f :=
  fun decides => satisfiable.elim fun x holds => refuses x (decides.complete x holds)

theorem DecidesCompletely.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x)) :
    ¬ DecidesCompletely accepts spec f :=
  fun decides => decides.refused.elim fun x h => h (acceptsAll x)

theorem DecidesSoundly.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x))
    (refutable : ∃ x, ¬ spec x) : ¬ DecidesSoundly accepts spec f :=
  fun decides => refutable.elim fun x fails => fails (decides.sound x (acceptsAll x))

end

section
variable {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}

theorem Decides.not_of_constant (result : ρ) : ¬ Decides accepts spec (fun _ : α => result) :=
  fun decides => decides.accepted.elim fun _ accepted =>
    decides.refused.elim fun _ refused => refused accepted

theorem DecisionEquivalence.of_constant (result : ρ) :
    DecisionEquivalence accepts (fun _ : α => accepts result) (fun _ : α => result) :=
  ⟨fun _ => Iff.rfl⟩

theorem DecidesSoundly.spec_of_constant {result : ρ}
    (decides : DecidesSoundly accepts spec (fun _ : α => result)) (x : α) : spec x :=
  decides.accepted.elim fun _ accepted => decides.sound x accepted

theorem DecidesCompletely.not_spec_of_constant {result : ρ}
    (decides : DecidesCompletely accepts spec (fun _ : α => result)) (x : α) : ¬ spec x :=
  fun holds => decides.refused.elim fun _ refused => refused (decides.complete x holds)

end

section
variable {σ : Sort w} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
  {f : α → ρ} {fields : σ → α}

theorem DecidesSoundly.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : DecidesSoundly accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    DecidesSoundly accepts spec f :=
  { sound := fun x accepted => (covers x).elim fun s same =>
      same ▸ decides.sound s (same ▸ accepted)
    accepted := decides.accepted.elim fun s accepted => ⟨fields s, accepted⟩ }

theorem DecidesCompletely.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : DecidesCompletely accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    DecidesCompletely accepts spec f :=
  { complete := fun x holds => (covers x).elim fun s same =>
      same ▸ decides.complete s (same ▸ holds)
    refused := decides.refused.elim fun s refused => ⟨fields s, refused⟩ }

theorem Decides.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : Decides accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    Decides accepts spec f :=
  { toDecidesSoundly := .of_packing covers decides.toDecidesSoundly
    toDecidesCompletely := .of_packing covers decides.toDecidesCompletely }

end

theorem uncurry_eq_fields {α : Type u} {β : Type v} {φ : Sort w} (f : α → β → φ) :
    Function.uncurry f = fun p => f p.1 p.2 := rfl

theorem packing_uncurry_covers {σ : Type u} {α : Type v} {β : Type w} {fields : σ → α}
    (covers : ∀ x, ∃ s, fields s = x) : ∀ p : α × β, ∃ q : σ × β, (fields q.1, q.2) = p :=
  fun p => (covers p.1).elim fun s packed => ⟨(s, p.2), by rw [packed]⟩

section
variable {α : Sort u} {β : Sort w} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
  {g : α → β → ρ}

theorem DecidesSoundly.iff_slice (b : β) :
    DecidesSoundly (fun h : β → ρ => accepts (h b)) spec g ↔
      DecidesSoundly accepts spec (fun x => g x b) :=
  ⟨fun decides => ⟨decides.sound, decides.accepted⟩,
    fun decides => ⟨decides.sound, decides.accepted⟩⟩

theorem DecidesCompletely.iff_slice (b : β) :
    DecidesCompletely (fun h : β → ρ => accepts (h b)) spec g ↔
      DecidesCompletely accepts spec (fun x => g x b) :=
  ⟨fun decides => ⟨decides.complete, decides.refused⟩,
    fun decides => ⟨decides.complete, decides.refused⟩⟩

theorem Decides.iff_slice (b : β) :
    Decides (fun h : β → ρ => accepts (h b)) spec g ↔ Decides accepts spec (fun x => g x b) :=
  ⟨fun decides =>
      { toDecidesSoundly := (DecidesSoundly.iff_slice b).mp decides.toDecidesSoundly
        toDecidesCompletely := (DecidesCompletely.iff_slice b).mp decides.toDecidesCompletely },
    fun decides =>
      { toDecidesSoundly := (DecidesSoundly.iff_slice b).mpr decides.toDecidesSoundly
        toDecidesCompletely := (DecidesCompletely.iff_slice b).mpr decides.toDecidesCompletely }⟩

end

namespace Dependent

/-- Whether an optional result holds a payload, with the payload forgotten. -/
def isSome {α : Sort u} {payload : α → Type v} (f : ∀ x, Option (payload x)) (x : α) : Bool :=
  (f x).isSome

/-- Whether a result is a success, with the payload and the error forgotten. -/
def isOk {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    (f : ∀ x, Except (ε x) (payload x)) (x : α) : Bool :=
  (f x).isOk

theorem isSome_eq_true_iff {α : Sort u} {payload : α → Type v} (f : ∀ x, Option (payload x))
    (x : α) : isSome f x = true ↔ ∃ value, f x = some value := by
  unfold isSome
  cases f x with
  | none => exact ⟨fun holds => absurd holds Bool.false_ne_true, fun ⟨_, same⟩ => nomatch same⟩
  | some value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

theorem isOk_eq_true_iff {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    (f : ∀ x, Except (ε x) (payload x)) (x : α) : isOk f x = true ↔ ∃ value, f x = .ok value := by
  unfold isOk
  cases f x with
  | error _ => exact ⟨fun holds => absurd holds Bool.false_ne_true, fun ⟨_, same⟩ => nomatch same⟩
  | ok value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

end Dependent

/- Realize these equation lemmas here, once, so importers that unfold the definitions use the
same declarations. -/
section
attribute [local simp] Except.toBool.eq_1 Except.toBool.eq_2 Function.uncurry.eq_1
  Dependent.isSome.eq_1 ExecutableContract.run.eq_1
end

end Regula
