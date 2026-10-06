module

/-!
# Executable contracts

Proof requirements for a named executable definition. `ExecutableContract f R`
requires a proof of `R f`; it does not infer whether `R` expresses the intended
behavior. The build linter separately checks that the registered `f` is an
executable constant and accounts for its compiler/runtime boundaries.

## Decision kinds

A function that acts as a checker (a parser, decoder, validator or admission function) is a
*decision*: some of its results accept the input and the others refuse it. Three requirements,
used as the `condition` of an `ExecutableContract`, state which direction of such a decision is
proved against a specification `spec`:

* `DecidesSoundly accepts spec f`: `f` accepts only inputs that satisfy `spec`.
* `DecidesCompletely accepts spec f`: `f` accepts every input that satisfies `spec`.
* `Decides accepts spec f`: both.

Each direction is a field, so Lean's kernel checks it and a one-way guarantee can be registered
only under the structure that names it. Each kind also carries a witness about `f` itself, so
the function that refuses every input has no sound kind and the function that accepts every
input has no complete kind. The linter reads the kind from the head constant of the
registration's elaborated requirement and reports it, with the direction a one-way kind leaves
open.

A function of several arguments is decided on the product of its arguments: state the kind about
`Function.uncurry f`, as in `ExecutableContract f (fun g => Decides accepts spec
(Function.uncurry g))`. `Function.uncurry` is a bijection between `α → β → ρ` and `α × β → ρ`
(`Function.curry_uncurry`, `Function.uncurry_curry`), so the kind's quantifiers over the pairs
are the quantifiers over both arguments (`Prod.forall`, `Prod.exists`), and the registered
implementation stays the constant its callers run.

## Dependent and polymorphic decisions

Two forms cover a function with an argument whose type depends on an earlier argument, with a
type or instance argument, or with a result type that depends on its arguments. They can be
used separately:

* **The fields of a structure.** State the kind about the function that applies `f` to every
  field of one structure, in the order of the fields: `fun input : Input => f input.a input.b
  input.c`, where `Input` is a structure whose fields are the arguments of `f`. The type of a
  field can depend on an earlier field, and a field can be a type or an instance. A value of a
  structure is its constructor applied to its fields, and each field of the constructor applied
  to arguments is that argument (both by definition), so the kind's quantifiers over the
  structure are the quantifiers over the arguments. For two arguments the structure can be a
  pair: `Prod`, `Sigma`, `PSigma` or `Subtype`. `Function.uncurry f` is this form at `Prod`
  (`uncurry_eq_fields`). The linter reads no other way of supplying the arguments as this form:
  a function that fixes an argument or gives a field twice decides `f` on part of its domain,
  and a structure with a field that `f` does not take, such as a proof about the other fields,
  can restrict the domain.
* **A result type that depends on the input.** `Dependent.DecidesSoundly`,
  `Dependent.DecidesCompletely` and `Dependent.Decides` state the three kinds about a function
  `f : ∀ x, Result (payload x)`: the result type is one type former `Result`, such as `Option`
  or `Except ε`, applied to a payload type that depends on the input. The acceptance predicate
  is `accepts : ∀ {τ}, Result τ → Prop`. It is stated for every payload type, outside the scope
  of the input, so it reads the result and the payload type and not the input the result was
  computed from: `fun x _ => spec x`, which would make both directions hold of every `f`, is not
  an acceptance predicate. The fields are those of the three kinds above, which are the case of
  a result type that does not vary (`Dependent.decides_const` and its companions).

A kind about a function with universe parameters is stated at those parameters, so that it
holds of every instance; the linter refuses a kind stated at other universe levels. A result
type that depends on the input in another way, such as an inductive family indexed by the input
or a subtype of `Bool`, has no kind: return `Decidable _`, or register an ordinary requirement.

Nested dependent pairs are not a form for three or more arguments. Each projection of a pair
carries the pair's type, so the elaborated statement grows by a large factor with each argument,
whichever way the pairs nest, and the linter does not read a field of a field as a field of the
structure. A structure declared for the arguments has projections of constant size.

None of the kinds says that `spec` is the intended specification, that every caller acts on the
verdict, or which value an accepting result carries. Those remain review.
-/

@[expose] public section

namespace Regula

universe u v w

/-- Required evidence about the exact implementation, not a similarly named model.
The linter recognizes closed declarations of this type as executable promises.
Use a named constant as `implementation`; put its complete domain inside `condition`.
Classical evidence is permitted under the selected Standard-Logical profile. -/
structure ExecutableContract {α : Type u} (implementation : α)
    (condition : α → Prop) : Prop where
  /-- A proof of `condition` about exactly `implementation`. -/
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

/-- A sound decision: `f` accepts only inputs that satisfy `spec`, and accepts at least one
input. `accepts` says which results are acceptances: `(· = true)` for a Boolean check,
`(·.isSome)` for a parser, `(· = none)` for a function that returns a failure.

**Not claimed:** completeness. `f` may refuse inputs that satisfy `spec`. Neither is it claimed
that `spec` is the intended specification, nor which value an accepting result carries. -/
structure DecidesSoundly {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  /-- Soundness: every input `f` accepts satisfies the specification. -/
  sound : ∀ x, accepts (f x) → spec x
  /-- `f` accepts some input. Without this the function that refuses every input would be
  sound for every specification. The witness is about `f`: a satisfiable `spec` alone does not
  exclude that function. -/
  accepted : ∃ x, accepts (f x)

/-- A complete decision: `f` accepts every input that satisfies `spec`, and refuses at least
one input. `accepts` says which results are acceptances, as for `DecidesSoundly`.

**Not claimed:** soundness. `f` may accept inputs that do not satisfy `spec`. Neither is it
claimed that `spec` is the intended specification, nor which value an accepting result
carries. -/
structure DecidesCompletely {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop where
  /-- Completeness: `f` accepts every input that satisfies the specification. -/
  complete : ∀ x, spec x → accepts (f x)
  /-- `f` refuses some input. Without this the function that accepts every input would be
  complete for every specification. -/
  refused : ∃ x, ¬ accepts (f x)

/-- A sound and complete decision: `f` accepts exactly the inputs that satisfy `spec`
(`Decides.iff`), and both outcomes occur, so `spec` is neither true of every input nor false of
every input (`DecidesSoundly.satisfiable`, `DecidesCompletely.refutable`).

**Not claimed:** that `spec` is the intended specification, that it is stated independently of
`f` in substance, or which value an accepting result carries. -/
structure Decides {α : Sort u} {ρ : Sort v} (accepts : ρ → Prop) (spec : α → Prop)
    (f : α → ρ) : Prop
    extends DecidesSoundly accepts spec f, DecidesCompletely accepts spec f

section
variable {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop} {f : α → ρ}

/-- The two directions of a `Decides` as one equivalence. -/
theorem Decides.iff (decides : Decides accepts spec f) (x : α) : accepts (f x) ↔ spec x :=
  ⟨decides.sound x, decides.complete x⟩

/-- A two-way theorem about `f` and one witness of each outcome give the two-way kind. -/
theorem Decides.of_iff (iff : ∀ x, accepts (f x) ↔ spec x) (accepted : ∃ x, accepts (f x))
    (refused : ∃ x, ¬ accepts (f x)) : Decides accepts spec f :=
  { sound := fun x => (iff x).mp, accepted, complete := fun x => (iff x).mpr, refused }

/-- A parser of a written form is a two-way decision of "is a written form": `parse` reads
every `write x` back as `x` and accepts nothing else, with one value and one input it refuses as
the witnesses. This is the shape of a closed vocabulary's spelling and parser. -/
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

/-- The specification of a sound decision is satisfiable: the accepted input satisfies it. -/
theorem DecidesSoundly.satisfiable (decides : DecidesSoundly accepts spec f) : ∃ x, spec x :=
  decides.accepted.elim fun x h => ⟨x, decides.sound x h⟩

/-- The specification of a complete decision is refutable: the refused input does not satisfy
it. -/
theorem DecidesCompletely.refutable (decides : DecidesCompletely accepts spec f) :
    ∃ x, ¬ spec x :=
  decides.refused.elim fun x h => ⟨x, fun holds => h (decides.complete x holds)⟩

/-- A function that refuses every input has no sound kind, whatever the specification: it has
no `accepted` witness. -/
theorem DecidesSoundly.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x)) :
    ¬ DecidesSoundly accepts spec f :=
  fun decides => decides.accepted.elim refuses

/-- A function that refuses every input is not complete for a satisfiable specification. -/
theorem DecidesCompletely.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x))
    (satisfiable : ∃ x, spec x) : ¬ DecidesCompletely accepts spec f :=
  fun decides => satisfiable.elim fun x holds => refuses x (decides.complete x holds)

/-- A function that accepts every input has no complete kind, whatever the specification: it
has no `refused` witness. -/
theorem DecidesCompletely.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x)) :
    ¬ DecidesCompletely accepts spec f :=
  fun decides => decides.refused.elim fun x h => h (acceptsAll x)

/-- A function that accepts every input is not sound for a refutable specification. -/
theorem DecidesSoundly.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x))
    (refutable : ∃ x, ¬ spec x) : ¬ DecidesSoundly accepts spec f :=
  fun decides => refutable.elim fun x fails => fails (decides.sound x (acceptsAll x))

end

/-- `Function.uncurry f` is `f` applied to the two fields of a pair, in order: a kind stated
through `Function.uncurry` is the kind stated about the fields of a structure, at the structure
`Prod`. -/
theorem uncurry_eq_fields {α : Type u} {β : Type v} {φ : Sort w} (f : α → β → φ) :
    Function.uncurry f = fun p => f p.1 p.2 := rfl

namespace Dependent

/-- A sound decision whose result type depends on its input: `f x` has type
`Result (payload x)`, one type former `Result` applied to a payload type that depends on `x`,
as `Except ε (Admitted x)` is `Except ε` applied to `Admitted x`. `f` accepts only inputs that
satisfy `spec`, and accepts at least one input.

`accepts` says which results are acceptances, for every payload type: `(·.isOk = true)` for an
`Except` result, `(·.isSome = true)` for an `Option` result. It is stated outside the scope of
the input, so it reads the result and the payload type and not the input the result was computed
from, and the witness stays a statement about `f`.

**Not claimed:** completeness. `f` may refuse inputs that satisfy `spec`. Neither is it claimed
that `spec` is the intended specification, nor which value an accepting result carries. -/
structure DecidesSoundly {α : Sort u} {payload : α → Sort v} {Result : Sort v → Sort w}
    (accepts : ∀ {τ : Sort v}, Result τ → Prop) (spec : α → Prop)
    (f : ∀ x, Result (payload x)) : Prop where
  /-- Soundness: every input `f` accepts satisfies the specification. -/
  sound : ∀ x, accepts (f x) → spec x
  /-- `f` accepts some input. Without this the function that refuses every input would be
  sound for every specification. -/
  accepted : ∃ x, accepts (f x)

/-- A complete decision whose result type depends on its input, as for
`Dependent.DecidesSoundly`: `f` accepts every input that satisfies `spec`, and refuses at least
one input.

**Not claimed:** soundness. `f` may accept inputs that do not satisfy `spec`. Neither is it
claimed that `spec` is the intended specification, nor which value an accepting result
carries. -/
structure DecidesCompletely {α : Sort u} {payload : α → Sort v} {Result : Sort v → Sort w}
    (accepts : ∀ {τ : Sort v}, Result τ → Prop) (spec : α → Prop)
    (f : ∀ x, Result (payload x)) : Prop where
  /-- Completeness: `f` accepts every input that satisfies the specification. -/
  complete : ∀ x, spec x → accepts (f x)
  /-- `f` refuses some input. Without this the function that accepts every input would be
  complete for every specification. -/
  refused : ∃ x, ¬ accepts (f x)

/-- A sound and complete decision whose result type depends on its input, as for
`Dependent.DecidesSoundly`: `f` accepts exactly the inputs that satisfy `spec`
(`Dependent.Decides.iff`), and both outcomes occur.

**Not claimed:** that `spec` is the intended specification, that it is stated independently of
`f` in substance, or which value an accepting result carries. -/
structure Decides {α : Sort u} {payload : α → Sort v} {Result : Sort v → Sort w}
    (accepts : ∀ {τ : Sort v}, Result τ → Prop) (spec : α → Prop)
    (f : ∀ x, Result (payload x)) : Prop
    extends DecidesSoundly @accepts spec f, DecidesCompletely @accepts spec f

section
variable {α : Sort u} {payload : α → Sort v} {Result : Sort v → Sort w}
  {accepts : ∀ {τ : Sort v}, Result τ → Prop} {spec : α → Prop} {f : ∀ x, Result (payload x)}

/-- The two directions of a `Dependent.Decides` as one equivalence. -/
theorem Decides.iff (decides : Decides @accepts spec f) (x : α) : accepts (f x) ↔ spec x :=
  ⟨decides.sound x, decides.complete x⟩

/-- A two-way theorem about `f` and one witness of each outcome give the two-way kind. -/
theorem Decides.of_iff (iff : ∀ x, accepts (f x) ↔ spec x) (accepted : ∃ x, accepts (f x))
    (refused : ∃ x, ¬ accepts (f x)) : Decides @accepts spec f :=
  { sound := fun x => (iff x).mp, accepted, complete := fun x => (iff x).mpr, refused }

/-- The specification of a sound decision is satisfiable: the accepted input satisfies it. -/
theorem DecidesSoundly.satisfiable (decides : DecidesSoundly @accepts spec f) : ∃ x, spec x :=
  decides.accepted.elim fun x h => ⟨x, decides.sound x h⟩

/-- The specification of a complete decision is refutable: the refused input does not satisfy
it. -/
theorem DecidesCompletely.refutable (decides : DecidesCompletely @accepts spec f) :
    ∃ x, ¬ spec x :=
  decides.refused.elim fun x h => ⟨x, fun holds => h (decides.complete x holds)⟩

/-- A function that refuses every input has no sound kind, whatever the specification. -/
theorem DecidesSoundly.not_of_refuses_all (refuses : ∀ x, ¬ accepts (f x)) :
    ¬ DecidesSoundly @accepts spec f :=
  fun decides => decides.accepted.elim refuses

/-- A function that accepts every input has no complete kind, whatever the specification. -/
theorem DecidesCompletely.not_of_accepts_all (acceptsAll : ∀ x, accepts (f x)) :
    ¬ DecidesCompletely @accepts spec f :=
  fun decides => decides.refused.elim fun x h => h (acceptsAll x)

end

section
variable {α : Sort u} {ρ : Sort w} {accepts : ρ → Prop} {spec : α → Prop} {f : α → ρ}

/-- `Regula.DecidesSoundly` is `Dependent.DecidesSoundly` at a result type that does not vary:
the result former ignores the payload type, whatever `payload` is. -/
theorem decidesSoundly_const (payload : α → Sort v) :
    DecidesSoundly (payload := payload) (Result := fun _ => ρ) (fun {_} => accepts) spec f ↔
      Regula.DecidesSoundly accepts spec f :=
  ⟨fun decides => ⟨decides.sound, decides.accepted⟩,
    fun decides => ⟨decides.sound, decides.accepted⟩⟩

/-- `Regula.DecidesCompletely` is `Dependent.DecidesCompletely` at a result type that does not
vary. -/
theorem decidesCompletely_const (payload : α → Sort v) :
    DecidesCompletely (payload := payload) (Result := fun _ => ρ) (fun {_} => accepts) spec f ↔
      Regula.DecidesCompletely accepts spec f :=
  ⟨fun decides => ⟨decides.complete, decides.refused⟩,
    fun decides => ⟨decides.complete, decides.refused⟩⟩

/-- `Regula.Decides` is `Dependent.Decides` at a result type that does not vary. -/
theorem decides_const (payload : α → Sort v) :
    Decides (payload := payload) (Result := fun _ => ρ) (fun {_} => accepts) spec f ↔
      Regula.Decides accepts spec f :=
  ⟨fun decides => ⟨(decidesSoundly_const payload).mp decides.toDecidesSoundly,
      (decidesCompletely_const payload).mp decides.toDecidesCompletely⟩,
    fun decides => ⟨(decidesSoundly_const payload).mpr decides.toDecidesSoundly,
      (decidesCompletely_const payload).mpr decides.toDecidesCompletely⟩⟩

end

end Dependent

end Regula
