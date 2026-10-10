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

The three kinds are the only kinds. Two forms bring under them a function with an argument whose
type depends on an earlier argument, with a type, instance or proof argument, or with a result
type that depends on its arguments. They can be used separately:

* **The fields of a structure.** State the kind about the function that applies `f` to every
  field of one structure, in the order of the fields: `fun input : Input => f input.a input.b
  input.c`, where `Input` is a structure whose fields are the arguments of `f`. The type of a
  field can depend on an earlier field, and a field can be a type, an instance or a proof. For
  two arguments the structure can be a pair (`Prod`, `Sigma`, `PSigma` or `Subtype`), and
  `Function.uncurry f` is this form at `Prod` (`uncurry_eq_fields`). The kind about that
  function is the kind about `f` when every tuple of arguments is the fields of some value
  (`Decides.of_packing` and its one-way forms). A type with one constructor and no index has
  that property: the constructor takes every tuple of fields to a value of the type, and Lean's
  kernel reduces each projection of that value to the field. The linter reads no other way of
  supplying the arguments as this form. A function that fixes an argument or gives a field twice
  decides `f` on part of its domain; a structure with a field that `f` does not take, such as a
  proof about the other fields, can restrict the domain; and a type with an index holds only
  the tuples whose fields compute that index.
* **An erasure of the result.** A result type that depends on the input is decided through one
  of two functions of this module, each of which forgets the part of the result whose type
  depends on the input: `Dependent.isSome f` for `f : ∀ x, Option (payload x)` and
  `Dependent.isOk f` for `f : ∀ x, Except (ε x) (payload x)`, both to `Bool`. The kind is one
  of the three above about the erased function, as in
  `Decides (· = true) spec (Dependent.isOk f)`, so the type of its acceptance predicate has no
  payload in it, and the predicate reads the erased result and nothing else. The linter reads
  these two erasures and no other, so a registration cannot supply an erasure of its own. An
  acceptance predicate or an erasure that is stated for every payload type can read the payload
  type: "the payload type has a value" is the specification of a proof-carrying payload,
  whatever the function returns.

A kind is stated about the function applied to every one of its arguments: the result type of
the function that is decided is not a function type. This restriction is structural, and it is
conservative. With an argument left, the result is a function, and how much of it the kind
constrains depends on the acceptance predicate. One that reads the result at one fixed value `b`
of that argument gives exactly the kind of the slice of the function at `b`
(`Decides.iff_slice`), which says nothing of the function at another value. One that quantifies
over that argument can constrain every value. The linter does not read the acceptance predicate:
it refuses every kind whose result type is a function type, a kind of the second form included,
in each form of the decided function (the function itself, `Function.uncurry` of it, and a
field application). The remedy is the same for both: supply the remaining argument, with one
more `Function.uncurry` (`packing_uncurry_covers`) or as a field of the structure.

A kind about a function with universe parameters is stated at those parameters, so that it
holds of every instance; the linter refuses a kind stated at other universe levels. A result
type whose dependency on the input neither erasure removes, such as an inductive family indexed
by the input, has no kind: return `Decidable _`, or register an ordinary requirement. A result
of a subtype type that depends on the input, `{r : ρ // P x r}`, is such a type until
https://github.com/rbeauchamp/regula/issues/243 is decided: an erasure that returns the value of
the subtype would keep a free acceptance predicate on a data value.

Nested dependent pairs are not a form for three or more arguments. Each projection of a pair
carries the pair's type, so the elaborated statement grows by a large factor with each argument,
whichever way the pairs nest, and the linter does not read a field of a field as a field of the
structure. A structure declared for the arguments has projections of constant size.

## Functions that the two sides share

A kind is a theorem about the present definitions. It compares `accepts (f x)` with `spec x`.
When `spec` and `f` both call a function, a change of that function changes the two sides
together. Each direction then holds or fails as its proof does, and a proof that goes through
the shared function on the two sides can stay valid although the meaning changed. So the kind
does not establish that the shared function is the intended one. The same holds of a function
that `spec` and `accepts` both call. The linter refuses a registration whose two sides share a
function of the first class below (rule RG1009), which it searches for at any depth of `spec`,
outside Lean's own library. It reads the definitions outside Lean's own library that `spec`
reaches and that `f` or `accepts` also reaches. It reads `accepts` as it reads `spec`: each is
a statement, and the value of a definition of a proposition that it names is read. It does not
enter the declaration of the input type of the kind from the input: it reads `spec` from its body
under its variable, and it does not follow a projection of a field of the input back to the input
type. `accepts` is read in the same way with the result type. So a test that only the declaration
of the input type names, such as a test that an invariant of a field of the input states, is not
shared through `spec`: a change of the test changes which inputs there are, on the two sides
together, and not the comparison at an input. The report names such a test apart, and no
registration is refused for it. A `spec` that names the input type in any other way, as
`∀ y : α` does, or that reads a field whose result type has such an invariant and is not the
input type, reads the declaration.
It reads the functions that the two sides share in two classes:

* **A function with a result of `Bool`, and a definition with a result of `BEq _`.** The
  registration is refused. A proposition takes its place in `spec`, with a theorem that
  connects the proposition to the function, or with a function that decides the proposition
  with `decide`.
* **Each other function**, such as an encoding, a measure or a state transition. No type tells
  a function that the specification is about from one that only prepares the input. The report
  names each such function where `spec` reaches it first, and no registration is refused for
  it.

Data and statements are not named. They are an inductive type with its constructors, its
recursor and its projection functions; a definition whose value is a type, a proposition or a
record of propositions; a proof; a definition with a result of `Decidable p`; and a constant
that is no function. A type `Decidable p` has at most one value, so a function that decides a
proposition of `spec` with `decide` uses the statement itself.

This is a search by name over definitions. A copy of a definition under a second name is a
different constant, and the search does not find it. A test with no name of its own, such as a
function abstraction inside a shared function, is not found either. For the first class the
search reads at any depth, also below a named function of the second class, so a registration
with none has none at any depth. For the second class the search stops at each named function,
so a function of that class that only a named function calls is not named.

None of the kinds says that `spec` is the intended specification, that `accepts` is the intended
reading of a result, that every caller acts on the verdict, or which value an accepting result
carries. Those remain review. A constant function has no two-way kind
(`Decides.not_of_constant`); a sound kind about one proves the specification of every input
(`DecidesSoundly.spec_of_constant`), and a complete kind about one refutes it of every input
(`DecidesCompletely.not_spec_of_constant`). But when the result of `f` determines its input, as
the result of the identity function does, an acceptance predicate can restate the
specification: `Decides spec spec id` holds of every specification that some input satisfies
and some input does not.
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

section
variable {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}

/-- A constant function has no two-way kind, whatever the acceptance predicate and the
specification: it accepts every input or refuses every input, and a two-way kind needs an input
of each outcome. -/
theorem Decides.not_of_constant (result : ρ) : ¬ Decides accepts spec (fun _ : α => result) :=
  fun decides => decides.accepted.elim fun _ accepted =>
    decides.refused.elim fun _ refused => refused accepted

/-- A constant function with a sound kind accepts every input, so the specification holds of
every input. -/
theorem DecidesSoundly.spec_of_constant {result : ρ}
    (decides : DecidesSoundly accepts spec (fun _ : α => result)) (x : α) : spec x :=
  decides.accepted.elim fun _ accepted => decides.sound x accepted

/-- A constant function with a complete kind refuses every input, so the specification holds of
no input. -/
theorem DecidesCompletely.not_spec_of_constant {result : ρ}
    (decides : DecidesCompletely accepts spec (fun _ : α => result)) (x : α) : ¬ spec x :=
  fun holds => decides.refused.elim fun _ refused => refused (decides.complete x holds)

end

section
variable {σ : Sort w} {α : Sort u} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
  {f : α → ρ} {fields : σ → α}

/-- A sound kind about `f` on a packing of its arguments is the sound kind about `f`, when every
argument is `fields s` for some packed value `s`. Without that hypothesis the packed kind says
nothing of an argument that no packed value has. -/
theorem DecidesSoundly.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : DecidesSoundly accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    DecidesSoundly accepts spec f :=
  { sound := fun x accepted => (covers x).elim fun s same =>
      same ▸ decides.sound s (same ▸ accepted)
    accepted := decides.accepted.elim fun s accepted => ⟨fields s, accepted⟩ }

/-- A complete kind about `f` on a packing of its arguments is the complete kind about `f`, when
every argument is `fields s` for some packed value `s`. -/
theorem DecidesCompletely.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : DecidesCompletely accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    DecidesCompletely accepts spec f :=
  { complete := fun x holds => (covers x).elim fun s same =>
      same ▸ decides.complete s (same ▸ holds)
    refused := decides.refused.elim fun s refused => ⟨fields s, refused⟩ }

/-- A two-way kind about `f` on a packing of its arguments is the two-way kind about `f`, when
every argument is `fields s` for some packed value `s`. This is the property a kind stated about
the fields of a structure relies on: for a type with one constructor and no index, the
constructor makes every tuple of fields the fields of a value.

The domain `α` is the type of the complete argument tuples of the function that is decided, and
`f` is that function applied to all of them. No hypothesis can say so: that a result type is not
a function type is not a proposition of Lean's logic. The linter refuses a kind about a function
with an argument left; when its acceptance predicate reads the result at one fixed value of that
argument, such a kind is the kind of one slice of the function (`Decides.iff_slice`). -/
theorem Decides.of_packing (covers : ∀ x, ∃ s, fields s = x)
    (decides : Decides accepts (fun s => spec (fields s)) (fun s => f (fields s))) :
    Decides accepts spec f :=
  { toDecidesSoundly := .of_packing covers decides.toDecidesSoundly
    toDecidesCompletely := .of_packing covers decides.toDecidesCompletely }

end

/-- `Function.uncurry f` is `f` applied to the two fields of a pair, in order: a kind stated
through `Function.uncurry` is the kind stated about the fields of a structure, at the structure
`Prod`. -/
theorem uncurry_eq_fields {α : Type u} {β : Type v} {φ : Sort w} (f : α → β → φ) :
    Function.uncurry f = fun p => f p.1 p.2 := rfl

/-- A packing under `Function.uncurry` reaches every pair of a packed part and a remaining
argument, when it reaches every packed part. So with `Decides.of_packing`, a kind about
`Function.uncurry (fun s => g (fields s))` is the kind of `Function.uncurry g`: an application of
`Function.uncurry` around a packing supplies the next argument of the function. -/
theorem packing_uncurry_covers {σ : Type u} {α : Type v} {β : Type w} {fields : σ → α}
    (covers : ∀ x, ∃ s, fields s = x) : ∀ p : α × β, ∃ q : σ × β, (fields q.1, q.2) = p :=
  fun p => (covers p.1).elim fun s packed => ⟨(s, p.2), by rw [packed]⟩

section
variable {α : Sort u} {β : Sort w} {ρ : Sort v} {accepts : ρ → Prop} {spec : α → Prop}
  {g : α → β → ρ}

/-- A sound kind about a function with an argument left, whose acceptance predicate reads the
function-valued result at one value `b` of that argument, is the sound kind of the slice of the
function at `b`, and of nothing else. -/
theorem DecidesSoundly.iff_slice (b : β) :
    DecidesSoundly (fun h : β → ρ => accepts (h b)) spec g ↔
      DecidesSoundly accepts spec (fun x => g x b) :=
  ⟨fun decides => ⟨decides.sound, decides.accepted⟩,
    fun decides => ⟨decides.sound, decides.accepted⟩⟩

/-- A complete kind about a function with an argument left, whose acceptance predicate reads the
function-valued result at one value `b` of that argument, is the complete kind of the slice of
the function at `b`, and of nothing else. -/
theorem DecidesCompletely.iff_slice (b : β) :
    DecidesCompletely (fun h : β → ρ => accepts (h b)) spec g ↔
      DecidesCompletely accepts spec (fun x => g x b) :=
  ⟨fun decides => ⟨decides.complete, decides.refused⟩,
    fun decides => ⟨decides.complete, decides.refused⟩⟩

/-- A two-way kind about a function with an argument left, whose acceptance predicate reads the
function-valued result at one value `b` of that argument, is the two-way kind of the slice of
the function at `b`. It holds of every function with that slice, so it says nothing of `g` at
another value of the argument. The hypothesis is on the acceptance predicate: one that
quantifies over the argument, such as `fun h => ∀ b, accepts (h b)`, is not of this form and can
constrain `g` at every value. The linter does not read the acceptance predicate and refuses
every kind whose result type is a function type, which is a conservative restriction; the
remedy is to state the kind about the function applied to every argument. -/
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

/-- Whether an optional result holds a payload, with the payload forgotten:
`isSome f x = (f x).isSome`. The payload type can depend on the input; the type of the erased
function does not, so a decision kind about `isSome f` has an acceptance predicate of `Bool`. -/
def isSome {α : Sort u} {payload : α → Type v} (f : ∀ x, Option (payload x)) (x : α) : Bool :=
  (f x).isSome

/-- Whether a result is a success, with the payload and the error forgotten:
`isOk f x = (f x).isOk`. The payload type and the error type can depend on the input; the type
of the erased function does not. -/
def isOk {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    (f : ∀ x, Except (ε x) (payload x)) (x : α) : Bool :=
  (f x).isOk

/-- The erased result of `isSome` is `true` exactly when the result holds a payload. -/
theorem isSome_eq_true_iff {α : Sort u} {payload : α → Type v} (f : ∀ x, Option (payload x))
    (x : α) : isSome f x = true ↔ ∃ value, f x = some value := by
  unfold isSome
  cases f x with
  | none => exact ⟨fun holds => absurd holds Bool.false_ne_true, fun ⟨_, same⟩ => nomatch same⟩
  | some value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

/-- The erased result of `isOk` is `true` exactly when the result is a success with a payload. -/
theorem isOk_eq_true_iff {α : Sort u} {ε : α → Type v} {payload : α → Type w}
    (f : ∀ x, Except (ε x) (payload x)) (x : α) : isOk f x = true ↔ ∃ value, f x = .ok value := by
  unfold isOk
  cases f x with
  | error _ => exact ⟨fun holds => absurd holds Bool.false_ne_true, fun ⟨_, same⟩ => nomatch same⟩
  | ok value => exact ⟨fun _ => ⟨value, rfl⟩, fun _ => rfl⟩

end Dependent

end Regula
