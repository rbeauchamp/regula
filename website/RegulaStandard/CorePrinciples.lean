import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "1. Core Principles" =>
%%%
tag := "1-core-principles"
file := "1-core-principles"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "1-overview"
number := false
%%%

This section states the required principles for mathematical proofs and verified functional programs in Lean.

State Lean theorems precisely for mathematical objects and executable definitions. Each claim MUST remain within the scope and strength of its supporting type, proof-bearing construction, or theorem.

# 1.1 The Principle of Representational Precision
%%%
tag := "11-the-principle-of-representational-precision"
number := false
%%%

*Principle*: Distinguish a unary invariant `I : S → Prop` of every admitted value from a relation over transitions, reachable states, histories, or resource use. Proof-bearing immutable types SHOULD be the default for admitted domain values. State exactly which values the type excludes and which relations need separate proofs.

*Rationale*: A proof field makes an invariant part of the value. A computable, proof-producing validator inspects raw input at runtime and, on success, returns a value carrying the invariant’s proof. The decision is input-dependent, but Lean checks universally that each successful branch establishes the invariant. An unchecked Boolean or a comment alone supplies no such evidence. Proof fields provide evidence for Lean’s type checker and are erased during compilation. Runtime validation still performs the computation needed to decide whether to admit an input.

*Requirements*:

* Every semantic distinction that the development claims Lean prevents from being confused MUST be encoded as a distinct type, constructor, or refined type.
* A claimed intrinsic invariant MUST be enforced by the type itself. Raw inputs MUST be distinguished from admitted values; constructors, parsers, loads, and every write/update boundary MUST establish the invariant relied on downstream.
* A raw internal representation MAY be used with a documented Lean-specific rationale, provided admission establishes the invariant and every write preserves it. Its exact initialization and preservation theorems MUST compose over the stated reachable states or traces. A consumer requiring the invariant MUST require its proof or obtain it from that verified reachability argument; an arbitrary raw value is not an admitted value.
* Transition, history, and resource-use claims MUST state and prove the exact property claimed. Claims established by induction over executions MUST include the required initialization and preservation proofs; claims about composition MUST establish the corresponding composition property. A conditional preservation lemma may assume a valid input; it alone establishes neither admission nor reachability. An immutable valid value can be copied: latest-state or single-use claims require proofs about the actual transition/trace semantics, not merely a state proof field.
* When an API claims construction is restricted to named smart constructors, the underlying constructor MUST be inaccessible at that boundary. A public proof-bearing structure enforces its fields but permits any construction that supplies the required proofs.
* Runtime decoding MAY produce a typed, proof-bearing result. A distinction claimed to be enforced by Lean MUST NOT depend only on untyped parsing or an unproved Boolean check.
* No `sorry`, `admit`, use of `sorryAx`, or project logical `axiom` declarations may occur in a conforming proof surface. Domain assumptions are parameters, hypotheses, or proof-bearing fields. Foundation strength is separately reported ({ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5]).

Prefer raw boundary data, then proof-producing admission, then immutable domain values, then total pure transformations, then explicit effect interpretation. Local `let mut` and efficient array operations can denote total pure Lean functions. Judge the elaborated semantics and proved boundary, not the syntax ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6]).

*Example - Smart Constructor Pattern*:

```lean
import Mathlib.Basic.NNReal.Defs

/-- A resource whose capacity is non-negative. The proof of the invariant is
    carried by Mathlib's canonical `NNReal` subtype. The outer structure keeps
    the domain concept nominally distinct. -/
structure Resource where
  capacity : NNReal

/-- Smart constructor: callers cannot build a `Resource` without the proof. -/
def mkResource (c : ℝ) (h : 0 ≤ c) : Resource := ⟨NNReal.mk c h⟩

/-- Accessor returning the canonical value-and-proof subtype. -/
def Resource.capacityWithProof (r : Resource) : NNReal := r.capacity
```

A direct construction cannot bypass the obligation. The anonymous-constructor form fails when the proof field is missing:

```lean (fails := "Insufficient number of fields|failed to synthesize")
import Mathlib.Basic.NNReal.Defs

structure Resource where
  capacity : NNReal

def bad : Resource := ⟨⟨(-1 : ℝ)⟩⟩
```

*Boundary decoding* can establish a statically usable invariant. The computable {repo "lean/Audit/Server.lean"}[`Glossary.Server.validate`] checks raw natural counts and returns `Option Server`; every returned state carries `served ≤ cap`. This is dynamic admission, not a claim that the input-dependent decision happened at compile time.

```lean
import Audit.Server
open Glossary

/-- On success, downstream code receives the bound as an ordinary Lean proof. -/
example (served cap : Nat) :
    ∀ s, Server.validate served cap = some s → s.served ≤ s.cap :=
  fun s _ => s.bounded

/-- The validator rejects exactly invalid inputs; it cannot silently reject valid ones. -/
example (served cap : Nat) :
    Server.validate served cap = none ↔ ¬ served ≤ cap :=
  Server.validate_none served cap

/-- Accepted fields are exactly the raw input, not substituted valid defaults. -/
example (served cap : Nat) (s : Server) (h : Server.validate served cap = some s) :
    s.served = served ∧ s.cap = cap := Server.validate_some h
```

Internally, pass the admitted value itself. Use `Option` when a new operation can fail and failure needs no diagnostic information; carrying `Server` avoids repeating validation of an already-proved bound. A constructor may accept a proof of a predicate even when no executable decision procedure for that predicate is available. For example, constructing an `NNReal` from a real number and a supplied non-negativity proof does not require deciding real non-negativity ({ref "324-decidability-logical-vs-executable"}[module 3 §3.2.4]).

# 1.2 Theorem-Backed Claims
%%%
tag := "12-theorem-backed-claims"
number := false
%%%

*Principle*: Every material property presented as established for a Lean definition MUST be stated by an exact theorem or carried by its type. The standard constrains the checked result, not the chronological order in which a developer writes it.

*Rationale*: Machine-checked guarantees require mathematical proof. A theorem-backed interface lets Lean check that a definition has the stated property; prose or workflow history cannot. Elaboration and tactics construct the definitions and proof terms that Lean’s kernel checks. The guarantee concerns the resulting formal statement and its dependencies, so review must also establish that this statement expresses the intended claim.

*Requirements*:

* Every function’s preconditions, postconditions, and invariants that matter to the claimed guarantee MUST be expressed in its type or in supporting Lean theorems.
* Recursive definitions on the conforming surface MUST have checked termination evidence. Authored partial and unsafe declarations are excluded; authenticated generated helpers follow {ref "84-inventory-every-owned-declaration"}[module 8 §8.4]. A contract for a potentially non-terminating execution is stated over finite prefixes or as partial correctness, not by admitting authored partiality ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6]).
* Proofs SHOULD be structured for human readability:
  * Complex proofs SHOULD be decomposed into well-named lemmas when that makes the argument easier to inspect
  * Each proof step MAY include a comment where the reasoning is not apparent from the tactics themselves ({ref "54-proof-readability"}[module 5 §5.4])

*Example - A Theorem-Backed Definition*:

```lean
import Mathlib.Analysis.SpecialFunctions.Exp  -- `Real.exp`
import Mathlib.Order.Monotone.Basic

/-- Specification: a function that is monotone and non-negative -/
structure GrowthFunction where
  func : ℝ → ℝ
  property : Monotone func ∧ ∀ t, 0 ≤ func t

/-- State the theorem that the intended implementation has the property.
    This can be a private lemma used to construct the final object. -/
private theorem exponentialGrowth_has_property (rate : ℝ) (h : 0 < rate) :
    Monotone (fun t => Real.exp (rate * t)) ∧ ∀ t, 0 ≤ Real.exp (rate * t) := by
  constructor
  · intro t₁ t₂ ht
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (le_of_lt h))
  · intro t
    exact le_of_lt (Real.exp_pos _)

/-- Implement a function that RETURNS the function AND its proof, bundled.
    The return type `GrowthFunction` guarantees the properties. -/
noncomputable def makeGrowingResource (rate : ℝ) (h : 0 < rate) : GrowthFunction :=
  ⟨fun t => Real.exp (rate * t), exponentialGrowth_has_property rate h⟩
```

If this definition claims to return a monotone, non-negative function, omitting the proof-bearing field or an equivalent theorem leaves the claim unverified. The bundled form encodes monotonicity and non-negativity in the return type.

# 1.3 The Specification/Model Firewall
%%%
tag := "13-the-specificationmodel-firewall"
number := false
%%%

*Principle*: A conforming development makes claims of distinct kinds, each exact about the Lean object it covers. A development may combine these claim kinds while keeping their scopes distinct. All kinds share the same no-holes and honest-claim requirements; none is a weaker tier of correctness.

*The claim kinds*:

1. *Abstract mathematical claims* — theorems about models built from mathematical types (ℝ, ℕ, `Set α`, Mathlib structures), with exact quantifiers and reported foundations. Their strength is unchanged by anything below.
2. *Executable Lean definition claims* — contracts about actual computable definitions: total functions, machine arithmetic, arrays and byte buffers, parsers, state transformers, monadic code, `IO` programs. Proof-bearing executable Lean is a first-class default, not an exception ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6]).
3. *Refinement/correspondence claims* — when an abstract model is used and a claim is transferred to an executable definition, the transfer is itself a proved Lean theorem relating model and executable under stated hypotheses ({ref "24-abstract-mathematical-models"}[module 2 §2.4]).
4. *External/effectful boundary claims* — at `@[extern]`/FFI, runtime-replacement, and external-world boundaries, the claim states exactly what is proved and what remains trusted ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6], {ref "86-classify-lean-computation-mechanisms-exactly"}[module 8 §8.6]).

*Rationale*: A theorem about a pure Lean model establishes properties of that model under its stated hypotheses. It does not establish that a separate implementation satisfies those properties. To transfer a result to an executable Lean definition, provide a checked theorem relating the two. Use concrete types such as machine integers when their semantics are the subject of the claim.

*Requirements*:

* A definition presented as a pure mathematical function MUST elaborate as a safe Lean definition with that exact functional meaning. Pure encodings such as `StateM`, `ReaderT`, and `Except` remain ordinary Lean functions and are permitted when their state, environment, or error result is part of the model.
* Concrete representations — finite machine integers, bitvectors, floating point, arrays, byte buffers, parsers, state transformers — are permitted specification objects when _they_ are the object of the claim. The specification MUST then state the exact representation semantics the claim relies on: overflow and wrapping, rounding, exceptional values, serialization, where applicable ({ref "41-numeric-representations-mathematical-and-machine-arithmetic"}[module 4 §4.1]).
* The representation MUST match the claim. A theorem over `ℝ` supports a claim about `Float` or `UInt32` computation only through a checked relation sufficient to transfer the claimed property ({ref "24-abstract-mathematical-models"}[module 2 §2.4]).
* Claims involving `IO`, `@[extern]`, runtime replacements, or other external-effect mechanisms MUST distinguish the logical Lean object from its runtime interpretation and name what is proved versus what remains trusted ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6]). Where a mechanism retains a pure Lean reference definition, theorems may concern that definition. Its proof alone MUST NOT be presented as proof of replacement or external execution behavior; transferring a formal property requires sufficient checked correspondence, with remaining execution trust explicit (module 8 §8.6).
* External adapter or bridge code whose behavior has no checked Lean correspondence MUST remain outside the proved model, in separate implementation modules that abstract specification modules do not import. Model compilation does not validate the adapter or certify an external system.
* A Lean abstraction map or relation with a checked transfer theorem belongs *inside the formal development*. It MAY import the concrete Lean definitions it relates. State its exact initialization, simulation, observation, and invariant-transfer obligations ({ref "39-stateful-refinement-and-finite-prefix-safety"}[module 3 §3.9]); this does not turn external adapters or native execution into proved Lean behavior.

*Example - Correspondence Under an Explicit Hypothesis*:

The following theorem relates Lean’s `UInt32` addition to natural-number addition. The no-overflow hypothesis is required for this equality:

```lean
import Mathlib.Data.Nat.Basic

example (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]
```

Without the hypothesis, the machine sum can wrap while the natural-number sum does not. This is a correspondence between Lean definitions; it does not independently verify compiled execution. {ref "24-abstract-mathematical-models"}[Module 2 §2.4] gives the expanded example and an overflow counterexample.

An abstraction boundary is a separate claim: an opaque package can hide a concrete representation while exporting selected operations. Its guarantee is limited to the operations and reduction behavior that Lean exposes. The complete example and forbidden construction/observation checks appear in {ref "651-opaque-packages"}[module 6 §6.5.1].

*Anti-Pattern - Claim/Type Mismatch*: Valid Lean may still carry the wrong contract. This is a review example, not a promised Lean diagnostic.

```lean
-- ANTI-PATTERN: the prose claims an exact real-valued sum of resources, but the
-- definition computes a Float fold whose result depends on evaluation order and
-- rounding. The defect is the unproved identification, not the use of Float.
-- A claim about this function must state Float semantics (module 4 §4.1).
def efficientResourceSum (resources : Array Float) : Float := Id.run do
  let mut sum := 0.0
  for r in resources do
    sum := sum + r
  return sum
```

# 1.4 Principled Mathematical Modeling
%%%
tag := "14-principled-mathematical-modeling"
number := false
%%%

*Principle*: Mathematical concepts MUST use or extend Mathlib's canonical definitions where they fit the intended concept. Custom definitions require documented justification.

*Rationale*: Mathlib provides mathematical structures with an extensive library of theorems. Reusing its definitions allows direct application of those theorems. A separate definition may require additional proofs connecting it to Mathlib's definitions.

*Requirements*:

* Mathematical concepts MUST use or extend applicable canonical Mathlib definitions, including:
  * Groups, rings, fields from `Mathlib.Algebra`
  * Orders and lattices from `Mathlib.Order`
  * Topological structures from `Mathlib.Topology`
  * Measure theory from `Mathlib.MeasureTheory`
* Every law or property claimed for an instance MUST be supported by a proof. Generic declarations MAY require these proofs as explicit hypotheses or proof-bearing fields.
* The choice of mathematical structure MUST be justified. State why the abstraction fits the intended claim, which theorems it makes available, and which constraints it enforces.
* Model time with the structure your claim needs. Continuous ℝ-based time and discrete `ℕ`-based clocks are both conforming choices when they are lawful Mathlib structures; what is not conforming is an order instance that does not supply the laws the prose claims ({ref "41-numeric-representations-mathematical-and-machine-arithmetic"}[module 4 §4.1]).
* Laws may be supplied by a `Prop`-valued lawful mixin over an operational class, as Mathlib and Core do; a generic lawful claim then requires the mixin directly or obtains its instance from stronger assumptions, and every mixin instance discharges every law ({ref "323-typeclasses-for-lawful-abstractions"}[module 3 §3.2.3]).
* A custom mathematical definition is permissible when no Mathlib equivalent exists. The module introducing it MUST state the definition precisely and explain why no existing one fits. Most domain definitions do not belong in Mathlib. The defect to avoid is accidental re-derivation of an existing definition, not ownership of a domain concept.

*Example - Leveraging Mathlib* (the ordered-additive interface used here separates `AddCommMonoid` and `Preorder` from the `Prop`-valued `IsOrderedAddMonoid` mixin):

```lean
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Basic.NNReal.Defs

/-- Pure composition reuses Mathlib's lawful `Monoid` interface and `List.prod`;
    there is no duplicate hand-written associativity/identity structure. -/
def totalResources {R : Type*} [Monoid R] (resources : List R) : R :=
  resources.prod

/-- A domain operation requires Mathlib's lawful interface directly; no
    one-field wrapper class duplicates the hierarchy. -/
def combineResources {R : Type*} [AddCommMonoid R] [Preorder R]
    [IsOrderedAddMonoid R] (a b : R) : R := a + b

/-- Mathlib already supplies the ordered-additive laws for NNReal. -/
example : IsOrderedAddMonoid NNReal := inferInstance

/-- The point of reuse: Mathlib's theorems apply to the wrapped concept. -/
example (a b c : NNReal) (h : a ≤ b) : a + c ≤ b + c := add_le_add_left h c
```

*Anti-Pattern - An Inadequate Group Interface*: This structure declares a binary operation and an identity candidate, but no inverse operation or group laws. It does not specify a group. Use Mathlib’s `Group` interface when a group is intended; even a complete custom group definition would require justification for duplicating that interface.

```lean
structure MyGroup where
  carrier : Type
  op : carrier → carrier → carrier
  id : carrier
  -- The inverse operation and proofs of the group laws are missing.
```

# 1.5 Explicit Parameters
%%%
tag := "15-explicit-parameters"
number := false
%%%

*Principle*: When prose presents a value as a fixed normative parameter of the Lean development, the development MUST expose that value as a named definition or proof-bearing field with a precise type; that type MUST carry any claimed constraints.

*Rationale*: A constraint that lives only in a comment can be violated silently. A proof-bearing parameter type requires evidence of the constraint when the parameter is constructed and makes that evidence available to its consumers.

*Requirements*:

* Normative parameters MUST be exposed as named definitions or proof-bearing fields with documentation stating what the value means, its encoded constraints, and any exact Lean theorem hypotheses or conclusions that depend on that value. Broader operational or organizational change-impact analysis is outside this standard.
* Parameter constraints MUST be proof-carrying: encode `{q : ℚ // 0 < q ∧ q < 1}`, not "q is a ratio between 0 and 1" in prose.
* Every unit or parameter-role distinction claimed to prevent cross-use MUST be enforced by the interface's distinct types, indices, or refinements ({ref "23-phantom-types-for-disambiguation"}[module 2 §2.3]).

*Example - Proof-Carrying Parameters*:

```lean
import Mathlib.Tactic.NormNum

/-- A quorum ratio: the type excludes 0, 1, and every value outside the unit
    interval, by proof. Changing the value is a one-line change; silently
    changing it to an invalid one is an elaboration error. -/
def minimumQuorum : {q : ℚ // 0 < q ∧ q < 1} := ⟨2/3, by norm_num⟩

/-- The parameter is usable as an ordinary rational everywhere. -/
example : (minimumQuorum : ℚ) = 2/3 := rfl
```

# 1.6 Claim Boundaries and Automated Checking
%%%
tag := "16-claim-boundaries-and-automated-checking"
number := false
%%%

*Principle*: No prose claim may be stronger than its supporting Lean type, proof-bearing construction, or theorem. Tools MUST check the mechanical part of conformance.

*Requirements*:

* A model theorem applies to the model. Transferring its result to another formal representation requires a checked theorem establishing the required relation. Claims about compiled artifacts or external systems MUST distinguish this formal correspondence from the compiler, runtime, and external-world assumptions needed to connect it to execution ({ref "36-contracts-for-executable-and-effectful-mechanisms"}[module 3 §3.6]). A Lean proof alone does not establish those external assumptions.
* A theorem about totalized operations (e.g., division that returns 0 on a zero divisor) is not a claim that domain errors are impossible; if a domain must exclude zero, the API type encodes the exclusion ({ref "321-totality-termination-and-totalized-operations"}[module 3 §3.2.1]).
* Checked structural or well-founded recursion establishes totality in Lean's logic; it does not establish compiled termination, a complexity bound, or a deployed system's security property.
* Conformance projects obtain the current-surface evidence required by {ref "8-tooling-and-machine-audit"}[module 8]: fresh warning-free root-package elaboration and checked declaration admission, declaration and foundation inspection over every owned module, and checked documentation examples. Checker implementations require qualification for their advertised behavior under {ref "88-qualify-checker-implementations-with-independent-mutations"}[§8.8]; valid evidence for unchanged supported inputs may be reused but does not replace current-surface inspection.

*Example - The exact claim of a composition theorem* ({ref "31-what-must-be-proven"}[module 3 §3.1] shows the full development):

```text
Given:  structure SystemState with invariant field  inv : activeProposals ≤ participants
Lean theorem:
  compose_preserves_safety (f g : SystemState → SystemState) :
      ∀ s, ((f ∘ g) s).activeProposals ≤ ((f ∘ g) s).participants
Exactly what it says: values of SystemState satisfy the invariant; composition of any
functions on them preserves it.
What it does NOT say: that any external system's states satisfy anything, that the model
is faithful to one, or that compiled executions of f and g terminate or are efficient.
The functions are total in Lean's logic; that is distinct from compiled execution.
```

# Summary of Section 1: Core Principles
%%%
tag := "summary-of-section-1-core-principles"
number := false
%%%

1. *Representational precision* — prefer proof-bearing admitted values; justified raw representations require verified admission and writes, and relational claims need proofs; `sorry`, `admit`, and project axioms are banned from conforming proof surfaces.
2. *Theorem-backed claims* — every material behavior claim presented as established is carried by a type or an exact Lean theorem, independent of authoring order.
3. *The specification/model firewall* — distinguish abstract, executable, refinement, and boundary claims. Transfers between formal representations require checked theorems; claims about external execution also retain explicit trust assumptions. Unproved external adapters remain outside the proved model.
4. *Mathlib reuse* — canonical definitions with full theorem corpora; custom definitions documented against the alternative.
5. *Explicit parameters* — named definitions or proof-bearing fields whose types carry the claimed constraints.
6. *Exact claim boundaries* — every claim within the scope and strength of its supporting Lean type, proof-bearing construction, or theorem; current-surface checks use applicable qualification for the checker's exact supported behavior.
