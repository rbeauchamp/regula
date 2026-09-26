import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "4. Mathematical Foundations" =>
%%%
tag := "4-mathematical-foundations"
file := "4-mathematical-foundations"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "4-overview"
number := false
%%%

Reuse Lean and Mathlib structures whose laws match the mathematical objects or executable program contracts being specified. State the exact foundation strength as described in §4.5.

# 4.1 Numeric Representations: Mathematical and Machine Arithmetic
%%%
tag := "41-numeric-representations-mathematical-and-machine-arithmetic"
number := false
%%%

*Requirement*: Use a numeric representation whose semantics match the claim. For example, `ℝ` provides exact real arithmetic, while `Float`, `UInt32`, and `BitVec n` have different arithmetic semantics. A claim relating different representations MUST state and prove the correspondence under its required hypotheses.

*Rationale*: `ℝ` provides exact real-number semantics. Floating-point arithmetic rounds and includes exceptional values such as `NaN` and infinities. Unsigned addition and multiplication on `n` bits wrap modulo `2 ^ n`. A theorem about real arithmetic does not establish the behavior of an unrelated machine computation. Checked correspondence connects the two when the claim needs both ({ref "24-abstract-mathematical-models"}[module 2 §2.4]).

*Implementation Guidelines*:

* Import `Mathlib.Basic.Real.Basic` when the model uses real numbers.
* Use `ℝ` when the claim treats time, probability, or another quantity as real-valued. Use the corresponding refined type when bounds are required.
* Use floating-point and fixed-width machine types when the claim is about that arithmetic, and name the semantics the claim relies on: rounding and exceptional values for `Float`; wrapping and bit width for machine words and `BitVec`; serialization when values cross a byte boundary.
* Specify an executable representation directly when its behavior is the subject of the claim. Transfer an abstract model’s result through checked correspondence to the actual implementation ({ref "13-the-specificationmodel-firewall"}[module 1 §1.3]).
* Discrete models, such as `ℕ`-based clocks and `Fin n` phases, also conform when they fit the claim. Supply the laws of every claimed mathematical interface.

*Example - Continuous Quantities with a Lawful Order*:

The shared `Time` type wraps non-negative real numbers. In {repo "lean/Audit/DocClaims.lean"}[`Audit.DocClaims`], `DecayingValue.valueAt` is `initial * exp (decayRate * (t - startTime))`, using the underlying real values of the times. The theorem below establishes a nonincreasing curve for a negative rate. It does not establish strict decrease because `initial` may be zero. Its quantifiers include all ordered pairs of times, including times before `startTime`. That field shifts the formula rather than restricting its domain.

```lean
import Audit.DocClaims
open Glossary

/- `Time` is a nominal wrapper around `NNReal`; `ResourceAmount` reuses
   `NNReal` directly. The wrapper has the complete lawful order claimed here. -/
noncomputable example : LinearOrder Time := inferInstance
example (t : Time) : 0 ≤ t.val := t.val.property

/- This alias exposes the exact theorem checked in `Audit.DocClaims`: for every
   curve with a negative rate and every ordered pair of nominal times, the
   later reference value is no greater than the earlier reference value. -/
theorem documented_decay_monotone (v : DecayingValue) (h : v.decayRate < 0) :
    ∀ t₁ t₂ : Time, t₁ ≤ t₂ → v.valueAt t₂ ≤ v.valueAt t₁ := by
  exact decay_monotone v h

/- The displayed hypotheses are jointly satisfiable; this is not a claim of
   reachability in an external system. -/
theorem documented_decay_nonvacuous :
    ∃ (v : DecayingValue) (t₁ t₂ : Time), v.decayRate < 0 ∧ t₁ ≤ t₂ :=
  decay_monotone_nonvacuous
```

An `LE` instance supplies a relation used by `≤`. It provides no proofs of reflexivity, transitivity, antisymmetry, or totality, and does not provide `min` or `max`. Even when its relation has those properties, the stronger interface requires their evidence. The bare relation below therefore does not synthesize `LinearOrder`:

```lean (fails := "(?s)failed to synthesize.*LinearOrder")
import Mathlib.Basic.Real.Basic

structure T where
  val : Real
  nonneg : 0 ≤ val

instance : LE T := ⟨fun x y => x.val ≤ y.val⟩

-- A bare relation does not synthesize the lawful bundled structure:
#synth LinearOrder T
```

If the prose claims that time has a linear order, supply the corresponding `LinearOrder` instance as the shared `Glossary.Time` does in {repo "lean/Audit/DocPrelude.lean"}[`Audit.DocPrelude`].

*Example - Machine Arithmetic as the Specification Object*:

When the claim is about the machine arithmetic itself, the specification uses the machine type and carries its exact semantics:

```lean
/-- Admission of a machine-float sensor reading. The exact semantics are in
    the result: the accepted branch carries proofs excluding the exceptional
    values `NaN` and ±∞, and the rejected branches are named. -/
def admitReading (x : Float) : Except String {v : Float // ¬v.isNaN ∧ ¬v.isInf} :=
  if h : x.isNaN then .error "NaN is not a reading"
  else if h₂ : x.isInf then .error "an infinite value is not a reading"
  else .ok ⟨x, h, h₂⟩

/-- Every non-exceptional input is accepted unchanged. -/
theorem admitReading_accepts (x : Float) (h : ¬x.isNaN ∧ ¬x.isInf) :
    admitReading x = .ok ⟨x, h⟩ := by
  simp [admitReading, h.1, h.2]
```

The specification uses `Float` because the claim concerns binary64 values. Its return type excludes `NaN` and infinities. `admitReading_accepts` additionally establishes acceptance and preservation of every input satisfying those conditions. These properties do not establish sensor accuracy or a permitted measurement range.

On the pinned toolchain, `Float` wraps a logical `Float.Model`. `isNaN` and `isInf` have definitions over that model. Compiled calls use native implementations through `@[extern]`. The proof does not verify those external implementations. A real-valued interpretation of accepted readings requires the stated correspondence ({ref "24-abstract-mathematical-models"}[module 2 §2.4]).

# 4.2 Algebraic Structures
%%%
tag := "42-algebraic-structures"
number := false
%%%

*Requirement*: Reuse the matching Lean or Mathlib algebraic structure when it expresses the intended interface. Introduce a custom structure only when existing interfaces do not fit, and explain the distinction. Its claimed laws still require proofs.

*Rationale*: The reuse principle of {ref "14-principled-mathematical-modeling"}[module 1 §1.4], applied to algebra: a standard structure carries its theorem library and integrates with the rest of Mathlib.

*Key Structures from Mathlib*:

* Groups: `AddGroup`, `AddCommGroup`, `Group`, `CommGroup`.
* Rings: `Semiring`, `Ring`, `CommRing`.
* Orders: `PartialOrder`, `LinearOrder`, `Lattice`.
* On the pinned Mathlib, the following ordered-algebra interfaces combine operational classes with proof-valued mixins: `AddCommGroup`, `PartialOrder` (or `LinearOrder`), and `IsOrderedAddMonoid` for ordered additive commutative groups; `Field`, `LinearOrder`, and `IsStrictOrderedRing` for linearly ordered fields. The former bundled names `OrderedAddCommGroup` and `LinearOrderedField` are absent on this pin. This describes those interfaces, not a ban on bundled hierarchies.

*Example - Canonical Orders Without Rebuilding Them*:

```lean
import Mathlib.Order.Basic
import Mathlib.Order.Lattice.Nat

/-- Named levels obtain an order by an injective rank into `ℕ`.
    `LinearOrder.lift'` transports the existing order and its laws. -/
inductive ConsensusLevel
  | none | weak | moderate | strong | unanimous
  deriving DecidableEq

/-- Index each level into the canonical natural order. -/
def ConsensusLevel.rank : ConsensusLevel → Nat
  | .none => 0 | .weak => 1 | .moderate => 2 | .strong => 3 | .unanimous => 4

instance : LinearOrder ConsensusLevel :=
  LinearOrder.lift' ConsensusLevel.rank (by
    intro a b h
    cases a <;> cases b <;> simp_all [ConsensusLevel.rank])

example : LinearOrder ConsensusLevel := inferInstance

/-- When named constructors aren't needed at all, an abbreviation inherits
    everything outright — no new structure, zero proofs. -/
abbrev Priority := Fin 5
example : LinearOrder Priority := inferInstance
```

The rank function chooses the intended ordering. The injection proof shows that distinct constructors receive distinct ranks. The imports above do not provide a `deriving LinearOrder` handler:

```lean (fails := "(?s)deriving.*LinearOrder")
import Mathlib.Order.Basic
import Mathlib.Order.Lattice.Nat

inductive Level
  | low | high
  deriving LinearOrder
```

# 4.3 Temporal Models
%%%
tag := "43-temporal-models"
number := false
%%%

*Principle*: Model time with the structure the claim needs — and provide the lawful structure the prose claims.

Discrete and continuous models are both conforming, as long as the order (or other) interface is complete and lawful:

```lean
import Mathlib.Order.Interval.Set.Basic
import Audit.DocPrelude
open Glossary

/- This fence uses the shared `Time` type (§4.1): non-negative reals
   with its lawful `LinearOrder`, shipped by the glossary. -/

/-- Events in the system (`Id`: §2.3, `Time`: §4.1, `OpaqueData`: module 6 §6.5.1) -/
structure Event where
  id : Glossary.Id EventTag
  timestamp : Time
  content : OpaqueData

/-- Temporal ordering of events, lifted from timestamps.
    (`Preorder.lift` needs a `Preorder` on the target; Time's `LinearOrder`
    supplies that weaker instance.) -/
noncomputable instance : Preorder Event :=
  Preorder.lift (fun e : Event => e.timestamp)

noncomputable example : Preorder Event := inferInstance

/-- A time window with validity proof -/
structure TimeWindow where
  start : Time
  finish : Time
  valid : start ≤ finish

/-- Check if a time is within the window -/
def TimeWindow.contains (w : TimeWindow) (t : Time) : Prop :=
  w.start ≤ t ∧ t ≤ w.finish

/-- Filter using a supplied decision procedure for window membership.
    `decide` converts each `Decidable` result to the `Bool` expected by
    `List.filter`. Execution requires a computable producer of that decision
    data (§3.2.4); the predicate alone does not supply one. -/
def eventsInWindow (events : List Event) (w : TimeWindow)
    [DecidablePred (fun (e : Event) => w.contains e.timestamp)] :=
  events.filter (fun e => decide (w.contains e.timestamp))

/-- Exact membership theorem for the filter: no event is added, and every
    retained event satisfies precisely the window predicate. -/
theorem mem_eventsInWindow (events : List Event) (w : TimeWindow)
    [DecidablePred (fun (e : Event) => w.contains e.timestamp)] (e : Event) :
    e ∈ eventsInWindow events w ↔ e ∈ events ∧ w.contains e.timestamp := by
  simp [eventsInWindow]

/-- A strict causal relation on the declared event set. `IsStrictOrder`
    supplies exactly irreflexivity and transitivity; this is not a reflexive
    `PartialOrder`. -/
structure CausalOrder where
  events : Set Event
  precedes : {e : Event // e ∈ events} → {e : Event // e ∈ events} → Prop
  laws : IsStrictOrder {e : Event // e ∈ events} precedes

-- A concrete causal relation supplies `precedes` and discharges the two law
-- fields of `IsStrictOrder`.
```

The timestamp order on `Event` is a preorder. Two different events can share a timestamp and be ordered both ways without being equal. A `PartialOrder Event` based only on timestamps would additionally need antisymmetry, which these fields do not establish.

`mem_eventsInWindow` states both directions of membership: an event is retained exactly when it belongs to the input list and satisfies the window predicate. The function is executable when its supplied decision procedure is executable. Arbitrary real-time comparison in the shared `Time` order is noncomputable, so that order does not supply an executable caller. A discrete clock or a different decidable input domain can serve a runtime requirement.

`CausalOrder` requires an irreflexive, transitive relation on the declared event set. Its fields do not connect that relation to timestamps or establish any external causal interpretation. State and prove such a connection separately when claimed.

For protocol models, a discrete clock can count steps. Here ticks and phase numbers must not be interchanged. {repo "lean/Audit/DocClaims.lean"}[`Glossary.Tick`] is a nominal structure with a public `val : Nat` field. Its `LinearOrder` reuses the natural order and its laws through that injective projection using Mathlib's `LinearOrder.lift'`. Construction and projection are explicit conversions, not an abstraction boundary.

```lean
import Audit.DocClaims
open Glossary

example : LinearOrder Tick := inferInstance
example (a b : Tick) : a ≤ b ↔ a.val ≤ b.val := Tick.le_iff a b

structure ProtocolStep where
  tick : Tick
  phase : Nat

example (n : Nat) : ProtocolStep := ⟨Tick.mk n, n⟩
```

A phase number cannot be used directly as a tick:

```lean (fails := "Application type mismatch")
import Audit.DocClaims

def atTick (t : Glossary.Tick) : Nat := t.val
example (phase : Nat) : Nat := atTick phase
```

If a model intentionally needs only another name for natural numbers, `abbrev Tick := Nat` inherits their `LinearOrder` but creates no semantic type distinction. An ordinary `def` is also definitionally equal to its body but is not unfolded by typeclass synthesis at the same transparency. The instance must be supplied explicitly or obtained by another deliberate transparency choice:

```lean (fails := "(?s)failed to synthesize.*LinearOrder")
import Mathlib.Order.Basic

def Tick := Nat
#synth LinearOrder Tick
```

# 4.4 Spatial Properties
%%%
tag := "44-spatial-properties"
number := false
%%%

*Requirement*: Reuse the matching Mathlib interface for the claimed geometry: for example, a metric for its distance laws or a topology for continuity. Incidence, affine, and combinatorial claims may use other structures. Require the laws the claim needs. Being geometric does not by itself require a metric or topology.

*Rationale*: A claim about distance or continuity needs the corresponding laws. Mathlib provides those verified interfaces, while other geometric claims may require different structures. Selecting the matching interface preserves the exact claim boundary from §1.4.

*Example - Geometric Constraints on Network Edges*:

```lean
import Mathlib.Topology.Instances.Real.Lemmas
import Audit.DocPrelude
open Glossary

/-- One-dimensional locations reuse the real line's canonical Mathlib metric.
    A higher-dimensional model can replace this alias with `EuclideanSpace`; the
    law-reuse point is the same. -/
abbrev Location := ℝ

structure NetworkNode where
  id : Glossary.Id NetworkNodeTag
  location : Location

/-- Coordinate distance is Mathlib's lawful real metric, not a hand-written
    distance relation. -/
noncomputable example : MetricSpace Location := inferInstance

/-- Nodes within communication range, measured through their locations'
    inherited metric. The identifier field does not itself supply a metric;
    route distance through the location field. -/
def inRange (n₁ n₂ : NetworkNode) (range : ℝ) : Prop :=
  dist n₁.location n₂.location ≤ range

/-- Admissible directed edge sets: each edge connects in-range listed nodes. -/
def networkTopology (nodes : Set NetworkNode) (range : ℝ) :=
  {edges : Set (NetworkNode × NetworkNode) //
    ∀ e ∈ edges, e.1 ∈ nodes ∧ e.2 ∈ nodes ∧ inRange e.1 e.2 range}
```

This subtype constrains which edges may be present. It does not require every in-range pair to be an edge. The empty edge set always satisfies it. It also requires neither symmetry nor absence of self-loops. A claim of a complete range graph or a simple undirected graph needs the corresponding definition and laws. Here `networkTopology` names a type of constrained edge sets, not a topological-space instance or a verified communication network.

# 4.5 Foundation Strength: Kernel-Only, Choice-Free, Standard-Logical
%%%
tag := "45-foundation-strength-kernel-only-choice-free-standard-logical"
number := false
%%%

Every Lean declaration has an exact transitive axiom set. `#print axioms` reports this set by following its logical dependencies, including those from Mathlib. This standard fixes exactly three logical foundation labels plus one non-logical classification:

:::table +header
*
  * Label
  * Transitive axioms
*
  * *Kernel-only*
  * `{}` — the kernel's rules alone
*
  * *Choice-Free*
  * ⊆ `{propext, Quot.sound}` — propositional extensionality and quotient soundness, without `Classical.choice`
*
  * *Standard-Logical*
  * ⊆ `{propext, Quot.sound, Classical.choice}` — Lean's full standard base
*
  * _compiler-trusting_
  * _not a logical label_: the axiom set additionally contains compiler-trust axioms (`Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or the per-invocation `._native.` axioms `native_decide` elaborates to) — reported separately, never folded into a logical label
:::

*Rules*:

* A choice-dependent declaration is *never* labeled Choice-Free. The repository's gate mechanically checks a surface's claimed profile against these exact sets ({ref "85-proof-completeness-and-foundation-strength"}[module 8 §8.5]).
* Standard-Logical is a permitted foundation profile. Erased mathematical proofs may use `Classical.choice` within that profile without making the associated program noncomputable. Select the foundation appropriate to the claim and report dependencies honestly. A smaller axiom set is useful when the interface requires it or when a simpler proof achieves it. It is not a general software-assurance ranking.
* Selecting Choice-Free limits the permitted dependencies. It is not a synonym for correctness or executable construction. Replacing a choice-dependent construction may require explicit witnesses, different operations, or weaker interfaces. Inspect the actual dependencies before deciding whether the change supports the claim.
* Importing Mathlib is not disqualifying. The transitive axiom set decides. A pure arithmetic theorem proved inside a Mathlib-importing module can still be kernel-only.

A project logical axiom, `sorryAx`, or an unrecognized axiom fails the conforming proof claim. Compiler-trusting mechanisms are classified separately and excluded from conforming positive proof surfaces. A generated-looking name alone does not establish a compiler origin. {ref "85-proof-completeness-and-foundation-strength"}[§8.5] defines the required classification.

*Selected actual labels from this repository*. An allowed maximum profile admits every subset of its permitted axioms including the empty set. An actual label is the smallest of these three profiles containing the declaration's computed set: empty is Kernel-only; a nonempty subset of `{propext, Quot.sound}` is Choice-Free; a permitted set containing `Classical.choice` is Standard-Logical. Never infer that set from a tactic name. For a theorem, its actual label does not establish that the same proposition has no proof with fewer axioms.

:::table +header
*
  * Declaration
  * Exact transitive axiom set
  * Actual label / declaration
*
  * `Audit.four`
  * `{}`
  * Kernel-only; the explicit even-number witness `⟨4, ⟨2, rfl⟩⟩` in `Audit.Basic`
*
  * `Audit.smoke`
  * `{}`
  * Kernel-only; `1 + 1 = 2` proved by `rfl` in `Audit.Basic`
*
  * `Glossary.reverse_append_correct`
  * `{propext}`
  * Choice-Free; delegates to Core's `List.reverse_append`
*
  * `Glossary.decay_monotone`
  * `{propext, Classical.choice, Quot.sound}`
  * Standard-Logical; the conditional real-valued antitonicity theorem in §4.1
:::

These assertions import the actual declarations from {repo "lean/Audit/Basic.lean"}[Basic] and {repo "lean/Audit/DocClaims.lean"}[DocClaims]. `#guard_msgs` compares each `#print axioms` result with its displayed expected output, so a changed set fails fence elaboration. This checks these selected dependency claims; the gate reports the complete declaration inventory with `lake exe axiomGate --json-out tmp/axiom-report.json`.

```lean
import Audit.Basic
import Audit.DocClaims

/-- info: 'Audit.four' does not depend on any axioms -/
#guard_msgs in
#print axioms Audit.four

/-- info: 'Audit.smoke' does not depend on any axioms -/
#guard_msgs in
#print axioms Audit.smoke

/-- info: 'Glossary.reverse_append_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Glossary.reverse_append_correct

/-- info: 'Glossary.decay_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glossary.decay_monotone
```

The label is computed per declaration, not inferred from an imported module or a type name. Some order and analysis operations over `ℝ` traverse choice-dependent definitions. Other declarations in the same module may remain kernel-only or Choice-Free. The exact transitive set decides. Constructive alternatives can change the interface and proof obligations. They are interface decisions, not automatic conformance upgrades.

*Selecting a maximum is an enforceable requirement.* The opt-in build linter ({ref "812-opt-in-enforcing-build-linter"}[§8.12]) reads the surface's `"claim"` from `foundation_manifest.json` on every enabled ordinary build. Selecting `"choice-free"` rejects both direct and imported/transitive `Classical.choice`, even when the modules have cached build artifacts. Switching a surface with a covered declaration that depends on `Classical.choice` from `"standard-logical"` to `"choice-free"` therefore fails without any source edit. The standalone qualification includes this intended `label-exceeds-claim` failure, a fresh restoration, and positive controls for all three profiles. Enabled ordinary-build evidence is incremental elaboration and current policy inspection, not fresh-source conformance evidence.

This foundation condition is separate from executable construction. A Standard-Logical correctness proof may use choice while its function computes normally ({ref "38-delivering-executable-witnesses-with-required-evidence"}[§3.8]). Choice-Free alone does not guarantee kernel normalization, executable witness extraction, or native execution assurance. Each requires its own precisely stated claim and evidence.

# Summary of Mathematical Foundations
%%%
tag := "summary-of-mathematical-foundations"
number := false
%%%

Apply these patterns so that:

* Numeric representations match the claim; real-valued models and machine arithmetic are connected by checked correspondence when needed.
* Matching Lean and Mathlib structures supply reusable laws and theorems.
* Claimed orders and interfaces are lawful and complete.
* Foundation strength is reported per declaration from its exact transitive axiom set, separately from executability and runtime trust.

By using Mathlib's lawful interfaces, Lean definitions and proofs can reuse their checked laws. Each result remains the exact theorem Lean accepted about the stated mathematical objects or executable definitions, at its reported foundation strength.
