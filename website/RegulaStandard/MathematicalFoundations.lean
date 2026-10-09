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
* Use core's `Rat` when the claim is exact rational arithmetic: its order is decidable and its operations execute. It is not a model of the reals; a statement that needs completeness, limits or analysis requires `ℝ`.
* Use floating-point and fixed-width machine types when the claim is about that arithmetic, and name the semantics the claim relies on: rounding and exceptional values for `Float`; wrapping and bit width for machine words and `BitVec`; serialization when values cross a byte boundary.
* Specify an executable representation directly when its behavior is the subject of the claim. Transfer an abstract model’s result through checked correspondence to the actual implementation ({ref "13-the-specificationmodel-firewall"}[module 1 §1.3]).
* Discrete models, such as `ℕ`-based clocks and `Fin n` phases, also conform when they fit the claim. Supply the laws of every claimed mathematical interface.

*Example - Exact Rational Quantities with a Lawful Order*:

The shared `Time` type wraps non-negative rational numbers: exact arithmetic with a decidable order, not the real numbers. In {repo "audit/Audit/DocClaims.lean"}[`Audit.DocClaims`], `DecayingValue.valueAt` is the linear curve `initial * (1 + decayRate * (t - startTime))`, using the underlying rational values of the times. The theorem below establishes a nonincreasing curve for a negative rate. It does not establish strict decrease because `initial` may be zero. Its quantifiers include all ordered pairs of times, including times before `startTime`. That field shifts the formula rather than restricting its domain. The curve is linear, not exponential: a claim about `initial * exp (decayRate * (t - startTime))` over `ℝ` needs Mathlib's real analysis, and the {repo "integration/mathlib/MathlibAudit/DocClaims.lean"}[Mathlib integration package] proves the same antitonicity statement for that real-valued curve.

```lean
import Audit.DocClaims
open Glossary

/- `Time` is a nominal wrapper around a non-negative `Rat`; `ResourceAmount` is the
canonical subtype directly. The wrapper has the complete lawful order claimed here,
and its comparison is decidable. -/
example : Std.IsLinearOrder Time := inferInstance
example (a b : Time) : Decidable (a ≤ b) := inferInstance
example (t : Time) : 0 ≤ t.val := t.nonneg

/-- This alias exposes the exact theorem checked in `Audit.DocClaims`: for every
curve with a negative rate and every ordered pair of nominal times, the
later reference value is no greater than the earlier reference value. -/
theorem valueAt_antitone_of_decayRate_neg (v : DecayingValue) (h : v.decayRate < 0)
    (t₁ t₂ : Time) (h₁₂ : t₁ ≤ t₂) : v.valueAt t₂ ≤ v.valueAt t₁ :=
  decay_monotone v h t₁ t₂ h₁₂

/-- The displayed hypotheses are jointly satisfiable; this is not a claim of
reachability in an external system. -/
theorem exists_decayRate_neg_and_le :
    ∃ (v : DecayingValue) (t₁ t₂ : Time), v.decayRate < 0 ∧ t₁ ≤ t₂ :=
  decay_monotone_nonvacuous
```

An `LE` instance supplies a relation used by `≤`. It provides no proofs of reflexivity, transitivity, antisymmetry, or totality, and does not provide `min` or `max`. Even when its relation has those properties, the stronger interface requires their evidence. The bare relation below therefore does not synthesize core's `Std.IsLinearOrder`:

```lean (fails := "(?s)failed to synthesize.*IsLinearOrder")
/-- A non-negative rational number. -/
structure T where
  /-- The underlying rational number. -/
  val : Rat
  /-- The number is non-negative. -/
  nonneg : 0 ≤ val

instance : LE T := ⟨fun x y ↦ x.val ≤ y.val⟩

-- A bare relation does not synthesize the lawful structure:
#synth Std.IsLinearOrder T
```

If the prose claims that time has a linear order, supply the corresponding lawful instance (core's `Std.IsLinearOrder`, or Mathlib's `LinearOrder` in a Mathlib project) as the shared `Glossary.Time` does in {repo "audit/Audit/DocPrelude.lean"}[`Audit.DocPrelude`].

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
theorem admitReading_eq_ok (x : Float) (h : ¬x.isNaN ∧ ¬x.isInf) :
    admitReading x = .ok ⟨x, h⟩ := by
  simp [admitReading, h.1, h.2]
```

The specification uses `Float` because the claim concerns binary64 values. Its return type excludes `NaN` and infinities. `admitReading_eq_ok` additionally establishes acceptance and preservation of every input satisfying those conditions. These properties do not establish sensor accuracy or a permitted measurement range.

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

*Key Structures from Lean's Core Library*:

* Order laws over the operational class `LE`: `Std.IsPreorder`, `Std.IsPartialOrder` and `Std.IsLinearOrder`, with the `Prop`-valued mixins `Std.LawfulOrderLT`, `Std.LawfulOrderMin` and `Std.LawfulOrderMax` relating `<`, `min` and `max` to `≤`.
* Laws of a binary operation: `Std.Associative`, `Std.Commutative` and `Std.LawfulIdentity`.
* `Std.LinearOrderPackage.ofLE` builds the lawful linear-order structure of a type from its `≤`, a decision procedure and the three laws `Std.Total`, `Trans` and `Std.Antisymm`.

*Example - Canonical Orders Without Rebuilding Them*:

```lean
/-- Named levels obtain an order by an injective rank into `Nat`. Core's
`Std.LinearOrderPackage.ofLE` builds the lawful structure from the laws of
the rank order, which are `Nat`'s. -/
inductive ConsensusLevel
  /-- No consensus. -/
  | none
  /-- Weak consensus. -/
  | weak
  /-- Moderate consensus. -/
  | moderate
  /-- Strong consensus. -/
  | strong
  /-- Every participant agrees. -/
  | unanimous

/-- Index each level into the canonical natural order. -/
def ConsensusLevel.rank : ConsensusLevel → Nat
  | .none => 0 | .weak => 1 | .moderate => 2 | .strong => 3 | .unanimous => 4

instance : LE ConsensusLevel := ⟨fun a b ↦ a.rank ≤ b.rank⟩

instance : DecidableLE ConsensusLevel :=
  fun a b ↦ inferInstanceAs (Decidable (a.rank ≤ b.rank))

instance : Std.Total (α := ConsensusLevel) (· ≤ ·) :=
  ⟨fun a b ↦ Nat.le_total a.rank b.rank⟩

instance : Trans (α := ConsensusLevel) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Nat.le_trans⟩

/-- The rank is injective, so levels that compare both ways are equal. -/
instance : Std.Antisymm (α := ConsensusLevel) (· ≤ ·) where
  antisymm a b hab hba := by
    have h : a.rank = b.rank := Nat.le_antisymm hab hba
    cases a <;> cases b <;> simp_all [ConsensusLevel.rank]

instance : Std.LinearOrderPackage ConsensusLevel := .ofLE ConsensusLevel

example : Std.IsLinearOrder ConsensusLevel := inferInstance

/-- When named constructors aren't needed at all, an abbreviation inherits
everything outright — no new structure, zero proofs. -/
abbrev Priority := Fin 5
example : Std.IsLinearOrder Priority := inferInstance
```

The rank function chooses the intended ordering. The injectivity proof shows that distinct constructors receive distinct ranks. In a Mathlib project, `LinearOrder.lift'` transports the order and its laws along the same injective rank in one step; {repo "integration/mathlib/MathlibAudit/DocClaims.lean"}[`Glossary.Tick`] in the Mathlib integration package is built that way. Lean provides no `deriving` handler for the lawful structure:

```lean (fails := "(?s)deriving.*IsLinearOrder")
/-- Two named levels. -/
inductive Level
  /-- The lower level. -/
  | low
  /-- The higher level. -/
  | high
  deriving Std.IsLinearOrder
```

# 4.3 Temporal Models
%%%
tag := "43-temporal-models"
number := false
%%%

*Principle*: Model time with the structure the claim needs — and provide the lawful structure the prose claims.

Discrete and continuous models are both conforming, as long as the order (or other) interface is complete and lawful:

```lean
import Audit.DocPrelude
open Glossary

/- This fence uses the shared `Time` type (§4.1): non-negative rationals
with a lawful, decidable linear order, shipped by the glossary. -/

/-- Events in the system (`Id`: §2.3, `Time`: §4.1, `OpaqueData`: module 6 §6.5.1). -/
structure Event where
  /-- The event's identifier, tagged as an event identifier. -/
  id : Glossary.Id EventTag
  /-- When the event occurred. -/
  timestamp : Time
  /-- The event's payload, which this model does not observe. -/
  content : OpaqueData

/-- Temporal ordering of events, by their timestamps. -/
instance : LE Event := ⟨fun e₁ e₂ ↦ e₁.timestamp ≤ e₂.timestamp⟩

/-- The timestamp order is a preorder: its two laws are those of `Time`'s
linear order, which supplies that weaker structure. -/
instance : Std.IsPreorder Event where
  le_refl e := Std.le_refl e.timestamp
  le_trans _ _ _ h₁ h₂ := Std.le_trans (α := Time) h₁ h₂

example : Std.IsPreorder Event := inferInstance

/-- A time window with validity proof. -/
structure TimeWindow where
  /-- The first time in the window. -/
  start : Time
  /-- The last time in the window. -/
  finish : Time
  /-- The window does not end before it starts. -/
  valid : start ≤ finish

/-- A time lies within the window, both ends included. -/
def TimeWindow.Contains (w : TimeWindow) (t : Time) : Prop :=
  w.start ≤ t ∧ t ≤ w.finish

/-- Filter using a supplied decision procedure for window membership.
`decide` converts each `Decidable` result to the `Bool` expected by
`List.filter`. Execution requires a computable producer of that decision
data (§3.2.4); the predicate alone does not supply one. -/
def eventsInWindow (events : List Event) (w : TimeWindow)
    [DecidablePred (fun (e : Event) ↦ w.Contains e.timestamp)] : List Event :=
  events.filter (fun e ↦ decide (w.Contains e.timestamp))

/-- Exact membership theorem for the filter: no event is added, and every
retained event satisfies precisely the window predicate. -/
theorem mem_eventsInWindow (events : List Event) (w : TimeWindow)
    [DecidablePred (fun (e : Event) ↦ w.Contains e.timestamp)] (e : Event) :
    e ∈ eventsInWindow events w ↔ e ∈ events ∧ w.Contains e.timestamp := by
  simp [eventsInWindow]

/-- A computable producer of the decision: both comparisons of rational times
are decidable. -/
instance (w : TimeWindow) (t : Time) : Decidable (w.Contains t) :=
  inferInstanceAs (Decidable (w.start ≤ t ∧ t ≤ w.finish))

/-- With that producer the filter has an executable caller. -/
def eventsWithin (events : List Event) (w : TimeWindow) : List Event :=
  eventsInWindow events w

/-- A strict causal relation on the declared events: exactly irreflexivity
and transitivity. This is not a reflexive partial order. -/
structure CausalOrder where
  /-- Which events are declared: a membership predicate. -/
  Declared : Event → Prop
  /-- The causal relation between declared events. -/
  precedes : {e : Event // Declared e} → {e : Event // Declared e} → Prop
  /-- `precedes` is irreflexive. -/
  irrefl : ∀ e, ¬ precedes e e
  /-- `precedes` is transitive. -/
  trans : ∀ e₁ e₂ e₃, precedes e₁ e₂ → precedes e₂ e₃ → precedes e₁ e₃

-- A concrete causal relation supplies `precedes` and discharges the two law
-- fields.
```

The timestamp order on `Event` is a preorder. Two different events can share a timestamp and be ordered both ways without being equal. A partial order on `Event` based only on timestamps would additionally need antisymmetry, which these fields do not establish.

`mem_eventsInWindow` states both directions of membership: an event is retained exactly when it belongs to the input list and satisfies the window predicate. The function is executable when its supplied decision procedure is executable. The shared `Time` order compares rationals and is decidable, so `eventsWithin` is an executable caller. A real-valued time has no executable comparison: over Mathlib's `ℝ` the same function has only noncomputable callers, and a discrete clock or another decidable input domain serves a runtime requirement.

`CausalOrder` requires an irreflexive, transitive relation on the declared events. Its fields do not connect that relation to timestamps or establish any external causal interpretation. State and prove such a connection separately when claimed.

For protocol models, a discrete clock can count steps. Here ticks and phase numbers must not be interchanged. {repo "audit/Audit/DocClaims.lean"}[`Glossary.Tick`] is a nominal structure with a public `val : Nat` field. Its `Std.IsLinearOrder` instance reuses the natural order and its laws through that injective projection, built by core's `Std.LinearOrderPackage.ofLE`. Construction and projection are explicit conversions, not an abstraction boundary.

```lean
import Audit.DocClaims
open Glossary

example : Std.IsLinearOrder Tick := inferInstance
example (a b : Tick) : a ≤ b ↔ a.val ≤ b.val := Tick.le_iff a b

/-- One protocol step: a clock tick and a phase number, kept as distinct types. -/
structure ProtocolStep where
  /-- The clock tick at which the step occurs. -/
  tick : Tick
  /-- The protocol phase number. -/
  phase : Nat

example (n : Nat) : ProtocolStep := ⟨Tick.mk n, n⟩
```

A phase number cannot be used directly as a tick:

```lean (fails := "Application type mismatch")
import Audit.DocClaims

/-- The natural number underlying a tick. -/
def atTick (t : Glossary.Tick) : Nat := t.val
example (phase : Nat) : Nat := atTick phase
```

If a model intentionally needs only another name for natural numbers, `abbrev Tick := Nat` inherits their order instances and laws but creates no semantic type distinction. An ordinary `def` is also definitionally equal to its body but is not unfolded by typeclass synthesis at the same transparency. Even the relation `≤` must be supplied explicitly or obtained by another deliberate transparency choice:

```lean (fails := "(?s)failed to synthesize.*LE Tick")
/-- Another name for natural numbers, as an ordinary `def`. -/
def Tick := Nat
#synth Std.IsLinearOrder Tick
```

# 4.4 Spatial Properties
%%%
tag := "44-spatial-properties"
number := false
%%%

*Requirement*: Reuse the matching Mathlib interface for the claimed geometry: for example, a metric for its distance laws or a topology for continuity. Incidence, affine, and combinatorial claims may use other structures. Require the laws the claim needs. Being geometric does not by itself require a metric or topology.

*Rationale*: A claim about distance or continuity needs the corresponding laws. Mathlib provides those verified interfaces, while other geometric claims may require different structures. Selecting the matching interface preserves the exact claim boundary from §1.4.

*Example - Incidence Constraints on Network Edges* (an incidence claim: which cells lie in which coverage zones. It needs no distance, so it uses no metric; a claim about range measures distance through Mathlib's `MetricSpace ℝ`, checked as `MathlibModels.InRange` in the {repo "integration/mathlib/MathlibAudit/Models.lean"}[Mathlib integration package]):

```lean
import Audit.DocPrelude
open Glossary

/-- A location is a cell of a floor plan: its row and its column. -/
abbrev Cell := Nat × Nat

/-- A network node: an identifier and the cell it is in. -/
structure NetworkNode where
  /-- The node's identifier, tagged as a network-node identifier. -/
  id : Glossary.Id NetworkNodeTag
  /-- The cell the node is in. -/
  cell : Cell

/-- A coverage zone lists the cells it contains. A cell lies in a zone by
core's list membership, not by a hand-written incidence relation. -/
abbrev Zone := List Cell

/-- Two nodes share a zone: one listed zone contains both their cells. The
identifier field does not locate a node; incidence goes through the cell field. -/
def ShareZone (zones : List Zone) (n₁ n₂ : NetworkNode) : Prop :=
  ∃ zone ∈ zones, n₁.cell ∈ zone ∧ n₂.cell ∈ zone

/-- Listing further zones keeps every shared zone, by the definition of core's
`List.Subset`. -/
theorem ShareZone.of_subset {zones zones' : List Zone} (h : zones ⊆ zones')
    {n₁ n₂ : NetworkNode} : ShareZone zones n₁ n₂ → ShareZone zones' n₁ n₂ :=
  fun ⟨zone, listed, incident⟩ ↦ ⟨zone, h listed, incident⟩

/-- Admissible directed edge relations: each edge connects listed nodes that
share a zone. -/
def NetworkTopology (listed : NetworkNode → Prop) (zones : List Zone) : Type :=
  {edges : NetworkNode → NetworkNode → Prop //
    ∀ n₁ n₂, edges n₁ n₂ → listed n₁ ∧ listed n₂ ∧ ShareZone zones n₁ n₂}
```

This subtype constrains which edges may be present. It does not require every pair that shares a zone to be an edge. The empty edge relation always satisfies it. It also requires neither symmetry nor absence of self-loops. A claim of a complete zone graph or a simple undirected graph needs the corresponding definition and laws. Here `NetworkTopology` names a type of constrained edge relations, not a topological-space instance or a verified communication network. `ShareZone` states incidence only: it is not transitive when zones overlap, and it says nothing about how far apart two cells are. `ShareZone.of_subset` is the one law this example proves about it. A claim about distance or range needs a metric and its laws, reused from the matching interface, not defined beside the example.

# 4.5 Foundation Strength: Kernel-Only, Choice-Free, Standard-Logical
%%%
tag := "45-foundation-strength-kernel-only-choice-free-standard-logical"
number := false
%%%

Every Lean declaration has an exact transitive axiom set: the axioms reached through the types and values of the constants it uses, including those from Mathlib. `#print axioms` follows these dependencies, but for an imported declaration it reads the axiom table that the declaration's module recorded when it was compiled, and on the pinned toolchain such a table can omit axioms reached through the constructors of an inductive type. A gate therefore computes the set from the kernel-checked declarations (§7.4). This standard fixes exactly three logical foundation labels plus one non-logical classification:

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
  * _not a logical label_: the axiom set additionally contains compiler-trust axioms (the `Lean.trustCompiler`, `Lean.ofReduceBool` and `Lean.ofReduceNat` family when the selected compiler declares it, or the authenticated per-invocation `._native.` axioms that `native_decide`, `decide +native`, and `bv_decide` elaborate to) — reported separately, never folded into a logical label; retired names have no compiler exception
:::

*Rules*:

* A choice-dependent declaration is *never* labeled Choice-Free. The shipped gate mechanically checks a surface's claimed profile against these exact sets ({ref "75-proof-completeness-and-foundation-strength"}[module 7 §7.5]).
* Standard-Logical is a permitted foundation profile. Erased mathematical proofs may use `Classical.choice` within that profile without making the associated program noncomputable. Select the foundation appropriate to the claim and report dependencies honestly. A smaller axiom set is useful when the interface requires it or when a simpler proof achieves it. It is not a general software-assurance ranking.
* Selecting Choice-Free limits the permitted dependencies. It is not a synonym for correctness or executable construction. Replacing a choice-dependent construction may require explicit witnesses, different operations, or weaker interfaces. Inspect the actual dependencies before deciding whether the change supports the claim.
* Importing Mathlib is not disqualifying. The transitive axiom set decides. A pure arithmetic theorem proved inside a Mathlib-importing module can still be kernel-only.

A project logical axiom, `sorryAx`, or an unrecognized axiom fails the conforming proof claim. Compiler-trusting mechanisms are classified separately and excluded from conforming positive proof surfaces. A generated-looking name alone does not establish a compiler origin. {ref "75-proof-completeness-and-foundation-strength"}[§7.5] defines the required classification.

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
  * `reverse_append_eq`
  * `{propext}`
  * Choice-Free; delegates to Core's `List.reverse_append` in the example of {ref "322-property-based-testing-as-refutation-aid"}[§3.2.2]
*
  * `Glossary.decay_monotone`
  * `{propext, Classical.choice, Quot.sound}`
  * Standard-Logical; the conditional rational-valued antitonicity theorem in §4.1, whose proof uses core's order lemmas for `Rat`
:::

These assertions import the actual declarations from {repo "audit/Audit/Basic.lean"}[Basic] and {repo "audit/Audit/DocClaims.lean"}[DocClaims]; the §3.2.2 example makes the same assertion for `reverse_append_eq` where it is written. `#guard_msgs` compares each `#print axioms` result with its displayed expected output, so a changed set fails fence elaboration. This checks these selected dependency claims; the gate reports the complete declaration inventory with `lake exe axiomGate --json-out tmp/axiom-report.json`.

```lean
import Audit.Basic
import Audit.DocClaims

/-- info: 'Audit.four' does not depend on any axioms -/
#guard_msgs in
#print axioms Audit.four

/-- info: 'Audit.smoke' does not depend on any axioms -/
#guard_msgs in
#print axioms Audit.smoke

/-- info: 'Glossary.decay_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Glossary.decay_monotone
```

The label is computed per declaration, not inferred from an imported module or a type name. Core's order lemmas for `Rat` traverse choice-dependent definitions, as do many order and analysis operations over Mathlib's `ℝ`. Other declarations in the same module may remain kernel-only or Choice-Free. The exact transitive set decides. Constructive alternatives can change the interface and proof obligations. They are interface decisions, not automatic conformance upgrades.

*Selecting a maximum is an enforceable requirement.* The opt-in build linter ({ref "711-opt-in-enforcing-build-linter"}[§7.11]) reads the surface's `"claim"` from `foundation_manifest.json` on every enabled ordinary build. Selecting `"choice-free"` rejects both direct and imported/transitive `Classical.choice`, even when the modules have cached build artifacts. Switching a surface with a covered declaration that depends on `Classical.choice` from `"standard-logical"` to `"choice-free"` therefore fails without any source edit. The standalone qualification includes this intended `label-exceeds-claim` failure, a fresh restoration, and positive controls for all three profiles. Enabled ordinary-build evidence is incremental elaboration and current policy inspection, not fresh-source conformance evidence.

This foundation condition is separate from executable construction. A Standard-Logical correctness proof may use choice while its function computes normally ({ref "38-delivering-executable-witnesses-with-required-evidence"}[§3.8]). Choice-Free alone does not guarantee kernel normalization, executable witness extraction, or native execution assurance. Each requires its own precisely stated claim and evidence.
