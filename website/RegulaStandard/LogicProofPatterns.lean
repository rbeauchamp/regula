import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "3. Logic and Proof Patterns" =>
%%%
tag := "3-logic-and-proof-patterns"
file := "3-logic-proof-patterns"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "3-overview"
number := false
%%%

This section establishes proof patterns for mathematical statements and contracts about executable Lean definitions. These patterns implement the theorem-backed-claims principle from Section 1.

# 3.1 What Must Be Proven
%%%
tag := "31-what-must-be-proven"
number := false
%%%

*Requirement*: Every material property claimed as established about a mathematical model or executable Lean definition MUST have machine-checked evidence from its type, proof-bearing construction, or a supporting theorem. State assumptions and open targets separately (§3.10).

*Claim-Specific Proof Obligations*: Apply the following obligations where required; they do not demand a separate theorem for every category.

1. *Admission and Invariant Preservation*: Establish the unary invariant at admission and every write/update by proof-bearing results or justified raw representation contracts of {ref "11-the-principle-of-representational-precision"}[§1.1]. Conditional preservation alone does not establish admission.
2. *Totality*: State the function’s domain and encode any promised restriction in its API. Distinguish a total logical definition from termination of its execution (§3.2.1).
3. *Termination*: Recursion presented as terminating requires structural or well-founded justification or another checked termination argument. Classify other recursion mechanisms explicitly (§3.6).
4. *Composition Properties*: Prove the claimed relations over transitions, reachable states, histories, or resource use. Include initialization, preservation, and composition where needed to derive the claim. A state invariant alone does not establish how an output relates to an input or history.
5. *Impossibility Results*: Use the type or a theorem to establish that the states a claim excludes cannot occur.

*Example - An Intrinsic Invariant and Its Consequences*:

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Basic

/-- A system state that must maintain invariants. -/
structure SystemState where
  /-- The number of participants. -/
  participants : ℕ
  /-- The number of active proposals. -/
  activeProposals : ℕ
  /-- Invariant: there are no more active proposals than participants. -/
  inv : activeProposals ≤ participants

/-- Non-vacuity: states satisfying the invariant exist. -/
example : Nonempty SystemState := ⟨⟨3, 1, by omega⟩⟩

/-- Adding a participant maintains the invariant. -/
def addParticipant (s : SystemState) : SystemState where
  participants := s.participants + 1
  activeProposals := s.activeProposals
  inv := by
    -- Proof that invariant is maintained (`omega`: core tactic, pure-Nat goal)
    have h := s.inv
    omega

/-- The input's active proposals stay within the participants after adding one. -/
theorem activeProposals_le_addParticipant_participants (s : SystemState) :
    s.activeProposals ≤ (addParticipant s).participants :=
  -- Proof is immediate from construction
  (addParticipant s).inv

/-- Composition preserves the invariant stated above. Because the invariant
is a *field* of `SystemState`, no side conditions on `f` and `g` are needed
for this bound — their results already carry it. -/
theorem comp_activeProposals_le_participants (f g : SystemState → SystemState)
    (s : SystemState) : ((f ∘ g) s).activeProposals ≤ ((f ∘ g) s).participants :=
  (f (g s)).inv

/-- Prove the excluded states are excluded. -/
theorem not_exists_participants_eq_zero_and_activeProposals_pos :
    ¬∃ s : SystemState, s.participants = 0 ∧ 0 < s.activeProposals := by
  intro ⟨s, hp, ha⟩
  have : s.activeProposals ≤ s.participants := s.inv
  rw [hp] at this
  omega
```

The theorem `comp_activeProposals_le_participants` follows from the result type: every returned `SystemState` carries its bound. The functions are total in Lean’s logic. This theorem establishes no relation between inputs and outputs beyond the invariant. It does not provide an execution time bound or connect to an external process ({ref "16-claim-boundaries-and-automated-checking"}[module 1 §1.6]).

# 3.2 Proof Patterns
%%%
tag := "32-proof-patterns"
number := false
%%%

*Pattern*: Structure proofs to be both correct and comprehensible, following established patterns for common proof obligations.

*Core Patterns*:

1. *Totality and Termination by Construction*: Use structural or well-founded recursion for terminating definitions; distinguish other computation mechanisms explicitly ({ref "86-classify-lean-computation-mechanisms-exactly"}[module 8 §8.6]).
2. *Property-Based Testing as Refutation Aid*: Use optional counterexample search to diagnose false candidates; a passing sampled run is not a proof (§3.2.2).
3. *Typeclasses for Lawful Abstractions*: Generic interfaces with proven laws, held in the operational class or in a `Prop`-valued lawful mixin (§3.2.3).
4. *Decidability*: Distinguish logical decidability from executable decision procedures (§3.2.4).
5. *Proof Economy*: Separate elaboration, proof-artifact, kernel-replay, and native-execution cost; inspect the resulting dependencies rather than inferring trust from speed (§3.2.5).

## 3.2.1 Totality, Termination, and Totalized Operations
%%%
tag := "321-totality-termination-and-totalized-operations"
number := false
%%%

*Rationale*: Structural and well-founded recursion justify a recursive definition through Lean’s recursors. Say precisely what that buys: the definition is total in Lean's logic. It has *not* established code generation, resource consumption, execution time, or a deployed system's behavior; termination is not a complexity bound and not, by itself, a security property.

*Example - Termination Patterns* (the examples use domain-specific types and operations rather than redeclaring matching Core or Mathlib functions such as `List.sum` or `Nat.ack`):

```lean
import Mathlib.Data.Nat.Notation

/-- A small review workflow used only to expose its recursive structure. -/
inductive ReviewPlan where
  /-- No step remains. -/
  | done
  /-- A review step, followed by the rest of the plan. -/
  | review (rest : ReviewPlan)
  /-- A revision step, followed by the rest of the plan. -/
  | revise (rest : ReviewPlan)

/-- Structural recursion: Lean accepts the call on the direct subplan. -/
def ReviewPlan.stepCount : ReviewPlan → ℕ
  | .done => 0
  | .review rest => rest.stepCount + 1
  | .revise rest => rest.stepCount + 1

/-- State for a bounded retry model. -/
structure RetryState where
  /-- Retries still to run. -/
  remaining : ℕ
  /-- Retries already completed. -/
  completed : ℕ

/-- The completed count once every remaining retry has run. Well-founded recursion:
each call has one fewer remaining retry. -/
def RetryState.totalCompleted (s : RetryState) : ℕ :=
  if _h : s.remaining = 0 then s.completed
  else totalCompleted { remaining := s.remaining - 1, completed := s.completed + 1 }
  termination_by s.remaining
  decreasing_by omega
```

This recursive call increases its argument indefinitely, and Lean rejects the ordinary `def`:

```lean (fails := "fail to show termination|failed to eliminate recursive")
import Mathlib.Data.Nat.Basic

/-- Unbounded increasing recursion: Lean refuses this ordinary definition. -/
def loop (n : ℕ) : ℕ := loop (n + 1)
```

*Totalized operations*: Natural-number division in Lean is total; division by zero returns `0`.

```lean
import Mathlib.Data.Nat.Basic

/-- `Nat.div` is total: the zero-divisor case is defined, yielding 0. -/
example : (1 : ℕ) / 0 = 0 := rfl

/-- A restricted domain is expressed by the API when the model wants one:
the denominator subtype carries the proof obligation. -/
def safeDiv (a : ℕ) (d : {d : ℕ // 0 < d}) : ℕ := a / d.val

/-- `safeDiv` agrees with the underlying total division. -/
theorem safeDiv_eq (a : ℕ) (d : {d : ℕ // 0 < d}) : safeDiv a d = a / d.val := rfl

example : safeDiv 6 ⟨2, by decide⟩ = 3 := rfl
```

The subtype documents the intended domain at the type level. The underlying division is total in both cases; `1 / 0` remains `0`, but a zero denominator cannot be constructed for `safeDiv`. Mathlib names this positive-natural subtype `ℕ+` (`PNat`). This example spells out the subtype pattern for teaching rather than introducing a new mathematical type. The existing name is available for ordinary reuse ({ref "14-principled-mathematical-modeling"}[module 1 §1.4]). The forbidden zero argument is checked separately:

```lean (fails := "Tactic `decide` proved|proved that the proposition")
import Mathlib.Data.Nat.Basic

/-- Division by a divisor that carries its proof of positivity. -/
def safeDiv (a : ℕ) (d : {d : ℕ // 0 < d}) : ℕ := a / d.val

/-- The domain restriction is enforced at elaboration: the zero divisor cannot be
supplied a proof, so this call does not elaborate. -/
def oops := safeDiv 1 ⟨0, by decide⟩
```

## 3.2.2 Property-Based Testing as Refutation Aid
%%%
tag := "322-property-based-testing-as-refutation-aid"
number := false
%%%

*Rationale*: Counterexample search is optional diagnostic assistance. A counterexample checked against exact definitions and hypotheses refutes a candidate universal statement. A passing sampled run does not prove it. Prefer types, construction, existing theorems, and structural or compositional proofs. Use testing to discover counterexamples when a suitable deductive or symbolic approach is unavailable. No authoring order is mandated ({ref "12-theorem-backed-claims"}[module 1 §1.2]).

Kernel-checked exhaustive case analysis over a closed finite domain is a proof, as is a checked witness of an existential claim. These differ from sampled agreement or unchecked enumeration. Mutation tests diagnose a checker’s response to selected inputs but do not establish its universal correctness.

*Example - Refutation, Then a Library Proof*:

```lean
import Mathlib.Data.Nat.Notation

/-- The naive claim
`∀ (l₁ l₂ : List ℕ), (l₁ ++ l₂).reverse = l₁.reverse ++ l₂.reverse`
is refuted by the counterexample `l₁ = [1]`, `l₂ = [2]`
(LHS `[2, 1]` ≠ RHS `[1, 2]`). The corrected statement follows from the
library theorem, regardless of how the counterexample was found. -/
theorem reverse_append_eq (l₁ l₂ : List ℕ) :
    (l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse :=
  @List.reverse_append ℕ l₁ l₂

/-- info: 'reverse_append_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reverse_append_eq
```

A discovered counterexample can become a checked refutation, and a discovered witness can become a checked existence proof. A corrected universal statement requires its own proof; the preceding test run does not establish it.

## 3.2.3 Typeclasses for Lawful Abstractions
%%%
tag := "323-typeclasses-for-lawful-abstractions"
number := false
%%%

*Rationale*: Typeclasses can bundle operations, laws, or both. An operational class alone supplies its declared operations. An instance of a law-bearing class must supply evidence of its laws.

*Requirement*: Every claimed typeclass law MUST follow from proof-requiring fields of the operational class or a lawful mixin required by the interface. A law may be supplied directly or derived by a checked theorem from sufficient primitive laws under the advertised hypotheses. Derived consequences need no duplicate fields. Comments explain laws but do not supply their proofs.

*Implementation Note*: Construct each law-bearing instance with evidence for every required field, reusing existing instances or theorems where appropriate. Missing evidence prevents a complete instance; `sorry` or `admit` is prohibited. An operations-only instance is valid when it makes no lawfulness claim.

*Example - Operations Without the Claimed Laws*:

The following class and instance elaborate, but the two advertised laws are false. The checked refutations identify the defect; merely compiling the operations would not.

```lean
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-- ❌ CRITICAL VIOLATION: laws only in documentation. The operations below are
the class's only fields. -/
class BadFlourishing (α : Type) where
  /-- A binary combining operation. -/
  enhance : α → α → α
  /-- A real-valued measure. -/
  measure : α → ℝ
  -- Law: enhance is associative (comment only)
  -- Law: measure is monotone (comment only)
  -- These "laws" are just comments! Any instance can violate them!
  -- (Plain `--` lines, NOT `/-- ... -/` docstrings: a docstring demands a
  -- declaration after it, and dangling ones fail to parse.)

-- This violating instance elaborates — that is exactly the defect:
instance : BadFlourishing ℝ where
  enhance := (· - ·)  -- Not associative!
  measure := (fun x ↦ -x)  -- Not monotone!
  -- No error because the laws are not fields

/-- Subtraction is not associative. -/
example : ¬ (∀ a b c : ℝ,
    BadFlourishing.enhance (BadFlourishing.enhance a b) c =
      BadFlourishing.enhance a (BadFlourishing.enhance b c)) := by
  intro h
  have bad := h 0 0 1
  norm_num [BadFlourishing.enhance] at bad

/-- Negation does not preserve the ordinary real order. -/
example : ¬ Monotone (BadFlourishing.measure : ℝ → ℝ) := by
  intro h
  have bad := h (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num [BadFlourishing.measure] at bad
```

*Example - Lawful Abstraction*:

Failure to prove a law leaves an unresolved obligation. A counterexample may show that the law or operations need correction; difficulty finding a proof does not prove either is wrong. This separate interface illustrates three order laws rather than repairing the associativity contract above.

```lean
import Mathlib.Basic.Real.Basic     -- `measure : α → ℝ` and the ℝ instance below
import Mathlib.Algebra.Order.Group.Defs

/-- The order is a separate lawful parameter (`Preorder`), not an `LE` parent
the instance could choose for itself. -/
class Flourishable (α : Type) [Preorder α] where
  -- Operations
  /-- An operation that must not decrease its first argument. -/
  enhance : α → α → α
  /-- An operation that must not increase its first argument. -/
  diminish : α → α → α
  /-- A real-valued measure that must preserve the order. -/
  measure : α → ℝ

  -- Laws that MUST be proven for every instance
  /-- `enhance` does not decrease its first argument. -/
  enhance_increases : ∀ a b, a ≤ enhance a b
  /-- `diminish` does not increase its first argument. -/
  diminish_decreases : ∀ a b, diminish a b ≤ a
  /-- `measure` preserves the order. -/
  measure_monotone : ∀ a b, a ≤ b → measure a ≤ measure b

/-- Concrete instance with ALL laws proven. Mathlib's order lemmas prove the
max/min laws; the identity measure preserves the supplied inequality. -/
instance : Flourishable ℝ where
  enhance := max
  diminish := min
  measure := id

  enhance_increases := fun _ _ ↦ le_max_left _ _
  diminish_decreases := fun _ _ ↦ min_le_left _ _
  measure_monotone := fun _ _ h ↦ h
```

These laws state that `enhance` does not decrease its first argument, `diminish` does not increase it, and `measure` preserves the supplied order. Whether these properties suffice depends on the interface’s intended claim.

*Laws in a lawful mixin*: The laws need not live in the class that holds the operations. The pinned Mathlib keeps ordered-algebra laws in `Prop`-valued mixins (`IsOrderedAddMonoid`, `IsStrictOrderedRing`) over the operational classes, and Core keeps `LawfulFunctor`, `LawfulMonad`, and `LawfulBEq` apart from `Functor`, `Monad`, and `BEq`. Every claimed law must follow from the available law-bearing evidence, directly or by checked derivation. Every instance discharges each required primitive field, and a claimed lawful interface obtains its required mixin. Four consequences follow:

1. A declaration using a mixin’s law MUST have its evidence available. A generic declaration may require the mixin directly (`[Flourishable α] [LawfulFlourishable α]`) or obtain it from stronger assumptions that supply the instance. A concrete use obtains it from an established instance (the ℝ examples below). The operations alone do not supply the mixin’s laws; the elaborator refuses the law without the mixin (second negative fence below).
2. An operational instance alone supplies no evidence of the mixin’s laws. Prose that presents it as lawful is a prose-only law (`THEOREM-02`, `SCOPE-02`), and a claimed-lawful use site that omits the mixin fails `THEOREM-02`.
3. The mixin instance is admitted only with every field proved; the elaborator rejects an omitted law exactly as it does for a law in the operational class (first negative fence below).
4. The laws are relative to the order supplied to the mixin (`[Preorder α]`). When the claim concerns an existing order, the interface MUST use that order or provide checked correspondence to it. This example takes the order as a parameter so the operations do not select a different relation. Bundled order hierarchies are also valid. Avoid competing instance paths that silently select a different order.

```lean
import Audit.Economy

/-- The claim names the mixin; the ℝ instance discharged every law from
Mathlib's lattice lemmas. -/
example : Economy.LawfulFlourishable ℝ := inferInstance

/-- Using a law requires the mixin in the binders. -/
example {α : Type} [Preorder α] [Economy.Flourishable α] [Economy.LawfulFlourishable α]
    (a b : α) :
    Economy.Flourishable.measure a ≤
      Economy.Flourishable.measure (Economy.Flourishable.enhance a b) :=
  Economy.measure_enhance_ge a b
```

For the order on `Bad` induced by its real field, subtraction violates `enhance_increases` and negation violates `measure_monotone`. The following fence checks that an instance omitting the required laws is rejected. Missing-field rejection alone does not prove that proposed laws are false.

```lean (fails := "Fields missing|fields missing")
import Audit.Economy

/-- A wrapper around a real number. -/
structure Bad where
  /-- The wrapped real number. -/
  x : ℝ

instance : Preorder Bad := Preorder.lift Bad.x

instance : Economy.Flourishable Bad where
  enhance := fun a b ↦ ⟨a.x - b.x⟩
  diminish := fun a b ↦ ⟨a.x + b.x⟩
  measure := fun a ↦ -a.x

-- The mixin instance is the lawfulness claim; it is refused without its proofs.
instance : Economy.LawfulFlourishable Bad where
```

And a law cannot be used from the operations alone:

```lean (fails := "failed to synthesize")
import Audit.Economy

/-- The mixin is not required, so the law is not available. -/
theorem le_enhance {α : Type} [Preorder α] [Economy.Flourishable α] (a b : α) :
    a ≤ Economy.Flourishable.enhance a b :=
  Economy.LawfulFlourishable.enhance_increases a b
```

## 3.2.4 Decidability: Logical vs Executable
%%%
tag := "324-decidability-logical-vs-executable"
number := false
%%%

*Rationale*: A proposition `p : Prop` states a property; it is not a proof or a decision procedure. `Decidable p` is data with two constructors: one carries a proof of `p`, the other a proof of `¬p`. A computable producer of that data gives an executable decision procedure. `Classical.propDecidable` supplies such data logically for any proposition, but is noncomputable and depends on `Classical.choice`.

A branch that affects runtime data needs a computable decision procedure. Classical reasoning may be used in erased proofs under an allowed foundation profile or in noncomputable logical definitions. Proof erasure and noncomputability do not prevent all logical reduction; they distinguish what must execute in compiled code. For example, this logical constructor uses noncomputable real order:

```lean
import Mathlib.Basic.NNReal.Defs

/-- Proof-producing logical admission; arbitrary real comparison is noncomputable. -/
noncomputable def mkResource? (c : ℝ) : Option NNReal :=
  if h : 0 ≤ c then some ⟨c, h⟩ else none
```

In contrast, the natural-number validator in {ref "11-the-principle-of-representational-precision"}[module 1 §1.1] is executable and produces a proof-bearing value.

*Example - A Predicate with an Executable Decision Procedure*:

```lean
import Mathlib.Data.List.Basic

/-- A proposition over natural-number arithmetic. -/
def HasQuorum (n : ℕ) (total : ℕ) : Prop :=
  2 * total < 3 * n

/-- A *computable* decision procedure for the predicate. -/
instance (n total : ℕ) : Decidable (HasQuorum n total) :=
  inferInstanceAs (Decidable (2 * total < 3 * n))

/-- The decision message; it branches on the predicate in computable code. -/
def quorumDecision (votes total : ℕ) : String :=
  if HasQuorum votes total then
    "Proceed with proposal"
  else
    "Insufficient votes"

-- The predicate is both logically precise and computationally usable
example : quorumDecision 7 10 = "Proceed with proposal" := rfl

/-- The contrast: `Classical.propDecidable` decides ANY proposition — but it
is noncomputable and choice-dependent. It licenses `if` in *proofs*,
never an executable decision. -/
noncomputable def classicalDecidable (p : Prop) : Decidable p := Classical.propDecidable p

-- 'classicalDecidable' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms classicalDecidable
```

*Rule*: A decision used in erased proof code must respect the claimed foundation profile. A decision used to select runtime data must have a computable producer. A `Decidable` type alone establishes neither executability nor foundation profile.

## 3.2.5 Proof Economy: Four Cost Domains and One Trust Question
%%%
tag := "325-proof-economy-four-cost-domains-and-one-trust-question"
number := false
%%%

*Rationale*: Proof cost has four distinct domains. A proof can be cheap in one and expensive in another. Soundness and foundation strength depend on the resulting term and its dependencies, not on its speed. Prefer the simplest proof of the same claim under the intended assumptions and foundation profile.

:::table +header
*
  * Domain
  * Cost
  * When it is paid
*
  * Elaboration and search
  * Tactic execution, unification, typeclass synthesis, and proof construction.
  * When the source is elaborated.
*
  * Proof artifact
  * Produced terms and auxiliary declarations, serialized size, and loading.
  * During storage and loading of imported artifacts.
*
  * Kernel checking
  * Type checking and the definitional reduction needed to accept the term.
  * When a declaration is kernel-checked, including fresh checks.
*
  * Native execution
  * Compiled code, including compiler replacements and external primitives.
  * When that code runs.
:::

* *Separate tactic reduction from kernel reduction.* In the examples below, structural `sumTo` unfolds for ordinary `decide`. The well-founded `sumWf` is irreducible at the elaborator’s default transparency, so ordinary `decide` fails. `decide +kernel` can ask the kernel to check by reduction. A tactic’s failure to unfold a definition is not evidence that the kernel cannot reduce it.
* *A small proof term can require substantial checking.* Reduction-based proofs such as `decide` and `rfl` may require the kernel to evaluate definitions in the goal. By default, `decide` also reduces its decision instance during elaboration. `+kernel` avoids that initial evaluation. Proof-producing tactics such as `simp`, `omega`, and `norm_num` can avoid replaying the target computation, but their costs depend on the goal and generated proof. No tactic name guarantees cheap checking.
* *Prefer reusable arguments when they eliminate repeated computation.* `two_mul_sumTo` proves the identity for every natural number by induction. Applying it avoids unfolding the recursive sum separately for each numeral. Reducing `sumTo n` traverses recursive cases. That observation alone is not a wall-clock complexity bound because arithmetic and checker overhead also cost time.
* *Inspect the elaborated recursion and its dependencies.* On this pin, `sumWf` uses `WellFounded.Nat.fix`. A general well-founded relation can use `WellFounded.fix` and an accessibility proof. The former uses recursion over a natural-number fuel bound. `#print` shows the actual construction. A definition’s transitive axiom set includes its body, termination proof, and selected instances. The `omega` proof in this particular `sumWf` contributes `propext` and `Quot.sound`. Do not assign a foundation profile from the recursion scheme or tactic name alone.
* *Compiler simplification preserves the logical definition.* The `@[csimp]` equality replaces compiled calls to `sumTo` with `closedSum`. It does not change the kernel reduction of `sumTo`. So it does not remove recursive computation from a `decide` proof about that definition (§3.6).
* *Native proof evaluation changes the trust account.* Ordinary `#eval` produces an observed result, not a theorem. `native_decide` uses a generated axiom to accept a compiled result. On this pin, the SAT path of `bv_decide` likewise uses native certificate checking. A goal closed by normalization alone may have no such axiom. Inspect the exact axiom set. These mechanisms are classified as compiler-trusting and excluded from conforming positive proof surfaces (§3.4).

*Example - Same Equations, Different Kernel Cost, Analytic Discharge*:

```lean
import Audit.Economy

open Economy

/-- Kernel reduction evaluates the structural recursion at 100. -/
example : sumTo 100 = 5050 := by decide

/-- Analytic discharge: one rewrite by the universal theorem, then
kernel-accelerated literal arithmetic. -/
example : sumTo 100 = 5050 := by rw [sumTo_eq_closedSum]; rfl

/-- The universal statement costs one induction for every `n`. -/
example (n : Nat) : 2 * sumTo n = n * (n + 1) := two_mul_sumTo n

/-- The well-founded twin agrees pointwise; the proof goes through its
equation theorem, the stable interface, rather than through transparency. -/
example : sumWf 100 = 5050 := by rw [sumWf_eq_sumTo]; decide

/-- Kernel replay of the well-founded definition is available; only the
elaborator's default-transparency reduction is not. -/
example : sumWf 10 = 55 := by decide +kernel

#print axioms sumTo   -- 'Economy.sumTo' does not depend on any axioms
#print axioms sumWf   -- 'Economy.sumWf' depends on axioms: [propext, Quot.sound]
```

The elaborator does not unfold the `@[irreducible]` well-founded definition at default transparency, so a plain `decide` fails before any kernel replay starts. This is an elaboration-domain failure, not a kernel fact. The preceding `decide +kernel` proves the same statement by kernel replay.

```lean (fails := "did not reduce to `isTrue` or `isFalse`")
import Audit.Economy

example : Economy.sumWf 10 = 55 := by decide
```

*Example - Same Statement, Different Trust*:

```lean +trustedCompiler
import Init

/-- Kernel-checked: `decide` produces a proof term the kernel re-checks. -/
theorem gcd_1071_462_kernel : Nat.gcd 1071 462 = 21 := by decide

/-- Compiler-trusting: `native_decide` trusts the compiled evaluation. -/
theorem gcd_1071_462_native : Nat.gcd 1071 462 = 21 := by native_decide

#print axioms gcd_1071_462_kernel
-- 'gcd_1071_462_kernel' does not depend on any axioms
#print axioms gcd_1071_462_native
-- The output includes a per-invocation `._native.native_decide` axiom;
-- inspect the printed name rather than relying on its generated suffix.
```

The second theorem relies on a compiler-generated axiom; it is a classified teaching example, not a conforming proof. The first theorem uses kernel reduction. Neither tactic choice alone states the cost or foundation of an arbitrary proof.

*Proof maintenance*: Economy over time comes from four habits, none of which is a global tactic, style, or import mandate. State theorems against stable, elaborated interfaces (the API the definition exports, not its unfolded internals) so a representation change doesn't reopen every proof. Keep hypotheses local as binders rather than as global instances or options. Use automation intentionally: where the produced term matters for replay or readability, name the lemmas the automation may use; where it does not, closing the goal is enough. Match existing library abstractions ({ref "14-principled-mathematical-modeling"}[module 1 §1.4]) so their theorems, instances, and simp sets do the work instead of bespoke ones.

*When cost cannot be derived*: The examples above explain which computations a proof requires; they do not establish timings. If a remaining performance decision needs measurement, first state why derivation does not settle it, the smallest informative comparison, the pinned inputs, the decision criterion, and a resource budget. Report run-to-run uncertainty when it affects the decision. A profiler observation concerns the toolchain and machine; it does not establish correctness or foundation strength ({ref "9-compliance-and-quality-audit"}[module 9]).

# 3.3 Elaboration-Time Verification
%%%
tag := "33-elaboration-time-verification"
number := false
%%%

*Requirement*: Express the properties an interface enforces in its types and proof obligations, and ensure the resulting terms are kernel-checked. Elaboration constructs those terms and reports unsolved obligations. This checks the program’s reasoning before execution; validating runtime inputs may still require runtime computation.

*Strategies*:

1. *Dependent Return Types*: Functions return proofs along with values.
2. *Propositions as Types*: Encode requirements in type signatures.
3. *Indexed Bounds*: Use types such as `Fin n` to require evidence of a bound; `n` and the index may be runtime inputs.
4. *Witness Types*: Return evidence of properties, not just boolean checks.

*Example - Proof-Requiring Interfaces* (these definitions use computable operations):

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Vector.Basic

/-- Return a value with its proof of property. -/
def findPositive (l : List ℕ) : Option {x : ℕ // 0 < x ∧ x ∈ l} :=
  match hx : l.find? (0 < ·) with
  | none => none
  | some x =>
    have hp := List.find?_some hx
    some ⟨x, of_decide_eq_true hp, List.mem_of_find?_eq_some hx⟩

/-- Access requires an index whose bound has been established. -/
def safeGet {α : Type} {n : ℕ} (v : Vector α n) (i : Fin n) : α :=
  -- The index carries the proof `i.val < n`; this is an API claim, not a runtime-cost claim.
  v.get i

/-- Witness-bearing comparison. -/
inductive CompareResult (a b : ℕ) : Type
  /-- `a` is less than `b`. -/
  | lt (h : a < b) : CompareResult a b
  /-- `a` equals `b`. -/
  | eq (h : a = b) : CompareResult a b
  /-- `a` is greater than `b`. -/
  | gt (h : b < a) : CompareResult a b

/-- The comparison of `a` and `b`, with the proof of the relation that holds. -/
def compare (a b : ℕ) : CompareResult a b :=
  if h : a < b then .lt h
  else if h : a = b then .eq h
  else .gt (by omega)

/-- Type-level state machine whose invalid transitions are type errors. -/
inductive State : Type
  /-- Waiting to start. -/
  | ready
  /-- Started and not yet finished. -/
  | running
  /-- Finished. -/
  | done

/-- The allowed transitions between states; a missing edge has no constructor. -/
inductive ValidTransition : State → State → Type
  /-- Start a ready machine. -/
  | start : ValidTransition .ready .running
  /-- Finish a running machine. -/
  | finish : ValidTransition .running .done
  /-- Reset a finished machine. -/
  | reset : ValidTransition .done .ready

/-- The target state of an allowed transition. -/
def transition {s₁ s₂ : State} (_ : ValidTransition s₁ s₂) : State := s₂

/-- There is no direct transition from ready to done in this relation. -/
example (t : ValidTransition .ready .done) : False := nomatch t
```

In `findPositive` and `compare`, the search or comparison still executes when the inputs arrive at runtime; the proof fields are erased. `findPositive`’s return type establishes soundness of a successful result but does not promise success whenever the list contains a positive value. Likewise, `ValidTransition` describes allowed edges; it does not require callers to use the latest state.

# 3.4 Foundation Strength: Axioms Are Reported, Never Assumed
%%%
tag := "34-foundation-strength-axioms-are-reported-never-assumed"
number := false
%%%

*Requirement*: A conforming proof surface contains no project logical `axiom` declarations and no `sorry`, `admit`, or transitive dependence on `sorryAx`. Domain assumptions are explicit parameters, hypotheses, or proof-bearing fields. Lean 4 has no `constant` command. Implemented `opaque` declarations are classified separately (§3.6).

What a theorem _does_ transitively use of Lean's standard logical axioms is not hidden: it is reported, exactly, per declaration. The report is a dependency statement, not a quality ranking ({ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5]).

```lean
import Mathlib.Tactic.NormNum

/-- A small arithmetic fact, proved by `norm_num`. -/
theorem Nat.one_add_one_eq_two : (1 : ℕ) + 1 = 2 := by norm_num

-- The output is exactly this theorem's slice of the trusted base:
#print axioms Nat.one_add_one_eq_two
-- 'Nat.one_add_one_eq_two' depends on axioms: [propext]
```

* *Foundation profiles* — kernel-only, choice-free, standard-logical — are defined precisely in {ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5]. The repository's gate ({ref "85-proof-completeness-and-foundation-strength"}[module 8 §8.5]) computes each declaration's exact transitive axiom set and its profile mechanically, including through Mathlib dependencies.
* Compiler-trusting proof mechanisms generate axioms outside the permitted standard logical set. They are classified separately and rejected from conforming positive surfaces. They are never folded into a foundation label ({ref "85-proof-completeness-and-foundation-strength"}[module 8 §8.5]).

# 3.5 Theorems Worth Proving
%%%
tag := "35-theorems-worth-proving"
number := false
%%%

*Principle*: Prove the theorems the development’s claims need. Explain each theorem’s mathematical purpose or intended use in its docstring. An unresolved obligation must remain explicitly open or conditional; it must not appear as a completed theorem with `sorry` or `admit`. Whether proof terms are erased during compilation is a separate question.

*Documentation pattern*: State why the result matters, its assumptions, and the exact conclusion. For example, `runChecked_compose_success` in §3.7 explains how a successful prefix supplies the state its suffix requires. Its theorem names the actual runner and the hypotheses under which the composition succeeds.

It is acceptable to defer a theorem when no current claim needs it. Its statement may remain as an explicitly open `Prop` definition or a hypothesis in a conditional result (§3.10); it must not be presented as proved.

# 3.6 Contracts for Executable and Effectful Mechanisms
%%%
tag := "36-contracts-for-executable-and-effectful-mechanisms"
number := false
%%%

*Requirement*: Every material behavior claimed for an owned executable component has explicit contracts checked against its actual Lean definitions. Each contract states exactly the guarantee its mechanism provides on the pinned toolchain. Executable partiality, logical opacity, and unsoundness are different properties and MUST NOT be conflated.

*What each mechanism guarantees on the pinned toolchain*:

* *Total definitions*, including recursion accepted by structural or well-founded termination checking: kernel-checked definitions, total in Lean's logic, open to equational reasoning. Termination-as-checked is not a complexity bound and not a runtime guarantee (§3.2.1).
* *Noncomputable definitions*: code generation is omitted for these declarations; the modifier adds no logical axiom by itself. A noncomputable reference alone supplies no executable witness. An executable implementation or compiled caller may be related to that reference by checked correspondence, while replacement and external execution retain their stated trust boundaries (§3.2.4).
* *Pure monadic code* (`StateM`, `ReaderT`, `Except`, ...): ordinary total functions; proofs reason by ordinary reduction (example below).
* *`IO` and runtime execution*: an `IO α` value is a program description run by Lean's runtime. Lean theorems cover the pure core and relations between programs; a theorem about a program or effect model does not by itself establish what happens in the outside world. A conforming executable claim names the split (example below).
* *`partial`*: executable recursion without a kernel termination proof. The logical-facing declaration is opaque (`#print` shows `opaque f`; the kernel does not unfold calls) and the mechanism introduces no new logical axiom; dependencies of its type and implementation still require inspection. Opacity is not unsoundness, and an opaque constant proves nothing about its own executions. `partial` is excluded from conforming proof surfaces ({ref "86-classify-lean-computation-mechanisms-exactly"}[module 8 §8.6]).
* *`partial_fixpoint`* (present on the pinned toolchain): a termination clause that, for supported result domains and with checked monotonicity in recursive calls, accepts a potentially non-terminating recursive equation as a safe `def`, generating one-step unfolding theorems (`f.eq_def`) from a choice-dependent fixpoint construction. The definition is logically sound within the standard axioms, but kernel reduction does not follow the recursive equation; proofs use the generated equations. Its execution may not terminate. This mechanism is outside the current conforming recursion surface: its generated partial helper does not meet the structural or well-founded authentication required by {ref "84-inventory-every-owned-declaration"}[module 8 §8.4]. This restriction is a standard/checker policy, not a claim of logical unsoundness.
* *`unsafe`*: excluded from safe kernel declarations — the kernel rejects a safe declaration that references it — and intended for compiled execution; excluded from conforming proof surfaces ({ref "86-classify-lean-computation-mechanisms-exactly"}[module 8 §8.6]).
* *`@[implemented_by]`*: kernel reasoning uses the reference definition while compiled execution runs the replacement. The correspondence is checked only when a Lean theorem states it (`f = g`, or pointwise, e.g. `∀ xs, f xs = g xs`); otherwise the replacement is a trusted boundary.
* *`@[csimp]`*: prefer this proof-backed optimization when the pinned compiler's supported constant-equality form fits. An unconditional equality `@reference = @replacement` lets compilation replace occurrences without changing kernel reduction. The equality relates the Lean constants; it does not verify an extern, unsafe implementation, or further replacement reached from the target. Imported and chained transformations belong in the separate execution account (§8.6), including choices subsequently overwritten or scoped away. The attribute acts only in the compiler: kernel reduction, `decide` cost, and the logical definition the theorems are about are unchanged (§3.2.5).
* *`@[extern]` / FFI*: executed behavior comes from external code the Lean declaration does not establish — always a trusted boundary. Primitives resolved from the pinned toolchain's `Init` modules (for example `Float` arithmetic) are the standard runtime's own trusted base; they are reported as what they are, neither confused with project externs nor presented as kernel-checked correspondence.

*Continuing services and streams*: A continuing service is not required to terminate, and its safety contract does not ask it to. Conforming forms include invariant preservation over arbitrary finite execution prefixes and partial correctness (every produced result satisfies the postcondition). Both are statable over total definitions, as the example below shows. Termination, productivity, progress, and liveness are distinct claims. When claimed, each carries its own stated hypotheses (scheduling or fairness assumptions as explicit parameters) and is never read out of a safety theorem.

*Metaprograms*: A metaprogram has two distinct objects: the terms it produces, which the kernel checks independently of how they were generated, and the producer's own behavior (which declarations it emits, which goals it closes), which kernel checking of the products does not establish. A sound resulting proof does not prove the producer correct. Claims about the producer are executable Lean definition claims with their own contracts.

*Models of effects*: proofs about models of effects — a modeled file system, a modeled network — are theorems about the model, distinct from guarantees about the external world. Assumptions are explicit parameters, hypotheses, or proof-bearing interfaces (§3.4), never project logical axioms.

*Checker alignment*: Foundation labels report transitive logical axiom dependencies ({ref "45-foundation-strength-kernel-only-choice-free-standard-logical"}[module 4 §4.5]). The declaration gate separately computes an execution-coverage account for each owned executable root using the conservative closure defined in {ref "8-tooling-and-machine-audit"}[module 8]. That account distinguishes retained execution edges, candidate transformations, and checked, trusted, or unresolved boundaries. A logical profile pass is not an execution guarantee: an unresolved boundary blocks the affected execution claim, and a trusted boundary must not be presented as unconditionally checked.

*Example — Proof-Backed Compiler Optimization*:

```lean
import Init

/-- A reference convenient for stating a property. -/
def referenceStep (n : Nat) : Nat := 1 + n

/-- A different executable definition with the same result. -/
def replacementStep (n : Nat) : Nat := n + 1

/-- Exact function equality; no additional premises or native evaluation. -/
@[csimp] theorem referenceStep_eq_replacementStep : referenceStep = replacementStep :=
  funext fun n => Nat.add_comm 1 n

/-- Subsequent compilation can use the replacement. -/
def nextStep (n : Nat) : Nat := referenceStep n
```

This theorem proves function equality for every `Nat`, using `funext` and `Nat.add_comm`. It does not establish a speed improvement. Both definitions use trusted native natural-number arithmetic when compiled.

*Example - Pure Monadic Code Reasons by Ordinary Reduction*:

```lean
import Mathlib.Data.Nat.Basic

/-- Increment-and-report over pure state. -/
def tick : StateM ℕ ℕ := do
  let s ← get
  set (s + 1)
  pure s

/-- The computation unfolds by ordinary reduction. -/
example : tick 0 = (0, 1) := rfl
```

*Example - Safety Over Arbitrary Finite Prefixes* (a continuing service):

The authoritative definitions and universal proofs are in {repo "lean/Audit/Server.lean"}[`lean/Audit/Server.lean`]. `Glossary.Server` carries `served ≤ cap`; `init` constructs an idle value for every capacity, and `validate` admits exactly valid raw counts. Its public constructor requires the same proof, so it enforces validity without claiming construction is exclusive to `validate`.

```lean
import Audit.Server
open Glossary

/-- Initialization establishes the bound by construction, for any capacity. -/
example (cap : Nat) : (Server.init cap).served = 0 ∧ (Server.init cap).cap = cap :=
  ⟨rfl, rfl⟩

/-- The actual update supplies the new proof at the write boundary. -/
example (s : Server) : s.step.served =
    if s.served < s.cap then s.served + 1 else s.served := Server.step_served s

/-- A frame property is separate from the intrinsic bound. -/
example (s : Server) : s.step.cap = s.cap := Server.step_cap s

/-- Every finite prefix stays within the starting capacity. -/
example (n : Nat) (s : Server) : (Server.run n s).served ≤ s.cap :=
  Server.run_bounded n s

/-- The shell describes an output action; terminal effects remain trusted. -/
def Server.announce (s : Server) : IO Unit :=
  IO.println s!"served {s.served} of {s.cap}"
```

`run_bounded` combines the output proof field with `run_cap`, proved by induction over `run`. It covers every `n : Nat` and admitted `s : Server`, including values constructed directly with a proof. `step_served` establishes the exact increment/refusal behavior; the bound alone would also allow an idle implementation. These theorems do not establish liveness, productivity, external service behavior, or a rule requiring callers to use the latest state. Reusing a saved immutable value is well-typed. Any stronger usage guarantee must be proved over the actual transition or trace semantics. Each finite `run` is total; it is not a whole-process termination claim.

Direct invalid construction and an invalid update both fail at their proof obligation:

```lean (fails := "Tactic `decide` proved that the proposition")
import Audit.Server

/-- Attempt to build a server that has served more than its capacity. -/
def invalid : Glossary.Server := ⟨1, 0, by decide⟩
```

```lean (fails := "Tactic `decide` proved that the proposition")
import Audit.Server

/-- Attempt to update a server past its capacity. -/
def invalidUpdate : Glossary.Server :=
  { Glossary.Server.init 0 with served := 1, bounded := by decide }
```

Raw counts also cannot be passed directly to the admitted-state API:

```lean (fails := "Application type mismatch|is expected to have type")
import Audit.Server

/-- Attempt to step a raw pair as if it were a server. -/
def rawCrossUse (raw : Nat × Nat) : Glossary.Server := Glossary.Server.step raw
```

# 3.7 A Compositional Method for Complete Program Contracts
%%%
tag := "37-a-compositional-method-for-complete-program-contracts"
number := false
%%%

A type invariant describes valid results; a functional contract also relates them to the input. For each owned component, state the intended relation before selecting proof tools. The obligations below apply to material claims about that component, not to unrelated mathematical definitions or every implementation helper.

:::table +header
*
  * Boundary
  * Required contract
*
  * Pure total function
  * State the exact input domain, any precondition, and the input–output relation. A restricted domain MUST appear in the API when promised (§3.2.1).
*
  * Parser, decoder, admission
  * Prove accepted-result soundness and input meaning. State and prove rejection behavior and any normalization/default policy. If the API promises success on a class of inputs, prove that completeness; a conditional soundness theorem alone does not deliver it.
*
  * Update
  * Establish the invariant at the write boundary, the intended change, and frame conditions for components promised unchanged.
*
  * Composition
  * Show that intermediate postconditions supply subsequent preconditions. State and prove the chosen state/error semantics, including what state an error exposes and whether the continuation runs.
*
  * Fold or loop
  * Prove the promised relation to the processed input. An inductive invariant is a common method: establish it initially, preserve it at each step, and derive the final relation. Reuse a library theorem or another checked argument when it already proves the claim. Separate partial correctness from termination/total correctness.
*
  * Effect interpretation
  * Keep a pure immutable core with an explicit interpreter/IO shell where pragmatic. Identify the actual proved definitions and modeled relation, and the external runtime assumptions at each crossed boundary (§3.6).
:::

Every required relation MUST be proved about the actual definitions used by the application (or transferred through exact checked correspondence). Reuse proof-bearing construction and library lemmas; do not create a parallel implementation and assume equivalence. A finite fold is total in Lean's logic; arbitrary finite-prefix safety for a continuing service does not assert process termination, progress, fairness, or liveness.

*Why the invariant is insufficient.* This always-rejecting implementation satisfies its refined return type but violates positive-input completeness:

```lean
/-- Every possible successful result would be positive, but there are none. -/
def rejectAll : Nat → Option {n : Nat // 0 < n} := fun _ => none

example : ¬ (∀ n, 0 < n → (rejectAll n).isSome = true) := by
  intro h
  have bad := h 1 (by decide)
  contradiction
```

The intended admission in {repo "lean/AuditApp/Limiter.lean"}[`lean/AuditApp/Limiter.lean`] instead has `admit_exact`. For every natural capacity, a positive input returns the idle state at exactly that capacity, and zero returns `none`. It performs no normalization. `admit_sound` alone would not exclude always rejecting or substituting a different positive capacity. At the CLI boundary, `requestedCapacity_exact` gives the separate policy: apply Lean's `String.toNat?` to the first argument, default to 2 on missing/unparsable input, and ignore trailing arguments; admission then rejects parsed zero. The parser's meaning is that pinned library definition, not a theorem about terminal input or an unspecified external encoding.

*Worked state/error program.* The limiter carries `inUse ≤ capacity`. Its `grant_some` and `grant_none` prove exact increment/frame and refusal behavior; `step_capacity` supplies the capacity frame for release and reset as well. `run_capacity` and `run_replicate_grant` retain the total fold's frame and exact successful-burst result. `run` keeps going after a refused grant. The strict `runChecked` instead sequences `checkedStep` with ordinary monadic bind and stops at the first refusal.

Its stack is `ExceptT Unit (StateM Limiter) Unit`, which runs as `Limiter → (Except Unit Unit × Limiter)`. State is returned on either outcome. A refused operation preserves its input state; earlier successful updates remain, and the suffix is not run (`checkedStep_exact`, `runChecked_cons`, `runChecked_error`). This is retention, not rollback to the script's initial state. Conversely, `StateT Limiter (Except Unit)` has result shape `Except Unit (α × Limiter)` and exposes no state on error; that type alone would not specify an application's recovery policy or undo external effects.

`Fits ops l` states that every grant has space at the state reached by its preceding operations, using the total `step`. `runChecked_success` is an equivalence: success occurs exactly for a fitting script, and its returned state equals `run ops l`. The successful prefix invariant is `Fits prefix initial ∧ current = run prefix initial`. `runChecked_append` threads that current state to the suffix on success, or retains the prefix error/state; `runChecked_error` identifies the successful prefix immediately before the first full grant. `runChecked_capacity` frames capacity in both cases, so the returned state's intrinsic bound is also relative to the original capacity.

```lean
import AuditApp.Limiter
open AuditApp

/-- Positive admission allows a real grant, universally over positive capacities. -/
example (cap : Nat) (h : 0 < cap) :
    Fits [.grant] ⟨cap, 0, Nat.zero_le cap⟩ := ⟨fun _ => h, trivial⟩

/-- The intermediate post-state is the input to the next script's precondition. -/
example (xs ys : List Op) (l : Limiter)
    (hx : Fits xs l) (hy : Fits ys (run xs l)) :
    runChecked (xs ++ ys) l = (.ok (), run ys (run xs l)) :=
  runChecked_compose_success xs ys l hx hy

/-- Error exposes exactly the successful prefix before a full grant. -/
example (ops : List Op) (l final : Limiter) :
    runChecked ops l = (.error (), final) ↔
      ∃ before after, ops = before ++ .grant :: after ∧
        Fits before l ∧ final = run before l ∧ final.inUse = final.capacity :=
  runChecked_error ops l final
```

`executeChecked_exact` composes admission with this runner. `Main` passes `required_contracts` to `executeChecked`, so required admission, update, input policy, success/refusal, and composition propositions are proof obligations about the same core it calls (§8.5). The shell describes success/refusal output using the returned result and state. The proofs do not establish terminal effects, native arithmetic correctness, complexity, empirical benefit, or external liveness. The default demonstration reaches a refusal; `AuditApp.demo_checked_error` derives its stopped state from the universal contract.

*Choose the smallest proof interface.* The pinned Lean 4.34.0 library provides `Std.Do.Triple` (precondition entails weakest precondition), `Std.Do.Triple.bind` for composition, `WPMonad` instances for `StateT`/`ExceptT`, and `Std.Tactic.Do`'s `mvcgen`. Use these when they simplify verification conditions; no tactic is mandatory. This example reuses the standard transformers and proves exact outcome equations by reduction and list induction, avoiding an additional predicate-transformer encoding of the same equations. For a larger monadic program, `Triple.bind` connects the first result's postcondition to the continuation's precondition while retaining explicit exceptional postconditions.

Local `let mut`, a `for` loop, or an efficient array representation does not itself imply external effects or `unsafe` execution. Inspect the elaborated total function and prove its relation; efficient representations remain permitted with their boundary/correspondence proofs. For example, local rebinding below denotes a pure function for every `Nat`:

```lean
/-- Local syntax, immutable mathematical input/output semantics. -/
def incrementLocal (n : Nat) : Nat := Id.run do
  let mut current := n
  current := current + 1
  return current

example (n : Nat) : incrementLocal n = n + 1 := rfl
```

# 3.8 Delivering Executable Witnesses with Required Evidence
%%%
tag := "38-delivering-executable-witnesses-with-required-evidence"
number := false
%%%

When an API promises to produce a witness or make a decision at runtime, it MUST supply an executable definition and the required relation about that same definition. A theorem `∃ y, R x y` establishes existence in Lean's logic; it does not by itself deliver executable data. Existential mathematical theorems remain legitimate. Likewise, a `Decidable` argument used for execution must have a computable producer (§3.2.4).

The public `Regula.Contract` import provides `ExecutableContract f R : Prop`, whose `evidence` field requires exactly `R f`. Its `run` requires that evidence and reduces to `f` (`ExecutableContract.run_eq`); compilation erases the proof. An application can use this interface or a richer one such as `AuditApp.RequiredContracts`.

Contract adequacy remains semantic. Replacing a required relation with `fun _ => True` loses that requirement. By contrast, a dependent function type may already enforce the entire intended relation: every `f : (n : Nat) → {m : Nat // m = n + 1}` supplies the stated successor property. Such evidence by construction is sufficient for that claim. Require additional input, success/refusal, frame, or composition relations only where the intended behavior needs them (§3.7).

An executable may have a classical correctness proof under Standard-Logical. Proof erasure does not turn its runtime data into a noncomputable construction:

```lean
import Regula.Contract

/-- The successor of a natural number. -/
def successor (n : Nat) : Nat := n + 1

/-- `successor` returns `n + 1` for every `n`, proved classically for illustration. -/
theorem successor_contract : Regula.ExecutableContract successor
    (fun f => ∀ n, f n = n + 1) :=
  ⟨Classical.byContradiction (fun h => h (fun _ => rfl))⟩

/-- `successor`, run through its registered contract. -/
def next (n : Nat) : Nat := successor_contract.run n

/-- info: 'successor_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms successor_contract

example (n : Nat) : next n = n + 1 := rfl
```

The classical proof here deliberately illustrates the distinction; the direct proof `⟨fun _ => rfl⟩` is simpler. The shipped {repo "examples/build-lint/Widget.lean"}[standalone adopter] uses that direct proof and selects Kernel-only. Its ordinary `lake build` also inspects registered executable roots, the selected transitive foundation profile, and execution boundaries ({ref "812-opt-in-enforcing-build-linter"}[§8.12]).

Omitting evidence while keeping the requirement fails at the proof-bearing field:

```lean (fails := "Fields missing.*evidence")
import Regula.Contract

/-- The successor of a natural number. -/
def successor (n : Nat) := n + 1
theorem missing : Regula.ExecutableContract successor
    (fun f => ∀ n, f n = n + 1) where
```

Existence evidence cannot fill a promised data result:

```lean (fails := "Type mismatch")
theorem exists_eq_add_one (n : Nat) : ∃ m : Nat, m = n + 1 := ⟨n + 1, rfl⟩
/-- Attempt to compute a successor from the existence proof alone. -/
def promised (n : Nat) : {m : Nat // m = n + 1} := exists_eq_add_one n
```

Using choice to extract the data makes it a noncomputable specification instead:

```lean (fails := "noncomputable")
/-- Attempt to compute a successor by choosing a witness of its existence. -/
def promised (n : Nat) : Nat :=
  Classical.choose (show ∃ m : Nat, m = n + 1 from ⟨n + 1, rfl⟩)
```

Marking that definition `noncomputable` permits the logical definition; it does not deliver the executable promise. The build linter rejects a registered noncomputable root even under Standard-Logical. Conversely, classical evidence alone does not reject a computable root. Neither a successful build nor a Choice-Free label proves kernel normalization, witness extraction from arbitrary existence theorems, compiler correctness, or native/FFI behavior.

# 3.9 Stateful Refinement and Finite-Prefix Safety
%%%
tag := "39-stateful-refinement-and-finite-prefix-safety"
number := false
%%%

A stateful safety transfer MUST identify the concrete and abstract semantics, the initial conditions, and the checked correspondence that transfers the claimed property. The forward-simulation method below uses state domains `C` and `A`, step relations, an abstract invariant, and a relation `R : C → A → Prop`. Other checked transfer arguments may use different obligations; they must still establish the stated claim.

For this method, prove initialization, abstract invariant preservation, and that the invariant together with `R` implies the concrete property. Its simulation hypothesis covers *every* related pair and *every* concrete successor: `R c a → StepC c c' → ∃ a', StepA* a a' ∧ R c' a'`. The abstract successor is existential, even when the abstract system is nondeterministic; this is neither reverse simulation nor equivalence of behaviors.

Define `StepA*` explicitly. Here it is Mathlib's `Relation.ReflTransGen StepA`: zero steps (`refl`), or a finite path extended by one edge (`tail`). Zero steps permit stuttering. {repo "lean/AuditApp/Refinement.lean"}[`AuditApp.Refinement.finite_transfer`] proves the reusable transfer by induction over `ReflTransGen StepC`: given a related initial pair and the initial abstract invariant, each finite concrete path ends at a state with a reachable abstract witness, the relation, the abstract invariant, and the concrete safety property. Its types and relations are parameters; it assumes neither deterministic transitions nor an executable procedure that selects matching abstract paths. The caller supplies initialization; it is not silently assumed to exist.

The concrete step MUST be the actual executable definition or have exact checked correspondence to it. If you claim observable agreement, state the observations and prove that agreement at the promised granularity. Matching endpoints after several abstract steps does not establish equality of intermediate observations or labeled traces.

*Worked limiter refinement.* The authoritative instance is {repo "lean/AuditApp/Refinement.lean"}[`lean/AuditApp/Refinement.lean`], reusing {repo "lean/AuditApp/Limiter.lean"}[`lean/AuditApp/Limiter.lean`] without another interpreter:

:::table +header
*
  * Object
  * Exact meaning
*
  * Concrete state `c : Limiter`
  * Natural `capacity`, natural `inUse`, and intrinsic `inUse ≤ capacity`.
*
  * Abstract state `a : Nat`
  * Free slots; `Inv cap a` is `a ≤ cap`. Raw numbers are a convenient relational domain; the bound holds for reachable states, not all natural numbers.
*
  * `R cap c a`
  * `c.capacity = cap ∧ c.inUse + a = cap`. It fixes capacity and relates occupied to free slots.
*
  * `StepA cap a a'`
  * Either `0 < a ∧ a' = a - 1`, or `a < cap ∧ a' = a + 1`. Both choices may be enabled.
*
  * `StepC c c'`
  * `∃ op, c' = AuditApp.step c op`, using the existing executable dispatcher.
*
  * Initialization
  * `initial_related` proves `R cap c cap ∧ Inv cap cap` whenever actual `admit cap = some c`. `admit_exact` establishes that this occurs for every positive capacity.
*
  * Preservation and simulation
  * `preserve` covers both abstract edges; `simulation` covers every related pair and concrete edge. Grants consume one free slot; releases return one; refused grants and idle releases stutter; reset uses `free_to_capacity`, a finite sequence of releases.
*
  * Transfer and observations
  * `sound` gives `c.capacity = cap ∧ c.inUse ≤ cap`; `observations` gives `(c.capacity, c.inUse) = (cap, cap - a)` at related endpoints.
:::

The intrinsic bound already guarantees valid concrete values. The refinement adds the fixed-capacity relation and a matching abstract path. Indeed, this particular `R` already implies the concrete bound; `sound` retains the invariant premise to instantiate the general method, without pretending that premise is necessary here. Abstract initialization and preservation remain separately proved. Natural subtraction truncates at zero: the positive allocation guard and the relation justify the decrement, and `observations` derives its subtraction equation from the sum relation. All counts are unbounded Lean naturals; no fixed-width wrapping or real-number approximation is assumed.

```lean
import AuditApp.Refinement
open AuditApp AuditApp.Refinement

/-- Non-vacuity: every positive capacity admits the stated initial pair. -/
example (cap : Nat) (h : 0 < cap) :
    admit cap = some ⟨cap, 0, Nat.zero_le cap⟩ := by
  rw [admit_exact, ite_eq_left h]

/-- Universal simulation, with an existential finite abstract match. -/
example (cap a : Nat) (c c' : Limiter) (hr : R cap c a) (hs : StepC c c') :
    ∃ a', Relation.ReflTransGen (StepA cap) a a' ∧ R cap c' a' :=
  simulation hr hs

/-- Every finite prefix, including refusal, has an abstract witness and is safe. -/
example (cap : Nat) (c : Limiter) (h : admit cap = some c) (ops : List Op) (n : Nat) :
    ∃ a, Relation.ReflTransGen (StepA cap) cap a ∧
      R cap (runChecked (ops.take n) c).2 a ∧ Inv cap a ∧
      ((runChecked (ops.take n) c).2.capacity = cap ∧
        (runChecked (ops.take n) c).2.inUse ≤ cap) :=
  prefix_safe h ops n
```

`reachable_safe` covers every finite concrete path, not a selected set of scripts or a bounded search. `run_path` links the total fold to those paths; `runChecked_path` uses the strict runner's exact state/error equation, including retained state on refusal. `prefix_safe` specializes transfer to every `ops : List Op` and `n : Nat`; taking beyond the list length selects the whole list. The existing `executeChecked_exact` connects positive admission to that same strict runner used by `Main`. This refinement observes only the returned capacity and occupancy; the runner's success/error contract remains §3.7, and terminal effects remain trusted.

A safety transfer MUST NOT be read as progress, fairness, productivity, termination of a continuing process, or liveness. Unlimited stuttering or starvation can preserve safety; any such additional claim needs its own explicit hypotheses and proof. Totality of each finite Lean runner does not establish a matching infinite abstract execution with progress. Theorems about these Lean definitions also do not verify their compiled natural arithmetic, code generation, runtime, external adapters, or scheduling (§3.6).

# 3.10 Research Statements: Adequacy, Conditional Completeness, and Open Targets
%%%
tag := "310-research-statements-adequacy-conditional-completeness-and-open-targets"
number := false
%%%

A kernel-checked proof establishes its elaborated proposition under its explicit hypotheses and transitive axiom dependencies. It establishes nothing about whether that proposition faithfully encodes the intended mathematical problem. A research formalization, a conjecture, a reduction, or a proof-challenge submission therefore carries four separate questions, and a conforming development keeps them separate:

:::table +header
*
  * Question
  * What settles it
*
  * *Statement adequacy*
  * An independent mathematical read-back of the elaborated declaration against the source mathematics (below). Not a kernel result.
*
  * *Exact formal truth*
  * The kernel-checked proof of the elaborated statement, with its exact axiom report (§3.4).
*
  * *Conditional completeness*
  * A theorem `H → C` is complete when `C` is proved from `H`; it claims the implication and nothing about `H`'s inhabitance.
*
  * *Open target*
  * A `Prop`-valued definition, or an unproved binder, that no declaration on the conforming surface claims to prove. Never labeled proved.
:::

*Read-back.* Before a formal statement is presented as the intended problem, the elaborated declaration MUST be read back into mathematics independently of the prose that motivated it. Inspect, in the elaborated term rather than the source text: quantifier order and dependence; implicit parameters and universe levels; every consequential definition the statement unfolds to (a Mathlib predicate may carry a side condition the informal statement omits, or omit one it assumes); notation, coercions, and the instances actually selected; totalized operations and domain restrictions (§3.2.1); and whether the statement asserts existence, construction, uniqueness, or a complexity bound, since these are distinct propositions. The Lean declaration remains the object proved; when the read-back and source disagree, the statement is inadequate even if the proof is valid. This is a semantic review of one declaration, not a provenance record.

*Non-vacuity is relative to the claim* ({ref "the-necessary-dual-non-vacuity"}[module 0]). A claimed admitted state, unconditional existence, or reachability requires its stated inhabitance, joint-satisfiability, or reachability proof. A deliberately conditional theorem, a contradiction argument, or a minimal-counterexample lemma claims only its implication and MUST NOT be rejected for lacking an inhabitant of its antecedent: a restriction on a hypothetical odd perfect number does not require first proving that one exists. The review question is which claim the prose makes, not whether every hypothesis has a witness. If the development establishes `¬H`, then `H → C` is vacuously true for any `C`. State that fact when it affects the interpretation; do not present the implication as evidence that `H` is inhabited or that `C` holds unconditionally. Such implications remain valid and may serve as contradiction steps, boundary cases, or reusable logical lemmas.

*Open targets and reductions.* An open question MAY be stated as a `Prop`-valued definition. A reduction `H₁ → H₂ → Goal` MAY be a complete theorem without proving `Goal` unconditionally. Assumptions stay in binders or proof-bearing fields; they MUST NOT become project axioms, `sorry`, or `admit` (§3.4), and an unresolved target MUST NOT be described as proved, closed, or established. The conforming surface may contain the conjecture’s statement and conditional theorems without containing a proof of the conjecture.

*External platforms.* A proof platform's open cards, sketches, and accepted results are distinct from conformance under this standard. An intentionally incomplete sketch or adapter MUST stay outside every positive surface and outside the dependency closure of any declaration presented as closed ({ref "82-define-surfaces-through-lake-semantics"}[module 8 §8.2], {ref "810-dogfooding"}[§8.10]). Before reusing a platform-accepted result, state the exact elaborated type, toolchain, and foundation under which it was accepted; a result about another elaboration environment is a result about that environment (§8.1).

*Worked example.* {repo "lean/Audit/Research.lean"}[`lean/Audit/Research.lean`] states the existence of an odd perfect number as `Research.OddPerfectExists : Prop` and proves nothing about it unconditionally. Read-back of that definition: one existential over `ℕ`; `Odd n` is Mathlib's `∃ m, n = 2 * m + 1`; `Nat.Perfect n` is the proper-divisor sum equation _and_ `0 < n`. Positivity excludes `0` from `Nat.Perfect`, because the bare sum equation holds at `0` (`zero_sum_properDivisors`). For this odd-perfect target, however, `Odd.pos` already supplies positivity: `oddPerfectExists_iff_sum` proves that omitting that conjunct gives an equivalent target. The canonical `Nat.Perfect` definition is retained; the equivalence proves neither version of the target. `oddPerfect_nine_le` is a conditional restriction, `every odd perfect number is at least 9`, proved by a closed finite case analysis over `1`, `3`, `5`, `7` and Mathlib's `Nat.Prime.not_perfect`; it needs no witness. `not_oddPerfectExists_of_bound` is a complete reduction: an explicit upper bound plus a finite search below it refutes the target. `search_below_nine` discharges the search half at `9`; the bound half remains an open binder, so the goal remains open. `exists_even_perfect` shows the contrasting claim kind: an unconditional existence theorem, delivered with its witness `6`.

```lean
import Audit.Research
open Research

/-- Conditional completeness: the implication is proved for every `n`, with no
inhabitant of the antecedent required or supplied. -/
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) : 9 ≤ n ∧ ¬ IsPrimePow n :=
  ⟨oddPerfect_nine_le hodd hperf, Perfect.not_isPrimePow hperf⟩

/-- The reduction instantiated at `9`: the only remaining obligation is the
explicit bound hypothesis, which this example does not pretend to have. -/
example (hbound : ∀ n, Odd n → n.Perfect → n < 9) : ¬ OddPerfectExists :=
  not_oddPerfectExists_of_bound 9 hbound search_below_nine

/-- Unconditional existence still requires its witness. -/
example : ∃ n : ℕ, Even n ∧ n.Perfect := exists_even_perfect

/-- Quantifier order is part of the statement: the swapped form is false. -/
example : ¬ ∃ y : ℕ, ∀ x : ℕ, x < y := no_greatest_nat_swapped
```

A `Prop` target is not its own proof. Presenting the definition where a proof is required fails at the type level:

```lean (fails := "Type mismatch")
import Audit.Research

theorem claimed : Research.OddPerfectExists := Research.OddPerfectExists
```

Using `sorry` as the proof, or replacing the theorem with a project `axiom` declaration, elaborates but is rejected by the declaration gate and fence audit on a positive surface (§3.4, {ref "85-proof-completeness-and-foundation-strength"}[module 8 §8.5]). The declaration gate reports each `Audit.Research` declaration's exact axiom set within the surface's Standard-Logical claim; none includes `sorryAx` or a project axiom.

# Summary of Logic and Proof Patterns
%%%
tag := "summary-of-logic-and-proof-patterns"
number := false
%%%

Apply these patterns so that:

* Every material property presented as established has machine-checked evidence about the stated Lean objects.
* Proofs are structured for human comprehension.
* Types and proofs establish the reasoning before execution; runtime validation remains explicit.
* Project axioms and holes are banned; Lean's standard logical axioms are reported exactly.
* Executable and effectful mechanisms carry exact contracts — proved properties, stated hypotheses, and honestly classified trusted boundaries; a logical label is not an execution guarantee.
* Research statements separate adequacy, exact truth, conditional completeness, and open targets: a conditional theorem needs no antecedent witness, and an open `Prop` target is never a hole, an axiom, or a claimed proof.
* Proof cost is distinguished across elaboration, proof artifacts, kernel checking, and native execution; foundation and trust are reported from the actual dependencies.
* Safety theorems establish their exact properties about the stated Lean models or executable definitions.

The result is a development whose claims match its types and theorems, whose open obligations remain visible, and whose execution boundaries are explicit.
