import VersoManual
import RegulaExample

open Verso.Genre Manual RegulaExample

#doc (Manual) "2. Type Design Patterns" =>
%%%
tag := "2-type-design-patterns"
file := "2-type-design-patterns"
number := false
%%%

{pageAnchor}

# Overview
%%%
tag := "2-overview"
number := false
%%%

This section applies the principles from {ref "1-core-principles"}[module 1] through semantic types, proof-bearing values, phantom tags, and abstract models. Each pattern states which distinctions or properties its types enforce, and which claims require additional proofs.

# 2.1 Semantic Types (Typed Decoding Boundaries)
%%%
tag := "21-semantic-types-typed-decoding-boundaries"
number := false
%%%

*Pattern*: Every semantic distinction claimed to be enforced by Lean MUST be represented in the types or constructors used by the interface. State whether the representation restricts the possible values or makes a particular cross-use ill-typed. Meaning that exists only in strings or other shared primitive values is not a type-level distinction.

*Rationale*: When two semantic domains use the same `String` type, Lean accepts either value wherever a `String` is expected. A decoder can distinguish them by returning a domain-specific type. An enumeration serves a different purpose: its constructors restrict the vocabulary, but remain values of the same type.

*Implementation Strategy*:

1. Identify the distinctions the interface claims to enforce.
2. Use an enumeration for a closed vocabulary; use distinct types, indices, or refinements when the interface must reject particular cross-use. The enumeration alone does not establish that an operation is authorized.
3. Use smart constructors where validation is needed.
4. Decode raw strings into the semantic type at admission, and require that type downstream. Treat the decoder as the place where you establish validation. A result type alone does not specify how the decoder interprets, rejects, or normalizes input; claimed behavior needs a contract about that decoder ({ref "37-a-compositional-method-for-complete-program-contracts"}[§3.7]).

*Example - Entity Roles*:

```lean
import Audit.DocPrelude
open Glossary

/-- Closed vocabulary for the permission policy below. -/
inductive EntityRole
  /-- Submits proposals. -/
  | proposer
  /-- Reviews proposals. -/
  | reviewer
  /-- Observes without acting. -/
  | observer
  /-- Administers the system. -/
  | administrator
  deriving Repr, DecidableEq

/-- Permissions are derived from roles, not string parsing. -/
def EntityRole.canPropose : EntityRole → Bool
  | .proposer => true
  | .administrator => true
  | _ => false

/-- Whether the role permits reviewing. -/
def EntityRole.canReview : EntityRole → Bool
  | .reviewer => true
  | .proposer => true
  | .administrator => true
  | .observer => false

/-- Type-safe role assignment with no string parsing
(`Id`: wrap identifiers in a phantom-typed key per §2.3). -/
structure Entity where
  /-- The entity's tagged identifier. -/
  id : Glossary.Id Glossary.EntityTag
  /-- The assigned roles; use a set type (Std's `Std.HashSet`, or Mathlib's `Finset`
  with its richer API) once duplicates matter. -/
  roles : List EntityRole

/-- Compute whether any assigned role permits proposing. -/
def Entity.canPropose (e : Entity) : Bool :=
  e.roles.any (fun r ↦ r.canPropose)
```

All four constructors have type `EntityRole`. The type restricts role values to that vocabulary; the functions compute permission decisions. An operation requiring permission must either enforce that decision or require corresponding proof evidence. The enumeration alone does not prevent an unauthorized operation.

*Anti-Pattern to Avoid* when the interface claims role distinctions are type-enforced (this implementation elaborates, but its behavior depends on an unconstrained `String` rather than the closed `EntityRole` constructors, so the claimed type boundary does not exist):

```lean
import Init.Data.String.Search

/-- An entity whose role is an unconstrained string. -/
structure BadEntity where
  /-- An untyped identifier. -/
  id : String
  /-- The role as free text, such as `"proposer"` or `"reviewer"`. -/
  roleString : String

/-- Whether the role text contains the substring `"proposer"`. -/
def BadEntity.canPropose (e : BadEntity) : Bool :=
  e.roleString.contains "proposer"   -- substring search over an unconstrained value
```

# 2.2 Dependent Types for Invariants
%%%
tag := "22-dependent-types-for-invariants"
number := false
%%%

*Pattern*: Use dependent types, including `Subtype` (written `{x : T // P x}`), to bundle values with proofs. A subtype adds the predicate `P` to the underlying type `T`. Every value supplies evidence of that predicate, and the interface should state when later use depends on that evidence.

*Rationale*: Every value of `{p : Rat // 0 ≤ p ∧ p ≤ 1}` supplies a rational number and a proof of its bounds. Further properties may follow from those bounds, but reachability through a particular process or consistency with other quantities requires evidence of the corresponding relation. Documentation explains the predicate’s intended meaning and limits; it does not replace the proof ({ref "the-necessary-dual-non-vacuity"}[module 0: non-vacuity]).

*Implementation Strategy*:

1. Identify unary properties that must hold for every admitted value.
2. Use Lean's subtype notation `{x : T // P x}` to create refined types.
3. For complex invariants, use structures with proof fields.
4. Provide smart constructors that bundle values with their proofs.
5. Ensure admission and every update return refined types. Justified raw internal representations follow the verified-boundary alternative in {ref "11-the-principle-of-representational-precision"}[§1.1]. State and prove transition or history claims separately. Include initialization, preservation, and composition obligations where the claim requires them. A predicate about one admitted state alone does not establish those relations.

*Example - Core Refinement Patterns* (shared `Time` type: `import Audit.DocPrelude`, defined in {ref "41-numeric-representations-mathematical-and-machine-arithmetic"}[module 4 §4.1]):

```lean
import Audit.DocPrelude
open Glossary

/-- A rational probability reuses Lean's canonical `Subtype`: a rational in `[0, 1]`. -/
abbrev Probability : Type := {p : Rat // 0 ≤ p ∧ p ≤ 1}

/-- Smart constructor for probabilities. -/
def mkProbability (p : Rat) (h : 0 ≤ p ∧ p ≤ 1) : Probability := ⟨p, h⟩

/-- Non-vacuity: at least one probability exists. This proves inhabitance,
nothing stronger. -/
example : Nonempty Probability := ⟨mkProbability 0 (by decide +kernel)⟩

/-- Complement closure is proved once, from the bounds the argument carries. -/
def Probability.complement (p : Probability) : Probability :=
  ⟨1 - p.val, by have := p.property; grind⟩

/-- Valid identifier: non-empty, alphanumeric with underscores. -/
def ValidIdentifier := {s : String // 0 < s.length ∧ s.all (fun c ↦ c.isAlphanum || c = '_')}

/-- Time intervals with proven ordering (`Time`: `import Audit.DocPrelude`). -/
structure TimeInterval where
  /-- The start time. -/
  start : Time
  /-- The finish time. -/
  finish : Time
  /-- Proof field: the interval is ordered. -/
  valid : start ≤ finish

/-- Duration of an interval is provably non-negative. -/
def TimeInterval.duration (ti : TimeInterval) : {d : Rat // 0 ≤ d} :=
  ⟨ti.finish.val - ti.start.val, by
    have hv : ti.start.val ≤ ti.finish.val := ti.valid
    grind⟩

/-- Bounded collections with size guarantees. -/
def BoundedList (α : Type) (n : Nat) := {l : List α // l.length ≤ n}

/-- Adding requires proof we won't exceed bound. -/
def BoundedList.cons {α : Type} {n : Nat} (x : α) (bl : BoundedList α n)
    (h : bl.val.length < n) : BoundedList α n :=
  ⟨x :: bl.val, by
    simp only [List.length_cons]
    exact Nat.succ_le_of_lt h⟩
```

The rational `Probability` above is exact rational arithmetic, not a real interval: a real-valued probability reuses Mathlib's `unitInterval`, whose symmetry supplies the complement, and is checked as `MathlibModels.Probability` in the {repo "integration/mathlib/MathlibAudit/Models.lean"}[Mathlib integration package].

The shared glossary deliberately makes `Time` nominal while `ResourceAmount` reuses the canonical subtype of non-negative rationals. Although both expose non-negative rational values, direct cross-use is rejected:

```lean (fails := "Type mismatch|is expected to have type")
import Audit.DocPrelude

/-- Consume a resource amount. -/
def consume (_amount : Glossary.ResourceAmount) : Unit := ()

/-- Attempt to consume a time as a resource amount. -/
def wrongDomain (t : Glossary.Time) : Unit := consume t
```

# 2.3 Phantom Types for Disambiguation
%%%
tag := "23-phantom-types-for-disambiguation"
number := false
%%%

*Pattern*: Parameterize a wrapper by a type tag that does not occur in its stored fields. Different tags distinguish otherwise similar types during type checking. The tag carries no runtime value; this does not by itself specify the wrapper’s compiled representation.

*Rationale*: A function requiring `TaggedId UserTag` rejects a `TaggedId ProposalTag` argument. This prevents direct cross-use of those types. Public payload access and constructors still permit explicit rewrapping under another tag. It does not prove that the wrapped string identifies an existing user or proposal.

*Implementation Strategy*:

1. Define a generic wrapper type parameterized by a phantom tag.
2. Create tag types that are not definitionally equal; different names for the same type do not suffice. Empty inductive types suffice because no tag value is stored.
3. Define type aliases using the wrapper with specific tags.
4. Verify representative wrong-tag applications fail by type mismatch.

*Example - Type-Safe Identifiers*:

```lean
namespace PhantomIds
/-- An identifier tagged with the phantom type `entity`, which it does not store. -/
structure TaggedId (entity : Type) where
  /-- The identifier text. -/
  value : String
end PhantomIds
open PhantomIds

/-- Phantom tag for users: an empty type, used only as a type index. -/
inductive UserTag
/-- Phantom tag for proposals. -/
inductive ProposalTag
/-- Phantom tag for entities. -/
inductive EntityTag
/-- Phantom tag for content. -/
inductive ContentTag

/-- User identifiers. -/
def UserId := TaggedId UserTag
/-- Proposal identifiers. -/
def ProposalId := TaggedId ProposalTag
/-- Entity identifiers. -/
def EntityId := TaggedId EntityTag
/-- Content identifiers. -/
def ContentId := TaggedId ContentTag

/-- A user record. -/
structure User where
  /-- The user's name. -/
  name : String

/-- These function parameters specify argument types only; this example makes
no claim about lookup results or proposal submission behavior. -/
example (getUser : UserId → Option User) (submitProposal : UserId → ProposalId → Bool)
    (uid : UserId) (pid : ProposalId) : Unit :=
  let _ := getUser uid
  let _ := submitProposal uid pid
  ()

/-- A rational quantity tagged with its phantom unit of measure. -/
structure Quantity (unit : Type) where
  /-- The magnitude, in the tagged unit. -/
  value : Rat

/-- Phantom unit tag: metres. -/
inductive Meters
/-- Phantom unit tag: seconds. -/
inductive Seconds
/-- Phantom unit tag: metres per second. -/
inductive MetersPerSecond

/-- A distance in metres. -/
def Distance := Quantity Meters
/-- A duration in seconds. -/
def Duration := Quantity Seconds
/-- A velocity in metres per second. -/
def Velocity := Quantity MetersPerSecond

/-- The velocity `d / t`, in exact rational arithmetic. The lesson here is the
*type* safety of the tagged arguments; rational division is total, so a zero
duration yields velocity `0`. -/
def velocity (d : Distance) (t : Duration) : Velocity :=
  ⟨d.value / t.value⟩

-- velocity t d  -- Would be a type error (wrong argument order)
```

*Boundary of enforcement*: Phantom tags make swapped types an elaboration error. `Quantity Seconds` and `Quantity Meters` are distinct types. Rational division is total: `velocity` of a zero `Duration` produces a well-defined `Velocity` with value `0`. No type error or exception occurs. See {ref "321-totality-termination-and-totalized-operations"}[module 3 §3.2.1] for totalized operations and encoding a nonzero domain when required.

```lean (fails := "Application type mismatch|is expected to have type")
/-- The unit tag for meters. -/
inductive Meters
/-- The unit tag for seconds. -/
inductive Seconds
/-- A rational quantity tagged with its unit. -/
structure Qty (unit : Type) where
  /-- The quantity's magnitude. -/
  value : Rat

/-- A distance in meters. -/
abbrev Distance := Qty Meters
/-- A duration in seconds. -/
abbrev Duration := Qty Seconds

/-- Argument order is enforced by the distinct tags. -/
def ratio (d : Distance) (t : Duration) : Rat := d.value / t.value

/-- Swapped arguments are a type error at elaboration. -/
def bad : Rat := ratio (⟨1⟩ : Duration) (⟨1⟩ : Distance)
```

# 2.4 Abstract Mathematical Models
%%%
tag := "24-abstract-mathematical-models"
number := false
%%%

*Pattern*: Define system concepts using abstract mathematical types when the claim does not depend on a concrete representation — and define them against the concrete executable types when it does. Abstraction is a tool for claim precision, not a universal exclusion of executable representations.

*Rationale*: An abstract model omits representation details that the claim does not need. Its proofs establish properties of that model. Transferring a result to an executable Lean definition MUST use a checked theorem relating the two under the required hypotheses. Claims about external execution additionally identify the compiler, runtime, and external-world assumptions that connect the formal objects to execution ({ref "13-the-specificationmodel-firewall"}[module 1 §1.3]).

*Implementation Strategy*:

1. Use mathematical types (ℝ, ℕ, `Set α`) when the claim is representation-independent
2. Keep representations abstract by parameterizing structures over the content type. A type parameter is quantified and introduces no project logical axiom. An implemented opaque package can instead expose selected operations over a hidden representation ({ref "651-opaque-packages"}[module 6 §6.5.1]).
3. Specify behavior through mathematical properties when abstraction serves the claim; specify executable behavior against the executable definition itself when it does not
4. Transfer a model claim to an executable definition only through a proved refinement theorem whose hypotheses name the exact machine conditions — bounds, overflow freedom, domain restrictions — under which the correspondence holds
5. Let implementations choose appropriate concrete representations

*Example - Abstract Content Storage*:

```lean
/-- Abstract storage, parameterized over the content type. No representation
chosen, no logical assumption introduced: `Content` is a bound parameter. -/
structure ContentStore (Content : Type) where
  /-- Which content is stored: a membership predicate, not a data structure. -/
  Stored : Content → Prop
  /-- Retrieval relation (mathematical, not algorithmic). -/
  Retrievable : Content → Prop
  /-- Consistency: can only retrieve what's stored. -/
  stored_of_retrievable : ∀ c, Retrievable c → Stored c

/-- A verification scheme specified by its relation and the law every
instance must prove. No commitment to binary trees, hash functions, or
byte arrays — `Content` and `Id` are parameters. -/
structure VerificationScheme (Content Id : Type) where
  /-- Verification is a mathematical relation, not an algorithm. -/
  Verifies : Content → Id → Prop
  /-- Soundness: one identifier verifies at most one content. -/
  eq_of_verifies : ∀ c₁ c₂ : Content, ∀ i : Id, Verifies c₁ i → Verifies c₂ i → c₁ = c₂
```

The `stored_of_retrievable` field proves that retrieved content satisfies `Stored`; it does not require retrieving any content. The `eq_of_verifies` field proves content uniqueness for each verifying identifier; it does not require any identifier to verify anything. An always-false relation satisfies either condition. Existence, retrieval completeness, or a decision procedure requires separate evidence when claimed.

*Example - A Checked Refinement Relation*:

When the claim transfers from a model to a machine implementation, the transfer theorem carries the machine's exact semantics in its statement and its hypotheses:

```lean
/-- Model: exact natural-number addition. -/
def modelAdd (a b : Nat) : Nat := a + b

/-- Implementation: 32-bit machine addition, which wraps modulo 2^32. -/
def implAdd (a b : UInt32) : UInt32 := a + b

/-- The refinement theorem: under the no-overflow hypothesis the machine
semantics needs, the executable result is the model result. -/
theorem toNat_implAdd_of_lt (a b : UInt32) (h : a.toNat + b.toNat < 2 ^ 32) :
    (implAdd a b).toNat = modelAdd a.toNat b.toNat := by
  unfold implAdd modelAdd
  rw [UInt32.toNat_add, Nat.mod_eq_of_lt h]

/-- The hypothesis is load-bearing: at the word boundary the machine result
wraps to 0 while the model sum is 2^32. -/
example : ((0xffffffff : UInt32) + 1).toNat = 0 ∧
    modelAdd (0xffffffff : UInt32).toNat 1 = 2 ^ 32 := by
  decide
```

Without `h`, the unconditional refinement statement is false, as the boundary example shows. The checked relation and its hypotheses justify the transfer. `UInt32.toNat_add` is the exact machine semantics — wrapping modulo `2 ^ 32` — stated by the core library and used by the proof.

*Stateful refinement for finite-prefix safety* relates transition systems as well as state representations. Relate concrete and abstract states, prove initialization and forward simulation into a precisely defined finite abstract closure, and derive invariant transfer over every finite concrete path. {ref "39-stateful-refinement-and-finite-prefix-safety"}[Module 3 §3.9] works through the actual limiter: occupied and free slots are different representations, refusal can stutter, and one reset can match several abstract releases. The proved Lean relation is part of the formal development, distinct from an unproved external adapter.

*Anti-Pattern - Unsupported Claims About a Representation*: A byte array, hash function, or binary tree is a valid subject for a Lean specification. The defect is claiming properties that its definition and proofs do not establish. A tree representation alone proves no hash-collision or authentication property, and a theorem about an abstract verification relation does not establish the behavior of an unrelated implementation. State the required property and prove it about the chosen representation, or provide the checked correspondence needed to transfer it.
