/-!
# Documentation fence prelude

Machine-audit prelude for the shared primitives used by documentation fences.
It provides nominal `Glossary.Time` over non-negative rationals with a lawful,
decidable linear order; `ResourceAmount` as the canonical subtype of non-negative
rationals; `OpaqueDataPackage` and its opaque value `opaqueDataPackage`, whose
exported `wrap` operation constructs `OpaqueData` (also through `OpaqueData.seal`);
and phantom-typed `Id` values with the documented domain tags. The only
representation exposure is through the operations named by each declaration;
external construction, payload recovery, and private-name access are rejected by
the `lean (fails := ...)` examples of the standard's module 6
(`website/RegulaStandard/CodeOrganization.lean`).

Every definition here uses Lean's core library only. `Rat` is exact rational
arithmetic, not the real numbers: a claim about real-valued time needs Mathlib's
`ℝ`, and the Mathlib integration package (`integration/mathlib/`) keeps that model.

Fences import this module explicitly, so their assumptions are their printed
imports plus these exact APIs. This module is part of the positive surface, and
the axiom gate reports every declaration and foundation label below.
-/

namespace Glossary

/-- `Time` (§2.2 / §4.1): a nominal wrapper around non-negative rationals.

The wrapper is intentionally distinct from every other rational-backed domain
type: a time cannot be passed directly where a resource amount is required.
The `val` field exposes the underlying rational when a formula needs it. -/
structure Time where
  /-- The rational this time wraps. -/
  val : Rat
  /-- The time is non-negative. -/
  nonneg : 0 ≤ val

/-- Times compare by their underlying rationals. -/
instance : LE Time := ⟨fun a b => a.val ≤ b.val⟩

/-- The comparison of two times is the decidable comparison of their rationals. -/
instance : DecidableLE Time := fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))

/-- The order on `Time` compares exactly the underlying rationals. -/
theorem Time.le_iff (a b : Time) : a ≤ b ↔ a.val ≤ b.val := Iff.rfl

/-- Any two times are comparable, as their rationals are. -/
instance : Std.Total (α := Time) (· ≤ ·) := ⟨fun _ _ => Rat.le_total⟩

/-- The comparison of times is transitive, as that of their rationals is. -/
instance : Trans (α := Time) (· ≤ ·) (· ≤ ·) (· ≤ ·) := ⟨Rat.le_trans⟩

/-- Times that compare both ways are equal: `val` is injective, because the remaining
field is a proof. -/
instance : Std.Antisymm (α := Time) (· ≤ ·) where
  antisymm a b hab hba := by
    cases a
    cases b
    simp only [Time.mk.injEq]
    exact Rat.le_antisymm hab hba

/-- Lawful linear order on `Time`, built by core's `Std.LinearOrderPackage.ofLE` factory
from the three laws above, which are `Rat`'s transported along the injective `val`
projection. The factory derives `<`, `min`, `max`, `compare` and their compatibility
proofs from `≤`; no order law is restated here. -/
instance : Std.LinearOrderPackage Time := .ofLE Time

/-- Resource quantities reuse Lean's canonical `Subtype` of non-negative rationals. This
is definitionally that subtype, unlike the nominal `Time` wrapper. -/
abbrev ResourceAmount : Type := {amount : Rat // 0 ≤ amount}

/-- Existential-style API package used to keep a representation abstract.

The package exposes a carrier and an introduction operation, but deliberately
contains no payload observer or equation identifying the carrier with
`String`. -/
structure OpaqueDataPackage where
  /-- The abstract type of packaged values. -/
  Carrier : Type
  /-- Introduces a carrier value from a string; the package offers no inverse. -/
  wrap : String → Carrier

/-- The concrete implementation used to initialize `opaqueDataPackage`.
It remains an implementation detail; clients reason only through the package
fields that are actually exported. -/
private def opaqueDataImplementation : OpaqueDataPackage where
  Carrier := String
  wrap := id

/-- Opaque package value: its body is not kernel-reducible by clients, so the
carrier cannot be identified with the implementation type. This is an
implemented `opaque` definition, not a logical `axiom` or `constant`. -/
opaque opaqueDataPackage : OpaqueDataPackage := opaqueDataImplementation

/-- `OpaqueData` (§1.3): an abstract carrier obtained from an opaque package.

External code may introduce values through the package's documented `wrap`
operation (or `OpaqueData.seal` below), but it has no constructor, projection,
inductive eliminator, or payload observer for this carrier. The standard's
`lean (fails := ...)` examples check that direct construction and payload
recovery are rejected. -/
abbrev OpaqueData : Type := opaqueDataPackage.Carrier

/-- Documented convenience constructor for the abstract carrier. -/
def OpaqueData.seal : String → OpaqueData := opaqueDataPackage.wrap

/-- Phantom tag for entity identifiers. -/
inductive EntityTag

/-- Phantom tag for user identifiers. -/
inductive UserTag

/-- Phantom tag for proposal identifiers. -/
inductive ProposalTag

/-- Phantom tag for content identifiers. -/
inductive ContentTag

/-- Phantom tag for event identifiers. -/
inductive EventTag

/-- Phantom tag for network-node identifiers. -/
inductive NetworkNodeTag

/-- Phantom-typed identifier (§2.3): an `Id UserTag` and an `Id ProposalTag`
are distinct types even though both wrap a `String`. Outside this namespace,
write `Glossary.Id` explicitly to distinguish it from the prelude's `Id` monad. -/
structure Id (entity : Type) where
  /-- The identifier's text. -/
  value : String
  deriving Repr

end Glossary
