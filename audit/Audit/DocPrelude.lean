import Mathlib.Basic.NNReal.Defs
import Mathlib.Order.Basic

/-!
# Documentation fence prelude

Machine-audit prelude for the shared primitives used by documentation fences.
It provides nominal `Glossary.Time` with a lifted lawful linear order;
`ResourceAmount` as the canonical `NNReal`; `OpaqueDataPackage` and its opaque
value `opaqueDataPackage`, whose exported `wrap` operation constructs
`OpaqueData` (also through `OpaqueData.seal`); and phantom-typed
`Id` values with the documented domain tags. The only representation exposure
is through the operations named by each declaration; external construction,
observation, and private-name access are negative fixtures.

Fences import this module explicitly, so their assumptions are their printed
imports plus these exact APIs. This module is part of the positive surface, and
the axiom gate reports every declaration and foundation label below.
-/

namespace Glossary

/-- `Time` (§2.2 / §4.1): a nominal wrapper around non-negative reals.

The wrapper is intentionally distinct from every other `NNReal`-backed domain
type: a time cannot be passed directly where a resource amount is required.
The `val` field exposes the underlying non-negative real when a formula needs
it. -/
structure Time where
  /-- The non-negative real this time wraps. -/
  val : NNReal

/-- Lawful linear order on `Time`, lifted from Mathlib's `NNReal` order. The
instance is noncomputable because `NNReal`'s inherited real order is. -/
noncomputable instance : LinearOrder Time :=
  LinearOrder.lift' Time.val (by
    intro a b h
    cases a
    cases b
    simp_all)

/-- Resource quantities reuse Mathlib's canonical non-negative reals. This is
definitionally `NNReal`, unlike the nominal `Time` wrapper. -/
abbrev ResourceAmount : Type := NNReal

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
inductive eliminator, or payload observer for this carrier. The negative
fixtures regress direct construction and payload recovery. -/
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
