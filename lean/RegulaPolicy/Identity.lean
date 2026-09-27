module

public import Std
public import Init.Data.Ord.String

/-! Structural Lean identities. The tagged component sequence preserves string and
numeric constructors (including empty strings). No display-name round trip is used.
Names remain Lean's own datatype; `Identity` adds only non-anonymity for coverage keys.
Exact source bytes, not a digest, determine `SourceSnapshot` equality. -/

@[expose] public section

namespace RegulaPolicy
open Lean Std
attribute [local instance] lexOrd

/-- Outer component first. Zero tags string components; successor tags numbers. -/
def nameComponents : Name → List (Nat × String)
  | .anonymous => []
  | .str p s => (0, s) :: nameComponents p
  | .num p n => (n + 1, "") :: nameComponents p

/-- Total inverse on the canonical image; noncanonical numeric payloads are refused. -/
def nameFromComponents : List (Nat × String) → Except String Name
  | [] => .ok .anonymous
  | (0, s) :: rest => return .str (← nameFromComponents rest) s
  | (n + 1, s) :: rest =>
      if s = "" then return .num (← nameFromComponents rest) n
      else .error "numeric name component has string payload"

/-- Every Lean name, including anonymous prefixes and empty strings, round-trips. -/
@[simp] theorem name_components_roundtrip (n : Name) :
    nameFromComponents (nameComponents n) = .ok n := by
  induction n with
  | anonymous => rfl
  | str p s ih => simp [nameComponents, nameFromComponents, ih] <;> rfl
  | num p n ih => simp [nameComponents, nameFromComponents, ih] <;> rfl

/-- Distinct constructor trees never acquire the same structural key. -/
theorem nameComponents_injective {a b : Name} (h : nameComponents a = nameComponents b) :
    a = b := by
  have := congrArg nameFromComponents h
  simpa using this

/-- Structural ordering for Lean's own name type, scoped to policy collections. -/
scoped instance : Ord Name := ⟨compareOn nameComponents⟩
scoped instance : TransOrd Name := inferInstanceAs (TransCmp (compareOn nameComponents))
scoped instance : LawfulEqOrd Name where
  eq_of_compare h := nameComponents_injective (LawfulEqOrd.eq_of_compare h)

/-- A module/declaration key cannot be anonymous. This is not a source identifier grammar. -/
structure Identity where
  name : Name
  nonanonymous : name ≠ .anonymous
  deriving DecidableEq

instance : Repr Identity := ⟨fun x _ => repr x.name⟩
instance : ToString Identity := ⟨fun x => x.name.toString⟩
instance : Ord Identity := ⟨compareOn (fun x => nameComponents x.name)⟩
instance : TransOrd Identity := inferInstanceAs (TransCmp (compareOn (fun x : Identity => nameComponents x.name)))
instance : LawfulEqOrd Identity where
  eq_of_compare {a b} h := by
    have e : nameComponents a.name = nameComponents b.name := LawfulEqOrd.eq_of_compare h
    cases a
    cases b
    have := nameComponents_injective e
    cases this
    rfl

/-- Refuse anonymous coverage identities instead of manufacturing a default. -/
def admitIdentity (n : Name) : Except String Identity :=
  if h : n ≠ .anonymous then .ok ⟨n, h⟩ else .error "anonymous coverage identity"

/-- Every nonanonymous input is admitted unchanged. -/
theorem admitIdentity_exact (n : Name) (h : n ≠ .anonymous) :
    admitIdentity n = .ok ⟨n, h⟩ := by simp [admitIdentity, h]

/-- Exact source content and logical URI; compiler/filesystem authenticity is external. -/
structure SourceSnapshot where
  uri : String
  source : String
  deriving Repr, DecidableEq

structure ByteRange where
  start : Nat
  stop : Nat
  deriving Repr, DecidableEq
end RegulaPolicy
