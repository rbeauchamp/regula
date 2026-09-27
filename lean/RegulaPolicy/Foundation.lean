module

public import RegulaPolicy.Admission

/-! Independent finite foundation predicates. Profiles are bounds on exact transitive
axiom membership, not claims about alternative proofs or native execution. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)

/-- Semantic failures are mapped to the one diagnostic registry by the adapter. -/
inductive DeclarationFailure where
  | projectAxiom | proofHole | unknownAxiom | escapeHatch | compilerTrusting
  | executableContract | profileExceeded | invalidInventory
  deriving Repr, DecidableEq

/-- Inspection and teaching cannot serve as a positive conformance profile. -/
inductive InspectionRequest where
  | classification | teaching | conforming (profile : ConformingProfile)
  deriving Repr, DecidableEq

def ConformingProfile.permits : ConformingProfile → Name → Bool
  | .kernelOnly, _ => false
  | .choiceFree, n => n == `propext || n == `Quot.sound
  | .standardLogical, n => n == `propext || n == `Quot.sound || n == `Classical.choice

def standardLogicalAxiom (name : Name) : Bool :=
  ConformingProfile.permits .standardLogical name

def builtinCompilerAxiom (name : Name) : Bool :=
  name == `Lean.trustCompiler || name == `Lean.ofReduceBool
    || name == `Lean.ofReduceNat


/-- The three permitted sets, specified by membership rather than a classifier result. -/
def Permitted : ConformingProfile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, n => n = `propext ∨ n = `Quot.sound
  | .standardLogical, n => n = `propext ∨ n = `Quot.sound ∨ n = `Classical.choice
instance (p : ConformingProfile) (n : Name) : Decidable (Permitted p n) := by
  cases p <;> unfold Permitted <;> infer_instance

/-- A profile contains every member of the observed finite axiom set. -/
def ContainsFoundation (p : ConformingProfile) (axioms : Array Name) : Prop :=
  ∀ n ∈ axioms, Permitted p n
instance (p : ConformingProfile) (a : Array Name) : Decidable (ContainsFoundation p a) := by
  unfold ContainsFoundation; infer_instance

/-- Foundation order is inclusion of the permitted sets. -/
def ProfileLE (p q : ConformingProfile) : Prop := ∀ n, Permitted p n → Permitted q n

/-- Least means containment and minimality among all three permitted sets. -/
def LeastFoundation (a : Array Name) (p : ConformingProfile) : Prop :=
  ContainsFoundation p a ∧ ∀ q, ContainsFoundation q a → ProfileLE p q

@[simp] theorem permits_iff (p : ConformingProfile) (n : Name) :
    p.permits n = true ↔ Permitted p n := by
  cases p <;> simp [ConformingProfile.permits, Permitted, or_assoc]

/-- Executable least-label selection, defined over set membership with no enumeration
of programs or axiom subsets. The caller separately classifies forbidden axioms. -/
def leastFoundation (a : Array Name) : ConformingProfile :=
  if ContainsFoundation .kernelOnly a then .kernelOnly
  else if ContainsFoundation .choiceFree a then .choiceFree else .standardLogical

/-- Every admissible axiom set gets its least containing logical profile. -/
theorem leastFoundation_spec (a : Array Name) (h : ContainsFoundation .standardLogical a) :
    LeastFoundation a (leastFoundation a) := by
  unfold leastFoundation
  split
  next hk =>
    exact ⟨hk, fun _ _ _ hn => False.elim hn⟩
  next hk =>
    split
    next hc =>
      refine ⟨hc, ?_⟩
      intro q hq n hn
      cases q with
      | kernelOnly => exact False.elim (hk hq)
      | choiceFree => exact hn
      | standardLogical =>
        rcases hn with hn | hn
        · exact Or.inl hn
        · exact Or.inr (Or.inl hn)
    next hc =>
      refine ⟨h, ?_⟩
      intro q hq n hn
      cases q with
      | kernelOnly => exact False.elim (hk hq)
      | choiceFree => exact False.elim (hc hq)
      | standardLogical => exact hn

/-- Order and duplicate occurrences do not change the computed least profile. -/
theorem leastFoundation_ext (a b : Array Name) (h : ∀ n, n ∈ a ↔ n ∈ b) :
    leastFoundation a = leastFoundation b := by
  have eq (p : ConformingProfile) : ContainsFoundation p a ↔ ContainsFoundation p b := by
    constructor <;> intro hp n hn
    · exact hp n ((h n).mpr hn)
    · exact hp n ((h n).mp hn)
  simp only [leastFoundation, propext (eq .kernelOnly), propext (eq .choiceFree)]

end RegulaPolicy
