module

public import RegulaPolicy.Decision
public import Regula.Contract

/-! # Operational self-audit policy

Declaration policy for the operational self-audit of the excluded checker library.

Operational code is not a conforming proof surface: it holds the IO adapters that observe
Lake, the compiler and the filesystem. Two of its facts are therefore reported rather than
failed, and nothing else is relaxed:

- an authored `unsafe` or `partial` declaration (an escape hatch, RG1006), which environment
  loading and some traversals need; and
- in a definition whose type is not a proposition, a transitive axiom of the supplied
  `ToolchainAxioms` set, such as the pinned toolchain's Lake type-family equations that
  in-process Lake APIs reach.

`operationalFailure` runs the conforming Standard-Logical decision `declarationFailure` on
`operationalView`, which erases exactly those two facts. It uses no generated-role receipts, so
a compiler-trusting proof or an owned native axiom fails. `operationalFailure_none_iff` states
its success relation, `operationalFailure_ne_escapeHatch` and `operationalFailure_safety`
show escape hatches never decide it, `operationalFailure_prop` shows a proposition-typed
declaration gets exactly the conforming decision, and `operationalFailure_eq_conforming`
shows the whole decision is the conforming one on every declaration without a reported fact.
The observations themselves, and whether a name belongs to the toolchain, are established by
the operational adapter, not by these theorems. -/

@[expose] public section

namespace RegulaPolicy
open Lean (Name)

/-- Axioms an operational definition may reach beyond Standard-Logical. None is `sorryAx` or a
compiler axiom, so erasing them can never hide a hole or compiler trust. -/
structure ToolchainAxioms where
  /-- The axiom names, as the operational adapter observed them. -/
  names : Array Name
  /-- `sorryAx` is not among them. -/
  not_hole : `sorryAx ∉ names
  /-- No legacy compiler axiom enabled by this compiler's admitted capability occurs. -/
  not_compiler : ∀ n ∈ names, ¬ CompilerAxiom #[] n

/-- Admission of an observed toolchain axiom set; it refuses a hole or compiler axiom. -/
def admitToolchainAxioms (names : Array Name) : Except String ToolchainAxioms :=
  if h : `sorryAx ∉ names ∧ ∀ n ∈ names, ¬ CompilerAxiom #[] n then
    .ok ⟨names, h.1, h.2⟩
  else .error "toolchain axiom set contains sorryAx or a compiler axiom"

/-- The admitted set is exactly the supplied names. -/
theorem admitToolchainAxioms_names {names : Array Name} {t : ToolchainAxioms}
    (h : admitToolchainAxioms names = .ok t) : t.names = names := by
  unfold admitToolchainAxioms at h
  split at h
  · cases h; rfl
  · cases h

/-- The observed transitive axioms the operational decision inspects: all of them for a
proposition, and all but the reported toolchain axioms for any other declaration. -/
def operationalAxioms (t : ToolchainAxioms) (d : Declaration) : Array Name :=
  if d.isProp then d.axioms else d.axioms.filter fun n => !t.names.contains n

/-- The declaration the conforming decision sees: escape-hatch flags erased and reported
toolchain axioms removed from a non-proposition's axiom set. -/
def operationalView (t : ToolchainAxioms) (d : Declaration) : Declaration :=
  { d with isUnsafe := false, isPartial := false, axioms := operationalAxioms t d }

/-- Operational declaration decision: the conforming Standard-Logical decision on the view,
with no teaching-native or recursive-helper roles. -/
def operationalFailure (t : ToolchainAxioms) (d : Declaration) : Option DeclarationFailure :=
  declarationFailure (operationalView t d) (.conforming .standardLogical) #[] #[]

/-- Operational success: not an axiom declaration, every transitive axiom Standard-Logical or
(for a non-proposition) a reported toolchain axiom, and every recorded contract complete.
Escape hatches do not appear. -/
def OperationalOK (t : ToolchainAxioms) (d : Declaration) : Prop :=
  d.kind ≠ .«axiom» ∧
  (∀ n ∈ d.axioms, Permitted .standardLogical n ∨ (d.isProp = false ∧ n ∈ t.names)) ∧
  ContractOK d

theorem mem_operationalAxioms (t : ToolchainAxioms) (d : Declaration) (n : Name) :
    n ∈ operationalAxioms t d ↔ n ∈ d.axioms ∧ (d.isProp = false → n ∉ t.names) := by
  unfold operationalAxioms
  cases hp : d.isProp <;> simp [Array.mem_filter]

/-- Exact success relation of the executed operational decision. -/
theorem operationalFailure_none_iff (t : ToolchainAxioms) (d : Declaration) :
    operationalFailure t d = none ↔ OperationalOK t d := by
  unfold operationalFailure
  rw [declarationFailure_none_iff]
  simp only [DeclarationOK, operationalView, KnownDependencies, SafetyOK, CompilerPolicyOK,
    ContractOK, ProfileOK, OperationalOK, mem_operationalAxioms]
  have hsorry := t.not_hole
  have hcomp := t.not_compiler
  constructor
  · rintro (⟨_, hn, _⟩ | ⟨hk, _, hknown, _, hcompiler, hcontract, _⟩)
    · simp at hn
    · refine ⟨hk, fun n hn => ?_, hcontract⟩
      by_cases ht : d.isProp = false ∧ n ∈ t.names
      · exact Or.inr ht
      · have hmem : n ∈ d.axioms ∧ (d.isProp = false → n ∉ t.names) :=
          ⟨hn, fun hp hm => ht ⟨hp, hm⟩⟩
        rcases hknown n hmem with hs | hc
        · exact Or.inl hs
        · exact absurd hc (hcompiler.resolve_left (by simp) n hmem)
  · rintro ⟨hk, hall, hcontract⟩
    have hlog : ∀ n, n ∈ d.axioms ∧ (d.isProp = false → n ∉ t.names) →
        Permitted .standardLogical n := fun n ⟨hn, hnt⟩ =>
      (hall n hn).resolve_right fun ⟨hp, hm⟩ => hnt hp hm
    have hnc : ∀ n, n ∈ d.axioms ∧ (d.isProp = false → n ∉ t.names) →
        ¬ CompilerAxiom #[] n := fun n h hc => by
      have hs := hlog n h
      rcases hc with ⟨_, rfl | rfl | rfl⟩ | hc
      · simp [Permitted] at hs
      · simp [Permitted] at hs
      · simp [Permitted] at hs
      · simp at hc
    refine Or.inr ⟨hk, fun h => ?_, fun n h => Or.inl (hlog n h), by simp,
      Or.inr hnc, hcontract, fun n h => Or.inr (hlog n h)⟩
    have hs := hlog _ h
    simp [Permitted] at hs

/-- An escape hatch is never the operational failure. -/
theorem operationalFailure_ne_escapeHatch (t : ToolchainAxioms) (d : Declaration) :
    operationalFailure t d ≠ some .escapeHatch := by
  unfold operationalFailure declarationFailure operationalView
  intro h
  repeat' split at h
  all_goals simp_all

/-- The decision does not depend on the escape-hatch flags. -/
theorem operationalFailure_safety (t : ToolchainAxioms) (d : Declaration) (u p : Bool) :
    operationalFailure t { d with isUnsafe := u, isPartial := p } = operationalFailure t d := by
  rfl

/-- A proposition-typed declaration gets exactly the conforming Standard-Logical decision,
up to its escape-hatch flags: no toolchain axiom is removed from a proof. -/
theorem operationalFailure_prop (t : ToolchainAxioms) (d : Declaration) (hp : d.isProp = true) :
    operationalFailure t d = declarationFailure { d with isUnsafe := false, isPartial := false }
      (.conforming .standardLogical) #[] #[] := by
  simp [operationalFailure, operationalView, operationalAxioms, hp]

/-- On a declaration with no reported fact (no escape hatch and no toolchain axiom), the
operational decision is the conforming Standard-Logical decision itself. -/
theorem operationalFailure_eq_conforming (t : ToolchainAxioms) (d : Declaration)
    (hu : d.isUnsafe = false) (hpartial : d.isPartial = false)
    (hnone : ∀ n ∈ d.axioms, n ∉ t.names) :
    operationalFailure t d = declarationFailure d (.conforming .standardLogical) #[] #[] := by
  have hax : operationalAxioms t d = d.axioms := by
    unfold operationalAxioms
    split
    · rfl
    · exact Array.filter_eq_self.mpr fun n hn => by simpa using hnone n hn
  have hview : operationalView t d = d := by
    cases d
    simp_all [operationalView]
  simp [operationalFailure, hview]

/-- Required meaning of the executed operational decision: its exact success relation, no
escape-hatch failure, and agreement with the conforming Standard-Logical decision on every
declaration without a reported fact. -/
def OperationalFailureContract
    (decide : ToolchainAxioms → Declaration → Option DeclarationFailure) : Prop :=
  ∀ t d, (decide t d = none ↔ OperationalOK t d) ∧ decide t d ≠ some .escapeHatch ∧
    (d.isUnsafe = false → d.isPartial = false → (∀ n ∈ d.axioms, n ∉ t.names) →
      decide t d = declarationFailure d (.conforming .standardLogical) #[] #[])

/-- Registers `OperationalFailureContract` about `operationalFailure`; the self-audit runs
`checked_operationalFailure.run`. -/
theorem checked_operationalFailure :
    Regula.ExecutableContract operationalFailure OperationalFailureContract :=
  ⟨fun t d => ⟨operationalFailure_none_iff t d, operationalFailure_ne_escapeHatch t d,
    operationalFailure_eq_conforming t d⟩⟩

end RegulaPolicy
