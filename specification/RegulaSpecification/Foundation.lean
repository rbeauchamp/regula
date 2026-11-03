import RegulaSpecification.RuleRecord

/-!
# The axioms that more than one rule names

The vocabulary of the foundation profile that RG1002 to RG1005 share: Lean's three logical axioms, the
toolchain's axioms by which the kernel trusts the compiler, the name form of a native proof's axiom, and
which axioms are known. Each rule's own statement is in its module below {lit}`Rules/`, and
{lit}`Refinement.lean` proves that each axiom RG1002 to RG1004 name also violates RG1005.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The three axioms of Lean's logic that a profile can admit. -/
def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The axioms of the toolchain by which Lean's kernel trusts the compiler. Lean v4.35.0 declares
none: `Lean.ofReduceBool`, `Lean.ofReduceNat` and `Lean.trustCompiler`, which v4.34.1 declared
({lit}`Init/Core.lean:2338`, {lit}`2396` and {lit}`2409` there), are gone. A native proof still adds an axiom of
its own ({lit}`NativeProofAxiom`). -/
def compilerAxioms : List Name := []

/-- {name}`a` has the name form of the axiom that a native proof ({tactic}`native_decide`, {tactic}`decide +native`,
{tactic}`bv_decide`) adds at Lean v4.34.1 and v4.35.0: `<declaration>._native.<tactic>.<suffix>`
({lit}`Lean/Meta/Native.lean:45` and {lit}`75-82` at v4.35.0). -/
def NativeProofAxiom (a : Name) : Prop :=
  ∃ p tactic suffix, a = Name.str (Name.str (Name.str p "_native") tactic) suffix

namespace Input

variable (i : Input)

/-- {name}`a` is one of the three logical axioms and is the toolchain's own constant of that name. -/
def Known (a : Name) : Prop :=
  a ∈ logicalAxioms ∧ ∃ d ∈ i.decls, d.name = a ∧ d.inToolchain = true

end Input

theorem sorry_not_known (i : Input) : ¬ i.Known ``sorryAx := by
  intro h
  have := h.1
  simp [logicalAxioms] at this

/-- The number of components of a name. -/
def components : Name → Nat
  | .anonymous => 0
  | .str p _ => components p + 1
  | .num p _ => components p + 1

theorem components_of_native {a : Name} (h : NativeProofAxiom a) : 3 ≤ components a := by
  obtain ⟨p, t, s, rfl⟩ := h
  simp only [components]
  omega

theorem native_not_logical {a : Name} (h : NativeProofAxiom a) : a ∉ logicalAxioms := by
  have := components_of_native h
  simp only [logicalAxioms, List.mem_cons, List.not_mem_nil, or_false]
  rintro (rfl | rfl | rfl) <;> simp [components] at this

end RegulaSpecification
