module

public import RegulaSpecification.RuleRecord

@[expose] public section

namespace RegulaSpecification

open Lean (Name)

def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

def compilerAxioms : List Name := []

def NativeProofAxiom (a : Name) : Prop :=
  ∃ p tactic suffix, a = Name.str (Name.str (Name.str p "_native") tactic) suffix

namespace Input

variable (i : Input)

def Known (a : Name) : Prop :=
  a ∈ logicalAxioms ∧ ∃ d ∈ i.decls, d.name = a ∧ d.inToolchain = true

end Input

theorem sorry_not_known (i : Input) : ¬ i.Known ``sorryAx := by
  intro h
  have := h.1
  simp [logicalAxioms] at this

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
