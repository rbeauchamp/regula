import RegulaSpecification.RuleRecord

/-!
# The foundation profile: RG1001 to RG1005

Each rule reads the constants of the loaded environment and their transitive axiom sets
(`Input.AxiomOf`), which `Lean.collectAxioms` computes from the constants themselves when the
environment is imported without extension states (see the specification's input section). The
five rules refine one refusal: `rg1005_of_hole`, `rg1005_of_unknown` and `rg1005_of_compiler`
prove that each axiom RG1002 to RG1004 name also violates RG1005 for every profile, so a wrong
choice among them changes the reported rule, never the verdict. RG1001 alone reports an axiom
that nothing uses.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The three axioms of Lean's logic that a profile can admit. -/
def logicalAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The axioms by which Lean's kernel trusts the compiler. -/
def compilerAxioms : List Name := [``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- `a` has the name form of the axiom that a native proof (`native_decide`, `decide +native`,
`bv_decide`) adds at Lean v4.34.1: `<declaration>._native.<tactic>.<suffix>`. -/
def NativeProofAxiom (a : Name) : Prop :=
  ∃ p tactic suffix, a = Name.str (Name.str (Name.str p "_native") tactic) suffix

namespace Input

variable (i : Input)

/-- `a` is one of the three logical axioms and is the toolchain's own constant of that name. -/
def Known (a : Name) : Prop :=
  a ∈ logicalAxioms ∧ ∃ d ∈ i.decls, d.name = a ∧ d.inToolchain = true

/-- Profile `p` admits axiom `a`: a known axiom in the profile's set. -/
def Admits : Profile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, a => i.Known a ∧ (a = ``propext ∨ a = ``Quot.sound)
  | .standardLogical, a => i.Known a

end Input

/-- RG1001: a claimed module declares an axiom, the axiom of a native proof included. -/
def Violates1001 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ d.kind = .axiom

/-- RG1002: a constant of a claimed module depends on `sorryAx`. -/
def Violates1002 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ i.AxiomOf c ``sorryAx

/-- RG1003: a constant of a claimed module depends on an axiom that is not one of the known
three, and that RG1002 and RG1004 do not name. -/
def Violates1003 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ ∃ a, i.AxiomOf c a ∧ ¬ i.Known a ∧ a ≠ ``sorryAx ∧
    ¬ NativeProofAxiom a ∧ a ∉ compilerAxioms

/-- RG1004: a constant of a claimed module depends on a native proof's axiom or on an axiom by
which the kernel trusts the compiler. -/
def Violates1004 (i : Input) (c : Name) : Prop :=
  i.ClaimedName c ∧ ∃ a, i.AxiomOf c a ∧ (NativeProofAxiom a ∨ a ∈ compilerAxioms)

/-- RG1005: a constant of a module claimed with profile `p` depends on an axiom `p` does not
admit. -/
def Violates1005 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ ∃ p e, i.Claimed d.module p e ∧ ∃ a, i.AxiomOf c a ∧ ¬ i.Admits p a

/-- The intent record of RG1001. -/
def rg1001 := ruleRecord "RG1001" Violates1001
/-- The intent record of RG1002. -/
def rg1002 := ruleRecord "RG1002" Violates1002
/-- The intent record of RG1003. -/
def rg1003 := ruleRecord "RG1003" Violates1003
/-- The intent record of RG1004. -/
def rg1004 := ruleRecord "RG1004" Violates1004
/-- The intent record of RG1005. -/
def rg1005 := ruleRecord "RG1005" Violates1005

theorem admits_known {i : Input} {p : Profile} {a : Name} (h : i.Admits p a) : i.Known a := by
  cases p with
  | kernelOnly => exact absurd h id
  | choiceFree => exact h.1
  | standardLogical => exact h

theorem sorry_not_known (i : Input) : ¬ i.Known ``sorryAx := by
  intro h
  have := h.1
  simp [logicalAxioms] at this

/-- A claimed constant that depends on an axiom that is not known violates RG1005, whatever the
profile of its module. -/
theorem rg1005_of_known {i : Input} {c a : Name} (hc : i.ClaimedName c) (ha : i.AxiomOf c a)
    (hk : ¬ i.Known a) : Violates1005 i c := by
  obtain ⟨d, hd, rfl, p, e, hp⟩ := hc
  exact ⟨d, hd, rfl, p, e, hp, a, ha, fun h => hk (admits_known h)⟩

/-- RG1002 implies RG1005. -/
theorem rg1005_of_hole {i : Input} {c : Name} (h : Violates1002 i c) : Violates1005 i c :=
  rg1005_of_known h.1 h.2 (sorry_not_known i)

/-- RG1003 implies RG1005. -/
theorem rg1005_of_unknown {i : Input} {c : Name} (h : Violates1003 i c) : Violates1005 i c := by
  obtain ⟨hc, a, ha, hk, -⟩ := h
  exact rg1005_of_known hc ha hk

/-- The number of components of a name. -/
def components : Name → Nat
  | .anonymous => 0
  | .str p _ => components p + 1
  | .num p _ => components p + 1

/-- A native proof's axiom has at least three components. -/
theorem components_of_native {a : Name} (h : NativeProofAxiom a) : 3 ≤ components a := by
  obtain ⟨p, t, s, rfl⟩ := h
  simp only [components]
  omega

theorem native_not_logical {a : Name} (h : NativeProofAxiom a) : a ∉ logicalAxioms := by
  have := components_of_native h
  simp only [logicalAxioms, List.mem_cons, List.not_mem_nil, or_false]
  rintro (rfl | rfl | rfl) <;> simp [components] at this

/-- RG1004 implies RG1005. -/
theorem rg1005_of_compiler {i : Input} {c : Name} (h : Violates1004 i c) : Violates1005 i c := by
  obtain ⟨hc, a, ha, hn⟩ := h
  refine rg1005_of_known hc ha fun hk => ?_
  rcases hn with hn | hn
  · exact native_not_logical hn hk.1
  · have := hk.1
    simp only [compilerAxioms, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp [logicalAxioms] at this

end RegulaSpecification
