import RegulaSpecification.RuleRecord

/-!
# Decision and executable contracts: RG1007, RG1008 and RG1009

The rules read each executable contract from its theorem's type (`Contract`), the decision
registrations, and the constants each mentions. A registration is a declaration of a claimed
module, not an attribute entry, so the closed subset (`RG2007`) can refuse every attribute that
Lean does not define.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Input

variable (i : Input)

/-- `f` is a safe, total, computable constant of the input. -/
def SafeComputable (f : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = f ∧ d.isUnsafe = false ∧ d.isPartial = false ∧ d.isNoncomputable = false

/-- The specification of contract `k` reaches its implementation. -/
def SpecReachesImpl (k : Contract) : Prop := ∃ s ∈ k.spec, i.Reaches s k.impl

/-- A Boolean test outside the toolchain. -/
def ProjectTest (t : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = t ∧ d.isBoolTest = true ∧ d.inToolchain = false

end Input

/-- A contract is a decision contract when its kind is a decision kind. -/
def Contract.IsDecision (k : Contract) : Prop := k.kind ≠ .other

/-- RG1007: the executable contract `k` of a claimed module fixes arguments of its implementation,
names an implementation that is not safe and computable, or, as a decision contract, states its
specification through its implementation. -/
def Violates1007 (i : Input) (c : Name) : Prop :=
  ∃ k ∈ i.contracts, k.theorem_ = c ∧ i.ClaimedName c ∧
    (k.fixedArgs ≠ 0 ∨ ¬ i.SafeComputable k.impl ∨ (k.IsDecision ∧ i.SpecReachesImpl k))

/-- RG1008: a registered decision function of a claimed module has no decision contract in a
claimed module and no `Decidable` result type. -/
def Violates1008 (i : Input) (f : Name) : Prop :=
  f ∈ i.decisions ∧ i.ClaimedName f ∧ f ∉ i.decidableResults ∧
    ¬ ∃ k ∈ i.contracts, k.impl = f ∧ k.IsDecision ∧ i.ClaimedName k.theorem_

/-- RG1009: the specification of the decision contract `c` and its implementation or acceptance
predicate reach one Boolean test outside the toolchain. -/
def Violates1009 (i : Input) (c : Name) : Prop :=
  ∃ k ∈ i.contracts, k.theorem_ = c ∧ i.ClaimedName c ∧ k.IsDecision ∧
    ∃ t, i.ProjectTest t ∧ (∃ s ∈ k.spec, i.Reaches s t) ∧
      (i.Reaches k.impl t ∨ ∃ a ∈ k.accept, i.Reaches a t)

/-- The intent record of RG1007. -/
def rg1007 := ruleRecord "RG1007" Violates1007
/-- The intent record of RG1008. -/
def rg1008 := ruleRecord "RG1008" Violates1008
/-- The intent record of RG1009. -/
def rg1009 := ruleRecord "RG1009" Violates1009

end RegulaSpecification
