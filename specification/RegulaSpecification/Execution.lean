import RegulaSpecification.RuleRecord

/-!
# Escape hatches and execution: RG1006, RG3001 and RG3002

RG1006 reads each constant's safety. The one partial constant it admits is the recursion helper
Lean's elaborator adds for a safe recursive definition (`f._unsafe_rec`, observed at v4.34.1 as a
partial definition beside its safe base). That a helper computes what its base does is an
execution question, which RG3002 decides under a checked execution claim.

RG3001 and RG3002 read the execution closure of an executable target: from its `main`, the
constants compiled code can run. A constant with a runtime replacement runs the replacement, one
with a recursion helper runs the helper, and every other constant runs the constants its value
mentions.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Input

variable (i : Input)

/-- `d` is the recursion helper of a safe base in the same module: a partial, safe-flagged
definition named `f._unsafe_rec` beside a safe, total `f` with no runtime replacement. -/
def RecursionHelper (d : Decl) : Prop :=
  d.isPartial = true ∧ d.isUnsafe = false ∧ d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ base ∈ i.decls, d.name = Name.str base.name "_unsafe_rec" ∧ base.module = d.module ∧
      base.isUnsafe = false ∧ base.isPartial = false ∧ base.implementedBy = none ∧
      base.isExtern = false

/-- `c` has a recursion helper in the input. -/
def HasHelper (c : Name) : Prop :=
  ∃ h ∈ i.decls, h.name = Name.str c "_unsafe_rec" ∧ i.RecursionHelper h

/-- The constants compiled code runs where it runs `d`. -/
def Runs (d : Decl) (n : Name) : Prop :=
  d.implementedBy = some n ∨
    (d.implementedBy = none ∧ i.HasHelper d.name ∧ n = Name.str d.name "_unsafe_rec") ∨
    (d.implementedBy = none ∧ ¬ i.HasHelper d.name ∧ n ∈ d.uses)

/-- `c` is in the execution closure of `r`. -/
inductive Executes : Name → Name → Prop
  | root (r : Name) : Executes r r
  | step {r c n : Name} (d : Decl) : Executes r c → d ∈ i.decls → d.name = c → i.Runs d n →
      Executes r n

/-- `r` is the `main` of an executable target claimed with execution mode `e`. -/
def ExecutableRoot (r : Name) (e : Execution) : Prop :=
  ∃ t ∈ i.targets, t.kind = .executable ∧ (∃ p, ⟨t.name, .claimed p e⟩ ∈ i.manifest) ∧
    ∃ d ∈ i.decls, d.name = r ∧ r = `main ∧ d.module ∈ t.modules

/-- `d` is code whose run no theorem of Lean can bind to a kernel value: foreign code (`@[extern]`),
a partial definition that is not a recursion helper, whose kernel value is opaque, or a value that
an initializer sets when the program starts. -/
def Unbindable (d : Decl) : Prop :=
  d.isExtern = true ∨ (d.isPartial = true ∧ ¬ i.RecursionHelper d) ∨ d.isInitialized = true

/-- `c` is an execution boundary outside the toolchain: compiled code runs something other than
its kernel definition there. -/
def Boundary (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ d.inToolchain = false ∧
    (d.implementedBy.isSome = true ∨ i.HasHelper c ∨ i.Unbindable d)

/-- `c` is a boundary outside the toolchain that no correspondence theorem can discharge. -/
def UnbindableBoundary (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ d.inToolchain = false ∧ i.Unbindable d

end Input

/-- RG1006: a constant of a claimed module is unsafe or partial, and is not a recursion helper. -/
def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧ (d.isUnsafe = true ∨ d.isPartial = true) ∧
    ¬ i.RecursionHelper d

/-- RG3001: the execution closure of a claimed executable reaches a name the input does not
resolve. -/
def Violates3001 (i : Input) (c : Name) : Prop :=
  ∃ r e, i.ExecutableRoot r e ∧ i.Executes r c ∧ ¬ i.Resolves c

/-- RG3002: under a checked execution claim, the closure reaches a boundary that no theorem of a
claimed module states the correspondence of, or a boundary that no theorem can bind (`Unbindable`). -/
def Violates3002 (i : Input) (c : Name) : Prop :=
  ∃ r, i.ExecutableRoot r .checked ∧ i.Executes r c ∧ i.Boundary c ∧
    (Goal.corresponds c ∉ i.proved ∨ i.UnbindableBoundary c)

/-- The intent record of RG1006. -/
def rg1006 := ruleRecord "RG1006" Violates1006
/-- The intent record of RG3001. -/
def rg3001 := ruleRecord "RG3001" Violates3001
/-- The intent record of RG3002. -/
def rg3002 := ruleRecord "RG3002" Violates3002

end RegulaSpecification
