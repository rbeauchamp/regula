import RegulaSpecification.Foundation

/-!
# RG1006: `unsafe` and `partial` declarations

RG1006 reads each constant's safety. The one partial constant it admits has the form of the recursion
helper that Lean's elaborator adds for a safe recursive definition (`f._unsafe_rec`, a partial
definition beside its safe base). The rule checks that form and nothing about what the helper
computes, so a claimed module that adds a constant of that form through its own code during the build
passes (the specification's known gap).
-/

namespace RegulaSpecification

open Lean (Name)

namespace Input

variable (i : Input)

/-- `d` has the form of the recursion helper of a safe base in the same module: a partial,
safe-flagged definition named `f._unsafe_rec` beside a safe, total definition `f`, neither with an
`@[implemented_by]` or `@[extern]`. The base of a `partial def` is an opaque constant, so its helper
has not this form. -/
def RecursionHelper (d : Decl) : Prop :=
  d.isPartial = true ∧ d.isUnsafe = false ∧ d.implementedBy = none ∧ d.isExtern = false ∧
    ∃ base ∈ i.decls, d.name = Name.str base.name "_unsafe_rec" ∧ base.kind = .definition ∧
      base.module = d.module ∧ base.isUnsafe = false ∧ base.isPartial = false ∧
      base.implementedBy = none ∧ base.isExtern = false

end Input

/-- RG1006: a claimed module holds an unsafe or partial constant without the form of a recursion
helper. -/
def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧
    (d.isUnsafe = true ∨ d.isPartial = true) ∧ ¬ i.RecursionHelper d

/-- The intent record of RG1006. -/
def rg1006 := ruleRecord "RG1006" Violates1006

end RegulaSpecification
