import RegulaSpecification.Foundation

/-!
# RG1006: `unsafe`, `partial` and loop declarations

RG1006 refuses three things in a claimed module: a constant that is unsafe or partial, a constant
that has the name of a recursion helper, and a constant whose value mentions a loop construct of
Lean. A `while` needs no `partial` of the module that uses it: it compiles through a private
`partial` of Lean's library (`Init/While.lean`), so the flags alone do not show it. A constant with
a helper's name needs no flag either: the compiler reads `f._unsafe_rec` in place of `f` by its name
alone (`getDeclInfo?`, `Lean/Compiler/LCNF/ToDecl.lean:25-27`).

The one constant of these the rule admits has the form of the recursion helper that Lean's
elaborator adds for a safe recursive definition (`f._unsafe_rec`, a partial definition beside its
safe base).
The rule checks that form and nothing about what the helper computes, so a claimed module that adds
a constant of that form through its own code during the build passes (the specification's known
gap).
-/

namespace RegulaSpecification

open Lean (Name)

/-- The constants through which Lean's `while`, `repeat` and `repeat ... until` run: the one value
of the type `Lean.Loop` that they iterate over, and the loop itself (`Init/While.lean` at v4.35.0).
-/
def loopConstructs : List Name := [``Lean.Loop.mk, ``repeatM]

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

/-- The name of `d` is one that the compiler reads as a recursion helper: `b._unsafe_rec`, for some
name `b`. Nothing here depends on the constant's kind or flags. -/
def HelperNamed (d : Decl) : Prop := ∃ b : Name, d.name = Name.str b "_unsafe_rec"

/-- The value of `d` directly mentions a loop construct. -/
def MentionsLoop (d : Decl) : Prop := ∃ l ∈ loopConstructs, l ∈ d.valueUses

/-- RG1006: a claimed module holds a constant that is unsafe, partial or named as a recursion
helper, without the form of a recursion helper, or a constant whose value directly mentions a loop
construct. -/
def Violates1006 (i : Input) (c : Name) : Prop :=
  ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module ∧
    (((d.isUnsafe = true ∨ d.isPartial = true ∨ HelperNamed d) ∧ ¬ i.RecursionHelper d) ∨
      MentionsLoop d)

/-- The intent record of RG1006. -/
def rg1006 := ruleRecord "RG1006" Violates1006

end RegulaSpecification
