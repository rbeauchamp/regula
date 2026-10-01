module

/-! # Generated declaration families

The families of declarations Lean generates from another declaration that a finding is attributed
to. Each family has one relating clause: the checker's collector reads most of them from the
environment (`Regula.Collect.generatedBy?`, trying them in the order of `GeneratedFamily.all`),
and a compiled recursion helper is related by the admitted helper authorization
(`Regula.Findings.stepOf`). The RG1005 guidance names these families from the same list
(`GeneratedFamily.text`), each by its family name, with an example where one helps; it does not
list every member. The enumeration of the declarations Lean v4.34.0 generates, with the family
that covers each or the reason it is reported at its own location, is in
`docs/guides/proofs-and-boundaries.md#generated-declaration-families`. -/

@[expose] public section

namespace Regula

/-- A family of declarations Lean generates from another declaration. -/
inductive GeneratedFamily where
  /-- A constructor, generated from its inductive type. -/
  | constructor
  /-- A structure projection, generated from the structure's constructor. -/
  | projection
  /-- A recursor, an auxiliary recursor such as `casesOn`, or a `noConfusion`. -/
  | recursor
  /-- An equation lemma such as `f.eq_1`, `f.eq_def` or `f.eq_unfold`. -/
  | equationLemma
  /-- A declaration Lean generates on demand under a name it reserves, such as `f.induct`. -/
  | reservedName
  /-- A matcher `f.match_1`, and its equations and splitter. -/
  | matcher
  /-- The function a well-founded or `partial_fixpoint` definition `f` is compiled through, such as
  `f._unary`. -/
  | wellFounded
  /-- A helper of a structurally recursive definition `f`, such as its functional `f._f`. -/
  | structural
  /-- An auxiliary declaration Lean abstracts out of `f` or generates for it, such as
  `f._proof_1`. -/
  | auxiliaryLemma
  /-- A lemma Lean generates for a constructor, such as `c.injEq`. -/
  | constructorLemma
  /-- A construction Lean generates for an inductive type, such as `t.ctorIdx`. -/
  | typeConstruction
  /-- A structure field's default, such as `S.x._default`. -/
  | fieldDefault
  /-- The helper `f._unsafe_rec` Lean compiles a recursive definition `f` through. -/
  | recursionHelper
  deriving DecidableEq, Repr

/-- Every family, in the order the collector tries them. -/
def GeneratedFamily.all : List GeneratedFamily :=
  [.constructor, .projection, .recursor, .equationLemma, .reservedName, .matcher, .wellFounded,
    .structural, .auxiliaryLemma, .constructorLemma, .typeConstruction, .fieldDefault,
    .recursionHelper]

theorem GeneratedFamily.mem_all (family : GeneratedFamily) : family ∈ GeneratedFamily.all := by
  cases family <;> simp [GeneratedFamily.all]

/-- The family's name in the RG1005 guidance, with an example where one helps; the whole rewrite
fits its byte budget. It names the family, not every member. -/
def GeneratedFamily.text : GeneratedFamily → String
  | .constructor => "constructor"
  | .projection => "projection"
  | .recursor => "recursor such as `casesOn`"
  | .equationLemma => "equation lemma"
  | .reservedName => "reserved name such as `f.induct`"
  | .matcher => "matcher"
  | .wellFounded => "fixpoint helper"
  | .structural => "structural helper"
  | .auxiliaryLemma => "auxiliary declaration such as `f._proof_1`"
  | .constructorLemma => "constructor lemma"
  | .typeConstruction => "type construction"
  | .fieldDefault => "field default"
  | .recursionHelper => "recursion helper `f._unsafe_rec`"

end Regula
