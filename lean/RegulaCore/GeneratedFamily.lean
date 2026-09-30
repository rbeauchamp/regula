module

/-! # Generated declaration families

The families of declarations Lean generates from another declaration that a finding is attributed
to. The checker's collector relates a declaration to the one Lean generated it from by one clause
per family (`Regula.Collect.generatedBy?`), trying them in the order of `GeneratedFamily.all`, and
the RG1005 guidance names exactly these families (`GeneratedFamily.text`), so the documented list
and the executed clauses are the same closed set. -/

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
  /-- An equation lemma `f.eq_1`, `f.eq_def` or `f.eq_unfold`. -/
  | equationLemma
  /-- A declaration Lean generates on demand under a name it reserves, such as `f.induct`. -/
  | reservedName
  /-- A matcher `f.match_1`, and its equations and splitter. -/
  | matcher
  /-- The `f._unary` or `f._mutual` function a well-founded definition `f` is compiled through. -/
  | wellFounded
  /-- The functional `f._f` and smart-unfolding definition `f._sunfold` of a structurally
  recursive definition `f`. -/
  | structural
  /-- An auxiliary lemma such as `f._proof_1` that `f`'s value or equation information uses. -/
  | auxiliaryLemma
  /-- A constructor's `inj`, `injEq`, `sizeOf_spec` and `_flat_ctor`. -/
  | constructorLemma
  /-- An inductive type's `ctorIdx`, `noConfusionType`, `ctorElimType`, `_sizeOf_1` and
  `_sizeOf_inst`. -/
  | typeConstruction
  /-- A structure field's default `S.x._default` or `S.x._inherited_default`. -/
  | fieldDefault
  deriving DecidableEq, Repr

/-- Every family, in the order the collector tries them. -/
def GeneratedFamily.all : List GeneratedFamily :=
  [.constructor, .projection, .recursor, .equationLemma, .reservedName, .matcher, .wellFounded,
    .structural, .auxiliaryLemma, .constructorLemma, .typeConstruction, .fieldDefault]

theorem GeneratedFamily.mem_all (family : GeneratedFamily) : family ∈ GeneratedFamily.all := by
  cases family <;> simp [GeneratedFamily.all]

/-- The family's short name in the RG1005 guidance, whose whole rewrite fits its byte budget. -/
def GeneratedFamily.text : GeneratedFamily → String
  | .constructor => "constructor"
  | .projection => "projection"
  | .recursor => "recursor or `casesOn`"
  | .equationLemma => "equation lemma"
  | .reservedName => "reserved `f.induct`"
  | .matcher => "matcher"
  | .wellFounded => "`f._unary`"
  | .structural => "`f._f` or `f._sunfold`"
  | .auxiliaryLemma => "`f._proof_1` used by `f`"
  | .constructorLemma => "`c.injEq`, `c.sizeOf_spec` or `c._flat_ctor`"
  | .typeConstruction => "`t.ctorIdx` or `t._sizeOf_1`"
  | .fieldDefault => "default `S.x._default`"

end Regula
