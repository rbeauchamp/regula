import Regula.Rules
import RegulaSpecification.CasesGate

/-!
# The link from the implementation's input to the specification's

The checker runs over `Regula.Closed.Input`, and the specification states each rule over
`RegulaSpecification.Input`: two types with the same fields, so that the specification is written
independently of the code. `toSpec` carries an input of the checker to the specification's, and each
theorem of this directory is stated about the function that the checker runs on an input `i` and the
predicate of the specification at `toSpec i`.

`ofSpec` goes the other way, so that a function of the checker is a checker of the specification's
input (`Checker`) and can meet a rule's intent record.
-/

namespace RegulaSpecification

open Lean (Name)

namespace Link

/-- The implementation's profile in the specification. -/
def profile : Regula.Closed.Profile → Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The specification's profile in the implementation. -/
def profile' : Profile → Regula.Closed.Profile
  | .kernelOnly => .kernelOnly
  | .choiceFree => .choiceFree
  | .standardLogical => .standardLogical

/-- The implementation's kind of constant in the specification. -/
def constKind : Regula.Closed.Kind → Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

/-- The specification's kind of constant in the implementation. -/
def constKind' : Kind → Regula.Closed.Kind
  | .axiom => .axiom
  | .definition => .definition
  | .theorem => .theorem
  | .opaque => .opaque
  | .quotient => .quotient
  | .inductive => .inductive
  | .constructor => .constructor
  | .recursor => .recursor

/-- The implementation's constant in the specification. -/
def decl (d : Regula.Closed.Decl) : Decl where
  name := d.name
  module := d.module
  kind := constKind d.kind
  isUnsafe := d.isUnsafe
  isPartial := d.isPartial
  uses := d.uses
  valueUses := d.valueUses
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  inToolchain := d.inToolchain

/-- The input of the checker as the specification's input. -/
def toSpec (i : Regula.Closed.Input) : Input where
  profile := profile i.profile
  modules := i.modules
  decls := i.decls.map decl
  loads := i.loads

/-- The specification's constant in the implementation. -/
def decl' (d : Decl) : Regula.Closed.Decl where
  name := d.name
  module := d.module
  kind := constKind' d.kind
  isUnsafe := d.isUnsafe
  isPartial := d.isPartial
  uses := d.uses
  valueUses := d.valueUses
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  inToolchain := d.inToolchain

/-- The specification's input as the input of the checker. -/
def ofSpec (s : Input) : Regula.Closed.Input where
  profile := profile' s.profile
  modules := s.modules
  decls := s.decls.map decl'
  loads := s.loads

theorem profile_surj (p : Profile) : profile (profile' p) = p := by cases p <;> rfl

theorem decl_decl' (d : Decl) : decl (decl' d) = d := by
  rcases d with ⟨_, _, k, _, _, _, _, _, _, _⟩
  cases k <;> rfl

/-- `ofSpec` loses nothing that the specification's input holds. -/
theorem toSpec_ofSpec (s : Input) : toSpec (ofSpec s) = s := by
  rcases s with ⟨p, m, ds, l⟩
  simp only [toSpec, ofSpec, profile_surj, List.map_map, Function.comp_def, decl_decl',
    List.map_id']

/-- The constant of the specification's input and the checker's constant have one name. -/
theorem mem_decls {i : Regula.Closed.Input} {x : Decl} :
    x ∈ (toSpec i).decls ↔ ∃ d ∈ i.decls, decl d = x := by simp [toSpec]

end Link

end RegulaSpecification
