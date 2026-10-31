import Regula.Rules
import RegulaSpecification.CasesGate

/-!
# The link from the implementation's input to the specification's

The checker runs over `Regula.Closed.Input`, and the specification states each rule over
`RegulaSpecification.Input`: two types with the same fields, so that the specification is written
independently of the code. `toSpec` carries an input of the checker to the specification's, and each
theorem of this directory is stated about the function that the checker runs on an input `i` and the
predicate of the specification at `toSpec i`.

One field differs. `Decl.axioms` is the checker's: it holds what `Lean.collectAxioms` gives in the
loader, and the specification states the axiom set as `Input.AxiomOf`. `AxiomsRead` states that they
agree, as a hypothesis of each theorem that reads the set. No proof examines `Lean.collectAxioms`, so
this is an assumption about Lean (the specification's trusted base).

`ofSpec` goes the other way, so that a function of the checker is a checker of the specification's
input (`Checker`) and can meet a rule's intent record. It is noncomputable, because it fills
`Decl.axioms` with the set that `AxiomOf` states, and it is used only in statements.
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

/-- The implementation's constant in the specification. It has no axiom set: `Input.AxiomOf` states
that. -/
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

open Classical in
/-- The axiom set that `AxiomOf` states for `c`, as a list. -/
noncomputable def axiomList (s : Input) (c : Name) : List Name :=
  (s.decls.map (·.name)).filter fun a => decide (s.AxiomOf c a)

/-- The specification's constant in the implementation, with the set that `AxiomOf` states. -/
noncomputable def decl' (s : Input) (d : Decl) : Regula.Closed.Decl where
  name := d.name
  module := d.module
  kind := constKind' d.kind
  isUnsafe := d.isUnsafe
  isPartial := d.isPartial
  uses := d.uses
  valueUses := d.valueUses
  axioms := some (axiomList s d.name)
  implementedBy := d.implementedBy
  isExtern := d.isExtern
  inToolchain := d.inToolchain

/-- The specification's input as the input of the checker. -/
noncomputable def ofSpec (s : Input) : Regula.Closed.Input where
  profile := profile' s.profile
  modules := s.modules
  decls := s.decls.map (decl' s)
  loads := s.loads

theorem profile_surj (p : Profile) : profile (profile' p) = p := by cases p <;> rfl

theorem decl_decl' (s : Input) (d : Decl) : decl (decl' s d) = d := by
  rcases d with ⟨_, _, k, _, _, _, _, _, _, _⟩
  cases k <;> rfl

/-- `ofSpec` loses nothing that the specification's input holds. -/
theorem toSpec_ofSpec (s : Input) : toSpec (ofSpec s) = s := by
  rcases s with ⟨p, m, ds, l⟩
  simp only [toSpec, ofSpec, profile_surj, List.map_map, Function.comp_def, decl_decl', List.map_id']

/-- The constant of the specification's input and the checker's constant have one name. -/
theorem mem_decls {i : Regula.Closed.Input} {x : Decl} :
    x ∈ (toSpec i).decls ↔ ∃ d ∈ i.decls, decl d = x := by simp [toSpec]

/-- What the theorems that read an axiom set assume of the input. Each constant of a claimed module
has a set, and each set is the one that `AxiomOf` states: the loader computes it with
`Lean.collectAxioms`, and no proof examines that function. -/
structure AxiomsRead (i : Regula.Closed.Input) : Prop where
  /-- Each constant of a claimed module has a set. -/
  present : ∀ d ∈ i.decls, (toSpec i).ClaimedModule d.module → d.axioms.isSome = true
  /-- Each set holds exactly the axioms of the constant. -/
  faithful : ∀ d ∈ i.decls, ∀ as, d.axioms = some as → ∀ a, a ∈ as ↔ (toSpec i).AxiomOf d.name a

/-- What the theorems of this directory assume of an input: it has the closed form, and it holds
the axiom sets that `AxiomOf` states. -/
structure Admitted (i : Regula.Closed.Input) : Prop where
  /-- The specification's admission. -/
  wf : (toSpec i).WellFormed
  /-- The axiom sets. -/
  axioms : AxiomsRead i

end Link

end RegulaSpecification
