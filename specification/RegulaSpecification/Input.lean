/-!
# The closed input

Every rule of Regula reads one closed input: the constants Lean loads from a finished build, the
modules that the build claims, and the profile that the project states. This module states that input
as data, independently of the implementation. Each field says which interface of Lean or Lake gives
it; that the shell reads the field through that interface is not a fact this module establishes, and
the specification's trusted base lists it.

The input carries no source text, no message, no compiled code, no option and no build log: what a
rule cannot read here, it does not decide.
-/

namespace RegulaSpecification

open Lean (Name)

/-- The kind of a constant, one for each constructor of Lean's `ConstantInfo`. -/
inductive Kind where
  | «axiom»
  | «definition»
  | «theorem»
  | «opaque»
  | quotient
  | «inductive»
  | constructor
  | recursor
  deriving DecidableEq, Repr

/-- One constant of the loaded environment, as Lean reports it from the build's `.olean` files. -/
structure Decl where
  /-- Its name. A loaded environment holds at most one constant of each name. -/
  name : Name
  /-- The module whose `.olean` holds it (`Environment.getModuleIdxFor?`). -/
  module : Name
  /-- Its `ConstantInfo` constructor. -/
  kind : Kind
  /-- `ConstantInfo.isUnsafe`. -/
  isUnsafe : Bool
  /-- `ConstantInfo.isPartial`. -/
  isPartial : Bool
  /-- The constants its type and value mention, the ones `Lean.collectAxioms` walks: type and
  value of a definition, theorem or opaque constant, the type of an axiom, constructor or
  recursor, and the type and constructors of an inductive type. -/
  uses : List Name
  /-- The constant `@[implemented_by]` names, if any (`Lean.Compiler.getImplementedBy?`). Only the
  form of a recursion helper (RG1006) reads it. -/
  implementedBy : Option Name
  /-- Whether it is `@[extern]` (`Lean.isExtern`). Only the form of a recursion helper reads it. -/
  isExtern : Bool
  /-- Whether its module belongs to the Lean toolchain's own library. -/
  inToolchain : Bool
  deriving DecidableEq, Repr

/-- The foundation profiles a project can state. -/
inductive Profile where
  /-- No axiom. -/
  | kernelOnly
  /-- `propext` and `Quot.sound` only. -/
  | choiceFree
  /-- `propext`, `Quot.sound` and `Classical.choice`. -/
  | standardLogical
  deriving DecidableEq, Repr

/-- The closed input of one run. -/
structure Input where
  /-- The profile that the project states. -/
  profile : Profile
  /-- The claimed modules: each module of a default target of the root package, and each module of
  the root package that their imports reach. -/
  modules : List Name
  /-- The constants of the claimed modules, with each constant that they reach through what each
  mentions. -/
  decls : List Decl
  /-- The modules the environment imports (the module names of its header). -/
  loads : List Name

namespace Input

variable (i : Input)

/-- Module `m` is claimed. -/
def ClaimedModule (m : Name) : Prop := m ∈ i.modules

/-- `c` names a constant of a claimed module. -/
def ClaimedName (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module

/-- `c` names a constant of the input. -/
def Resolves (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c

/-- `e` is `c` or a constant that `c` reaches through the constants each mentions. -/
inductive Reaches : Name → Name → Prop
  | refl (c : Name) : Reaches c c
  | step {c u e : Name} (d : Decl) : d ∈ i.decls → d.name = c → u ∈ d.uses → Reaches u e →
      Reaches c e

/-- `a` names an axiom of the input. -/
def IsAxiom (a : Name) : Prop := ∃ d ∈ i.decls, d.name = a ∧ d.kind = .axiom

/-- `a` is an axiom in the transitive axiom set of `c`. -/
def AxiomOf (c a : Name) : Prop := i.Reaches c a ∧ i.IsAxiom a

/-- The admission of the closed input: what the shell refuses, as incomplete, before any rule runs.
Each name is the name of one constant; each mentioned constant is held; at least one module is
claimed, so that a claim of nothing is not read as a pass; each claimed module is loaded. -/
structure WellFormed : Prop where
  unique : (i.decls.map (·.name)).Nodup
  closed : ∀ d ∈ i.decls, ∀ u ∈ d.uses, i.Resolves u
  claims : i.modules ≠ []
  loaded : ∀ m ∈ i.modules, m ∈ i.loads

end Input

end RegulaSpecification
