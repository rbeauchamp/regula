module

@[expose] public section

namespace RegulaSpecification

open Lean (Name)

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

inductive Safety where
  | safe
  | «unsafe»
  | «partial»
  deriving DecidableEq, Repr

inductive CtorIdxForm where
  | none
  | defn (ind : Name)
  | impl (ind : Name)
  deriving DecidableEq, Repr

structure Decl where
  name : Name
  module : Name
  kind : Kind
  safety : Safety
  uses : List Name
  valueUses : List Name
  implementedBy : Option Name
  isExtern : Bool
  initFn : Option Name
  inToolchain : Bool
  ctorIdxForm : CtorIdxForm
  deriving DecidableEq, Repr

inductive Profile where
  | kernelOnly
  | choiceFree
  | standardLogical
  deriving DecidableEq, Repr

structure CSimpEntry where
  module : Name
  thm : Name
  deriving DecidableEq, Repr

structure Input where
  profile : Profile
  modules : List Name
  moduleFiles : List Name
  claimedConstants : List Name
  csimps : List CSimpEntry
  decls : List Decl
  unique : (decls.map (·.name)).Nodup

namespace Input

variable (i : Input)

def ClaimedModule (m : Name) : Prop := m ∈ i.modules

def ModuleFile (m : Name) : Prop := m ∈ i.moduleFiles

def DeclaredInClaimed (c : Name) : Prop := c ∈ i.claimedConstants

def HasCSimp (m thm : Name) : Prop := ⟨m, thm⟩ ∈ i.csimps

def ClaimedName (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module

def Resolves (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c

inductive Reaches : Name → Name → Prop
  | refl (c : Name) : Reaches c c
  | step {c u e : Name} (d : Decl) : d ∈ i.decls → d.name = c → u ∈ d.uses → Reaches u e →
      Reaches c e

def IsAxiom (a : Name) : Prop := ∃ d ∈ i.decls, d.name = a ∧ d.kind = .axiom

def AxiomOf (c a : Name) : Prop := i.Reaches c a ∧ i.IsAxiom a

def CtorIdxPair (ind : Name) (defDecl implDecl : Decl) : Prop :=
  let defName := Name.str ind "ctorIdx"
  let implName := Name.str defName "_impl"
  (∃ g ∈ i.decls, g.name = `getObjTagNat ∧ g.inToolchain = true) ∧
  (∃ indDecl ∈ i.decls, indDecl.name = ind ∧ indDecl.kind = .inductive ∧
    indDecl.safety = .safe ∧ indDecl.module = defDecl.module) ∧
  defDecl.name = defName ∧ defDecl.kind = .definition ∧ defDecl.safety = .safe ∧
  defDecl.ctorIdxForm = .defn ind ∧ defDecl.implementedBy = some implName ∧
  defDecl.isExtern = false ∧ defDecl.initFn = none ∧
  implDecl.name = implName ∧ implDecl.module = defDecl.module ∧
  implDecl.kind = .definition ∧ implDecl.safety = .unsafe ∧
  implDecl.ctorIdxForm = .impl ind ∧ implDecl.implementedBy = none ∧
  implDecl.isExtern = false ∧ implDecl.initFn = none

def CtorIdxDef (d : Decl) : Prop :=
  ∃ ind implDecl, implDecl ∈ i.decls ∧ i.CtorIdxPair ind d implDecl

def CtorIdxImpl (d : Decl) : Prop :=
  ∃ ind defDecl, defDecl ∈ i.decls ∧ i.CtorIdxPair ind defDecl d

structure WellFormed : Prop where
  closed : ∀ d ∈ i.decls, ∀ u ∈ d.uses, i.Resolves u
  claims : i.modules ≠ []

end Input

end RegulaSpecification
