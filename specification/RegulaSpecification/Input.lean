/-
Copyright (c) 2026 Regula contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Regula contributors
-/
module

/-!
# The closed input

Every rule of Regula reads one closed input: the constants Lean loads from a finished build, the
modules that the build claims, and the profile that the project states. This module states that
input as data, independently of the implementation. Each field says which interface of Lean or Lake
gives it. `Proofs/Load.lean` states what the loader gives in terms of those interfaces, and the
specification's trusted base lists what they report.

The input carries no source text, no message, no compiled code, no option and no build log: what a
rule cannot read here, it does not decide.
-/

public section

namespace RegulaSpecification

open Lean (Name)

/-- The kind of a constant, one for each constructor of Lean's `ConstantInfo`. -/
inductive Kind where
  /-- `ConstantInfo.axiomInfo`. -/
  | «axiom»
  /-- `ConstantInfo.defnInfo`. -/
  | «definition»
  /-- `ConstantInfo.thmInfo`. -/
  | «theorem»
  /-- `ConstantInfo.opaqueInfo`. -/
  | «opaque»
  /-- `ConstantInfo.quotInfo`. -/
  | quotient
  /-- `ConstantInfo.inductInfo`. -/
  | «inductive»
  /-- `ConstantInfo.ctorInfo`. -/
  | constructor
  /-- `ConstantInfo.recInfo`. -/
  | recursor
  deriving DecidableEq, Repr

/-- The safety of a constant. Lean gives a definition one `DefinitionSafety` and each other constant
at most an unsafe flag, so a constant that is both unsafe and partial does not exist, and this type
cannot state one. -/
inductive Safety where
  /-- Neither `ConstantInfo.isUnsafe` nor `ConstantInfo.isPartial`. -/
  | safe
  /-- `ConstantInfo.isUnsafe`. -/
  | «unsafe»
  /-- `ConstantInfo.isPartial`. -/
  | «partial»
  deriving DecidableEq, Repr

/-- One constant of the loaded environment, as Lean reports it from the build's `.olean` files. -/
structure Decl where
  /-- Its name. -/
  name : Name
  /-- The module whose `.olean` holds it (`Environment.getModuleIdxFor?`). -/
  module : Name
  /-- `axiom` when any loaded module's own data states an axiom of this name (Lean's import can drop
  it for a theorem), and otherwise the `ConstantInfo` constructor of the constant Lean keeps. -/
  kind : Kind
  /-- Whether it is safe, unsafe or partial. -/
  safety : Safety
  /-- The constants that the type and value mention, the fields that `Lean.collectAxioms` walks:
  type and value of a definition, theorem or opaque constant, the type of an axiom, constructor or
  recursor, and the type and constructors of an inductive type. It covers the constant Lean keeps
  and each constant of this name that a loaded module's own data states, which Lean's import can
  drop. -/
  uses : List Name
  /-- The constants its value mentions, for a definition, theorem or opaque constant, and nothing
  for any other constant. RG1006 reads it for Lean's loop constructs. -/
  valueUses : List Name
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
  /-- The constants of the environment that the shell loads. -/
  decls : List Decl
  /-- Each name is the name of one constant. An environment keeps its constants in a hash map, so an
  input that holds a name twice is no reading of one, and this type cannot state it. -/
  unique : (decls.map (·.name)).Nodup

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
  /-- A constant reaches itself. -/
  | refl (c : Name) : Reaches c c
  /-- A constant reaches what a constant that it mentions reaches. -/
  | step {c u e : Name} (d : Decl) : d ∈ i.decls → d.name = c → u ∈ d.uses → Reaches u e →
      Reaches c e

/-- `a` names an axiom of the input. -/
def IsAxiom (a : Name) : Prop := ∃ d ∈ i.decls, d.name = a ∧ d.kind = .axiom

/-- `a` is an axiom in the transitive axiom set of `c`. -/
def AxiomOf (c a : Name) : Prop := i.Reaches c a ∧ i.IsAxiom a

/-- The admission of the closed input: what the shell refuses, as incomplete, before any rule runs.
Each mentioned constant is held, and at least one module is claimed, so that a claim of nothing is
not read as a pass. A rule reads only an input that has this form, so no rule has a case for one
that does not. -/
structure WellFormed : Prop where
  /-- Each mentioned constant is held. -/
  closed : ∀ d ∈ i.decls, ∀ u ∈ d.uses, i.Resolves u
  /-- At least one module is claimed. -/
  claims : i.modules ≠ []

end Input

end RegulaSpecification
