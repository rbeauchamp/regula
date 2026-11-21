module

/-!
# The closed input

Every rule of Regula reads one closed input: the constants Lean loads from a finished build, the
modules that the build claims, the loaded modules that are {lit}`module` files, and the profile that the
project states. This module states that
input as data, independently of the implementation. Each field says which interface of Lean or Lake
gives it. {lit}`Proofs/Load.lean` states what the loader gives in terms of those interfaces, and the
specification's trusted base lists what they report.

The input carries no source text, no message, no compiled code, no option and no build log: what a
rule cannot read here, it does not decide.
-/

@[expose] public section

namespace RegulaSpecification

open Lean (Name)

/-- The kind of a constant, one for each constructor of Lean's {lit}`ConstantInfo`. -/
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

/-- The safety of a constant. Lean gives a definition one {lit}`DefinitionSafety` and each other constant
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

/-- One constant of the loaded environment, as Lean reports it from the build's {lit}`.olean` files. -/
structure Decl where
  /-- Its name. -/
  name : Name
  /-- The module whose {lit}`.olean` holds it (`Environment.getModuleIdxFor?`). -/
  module : Name
  /-- `axiom` when any loaded module's own data states an axiom of this name (Lean's import can drop
  it for a theorem), and otherwise the {lit}`ConstantInfo` constructor of the constant Lean keeps. -/
  kind : Kind
  /-- Whether it is safe, unsafe or partial. -/
  safety : Safety
  /-- The constants that it mentions: what Lean's kernel checks it against when Lean replays it, the type of
  each constant, the value of a definition, theorem or opaque constant, the constructors and the other types of
  an inductive type's block, the inductive type of a constructor, the types of a recursor's block, and {name}`Eq` for a
  quotient. It covers the constant Lean keeps and each constant of this name that a loaded module's own data
  states, which Lean's import can drop. -/
  uses : List Name
  /-- The constants its value mentions, for a definition, theorem or opaque constant, and nothing
  for any other constant. RG1006 reads it for Lean's loop constructs and {name}`Lean.Order.fix`,
  and RG1012 for panic forms. -/
  valueUses : List Name
  /-- The constant {attr}`@[implemented_by]` names, if any (`Lean.Compiler.getImplementedBy?`). RG1011 reads
  it, and so does the form of a recursion helper (RG1006). -/
  implementedBy : Option Name
  /-- Whether it is {attr}`@[extern]` (`Lean.isExtern`). RG1011 reads it, and so does the form of a recursion
  helper (RG1006). -/
  isExtern : Bool
  /-- The initialization function that {attr}`@[init]` or {attr}`@[builtin_init]` names for it, if any
  (`Lean.getInitFnNameFor?`). RG1011 reads it of a definition. -/
  initFn : Option Name
  /-- Whether its module belongs to the Lean toolchain's own library. -/
  inToolchain : Bool
  deriving DecidableEq, Repr

/-- The foundation profiles a project can state. -/
inductive Profile where
  /-- No axiom. -/
  | kernelOnly
  /-- {name}`propext` and {name}`Quot.sound` only. -/
  | choiceFree
  /-- {name}`propext`, {name}`Quot.sound` and {name}`Classical.choice`. -/
  | standardLogical
  deriving DecidableEq, Repr

/-- An exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entry registered in a module
(`Lean.Compiler.CSimp.ext.ext.getModuleEntries`). -/
structure CSimpEntry where
  /-- The module whose extension entries hold this registration. -/
  module : Name
  /-- The theorem or declaration that {attr}`@[csimp]` names (`Lean.Compiler.CSimp.Entry.thmName`). -/
  thm : Name
  deriving DecidableEq, Repr

/-- The closed input of one run. -/
structure Input where
  /-- The profile that the project states. -/
  profile : Profile
  /-- The claimed modules: each module of a default target of the root package, and each module of
  the root package that their imports reach. -/
  modules : List Name
  /-- The loaded modules whose {lit}`.olean` states that Lean read the file as a {lit}`module` file
  (`ModuleData.isModule`). RG1013 reads it. -/
  moduleFiles : List Name
  /-- Of the names that the entries of {lit}`csimps` give, those that a claimed module's own {lit}`.olean`
  data declares (`ModuleData.constNames`). On merged theorems, `Environment.getModuleIdxFor?` keeps the first
  module ({lit}`Lean/Environment.lean:2345` at v4.35.0), which can be unclaimed even when a claimed module
  declared the theorem; RG1011 reads this list so merged claimed theorems count as claimed. -/
  claimedConstants : List Name
  /-- Exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entries of claimed modules
  (`Lean.Compiler.CSimp.ext.ext.getModuleEntries`). RG1011 reads them. -/
  csimps : List CSimpEntry
  /-- The constants of the environment that the shell loads. -/
  decls : List Decl
  /-- Each name is the name of one constant. An environment keeps its constants in a hash map, so an
  input that holds a name twice is no reading of one, and this type cannot state it. -/
  unique : (decls.map (·.name)).Nodup

namespace Input

variable (i : Input)

/-- Module {name}`m` is claimed. -/
def ClaimedModule (m : Name) : Prop := m ∈ i.modules

/-- Lean read the file of the module {name}`m` as a {lit}`module` file. -/
def ModuleFile (m : Name) : Prop := m ∈ i.moduleFiles

/-- {name}`c`, which an exported {attr}`@[csimp]` entry of a claimed module names, is declared in a claimed
module's own {lit}`.olean` data. -/
def DeclaredInClaimed (c : Name) : Prop := c ∈ i.claimedConstants

/-- Module {name}`m` has an exported {attr}`@[csimp]` entry naming {name}`thm`. -/
def HasCSimp (m thm : Name) : Prop := ⟨m, thm⟩ ∈ i.csimps

/-- {name}`c` names a constant of a claimed module. -/
def ClaimedName (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module

/-- {name}`c` names a constant of the input. -/
def Resolves (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c

/-- {lit}`e` is {lit}`c` or a constant that {lit}`c` reaches through the constants each mentions. -/
inductive Reaches : Name → Name → Prop
  /-- A constant reaches itself. -/
  | refl (c : Name) : Reaches c c
  /-- A constant reaches what a constant that it mentions reaches. -/
  | step {c u e : Name} (d : Decl) : d ∈ i.decls → d.name = c → u ∈ d.uses → Reaches u e →
      Reaches c e

/-- {name}`a` names an axiom of the input. -/
def IsAxiom (a : Name) : Prop := ∃ d ∈ i.decls, d.name = a ∧ d.kind = .axiom

/-- {name}`a` is an axiom in the transitive axiom set of {name}`c`. -/
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
