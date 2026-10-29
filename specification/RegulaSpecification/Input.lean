/-!
# The closed input

Every kept and new rule of the smaller Regula reads one closed input: the declarations Lean loads
from the finished build, with the compiled code that the build records for each, Lake's own list
of the targets and modules it builds, and the project's claim (`foundation_manifest.json`). This
module states that input as data, independently of any implementation. Each field says which
interface of Lean or Lake gives it; that the shell reads the field through that interface is the
implementation's obligation (#483), not a fact this module establishes. The mechanism that reads
compiled code is #487's.

The input carries no source text, no message, no info tree, no option set in source, no build log
and no file listing: what a rule cannot read here, it does not decide.
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

/-- One point at which compiled code departs from a kernel value: where the kernel value has the
constant `reference`, compiled code runs `runs`. A runtime replacement (`@[implemented_by]`), a
`@[csimp]` rewrite at a call site, local or global, a recursion helper, and each other departure
give one. -/
structure Departure where
  /-- The constant that the kernel value has at this point. -/
  reference : Name
  /-- The constant that compiled code runs in its place. -/
  runs : Name
  /-- Whether a module of the toolchain's own library makes the departure: a replacement or a
  `@[csimp]` lemma that such a module registers, or the recursion helper of a toolchain constant. -/
  inToolchain : Bool
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
  form of a recursion helper (RG1006) reads it: the execution closure reads `compiled` and
  `departures`. -/
  implementedBy : Option Name
  /-- The constants its compiled code runs, as the build's compiled code records them. -/
  compiled : List Name
  /-- Each point at which its compiled code departs from its kernel value, as the build's compiled
  code records it. -/
  departures : List Departure
  /-- Whether it is `@[extern]` (`Lean.isExtern`). -/
  isExtern : Bool
  /-- Whether an `initialize` or `builtin_initialize` declaration sets its value when the program
  starts (`Lean.getInitFnNameFor?`). -/
  isInitialized : Bool
  /-- Whether Lean marks it `noncomputable` (`Lean.isNoncomputable`). -/
  isNoncomputable : Bool
  /-- Whether its type's result is `Bool`, or it is an instance of `BEq`, and it is no field's
  projection function: a Boolean test. A projection reads a field of data, which no definition
  computes. -/
  isBoolTest : Bool
  /-- Whether its module belongs to the Lean toolchain's own library (`Init`, `Std`, `Lean`). -/
  inToolchain : Bool
  deriving DecidableEq, Repr

/-- One module of the root package that Lake builds, as Lean reads its `.olean` files. -/
structure ModuleRecord where
  /-- The module's name. -/
  name : Name
  /-- The modules it imports (`ModuleData.imports`). -/
  imports : List Name
  /-- The names of the environment extensions that have entries in any part of its `.olean`
  (`ModuleData.entries` of the exported, server and private parts). -/
  extensions : List Name
  deriving DecidableEq, Repr

/-- The two kinds of Lake target that a claim classifies. -/
inductive TargetKind where
  | library
  | executable
  deriving DecidableEq, Repr

/-- One root-package target, from Lake's own load of the workspace. -/
structure Target where
  /-- Its Lake name. -/
  name : Name
  /-- Library or executable. -/
  kind : TargetKind
  /-- The modules Lake builds for it: a library's modules, an executable's root module. -/
  modules : List Name
  /-- The options Lake gives Lean for its modules (`leanOptions`, and `-D` arguments). -/
  options : List (Name × String)
  /-- Every other way the target changes Lean's process: plugins, dynamic libraries and every
  extra Lean argument that is not a `-D` option. -/
  extras : List String
  /-- Whether it is a default target of the root package (`defaultTargets` in Lake's load).
  `lake check` checks only the modules of the default targets. -/
  isDefault : Bool
  deriving DecidableEq, Repr

/-- The foundation profiles a surface can claim. -/
inductive Profile where
  /-- No axiom. -/
  | kernelOnly
  /-- `propext` and `Quot.sound` only. -/
  | choiceFree
  /-- `propext`, `Quot.sound` and `Classical.choice`. -/
  | standardLogical
  deriving DecidableEq, Repr

/-- The execution mode a surface claims. -/
inductive Execution where
  /-- Execution boundaries are reported. -/
  | report
  /-- Each reachable execution boundary needs a kernel-checked correspondence. -/
  | checked
  deriving DecidableEq, Repr

/-- How the claim classifies one target. -/
inductive Classification where
  | claimed (profile : Profile) (execution : Execution)
  | excluded
  deriving DecidableEq, Repr

/-- One entry of the claim: a target and its classification. -/
structure Entry where
  target : Name
  classification : Classification
  deriving DecidableEq, Repr

/-- The decision kind of an executable contract. -/
inductive ContractKind where
  | decides
  | decidesSoundly
  | decidesCompletely
  /-- Any other relation: a contract that is not a decision kind. -/
  | other
  deriving DecidableEq, Repr

/-- One executable contract: a theorem whose type is `ExecutableContract f R`, read from its type. -/
structure Contract where
  /-- The theorem. -/
  theorem_ : Name
  /-- The head constant `f` of the implementation. -/
  impl : Name
  /-- The number of arguments the contract fixes for `f`; a closed contract fixes none. -/
  fixedArgs : Nat
  /-- The decision kind, if any. -/
  kind : ContractKind
  /-- The constants the specification of a decision kind mentions. -/
  spec : List Name
  /-- The constants the acceptance predicate mentions. -/
  accept : List Name
  deriving DecidableEq, Repr

/-- The obligations lean-intent states of an intent record. -/
inductive Obligation where
  | o1 | o2 | o3 | o4 | o5
  /-- O2 before a run: the record has a model (`LeanIntent.O2Run`). -/
  | o2Run
  /-- lean-intent's degenerate check: each degenerate subject of the record's type that meets it is
  one the owner confirmed (`LeanIntent.Degenerate`). -/
  | nondegenerate
  deriving DecidableEq, Repr

/-- A constant named by its module and its name. Two environments can each hold a constant of one
name, such as the `main` of two executables, and the module tells them apart. -/
structure QualName where
  /-- The module whose `.olean` holds the constant. -/
  module : Name
  /-- The name of the constant. -/
  name : Name
  deriving DecidableEq, Repr

/-- A deliverable that the owner's record names: its implementation and its intent record, each
by its module and its name. -/
structure Deliverable where
  impl : QualName
  record : QualName
  deriving DecidableEq, Repr

/-- A statement that a theorem proves, read from the theorem's type, which must be exactly the
statement that the matching goal former gives. A constant of a statement about a deliverable has
its module, which the environment that holds the theorem gives (`Environment.getModuleIdxFor?`). -/
inductive Goal where
  /-- The obligation `k` of the intent record `record`. -/
  | obligation (k : Obligation) (record : QualName)
  /-- The confirmed consequence `consequence` of the intent record `record`. -/
  | keeps (record consequence : QualName)
  /-- The implementation `impl` fulfils the intent record `record`. -/
  | fulfils (impl record : QualName)
  /-- The correspondence of the departure at which compiled code runs `runs` in place of
  `reference`. For a runtime replacement or a `@[csimp]` rewrite it is the equality
  `@reference = @runs`, which a `@[csimp]` lemma states. -/
  | corresponds (reference runs : Name)
  deriving DecidableEq, Repr

/-- A statement and the theorem that proves it. -/
structure Proof where
  statement : Goal
  theorem_ : Name
  deriving DecidableEq, Repr

/-- The closed input of one run. -/
structure Input where
  /-- The root package's library and executable targets, from Lake. -/
  targets : List Target
  /-- The claim. -/
  manifest : List Entry
  /-- The root-package modules Lake builds, as loaded. -/
  modules : List ModuleRecord
  /-- Every constant of one environment that the shell loads. -/
  decls : List Decl
  /-- The modules that environment imports (the module names of its header). -/
  loads : List Name
  /-- The executable contracts of claimed modules. -/
  contracts : List Contract
  /-- The functions that claimed modules register as decision functions. -/
  decisions : List Name
  /-- The decision functions whose result type is `Decidable`. -/
  decidableResults : List Name
  /-- The deliverables that the owner's committed confirmation record names, or `none` when the
  project has no such record. The project's own code does not name them, so removing a declaration
  removes no obligation. -/
  inventory : Option (List Deliverable)
  /-- Each statement that a theorem of the environment proves, with the theorem. -/
  proved : List Proof
  /-- The owner's confirmed or declined consequences: an intent record and a consequence. -/
  confirmed : List (QualName × QualName)

namespace Input

variable (i : Input)

/-- Module `m` is in target `t`, which the claim classifies as `c`. -/
def InTarget (m : Name) (c : Classification) : Prop :=
  ∃ t ∈ i.targets, m ∈ t.modules ∧ ⟨t.name, c⟩ ∈ i.manifest

/-- Module `m` is claimed with profile `p` and execution mode `e`. -/
def Claimed (m : Name) (p : Profile) (e : Execution) : Prop := i.InTarget m (.claimed p e)

/-- Module `m` is claimed. -/
def ClaimedModule (m : Name) : Prop := ∃ p e, i.Claimed m p e

/-- Module `m` is in an excluded target. -/
def ExcludedModule (m : Name) : Prop := i.InTarget m .excluded

/-- `c` names a constant of a claimed module. -/
def ClaimedName (c : Name) : Prop := ∃ d ∈ i.decls, d.name = c ∧ i.ClaimedModule d.module

/-- The constant `q` is in the input, in the module that `q` names, and that module is claimed. -/
def ClaimedConst (q : QualName) : Prop :=
  ∃ d ∈ i.decls, d.name = q.name ∧ d.module = q.module ∧ i.ClaimedModule d.module

/-- A theorem of a claimed module proves `g`. -/
def ProvedClaimed (g : Goal) : Prop := ∃ q ∈ i.proved, q.statement = g ∧ i.ClaimedName q.theorem_

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

/-- The admission of the closed input: what the shell refuses, as incomplete, before any rule
runs. Each name is the name of one constant; each mentioned constant is loaded; each module that
Lake lists for a target is loaded. -/
structure WellFormed : Prop where
  unique : (i.decls.map (·.name)).Nodup
  closed : ∀ d ∈ i.decls, ∀ u ∈ d.uses, i.Resolves u
  loaded : ∀ t ∈ i.targets, ∀ m ∈ t.modules, ∃ r ∈ i.modules, r.name = m

end Input

end RegulaSpecification
