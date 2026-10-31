import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The closed input

The one input every rule of the checker reads: the constants Lean loads from the finished build,
Lake's own list of the targets and the modules it builds, and the project's claim
(`foundation_manifest.json`). It carries no source text, message, info tree, option set in source,
build log or file listing, so a rule cannot decide anything that is not here.

The types follow the specification of the smaller Regula
(`specification/RegulaSpecification/Input.lean`, `Gate.lean`): `Decl`, `ModuleRecord`, `Target`,
`Entry`, `Contract`, `Input` and `Bundle` have the specification's fields, and `Bundle.refusal?`
decides the specification's admission
(`Bundle.WellFormed`, `Input.WellFormed`), and the input that a rule reads the axiom set of a
constant from. That the shell (`Regula.Load`) fills each field through the interface its docstring
names is trusted. `specification/RegulaSpecification/Proofs/` proves each rule function of
`Regula.Rules` against the specification's violation predicate, and this admission against its
statement.

Two choices are the implementation's, made on the owner's behalf:

- `decls` holds the constants of the environment that the rules can reach: every constant of a
  claimed module, the `main` of each executable root, the theorems that state a correspondence, and
  everything these mention or run, with each constant that a checked claim's boundaries of `main`
  reach (`Regula.Load.Facts.boundaries`). Each rule of the specification quantifies over such constants,
  and a departure that only a constant off the list records is left out: no executed code makes
  it. That the rules decide the same on this list as on every constant of the environment is
  argued, with no theorem. The list stays small for an environment that imports `Lean`.
- A `Target`'s options keep Lake's own values as text (`Target.options`), as the specification
  states them.
-/

namespace Regula.Closed

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
  deriving DecidableEq, Repr, Inhabited

/-- One point at which compiled code can depart from a kernel value: where the kernel value has the
constant `reference`, compiled code runs `runs`, whether or not the compiler leaves a call of `runs`
that a read of the code shows. -/
structure Departure where
  /-- The constant that the kernel value has at this point. -/
  reference : Name
  /-- The constant that compiled code runs in its place. -/
  runs : Name
  /-- Whether a module of the toolchain's own library makes the departure. -/
  inToolchain : Bool
  deriving DecidableEq, Repr, Inhabited

/-- One constant of a loaded environment, as Lean reports it from the build's `.olean` files. -/
structure Decl where
  /-- Its name. -/
  name : Name
  /-- The module whose `.olean` holds it (`Environment.getModuleIdxFor?`). -/
  module : Name
  /-- Its `ConstantInfo` constructor. -/
  kind : Kind
  /-- `ConstantInfo.isUnsafe`. -/
  isUnsafe : Bool
  /-- `ConstantInfo.isPartial`. -/
  isPartial : Bool
  /-- The constants its type and value mention, the ones `Lean.collectAxioms` walks. -/
  uses : List Name
  /-- Its transitive axiom set, as `Lean.collectAxioms` computes it from the loaded constants,
  for each constant whose axiom set a rule reads: a constant of a claimed module, and a theorem
  that states a correspondence. `none` for every other constant. -/
  axioms : Option (List Name)
  /-- The constant `@[implemented_by]` names, if any (`Lean.Compiler.getImplementedBy?`). -/
  implementedBy : Option Name
  /-- The constants its compiled code runs. -/
  compiled : List Name
  /-- Each point at which its compiled code departs from its kernel value. On the `main` of a checked
  claim, also each replacement and recursion helper outside the toolchain whose reference the closure
  of `main` reaches, whatever survives in compiled code (`Regula.Load.Facts.boundaries`). -/
  departures : List Departure
  /-- Whether it is `@[extern]` (`Lean.isExtern`). -/
  isExtern : Bool
  /-- Whether an initializer sets its value when the program starts (`Lean.getInitFnNameFor?`). -/
  isInitialized : Bool
  /-- Whether Lean marks it `noncomputable` (`Lean.isNoncomputable`). -/
  isNoncomputable : Bool
  /-- Whether its type's result is `Bool` or `BEq _` and it is no field's projection function: a
  Boolean test. -/
  isBoolTest : Bool
  /-- Whether its module belongs to the Lean toolchain's own library. -/
  inToolchain : Bool
  deriving Repr, Inhabited

/-- One module of the root package that Lake builds, as Lean reads its `.olean` files. -/
structure ModuleRecord where
  /-- The module's name. -/
  name : Name
  /-- The modules it imports (`ModuleData.imports`). -/
  imports : List Name
  /-- The names of the environment extensions that have entries in any part of its `.olean`. -/
  extensions : List Name
  deriving DecidableEq, Repr, Inhabited

/-- The two kinds of Lake target that a claim classifies. -/
inductive TargetKind where
  /-- A `lean_lib`. -/
  | library
  /-- A `lean_exe`. -/
  | executable
  deriving DecidableEq, Repr, Inhabited

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
  /-- Whether it is a default target of the root package. -/
  isDefault : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The foundation profiles a surface can claim. -/
inductive Profile where
  /-- No axiom. -/
  | kernelOnly
  /-- `propext` and `Quot.sound` only. -/
  | choiceFree
  /-- `propext`, `Quot.sound` and `Classical.choice`. -/
  | standardLogical
  deriving DecidableEq, Repr, Inhabited

/-- The execution mode a surface claims. -/
inductive Execution where
  /-- Execution boundaries are not checked. -/
  | report
  /-- Each reachable execution boundary needs an admitted correspondence. -/
  | checked
  deriving DecidableEq, Repr, Inhabited

/-- How the claim classifies one target. -/
inductive Classification where
  /-- Claimed with a profile and an execution mode. -/
  | claimed (profile : Profile) (execution : Execution)
  /-- Excluded from every claimed surface. -/
  | excluded
  deriving DecidableEq, Repr, Inhabited

/-- One entry of the claim: a target and its classification. -/
structure Entry where
  /-- The target, by its Lake name. -/
  target : Name
  /-- How the claim classifies it. -/
  classification : Classification
  deriving DecidableEq, Repr, Inhabited

/-- The decision kind of an executable contract. -/
inductive ContractKind where
  /-- `Regula.Decides`. -/
  | decides
  /-- `Regula.DecidesSoundly`. -/
  | decidesSoundly
  /-- `Regula.DecidesCompletely`. -/
  | decidesCompletely
  /-- Any other relation: a contract that is not a decision kind. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- One executable contract: a theorem whose type is `ExecutableContract f R`, read from its
type. -/
structure Contract where
  /-- The theorem. -/
  theorem_ : Name
  /-- The head constant `f` of the implementation, or `.anonymous` when its head is not a
  constant. -/
  impl : Name
  /-- The number of arguments the contract fixes for `f`. -/
  fixedArgs : Nat
  /-- The decision kind, if any. -/
  kind : ContractKind
  /-- The constants the specification of a decision kind mentions. -/
  spec : List Name
  /-- The constants the acceptance predicate mentions. -/
  accept : List Name
  deriving DecidableEq, Repr, Inhabited

/-- A theorem that states the correspondence `@reference = @runs` of a departure. -/
structure Correspondence where
  /-- The constant that the kernel value has. -/
  reference : Name
  /-- The constant that compiled code runs in its place. -/
  runs : Name
  /-- The theorem that states `@reference = @runs`. -/
  theorem_ : Name
  deriving DecidableEq, Repr, Inhabited

/-- The closed input of one environment. -/
structure Input where
  /-- The root package's library and executable targets, from Lake. -/
  targets : List Target
  /-- The claim. -/
  manifest : List Entry
  /-- The root-package modules Lake builds, as loaded. -/
  modules : List ModuleRecord
  /-- The constants of the environment that the rules can reach (see the module docstring). -/
  decls : List Decl
  /-- The modules the environment imports. -/
  loads : List Name
  /-- The executable contracts of claimed modules. -/
  contracts : List Contract
  /-- The functions that claimed modules register as decision functions. -/
  decisions : List Name
  /-- The decision functions whose result type is `Decidable`. -/
  decidableResults : List Name
  /-- Each correspondence that a theorem of the environment proves. -/
  proved : List Correspondence
  deriving Inhabited

/-- The closed input of one run: one `Input` for each environment the shell loads. -/
structure Bundle where
  /-- The input of each environment. -/
  envs : List Input
  deriving Inhabited

namespace Input

variable (i : Input)

/-- The constants of the input by name. -/
def index : Std.HashMap Name Decl :=
  i.decls.foldl (fun m d => m.insert d.name d) {}

/-- The profile and execution mode of each claim of a target that contains module `m`. -/
def claimsOf (m : Name) : List (Profile × Execution) :=
  i.targets.flatMap fun t =>
    if t.modules.contains m then
      i.manifest.filterMap fun e =>
        if e.target == t.name then
          match e.classification with
          | .claimed p x => some (p, x)
          | .excluded => none
        else none
    else []

/-- The claims of each module of a target, as `claimsOf` gives them, computed once for all
modules. -/
def claimTable : Std.HashMap Name (List (Profile × Execution)) :=
  (i.targets.flatMap (·.modules)).foldl (fun table m => table.insert m (i.claimsOf m)) {}

/-- Whether module `m` is claimed. -/
def claimedModule (m : Name) : Bool := !(i.claimsOf m).isEmpty

/-- Whether module `m` is in an excluded target. -/
def excludedModule (m : Name) : Bool :=
  i.targets.any fun t => t.modules.contains m &&
    i.manifest.any fun e => e.target == t.name && e.classification == .excluded

/-- Whether target `t` is claimed. -/
def claimedTarget (t : Name) : Bool :=
  i.manifest.any fun e => e.target == t && match e.classification with
    | .claimed .. => true
    | .excluded => false

/-- The first name of `names` that is in `seen` or that an earlier name of `names` repeats. -/
def duplicate? (seen : Std.HashSet Name) : List Name → Option Name
  | [] => none
  | n :: rest => if seen.contains n then some n else duplicate? (seen.insert n) rest

/-- The name of each constant. -/
def nameSet : Std.HashSet Name := i.decls.foldl (fun s d => s.insert d.name) {}

/-- The name of each module record. -/
def recordSet : Std.HashSet Name := i.modules.foldl (fun s r => s.insert r.name) {}

/-- Each theorem that states a correspondence. -/
def theoremSet : Std.HashSet Name := i.proved.foldl (fun s q => s.insert q.theorem_) {}

/-- The first constant that mentions a constant that the input does not hold, with what it mentions. -/
def openMention? : Option (Name × Name) :=
  let names := i.nameSet
  i.decls.findSome? fun d => (d.uses.find? (!names.contains ·)).map (d.name, ·)

/-- The first module of a target with no record, with its target. -/
def unrecorded? : Option (Name × Name) :=
  let recorded := i.recordSet
  i.targets.findSome? fun t => (t.modules.find? (!recorded.contains ·)).map (t.name, ·)

/-- The first constant without the axiom set that a rule reads: one of a claimed module, or a
theorem that states a correspondence. The rules of RG1002 to RG1005 and RG3002 read these sets, so
a set that the loader did not compute is a failure, never an empty set. -/
def axiomsMissing? : Option Name :=
  let claims := i.claimTable
  let theorems := i.theoremSet
  (i.decls.find? fun d =>
    d.axioms.isNone && (!(claims.getD d.module []).isEmpty || theorems.contains d.name)).map (·.name)

/-- Why the input does not have the closed form (`Input.WellFormed` of the specification), or
`none`: each name is the name of one constant, each mentioned constant is a constant of the
input, each module that Lake lists for a target has a module record, and each constant that a rule
reads the axioms of has its set. -/
def refusal? : Option String :=
  match duplicate? {} (i.decls.map (·.name)) with
  | some n => some s!"the constant {n} occurs twice in one environment"
  | none =>
    match i.openMention? with
    | some (n, u) => some s!"the constant {n} mentions {u}, which the environment does not hold"
    | none =>
      match i.unrecorded? with
      | some (t, m) => some s!"the module {m} of target {t} has no record of its .olean files"
      | none =>
        match i.axiomsMissing? with
        | some n => some s!"the loader computed no axiom set of {n}"
        | none => none

end Input

namespace Bundle

/-- Each module that an environment of the bundle loads. -/
def loadedSet (b : Bundle) : Std.HashSet Name :=
  b.envs.foldl (fun s i => i.loads.foldl (·.insert ·) s) {}

/-- The first module of a target of `first` that no environment loads, with its target. -/
def unloaded? (b : Bundle) (first : Input) : Option (Name × Name) :=
  let loaded := b.loadedSet
  first.targets.findSome? fun t => (t.modules.find? (!loaded.contains ·)).map (t.name, ·)

/-- Whether each environment has the targets, the claim and the module records of `first`. -/
def oneProject (b : Bundle) (first : Input) : Bool :=
  b.envs.all fun i => i.targets == first.targets && i.manifest == first.manifest &&
    i.modules == first.modules

/-- Whether the claim of an environment claims a target. -/
def claimsSome (b : Bundle) : Bool :=
  b.envs.any fun i => i.manifest.any fun e => i.claimedTarget e.target

/-- Why the bundle does not have the closed form (`Bundle.WellFormed` of the specification), or
`none`: at least one environment, each well-formed, one project in all of them, each module of
each target loaded in one of them, and a claim of at least one target. -/
def refusal? (b : Bundle) : Option String :=
  match b.envs with
  | [] => some "the shell loaded no environment"
  | first :: _ =>
    match b.envs.findSome? (·.refusal?) with
    | some why => some why
    | none =>
      if !b.oneProject first then
        some "the environments of one run do not carry one project"
      else
        match b.unloaded? first with
        | some (t, m) => some s!"the module {m} of target {t} is loaded in no environment"
        | none =>
          if b.claimsSome then none
          else some "the claim claims no target, so nothing is checked"

end Bundle

end Regula.Closed
