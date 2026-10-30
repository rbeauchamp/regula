import Lean.Data.NameMap

/-!
# The closed input

The one input every rule of the checker reads: the constants Lean loads from the finished build,
Lake's own list of the targets and the modules it builds, and the project's claim
(`foundation_manifest.json`). It carries no source text, message, info tree, option set in source,
build log or file listing, so a rule cannot decide anything that is not here.

The types follow the specification of the smaller Regula
(`specification/RegulaSpecification/Input.lean`, `Gate.lean`): `Decl`, `ModuleRecord`, `Target`,
`Entry`, `Contract`, `Input` and `Bundle` have the specification's fields, and `Bundle.refusal?` decides the specification's admission
(`Bundle.WellFormed`, `Input.WellFormed`). That the shell (`Regula.Load`) fills each field through
the interface its docstring names is the loader's obligation; that each rule function of
`Regula.Rules` decides the specification's violation predicate is #487's obligation, not a theorem
of this module.

Two choices are the implementation's, made on the owner's behalf:

- `decls` holds the constants of the environment that the rules can reach: every constant of a
  claimed module, the `main` of each executable root, the theorems that state a correspondence, and
  everything these mention or run. Each rule of the specification quantifies only over such
  constants, so the rules decide the same on this list as on every constant of the environment,
  while the list stays small for an environment that imports `Lean`.
- A `Target`'s options keep Lake's own values as text (`Target.options`), as the specification
  states them.
-/

namespace Regula.Closed

open Lean (Name NameMap NameSet)

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

/-- One point at which compiled code departs from a kernel value: where the kernel value has the
constant `reference`, compiled code runs `runs`. -/
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
  /-- Each point at which its compiled code departs from its kernel value. -/
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
def index : NameMap Decl :=
  i.decls.foldl (fun m d => m.insert d.name d) {}

/-- The classification the claim gives the target `t`, when exactly one entry names it. -/
def classificationOf (t : Name) : Option Classification :=
  match i.manifest.filter (·.target == t) with
  | [e] => some e.classification
  | _ => none

/-- The profile and execution mode of each claim of a target that contains module `m`. -/
def claimsOf (m : Name) : List (Profile × Execution) :=
  i.targets.foldl (init := []) fun acc t =>
    if t.modules.contains m then
      acc ++ (i.manifest.filterMap fun e =>
        if e.target == t.name then
          match e.classification with
          | .claimed p x => some (p, x)
          | .excluded => none
        else none)
    else acc

/-- The profile and execution mode of each claim of each module, as `claimsOf` gives them, computed
once for all modules. -/
def claimTable : NameMap (List (Profile × Execution)) :=
  i.targets.foldl (init := {}) fun table t =>
    let claims := i.manifest.filterMap fun e =>
      if e.target == t.name then
        match e.classification with
        | .claimed p x => some (p, x)
        | .excluded => none
      else none
    t.modules.foldl (fun table m => table.insert m ((table.find? m).getD [] ++ claims)) table

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

/-- Why the input does not have the closed form (`Input.WellFormed` of the specification), or
`none`: each name is the name of one constant, each mentioned constant is a constant of the
input, and each module that Lake lists for a target has a module record. -/
def refusal? : Option String := Id.run do
  let mut seen : NameSet := {}
  for d in i.decls do
    if seen.contains d.name then
      return some s!"the constant {d.name} occurs twice in one environment"
    seen := seen.insert d.name
  for d in i.decls do
    for u in d.uses do
      unless seen.contains u do
        return some s!"the constant {d.name} mentions {u}, which the environment does not hold"
  let recorded : NameSet := i.modules.foldl (fun s r => s.insert r.name) {}
  for t in i.targets do
    for m in t.modules do
      unless recorded.contains m do
        return some s!"the module {m} of target {t.name} has no record of its .olean files"
  return none

end Input

namespace Bundle

/-- Why the bundle does not have the closed form (`Bundle.WellFormed` of the specification), or
`none`: at least one environment, each well-formed, one project in all of them, each module of
each target loaded in one of them, and a claim of at least one target. -/
def refusal? (b : Bundle) : Option String := Id.run do
  let some first := b.envs.head? | return some "the shell loaded no environment"
  for i in b.envs do
    if let some why := i.refusal? then return some why
    unless i.targets == first.targets && i.manifest == first.manifest &&
        i.modules == first.modules do
      return some "the environments of one run do not carry one project"
  let loaded : NameSet := b.envs.foldl (fun s i => i.loads.foldl (·.insert ·) s) {}
  for t in first.targets do
    for m in t.modules do
      unless loaded.contains m do
        return some s!"the module {m} of target {t.name} is loaded in no environment"
  unless first.manifest.any (fun e => first.claimedTarget e.target) do
    return some "the claim claims no target, so nothing is checked"
  return none

end Bundle

end Regula.Closed
