module

public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The closed input

The one input every rule of the checker reads: the constants Lean loads from the finished build, the
modules that the build claims, and the profile that the project states. It carries no source text,
message, compiled code, option or build log, so a rule cannot decide anything that is not here.

The types follow `specification/RegulaSpecification/Input.lean`, and `Input.refusal?` decides that
module's admission (`Input.WellFormed`). `specification/RegulaSpecification/Proofs/` proves each
rule function of `Regula.Rules` against the specification's violation predicate, this admission
against its statement, and each field against the environment that `Regula.Load` reads it from.
That Lean's and Lake's interfaces report the build is what the specification's trusted base lists.
-/

public section

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

/-- One constant of a loaded environment, as Lean reports it from the build's `.olean` files. -/
structure Decl where
  /-- Its name. -/
  name : Name
  /-- The module whose `.olean` holds it (`Environment.getModuleIdxFor?`). -/
  module : Name
  /-- `axiom` when any loaded module's own data states an axiom of this name (Lean's import can drop
  it for a theorem), and otherwise the `ConstantInfo` constructor of the constant Lean keeps. -/
  kind : Kind
  /-- `ConstantInfo.isUnsafe`. -/
  isUnsafe : Bool
  /-- `ConstantInfo.isPartial`. -/
  isPartial : Bool
  /-- The constants that the type and value mention, the fields that `Lean.collectAxioms` walks, of
  the constant Lean keeps and of each constant of this name that a loaded module's own data states
  (Lean's import can drop those). -/
  uses : List Name
  /-- The constants its value mentions, for a definition, theorem or opaque constant, and nothing
  for any other constant. -/
  valueUses : List Name
  /-- The constant `@[implemented_by]` names, if any (`Lean.Compiler.getImplementedBy?`). -/
  implementedBy : Option Name
  /-- Whether it is `@[extern]` (`Lean.isExtern`). -/
  isExtern : Bool
  /-- Whether its module belongs to the Lean toolchain's own library. -/
  inToolchain : Bool
  deriving Repr, Inhabited

/-- The foundation profiles a project can state. -/
inductive Profile where
  /-- No axiom. -/
  | kernelOnly
  /-- `propext` and `Quot.sound` only. -/
  | choiceFree
  /-- `propext`, `Quot.sound` and `Classical.choice`. -/
  | standardLogical
  deriving DecidableEq, Repr, Inhabited

/-- The closed input of one run. -/
structure Input where
  /-- The profile that the project states. -/
  profile : Profile
  /-- The claimed modules: each module of a default target of the root package, and each module of
  the root package that their imports reach. -/
  modules : List Name
  /-- The constants of the environment. -/
  decls : List Decl
  /-- The modules the environment imports. -/
  loads : List Name
  deriving Inhabited

/-- The names of `l`, for lookups. -/
def setOf (l : List Name) : Std.HashSet Name := l.foldl (·.insert ·) {}

namespace Input

variable (i : Input)

/-- The constants of the input by name. -/
def index : Std.HashMap Name Decl :=
  i.decls.foldl (fun m d => m.insert d.name d) {}

/-- The first name of `names` that is in `seen` or that an earlier name of `names` repeats. -/
def duplicate? (seen : Std.HashSet Name) : List Name → Option Name
  | [] => none
  | n :: rest => if seen.contains n then some n else duplicate? (seen.insert n) rest

/-- The first constant that mentions a constant that the input does not hold, with what it
mentions. -/
def openMention? : Option (Name × Name) :=
  let names := setOf (i.decls.map (·.name))
  i.decls.findSome? fun d => (d.uses.find? (!names.contains ·)).map (d.name, ·)

/-- The first claimed module that the environment does not load. -/
def unloaded? : Option Name :=
  let loaded := setOf i.loads
  i.modules.find? (!loaded.contains ·)

/-- Why the input does not have the closed form (`Input.WellFormed` of the specification), or
`none`: each name is the name of one constant, each mentioned constant is a constant of the input,
at least one module is claimed, and each claimed module is loaded. -/
def refusal? : Option String :=
  match duplicate? {} (i.decls.map (·.name)) with
  | some n => some s!"the constant {n} occurs twice in one environment"
  | none =>
    match i.openMention? with
    | some (n, u) => some s!"the constant {n} mentions {u}, which the environment does not hold"
    | none =>
      if i.modules.isEmpty then some "the build claims no module, so nothing is checked"
      else
        match i.unloaded? with
        | some m => some s!"the claimed module {m} is not loaded"
        | none => none

end Input

end Regula.Closed
