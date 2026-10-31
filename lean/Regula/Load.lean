import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Util.CollectAxioms
import Lean.Util.Path
import Regula.Input

/-!
# The loader of the closed input

What reads a loaded environment into the closed input (`Regula.Closed.Input`), and refuses, as an error
that makes the run `incomplete` (RG2001), what it cannot read. `Regula.Workspace` holds the part that
calls Lake and imports the environment. No theorem yet states that this module fills the input
faithfully: the specification's trusted base lists that step.

What it reads, and through what:

- The constants: each constant of an environment that `Lean.importModules` loads with `loadExts := false`, so no
  extension state is built and no initializer of a loaded module runs. `getImplementedBy?` and
  `isExtern` read the module entries of an extension (`getModuleEntries`), which `importModules` sets
  whatever `loadExts` is, and no extension's built state.
- The axiom sets: `Lean.collectAxioms` of each constant of a claimed module (`axiomsIn`). Lean's recorded
  table of each module's axioms is an extension's state, which `loadExts := false` leaves empty, so the
  axioms come from the constants.
- The place of each module: where `Lean.findOLean` finds its `.olean` on Lake's search path. A claimed
  module lies below the root package's library directory; a constant of the toolchain is one whose module
  lies below the toolchain's library directory.
-/

namespace Regula.Load

open Lean System
open Regula.Closed

/-- Refuse the input: the run is `incomplete`. -/
def refuse {α : Type} (why : String) : IO α :=
  throw <| IO.userError why

/-- Whether `path` lies below the directory `dir`, by their components. -/
def below (dir path : FilePath) : Bool :=
  let parts (p : FilePath) := p.normalize.components.filter (!·.isEmpty)
  (parts dir).isPrefixOf (parts path) && parts dir != parts path

/-- The kind of a constant: its `ConstantInfo` constructor. -/
def kindOf : ConstantInfo → Kind
  | .axiomInfo _ => .axiom
  | .defnInfo _ => .definition
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | .quotInfo _ => .quotient
  | .inductInfo _ => .inductive
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor

/-- The constants a constant mentions, as `Lean.collectAxioms` walks them: the type and value of a
definition, theorem or opaque constant, the type of an axiom, constructor or recursor, the type and
constructors of an inductive type, and nothing of a quotient (`Lean/Util/CollectAxioms.lean`). -/
def usesOf (info : ConstantInfo) : Array Name :=
  let all := match info with
    | .axiomInfo v => v.type.getUsedConstants
    | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .quotInfo _ => #[]
    | .ctorInfo v => v.type.getUsedConstants
    | .recInfo v => v.type.getUsedConstants
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  all.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]

/-- The constants that the value of a definition, theorem or opaque constant mentions, and nothing of any
other constant. -/
def valueUsesOf : ConstantInfo → Array Name
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | _ => #[]

/-- What the loader knows of one loaded environment. -/
structure Facts where
  /-- The loaded environment. -/
  env : Environment
  /-- Whether each module, by its index, lies in the toolchain's library. -/
  inToolchain : Array Bool
  /-- The claimed modules: those that lie in the root package's library directory. -/
  claimed : List Name

/-- The facts of `env`: where each module's `.olean` lies. -/
def facts (env : Environment) (toolchainDir rootDir : FilePath) : IO Facts := do
  let mut inToolchain := #[]
  let mut claimed := []
  for m in env.header.moduleNames do
    let olean ← try findOLean m catch e => refuse s!"the module {m} was loaded and has no \
      .olean on Lake's search path: {e}"
    inToolchain := inToolchain.push (below toolchainDir olean)
    if below rootDir olean then claimed := m :: claimed
  return { env, inToolchain, claimed := claimed.reverse }

/-- The module whose `.olean` holds constant `n`. -/
def Facts.moduleOf (f : Facts) (n : Name) : Option Name :=
  (f.env.getModuleIdxFor? n).bind fun idx => f.env.header.moduleNames[idx.toNat]?

/-- Whether constant `n` is a constant of the toolchain's library. -/
def Facts.toolchain (f : Facts) (n : Name) : Bool :=
  ((f.env.getModuleIdxFor? n).bind fun idx => f.inToolchain[idx.toNat]?).getD false

/-- The constant `n` as the closed input states it, or the refusal of a constant that no loaded module
holds. -/
def Facts.decl (f : Facts) (n : Name) (info : ConstantInfo) : Except String Decl := do
  let some module := f.moduleOf n
    | throw s!"the constant {n} was loaded, and Lean gives it no module"
  return {
    name := n, module, kind := kindOf info
    isUnsafe := info.isUnsafe, isPartial := info.isPartial, uses := (usesOf info).toList
    valueUses := (valueUsesOf info).toList
    axioms := none
    implementedBy := Compiler.getImplementedBy? f.env n
    isExtern := isExtern f.env n
    inToolchain := f.toolchain n }

/-- The environment as the one state that `Lean.collectAxioms` reads. -/
local instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv f := modify f

/-- The transitive axiom set of constant `n` in `env`, as `Lean.collectAxioms` computes it, in the
order it returns. The loader imports the environment with `loadExts := false`, so the table of axioms
that Lean records for each module (`exportedAxiomsExt`) keeps its initial, empty state
(`Lean/Environment.lean:2404` and `2428-2433` at v4.35.0), and `collectAxioms` walks the type and value
of each constant that `n` reaches, as `usesOf` lists them (`Lean/Util/CollectAxioms.lean` at v4.35.0).
Each call starts from an empty cache, so its answer for `n` holds every axiom that `n` reaches. -/
def axiomsIn (env : Environment) (n : Name) : List Name :=
  ((collectAxioms n : StateM Environment (Array Name)).run' env).toList

/-- The axiom set of each constant of `names` in `env` (`axiomsIn`). The walks are independent, so they
run in tasks of Lean's task manager, a slice of `names` to each task. -/
def axiomTable (env : Environment) (names : Array Name) : NameMap (List Name) :=
  let slice := max 1 ((names.size + 63) / 64)
  let tasks := (List.range ((names.size + slice - 1) / slice)).map fun k =>
    Task.spawn fun _ => (names.extract (k * slice) ((k + 1) * slice)).map fun n =>
      (n, axiomsIn env n)
  tasks.foldl (fun table task => task.get.foldl (fun table (n, axs) => table.insert n axs) table)
    {}

/-- The closed input of the environment that `f` describes, under the profile `profile`: each constant of
the environment, with the axiom set of each constant of a claimed module. -/
def Facts.input (f : Facts) (profile : Profile) : Except String Input := do
  let claimed : NameSet := f.claimed.foldl (·.insert ·) {}
  let all ← f.env.constants.map₁.toList.mapM fun (n, info) => f.decl n info
  let names := all.filterMap fun d => if claimed.contains d.module then some d.name else none
  let table := axiomTable f.env names.toArray
  let decls := all.map fun d =>
    { d with axioms := if claimed.contains d.module then table.find? d.name else none }
  return { profile, modules := f.claimed, decls, loads := f.env.header.moduleNames.toList }

/-- Whether `root` is the last workspace library directory before Lake's library in the received search
path. Lake v4.35.0 `Package.lint` runs the driver without changing its directory
(`Lake/CLI/Actions.lean`), and `Workspace.augmentedLeanPath` supplies workspace libraries, then the
collocated Lake library, then inherited entries. The root package is first in Lake's package array, so
`Workspace.leanPath` puts its library last.

Assumes: Lake supplies that composition; its library is not a workspace library; and distinct packages
do not configure a shared library directory. Under those assumptions the theorem below identifies the
dispatching root, whatever search path the caller inherited. -/
def dispatchedFrom (root lakeLib : String) (leanPath : List String) : Bool :=
  decide ((leanPath.takeWhile (· ≠ lakeLib)).getLast? = some root) &&
    decide (lakeLib ∈ leanPath)

/-- For every search path of Lake's composition, the dispatch check accepts exactly the last workspace
library directory. Inherited entries cannot make a different root pass. -/
theorem dispatchedFrom_iff {root lakeLib : String} {dispatching inherited : List String}
    (h : lakeLib ∉ dispatching) :
    dispatchedFrom root lakeLib (dispatching ++ lakeLib :: inherited) = true ↔
      dispatching.getLast? = some root := by
  have hall : ∀ a ∈ dispatching, decide (a ≠ lakeLib) = true := by
    intro a ha
    simp only [ne_eq, decide_eq_true_eq]
    exact fun hal => h (hal ▸ ha)
  have htake : (dispatching ++ lakeLib :: inherited).takeWhile (fun a => decide (a ≠ lakeLib)) =
      dispatching := by
    rw [List.takeWhile_append_of_pos hall]
    simp
  simp only [dispatchedFrom, htake, Bool.and_eq_true, decide_eq_true_eq]
  simp

end Regula.Load
