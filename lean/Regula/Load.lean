module

public import Lean.Environment
public import Regula.Input
public import Regula.Rules
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Util.Path
import Lean.Compiler.Old

/-!
# The loader of the closed input

What reads a loaded environment into the closed input (`Regula.Closed.Input`), and refuses, as an
error that makes the run `incomplete` (RG2001), what it cannot read. `Regula.Workspace` holds the
part that calls Lake and imports the environment. `Facts.input` is a pure function of the
environment, and `specification/RegulaSpecification/Proofs/Load.lean` states what it gives in terms
of the environment. What that leaves assumed about Lean and Lake is in the specification's trusted
base.

What it reads, and through what:

- The constants: each constant of an environment that `Lean.importModules` loads with `loadExts :=
  false`, so no extension state is built and no initializer of a loaded module runs, and at the
  level `.private`, so a `module` file gives each constant with its body, exposed or not
  (`Lean/Environment.lean:1871` and `:2183` at v4.35.0).
  `getImplementedBy?` and `isExtern` read the module entries of an extension (`getModuleEntries`),
  which `importModules` sets whatever `loadExts` is, and no extension's built state.
- Each loaded module's own constants: `header.moduleData`, which Lean keeps as each `.olean` holds
  them, so that a constant that Lean's import replaced is read too. What any of them mentions, and
  whether it is an axiom, counts for its name (`Facts.stated`), in a dependency as in a claimed
  module. A claimed module's own constant must also fit the rules itself (`Facts.unread?`).
- The place of each module: where `Lean.findOLean` finds its `.olean` on Lake's search path. A
  claimed module lies below the root package's library directory; a constant of the toolchain is one
  whose module lies below the toolchain's library directory.
-/

public section

namespace Regula.Load

open Lean System
open Regula.Closed

/-- Refuse the input: the run is `incomplete`. -/
def refuse {α : Type} (why : String) : IO α :=
  throw <| IO.userError why

/-- The components of a path, as Lean normalizes it. -/
def parts (p : FilePath) : List String :=
  p.normalize.components.filter (!·.isEmpty)

/-- Whether `path` lies below the directory `dir`, by their components. -/
def below (dir path : FilePath) : Bool :=
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

/-- The names of `all`, each once. -/
def dedup (all : Array Name) : Array Name :=
  all.foldl (fun acc n => if acc.contains n then acc else acc.push n) #[]

/-- The constants a constant mentions, the fields that `Lean.collectAxioms` walks: the type and
value of a definition, theorem or opaque constant, the type of an axiom, constructor or recursor,
the type and constructors of an inductive type, and nothing of a quotient
(`Lean/Util/CollectAxioms.lean`). -/
def usesOf (info : ConstantInfo) : Array Name :=
  dedup <| match info with
    | .axiomInfo v => v.type.getUsedConstants
    | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .quotInfo _ => #[]
    | .ctorInfo v => v.type.getUsedConstants
    | .recInfo v => v.type.getUsedConstants
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray

/-- What the input states a constant mentions: what the constant that the environment keeps mentions
and what each constant in `stated`, those of its name that the loaded modules state, mentions. -/
def usesIn (info : ConstantInfo) (stated : List ConstantInfo) : Array Name :=
  dedup (stated.foldl (fun acc v => acc ++ usesOf v) (usesOf info))

/-- The kind the input states of a constant: an axiom when a constant in `stated`, those of its name
that the loaded modules state, is one, and otherwise the kind of the constant the environment keeps.
-/
def kindIn (info : ConstantInfo) (stated : List ConstantInfo) : Kind :=
  if stated.any (kindOf · == .axiom) then .axiom else kindOf info

/-- The constants that the value of a definition, theorem or opaque constant mentions, and nothing
of any other constant. -/
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

/-- The facts of `env`, from where the `.olean` of each of its modules lies, in the order of its
header. -/
def Facts.ofPlaces (env : Environment) (toolchainDir rootDir : FilePath) (places : Array FilePath) :
    Facts where
  env
  inToolchain := places.map (below toolchainDir)
  claimed := ((env.header.moduleNames.zip places).toList.filter (below rootDir ·.2)).map (·.1)

/-- Where the `.olean` of each module of `env` lies, in the order of its header. -/
def places (env : Environment) : IO (Array FilePath) :=
  env.header.moduleNames.mapM fun m =>
    try findOLean m catch e => refuse s!"the module {m} was loaded and has no .olean on Lake's \
      search path: {e}"

/-- The module whose `.olean` holds constant `n`. -/
def Facts.moduleOf (f : Facts) (n : Name) : Option Name :=
  (f.env.getModuleIdxFor? n).bind fun idx => f.env.header.moduleNames[idx.toNat]?

/-- Whether constant `n` is a constant of the toolchain's library. -/
def Facts.toolchain (f : Facts) (n : Name) : Bool :=
  ((f.env.getModuleIdxFor? n).bind fun idx => f.inToolchain[idx.toNat]?).getD false

/-- Each constant of each name, as the own data of each loaded module states it, claimed or not.
Lean's import keeps one constant of a name (`Facts.shown`), so this is what the others say. -/
def Facts.stated (f : Facts) : Std.HashMap Name (List ConstantInfo) :=
  f.env.header.moduleData.foldl (init := {}) fun acc data =>
    (data.constNames.zip data.constants).foldl (init := acc) fun acc x =>
      acc.insert x.1 (x.2 :: acc.getD x.1 [])

/-- The constant `n` of the module `module`, as the closed input states it: `info` is the constant
that the environment keeps, and `stated` those of its name that the loaded modules state. -/
def Facts.declIn (f : Facts) (n module : Name) (info : ConstantInfo)
    (stated : List ConstantInfo) : Decl where
  name := n
  module
  kind := kindIn info stated
  isUnsafe := info.isUnsafe
  isPartial := info.isPartial
  uses := (usesIn info stated).toList
  valueUses := (valueUsesOf info).toList
  implementedBy := Compiler.getImplementedBy? f.env n
  isExtern := isExtern f.env n
  inToolchain := f.toolchain n

/-- The constant `n` as the closed input states it, or the refusal of a constant that no loaded
module holds. -/
def Facts.decl (f : Facts) (n : Name) (info : ConstantInfo) (stated : List ConstantInfo) :
    Except String Decl :=
  match f.moduleOf n with
  | some module => .ok (f.declIn n module info stated)
  | none => .error s!"the constant {n} was loaded, and Lean gives it no module"

/-- What the rules read of a constant: its kind, its two flags and what it mentions. -/
def readOf (info : ConstantInfo) : Kind × Bool × Bool × List Name × List Name :=
  (kindOf info, info.isUnsafe, info.isPartial, (usesOf info).toList, (valueUsesOf info).toList)

/-- Each constant of each claimed module, with its module, as that module's `.olean` states it. -/
def Facts.claimedConstants (f : Facts) : List (Name × Name × ConstantInfo) :=
  ((f.env.header.moduleNames.zip f.env.header.moduleData).toList.filter
    (f.claimed.contains ·.1)).flatMap fun (m, data) =>
      (data.constNames.zip data.constants).toList.map fun (n, info) => (m, n, info)

/-- Whether the environment shows a constant of a claimed module to the rules: it holds a constant
of that name of which the rules read the same, in a claimed module. Lean's import merges two
theorems of one name and type, and a theorem with an axiom of that name and type: it keeps one, and
gives the name the first module that holds it (`subsumesInfo` and `finalizeImport`,
`Lean/Environment.lean:2269` and `2336-2345`). So a module's own constant can be one that no rule
reads as a subject. What a dropped constant mentions, and whether it is an axiom, the input still
states of its name (`Facts.stated`), in every loaded module; this check decides whether the rules
read a claimed module's own constant as a subject. -/
def Facts.shown (f : Facts) (x : Name × Name × ConstantInfo) : Bool :=
  match f.env.constants.map₁[x.2.1]?, f.moduleOf x.2.1 with
  | some kept, some m => decide (readOf kept = readOf x.2.2) && f.claimed.contains m
  | _, _ => false

/-- Whether a constant `n` that the environment does not show is what the rules would admit: a
theorem, with neither flag and no name that the compiler reads as a recursion helper's, whose value
mentions no loop construct, and each constant it mentions is held and reaches only axioms that the
profile admits. Lean regenerates a definition's equation lemmas in each module that needs them, so
such a constant can be conforming. -/
def fitsUnshown (t : Tables) (n : Name) (info : ConstantInfo) : Bool :=
  kindOf info == .theorem && !info.isUnsafe && !info.isPartial &&
    (Compiler.isUnsafeRecName? n).isNone &&
    loopConstructs.all (!(valueUsesOf info).contains ·) &&
    (usesOf info).all fun u => t.index.contains u && (t.axiomSet u).all (t.admits t.profile ·)

/-- The first constant of a claimed module that the environment does not show and that
`fitsUnshown` does not admit, with its module. -/
def Facts.unread? (f : Facts) (i : Input) : Option (Name × Name) :=
  match f.claimedConstants.filter (!f.shown ·) with
  | [] => none
  | unshown =>
    let t := i.tables
    (unshown.find? fun x => !fitsUnshown t x.2.1 x.2.2).map fun x => (x.1, x.2.1)

/-- The closed input of the environment that `f` describes, under the profile `profile`. It refuses
a module of `roots`, the default targets, that `f` does not claim, and a constant that
`Facts.unread?` gives. -/
def Facts.input (f : Facts) (roots : List Name) (profile : Profile) : Except String Input :=
  match roots.find? (!f.claimed.contains ·) with
  | some m => .error s!"the module {m} of a default target has its .olean outside the root \
      package's build"
  | none =>
    let stated := f.stated
    (f.env.constants.map₁.toList.mapM fun (n, info) =>
      f.decl n info (stated.getD n [])).bind fun decls =>
      let i : Input :=
        { profile, modules := f.claimed, decls, loads := f.env.header.moduleNames.toList }
      match f.unread? i with
      | some (m, n) => .error s!"the module {m} holds the constant {n}, which Lean's import \
          replaced with another of that name, and this one is no theorem within the profile or \
          has a recursion helper's name"
      | none => .ok i

/-- Whether `root` is the last workspace library directory before Lake's library in the received
search path. Lake v4.35.0 `Package.lint` runs the driver without changing its directory
(`Lake/CLI/Actions.lean`), and `Workspace.augmentedLeanPath` supplies workspace libraries, then the
collocated Lake library, then inherited entries. The root package is first in Lake's package array,
so `Workspace.leanPath` puts its library last.

Assumes: Lake supplies that composition; its library is not a workspace library; and distinct
packages do not configure a shared library directory. Under those assumptions the theorem below
identifies the dispatching root, whatever search path the caller inherited. -/
def dispatchedFrom (root lakeLib : String) (leanPath : List String) : Bool :=
  decide ((leanPath.takeWhile (· ≠ lakeLib)).getLast? = some root) &&
    decide (lakeLib ∈ leanPath)

/-- For every search path of Lake's composition, the dispatch check accepts exactly the last
workspace library directory. Inherited entries cannot make a different root pass. -/
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
