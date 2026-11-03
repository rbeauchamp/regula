module

public import Lean.Environment
public import Regula.Input
public import Regula.Rule
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Util.Path
import Lean.Compiler.Old

/-!
# The loader of the closed input

What reads a loaded environment into the closed input (`Regula.Closed.Input`), and refuses, as an error that
makes the run `incomplete` (RG2001), what it cannot read. It performs no effect: `Regula.Shell` asks Lean
for the environment and the places, and `Regula.Workspace` holds the calls of Lake. `Facts.input` is a pure
function of the environment, and `specification/RegulaSpecification/Proofs/Load.lean` states what it gives
in terms of the environment. What that leaves assumed about Lean and Lake is in the specification's trusted
base.

What it reads, and through what:
- The constants: each constant of an environment that `Lean.importModules` loads with `loadExts := false`,
  so no extension state is built and no initializer of a loaded module runs, and at the level `.private`, so a
  `module` file gives each constant with its body, exposed or not (`Lean/Environment.lean:1871` and `:2183` at
  v4.35.0). `getImplementedBy?` and `isExtern` read the module entries of an extension (`getModuleEntries`),
  which `importModules` sets whatever `loadExts` is, and no extension's built state. `Facts.unreplaced`
  also reads each claimed module's own entries, so merging names cannot hide an attribute.
- Each loaded module's own constants: `header.moduleData`, which Lean keeps as each `.olean` holds them, so
  that a constant that Lean's import replaced is read too. What any of them mentions, and whether it is an
  axiom, counts for its name (`Facts.stated`), in a dependency as in a claimed module. A claimed module's own
  constant must also fit the rules itself (`Facts.unread?`).
- The place of each module: where `Lean.findOLean` finds its `.olean` on Lake's search path. A claimed
  module lies below the root package's library directory; a constant of the toolchain is one whose module lies
  below the toolchain's library directory.
-/

public section

namespace Regula.Load

open Lean (ConstantInfo Environment Name TheoremVal findOLean isExtern)
open System (FilePath)
open Regula.Closed

/-- The components of a path, as Lean normalizes and splits it, with each empty one and each `.` removed. A `..` stays. So two
spellings of one path by text have one list, and two paths that one link joins have two. -/
abbrev parts (p : FilePath) : List String :=
  p.normalize.components.filter fun c => c != "" && c != "."

/-- Whether `path` lies below the directory `dir`, by their components. -/
def below (dir path : FilePath) : Bool :=
  (parts dir).isPrefixOf (parts path) && parts dir != parts path

/-- The name a file's parser input carries, a function of its components alone, so that two spellings of one path give Lean's parser
one input. It labels messages and selects nothing: the checker reads no message's text, and `Lean.Syntax` holds positions and no name. -/
abbrev inputName (p : FilePath) : String :=
  "/".intercalate (parts p)

/-- Whether `real`, which is the real path of `path`, is `path` itself at or below the directory `dir`, by
their components. So `path` crosses no link and holds no `..`. -/
def exactBelow (dir path real : FilePath) : Bool :=
  parts real == parts path && (parts dir).isPrefixOf (parts path)

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

/-- The constants a constant mentions: what Lean's kernel checks it against when Lean replays it. That is the type of each
constant, the value of a definition, theorem or opaque constant, the constructors and the other types of an inductive type's
block, the inductive type of a constructor, the types of a recursor's block, and `Eq` for a quotient. Lean's replay follows
`ConstantInfo.getUsedConstantsAsSet` (`Lean/Util/FoldConsts.lean:67-74`), reads each type of a block and its constructors
(`Lean/Replay.lean:105-111`), and adds `Eq` before a quotient, whose check reads it (`Lean/Replay.lean:129-133`,
`src/kernel/quot.cpp:19-50`), at v4.35.0. -/
def usesOf (info : ConstantInfo) : Array Name :=
  dedup <| match info with
    | .axiomInfo v => v.type.getUsedConstants
    | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
    | .quotInfo v => v.type.getUsedConstants.push `Eq
    | .ctorInfo v => v.type.getUsedConstants.push v.induct
    | .recInfo v => v.type.getUsedConstants ++ v.all.toArray
    | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray ++ v.all.toArray

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
  | .axiomInfo _ | .quotInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => #[]

/-- The safety of a constant, from Lean's two flags. Lean sets at most one of them on a constant
(`ConstantInfo.isUnsafe` and `ConstantInfo.isPartial`). -/
def safetyOf (info : ConstantInfo) : Safety :=
  if info.isUnsafe then .unsafe else if info.isPartial then .partial else .safe

/-- One module that an environment loaded, with where its `.olean` lies and what that place
decides. -/
structure LoadedModule where
  /-- The module. -/
  name : Name
  /-- Where its `.olean` lies. -/
  olean : FilePath
  /-- Whether it lies in the toolchain's library. -/
  inToolchain : Bool
  /-- Whether it lies in the root package's library: the module is claimed. -/
  claimed : Bool

/-- A module at the place `olean`, with what that place decides under the two library directories.
-/
def LoadedModule.ofPlace (toolchainDir rootDir : FilePath) (name : Name) (olean : FilePath) :
    LoadedModule :=
  { name, olean, inToolchain := below toolchainDir olean, claimed := below rootDir olean }

theorem LoadedModule.ofPlace_name (toolchainDir rootDir : FilePath) (name : Name) (olean : FilePath) :
    (LoadedModule.ofPlace toolchainDir rootDir name olean).name = name := by
  simp [LoadedModule.ofPlace]

theorem LoadedModule.ofPlace_self (toolchainDir rootDir : FilePath) (name : Name) (olean : FilePath) :
    LoadedModule.ofPlace toolchainDir rootDir name olean =
      LoadedModule.ofPlace toolchainDir rootDir
        (LoadedModule.ofPlace toolchainDir rootDir name olean).name
        (LoadedModule.ofPlace toolchainDir rootDir name olean).olean := by
  simp [LoadedModule.ofPlace]

/-- What the loader knows of one loaded environment. -/
structure Facts where
  /-- The loaded environment. -/
  env : Environment
  /-- The toolchain's library directory. -/
  toolchainDir : FilePath
  /-- The root package's library directory. -/
  rootDir : FilePath
  /-- Each module of the environment, by its index. -/
  modules : Array LoadedModule
  /-- These are the modules of the environment's header, in its order. -/
  names : modules.toList.map (·.name) = env.header.moduleNames.toList
  /-- What each module's place decides is what its fields say. -/
  placed : ∀ m ∈ modules, m = LoadedModule.ofPlace toolchainDir rootDir m.name m.olean

/-- The modules that are claimed. -/
def Facts.claimed (f : Facts) : List Name :=
  (f.modules.toList.filter (·.claimed)).map (·.name)

/-- The loaded module whose `.olean` holds constant `n`. -/
def Facts.info? (f : Facts) (n : Name) : Option LoadedModule :=
  (f.env.getModuleIdxFor? n).bind fun idx => f.modules[idx.toNat]?

/-- The name of the module whose `.olean` holds constant `n`. -/
def Facts.moduleOf? (f : Facts) (n : Name) : Option Name :=
  (f.info? n).map (·.name)

/-- Each constant of each name, as the own data of each loaded module states it, claimed or not.
Lean's import keeps one constant of a name (`Facts.shown`), so this is what the others say. -/
def Facts.stated (f : Facts) : Std.HashMap Name (List ConstantInfo) :=
  f.env.header.moduleData.foldl (init := {}) fun acc data =>
    (data.constNames.zip data.constants).foldl (init := acc) fun acc x =>
      acc.insert x.1 (x.2 :: acc.getD x.1 [])

/-- The constant `n` of the module `m`, as the closed input states it: `info` is the constant that
the environment keeps, and `stated` those of its name that the loaded modules state. -/
def Facts.declIn (f : Facts) (n : Name) (m : LoadedModule) (info : ConstantInfo)
    (stated : List ConstantInfo) : Decl where
  name := n
  module := m.name
  kind := kindIn info stated
  safety := safetyOf info
  uses := (usesIn info stated).toList
  valueUses := (valueUsesOf info).toList
  implementedBy := Lean.Compiler.getImplementedBy? f.env n
  isExtern := isExtern f.env n
  inToolchain := m.inToolchain

/-- The constant `n` as the closed input states it, or the refusal of a constant that no loaded
module holds. -/
def Facts.decl (f : Facts) (n : Name) (info : ConstantInfo) (stated : List ConstantInfo) :
    Except String Decl :=
  match f.info? n with
  | some m => .ok (f.declIn n m info stated)
  | none => .error s!"the constant {n} was loaded, and Lean gives it no module"

theorem mapM_ok {α β ε : Type} (g : α → Except ε β) (name : β → Name) (key : α → Name)
    (hname : ∀ a b, g a = .ok b → name b = key a) (l : List α) (r : List β)
    (h : l.mapM g = .ok r) :
    (∀ b ∈ r, ∃ a ∈ l, g a = .ok b) ∧ (∀ a ∈ l, ∃ b ∈ r, g a = .ok b) ∧
      r.map name = l.map key := by
  induction l generalizing r with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp
  | cons a l ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hg : g a with
    | error e =>
      rw [hg] at h
      cases h
    | ok b =>
      rw [hg] at h
      simp only at h
      cases hl : l.mapM g with
      | error e =>
        rw [hl] at h
        cases h
      | ok r' =>
        rw [hl] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨h1, h2, h3⟩ := ih r' hl
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact ⟨a, List.mem_cons_self .., hg⟩
          · obtain ⟨x, hx, hxy⟩ := h1 y hy
            exact ⟨x, List.mem_cons_of_mem _ hx, hxy⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨b, List.mem_cons_self .., hg⟩
          · obtain ⟨y, hy, hxy⟩ := h2 x hx
            exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩
        · simp [hname a b hg, h3]

theorem Facts.decl_name (f : Facts) {n : Name} {info : ConstantInfo} {stated : List ConstantInfo}
    {d : Decl} (h : f.decl n info stated = .ok d) : d.name = n := by
  simp only [Facts.decl] at h
  split at h
  · cases h
    rfl
  · cases h

theorem Facts.decls_nodup (f : Facts) {stated : Name → List ConstantInfo} {decls : List Decl}
    (h : f.env.constants.map₁.toList.mapM (fun x => f.decl x.1 x.2 (stated x.1)) = .ok decls) :
    (decls.map (·.name)).Nodup := by
  rw [(mapM_ok _ (·.name) (·.1) (fun _ _ hb => f.decl_name hb) _ _ h).2.2]
  refine List.pairwise_map.mpr (Std.HashMap.distinct_keys_toList.imp ?_)
  intro a b hab heq
  simp [heq] at hab

/-- What the rules read of a constant: its kind, its safety and what it mentions. -/
def readOf (info : ConstantInfo) : Kind × Safety × List Name × List Name :=
  (kindOf info, safetyOf info, (usesOf info).toList, (valueUsesOf info).toList)

/-- Each constant of each claimed module, with its module, as that module's `.olean` states it. -/
def Facts.claimedConstants (f : Facts) : List (Name × Name × ConstantInfo) :=
  ((f.modules.zip f.env.header.moduleData).toList.filter (·.1.claimed)).flatMap fun (m, data) =>
    (data.constNames.zip data.constants).toList.map fun (n, info) => (m.name, n, info)

/-- Whether the module's own entries give `n` neither replacement attribute. A missing module
index is not an empty set of attributes. Lean's name-based queries select only one module when
theorem names merge (`Lean/Attributes.lean:306-318` at v4.35.0). -/
def Facts.unreplaced (f : Facts) (m n : Name) : Bool :=
  match f.env.getModuleIdx? m with
  | none => false
  | some idx =>
    (Lean.Compiler.implementedByAttr.ext.getModuleEntries f.env idx).all (·.1 != n) &&
      (Lean.externAttr.ext.getModuleEntries f.env idx).all (·.1 != n)

/-- Whether the environment shows a constant of a claimed module to the rules: it holds a constant
of that name of which the rules read the same, in a claimed module. Lean's import merges two
theorems of one name and type, and a theorem with an axiom of that name and type: it keeps one, and
gives the name the first module that holds it (`subsumesInfo` and `finalizeImport`,
`Lean/Environment.lean:2269` and `2336-2345`). So a module's own constant can be one that no rule
reads as a subject. What a dropped constant mentions, and whether it is an axiom, the input still
states of its name (`Facts.stated`), in every loaded module; this check decides whether the rules
read a claimed module's own constant as a subject. Its own replacement attributes must be absent
or the represented constant must already carry a replacement that RG1011 refuses. -/
def Facts.shown (f : Facts) (x : Name × Name × ConstantInfo) : Bool :=
  match f.env.constants.map₁[x.2.1]?, f.info? x.2.1 with
  | some kept, some m => decide (readOf kept = readOf x.2.2) && m.claimed &&
      (f.unreplaced x.1 x.2.1 || (Lean.Compiler.getImplementedBy? f.env x.2.1).isSome ||
        isExtern f.env x.2.1)
  | none, _ | some _, none => false

/-- Whether a constant `n` that the environment does not show is what the rules would admit: a
theorem, safe, with neither replacement attribute in its own module and no name that the compiler
reads as a recursion helper's, whose value mentions no
loop construct, and each constant it mentions is held and reaches only axioms that the profile
admits. Lean regenerates a definition's equation lemmas in each module that needs them, so such a
constant can be conforming. -/
def fitsUnshown (f : Facts) {i : Input} (t : Tables i) (m n : Name) (info : ConstantInfo) : Bool :=
  f.unreplaced m n && (kindOf info == .theorem && safetyOf info == .safe &&
    (Lean.Compiler.isUnsafeRecName? n).isNone &&
    loopConstructs.all (!(valueUsesOf info).contains ·) &&
    (usesOf info).all fun u => t.index.contains u && (t.axiomSet u).all (t.admits i.profile ·))

/-- The first constant of a claimed module that the environment does not show and that
`fitsUnshown` does not admit, with its module. -/
def Facts.unread? (f : Facts) (i : Input) : Option (Name × Name) :=
  match f.claimedConstants.filter (!f.shown ·) with
  | [] => none
  | unshown =>
    let t := i.tables
    (unshown.find? fun x => !fitsUnshown f t x.1 x.2.1 x.2.2).map fun x => (x.1, x.2.1)

/-- The closed input of the environment that `f` describes, under the profile `profile`. It refuses
a module of `roots`, the default targets, that `f` does not claim, a constant with no module, a
reading that the admission refuses (`Draft.admit`), and a constant that `Facts.unread?` gives. -/
def Facts.input (f : Facts) (roots : List Name) (profile : Profile) : Except String Input :=
  let claimed := f.claimed
  match roots.find? (!claimed.contains ·) with
  | some m => .error s!"the module {m} of a default target has its .olean outside the root \
      package's build"
  | none =>
    let stated := f.stated
    match h : f.env.constants.map₁.toList.mapM (fun x => f.decl x.1 x.2 (stated.getD x.1 [])) with
    | .error why => .error why
    | .ok decls =>
      let draft : Draft :=
        { profile, modules := claimed, decls,
          unique := f.decls_nodup (stated := (stated.getD · [])) h }
      match draft.admit with
      | .error why => .error why
      | .ok i =>
        match f.unread? i with
        | some (m, n) => .error s!"the module {m} holds the constant {n}, which the merged environment \
            does not show to the rules, and this one is no theorem within the profile or \
            has a recursion helper's name or unread or forbidden compiled-code attributes"
        | none => .ok i

/-- Whether Lean's replay is given a constant of the cone: each constant but the companions of `Quot`, `Quot.mk`,
`Quot.lift` and `Quot.ind`, which the kernel adds with `Quot` and refuses to add again as names already taken
(`src/kernel/quot.cpp:50-56`). `leanchecker` leaves them out of its replay for that reason (`src/LeanChecker.lean:68-71`). -/
def replays : ConstantInfo → Bool
  | .quotInfo v =>
    match v.kind with
    | .type => true
    | _ => false
  | _ => true

/-- `m` with the constant `n` of `constants` when Lean's replay is given it (`replays`). -/
def replayStep (constants m : Std.HashMap Name ConstantInfo) (n : Name) : Std.HashMap Name ConstantInfo :=
  match constants[n]? with
  | some info => if replays info then m.insert n info else m
  | none => m

/-- The number of components of a name. -/
def depth : Name → Nat
  | .anonymous => 0
  | .str p _ => depth p + 1
  | .num p _ => depth p + 1

/-- A name of `d` components, each `0`. -/
def zeros : Nat → Name
  | 0 => .anonymous
  | d + 1 => .num (zeros d) 0

/-- A name deeper than each name of `constants`, so that no constant of theirs has a name that starts with it. -/
def copyRoot (constants : Std.HashMap Name ConstantInfo) : Name :=
  zeros (constants.keys.foldl (fun d n => max d (depth n)) 0 + 1)

/-- Each theorem of a claimed module, as that module's `.olean` states it, that is not the constant of its name that the
environment keeps. Lean's import keeps one of the theorems of a name and type that its modules state (`subsumesInfo` and
`finalizeImport`, `Lean/Environment.lean:2269-2275` and `2336-2345` at v4.35.0), so the kernel can check the others only as
copies. A theorem counts as kept when `==` (`Expr.eqv` on each expression, `Lean/Expr.lean:804-812`) relates the two. -/
def Facts.copies (f : Facts) : List TheoremVal :=
  f.claimedConstants.filterMap fun (_, n, info) =>
    match info with
    | .thmInfo v => if f.env.constants.map₁[n]? == some info then none else some v
    | _ => none

/-- The `k`-th copy under the name `root.k`, which no constant of the environment has (`copyRoot`). -/
def copyAt (root : Name) (x : TheoremVal × Nat) : Name × ConstantInfo :=
  (.num root x.2, .thmInfo { x.1 with name := .num root x.2, all := [.num root x.2] })

/-- Where the cone of the claim starts beyond the constants of claimed modules that the environment keeps: each name that a
claimed module's own data states, and `kernelNames`. -/
def Facts.coneSeeds (f : Facts) : List Name :=
  f.claimedConstants.map (·.2.1) ++ Input.kernelNames

/-- What Lean's replay is given of the cone of `i`'s claim (`Regula.Closed.Input.cone`): each constant of the cone that
`replays` admits, as the environment keeps it, and each of `copies` under a name of its own. -/
def Facts.replayConstants (f : Facts) (i : Input) : Std.HashMap Name ConstantInfo :=
  ((f.copies.zipIdx.map (copyAt (copyRoot f.env.constants.map₁))).foldl (fun m x => m.insert x.1 x.2)
    ((i.cone f.coneSeeds).toList.foldl (replayStep f.env.constants.map₁) {}))

/-- Whether `loaded`, the search path of the workspace that a load of the current directory gave, starts the search path that this program
received. Lake gives a program the libraries of its workspace, then its own, then what it inherited (`Workspace.augmentedLeanPath`,
`Lake/Config/Workspace.lean:391-392`). So a `lake -d` of an ordinary project from another workspace gives another start. That is all this says: a project sets
those directories (`leanLibDir`, `buildDir`), so another project can give the same start, and the same start names no workspace. A path that holds the search path's
separator is cut in `received`, and the test then fails. -/
def startsSearchPath (loaded received : List String) : Bool :=
  loaded.isPrefixOf received

end Regula.Load
