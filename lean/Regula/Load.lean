module

public import Lean.Environment
public import Regula.Input
public import Regula.Rule
import Lean.Compiler.CSimpAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.InitAttr
import Lean.Util.Path
import Lean.Compiler.Old
import Lean.Compiler.LCNF.Util
import Lean.Meta.Constructions.CasesOn

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
  `module` file gives each constant with its body, exposed or not (`Lean/Environment.lean:2213` and `:2547` at
  v4.36.0). `getImplementedBy?`, `isExtern` and `getInitFnNameFor?` read the module entries of an extension
  (`getModuleEntries`), which `importModules` sets whatever `loadExts` is, and no extension's built state.
  `Facts.unreplaced`, `Facts.ctorIdxEntryOnly`, and `Facts.uninitialized` also read each claimed module's
  own entries, so a name that two modules state cannot hide an attribute, and `Facts.csimps` reads each
  claimed module's exported (`global` and `scoped`) `@[csimp]` entries through
  `Lean.Compiler.CSimp.ext.ext.getModuleEntries` (`Lean/Environment.lean:1990-1996`, `:2742` at v4.36.0),
  refusing a claimed module with no module index.
  `Facts.claimedCSimpTargets` checks claimed ownership of exported `@[csimp]` entries strictly against
  claimed modules' own `moduleData` (`Facts.claimedConstants`), skipping all declaration work when no
  claimed module registers an entry and building only a set of the entry target names when entries are
  present (leaving `Facts.stated` unchanged and reading no dependency module's constants;
  `Facts.claimedConstants` steps once over the loaded modules, dependencies included, to select the
  claimed ones). `const2ModIdx` cannot decide
  ownership in either direction because `finalizeImport` keeps the first module on merged theorems and
  also inserts IR `extraConstNames` (`Lean/Environment.lean:2709-2712` at v4.36.0).
- Each loaded module's own constants: `header.moduleData`, which Lean keeps as each `.olean` holds them, so
  that a constant that Lean's import replaced is read too. What any of them mentions, and whether it is an
  axiom, counts for its name (`Facts.stated`), in a dependency as in a claimed module. A claimed module's own
  constant must also fit the rules itself (`Facts.unread?`).
- Whether each loaded module is a `module` file: the flag `isModule` of its data in `header.moduleData`, which Lean
  writes from the header of the environment that elaborated the file (`mkModuleData` and `writeModule`,
  `Lean/Environment.lean:2224-2227` and `2243-2259` at v4.36.0).
- The place of each module: where `Lean.findOLean` finds its `.olean` on Lake's search path. A claimed
  module lies below the root package's library directory; a constant of the toolchain is one whose module lies
  below the toolchain's library directory.
-/

public section

namespace Regula.Load

open Lean (ConstantInfo DefinitionVal Environment Expr FVarId InductiveVal Level LocalContext Name
  TheoremVal findOLean isExtern)
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

/-- One step of `dedup`: record `n` in `seen` and `out` when `seen` does not yet hold it. -/
def dedupStep (acc : Std.HashSet Name × Array Name) (n : Name) : Std.HashSet Name × Array Name :=
  let (seen, out) := acc
  if seen.contains n then (seen, out) else (seen.insert n, out.push n)

/-- The names of `all`, each once, in the order of their first occurrence. -/
def dedup (all : Array Name) : Array Name :=
  (all.foldl dedupStep ({}, #[])).2

/-- The constants a constant mentions: what Lean's kernel checks it against when Lean replays it. That is the type of each
constant, the value of a definition, theorem or opaque constant, the constructors and the other types of an inductive type's
block, the inductive type of a constructor, the types of a recursor's block, and `Eq` for a quotient. Lean's replay follows
`ConstantInfo.getUsedConstantsAsSet` (`Lean/Util/FoldConsts.lean:67-74`), reads each type of a block and its constructors
(`Lean/Replay.lean:105-111`), and adds `Eq` before a quotient, whose check reads it (`Lean/Replay.lean:129-133`,
`src/kernel/quot.cpp:19-50`), at v4.36.0. -/
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

/-- Strips `k` leading forall binders from `e`, returning the remaining body when all `k` exist. -/
def stripForalls : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ _ b _ => stripForalls k b
  | _ + 1, _ => none

/-- Reduces `e` with `Lean.Kernel.whnf` (`Lean/Environment.lean:3175-3176` at v4.36.0) as needed to
strip `n` leading forall binders (tracking outer binders in `lctx` and `fvars`) and reach the
resulting `.sort u`, returning each binder domain head-beta-reduced and abstracted back to bound
variables (`Lean/MetavarContext.lean:1358` at v4.36.0) together with `u`. -/
def stripIndTypeGo (env : Environment) :
    Nat → LocalContext → Array Expr → Expr → Option (List Expr × Level)
  | 0, lctx, _, e =>
    match e with
    | .sort u => some ([], u)
    | _ =>
      match Lean.Kernel.whnf env lctx e with
      | .ok (.sort u) => some ([], u)
      | _ => none
  | k + 1, lctx, fvars, e =>
    match (match e with
      | .forallE _ _ _ _ => some e
      | _ =>
        match Lean.Kernel.whnf env lctx e with
        | .ok w => some w
        | .error _ => none) with
    | some (.forallE nm d b bi) =>
      let fid := FVarId.mk (.num .anonymous fvars.size)
      let lctx' := lctx.mkLocalDecl fid nm d bi
      let fvar : Expr := .fvar fid
      match stripIndTypeGo env k lctx' (fvars.push fvar) (b.instantiate1 fvar) with
      | some (ds, u) => some (d.headBeta.abstract fvars :: ds, u)
      | none => none
    | _ => none

/-- Derives the `n` parameter/index binder domains and result universe level `u` of an inductive's
type `e`, reducing aliases via `Lean.Kernel.whnf`. -/
def stripIndType (env : Environment) (n : Nat) (e : Expr) : Option (List Expr × Level) :=
  stripIndTypeGo env n {} #[] e

/-- Strips leading forall binders from `e` whose domains match `doms` by `Expr.eqv` (`==`),
returning the remaining body. -/
def stripForallsWithDomains : List Expr → Expr → Option Expr
  | [], e => some e
  | d :: ds, .forallE _ td b _ =>
    if td == d then stripForallsWithDomains ds b else none
  | _ :: _, _ => none

/-- Strips leading lambda binders from `e` whose domains match `doms` by `Expr.eqv` (`==`),
returning the remaining body. -/
def stripLamsWithDomains : List Expr → Expr → Option Expr
  | [], e => some e
  | d :: ds, .lam _ vd b _ =>
    if vd == d then stripLamsWithDomains ds b else none
  | _ :: _, _ => none

/-- Strips `k` leading lambda binders from `val` and `k` leading forall binders from `ty` in lockstep,
checking `Expr.eqv` (`==`) on each lambda domain against the head-beta-reduced forall domain
(`Lean/MetavarContext.lean:1358` at v4.36.0). -/
def stripLamMatchingForall : Nat → Expr → Expr → Option (Expr × Expr)
  | 0, v, t => some (v, t)
  | k + 1, .lam _ vd vb _, .forallE _ td tb _ =>
    if vd == td.headBeta then stripLamMatchingForall k vb tb else none
  | _ + 1, _, _ => none

/-- The list `[.bvar (n - 1 + offset), ..., .bvar offset]`. -/
def bvarList : Nat → Nat → List Expr
  | 0, _ => []
  | n + 1, offset => .bvar (n + offset) :: bvarList n offset

/-- Lifts outer parameter bound variables (`≥ depth`) in each index domain by `shift`, giving the
motive's index binder domains inside `ind.ctorIdx`. -/
def liftIdxDomains (shift : Nat) : Nat → List Expr → List Expr
  | _, [] => []
  | depth, d :: ds => d.liftLooseBVars depth shift :: liftIdxDomains shift (depth + 1) ds

/-- Checks that `ind.casesOn` is a safe definition whose `levelParams`, `type`, and `value` match
`Lean.mkCasesOnImp env.toKernelEnv ind` (`Lean/Meta/Constructions/CasesOn.lean:17`,
`Lean/Environment.lean:730-732` at v4.36.0) with an extra universe parameter beyond
`indInfo.levelParams` (`Lean/Meta/Constructions/CtorIdx.lean:87`). -/
def checkCasesOn (env : Environment) (ind : Name) (indInfo : InductiveVal) : Bool :=
  match env.find? (.str ind "casesOn"), Lean.mkCasesOnImp env.toKernelEnv ind with
  | some (.defnInfo cv), .ok (.defnDecl d) =>
    cv.safety == .safe && d.levelParams.length > indInfo.levelParams.length &&
      cv.levelParams == d.levelParams && cv.type == d.type && cv.value == d.value
  | _, _ => false

/-- Checks that each branch in `alts` matches its constructor in `ctors`: `cInfo.numFields` lambdas
whose domains match `cInfo.type` after stripping and instantiating `np` constructor parameters,
around the raw natural literal `cInfo.cidx` (`Lean/Meta/Constructions/CtorIdx.lean:108-113` at
v4.36.0). -/
def checkCtorAlts (env : Environment) (ind : Name) (np ni : Nat) :
    List Name → List Expr → Bool
  | [], [] => true
  | c :: cs, alt :: alts =>
    match env.find? c with
    | some (.ctorInfo cInfo) =>
      cInfo.induct == ind &&
        match stripForalls np cInfo.type with
        | some cRest =>
          let cInst := cRest.instantiateRev (bvarList np (ni + 1)).toArray
          match stripLamMatchingForall cInfo.numFields alt cInst with
          | some (.lit (.natVal cidx), _) =>
            cidx == cInfo.cidx && checkCtorAlts env ind np ni cs alts
          | _ => false
        | none => false
    | _ => false
  | _, _ => false

/-- Whether `d` has the exact structural form of Lean's compiler-generated safe definition
`ind.ctorIdx` (`Lean/Meta/Constructions/CtorIdx.lean:77-141` at v4.36.0): a safe definition for a
safe, non-single-constructor, non-builtin, non-`Prop` inductive `ind`, whose parameter, index,
discriminant, motive, and constructor-branch field domains match those derived from `ind.type` and
each constructor's type, dispatching via `ind.casesOn.{1, us}` verified against `Lean.mkCasesOnImp`
to each constructor's index literal `cInfo.cidx`. -/
def isCtorIdxDef (env : Environment) (ind : Name) (indInfo : InductiveVal) (d : DefinitionVal) :
    Bool :=
  let np := indInfo.numParams
  let ni := indInfo.numIndices
  let n := np + ni
  let us := indInfo.levelParams.map Level.param
  !indInfo.isUnsafe && indInfo.numCtors != 1 && !Lean.Compiler.LCNF.isRuntimeBuiltinType ind &&
    d.safety == .safe && d.levelParams == indInfo.levelParams &&
    checkCasesOn env ind indInfo &&
    match stripIndType env n indInfo.type with
    | some (doms, u) =>
      let discrTy := Lean.mkAppN (.const ind us) (bvarList n 0).toArray
      let expectedDoms := doms ++ [discrTy]
      let motiveDiscrTy :=
        Lean.mkAppN (.const ind us) ((bvarList np (ni + 1 + ni) ++ bvarList ni 0).toArray)
      let motiveDoms := liftIdxDomains (ni + 1) 0 (doms.drop np) ++ [motiveDiscrTy]
      u.normalize != .zero &&
        stripForallsWithDomains expectedDoms d.type == some (.const `Nat []) &&
        match stripLamsWithDomains expectedDoms d.value with
        | some body =>
          let args := body.getAppArgs.toList
          body.getAppFn == .const (Name.str ind "casesOn") (.succ .zero :: us) &&
            match args.drop np with
            | motive :: rest2 =>
              match rest2.drop ni with
              | discr :: alts =>
                args.take np == bvarList np (ni + 1) &&
                  stripLamsWithDomains motiveDoms motive == some (.const `Nat []) &&
                  rest2.take ni == bvarList ni 1 &&
                  discr == .bvar 0 &&
                  checkCtorAlts env ind np ni indInfo.ctors alts
              | [] => false
            | [] => false
        | none => false
    | none => false

/-- Whether `d` has the exact structural form of Lean's compiler-generated unsafe implementation
`ind.ctorIdx._impl` (`Lean/Meta/Constructions/CtorIdx.lean:40-69` at v4.36.0): an unsafe definition
matching `dDef`'s universe parameters and type verbatim, whose parameter, index, and discriminant
domains match those derived from `ind.type` (with the second `headBeta` pass `mkCtorIdxImpl`'s
`mkLambdaFVars` applies to value binder domains, `Lean/Meta/Constructions/CtorIdx.lean:44-48`,
`Lean/MetavarContext.lean:1358` at v4.36.0), and whose body is `n + 1` lambdas around
`@getObjTagNat.{u} (ind.{us} #n ... #1) #0` at `ind.type`'s exact non-zero sort `u`. -/
def isCtorIdxImpl (env : Environment) (ind : Name) (indInfo : InductiveVal)
    (dDef d : DefinitionVal) : Bool :=
  let n := indInfo.numParams + indInfo.numIndices
  let us := indInfo.levelParams.map Level.param
  !indInfo.isUnsafe && indInfo.numCtors != 1 && !Lean.Compiler.LCNF.isRuntimeBuiltinType ind &&
    d.safety == .unsafe &&
    d.levelParams == indInfo.levelParams && d.levelParams == dDef.levelParams &&
    d.type == dDef.type &&
    match stripIndType env n indInfo.type with
    | some (doms, u) =>
      let discrTy := Lean.mkAppN (.const ind us) (bvarList n 0).toArray
      let expectedDoms := doms ++ [discrTy]
      let expectedValDoms := doms.map Expr.headBeta ++ [discrTy]
      u.normalize != .zero &&
        stripForallsWithDomains expectedDoms d.type == some (.const `Nat []) &&
        match stripLamsWithDomains expectedValDoms d.value with
        | some (.app (.app (.const `getObjTagNat [uTag]) tyArg) (.bvar 0)) =>
          uTag == u && tyArg == Lean.mkAppN (.const ind us) (bvarList n 1).toArray
        | _ => false
    | none => false

/-- Classifies constant `n` with body `info` in environment `env` as neither half (`.none`), the
safe definition `ind.ctorIdx` (`.defn ind`), or the unsafe implementation `ind.ctorIdx._impl`
(`.impl ind`) of Lean's compiler-generated `ctorIdx` pair. -/
def ctorIdxFormOf (env : Environment) (n : Name) (info : ConstantInfo) : CtorIdxForm :=
  match n, info with
  | .str (.str ind "ctorIdx") "_impl", .defnInfo d =>
    match env.find? ind, env.find? (.str ind "ctorIdx") with
    | some (.inductInfo indInfo), some (.defnInfo dDef) =>
      if isCtorIdxImpl env ind indInfo dDef d then .impl ind else .none
    | _, _ => .none
  | .str ind "ctorIdx", .defnInfo d =>
    match env.find? ind with
    | some (.inductInfo indInfo) =>
      if isCtorIdxDef env ind indInfo d then .defn ind else .none
    | _ => .none
  | _, _ => .none

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

/-- The loaded modules whose own data states that Lean read the file as a `module` file (`ModuleData.isModule`,
`Lean/Environment.lean:109-111` at v4.36.0). -/
def Facts.moduleFiles (f : Facts) : List Name :=
  ((f.modules.zip f.env.header.moduleData).toList.filter (·.2.isModule)).map (·.1.name)

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
  initFn := Lean.getInitFnNameFor? f.env n
  inToolchain := m.inToolchain
  ctorIdxForm := ctorIdxFormOf f.env n info

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

/-- What the rules read of a constant: its kind, its safety, what it mentions, and its `ctorIdx`
form. -/
def readOf (env : Environment) (n : Name) (info : ConstantInfo) :
    Kind × Safety × List Name × List Name × CtorIdxForm :=
  (kindOf info, safetyOf info, (usesOf info).toList, (valueUsesOf info).toList,
    ctorIdxFormOf env n info)

/-- Each constant of each claimed module, with its module, as that module's `.olean` states it. -/
def Facts.claimedConstants (f : Facts) : List (Name × Name × ConstantInfo) :=
  ((f.modules.zip f.env.header.moduleData).toList.filter (·.1.claimed)).flatMap fun (m, data) =>
    (data.constNames.zip data.constants).toList.map fun (n, info) => (m.name, n, info)

/-- Whether the module's own entries give `n` neither replacement attribute. A missing module
index is not an empty set of attributes. Lean's name-based queries select only one module when
theorem names merge (`Lean/Attributes.lean:310-322` at v4.36.0). -/
def Facts.unreplaced (f : Facts) (m n : Name) : Bool :=
  match f.env.getModuleIdx? m with
  | none => false
  | some idx =>
    (Lean.Compiler.implementedByAttr.ext.getModuleEntries f.env idx).all (·.1 != n) &&
      (Lean.externAttr.ext.getModuleEntries f.env idx).all (·.1 != n)

/-- Whether module `m`'s own replacement entries for `n` are solely the compiler-generated
`(n, n._impl)` entry for a constant of form `CtorIdxForm.defn`, with no `@[extern]` entry and no
other `@[implemented_by]` entry. -/
def Facts.ctorIdxEntryOnly (f : Facts) (m n : Name) (info : ConstantInfo) : Bool :=
  match ctorIdxFormOf f.env n info, f.env.getModuleIdx? m with
  | .defn _, some idx =>
    (Lean.Compiler.implementedByAttr.ext.getModuleEntries f.env idx).all
      (fun e => e.1 != n || e.2 == .str n "_impl") &&
      (Lean.externAttr.ext.getModuleEntries f.env idx).all (·.1 != n)
  | _, _ => false

/-- Whether the module's own entries of `@[init]` and `@[builtin_init]` name no initialization function
for `n`. An entry with the anonymous name is the form that names none (`getInitFnNameForCore?`,
`Lean/Compiler/InitAttr.lean:112-116` at v4.36.0). A missing module index is not an empty set of
entries. -/
def Facts.uninitialized (f : Facts) (m n : Name) : Bool :=
  match f.env.getModuleIdx? m with
  | none => false
  | some idx =>
    (Lean.regularInitAttr.ext.getModuleEntries f.env idx).all (fun e => e.1 != n || e.2 == .anonymous) &&
      (Lean.builtinInitAttr.ext.getModuleEntries f.env idx).all (fun e => e.1 != n || e.2 == .anonymous)

/-- Whether the environment shows a constant of a claimed module to the rules: it holds a constant
of that name of which the rules read the same, in a claimed module. Lean's import merges two
theorems of one name and type, and a theorem with an axiom of that name and type: it keeps one, and
gives the name the first module that holds it (`subsumesInfo` and `finalizeImport`,
`Lean/Environment.lean:2633` and `2700-2709`). So a module's own constant can be one that no rule
reads as a subject. What a dropped constant mentions, and whether it is an axiom, the input still
states of its name (`Facts.stated`), in every loaded module; this check decides whether the rules
read a claimed module's own constant as a subject. Its own replacement attributes must be absent,
solely the compiler-generated `(n, n._impl)` entry of a `ctorIdx` definition, or the represented
constant must already carry an unexempted replacement that RG1011 refuses. When the module's own
constant is a definition, its own entries must name no initialization function, or the query must give
one for the represented constant. -/
def Facts.shown (f : Facts) (x : Name × Name × ConstantInfo) : Bool :=
  match f.env.constants.map₁[x.2.1]?, f.info? x.2.1 with
  | some kept, some m =>
    decide (readOf f.env x.2.1 kept = readOf f.env x.2.1 x.2.2) && m.claimed &&
      (f.unreplaced x.1 x.2.1 ||
        f.ctorIdxEntryOnly x.1 x.2.1 x.2.2 ||
        isExtern f.env x.2.1 ||
        match Lean.Compiler.getImplementedBy? f.env x.2.1, ctorIdxFormOf f.env x.2.1 kept with
        | some impl, .defn _ => impl != .str x.2.1 "_impl"
        | some _, _ => true
        | none, _ => false) &&
      (kindOf x.2.2 != .definition || f.uninitialized x.1 x.2.1 ||
        (Lean.getInitFnNameFor? f.env x.2.1).isSome)
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

/-- The constants of claimed modules that the merged environment does not show to the rules. -/
def Facts.unshown (f : Facts) : List (Name × Name × ConstantInfo) :=
  f.claimedConstants.filter (!f.shown ·)

/-- The first constant of a claimed module that the environment does not show and that
`fitsUnshown` does not admit through the tables `t`, with its module. -/
def Facts.unread? (f : Facts) {i : Input} (t : Tables i) : Option (Name × Name) :=
  (f.unshown.find? fun x => !fitsUnshown f t x.1 x.2.1 x.2.2).map fun x => (x.1, x.2.1)

/-- The exported (`global` or `scoped`) `@[csimp]` entries registered by module `m`, or an error if Lean
gives `m` no module index. A missing module index is not an empty set of entries. Reads
`Lean.Compiler.CSimp.ext.ext.getModuleEntries`, which `finalizeImport` populates unconditionally even
under `loadExts := false` (`Lean/Environment.lean:1990-1996`, `:2742` at v4.36.0). -/
def Facts.moduleCSimps (f : Facts) (m : Name) : Except String (List CSimpEntry) :=
  match f.env.getModuleIdx? m with
  | none => .error s!"the claimed module {m} has no index in the loaded environment, so its \
      @[csimp] entries cannot be read"
  | some idx =>
    .ok ((Lean.Compiler.CSimp.ext.ext.getModuleEntries f.env idx).toList.map fun e =>
      { module := m, thm := match e with | .global ce => ce.thmName | .scoped _ ce => ce.thmName })

/-- The exported (`global` or `scoped`) `@[csimp]` entries of the modules `claimed`, or an error if any
of them has no index in the loaded environment. -/
def Facts.csimps (f : Facts) (claimed : List Name) : Except String (List CSimpEntry) :=
  (claimed.mapM f.moduleCSimps).map List.flatten

/-- Of the target theorem names in `csimps`, those declared in any claimed module's own `moduleData`
(`Facts.claimedConstants`). Returns `[]` immediately when `csimps` is empty; when `csimps` is
nonempty, builds a hash set of the `csimps` target names only and collects hits from
`Facts.claimedConstants`, each name once (leaving `Facts.stated` unchanged and reading no dependency
module's constants; `Facts.claimedConstants` steps once over the loaded modules, dependencies
included, to select the claimed ones). -/
def Facts.claimedCSimpTargets (f : Facts) (csimps : List CSimpEntry) : List Name :=
  if csimps.isEmpty then []
  else
    let targets := setOf (csimps.map (·.thm))
    (f.claimedConstants.foldl (init := ({} : Std.HashSet Name)) fun acc x =>
      if targets.contains x.2.1 then acc.insert x.2.1 else acc).toList

/-- The closed input admitted from the draft that `f` builds, before checking unshown constants. -/
def Facts.admitDraft (f : Facts) (roots : List Name) (profile : Profile) : Except String Input :=
  let claimed := f.claimed
  match roots.find? (!claimed.contains ·) with
  | some m => .error s!"the module {m} of a default target has its .olean outside the root \
      package's build"
  | none =>
    match f.csimps claimed with
    | .error why => .error why
    | .ok csimps =>
      let stated := f.stated
      match h : f.env.constants.map₁.toList.mapM (fun x => f.decl x.1 x.2 (stated.getD x.1 [])) with
      | .error why => .error why
      | .ok decls =>
        let draft : Draft :=
          { profile, modules := claimed, moduleFiles := f.moduleFiles,
            claimedConstants := f.claimedCSimpTargets csimps, csimps, decls,
            unique := f.decls_nodup (stated := (stated.getD · [])) h }
        draft.admit

/-- Refuses `t` when `Facts.unread?` finds an unshown constant of a claimed module that
`fitsUnshown` does not admit. -/
def Facts.checkUnread (f : Facts) {i : Input} (t : Tables i) : Except String Unit :=
  match f.unread? t with
  | some (m, n) => .error s!"the module {m} holds the constant {n}, which the merged environment \
      does not show to the rules, and this one is no theorem within the profile or \
      has a recursion helper's name or unread or forbidden compiled-code attributes"
  | none => .ok ()

/-- The closed input of the environment that `f` describes, under the profile `profile`, with
`Input.tables` of it, built once. It refuses a module of `roots`, the default targets, that `f` does
not claim, a constant with no module, a reading that the admission refuses (`Draft.admit`), and a
constant that `Facts.unread?` gives. -/
def Facts.prepare (f : Facts) (roots : List Name) (profile : Profile) : Except String Prepared :=
  match f.admitDraft roots profile with
  | .error why => .error why
  | .ok i =>
    let t := i.tables
    match f.checkUnread t with
    | .error why => .error why
    | .ok () => .ok ⟨i, t⟩

theorem Facts.prepare_tables (f : Facts) (roots : List Name) (profile : Profile) {p : Prepared}
    (h : f.prepare roots profile = .ok p) : p.tables = p.input.tables := by
  simp only [Facts.prepare] at h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  rfl

/-- The closed input of the environment that `f` describes, under the profile `profile`. When every
constant of a claimed module is shown (`Facts.unshown` is empty), this skips building `Input.tables`.
A run calls `Facts.prepare` so its rules reuse the tables built during admission; on an input with an
admitted unshown constant, `Input.report` on the result of `Facts.input` builds `Input.tables` again. -/
def Facts.input (f : Facts) (roots : List Name) (profile : Profile) : Except String Input :=
  match f.admitDraft roots profile with
  | .error why => .error why
  | .ok i =>
    if f.unshown.isEmpty then .ok i
    else
      match f.checkUnread i.tables with
      | .error why => .error why
      | .ok () => .ok i

theorem Facts.input_eq_prepare_map (f : Facts) (roots : List Name) (profile : Profile) :
    f.input roots profile = (f.prepare roots profile).map (·.input) := by
  simp only [Facts.input, Facts.prepare, Facts.checkUnread, Facts.unread?]
  cases f.admitDraft roots profile with
  | error why => rfl
  | ok i =>
    cases hu : f.unshown with
    | nil => simp [Except.map]
    | cons _ _ =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
      cases ((List.find? _ _).map _) <;> rfl

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
`finalizeImport`, `Lean/Environment.lean:2633-2639` and `2700-2709` at v4.36.0), so the kernel can check the others only as
copies. A theorem counts as kept when `==` (`Expr.eqv` on each expression, `Lean/Expr.lean:803-811`) relates the two. -/
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
