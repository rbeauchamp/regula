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

public section

namespace Regula.Load

open Lean (ConstantInfo DefinitionVal Environment Expr FVarId InductiveVal Level LocalContext Name
  TheoremVal findOLean isExtern)
open System (FilePath)
open Regula.Closed

abbrev parts (p : FilePath) : List String :=
  p.normalize.components.filter fun c => c != "" && c != "."

def below (dir path : FilePath) : Bool :=
  (parts dir).isPrefixOf (parts path) && parts dir != parts path

abbrev inputName (p : FilePath) : String :=
  "/".intercalate (parts p)

def exactBelow (dir path real : FilePath) : Bool :=
  parts real == parts path && (parts dir).isPrefixOf (parts path)

def kindOf : ConstantInfo → Kind
  | .axiomInfo _ => .axiom
  | .defnInfo _ => .definition
  | .thmInfo _ => .theorem
  | .opaqueInfo _ => .opaque
  | .quotInfo _ => .quotient
  | .inductInfo _ => .inductive
  | .ctorInfo _ => .constructor
  | .recInfo _ => .recursor

def dedupStep (acc : Std.HashSet Name × Array Name) (n : Name) : Std.HashSet Name × Array Name :=
  let (seen, out) := acc
  if seen.contains n then (seen, out) else (seen.insert n, out.push n)

def dedup (all : Array Name) : Array Name :=
  (all.foldl dedupStep ({}, #[])).2

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

def usesIn (info : ConstantInfo) (stated : List ConstantInfo) : Array Name :=
  dedup (stated.foldl (fun acc v => acc ++ usesOf v) (usesOf info))

def kindIn (info : ConstantInfo) (stated : List ConstantInfo) : Kind :=
  if stated.any (kindOf · == .axiom) then .axiom else kindOf info

def valueUsesOf : ConstantInfo → Array Name
  | .defnInfo v => v.value.getUsedConstants
  | .thmInfo v => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | .axiomInfo _ | .quotInfo _ | .inductInfo _ | .ctorInfo _ | .recInfo _ => #[]

def safetyOf (info : ConstantInfo) : Safety :=
  if info.isUnsafe then .unsafe else if info.isPartial then .partial else .safe

def stripForalls : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .forallE _ _ b _ => stripForalls k b
  | _ + 1, _ => none

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

def stripIndType (env : Environment) (n : Nat) (e : Expr) : Option (List Expr × Level) :=
  stripIndTypeGo env n {} #[] e

def stripForallsWithDomains : List Expr → Expr → Option Expr
  | [], e => some e
  | d :: ds, .forallE _ td b _ =>
    if td == d then stripForallsWithDomains ds b else none
  | _ :: _, _ => none

def stripLamsWithDomains : List Expr → Expr → Option Expr
  | [], e => some e
  | d :: ds, .lam _ vd b _ =>
    if vd == d then stripLamsWithDomains ds b else none
  | _ :: _, _ => none

def stripLamMatchingForall : Nat → Expr → Expr → Option (Expr × Expr)
  | 0, v, t => some (v, t)
  | k + 1, .lam _ vd vb _, .forallE _ td tb _ =>
    if vd == td.headBeta then stripLamMatchingForall k vb tb else none
  | _ + 1, _, _ => none

def bvarList : Nat → Nat → List Expr
  | 0, _ => []
  | n + 1, offset => .bvar (n + offset) :: bvarList n offset

def liftIdxDomains (shift : Nat) : Nat → List Expr → List Expr
  | _, [] => []
  | depth, d :: ds => d.liftLooseBVars depth shift :: liftIdxDomains shift (depth + 1) ds

def checkCasesOn (env : Environment) (ind : Name) (indInfo : InductiveVal) : Bool :=
  match env.find? (.str ind "casesOn"), Lean.mkCasesOnImp env.toKernelEnv ind with
  | some (.defnInfo cv), .ok (.defnDecl d) =>
    cv.safety == .safe && d.levelParams.length > indInfo.levelParams.length &&
      cv.levelParams == d.levelParams && cv.type == d.type && cv.value == d.value
  | _, _ => false

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

structure LoadedModule where
  name : Name
  olean : FilePath
  inToolchain : Bool
  claimed : Bool

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

structure Facts where
  env : Environment
  toolchainDir : FilePath
  rootDir : FilePath
  modules : Array LoadedModule
  names : modules.toList.map (·.name) = env.header.moduleNames.toList
  placed : ∀ m ∈ modules, m = LoadedModule.ofPlace toolchainDir rootDir m.name m.olean

def Facts.claimed (f : Facts) : List Name :=
  (f.modules.toList.filter (·.claimed)).map (·.name)

def Facts.moduleFiles (f : Facts) : List Name :=
  ((f.modules.zip f.env.header.moduleData).toList.filter (·.2.isModule)).map (·.1.name)

def Facts.info? (f : Facts) (n : Name) : Option LoadedModule :=
  (f.env.getModuleIdxFor? n).bind fun idx => f.modules[idx.toNat]?

def Facts.moduleOf? (f : Facts) (n : Name) : Option Name :=
  (f.info? n).map (·.name)

def Facts.stated (f : Facts) : Std.HashMap Name (List ConstantInfo) :=
  f.env.header.moduleData.foldl (init := {}) fun acc data =>
    (data.constNames.zip data.constants).foldl (init := acc) fun acc x =>
      acc.insert x.1 (x.2 :: acc.getD x.1 [])

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

def readOf (env : Environment) (n : Name) (info : ConstantInfo) :
    Kind × Safety × List Name × List Name × CtorIdxForm :=
  (kindOf info, safetyOf info, (usesOf info).toList, (valueUsesOf info).toList,
    ctorIdxFormOf env n info)

def Facts.claimedConstants (f : Facts) : List (Name × Name × ConstantInfo) :=
  ((f.modules.zip f.env.header.moduleData).toList.filter (·.1.claimed)).flatMap fun (m, data) =>
    (data.constNames.zip data.constants).toList.map fun (n, info) => (m.name, n, info)

def Facts.unreplaced (f : Facts) (m n : Name) : Bool :=
  match f.env.getModuleIdx? m with
  | none => false
  | some idx =>
    (Lean.Compiler.implementedByAttr.ext.getModuleEntries f.env idx).all (·.1 != n) &&
      (Lean.externAttr.ext.getModuleEntries f.env idx).all (·.1 != n)

def Facts.ctorIdxEntryOnly (f : Facts) (m n : Name) (info : ConstantInfo) : Bool :=
  match ctorIdxFormOf f.env n info, f.env.getModuleIdx? m with
  | .defn _, some idx =>
    (Lean.Compiler.implementedByAttr.ext.getModuleEntries f.env idx).all
      (fun e => e.1 != n || e.2 == .str n "_impl") &&
      (Lean.externAttr.ext.getModuleEntries f.env idx).all (·.1 != n)
  | _, _ => false

def Facts.uninitialized (f : Facts) (m n : Name) : Bool :=
  match f.env.getModuleIdx? m with
  | none => false
  | some idx =>
    (Lean.regularInitAttr.ext.getModuleEntries f.env idx).all (fun e => e.1 != n || e.2 == .anonymous) &&
      (Lean.builtinInitAttr.ext.getModuleEntries f.env idx).all (fun e => e.1 != n || e.2 == .anonymous)

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

def fitsUnshown (f : Facts) {i : Input} (t : Tables i) (m n : Name) (info : ConstantInfo) : Bool :=
  f.unreplaced m n && (kindOf info == .theorem && safetyOf info == .safe &&
    (Lean.Compiler.isUnsafeRecName? n).isNone &&
    loopConstructs.all (!(valueUsesOf info).contains ·) &&
    (usesOf info).all fun u => t.index.contains u && (t.axiomSet u).all (t.admits i.profile ·))

def Facts.unshown (f : Facts) : List (Name × Name × ConstantInfo) :=
  f.claimedConstants.filter (!f.shown ·)

def Facts.unread? (f : Facts) {i : Input} (t : Tables i) : Option (Name × Name) :=
  (f.unshown.find? fun x => !fitsUnshown f t x.1 x.2.1 x.2.2).map fun x => (x.1, x.2.1)

def Facts.moduleCSimps (f : Facts) (m : Name) : Except String (List CSimpEntry) :=
  match f.env.getModuleIdx? m with
  | none => .error s!"the claimed module {m} has no index in the loaded environment, so its \
      @[csimp] entries cannot be read"
  | some idx =>
    .ok ((Lean.Compiler.CSimp.ext.ext.getModuleEntries f.env idx).toList.map fun e =>
      { module := m, thm := match e with | .global ce => ce.thmName | .scoped _ ce => ce.thmName })

def Facts.csimps (f : Facts) (claimed : List Name) : Except String (List CSimpEntry) :=
  (claimed.mapM f.moduleCSimps).map List.flatten

def Facts.claimedCSimpTargets (f : Facts) (csimps : List CSimpEntry) : List Name :=
  if csimps.isEmpty then []
  else
    let targets := setOf (csimps.map (·.thm))
    (f.claimedConstants.foldl (init := ({} : Std.HashSet Name)) fun acc x =>
      if targets.contains x.2.1 then acc.insert x.2.1 else acc).toList

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

def Facts.checkUnread (f : Facts) {i : Input} (t : Tables i) : Except String Unit :=
  match f.unread? t with
  | some (m, n) => .error s!"the module {m} holds the constant {n}, which the merged environment \
      does not show to the rules, and this one is no theorem within the profile or \
      has a recursion helper's name or unread or forbidden compiled-code attributes"
  | none => .ok ()

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

def replays : ConstantInfo → Bool
  | .quotInfo v =>
    match v.kind with
    | .type => true
    | _ => false
  | _ => true

def replayStep (constants m : Std.HashMap Name ConstantInfo) (n : Name) : Std.HashMap Name ConstantInfo :=
  match constants[n]? with
  | some info => if replays info then m.insert n info else m
  | none => m

def depth : Name → Nat
  | .anonymous => 0
  | .str p _ => depth p + 1
  | .num p _ => depth p + 1

def zeros : Nat → Name
  | 0 => .anonymous
  | d + 1 => .num (zeros d) 0

def copyRoot (constants : Std.HashMap Name ConstantInfo) : Name :=
  zeros (constants.keys.foldl (fun d n => max d (depth n)) 0 + 1)

def Facts.copies (f : Facts) : List TheoremVal :=
  f.claimedConstants.filterMap fun (_, n, info) =>
    match info with
    | .thmInfo v => if f.env.constants.map₁[n]? == some info then none else some v
    | _ => none

def copyAt (root : Name) (x : TheoremVal × Nat) : Name × ConstantInfo :=
  (.num root x.2, .thmInfo { x.1 with name := .num root x.2, all := [.num root x.2] })

def Facts.coneSeeds (f : Facts) : List Name :=
  f.claimedConstants.map (·.2.1) ++ Input.kernelNames

def Facts.replayConstants (f : Facts) (i : Input) : Std.HashMap Name ConstantInfo :=
  ((f.copies.zipIdx.map (copyAt (copyRoot f.env.constants.map₁))).foldl (fun m x => m.insert x.1 x.2)
    ((i.cone f.coneSeeds).toList.foldl (replayStep f.env.constants.map₁) {}))

def startsSearchPath (loaded received : List String) : Bool :=
  loaded.isPrefixOf received

end Regula.Load
