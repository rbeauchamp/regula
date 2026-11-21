module

public import Regula.Load
public import Regula.Shell
public import RegulaSpecification.Proofs.Verdict
public import RegulaSpecification.Refinement
public import Lean.Compiler.CSimpAttr
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.ImplementedByAttr
import all Lean.Declaration
import all Regula.Input
import all Regula.Load
import all Regula.Rule
import all Regula.Rules
import all Regula.Shell
import all Regula.Tables
import all Regula.Verdict

/-!
# The loader, against the environment

{name}`Regula.Load.Facts.input` is the pure function that fills the closed input from a loaded environment, and
{name}`Regula.Closed.Input.report` the verdict that the checker gives on that input. {lit}`pass_iff` relates the two to
the environment: for every environment and {name (full := Regula.Load.Facts)}`Facts` on which the loader gives an input, a pass is exactly
{lit}`EnvForm` and {lit}`EnvFloor`, two statements that mention no field of the input. Each constant is read from
`Environment.constants.map₁` by name. What a name mentions, and whether it names an axiom, is read from
the fields of that {name (full := Lean.ConstantInfo)}`ConstantInfo` and of each constant of the name that any loaded module's own data states
({lit}`EnvMentions`, {lit}`EnvAxiom`, {lit}`mem_usesIn`), and {lit}`mem_stated` anchors those in `header.moduleData`. So an
axiom or a chain of mentions that Lean's import drops still counts. On a pass, each axiom reached that way
from a constant of a claimed module is one that the profile admits, and each claimed module is a {lit}`module`
file by the data of its {lit}`.olean` ({lit}`EnvFloor`, {lit}`EnvModuleFile`). {lit}`pass_held` states a pass
of each constant that {name (full := Regula.Load.Facts.claimedConstants)}`Facts.claimedConstants` lists, as that module's own {lit}`.olean` states it, also when
Lean's import replaced it.

So a loader that dropped a constant, a field or a mention would fail these proofs in the gate's build of
this package. What they leave assumed is Lean's and Lake's behaviour: that {name (full := Lean.SMap.map₁)}`map₁` holds the constants that
{name}`Lean.importModules` keeps and `header.moduleData` what each {lit}`.olean` states, what each query of the
environment returns, that {name (full := Lean.Expr.getUsedConstants)}`Expr.getUsedConstants` lists each constant of an expression, that {name (full := Lean.findOLean)}`findOLean`
finds each {lit}`.olean`, and that Lake names the modules of the default targets and the two library directories.
The specification's trusted base lists them.
-/

@[expose] public section

namespace RegulaSpecification

open Lean (Name ConstantInfo)
open Link

namespace Loader

variable {f : Regula.Load.Facts} {roots : List Name} {p : Regula.Closed.Profile}
  {i : Regula.Closed.Input}

/-- What a constant mentions, read from the fields of its {name}`ConstantInfo`: what Lean's kernel checks it against when
Lean replays it. That is the type of each constant, the value of a definition, theorem or opaque constant, the
constructors and the other types of an inductive type's block, the inductive type of a constructor, the types of a
recursor's block, and {lit}`Eq` for a quotient, whose check in the kernel reads it. -/
def Mentions : ConstantInfo → Name → Prop
  | .axiomInfo v, u => u ∈ v.type.getUsedConstants
  | .defnInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.value.getUsedConstants
  | .thmInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.value.getUsedConstants
  | .opaqueInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.value.getUsedConstants
  | .quotInfo v, u => u ∈ v.type.getUsedConstants ∨ u = `Eq
  | .ctorInfo v, u => u ∈ v.type.getUsedConstants ∨ u = v.induct
  | .recInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.all
  | .inductInfo v, u => u ∈ v.type.getUsedConstants ∨ u ∈ v.ctors ∨ u ∈ v.all

/-- What the value of a constant mentions, and nothing of a constant that has no value. -/
def ValueMentions : ConstantInfo → Name → Prop
  | .defnInfo v, u => u ∈ v.value.getUsedConstants
  | .thmInfo v, u => u ∈ v.value.getUsedConstants
  | .opaqueInfo v, u => u ∈ v.value.getUsedConstants
  | .axiomInfo _, _ | .quotInfo _, _ | .inductInfo _, _ | .ctorInfo _, _ | .recInfo _, _ => False

theorem mem_dedupFold (l : List Name) (seen : Std.HashSet Name) (out : Array Name)
    (hinv : ∀ x, seen.contains x = true ↔ x ∈ out) (u : Name) :
    u ∈ (l.foldl Regula.Load.dedupStep (seen, out)).2 ↔ u ∈ l ∨ u ∈ out := by
  induction l generalizing seen out with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_or]
  | cons a l ih =>
    simp only [List.foldl_cons, Regula.Load.dedupStep, List.mem_cons]
    split
    · have ha := (hinv a).mp ‹_›
      rw [ih seen out hinv]; grind only
    · have hinv' : ∀ x, (seen.insert a).contains x = true ↔ x ∈ out.push a := fun x => by
        simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hinv, Array.mem_push,
          eq_comm (a := a), or_comm]
      rw [ih _ _ hinv']; simp only [Array.mem_push]; grind only

theorem mem_dedup (all : Array Name) (u : Name) : u ∈ Regula.Load.dedup all ↔ u ∈ all := by
  simpa [Regula.Load.dedup, ← Array.foldl_toList] using mem_dedupFold all.toList {} #[] (by simp) u

theorem mem_usesOf (info : ConstantInfo) (u : Name) :
    u ∈ (Regula.Load.usesOf info).toList ↔ Mentions info u := by
  unfold Regula.Load.usesOf
  rw [Array.mem_toList_iff, mem_dedup]
  cases info <;> simp only [Mentions, Array.mem_append, Array.mem_push, List.mem_toArray, or_assoc]

theorem mem_usesFold (l : List ConstantInfo) (acc : Array Name) (u : Name) :
    u ∈ l.foldl (fun acc v => acc ++ Regula.Load.usesOf v) acc ↔
      u ∈ acc ∨ ∃ v ∈ l, Mentions v u := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, or_false]
  | cons a l ih =>
    simp only [List.foldl_cons, ih, Array.mem_append, (Array.mem_toList_iff ..).symm.trans (mem_usesOf a u),
      List.mem_cons, exists_eq_or_imp, or_assoc]

theorem mem_usesIn (info : ConstantInfo) (stated : List ConstantInfo) (u : Name) :
    u ∈ (Regula.Load.usesIn info stated).toList ↔ Mentions info u ∨ ∃ v ∈ stated, Mentions v u := by
  unfold Regula.Load.usesIn
  rw [Array.mem_toList_iff, mem_dedup, mem_usesFold, ← Array.mem_toList_iff, mem_usesOf]

theorem mem_valueUsesOf (info : ConstantInfo) (u : Name) :
    u ∈ (Regula.Load.valueUsesOf info).toList ↔ ValueMentions info u := by
  cases info <;> simp only [Regula.Load.valueUsesOf, ValueMentions, Array.mem_toList_iff, Array.toList_empty, List.not_mem_nil]

theorem mem_statedPairs (l : List (Name × ConstantInfo))
    (acc : Std.HashMap Name (List ConstantInfo)) (n : Name) (v : ConstantInfo) :
    v ∈ (l.foldl (fun acc x => acc.insert x.1 (x.2 :: acc.getD x.1 [])) acc).getD n [] ↔
      (n, v) ∈ l ∨ v ∈ acc.getD n [] := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_or]
  | cons a l ih =>
    rcases a with ⟨c, w⟩
    simp only [List.foldl_cons, ih, List.mem_cons, Prod.mk.injEq, Std.HashMap.getD_insert]
    by_cases hc : c = n
    · subst hc; simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons]; grind only
    · have hb : (c == n) = false := beq_false_of_ne hc
      simp only [hb, Bool.false_eq_true, ↓reduceIte]; grind only

theorem mem_statedData (l : List Lean.ModuleData)
    (acc : Std.HashMap Name (List ConstantInfo)) (n : Name) (v : ConstantInfo) :
    v ∈ (l.foldl (fun acc data => (data.constNames.zip data.constants).foldl
        (fun acc x => acc.insert x.1 (x.2 :: acc.getD x.1 [])) acc) acc).getD n [] ↔
      (∃ data ∈ l, (n, v) ∈ data.constNames.zip data.constants) ∨ v ∈ acc.getD n [] := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, false_or]
  | cons a l ih =>
    have hp := mem_statedPairs (a.constNames.zip a.constants).toList acc n v
    simp only [Array.foldl_toList, Array.mem_toList_iff] at hp
    simp only [List.foldl_cons, ih, hp, List.mem_cons, exists_eq_or_imp]
    rw [or_left_comm, ← or_assoc]

theorem mem_stated {n : Name} {v : ConstantInfo} :
    v ∈ f.stated.getD n [] ↔ ∃ data ∈ f.env.header.moduleData,
      (n, v) ∈ data.constNames.zip data.constants := by
  simpa [Regula.Load.Facts.stated, Array.foldl_toList, Array.mem_toList_iff] using
    mem_statedData f.env.header.moduleData.toList {} n v

/-- A constant is an axiom, by the constructor of its {name}`ConstantInfo`. -/
def AxiomInfo (k : ConstantInfo) : Prop := ∃ w, k = .axiomInfo w

/-- What the name {name}`c` mentions in the environment: what the constant that the environment keeps
mentions, and what each constant of that name that a loaded module's own data states mentions. -/
def EnvMentions (f : Regula.Load.Facts) (c u : Name) : Prop :=
  ∃ k, f.env.constants.map₁[c]? = some k ∧
    (Mentions k u ∨ ∃ v ∈ f.stated.getD c [], Mentions v u)

/-- The name {name}`a` names an axiom in the environment: the constant that the environment keeps is one,
or a constant of that name that a loaded module's own data states is one. -/
def EnvAxiom (f : Regula.Load.Facts) (a : Name) : Prop :=
  ∃ k, f.env.constants.map₁[a]? = some k ∧
    (AxiomInfo k ∨ ∃ v ∈ f.stated.getD a [], AxiomInfo v)

/-- {lit}`c` reaches {lit}`e` through what the names of the environment mention. -/
inductive EnvReaches (f : Regula.Load.Facts) : Name → Name → Prop
  /-- A constant reaches itself. -/
  | refl (c : Name) : EnvReaches f c c
  /-- A constant reaches what a constant that it mentions reaches. -/
  | step {c u e : Name} : EnvMentions f c u → EnvReaches f u e → EnvReaches f c e

/-- The closed form of the input, in the terms of the environment: each constant that a name
mentions is held, and at least one module is claimed. -/
structure EnvForm (f : Regula.Load.Facts) : Prop where
  /-- Each mentioned constant is held. -/
  closed : ∀ n u, EnvMentions f n u → ∃ info', f.env.constants.map₁[u]? = some info'
  /-- At least one module is claimed. -/
  claims : f.claimed ≠ []

/-- The constant {name}`a` is one of the toolchain's: the module that holds it lies in its library. -/
def EnvToolchain (f : Regula.Load.Facts) (a : Name) : Prop :=
  ∃ m, f.info? a = some m ∧ m.inToolchain = true

/-- Profile {name}`p` admits the axiom {lit}`a` of the environment: one of Lean's three, the toolchain's own
constant of that name, and in the profile's set. -/
def EnvAdmits (f : Regula.Load.Facts) : Regula.Closed.Profile → Name → Prop
  | .kernelOnly, _ => False
  | .choiceFree, a => (a = ``propext ∨ a = ``Quot.sound) ∧ EnvToolchain f a
  | .standardLogical, a =>
    (a = ``propext ∨ a = ``Quot.sound ∨ a = ``Classical.choice) ∧ EnvToolchain f a

/-- The form of a recursion helper: a partial, safe-flagged constant `b._unsafe_rec` with no
{attr}`@[implemented_by]` and not {attr}`@[extern]`, beside a safe, total definition {lit}`b` of its module of which
the same two hold, and of whose name no loaded module states an axiom. -/
def EnvHelper (f : Regula.Load.Facts) (n : Name) (info : ConstantInfo) (m : Name) : Prop :=
  info.isPartial = true ∧ info.isUnsafe = false ∧
    Lean.Compiler.getImplementedBy? f.env n = none ∧ Lean.isExtern f.env n = false ∧
    ∃ b v, n = .str b "_unsafe_rec" ∧ f.env.constants.map₁[b]? = some (.defnInfo v) ∧
      (∀ w ∈ f.stated.getD b [], ¬ AxiomInfo w) ∧
      f.moduleOf? b = some m ∧ (ConstantInfo.defnInfo v).isUnsafe = false ∧
      (ConstantInfo.defnInfo v).isPartial = false ∧
      Lean.Compiler.getImplementedBy? f.env b = none ∧ Lean.isExtern f.env b = false

/-- The fifteen types with builtin runtime support ({lit}`Lean.Compiler.LCNF.builtinRuntimeTypes`,
{lit}`Lean/Compiler/LCNF/Util.lean:40-47` at v4.36.0), stated as a literal apart from the checker's list. -/
def RuntimeBuiltinTypes : List Name :=
  [`String, `UInt8, `UInt16, `UInt32, `UInt64, `USize, `Float, `Float32,
   `Thunk, `Task, `Array, `ByteArray, `FloatArray, `Nat, `Int]

/-- Strips {lit}`k` leading lambda binders from an expression. -/
def stripLamsSpec : Nat → Lean.Expr → Option Lean.Expr
  | 0, e => some e
  | k + 1, .lam _ _ b _ => stripLamsSpec k b
  | _ + 1, _ => none

/-- Strips {lit}`k` leading forall binders from an expression. -/
def stripForallsSpec : Nat → Lean.Expr → Option Lean.Expr
  | 0, e => some e
  | k + 1, .forallE _ _ b _ => stripForallsSpec k b
  | _ + 1, _ => none

/-- Strips {lit}`k` leading lambda binders from {lit}`val` and {lit}`k` leading forall binders from
{lit}`ty` in lockstep, checking {lit}`Expr.eqv` ({lit}`==`) on each binder domain. -/
def stripLamMatchingForallSpec : Nat → Lean.Expr → Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | 0, v, t => some (v, t)
  | k + 1, .lam _ vd vb _, .forallE _ td tb _ =>
    if vd == td then stripLamMatchingForallSpec k vb tb else none
  | _ + 1, _, _ => none

/-- Applies {name}`fn` to {lit}`n` consecutive bound variables down to {lit}`offset`. -/
def mkBVarAppsSpec (fn : Lean.Expr) : Nat → Nat → Lean.Expr
  | 0, _ => fn
  | n + 1, offset => mkBVarAppsSpec (.app fn (.bvar (n + offset))) n offset

/-- Unwinds nested applications into head and argument list. -/
def unappGoSpec : Lean.Expr → List Lean.Expr → Lean.Expr × List Lean.Expr
  | .app f a, acc => unappGoSpec f (a :: acc)
  | e, acc => (e, acc)

/-- The list of {lit}`n` consecutive bound variables down to {lit}`offset`. -/
def bvarListSpec : Nat → Nat → List Lean.Expr
  | 0, _ => []
  | n + 1, offset => .bvar (n + offset) :: bvarListSpec n offset

/-- Checks that each branch matches its constructor's arity and index literal {lit}`cInfo.cidx`. -/
def checkCtorAltsSpec (env : Lean.Environment) (ind : Name) : List Name → List Lean.Expr → Bool
  | [], [] => true
  | c :: cs, alt :: alts =>
    match env.find? c with
    | some (.ctorInfo cInfo) =>
      cInfo.induct == ind &&
        stripLamsSpec cInfo.numFields alt == some (.lit (.natVal cInfo.cidx)) &&
        checkCtorAltsSpec env ind cs alts
    | _ => false
  | _, _ => false

/-- Independent specification of the structural shape of Lean's safe {lit}`ind.ctorIdx` definition
({lit}`Lean/Meta/Constructions/CtorIdx.lean:77-141` at v4.36.0), stated apart from {lit}`Regula.Load`. -/
def ctorIdxDefShape (env : Lean.Environment) (ind : Name) (indInfo : Lean.InductiveVal)
    (d : Lean.DefinitionVal) : Bool :=
  let np := indInfo.numParams
  let ni := indInfo.numIndices
  let n := np + ni
  let us := indInfo.levelParams.map Lean.Level.param
  !indInfo.isUnsafe && indInfo.numCtors != 1 && !RuntimeBuiltinTypes.contains ind &&
    d.safety == .safe && d.levelParams == indInfo.levelParams &&
    stripForallsSpec n indInfo.type != some (.sort .zero) &&
    match stripLamMatchingForallSpec (n + 1) d.value d.type, stripForallsSpec n d.type with
    | some (body, retTy), some (.forallE _ discrTy (.const `Nat []) _) =>
      retTy == .const `Nat [] &&
        discrTy == mkBVarAppsSpec (.const ind us) n 0 &&
        let (fn, args) := unappGoSpec body []
        fn == .const (Name.str ind "casesOn") (.succ .zero :: us) &&
          args.length == np + 1 + ni + 1 + indInfo.ctors.length &&
          match args.drop np with
          | motive :: rest2 =>
            match rest2.drop ni with
            | discr :: alts =>
              args.take np == bvarListSpec np (ni + 1) &&
                stripLamsSpec (ni + 1) motive == some (.const `Nat []) &&
                rest2.take ni == bvarListSpec ni 1 &&
                discr == .bvar 0 &&
                checkCtorAltsSpec env ind indInfo.ctors alts
            | [] => false
          | [] => false
    | _, _ => false

/-- Independent specification of the structural shape of Lean's unsafe {lit}`ind.ctorIdx._impl`
implementation ({lit}`Lean/Meta/Constructions/CtorIdx.lean:40-69` at v4.36.0), stated apart from
{lit}`Regula.Load`. -/
def ctorIdxImplShape (ind : Name) (indInfo : Lean.InductiveVal)
    (dDef d : Lean.DefinitionVal) : Bool :=
  let n := indInfo.numParams + indInfo.numIndices
  let us := indInfo.levelParams.map Lean.Level.param
  !indInfo.isUnsafe && indInfo.numCtors != 1 && !RuntimeBuiltinTypes.contains ind &&
    d.safety == .unsafe &&
    d.levelParams == indInfo.levelParams && d.levelParams == dDef.levelParams &&
    d.type == dDef.type &&
    stripForallsSpec n indInfo.type != some (.sort .zero) &&
    match stripLamMatchingForallSpec (n + 1) d.value d.type with
    | some (.app (.app (.const `getObjTagNat [u]) tyArg) (.bvar 0), .const `Nat []) =>
      u.isNeverZero && tyArg == mkBVarAppsSpec (.const ind us) n 1
    | _ => false

/-- Independent classification of a constant {name}`n` with {name}`info` in {name}`env` as
{lit}`CtorIdxForm.defn`, {lit}`CtorIdxForm.impl`, or {lit}`CtorIdxForm.none`, stated without naming
{lit}`Regula.Load`. -/
def ctorIdxShape (env : Lean.Environment) (n : Name) (info : ConstantInfo) : CtorIdxForm :=
  match n, info with
  | .str (.str ind "ctorIdx") "_impl", .defnInfo d =>
    match env.find? ind, env.find? (Name.str ind "ctorIdx") with
    | some (.inductInfo indInfo), some (.defnInfo dDef) =>
      if ctorIdxImplShape ind indInfo dDef d then .impl ind else .none
    | _, _ => .none
  | .str ind "ctorIdx", .defnInfo d =>
    match env.find? ind with
    | some (.inductInfo indInfo) =>
      if ctorIdxDefShape env ind indInfo d then .defn ind else .none
    | _ => .none
  | _, _ => .none

theorem runtimeBuiltinTypes_eq : Regula.Load.runtimeBuiltinTypes = RuntimeBuiltinTypes := by rfl

theorem stripLams_eq (k : Nat) (e : Lean.Expr) :
    Regula.Load.stripLams k e = stripLamsSpec k e := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih => cases e <;> first | rfl | exact ih _

theorem stripForalls_eq (k : Nat) (e : Lean.Expr) :
    Regula.Load.stripForalls k e = stripForallsSpec k e := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih => cases e <;> first | rfl | exact ih _

theorem stripLamMatchingForall_eq (k : Nat) (v t : Lean.Expr) :
    Regula.Load.stripLamMatchingForall k v t = stripLamMatchingForallSpec k v t := by
  induction k generalizing v t with
  | zero => rfl
  | succ k ih =>
    cases v <;> cases t <;> first | rfl | (
      simp only [Regula.Load.stripLamMatchingForall, stripLamMatchingForallSpec]
      split <;> first | rfl | exact ih _ _)

theorem mkBVarApps_eq (fn : Lean.Expr) (n offset : Nat) :
    Regula.Load.mkBVarApps fn n offset = mkBVarAppsSpec fn n offset := by
  induction n generalizing fn with
  | zero => rfl
  | succ n ih => exact ih _

theorem unappGo_eq (e : Lean.Expr) (acc : List Lean.Expr) :
    Regula.Load.unappGo e acc = unappGoSpec e acc := by
  induction e generalizing acc with
  | app f a ihf _ => exact ihf _
  | _ => rfl

theorem bvarList_eq (n offset : Nat) :
    Regula.Load.bvarList n offset = bvarListSpec n offset := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Regula.Load.bvarList, bvarListSpec, ih]

theorem checkCtorAlts_eq (env : Lean.Environment) (ind : Name) (cs : List Name)
    (alts : List Lean.Expr) :
    Regula.Load.checkCtorAlts env ind cs alts = checkCtorAltsSpec env ind cs alts := by
  induction cs generalizing alts with
  | nil => cases alts <;> rfl
  | cons c cs ih =>
    cases alts with
    | nil => rfl
    | cons a alts =>
      simp only [Regula.Load.checkCtorAlts, checkCtorAltsSpec, stripLams_eq, ih]
      rfl

theorem isCtorIdxDef_eq (env : Lean.Environment) (ind : Name) (indInfo : Lean.InductiveVal)
    (d : Lean.DefinitionVal) :
    Regula.Load.isCtorIdxDef env ind indInfo d = ctorIdxDefShape env ind indInfo d := by
  simp only [Regula.Load.isCtorIdxDef, ctorIdxDefShape, runtimeBuiltinTypes_eq,
    stripForalls_eq, stripLamMatchingForall_eq, mkBVarApps_eq, unappGo_eq, bvarList_eq,
    stripLams_eq, checkCtorAlts_eq]
  rfl

theorem isCtorIdxImpl_eq (ind : Name) (indInfo : Lean.InductiveVal)
    (dDef d : Lean.DefinitionVal) :
    Regula.Load.isCtorIdxImpl ind indInfo dDef d = ctorIdxImplShape ind indInfo dDef d := by
  simp only [Regula.Load.isCtorIdxImpl, ctorIdxImplShape, runtimeBuiltinTypes_eq,
    stripForalls_eq, stripLamMatchingForall_eq, mkBVarApps_eq]
  rfl

theorem ctorIdxFormOf_eq_shape (env : Lean.Environment) (n : Name) (info : ConstantInfo) :
    Link.ctorIdxForm (Regula.Load.ctorIdxFormOf env n info) = ctorIdxShape env n info := by
  unfold Regula.Load.ctorIdxFormOf ctorIdxShape
  split
  · split <;> simp_all [isCtorIdxImpl_eq]
    · split <;> rfl
    · rfl
  · split <;> simp_all [isCtorIdxDef_eq]
    · split <;> rfl
    · rfl
  · split <;> simp_all [Link.ctorIdxForm]

theorem ctorIdxForm_inj {a b : Regula.Closed.CtorIdxForm} :
    Link.ctorIdxForm a = Link.ctorIdxForm b ↔ a = b := by
  cases a <;> cases b <;> simp [Link.ctorIdxForm]

theorem ctorIdxFormOf_eq_iff (env : Lean.Environment) (n : Name) (k v : ConstantInfo) :
    Regula.Load.ctorIdxFormOf env n k = Regula.Load.ctorIdxFormOf env n v ↔
      ctorIdxShape env n k = ctorIdxShape env n v := by
  rw [← ctorIdxForm_inj, ctorIdxFormOf_eq_shape, ctorIdxFormOf_eq_shape]

/-- The compiler-generated {lit}`T.ctorIdx` / {lit}`T.ctorIdx._impl` pair for safe inductive
{name}`ind` in module {name}`m`, stated in the terms of the loaded environment. -/
def EnvCtorIdxPair (f : Regula.Load.Facts) (ind : Name) (defv implv : Lean.DefinitionVal)
    (m : Name) : Prop :=
  let defName := Name.str ind "ctorIdx"
  let implName := Name.str defName "_impl"
  (∃ k, f.env.constants.map₁[`getObjTagNat]? = some k) ∧ EnvToolchain f `getObjTagNat ∧
  (∃ indv, f.env.constants.map₁[ind]? = some (.inductInfo indv) ∧
    (∀ w ∈ f.stated.getD ind [], ¬ AxiomInfo w) ∧
    f.moduleOf? ind = some m ∧ (ConstantInfo.inductInfo indv).isUnsafe = false ∧
    (ConstantInfo.inductInfo indv).isPartial = false) ∧
  f.env.constants.map₁[defName]? = some (.defnInfo defv) ∧
  (∀ w ∈ f.stated.getD defName [], ¬ AxiomInfo w) ∧
  f.moduleOf? defName = some m ∧
  (ConstantInfo.defnInfo defv).isUnsafe = false ∧
  (ConstantInfo.defnInfo defv).isPartial = false ∧
  ctorIdxShape f.env defName (.defnInfo defv) = .defn ind ∧
  Lean.Compiler.getImplementedBy? f.env defName = some implName ∧
  Lean.isExtern f.env defName = false ∧
  Lean.getInitFnNameFor? f.env defName = none ∧
  f.env.constants.map₁[implName]? = some (.defnInfo implv) ∧
  (∀ w ∈ f.stated.getD implName [], ¬ AxiomInfo w) ∧
  f.moduleOf? implName = some m ∧
  (ConstantInfo.defnInfo implv).isUnsafe = true ∧
  ctorIdxShape f.env implName (.defnInfo implv) = .impl ind ∧
  Lean.Compiler.getImplementedBy? f.env implName = none ∧
  Lean.isExtern f.env implName = false ∧
  Lean.getInitFnNameFor? f.env implName = none

/-- The safe half {lit}`T.ctorIdx` of a compiler-generated {lit}`ctorIdx` pair in the loaded
environment. -/
def EnvCtorIdxDef (f : Regula.Load.Facts) (n : Name) (info : ConstantInfo) (m : Name) : Prop :=
  ∃ ind defv implv, n = Name.str ind "ctorIdx" ∧ info = .defnInfo defv ∧
    EnvCtorIdxPair f ind defv implv m

/-- The unsafe half {lit}`T.ctorIdx._impl` of a compiler-generated {lit}`ctorIdx` pair in the
loaded environment. -/
def EnvCtorIdxImpl (f : Regula.Load.Facts) (n : Name) (info : ConstantInfo) (m : Name) : Prop :=
  ∃ ind defv implv, n = Name.str (Name.str ind "ctorIdx") "_impl" ∧ info = .defnInfo implv ∧
    EnvCtorIdxPair f ind defv implv m

/-- The environment holds {name}`u` as a theorem: the constant that it keeps is one, and no loaded module
states an axiom of that name. -/
def EnvTheorem (f : Regula.Load.Facts) (u : Name) : Prop :=
  ∃ v, f.env.constants.map₁[u]? = some (.thmInfo v) ∧ ∀ w ∈ f.stated.getD u [], ¬ AxiomInfo w

/-- {name}`u` is a panic form in the terms of the environment: one of Lean's four panic functions, or a name
that {name}`BangNamed` admits and that the environment does not hold as a theorem. -/
def EnvPanic (f : Regula.Load.Facts) (u : Name) : Prop :=
  u ∈ panicFunctions ∨ (BangNamed u ∧ ¬ EnvTheorem f u)

/-- The module {name}`m` of the environment is a {lit}`module` file: the data that the environment holds of its
{lit}`.olean` says so ({name (full := Lean.ModuleData.isModule)}`ModuleData.isModule`). It names no function of the
checker. -/
def EnvModuleFile (env : Lean.Environment) (m : Name) : Prop :=
  ∃ (k : Nat) (data : Lean.ModuleData), env.header.moduleNames[k]? = some m ∧
    env.header.moduleData[k]? = some data ∧ data.isModule = true

/-- An exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entry of module {name}`m` in {name}`env`
names the theorem {name}`thm`. -/
def ModuleCSimp (env : Lean.Environment) (m thm : Name) : Prop :=
  ∃ idx, env.getModuleIdx? m = some idx ∧
    ∃ e : Lean.Compiler.CSimp.Entry,
      (Lean.ScopedEnvExtension.Entry.global e ∈ Lean.Compiler.CSimp.ext.ext.getModuleEntries env idx ∨
        ∃ ns, Lean.ScopedEnvExtension.Entry.scoped ns e ∈ Lean.Compiler.CSimp.ext.ext.getModuleEntries env idx) ∧
      e.thmName = thm

/-- Module {name}`m` has an index in {name}`env`, and each theorem that an exported {attr}`@[csimp]` entry
of {name}`m` names ({name}`ModuleCSimp`) meets {name}`Claimed`. A missing module index is never treated as
empty entries. -/
def ModuleCSimpIn (env : Lean.Environment) (Claimed : Name → Prop) (m : Name) : Prop :=
  (∃ idx, env.getModuleIdx? m = some idx) ∧ ∀ thm, ModuleCSimp env m thm → Claimed thm

/-- What the rules state, in the terms of the environment. Each claimed module is a {lit}`module` file (RG1013),
and has a module index whose exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entries each name a
constant declared in some claimed module's own {lit}`.olean` data (RG1011, with a missing index refused as
RG2001). And what RG1001 to RG1006, RG1011 and RG1012 state of each constant of a claimed module: no loaded
module states an axiom of its name (RG1001). When it is unsafe or partial, or
has a recursion helper's name, it has an exempted form ({name}`EnvHelper` or {name}`EnvCtorIdxImpl`, RG1006),
its value mentions no loop construct of Lean (RG1006), and, when it is a definition or an opaque constant,
its value does not mention {name}`Lean.Order.fix` (RG1006). Each axiom that it reaches, through what any loaded
module's own
data states, is one that the profile admits (RG1005), which also excludes {name}`sorryAx` (RG1002), a
native proof's axiom (RG1004) and every other axiom (RG1003): {name}`rg1005_of_hole`,
{name}`rg1005_of_compiler`, {name}`rg1005_of_unknown`. The environment gives it no constant by
{attr}`@[implemented_by]` (unless it is the safe half of a verified {lit}`ctorIdx` pair,
{name}`EnvCtorIdxDef`), does not mark it {attr}`@[extern]` and, when it is a definition, names no
initialization function for it (RG1011). When it is a definition or an
opaque constant, its value mentions no panic form (RG1012). -/
def EnvFloor (f : Regula.Load.Facts) (p : Regula.Closed.Profile) : Prop :=
  (∀ m ∈ f.claimed, EnvModuleFile f.env m) ∧
  (∀ m ∈ f.claimed, ModuleCSimpIn f.env (fun thm => ∃ cm info, (cm, thm, info) ∈ f.claimedConstants) m) ∧
  ∀ n info m, f.env.constants.map₁[n]? = some info → f.moduleOf? n = some m → m ∈ f.claimed →
    ¬ EnvAxiom f n ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
      EnvHelper f n info m ∨ EnvCtorIdxImpl f n info m) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ¬ ValueMentions info ``Lean.Order.fix) ∧
    (∀ a, EnvReaches f n a → EnvAxiom f a → EnvAdmits f p a) ∧
    (Lean.Compiler.getImplementedBy? f.env n = none ∨ EnvCtorIdxDef f n info m) ∧
    Lean.isExtern f.env n = false ∧
    ((∃ v, info = .defnInfo v) → Lean.getInitFnNameFor? f.env n = none) ∧
    ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ∀ u, ValueMentions info u → ¬ EnvPanic f u)

/-- The module's own attribute entries contain neither replacement attribute for this name,
including when another module's constant has the same name. -/
def ModuleUnreplaced (env : Lean.Environment) (m n : Name) : Prop :=
  ∃ idx, env.getModuleIdx? m = some idx ∧
    (∀ entry ∈ Lean.Compiler.implementedByAttr.ext.getModuleEntries env idx, entry.1 ≠ n) ∧
    (∀ entry ∈ Lean.externAttr.ext.getModuleEntries env idx, entry.1 ≠ n)

theorem unreplaced_iff (m n : Name) :
    f.unreplaced m n = true ↔ ModuleUnreplaced f.env m n := by
  unfold Regula.Load.Facts.unreplaced ModuleUnreplaced
  cases f.env.getModuleIdx? m <;>
    simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, Bool.false_eq_true,
      exists_eq_left', Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, bne_iff_ne]

/-- Module {name}`m`'s own replacement entries for {name}`n` are solely the compiler-generated
{lit}`(n, n._impl)` entry for a constant whose expression has shape {lit}`CtorIdxForm.defn`,
with no {attr}`@[extern]` entry and no other {attr}`@[implemented_by]` entry. -/
def ModuleCtorIdxEntryOnly (env : Lean.Environment) (m n : Name) (info : ConstantInfo) : Prop :=
  (∃ ind, ctorIdxShape env n info = .defn ind) ∧
  ∃ idx, env.getModuleIdx? m = some idx ∧
    (∀ entry ∈ Lean.Compiler.implementedByAttr.ext.getModuleEntries env idx,
      entry.1 = n → entry.2 = .str n "_impl") ∧
    (∀ entry ∈ Lean.externAttr.ext.getModuleEntries env idx, entry.1 ≠ n)

theorem ctorIdxEntryOnly_iff (m n : Name) (info : ConstantInfo) :
    f.ctorIdxEntryOnly m n info = true ↔ ModuleCtorIdxEntryOnly f.env m n info := by
  unfold Regula.Load.Facts.ctorIdxEntryOnly ModuleCtorIdxEntryOnly
  rw [← ctorIdxFormOf_eq_shape]
  have hor : ∀ e : Name × Name, (e.1 ≠ n ∨ e.2 = .str n "_impl") ↔ (e.1 = n → e.2 = .str n "_impl") :=
    fun _ => Decidable.imp_iff_not_or.symm
  cases Regula.Load.ctorIdxFormOf f.env n info with
  | none | impl _ => simp [Link.ctorIdxForm]
  | defn ind =>
    cases f.env.getModuleIdx? m with
    | none => simp [Link.ctorIdxForm]
    | some idx =>
      simp only [Link.ctorIdxForm, CtorIdxForm.defn.injEq, exists_eq', true_and,
        Option.some.injEq, exists_eq_left', Bool.and_eq_true,
        Array.all_eq_true_iff_forall_mem, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, hor]

/-- The module's own entries of {attr}`@[init]` and {attr}`@[builtin_init]` name no initialization function
for this name: each of its entries for the name holds the anonymous name, the form that names none. -/
def ModuleUninitialized (env : Lean.Environment) (m n : Name) : Prop :=
  ∃ idx, env.getModuleIdx? m = some idx ∧
    (∀ entry ∈ Lean.regularInitAttr.ext.getModuleEntries env idx, entry.1 = n → entry.2 = .anonymous) ∧
    (∀ entry ∈ Lean.builtinInitAttr.ext.getModuleEntries env idx, entry.1 = n → entry.2 = .anonymous)

theorem uninitialized_iff (m n : Name) :
    f.uninitialized m n = true ↔ ModuleUninitialized f.env m n := by
  unfold Regula.Load.Facts.uninitialized ModuleUninitialized
  have hor : ∀ e : Name × Name, (e.1 ≠ n ∨ e.2 = .anonymous) ↔ (e.1 = n → e.2 = .anonymous) :=
    fun _ => Decidable.imp_iff_not_or.symm
  cases f.env.getModuleIdx? m <;>
    simp only [Option.some.injEq, reduceCtorEq, false_and, exists_false, Bool.false_eq_true,
      exists_eq_left', Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Bool.or_eq_true,
      bne_iff_ne, beq_iff_eq, hor]

theorem kindOf_definition (k : ConstantInfo) : Regula.Load.kindOf k = .definition ↔ ∃ v, k = .defnInfo v := by
  cases k with | defnInfo v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩ | _ => exact ⟨(fun h => by cases h), (by rintro ⟨_, h⟩; cases h)⟩

theorem mem_modules_of_getElem {k : Nat} {m : Regula.Load.LoadedModule}
    (h : f.modules[k]? = some m) : m ∈ f.modules :=
  Array.mem_of_getElem? h

theorem mem_modules_of_info {n : Name} {m : Regula.Load.LoadedModule} (h : f.info? n = some m) :
    m ∈ f.modules := by
  obtain ⟨_, _, hm⟩ := Option.bind_eq_some_iff.mp h; exact mem_modules_of_getElem hm

theorem moduleNames_getElem (f : Regula.Load.Facts) (k : Nat) :
    (f.modules[k]?).map (·.name) = f.env.header.moduleNames[k]? := by
  have h := congrArg (·[k]?) f.names; simp only [List.getElem?_map, Array.getElem?_toList] at h; exact h

theorem moduleOf?_eq (f : Regula.Load.Facts) (n : Name) :
    f.moduleOf? n =
      (f.env.getModuleIdxFor? n).bind fun idx => f.env.header.moduleNames[idx.toNat]? := by
  simp only [Regula.Load.Facts.moduleOf?, Regula.Load.Facts.info?]
  cases f.env.getModuleIdxFor? n with | none => rfl | some idx => exact moduleNames_getElem f idx.toNat

theorem mem_claimed_iff (f : Regula.Load.Facts) (m : Name) :
    m ∈ f.claimed ↔ ∃ lm ∈ f.modules, lm.name = m ∧ lm.claimed = true := by
  simp only [Regula.Load.Facts.claimed, List.mem_map, List.mem_filter, Array.mem_toList_iff]
  exact ⟨by rintro ⟨lm, ⟨hm, hc⟩, h⟩; exact ⟨lm, hm, h, hc⟩, by rintro ⟨lm, hm, h, hc⟩; exact ⟨lm, ⟨hm, hc⟩, h⟩⟩

theorem claimed_loaded (f : Regula.Load.Facts) {m : Name} (h : m ∈ f.claimed) :
    m ∈ f.env.header.moduleNames.toList := by
  obtain ⟨lm, hm, rfl, -⟩ := (mem_claimed_iff f m).mp h
  exact f.names ▸ List.mem_map_of_mem (Array.mem_toList_iff.mpr hm)

theorem mem_claimed_place (f : Regula.Load.Facts) (m : Name) :
    m ∈ f.claimed ↔
      ∃ lm ∈ f.modules, lm.name = m ∧ Regula.Load.below f.rootDir lm.olean = true := by
  rw [mem_claimed_iff]
  exact exists_congr fun lm => and_congr_right fun hm => by
    rw [congrArg Regula.Load.LoadedModule.claimed (f.placed lm hm)]; rfl

theorem toolchain_place (f : Regula.Load.Facts) (n : Name) :
    EnvToolchain f n ↔
      ∃ (idx : Lean.ModuleIdx) (lm : Regula.Load.LoadedModule),
        f.env.getModuleIdxFor? n = some idx ∧ f.modules[idx.toNat]? = some lm ∧
          Regula.Load.below f.toolchainDir lm.olean = true := by
  have hflag {lm} (hm : lm ∈ f.modules) : lm.inToolchain = Regula.Load.below f.toolchainDir lm.olean :=
    congrArg (·.inToolchain) (f.placed lm hm)
  simp only [EnvToolchain, Regula.Load.Facts.info?, Option.bind_eq_some_iff]
  exact ⟨by rintro ⟨lm, ⟨idx, hi, hm⟩, ht⟩; exact ⟨idx, lm, hi, hm, hflag (mem_modules_of_getElem hm) ▸ ht⟩,
    by rintro ⟨idx, lm, hi, hm, ht⟩; exact ⟨lm, ⟨idx, hi, hm⟩, (hflag (mem_modules_of_getElem hm)).symm ▸ ht⟩⟩

theorem not_unsafe_of_partial (info : ConstantInfo) (h : info.isPartial = true) :
    info.isUnsafe = false := by
  cases info with
  | defnInfo v => simp only [ConstantInfo.isPartial, ConstantInfo.isUnsafe] at h ⊢; revert h; cases v.safety <;> decide
  | _ => cases h

theorem safetyOf_partial (info : ConstantInfo) :
    Regula.Load.safetyOf info = .partial ↔ info.isPartial = true ∧ info.isUnsafe = false := by
  unfold Regula.Load.safetyOf; cases info.isUnsafe <;> cases info.isPartial <;> decide

theorem safetyOf_safe (info : ConstantInfo) :
    Regula.Load.safetyOf info = .safe ↔ info.isUnsafe = false ∧ info.isPartial = false := by
  unfold Regula.Load.safetyOf; cases info.isUnsafe <;> cases info.isPartial <;> decide

theorem safetyOf_unsafe (info : ConstantInfo) :
    Regula.Load.safetyOf info = .unsafe ↔ info.isUnsafe = true := by
  unfold Regula.Load.safetyOf; cases info.isUnsafe <;> cases info.isPartial <;> decide

/-- What the loader gives, in the terms of the environment. -/
structure Loaded (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile)
    (i : Regula.Closed.Input) : Prop where
  /-- The profile is the one that the shell read. -/
  profile : i.profile = p
  /-- The claimed modules are those of the facts. -/
  modules : i.modules = f.claimed
  /-- The modules that are {lit}`module` files are those of the facts. -/
  moduleFiles : i.moduleFiles = f.moduleFiles
  /-- Every claimed module has an index in the loaded environment. -/
  indexed : ∀ m ∈ f.claimed, ∃ idx, f.env.getModuleIdx? m = some idx
  /-- Of the names that the exported {attr}`@[csimp]` entries give, the input holds those that
  {name (full := Regula.Load.Facts.claimedConstants)}`Facts.claimedConstants` lists for a claimed module. -/
  claimedConstants : ∀ c, c ∈ i.claimedConstants ↔
    (∃ e ∈ i.csimps, e.thm = c) ∧ ∃ cm info, (cm, c, info) ∈ f.claimedConstants
  /-- The exported ({lit}`global` or {lit}`scoped`) {attr}`@[csimp]` entries are exactly those of the claimed modules. -/
  csimps : ∀ e, e ∈ i.csimps ↔ e.module ∈ f.claimed ∧ ModuleCSimp f.env e.module e.thm
  /-- Each module of {name}`roots` is claimed. -/
  roots : ∀ r ∈ roots, r ∈ f.claimed
  /-- Each constant of the input is a constant of the environment, with the fields it gives. -/
  sound : ∀ d ∈ i.decls, ∃ info m, f.env.constants.map₁[d.name]? = some info ∧
    f.info? d.name = some m ∧ d = f.declIn d.name m info (f.stated.getD d.name [])
  /-- Each constant of the environment is in the input. -/
  whole : ∀ n info, f.env.constants.map₁[n]? = some info →
    ∃ m, f.info? n = some m ∧ f.declIn n m info (f.stated.getD n []) ∈ i.decls

theorem moduleCSimps_ok {m : Name} {entries : List Regula.Closed.CSimpEntry}
    (h : f.moduleCSimps m = .ok entries) :
    (∃ idx, f.env.getModuleIdx? m = some idx) ∧
      ∀ e, e ∈ entries ↔ e.module = m ∧ ModuleCSimp f.env m e.thm := by
  unfold Regula.Load.Facts.moduleCSimps at h
  cases hidx : f.env.getModuleIdx? m with
  | none => rw [hidx] at h; cases h
  | some idx =>
    simp only [hidx, Except.ok.injEq] at h; subst h
    refine ⟨⟨idx, rfl⟩, fun e => ?_⟩
    simp only [List.mem_map, Array.mem_toList_iff, ModuleCSimp, hidx, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨raw, hraw, rfl⟩; cases raw with
      | global ce => exact ⟨rfl, ce, .inl hraw, rfl⟩ | «scoped» ns ce => exact ⟨rfl, ce, .inr ⟨ns, hraw⟩, rfl⟩
    · rintro ⟨hm, ce, hg | ⟨ns, hs⟩, hthm⟩ <;> (cases e; cases hm; cases hthm)
      · exact ⟨.global ce, hg, rfl⟩
      · exact ⟨.«scoped» ns ce, hs, rfl⟩

theorem csimps_ok {claimed : List Name} {entries : List Regula.Closed.CSimpEntry}
    (h : f.csimps claimed = .ok entries) :
    (∀ m ∈ claimed, ∃ idx, f.env.getModuleIdx? m = some idx) ∧
      ∀ e, e ∈ entries ↔ e.module ∈ claimed ∧ ModuleCSimp f.env e.module e.thm := by
  unfold Regula.Load.Facts.csimps at h
  cases hmap : claimed.mapM f.moduleCSimps with
  | error _ => rw [hmap] at h; cases h
  | ok lists =>
    simp only [hmap, Except.map, Except.ok.injEq] at h; subst h
    obtain ⟨h1, h2, -⟩ := Regula.Load.mapM_ok f.moduleCSimps (fun _ => .anonymous) (fun _ => .anonymous)
      (fun _ _ _ => rfl) _ _ hmap
    refine ⟨fun m hm => by obtain ⟨_, _, hok⟩ := h2 m hm; exact (moduleCSimps_ok hok).1, fun e => ?_⟩
    simp only [List.mem_flatten]
    exact ⟨by rintro ⟨l, hl, he⟩; obtain ⟨m, hm, hok⟩ := h1 l hl; obtain ⟨rfl, hcs⟩ := ((moduleCSimps_ok hok).2 e).mp he; exact ⟨hm, hcs⟩,
      by rintro ⟨hm, hcs⟩; obtain ⟨l, hl, hok⟩ := h2 e.module hm; exact ⟨l, hl, ((moduleCSimps_ok hok).2 e).mpr ⟨rfl, hcs⟩⟩⟩

theorem mem_claimedTargetsFold (targets : Std.HashSet Name)
    (l : List (Name × Name × ConstantInfo)) (acc : Std.HashSet Name) (n : Name) :
    n ∈ l.foldl (fun s x => if targets.contains x.2.1 then s.insert x.2.1 else s) acc ↔
      n ∈ acc ∨ (targets.contains n = true ∧ ∃ x ∈ l, x.2.1 = n) := by
  induction l generalizing acc with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, false_and, exists_false, and_false, or_false]
  | cons a l ih =>
    simp only [List.foldl_cons, ih, List.mem_cons, exists_eq_or_imp]
    by_cases ht : targets.contains a.2.1 = true
    · simp only [ht, ↓reduceIte, Std.HashSet.mem_insert, beq_iff_eq]
      exact ⟨by rintro ((rfl | ha) | ⟨htn, hx⟩); exact .inr ⟨ht, .inl rfl⟩; exact .inl ha; exact .inr ⟨htn, .inr hx⟩,
        by rintro (ha | ⟨htn, rfl | hx⟩); exact .inl (.inr ha); exact .inl (.inl rfl); exact .inr ⟨htn, hx⟩⟩
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun h => h.imp id fun h => ⟨h.1, .inr h.2⟩,
        fun h => h.imp id fun h => ⟨h.1, h.2.elim (fun he => (ht (he ▸ h.1)).elim) id⟩⟩

theorem mem_claimedCSimpTargets (csimps : List Regula.Closed.CSimpEntry) (c : Name) :
    c ∈ f.claimedCSimpTargets csimps ↔
      (∃ e ∈ csimps, e.thm = c) ∧ ∃ cm info, (cm, c, info) ∈ f.claimedConstants := by
  cases csimps with
  | nil => simp only [Regula.Load.Facts.claimedCSimpTargets, List.isEmpty_nil, ↓reduceIte, List.not_mem_nil, false_and, exists_false]
  | cons e0 es =>
    simp only [Regula.Load.Facts.claimedCSimpTargets, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [Std.HashSet.mem_toList, mem_claimedTargetsFold, Regula.Closed.mem_setOf]
    simp only [Std.HashSet.not_mem_empty, false_or, List.mem_map]
    exact ⟨by rintro ⟨he, ⟨cm, _, info⟩, hm, h⟩; exact ⟨he, cm, info, h ▸ hm⟩,
      by rintro ⟨he, cm, info, hm⟩; exact ⟨he, (cm, c, info), hm, rfl⟩⟩

theorem decl_ok {n : Name} {info : ConstantInfo} {s : List ConstantInfo} {d : Regula.Closed.Decl}
    (h : f.decl n info s = .ok d) : ∃ m, f.info? n = some m ∧ d = f.declIn n m info s := by
  simp only [Regula.Load.Facts.decl] at h; split at h <;> cases h; exact ⟨_, ‹_›, rfl⟩

theorem shown_true {x : Name × Name × ConstantInfo} (h : f.shown x = true) :
    ∃ k m, f.env.constants.map₁[x.2.1]? = some k ∧
      Regula.Load.readOf f.env x.2.1 k = Regula.Load.readOf f.env x.2.1 x.2.2 ∧
      f.info? x.2.1 = some m ∧ m.claimed = true := by
  simp only [Regula.Load.Facts.shown] at h; split at h <;> try cases h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨_, _, ‹_›, h.1.1.1, ‹_›, h.1.1.2⟩

theorem shown_unreplaced {x : Name × Name × ConstantInfo} {k : ConstantInfo}
    (h : f.shown x = true) (hk : f.env.constants.map₁[x.2.1]? = some k)
    (hi : Lean.Compiler.getImplementedBy? f.env x.2.1 = none ∨
      (∃ ind, ctorIdxShape f.env x.2.1 k = .defn ind ∧
        Lean.Compiler.getImplementedBy? f.env x.2.1 = some (Name.str x.2.1 "_impl")))
    (he : Lean.isExtern f.env x.2.1 = false) :
    ModuleUnreplaced f.env x.1 x.2.1 ∨ ModuleCtorIdxEntryOnly f.env x.1 x.2.1 x.2.2 := by
  simp only [Regula.Load.Facts.shown, hk] at h
  cases hm : f.info? x.2.1 with
  | none => simp [hm] at h
  | some lm =>
    simp only [hm, Bool.and_eq_true, Bool.or_eq_true, he, Bool.false_eq_true, or_false] at h
    rcases h.1.2 with (hu | hc) | hmatch
    · exact .inl ((unreplaced_iff _ _).mp hu)
    · exact .inr ((ctorIdxEntryOnly_iff _ _ _).mp hc)
    · exfalso
      rcases hi with hnone | ⟨ind, hshape, hsome⟩
      · simp [hnone] at hmatch
      · have hform : Regula.Load.ctorIdxFormOf f.env x.2.1 k = .defn ind := by
          have h1 := ctorIdxFormOf_eq_shape f.env x.2.1 k
          rw [hshape] at h1
          exact ctorIdxForm_inj.mp h1
        simp [hsome, hform] at hmatch

theorem shown_uninitialized {x : Name × Name × ConstantInfo} (h : f.shown x = true)
    (hk : Regula.Load.kindOf x.2.2 = .definition)
    (hn : Lean.getInitFnNameFor? f.env x.2.1 = none) : ModuleUninitialized f.env x.1 x.2.1 := by
  simp only [Regula.Load.Facts.shown] at h; split at h <;> try cases h
  simp only [Bool.and_eq_true] at h; exact (uninitialized_iff _ _).mp (by simpa [hk, hn] using h.2)

theorem unread_none {x : Name × Name × ConstantInfo} (h : f.unread? i.tables = none)
    (hx : x ∈ f.claimedConstants) :
    f.shown x = true ∨ Regula.Load.fitsUnshown f i.tables x.1 x.2.1 x.2.2 = true := by
  by_cases hs : f.shown x = true
  · exact .inl hs
  · simp only [Regula.Load.Facts.unread?, Regula.Load.Facts.unshown, Option.map_eq_none_iff, List.find?_eq_none] at h
    exact .inr (by simpa using h x (by simp [hx, hs]))

theorem loaded_of_parts {csimps : List Regula.Closed.CSimpEntry} {decls : List Regula.Closed.Decl}
    {i' : Regula.Closed.Input}
    (hfind : roots.find? (fun x => !f.claimed.contains x) = none)
    (hcs : f.csimps f.claimed = .ok csimps)
    (hm : f.env.constants.map₁.toList.mapM
      (fun x => f.decl x.1 x.2 (f.stated.getD x.1 [])) = .ok decls)
    {unique : (decls.map (·.name)).Nodup}
    (hadmit : ({ profile := p, modules := f.claimed, moduleFiles := f.moduleFiles,
                 claimedConstants := f.claimedCSimpTargets csimps,
                 csimps, decls, unique } :
      Regula.Closed.Draft).admit = .ok i') :
    Loaded f roots p i' := by
  have hd := admit_toDraft hadmit
  obtain ⟨h1, h2, -⟩ := Regula.Load.mapM_ok
    (fun x : Name × ConstantInfo => f.decl x.1 x.2 (f.stated.getD x.1 []))
    (·.name) (·.1) (fun _ _ hb => f.decl_name hb) _ _ hm
  obtain ⟨hidx, hcs'⟩ := csimps_ok hcs
  have hdecls : i'.decls = decls := by rw [hd]
  refine ⟨by rw [hd], by rw [hd], by rw [hd], hidx,
    fun c => by rw [hd]; exact mem_claimedCSimpTargets csimps c,
    fun e => by rw [hd]; exact hcs' e,
    fun r hr => by simpa using List.find?_eq_none.mp hfind r hr, ?_, ?_⟩
  · intro d hd'
    obtain ⟨⟨n, info⟩, hx, hok⟩ := h1 d (hdecls ▸ hd')
    obtain ⟨m, hmod, hdv⟩ := decl_ok hok
    obtain rfl := f.decl_name hok
    exact ⟨info, m, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx, hmod, hdv⟩
  · intro n info hn
    obtain ⟨d, hd', hok⟩ := h2 (n, info) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hn)
    obtain ⟨m, hmod, hdv⟩ := decl_ok hok
    exact ⟨m, hmod, hdecls.symm ▸ hdv ▸ hd'⟩

theorem input_eq_ok_iff :
    f.input roots p = .ok i ↔ ∃ prep, f.prepare roots p = .ok prep ∧ prep.input = i := by
  rw [Regula.Load.Facts.input_eq_prepare_map]
  cases f.prepare roots p <;> simp [Except.map]

theorem admitDraft_loaded {i' : Regula.Closed.Input} (h : f.admitDraft roots p = .ok i') :
    Loaded f roots p i' := by
  simp only [Regula.Load.Facts.admitDraft] at h
  (split at h <;> try cases h); (split at h <;> try cases h); (split at h <;> try cases h)
  exact loaded_of_parts ‹_› ‹_› ‹_› h

theorem prepare_loaded {prep : Regula.Closed.Prepared} (h : f.prepare roots p = .ok prep) :
    Loaded f roots p prep.input := by
  simp only [Regula.Load.Facts.prepare] at h
  (split at h <;> try cases h); (split at h <;> try cases h)
  exact admitDraft_loaded ‹_›

theorem input_loaded (h : f.input roots p = .ok i) : Loaded f roots p i := by
  obtain ⟨prep, hprep, rfl⟩ := input_eq_ok_iff.mp h
  exact prepare_loaded hprep

theorem input_kept (h : f.input roots p = .ok i) {x : Name × Name × ConstantInfo}
    (hx : x ∈ f.claimedConstants) :
    f.shown x = true ∨ Regula.Load.fitsUnshown f i.tables x.1 x.2.1 x.2.2 = true := by
  obtain ⟨prep, hprep, rfl⟩ := input_eq_ok_iff.mp h
  simp only [Regula.Load.Facts.prepare] at hprep
  (split at hprep <;> try cases hprep); (split at hprep <;> try cases hprep)
  rename_i hc; simp only [Regula.Load.Facts.checkUnread] at hc
  (split at hc <;> try cases hc); exact unread_none ‹_› hx

theorem claimed_iff (hl : Loaded f roots p i) (m : Name) :
    (toSpec i).ClaimedModule m ↔ m ∈ f.claimed := by
  simp [Input.ClaimedModule, toSpec, toSpecDraft, hl.modules]

theorem mem_moduleFiles (f : Regula.Load.Facts) (m : Name) : m ∈ f.moduleFiles ↔ EnvModuleFile f.env m := by
  simp only [Regula.Load.Facts.moduleFiles, List.mem_map, List.mem_filter, Array.mem_toList_iff,
    Array.mem_iff_getElem?, Array.getElem?_zip_eq_some, EnvModuleFile]
  exact ⟨by rintro ⟨⟨lm, data⟩, ⟨⟨k, h1, h2⟩, hmod⟩, rfl⟩; exact ⟨k, data, by rw [← moduleNames_getElem, h1]; rfl, h2, hmod⟩,
    by rintro ⟨k, data, hname, h2, hmod⟩; rw [← moduleNames_getElem] at hname
       obtain ⟨lm, h1, rfl⟩ := Option.map_eq_some_iff.mp hname; exact ⟨(lm, data), ⟨⟨k, h1, h2⟩, hmod⟩, rfl⟩⟩

theorem moduleFile_env (hl : Loaded f roots p i) (m : Name) :
    (toSpec i).ModuleFile m ↔ EnvModuleFile f.env m := by
  rw [← mem_moduleFiles]; simp only [Input.ModuleFile, toSpec, toSpecDraft, hl.moduleFiles]

theorem of_mem {x : Decl} (hl : Loaded f roots p i) (hx : x ∈ (toSpec i).decls) :
    ∃ info m, f.env.constants.map₁[x.name]? = some info ∧ f.info? x.name = some m ∧
      x = decl (f.declIn x.name m info (f.stated.getD x.name [])) := by
  obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx
  obtain ⟨info, m, hn, hm, hv⟩ := hl.sound d hd
  exact ⟨info, m, hn, hm, congrArg decl hv⟩

theorem to_mem (hl : Loaded f roots p i) {n : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) {m : Regula.Load.LoadedModule}
    (hm : f.info? n = some m) :
    decl (f.declIn n m info (f.stated.getD n [])) ∈ (toSpec i).decls := by
  obtain ⟨_, hm', hmem⟩ := hl.whole n info hn
  rw [hm] at hm'; cases hm'; exact mem_decls.mpr ⟨_, hmem, rfl⟩

theorem module_of (hl : Loaded f roots p i) {n : Name} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) : ∃ m, f.info? n = some m := by
  obtain ⟨m, hm, _⟩ := hl.whole n info hn; exact ⟨m, hm⟩

theorem moduleOf?_eq_some {n m : Name} :
    f.moduleOf? n = some m ↔ ∃ lm, f.info? n = some lm ∧ lm.name = m := by
  simp only [Regula.Load.Facts.moduleOf?, Option.map_eq_some_iff]

private theorem exists_decl_env (hl : Loaded f roots p i) (u : Name) (P : Decl → Prop) :
    (∃ x ∈ (toSpec i).decls, x.name = u ∧ P x) ↔
      ∃ info m, f.env.constants.map₁[u]? = some info ∧ f.info? u = some m ∧
        P (decl (f.declIn u m info (f.stated.getD u []))) :=
  ⟨by rintro ⟨_, hx, rfl, hp⟩; obtain ⟨info, m, hn, hm, hv⟩ := of_mem hl hx; exact ⟨info, m, hn, hm, hv ▸ hp⟩,
   by rintro ⟨_, _, hn, hm, hp⟩; exact ⟨_, to_mem hl hn hm, rfl, hp⟩⟩

theorem resolves_env (hl : Loaded f roots p i) (u : Name) :
    (toSpec i).Resolves u ↔ ∃ info, f.env.constants.map₁[u]? = some info :=
  ⟨by rintro ⟨_, hx, rfl⟩; obtain ⟨info, _, hn, _, _⟩ := of_mem hl hx; exact ⟨info, hn⟩,
   by rintro ⟨_, hn⟩; obtain ⟨m, hm⟩ := module_of hl hn; exact ⟨_, to_mem hl hn hm, rfl⟩⟩

theorem reaches_env (hl : Loaded f roots p i) (c e : Name) :
    (toSpec i).Reaches c e ↔ EnvReaches f c e :=
  ⟨fun h => by
    induction h with
    | refl => exact .refl _
    | step x hx hc hu _ ih =>
      subst hc; obtain ⟨info, _, hn, -, hv⟩ := of_mem hl hx
      exact .step ⟨info, hn, (mem_usesIn info _ _).mp (hv ▸ hu)⟩ ih,
   fun h => by
    induction h with
    | refl => exact .refl _
    | step hm _ ih =>
      obtain ⟨info, hn, hu⟩ := hm; obtain ⟨m, hmod⟩ := module_of hl hn
      exact .step _ (to_mem hl hn hmod) rfl ((mem_usesIn info _ _).mpr hu) ih⟩

theorem kindOf_axiom (k : ConstantInfo) : Regula.Load.kindOf k = .axiom ↔ AxiomInfo k := by
  cases k with | axiomInfo v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩ | _ => exact ⟨(fun h => by cases h), (by rintro ⟨_, h⟩; cases h)⟩

theorem kindIn_axiom (k : ConstantInfo) (s : List ConstantInfo) :
    Regula.Load.kindIn k s = .axiom ↔ AxiomInfo k ∨ ∃ v ∈ s, AxiomInfo v := by
  simp only [Regula.Load.kindIn]
  split
  · rename_i hs; simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs; exact ⟨fun _ => .inr hs, fun _ => rfl⟩
  · rename_i hs; simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs; simp only [kindOf_axiom, hs, or_false]

private theorem constKind'_constKind (k : Regula.Closed.Kind) : Link.constKind' (constKind k) = k := by
  cases k <;> rfl

private theorem constKind_inj {a b : Regula.Closed.Kind} : constKind a = constKind b ↔ a = b :=
  ⟨fun h => (constKind'_constKind a).symm.trans ((congrArg Link.constKind' h).trans (constKind'_constKind b)),
    congrArg constKind⟩

private theorem decl_safety_eq {d : Regula.Closed.Decl} {v : Regula.Closed.Safety} :
    (decl d).safety = safety v ↔ d.safety = v := (Link.safety_iff d v).symm

private theorem decl_kind_eq {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} {k : Regula.Closed.Kind} :
    (decl (f.declIn n m info s)).kind = constKind k ↔ Regula.Load.kindIn info s = k :=
  constKind_inj

private theorem kindIn_eq_of_ne_axiom {info : ConstantInfo} {s : List ConstantInfo} {k : Regula.Closed.Kind}
    (hk : k ≠ .axiom) :
    Regula.Load.kindIn info s = k ↔ Regula.Load.kindOf info = k ∧ ∀ w ∈ s, ¬ AxiomInfo w := by
  simp only [Regula.Load.kindIn]
  split
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom] at hs
    obtain ⟨w, hw, hax⟩ := hs
    exact ⟨fun h => (hk h.symm).elim, fun h => (h.2 w hw hax).elim⟩
  · rename_i hs
    simp only [List.any_eq_true, beq_iff_eq, kindOf_axiom, not_exists, not_and] at hs
    exact ⟨fun h => ⟨h, hs⟩, (·.1)⟩

theorem kind_axiom {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .axiom ↔ AxiomInfo info ∨ ∃ v ∈ s, AxiomInfo v :=
  (decl_kind_eq (k := .axiom)).trans (kindIn_axiom info s)

theorem kind_definition {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .definition ↔
      (∃ v, info = .defnInfo v) ∧ ∀ w ∈ s, ¬ AxiomInfo w :=
  (decl_kind_eq (k := .definition)).trans
    ((kindIn_eq_of_ne_axiom (by decide)).trans (and_congr_left fun _ => kindOf_definition info))

theorem kind_inductive {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .inductive ↔
      (∃ v, info = .inductInfo v) ∧ ∀ w ∈ s, ¬ AxiomInfo w :=
  (decl_kind_eq (k := .inductive)).trans
    ((kindIn_eq_of_ne_axiom (by decide)).trans (and_congr_left fun _ => by
      cases info with | inductInfo v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩ | _ => exact ⟨(fun h => by cases h), (by rintro ⟨_, h⟩; cases h)⟩))

theorem kind_envAxiom {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    (hn : f.env.constants.map₁[n]? = some info) :
    (decl (f.declIn n m info (f.stated.getD n []))).kind = .axiom ↔ EnvAxiom f n :=
  kind_axiom.trans ⟨(⟨info, hn, ·⟩), by rintro ⟨_, hk, h⟩; rw [hn] at hk; cases hk; exact h⟩

theorem kindIn_of_stated {info : ConstantInfo} {s : List ConstantInfo} (hs : ∀ w ∈ s, ¬ AxiomInfo w) :
    Regula.Load.kindIn info s = Regula.Load.kindOf info := by
  have hn : s.any (Regula.Load.kindOf · == .axiom) = false :=
    List.any_eq_false.mpr fun w hw hk => hs w hw ((kindOf_axiom w).mp (beq_iff_eq.mp hk))
  simp only [Regula.Load.kindIn, hn, Bool.false_eq_true, ↓reduceIte]

theorem kind_theorem {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).kind = .theorem ↔
      (∃ v, info = .thmInfo v) ∧ ∀ w ∈ s, ¬ AxiomInfo w :=
  (decl_kind_eq (k := .theorem)).trans
    ((kindIn_eq_of_ne_axiom (by decide)).trans (and_congr_left fun _ => by
      cases info with | thmInfo v => exact ⟨fun _ => ⟨v, rfl⟩, fun _ => rfl⟩ | _ => exact ⟨(fun h => by cases h), (by rintro ⟨_, h⟩; cases h)⟩))

/-- A constant of no stated axiom is a definition or an opaque constant in the input exactly when its
{name}`ConstantInfo` is one. -/
theorem kind_runs {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} (hs : ∀ w ∈ s, ¬ AxiomInfo w) :
    ((decl (f.declIn n m info s)).kind = .definition ∨ (decl (f.declIn n m info s)).kind = .opaque) ↔
      (∃ v, info = .defnInfo v) ∨ ∃ v, info = .opaqueInfo v := by
  simp only [decl, Regula.Load.Facts.declIn, kindIn_of_stated hs]
  cases info with
  | defnInfo v => exact ⟨fun _ => .inl ⟨v, rfl⟩, fun _ => .inl rfl⟩
  | opaqueInfo v => exact ⟨fun _ => .inr ⟨v, rfl⟩, fun _ => .inr rfl⟩
  | _ => exact ⟨(by rintro (h | h) <;> cases h), (by rintro (⟨_, h⟩ | ⟨_, h⟩) <;> cases h)⟩

theorem theorem_env (hl : Loaded f roots p i) (u : Name) :
    (∃ e ∈ (toSpec i).decls, e.name = u ∧ e.kind = .theorem) ↔ EnvTheorem f u := by
  rw [exists_decl_env hl]
  exact ⟨by rintro ⟨_, _, hn, _, hk⟩; obtain ⟨⟨v, rfl⟩, hs⟩ := kind_theorem.mp hk; exact ⟨v, hn, hs⟩,
    by rintro ⟨v, hn, hs⟩; obtain ⟨m, hm⟩ := module_of hl hn; exact ⟨_, m, hn, hm, kind_theorem.mpr ⟨⟨v, rfl⟩, hs⟩⟩⟩

theorem panic_env (hl : Loaded f roots p i) (u : Name) :
    (toSpec i).PanicForm u ↔ EnvPanic f u := by
  unfold Input.PanicForm EnvPanic; rw [theorem_env hl]

theorem isAxiom_env (hl : Loaded f roots p i) (a : Name) :
    (toSpec i).IsAxiom a ↔ EnvAxiom f a := by
  rw [Input.IsAxiom, exists_decl_env hl]
  exact ⟨by rintro ⟨_, _, hn, _, hk⟩; exact (kind_envAxiom hn).mp hk,
    fun h => by obtain ⟨_, hn, _⟩ := id h; obtain ⟨m, hm⟩ := module_of hl hn; exact ⟨_, m, hn, hm, (kind_envAxiom hn).mpr h⟩⟩

theorem known_env (hl : Loaded f roots p i) (a : Name) :
    (toSpec i).Known a ↔ a ∈ logicalAxioms ∧ (∃ info, f.env.constants.map₁[a]? = some info) ∧
      EnvToolchain f a :=
  and_congr_right fun _ => (exists_decl_env hl a (·.inToolchain = true)).trans
    ⟨by rintro ⟨info, m, hn, hm, ht⟩; exact ⟨⟨info, hn⟩, m, hm, ht⟩,
     by rintro ⟨⟨info, hn⟩, m, hm, ht⟩; exact ⟨info, m, hn, hm, ht⟩⟩

theorem admits_env (hl : Loaded f roots p i) {a : Name} {info : ConstantInfo}
    (ha : f.env.constants.map₁[a]? = some info) :
    (toSpec i).Admits (toSpec i).profile a ↔ EnvAdmits f p a := by
  have hp : (toSpec i).profile = profile p := by simp only [toSpec, toSpecDraft, hl.profile]
  rw [hp]
  cases p <;> simp only [Input.Admits, profile, EnvAdmits, known_env hl, logicalAxioms,
    List.mem_cons, List.not_mem_nil, or_false]
  · exact ⟨fun h => ⟨h.2, h.1.2.2⟩, fun h => ⟨⟨h.1.imp id .inl, ⟨info, ha⟩, h.2⟩, h.1⟩⟩
  · exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ⟨info, ha⟩, h.2⟩⟩

theorem safety_partial {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).safety = .partial ↔
      info.isPartial = true ∧ info.isUnsafe = false :=
  (decl_safety_eq (v := .partial)).trans (safetyOf_partial info)

theorem safety_safe {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).safety = .safe ↔
      info.isUnsafe = false ∧ info.isPartial = false :=
  (decl_safety_eq (v := .safe)).trans (safetyOf_safe info)

theorem safety_unsafe {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    (decl (f.declIn n m info s)).safety = .unsafe ↔ info.isUnsafe = true :=
  (decl_safety_eq (v := .unsafe)).trans (safetyOf_unsafe info)

theorem helper_env (hl : Loaded f roots p i) (n : Name) (m : Regula.Load.LoadedModule)
    (info : ConstantInfo) :
    (toSpec i).HelperForm (decl (f.declIn n m info (f.stated.getD n []))) ↔
      EnvHelper f n info m.name := by
  constructor
  · rintro ⟨h1, h2, h3, base, hb, hname, hk, hm, hu, hi', he⟩
    obtain ⟨hp, hs⟩ := safety_partial.mp h1
    obtain ⟨_, lm, hn', hm', hv⟩ := of_mem hl hb; rw [hv] at hk hu hi' he
    obtain ⟨⟨v, rfl⟩, hst⟩ := kind_definition.mp hk; obtain ⟨hu1, hu2⟩ := safety_safe.mp hu
    exact ⟨hp, hs, h2, h3, base.name, v, hname, hn', hst,
      moduleOf?_eq_some.mpr ⟨lm, hm', (congrArg Decl.module hv).symm.trans hm⟩, hu1, hu2, hi', he⟩
  · rintro ⟨hp, hs, h2, h3, _, v, hname, hn', hst, hmod, hu1, hu2, hi', he⟩
    obtain ⟨lm, hm', hlm⟩ := moduleOf?_eq_some.mp hmod
    exact ⟨safety_partial.mpr ⟨hp, hs⟩, h2, h3, _, to_mem hl hn' hm', hname,
      kind_definition.mpr ⟨⟨v, rfl⟩, hst⟩, hlm, safety_safe.mpr ⟨hu1, hu2⟩, hi', he⟩

theorem ctorIdxDef_env (hl : Loaded f roots p i) {n : Name} {m : Regula.Load.LoadedModule}
    {info : ConstantInfo} (hn : f.env.constants.map₁[n]? = some info) (hm : f.info? n = some m) :
    (toSpec i).CtorIdxDef (decl (f.declIn n m info (f.stated.getD n []))) ↔
      EnvCtorIdxDef f n info m.name := by
  constructor
  · rintro ⟨ind, implSpec, himplMem, hpair⟩
    obtain ⟨⟨g, hgMem, hgName, hgTc⟩, ⟨indSpec, hindMem, hindName, hindKind, hindSafe, hindMod⟩,
      hdName, hdKind, hdSafe, hdForm, hdImpl, hdExt, hdInit,
      hiName, hiMod, hiKind, hiSafe, hiForm, hiImpl, hiExt, hiInit⟩ := hpair
    change n = Name.str ind "ctorIdx" at hdName
    obtain ⟨⟨defv, rfl⟩, hdSt⟩ := kind_definition.mp hdKind
    obtain ⟨hdU, hdP⟩ := safety_safe.mp hdSafe
    have hdShape : ctorIdxShape f.env n (.defnInfo defv) = .defn ind := by
      simpa [decl, Regula.Load.Facts.declIn, ctorIdxFormOf_eq_shape] using hdForm
    obtain ⟨gk, glm, hgk, hglm, hgv⟩ := of_mem hl hgMem
    have hgtag : (∃ k, f.env.constants.map₁[`getObjTagNat]? = some k) ∧ EnvToolchain f `getObjTagNat := by
      rw [hgName] at hgk hglm; rw [hgv] at hgTc
      exact ⟨⟨gk, hgk⟩, glm, hglm, hgTc⟩
    obtain ⟨indInfo, indLm, hindK, hindLm, hindV⟩ := of_mem hl hindMem
    rw [hindName] at hindK hindLm; rw [hindV] at hindKind hindSafe hindMod
    obtain ⟨⟨indv, rfl⟩, hindSt⟩ := kind_inductive.mp hindKind
    obtain ⟨hindU, hindP⟩ := safety_safe.mp hindSafe
    obtain ⟨implInfo, implLm, himplK, himplLm, himplV⟩ := of_mem hl himplMem
    rw [hiName] at himplK himplLm; rw [himplV] at hiMod hiKind hiSafe hiForm hiImpl hiExt hiInit
    obtain ⟨⟨implv, rfl⟩, himplSt⟩ := kind_definition.mp hiKind
    have himplU := safety_unsafe.mp hiSafe
    have himplShape : ctorIdxShape f.env (Name.str (Name.str ind "ctorIdx") "_impl") (.defnInfo implv) = .impl ind := by
      simpa [decl, Regula.Load.Facts.declIn, hiName, ctorIdxFormOf_eq_shape] using hiForm
    refine ⟨ind, defv, implv, hdName, rfl, hgtag.1, hgtag.2,
      ⟨indv, hindK, hindName ▸ hindSt, moduleOf?_eq_some.mpr ⟨indLm, hindLm, hindMod⟩, hindU, hindP⟩,
      hdName ▸ hn, hdName ▸ hdSt, hdName ▸ moduleOf?_eq_some.mpr ⟨m, hm, rfl⟩,
      hdU, hdP, hdName ▸ hdShape, hdName ▸ hdImpl, hdName ▸ hdExt, hdName ▸ hdInit,
      himplK, hiName ▸ himplSt, moduleOf?_eq_some.mpr ⟨implLm, himplLm, hiMod⟩,
      himplU, himplShape, hiName ▸ hiImpl, hiName ▸ hiExt, hiName ▸ hiInit⟩
  · rintro ⟨ind, defv, implv, rfl, rfl, ⟨gk, hgk⟩, ⟨glm, hglm, hgTc⟩,
      ⟨indv, hindK, hindSt, hindMod, hindU, hindP⟩,
      _, hdSt, _, hdU, hdP, hdShape, hdImpl, hdExt, hdInit,
      himplK, himplSt, himplMod, himplU, himplShape, hiImpl, hiExt, hiInit⟩
    obtain ⟨indLm, hindLm, hindLmName⟩ := moduleOf?_eq_some.mp hindMod
    obtain ⟨implLm, himplLm, himplLmName⟩ := moduleOf?_eq_some.mp himplMod
    refine ⟨ind, decl (f.declIn (Name.str (Name.str ind "ctorIdx") "_impl") implLm (.defnInfo implv)
        (f.stated.getD (Name.str (Name.str ind "ctorIdx") "_impl") [])),
      to_mem hl himplK himplLm, ?_⟩
    exact ⟨⟨_, to_mem hl hgk hglm, rfl, hgTc⟩,
      ⟨_, to_mem hl hindK hindLm, rfl, kind_inductive.mpr ⟨⟨indv, rfl⟩, hindSt⟩,
        safety_safe.mpr ⟨hindU, hindP⟩, hindLmName⟩,
      rfl, kind_definition.mpr ⟨⟨defv, rfl⟩, hdSt⟩, safety_safe.mpr ⟨hdU, hdP⟩,
      by simpa [decl, Regula.Load.Facts.declIn, ctorIdxFormOf_eq_shape] using hdShape,
      hdImpl, hdExt, hdInit,
      rfl, himplLmName, kind_definition.mpr ⟨⟨implv, rfl⟩, himplSt⟩, safety_unsafe.mpr himplU,
      by simpa [decl, Regula.Load.Facts.declIn, ctorIdxFormOf_eq_shape] using himplShape,
      hiImpl, hiExt, hiInit⟩

theorem ctorIdxImpl_env (hl : Loaded f roots p i) {n : Name} {m : Regula.Load.LoadedModule}
    {info : ConstantInfo} (hn : f.env.constants.map₁[n]? = some info) (hm : f.info? n = some m) :
    (toSpec i).CtorIdxImpl (decl (f.declIn n m info (f.stated.getD n []))) ↔
      EnvCtorIdxImpl f n info m.name := by
  constructor
  · rintro ⟨ind, defSpec, hdefMem, hpair⟩
    obtain ⟨⟨g, hgMem, hgName, hgTc⟩, ⟨indSpec, hindMem, hindName, hindKind, hindSafe, hindMod⟩,
      hdName, hdKind, hdSafe, hdForm, hdImpl, hdExt, hdInit,
      hiName, hiMod, hiKind, hiSafe, hiForm, hiImpl, hiExt, hiInit⟩ := hpair
    change n = Name.str (Name.str ind "ctorIdx") "_impl" at hiName
    obtain ⟨⟨implv, rfl⟩, hiSt⟩ := kind_definition.mp hiKind
    have hiU := safety_unsafe.mp hiSafe
    have hiShape : ctorIdxShape f.env n (.defnInfo implv) = .impl ind := by
      simpa [decl, Regula.Load.Facts.declIn, ctorIdxFormOf_eq_shape] using hiForm
    obtain ⟨gk, glm, hgk, hglm, hgv⟩ := of_mem hl hgMem
    have hgtag : (∃ k, f.env.constants.map₁[`getObjTagNat]? = some k) ∧ EnvToolchain f `getObjTagNat := by
      rw [hgName] at hgk hglm; rw [hgv] at hgTc
      exact ⟨⟨gk, hgk⟩, glm, hglm, hgTc⟩
    obtain ⟨defInfo, defLm, hdefK, hdefLm, hdefV⟩ := of_mem hl hdefMem
    rw [hdName] at hdefK hdefLm; rw [hdefV] at hdKind hdSafe hdForm hdImpl hdExt hdInit hiMod hindMod
    have hdefLmName : defLm.name = m.name := hiMod.symm
    obtain ⟨⟨defv, rfl⟩, hdSt⟩ := kind_definition.mp hdKind
    obtain ⟨hdU, hdP⟩ := safety_safe.mp hdSafe
    have hdShape : ctorIdxShape f.env (Name.str ind "ctorIdx") (.defnInfo defv) = .defn ind := by
      simpa [decl, Regula.Load.Facts.declIn, hdName, ctorIdxFormOf_eq_shape] using hdForm
    obtain ⟨indInfo, indLm, hindK, hindLm, hindV⟩ := of_mem hl hindMem
    rw [hindName] at hindK hindLm; rw [hindV] at hindKind hindSafe hindMod
    obtain ⟨⟨indv, rfl⟩, hindSt⟩ := kind_inductive.mp hindKind
    obtain ⟨hindU, hindP⟩ := safety_safe.mp hindSafe
    refine ⟨ind, defv, implv, hiName, rfl, hgtag.1, hgtag.2,
      ⟨indv, hindK, hindName ▸ hindSt, moduleOf?_eq_some.mpr ⟨indLm, hindLm, hindMod.trans hdefLmName⟩, hindU, hindP⟩,
      hdefK, hdName ▸ hdSt, moduleOf?_eq_some.mpr ⟨defLm, hdefLm, hdefLmName⟩,
      hdU, hdP, hdShape, hdName ▸ hdImpl, hdName ▸ hdExt, hdName ▸ hdInit,
      hiName ▸ hn, hiName ▸ hiSt, hiName ▸ moduleOf?_eq_some.mpr ⟨m, hm, rfl⟩,
      hiU, hiName ▸ hiShape, hiName ▸ hiImpl, hiName ▸ hiExt, hiName ▸ hiInit⟩
  · rintro ⟨ind, defv, implv, rfl, rfl, ⟨gk, hgk⟩, ⟨glm, hglm, hgTc⟩,
      ⟨indv, hindK, hindSt, hindMod, hindU, hindP⟩,
      hdefK, hdSt, hdefMod, hdU, hdP, hdShape, hdImpl, hdExt, hdInit,
      _, hiSt, _, hiU, hiShape, hiImpl, hiExt, hiInit⟩
    obtain ⟨indLm, hindLm, hindLmName⟩ := moduleOf?_eq_some.mp hindMod
    obtain ⟨defLm, hdefLm, hdefLmName⟩ := moduleOf?_eq_some.mp hdefMod
    refine ⟨ind, decl (f.declIn (Name.str ind "ctorIdx") defLm (.defnInfo defv)
        (f.stated.getD (Name.str ind "ctorIdx") [])),
      to_mem hl hdefK hdefLm, ?_⟩
    exact ⟨⟨_, to_mem hl hgk hglm, rfl, hgTc⟩,
      ⟨_, to_mem hl hindK hindLm, rfl, kind_inductive.mpr ⟨⟨indv, rfl⟩, hindSt⟩,
        safety_safe.mpr ⟨hindU, hindP⟩, hindLmName.trans hdefLmName.symm⟩,
      rfl, kind_definition.mpr ⟨⟨defv, rfl⟩, hdSt⟩, safety_safe.mpr ⟨hdU, hdP⟩,
      by simpa [decl, Regula.Load.Facts.declIn, ctorIdxFormOf_eq_shape] using hdShape,
      hdImpl, hdExt, hdInit,
      rfl, hdefLmName.symm, kind_definition.mpr ⟨⟨implv, rfl⟩, hiSt⟩, safety_unsafe.mpr hiU,
      by simpa [decl, Regula.Load.Facts.declIn, ctorIdxFormOf_eq_shape] using hiShape,
      hiImpl, hiExt, hiInit⟩

theorem wf_env (hl : Loaded f roots p i) : (toSpec i).WellFormed ↔ EnvForm f :=
  ⟨fun h => ⟨by rintro _ u ⟨info, hn, hm⟩; obtain ⟨_, hmod⟩ := module_of hl hn; exact (resolves_env hl u).mp (h.closed _ (to_mem hl hn hmod) u ((mem_usesIn info _ u).mpr hm)),
      by simpa [toSpec, toSpecDraft, hl.modules] using h.claims⟩,
   fun h => ⟨fun _ hx u hu => by obtain ⟨info, _, hn, _, hv⟩ := of_mem hl hx; exact (resolves_env hl u).mpr (h.closed _ u ⟨info, hn, (mem_usesIn info _ u).mp (hv ▸ hu)⟩),
      by simpa [toSpec, toSpecDraft, hl.modules] using h.claims⟩⟩

theorem flagged_iff {n : Name} {m : Regula.Load.LoadedModule} {info : ConstantInfo}
    {s : List ConstantInfo} :
    ((decl (f.declIn n m info s)).safety ≠ .safe ∨ HelperNamed (decl (f.declIn n m info s))) ↔
      (info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") := by
  have hs : (decl (f.declIn n m info s)).safety ≠ .safe ↔ info.isUnsafe = true ∨ info.isPartial = true := by
    rw [ne_eq, safety_safe]; cases info.isUnsafe <;> cases info.isPartial <;> decide
  rw [hs, or_assoc]; rfl

/-- What every rule of the registry states, rule by rule: the statement that {name}`EnvFloor` restates in the terms of the
environment. A rule added to the registry makes this false until {name}`EnvFloor` and this theorem state it too. -/
theorem allHold_iff (i : Input) : AllHold i ↔
    (∀ c, ¬ Violates1001 i c) ∧ (∀ c, ¬ Violates1002 i c) ∧ (∀ c, ¬ Violates1003 i c) ∧
      (∀ c, ¬ Violates1004 i c) ∧ (∀ c, ¬ Violates1005 i c) ∧ (∀ c, ¬ Violates1006 i c) ∧
      (∀ c, ¬ Violates1011 i c) ∧ (∀ c, ¬ Violates1012 i c) ∧ (∀ c, ¬ Violates1013 i c) := by
  simp only [AllHold, registry, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    rg1001Proved, rg1002Proved, rg1003Proved, rg1004Proved, rg1005Proved, rg1006Proved,
    rg1011Proved, rg1012Proved, rg1013Proved]

theorem declaredInClaimed_env (hl : Loaded f roots p i) {m c : Name} (hcs : (toSpec i).HasCSimp m c) :
    (toSpec i).DeclaredInClaimed c ↔ ∃ cm info, (cm, c, info) ∈ f.claimedConstants := by
  simp only [Input.HasCSimp, toSpec, toSpecDraft, List.mem_map] at hcs
  obtain ⟨e, he, hmk⟩ := hcs
  exact (hl.claimedConstants c).trans (and_iff_right ⟨e, he, congrArg CSimpEntry.thm hmk⟩)

theorem hasCSimp_env (hl : Loaded f roots p i) (m thm : Name) :
    (toSpec i).HasCSimp m thm ↔ m ∈ f.claimed ∧ ModuleCSimp f.env m thm := by
  simp only [Input.HasCSimp, toSpec, toSpecDraft, List.mem_map]
  exact ⟨by rintro ⟨e, he, hmk⟩; cases hmk; exact (hl.csimps e).mp he,
    fun h => ⟨⟨m, thm⟩, (hl.csimps ⟨m, thm⟩).mpr h, rfl⟩⟩

theorem allHold_env (hl : Loaded f roots p i) : AllHold (toSpec i) ↔ EnvFloor f p := by
  rw [allHold_iff]
  constructor
  · rintro ⟨h1, -, -, -, h5, h6, h11, h12, h13⟩
    refine ⟨fun m hm => Classical.byContradiction fun hno =>
        h13 m ⟨(claimed_iff hl m).mpr hm, fun h => hno ((moduleFile_env hl m).mp h)⟩,
      fun m hm => ⟨hl.indexed m hm, fun thm hcs => Classical.byContradiction fun hno =>
        let hs := (hasCSimp_env hl m thm).mpr ⟨hm, hcs⟩
        h11 thm (.inr ⟨m, (claimed_iff hl m).mpr hm, hs, fun hd => hno ((declaredInClaimed_env hl hs).mp hd)⟩)⟩,
      ?_⟩
    intro n info m hn hm hc
    obtain ⟨lm, hlm, rfl⟩ := moduleOf?_eq_some.mp hm
    have hx := to_mem hl hn hlm
    have hcm := (claimed_iff hl _).mpr hc
    have hs : ∀ w ∈ f.stated.getD n [], ¬ AxiomInfo w := fun w hw hax =>
      h1 n ⟨_, hx, rfl, hcm, (kind_envAxiom hn).mpr ⟨info, hn, .inr ⟨w, hw, hax⟩⟩⟩
    have hr6 := fun r => h6 n ⟨_, hx, rfl, hcm, r⟩
    have hr11 := fun r => h11 n (.inl ⟨_, hx, rfl, hcm, r⟩)
    refine ⟨fun hax => h1 n ⟨_, hx, rfl, hcm, (kind_envAxiom hn).mpr hax⟩,
      fun hflag => Classical.byContradiction fun hno =>
        hr6 (.inl ⟨flagged_iff.mpr hflag,
          fun hh => hno (.inl ((helper_env hl n lm info).mp hh)),
          fun hc' => hno (.inr ((ctorIdxImpl_env hl hn hlm).mp hc'))⟩),
      fun l hl' hv => hr6 (.inr (.inl ⟨l, hl', (mem_valueUsesOf info l).mpr hv⟩)),
      fun hrun hv => hr6 (.inr (.inr ⟨(kind_runs hs).mpr hrun, (mem_valueUsesOf info ``Lean.Order.fix).mpr hv⟩)),
      fun a hr hax => hax.elim fun _ ha => Classical.byContradiction fun hno =>
        h5 n ⟨⟨_, hx, rfl, hcm⟩, a, ⟨(reaches_env hl n a).mpr hr, (isAxiom_env hl a).mpr hax⟩,
          fun hadm => hno ((admits_env hl ha.1).mp hadm)⟩,
      ?_, ?_, fun hdef => ?_,
      fun hrun u hv hpanic => h12 n ⟨_, hx, rfl, hcm, (kind_runs hs).mpr hrun, u,
        (mem_valueUsesOf info u).mpr hv, (panic_env hl u).mpr hpanic⟩⟩
    · cases hi : Lean.Compiler.getImplementedBy? f.env n with
      | none => exact .inl rfl
      | some impl =>
        exact .inr (Classical.byContradiction fun hno =>
          hr11 (.inl ⟨⟨impl, hi⟩, fun hc' => hno ((ctorIdxDef_env hl hn hlm).mp hc')⟩))
    · cases he : Lean.isExtern f.env n with
      | false => rfl | true => exact (hr11 (.inr (.inl he))).elim
    · cases hfn : Lean.getInitFnNameFor? f.env n with
      | none => rfl | some fn => exact (hr11 (.inr (.inr ⟨kind_definition.mpr ⟨hdef, hs⟩, fn, hfn⟩))).elim
  · rintro ⟨hfiles, hcsimps, hf⟩
    have hget {x : Decl} {info m} (hn : f.env.constants.map₁[x.name]? = some info)
        (hm : f.info? x.name = some m)
        (hv : x = decl (f.declIn x.name m info (f.stated.getD x.name [])))
        (hcm : (toSpec i).ClaimedModule x.module) :=
      hf _ _ _ hn (moduleOf?_eq_some.mpr ⟨m, hm, by rw [hv]; rfl⟩) ((claimed_iff hl _).mp hcm)
    have no5 : ∀ c, ¬ Violates1005 (toSpec i) c := by
      rintro c ⟨⟨x, hx, rfl, hcm⟩, a, ⟨hr, hax⟩, hna⟩
      obtain ⟨info, m, hn, hm, hv⟩ := of_mem hl hx
      have hax' := (isAxiom_env hl a).mp hax
      obtain ⟨_, ha, -⟩ := id hax'
      exact hna ((admits_env hl ha).mpr ((hget hn hm hv hcm).2.2.2.2.1 a ((reaches_env hl _ a).mp hr) hax'))
    refine ⟨?_, fun c h => no5 c (rg1005_of_hole h), fun c h => no5 c (rg1005_of_unknown h),
      fun c h => no5 c (rg1005_of_compiler h), no5, ?_, ?_, ?_,
      fun c h => h.2 ((moduleFile_env hl c).mpr (hfiles c ((claimed_iff hl c).mp h.1)))⟩
    · rintro _ ⟨x, hx, rfl, hcm, hk⟩
      obtain ⟨info, m, hn, hm, hv⟩ := of_mem hl hx
      exact (hget hn hm hv hcm).1 ((kind_envAxiom hn).mp (hv ▸ hk))
    · rintro _ ⟨x, hx, rfl, hcm, hv⟩
      obtain ⟨info, m, hn, hm, hd⟩ := of_mem hl hx
      obtain ⟨hna, h6, h7, hfix, -⟩ := hget hn hm hd hcm
      have hmn : m.name = x.module := by rw [hd]; rfl
      rw [hd] at hv
      rcases hv with ⟨hflag, hno, hnc⟩ | ⟨l, hl', hu⟩ | ⟨hk, hu⟩
      · rcases hmn ▸ h6 (flagged_iff.mp hflag) with hh | hc'
        · exact hno ((helper_env hl _ m info).mpr hh)
        · exact hnc ((ctorIdxImpl_env hl hn hm).mpr hc')
      · exact h7 l hl' ((mem_valueUsesOf info l).mp hu)
      · exact hfix ((kind_runs fun w hw hax => hna ⟨info, hn, .inr ⟨w, hw, hax⟩⟩).mp hk)
          ((mem_valueUsesOf info ``Lean.Order.fix).mp hu)
    · rintro c (⟨x, hx, rfl, hcm, hr⟩ | ⟨m, hcm, hcs, hnot⟩)
      · obtain ⟨info, m, hn, hm, hd⟩ := of_mem hl hx
        obtain ⟨-, -, -, -, -, hi, he, hinit, -⟩ := hget hn hm hd hcm
        have hmn : m.name = x.module := by rw [hd]; rfl
        rw [hd] at hr
        rcases hr with ⟨⟨_, himpl⟩, hnc⟩ | hext | ⟨hkind, _, hfn⟩
        · rcases hi with hnone | hcd
          · cases himpl.symm.trans hnone
          · exact hnc ((ctorIdxDef_env hl hn hm).mpr (hmn ▸ hcd))
        · cases hext.symm.trans he
        · cases hfn.symm.trans (hinit (kind_definition.mp hkind).1)
      · obtain ⟨hm, hreg⟩ := (hasCSimp_env hl m c).mp hcs
        exact hnot ((declaredInClaimed_env hl hcs).mpr ((hcsimps m hm).2 c hreg))
    · rintro _ ⟨x, hx, rfl, hcm, hk, u, hu, hp⟩
      obtain ⟨info, m, hn, hm, hd⟩ := of_mem hl hx
      obtain ⟨hna, -, -, -, -, -, -, -, h12⟩ := hget hn hm hd hcm
      rw [hd] at hk hu
      exact h12 ((kind_runs fun w hw hax => hna ⟨info, hn, .inr ⟨w, hw, hax⟩⟩).mp hk) u
        ((mem_valueUsesOf info u).mp hu) ((panic_env hl u).mp hp)

theorem input_form (h : f.input roots p = .ok i) : EnvForm f :=
  (wf_env (input_loaded h)).mp (wf_toSpec i)

theorem pass_iff (h : f.input roots p = .ok i) :
    i.report.verdict = .pass ↔ EnvForm f ∧ EnvFloor f p := by
  rw [(report_complete i).2, allHold_env (input_loaded h)]
  exact ⟨fun hf => ⟨input_form h, hf⟩, (·.2)⟩

theorem decision_failed (why : String) :
    (Regula.Closed.decision (.error why)).verdict = .incomplete := by rfl

theorem decision_pass {r : Except String Regula.Closed.Input}
    (h : (Regula.Closed.decision r).verdict = .pass) :
    ∃ i, r = .ok i ∧ i.report.verdict = .pass := by
  cases r with | error _ => cases h | ok i => exact ⟨i, rfl, h⟩

theorem pass_floor (h : (Regula.Closed.decision (f.input roots p)).verdict = .pass) :
    (∀ r ∈ roots, r ∈ f.claimed) ∧ (∀ m ∈ f.claimed, m ∈ f.env.header.moduleNames.toList) ∧
      (∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.moduleOf? n = some m) ∧
      EnvForm f ∧ EnvFloor f p := by
  obtain ⟨i, hi, hp⟩ := decision_pass h; have hl := input_loaded hi
  exact ⟨hl.roots, fun _ => claimed_loaded f,
    fun _ _ hn => by obtain ⟨m, hm⟩ := module_of hl hn; exact ⟨m.name, moduleOf?_eq_some.mpr ⟨m, hm, rfl⟩⟩,
    (pass_iff hi).mp hp⟩

theorem mem_claimedConstants {m n : Name} {info : ConstantInfo} :
    (m, n, info) ∈ f.claimedConstants ↔ ∃ (k : Nat) (lm : Regula.Load.LoadedModule) (data :
        Lean.ModuleData), f.modules[k]? = some lm ∧ lm.claimed = true ∧ lm.name = m ∧
      f.env.header.moduleData[k]? = some data ∧ (n, info) ∈ data.constNames.zip data.constants := by
  simp only [Regula.Load.Facts.claimedConstants, List.mem_flatMap, List.mem_filter,
    Array.mem_toList_iff, List.mem_map, Prod.mk.injEq, Array.mem_iff_getElem?,
    Array.getElem?_zip_eq_some]
  exact ⟨by rintro ⟨⟨lm, data⟩, ⟨⟨k, h1, h2⟩, hc⟩, ⟨_, _⟩, hx, rfl, rfl, rfl⟩; exact ⟨k, lm, data, h1, hc, rfl, h2, hx⟩,
    by rintro ⟨k, lm, data, h1, hc, rfl, h2, hx⟩; exact ⟨(lm, data), ⟨⟨k, h1, h2⟩, hc⟩, (n, info), hx, rfl, rfl, rfl⟩⟩

theorem fitsUnshown_iff (hl : Loaded f roots p i) (x : Name × Name × ConstantInfo) :
    Regula.Load.fitsUnshown f i.tables x.1 x.2.1 x.2.2 = true ↔
      ModuleUnreplaced f.env x.1 x.2.1 ∧
      Regula.Load.kindOf x.2.2 = .theorem ∧ Regula.Load.safetyOf x.2.2 = .safe ∧
      (∀ b, x.2.1 ≠ .str b "_unsafe_rec") ∧ (∀ l ∈ loopConstructs, ¬ ValueMentions x.2.2 l) ∧
      ∀ u, Mentions x.2.2 u → (∃ k, f.env.constants.map₁[u]? = some k) ∧
        ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨m, n, info⟩ := x
  have hheld (u : Name) : i.tables.index.contains u = true ↔ ∃ k, f.env.constants.map₁[u]? = some k := by
    rw [← resolves_env hl u, Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists]
    exact ⟨by rintro ⟨d, hd⟩; obtain ⟨hm, rfl⟩ := (i.tables.mem_index _ _).mp hd; exact ⟨_, mem_decls.mpr ⟨d, hm, rfl⟩, rfl⟩,
      by rintro ⟨_, hx, rfl⟩; obtain ⟨d, hd, rfl⟩ := mem_decls.mp hx; exact ⟨d, (i.tables.mem_index _ _).mpr ⟨hd, rfl⟩⟩⟩
  have hadm (u : Name) : (∀ a ∈ i.tables.axiomSet u, i.tables.admits i.profile a = true) ↔
      ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a :=
    ⟨fun hall a hr hea => hea.elim fun _ ha => (admits_env hl ha.1).mp ((admits_iff _ i.profile a).mp
        (hall a ((axiomSet_iff _ u a).mpr ⟨(reaches_env hl u a).mpr hr, (isAxiom_env hl a).mpr hea⟩))),
     fun hall a hax => let hh := (axiomSet_iff _ u a).mp hax; let hea := (isAxiom_env hl a).mp hh.2
       hea.elim fun _ ha => (admits_iff _ i.profile a).mpr ((admits_env hl ha.1).mpr (hall a ((reaches_env hl u a).mp hh.1) hea))⟩
  simp only [Regula.Load.fitsUnshown, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    unreplaced_iff, List.all_eq_true, Array.all_eq_true_iff_forall_mem, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr ?_ (and_congr ?_ ?_)
  · exact ⟨fun h b hb => (by rw [(isUnsafeRecName_eq n b).mpr hb] at h; cases h),
      fun h => by cases hu : Lean.Compiler.isUnsafeRecName? n with
        | none => rfl | some b => exact absurd ((isUnsafeRecName_eq n b).mp hu) (h b)⟩
  · exact forall_congr' fun l => imp_congr Iff.rfl
      (by rw [← mem_valueUsesOf info l, Array.mem_toList_iff, Bool.eq_false_iff, ne_eq, Array.contains_iff_mem])
  · exact forall_congr' fun u => imp_congr (by rw [← Array.mem_toList_iff, mem_usesOf])
      (and_congr (hheld u) (hadm u))

theorem pass_held (h : (Regula.Closed.decision (f.input roots p)).verdict = .pass) {m n : Name}
    {info : ConstantInfo} (hx : (m, n, info) ∈ f.claimedConstants) :
    (ModuleUnreplaced f.env m n ∨ ModuleCtorIdxEntryOnly f.env m n info) ∧
    ((∃ v, info = .defnInfo v) → ModuleUninitialized f.env m n) ∧
    (∀ v, info ≠ .axiomInfo v) ∧
    ((info.isUnsafe = true ∨ info.isPartial = true ∨ ∃ b, n = .str b "_unsafe_rec") →
      (info.isPartial = true ∧ info.isUnsafe = false) ∨
        (info.isUnsafe = true ∧ ∃ ind, ctorIdxShape f.env n info = .impl ind)) ∧
    (∀ l ∈ loopConstructs, ¬ ValueMentions info l) ∧
    ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ¬ ValueMentions info ``Lean.Order.fix) ∧
    ((∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v) → ∀ u, ValueMentions info u → ¬ EnvPanic f u) ∧
    ∀ u, Mentions info u → ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a := by
  obtain ⟨i, hi, hp⟩ := decision_pass h; have hl := input_loaded hi
  rcases (input_kept hi hx).symm with hfits | hshown
  · obtain ⟨hattrs, hkind, hsafety, hname, hloop, huses⟩ := (fitsUnshown_iff hl _).mp hfits
    obtain ⟨hunsafe, hpartial⟩ := (safetyOf_safe info).mp hsafety
    refine ⟨.inl hattrs, (by rintro ⟨_, rfl⟩; cases hkind),
      (by rintro _ rfl; cases hkind),
      fun | .inl h => (by rw [hunsafe] at h; cases h)
          | .inr (.inl h) => (by rw [hpartial] at h; cases h)
          | .inr (.inr ⟨b, hb⟩) => (hname b hb).elim,
      hloop,
      (by rintro (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> cases hkind),
      (by rintro (⟨_, rfl⟩ | ⟨_, rfl⟩) <;> cases hkind),
      fun u hu => (huses u hu).2⟩
  obtain ⟨k, lm, hk, hread, hinfo, hclaimed⟩ := shown_true hshown
  have hmod : f.moduleOf? n = some lm.name := moduleOf?_eq_some.mpr ⟨lm, hinfo, rfl⟩
  have hcl : lm.name ∈ f.claimed := (mem_claimed_iff f _).mpr ⟨lm, mem_modules_of_info hinfo, rfl, hclaimed⟩
  obtain ⟨h1, h2, h3, hfix, h4, himpl, hext, hinit, h12⟩ := ((pass_iff hi).mp hp).2.2.2 n k lm.name hk hmod hcl
  simp only [Regula.Load.readOf, Prod.mk.injEq] at hread
  obtain ⟨hkind, hsafety, huses, hvalue, hctor⟩ := hread
  have hshape : ctorIdxShape f.env n k = ctorIdxShape f.env n info :=
    (ctorIdxFormOf_eq_iff f.env n k info).mp hctor
  have hsafe : k.isUnsafe = info.isUnsafe ∧ k.isPartial = info.isPartial := by
    let flags : Regula.Closed.Safety → Bool × Bool
      | .unsafe => (true, false) | .partial => (false, true) | .safe => (false, false)
    have hb (c : ConstantInfo) : (c.isUnsafe, c.isPartial) = flags (Regula.Load.safetyOf c) := by
      unfold Regula.Load.safetyOf
      cases hu : c.isUnsafe <;> cases hq : c.isPartial <;>
        first | rfl | exact absurd (not_unsafe_of_partial c hq) (by rw [hu]; decide)
    exact Prod.mk.inj ((hb k).trans ((congrArg flags hsafety).trans (hb info).symm))
  have hrun' (hr : (∃ v, info = .defnInfo v) ∨ (∃ v, info = .opaqueInfo v)) :
      (∃ v, k = .defnInfo v) ∨ (∃ v, k = .opaqueInfo v) := by
    cases k <;> rcases hr with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, rfl⟩ | cases hkind
  have hval {u} (hv : ValueMentions info u) : ValueMentions k u :=
    (mem_valueUsesOf k u).mp (hvalue ▸ (mem_valueUsesOf info u).mpr hv)
  refine ⟨shown_unreplaced hshown hk (himpl.imp id fun hcd => by
      obtain ⟨ind, defv, implv, rfl, rfl, hpair⟩ := hcd
      obtain ⟨-, -, -, -, -, -, -, -, hsh, himp, -⟩ := hpair
      exact ⟨ind, hsh, himp⟩) hext,
    fun hdef => let hki := (kindOf_definition info).mpr hdef
      shown_uninitialized hshown hki (hinit ((kindOf_definition k).mp (hkind.trans hki))),
    fun v hv => h1 ⟨k, hk, .inl ((kindOf_axiom k).mp (hkind.trans (congrArg Regula.Load.kindOf hv)))⟩,
    fun hflag => (by
      rcases h2 (by rwa [hsafe.1, hsafe.2]) with ⟨hpart, hsf, _⟩ | ⟨ind, defv, implv, rfl, rfl, hpair⟩
      · exact .inl ⟨hsafe.2 ▸ hpart, hsafe.1 ▸ hsf⟩
      · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, huns, hsh, -⟩ := hpair
        exact .inr ⟨hsafe.1 ▸ huns, ind, hshape ▸ hsh⟩),
    fun l hl' hv => h3 l hl' (hval hv),
    fun hrun hv => hfix (hrun' hrun) (hval hv),
    fun hrun u hv => h12 (hrun' hrun) u (hval hv),
    fun u hu a hr hax =>
      h4 a (.step ⟨k, hk, .inl ((mem_usesOf k u).mp (huses ▸ (mem_usesOf info u).mpr hu))⟩ hr) hax⟩

theorem profileOfRun_ok {version commit : String} {args : List String}
    {q : Regula.Closed.Profile} (h : Regula.Shell.profileOfRun version commit args = .ok q) :
    version = "4.36.0" ∧ commit = "611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9" ∧
      ∃ text, args = [text] ∧ Regula.Closed.Profile.ofSpelling? text = some q := by
  unfold Regula.Shell.profileOfRun at h; (split at h <;> try cases h)
  rename_i hs
  simp only [Bool.not_eq_true', Bool.eq_false_iff, Classical.not_not, Regula.Shell.supportsLean,
    Regula.Closed.pinnedLean, beq_iff_eq, Prod.mk.injEq] at hs
  (split at h <;> try cases h); (split at h <;> try cases h)
  exact ⟨hs.1, hs.2, _, rfl, ‹_›⟩

theorem profileOf_eq_some {text : String} {q : Regula.Closed.Profile}
    (h : Regula.Closed.Profile.ofSpelling? text = some q) :
    (text = "kernel-only" ∧ q = .kernelOnly) ∨ (text = "choice-free" ∧ q = .choiceFree) ∨
      (text = "standard-logical" ∧ q = .standardLogical) := by
  have hs := Regula.Closed.Profile.ofSpelling?_eq_some.mp h
  subst hs; cases q <;> simp only [Regula.Closed.Profile.spelling, true_and, true_or, or_true]

/-- {name (full := Regula.Load.below)}`below` is a test on components: the directory's are a proper prefix of the path's. It does not resolve `..`, and it does not
tell an absolute path from a relative one. -/
theorem below_iff (dir path : System.FilePath) :
    Regula.Load.below dir path = true ↔
      Regula.Load.parts dir <+: Regula.Load.parts path ∧
        Regula.Load.parts dir ≠ Regula.Load.parts path := by
  simp only [Regula.Load.below, Bool.and_eq_true, List.isPrefixOf_iff_prefix, bne_iff_ne]

/-- {name (full := Regula.Load.exactBelow)}`exactBelow` is a test on the components of the three paths: the real path's are the path's, and the directory's are a prefix of them,
so at or below. It does not tell an absolute path from a relative one. -/
theorem exactBelow_iff (dir path real : System.FilePath) :
    Regula.Load.exactBelow dir path real = true ↔
      Regula.Load.parts real = Regula.Load.parts path ∧
        Regula.Load.parts dir <+: Regula.Load.parts path := by
  simp only [Regula.Load.exactBelow, Bool.and_eq_true, beq_iff_eq, List.isPrefixOf_iff_prefix]

/-- A path with a `..` passes {name (full := Regula.Load.exactBelow)}`exactBelow` against no real path that has none, so a `..` needs no test of
its own. That {name}`IO.FS.realPath` gives a path with no `..` is the operating system's. -/
theorem exactBelow_no_parent (dir path real : System.FilePath)
    (h : Regula.Load.exactBelow dir path real = true) (hr : ".." ∉ Regula.Load.parts real) :
    ".." ∉ Regula.Load.parts path :=
  ((exactBelow_iff dir path real).mp h).1 ▸ hr

/-- What the loader asks of each constant of a claimed module's own {lit}`.olean` that the environment does not show to the rules
({name (full := Regula.Load.Facts.shown)}`Facts.shown`), in the terms of the environment: a safe theorem with neither replacement attribute
in its own module and no recursion helper's name, whose value mentions no
loop construct, and each constant it mentions is held and reaches only axioms that the profile admits. Lean's import
replaces such a constant ({name (full := Regula.Load.Facts.stated)}`Facts.stated`), so no rule reads it as a subject. -/
def EnvUnshown (f : Regula.Load.Facts) (p : Regula.Closed.Profile) : Prop :=
  ∀ x ∈ f.claimedConstants, f.shown x = false →
    ModuleUnreplaced f.env x.1 x.2.1 ∧
    Regula.Load.kindOf x.2.2 = .theorem ∧ Regula.Load.safetyOf x.2.2 = .safe ∧
    (∀ b, x.2.1 ≠ .str b "_unsafe_rec") ∧ (∀ l ∈ loopConstructs, ¬ ValueMentions x.2.2 l) ∧
    ∀ u, Mentions x.2.2 u → (∃ k, f.env.constants.map₁[u]? = some k) ∧
      ∀ a, EnvReaches f u a → EnvAxiom f a → EnvAdmits f p a

/-- What a build must be for the loader and the rules to pass it, in the terms of the {name (full := Regula.Load.Facts)}`Facts` and the roots:
each module of {name}`roots` is claimed, each constant has a module, and the environment has {name}`EnvForm`, {name}`EnvFloor` and
{name}`EnvUnshown`. -/
structure LoadFloor (f : Regula.Load.Facts) (roots : List Name) (p : Regula.Closed.Profile) : Prop where
  /-- Each module of {name}`roots` is claimed. -/
  roots : ∀ r ∈ roots, r ∈ f.claimed
  /-- Each constant has a module. -/
  placed : ∀ n info, f.env.constants.map₁[n]? = some info → ∃ m, f.info? n = some m
  /-- The closed form. -/
  form : EnvForm f
  /-- The floor of the rules. -/
  floor : EnvFloor f p
  /-- What the environment does not show. -/
  unshown : EnvUnshown f p

theorem unread_none_of {i : Regula.Closed.Input}
    (h : ∀ x ∈ f.claimedConstants,
      f.shown x = true ∨ Regula.Load.fitsUnshown f i.tables x.1 x.2.1 x.2.2 = true) :
    f.unread? i.tables = none := by
  simp only [Regula.Load.Facts.unread?, Regula.Load.Facts.unshown, Option.map_eq_none_iff,
    List.find?_eq_none, List.mem_filter, Bool.not_eq_true']
  rintro x ⟨hx, hns⟩; simpa [hns] using h x hx

theorem mapM_error {α β ε : Type} (g : α → Except ε β) (l : List α) (e : ε) (h : l.mapM g = .error e) :
    ∃ a ∈ l, ∃ e', g a = .error e' := by
  induction l generalizing e with
  | nil => simp only [List.mapM_nil, pure, Except.pure, reduceCtorEq] at h
  | cons a l ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hg : g a with
    | error e' => exact ⟨a, List.mem_cons_self, e', hg⟩
    | ok _ =>
      rw [hg] at h
      cases hl : l.mapM g with
      | error e' => obtain ⟨x, hx, hy⟩ := ih e' hl; exact ⟨x, List.mem_cons_of_mem _ hx, hy⟩
      | ok _ => rw [hl] at h; cases h

theorem admitDraft_of_floor (h : LoadFloor f roots p) : ∃ i, f.admitDraft roots p = .ok i := by
  dsimp only [Regula.Load.Facts.admitDraft]
  split
  · rename_i m hf
    exact absurd (List.find?_some hf) (by simp only [List.contains_eq_mem, h.roots m (List.mem_of_find?_eq_some hf), decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true])
  split
  · rename_i _ hcs
    dsimp only [Regula.Load.Facts.csimps] at hcs
    cases hmap : f.claimed.mapM f.moduleCSimps with
    | error _ =>
      obtain ⟨m, hm', _, he'⟩ := mapM_error _ _ _ hmap; obtain ⟨⟨_, hidx⟩, -⟩ := h.floor.2.1 m hm'
      rw [Regula.Load.Facts.moduleCSimps, hidx] at he'; cases he'
    | ok _ => rw [hmap] at hcs; cases hcs
  split
  · rename_i _ hm
    obtain ⟨⟨n, info⟩, hx, _, he⟩ := mapM_error _ _ _ hm
    obtain ⟨_, hmod⟩ := h.placed n info (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hx)
    rw [Regula.Load.Facts.decl, hmod] at he; cases he
  rename_i csimps _ decls hm
  obtain ⟨h1, h2, -⟩ := Regula.Load.mapM_ok
    (fun x : Name × ConstantInfo => f.decl x.1 x.2 (f.stated.getD x.1 []))
    (·.name) (·.1) (fun _ _ hb => f.decl_name hb) _ _ hm
  refine (admit_ok_iff _).mpr ((wf_toSpecDraft_iff _).mpr ⟨fun x hx u hu => ?_, h.form.claims⟩)
  obtain ⟨⟨n, info⟩, hin, hok⟩ := h1 x hx
  obtain ⟨_, -, rfl⟩ := decl_ok hok
  obtain ⟨k, hk⟩ := h.form.closed n u ⟨info, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hin, (mem_usesIn info _ u).mp hu⟩
  obtain ⟨y, hy, hoky⟩ := h2 (u, k) (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk)
  exact ⟨y, hy, f.decl_name hoky⟩

theorem prepare_of_floor (h : LoadFloor f roots p) : ∃ prep, f.prepare roots p = .ok prep := by
  obtain ⟨i', hd⟩ := admitDraft_of_floor h
  have hnone := unread_none_of (i := i') fun x hx =>
    (Bool.eq_false_or_eq_true (f.shown x)).elim .inl
      fun hs => .inr ((fitsUnshown_iff (admitDraft_loaded hd) x).mpr (h.unshown x hx hs))
  exact ⟨⟨i', i'.tables⟩, by simp only [Regula.Load.Facts.prepare, hd, Regula.Load.Facts.checkUnread, hnone]⟩

theorem input_of_floor (h : LoadFloor f roots p) : ∃ i, f.input roots p = .ok i := by
  obtain ⟨prep, hprep⟩ := prepare_of_floor h
  exact ⟨prep.input, by rw [Regula.Load.Facts.input_eq_prepare_map, hprep]; rfl⟩

theorem pass_iff_floor :
    (Regula.Closed.decision (f.input roots p)).verdict = .pass ↔ LoadFloor f roots p := by
  constructor
  · intro h
    obtain ⟨h1, -, _, h4, h5⟩ := pass_floor h
    obtain ⟨i, hi, -⟩ := decision_pass h; have hl := input_loaded hi
    exact ⟨h1, fun _ _ hn => module_of hl hn, h4, h5, fun x hx hs =>
      (input_kept hi hx).elim (fun ht => absurd (hs.symm.trans ht) Bool.false_ne_true) (fitsUnshown_iff hl x).mp⟩
  · intro h; obtain ⟨i, hi⟩ := input_of_floor h; exact hi ▸ (pass_iff hi).mpr ⟨h.form, h.floor⟩

/-! ## The cone that Lean's kernel replays -/

/-- The constants that Lean's kernel builds into a term that it checks, read from its source at v4.36.0: the types of a
literal, what it unfolds a number and a string literal to, and the values of its arithmetic on numbers
({lit}`Lean/Expr.lean:622-624`, {lit}`src/kernel/inductive.cpp:1347-1390`, {lit}`src/kernel/type_checker.cpp:665`,
{lit}`src/library/constants.cpp:12-15`). It is stated here as a literal, apart from the checker's list. -/
def KernelNames : List Name :=
  [`Nat, `String, `Nat.zero, `Nat.succ, `String.ofList, `List.cons, `List.nil, `Char, `Char.ofNat, `Bool.true,
    `Bool.false]

/-- The checker's list is this one, so a change of either fails this proof. -/
theorem kernelNames_eq : Regula.Closed.Input.kernelNames = KernelNames := by rfl

/-- What the constant of a name mentions in the input, and nothing for a name that the input does not hold. -/
def inputMentions (i : Regula.Closed.Input) (n : Name) : List Name :=
  ((i.index[n]?).map (·.uses)).getD []

/-- Where the checker's cone starts: each constant of a claimed module, and each of {name}`seeds`. -/
def inputSeeds (i : Regula.Closed.Input) (seeds : List Name) : List Name :=
  i.claimedDecls.map (·.name) ++ seeds

/-- The checker's cone is the search over what each constant of the input mentions, from those seeds. -/
theorem cone_eq (i : Regula.Closed.Input) (seeds : List Name) :
    i.cone seeds = Regula.Closed.reach (inputMentions i) (i.decls.map (·.uses.length)).sum (inputSeeds i seeds) := by rfl

theorem inputMentions_name (i : Regula.Closed.Input) {d : Regula.Closed.Decl} (hd : d ∈ i.decls) :
    inputMentions i d.name = d.uses := by
  simp [inputMentions, (i.index_eq_some d.name d).mpr ⟨hd, rfl⟩]

theorem reaches_snoc (i : Regula.Closed.Input) {s b c : Name} (h : i.Reaches s b) (hc : c ∈ inputMentions i b) :
    i.Reaches s c := by
  induction h generalizing c with
  | refl b =>
    unfold inputMentions at hc
    cases hget : i.index[b]? with
    | none => simp [hget] at hc
    | some d =>
      obtain ⟨hd, hn⟩ := (i.index_eq_some b d).mp hget
      exact .step d hd hn (by simpa [hget] using hc) (.refl c)
  | step d hd hn hu _ ih => exact .step d hd hn hu (ih hc)

theorem reach_cons {next : Name → List Name} {c u e : Name} (h : Regula.Closed.Reach next u e) (hu : u ∈ next c) :
    Regula.Closed.Reach next c e := by
  induction h with
  | refl => exact .step .refl hu
  | step _ hb ih => exact .step ih hb

theorem reach_inputMentions_iff (i : Regula.Closed.Input) {s x : Name} :
    Regula.Closed.Reach (inputMentions i) s x ↔ i.Reaches s x :=
  ⟨fun h => by induction h with | refl => exact .refl s | step _ hc ih => exact reaches_snoc i ih hc,
   fun h => by induction h with | refl => exact .refl | step _ hd hn hu _ ih =>
     subst hn; exact reach_cons ih ((inputMentions_name i hd).symm ▸ hu)⟩

/-- **The checker's search gives exactly what its seeds reach** through what each constant of the input mentions. -/
theorem mem_cone (i : Regula.Closed.Input) (seeds : List Name) (x : Name) :
    (i.cone seeds).contains x = true ↔ ∃ s ∈ inputSeeds i seeds, i.Reaches s x := by
  rw [cone_eq, Regula.Closed.mem_reach (i.decls.map (·.name)) (inputSeeds i seeds)]
  · simp only [reach_inputMentions_iff]
  · intro n hn
    unfold inputMentions at hn
    cases hget : i.index[n]? with
    | none => simp [hget] at hn
    | some d =>
      obtain ⟨hd, rfl⟩ := (i.index_eq_some n d).mp hget
      exact List.mem_map_of_mem hd
  · rw [List.map_map]
    exact Nat.le_of_eq (congrArg List.sum (List.map_congr_left fun d hd => by simp [inputMentions_name i hd]))

/-- Where the cone of a claim starts, in the terms of the environment: a constant of a claimed module, a name that a claimed
module's own data states ({name}`mem_claimedConstants`), or one of {name}`KernelNames`. -/
def ConeSeed (f : Regula.Load.Facts) (s : Name) : Prop :=
  (∃ info m, f.env.constants.map₁[s]? = some info ∧ f.moduleOf? s = some m ∧ m ∈ f.claimed) ∨
    (∃ m info, (m, s, info) ∈ f.claimedConstants) ∨ s ∈ KernelNames

/-- The cone of the claim, in the terms of the environment: each name that a seed reaches through what the names of the
environment mention ({name}`EnvMentions`). -/
def InCone (f : Regula.Load.Facts) (n : Name) : Prop :=
  ∃ s, ConeSeed f s ∧ EnvReaches f s n

/-- The cone is closed under what its names mention. -/
theorem inCone_mentions {n u : Name} (h : InCone f n) (hm : EnvMentions f n u) : InCone f u := by
  obtain ⟨s, hs, hr⟩ := h
  exact ⟨s, hs, by clear hs; induction hr with | refl => exact .step hm (.refl u) | step h₁ _ ih => exact .step h₁ (ih hm)⟩

theorem index_contains (i : Regula.Closed.Input) (n : Name) :
    i.index.contains n = true ↔ ∃ d ∈ i.decls, d.name = n := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, Option.isSome_iff_exists]
  exact exists_congr fun d => i.index_eq_some n d

theorem mem_inputSeeds (hl : Loaded f roots p i) (s : Name) : s ∈ inputSeeds i f.coneSeeds ↔ ConeSeed f s := by
  simp only [inputSeeds, Regula.Load.Facts.coneSeeds, List.mem_append, List.mem_map,
    Regula.Closed.Input.mem_claimedDecls, ConeSeed, kernelNames_eq]
  refine or_congr ⟨?_, ?_⟩ (or_congr ⟨by rintro ⟨⟨m, _, info⟩, hx, h⟩; exact ⟨m, info, h ▸ hx⟩,
    by rintro ⟨m, info, hx⟩; exact ⟨(m, s, info), hx, rfl⟩⟩ Iff.rfl)
  · rintro ⟨d, ⟨hd, hmod⟩, rfl⟩
    obtain ⟨info, m, hn, hm, hv⟩ := hl.sound d hd
    exact ⟨info, m.name, hn, moduleOf?_eq_some.mpr ⟨m, hm, rfl⟩, hl.modules ▸ (by rw [hv] at hmod; exact hmod)⟩
  · rintro ⟨info, m, hn, hm, hc⟩
    obtain ⟨lm, hlm, rfl⟩ := moduleOf?_eq_some.mp hm
    obtain ⟨_, hlm', hmem⟩ := hl.whole s info hn
    rw [hlm] at hlm'; cases hlm'
    exact ⟨_, ⟨hmem, hl.modules.symm ▸ hc⟩, rfl⟩

/-- **The cone that the checker computes is the cone of the claim**, in the terms of the environment. -/
theorem mem_cone_env (hl : Loaded f roots p i) (n : Name) : (i.cone f.coneSeeds).contains n = true ↔ InCone f n := by
  rw [mem_cone]
  exact exists_congr fun s => and_congr (mem_inputSeeds hl s) (Link.reaches_iff.trans (reaches_env hl s n))

/-- Which constants Lean's replay is given, in other terms than the checker's test: each but a quotient's companion. -/
theorem replays_iff (info : ConstantInfo) :
    Regula.Load.replays info = true ↔ ∀ v, info = .quotInfo v → v.kind = .type := by
  cases info with
  | quotInfo v => rcases v with ⟨_, k⟩; cases k with
    | type => exact ⟨fun _ _ h => (by cases h; rfl), fun _ => rfl⟩ | _ => exact ⟨fun h => (by cases h), fun h => by cases h _ rfl⟩
  | _ => exact ⟨fun _ _ h => (by cases h), fun _ => rfl⟩

theorem replayStep_get (M m : Std.HashMap Name ConstantInfo) (x n : Name) (info : ConstantInfo)
    (hm : ∀ v, m[n]? = some v → M[n]? = some v) :
    (Regula.Load.replayStep M m x)[n]? = some info ↔
      (x = n ∧ M[n]? = some info ∧ Regula.Load.replays info = true) ∨ m[n]? = some info := by
  unfold Regula.Load.replayStep
  have hm' := hm info
  cases hx : M[x]? with
  | none => grind only
  | some k =>
    dsimp only
    split
    · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]; grind only
    · grind only

theorem replayFold_get (M : Std.HashMap Name ConstantInfo) (n : Name) (info : ConstantInfo) :
    ∀ (l : List Name) (init : Std.HashMap Name ConstantInfo), (∀ v, init[n]? = some v → M[n]? = some v) →
      ((l.foldl (Regula.Load.replayStep M) init)[n]? = some info ↔
        (n ∈ l ∧ M[n]? = some info ∧ Regula.Load.replays info = true) ∨ init[n]? = some info)
  | [], _, _ => by simp only [List.foldl_nil, List.not_mem_nil, false_and, false_or]
  | x :: l, init, hinit => by
    have hinv v hv := ((replayStep_get M init x n v hinit).mp hv).elim (·.2.1) (hinit v)
    rw [List.foldl_cons, replayFold_get M n info l _ hinv, replayStep_get M init x n info hinit, List.mem_cons]
    simp only [or_and_right, eq_comm (a := x)]
    rw [or_left_comm, ← or_assoc]

/-- The part of the replay's map that the cone gives. -/
def coneConstants (f : Regula.Load.Facts) (i : Regula.Closed.Input) : Std.HashMap Name ConstantInfo :=
  (i.cone f.coneSeeds).toList.foldl (Regula.Load.replayStep f.env.constants.map₁) {}

theorem mem_coneConstants (f : Regula.Load.Facts) (i : Regula.Closed.Input) (n : Name) (info : ConstantInfo) :
    (coneConstants f i)[n]? = some info ↔
      (i.cone f.coneSeeds).contains n = true ∧ f.env.constants.map₁[n]? = some info ∧
        Regula.Load.replays info = true := by
  rw [coneConstants, replayFold_get _ n info _ {} (by simp only [Std.HashMap.getElem?_empty, reduceCtorEq, false_implies, implies_true])]
  simp only [Std.HashSet.mem_toList, Std.HashSet.contains_iff_mem, Std.HashMap.getElem?_empty, reduceCtorEq, or_false]

/-- The entries of the copies, each under its name. -/
def copyEntries (f : Regula.Load.Facts) : List (Name × ConstantInfo) :=
  f.copies.zipIdx.map (Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁))

theorem replayConstants_eq (f : Regula.Load.Facts) (i : Regula.Closed.Input) :
    f.replayConstants i = (copyEntries f).foldl (fun m x => m.insert x.1 x.2) (coneConstants f i) := by rfl

theorem mem_insertFold (L : List (Name × ConstantInfo)) (hL : (L.map (·.1)).Nodup)
    (base : Std.HashMap Name ConstantInfo) (n : Name) (info : ConstantInfo) :
    (L.foldl (fun m x => m.insert x.1 x.2) base)[n]? = some info ↔
      (n, info) ∈ L ∨ (n ∉ L.map (·.1) ∧ base[n]? = some info) := by
  induction L generalizing base with
  | nil => simp only [List.foldl_nil, List.not_mem_nil, List.map_nil, not_false_eq_true, true_and, false_or]
  | cons a L ih =>
    simp only [List.map_cons, List.nodup_cons] at hL
    rw [List.foldl_cons, ih hL.2, Std.HashMap.getElem?_insert]
    have hnotL : (a.1, info) ∉ L := fun hx => hL.1 (List.mem_map.mpr ⟨_, hx, rfl⟩)
    simp only [List.mem_cons, List.map_cons, beq_iff_eq]
    grind only

theorem depth_zeros (d : Nat) : Regula.Load.depth (Regula.Load.zeros d) = d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Regula.Load.zeros, Regula.Load.depth, ih]

theorem depth_le_fold (l : List Name) (init : Nat) :
    init ≤ l.foldl (fun d n => max d (Regula.Load.depth n)) init ∧
      ∀ x ∈ l, Regula.Load.depth x ≤ l.foldl (fun d n => max d (Regula.Load.depth n)) init := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil, Nat.le_refl, List.not_mem_nil, false_implies, implies_true, and_self]
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih (max init (Regula.Load.depth a))
    simp only [List.foldl_cons]
    exact ⟨Nat.le_trans (Nat.le_max_left _ _) h1,
      fun x hx => (List.mem_cons.mp hx).elim (fun h => by subst h; exact Nat.le_trans (Nat.le_max_right _ _) h1) (h2 x)⟩

/-- **No constant of the environment has the name of a copy**: the root of those names is deeper than each of its names. -/
theorem copy_name_fresh (f : Regula.Load.Facts) (k : Nat) :
    Name.num (Regula.Load.copyRoot f.env.constants.map₁) k ∉ f.env.constants.map₁ := by
  intro hmem
  have hk := (depth_le_fold f.env.constants.map₁.keys 0).2 _ (Std.HashMap.mem_keys.mpr hmem)
  simp only [Regula.Load.copyRoot, Regula.Load.depth, depth_zeros] at hk
  omega

/-- The copies have distinct names. -/
theorem copyEntries_nodup (f : Regula.Load.Facts) : ((copyEntries f).map (·.1)).Nodup := by
  have heq : (copyEntries f).map (·.1) =
      (List.range' 0 f.copies.length).map (Name.num (Regula.Load.copyRoot f.env.constants.map₁)) := by
    rw [← List.zipIdx_map_snd 0 f.copies, List.map_map]
    simp only [copyEntries, List.map_map, Function.comp_def, Regula.Load.copyAt]
  rw [heq]
  exact List.Pairwise.map _ (fun a b hab heq => hab (Name.num.inj heq).2) List.nodup_range'

/-- **What Lean's replay is given**, in the terms of the environment: the constants of the cone of the claim, each as the
environment keeps it, but the companions of {lit}`Quot`, which the kernel adds with it, and the copies, each under a name of its own. -/
theorem replayConstants_env (hl : Loaded f roots p i) (n : Name) (info : ConstantInfo) :
    (f.replayConstants i)[n]? = some info ↔
      (f.env.constants.map₁[n]? = some info ∧ InCone f n ∧ ∀ v, info = .quotInfo v → v.kind = .type) ∨
        (n, info) ∈ copyEntries f := by
  rw [replayConstants_eq, mem_insertFold _ (copyEntries_nodup f), mem_coneConstants, mem_cone_env hl, replays_iff]
  constructor
  · rintro (h | ⟨_, h1, h2, h3⟩); exact .inr h; exact .inl ⟨h2, h1, h3⟩
  · rintro (⟨h2, h1, h3⟩ | h)
    · refine .inr ⟨fun hn => ?_, h1, h2, h3⟩
      obtain ⟨_, hx, rfl⟩ := List.mem_map.mp hn
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact copy_name_fresh f y.2 (Std.HashMap.mem_iff_isSome_getElem?.mpr (by
        show (f.env.constants.map₁[(Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) y).1]?).isSome = true
        rw [h2]; rfl))
    · exact .inl h

/-- **Each theorem of a claimed module is checked**: as its own module's data states it, it is, by {lit}`==`, the constant of its
name that the environment keeps, or the replay is given it under a name of its own, with its type and its value. -/
theorem claimed_theorem_replayed (hl : Loaded f roots p i) {m n : Name} {v : Lean.TheoremVal}
    (hx : (m, n, .thmInfo v) ∈ f.claimedConstants) :
    (f.env.constants.map₁[n]? == some (.thmInfo v)) = true ∨
      ∃ k, (f.replayConstants i)[(Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) (v, k)).1]? =
        some (Regula.Load.copyAt (Regula.Load.copyRoot f.env.constants.map₁) (v, k)).2 := by
  by_cases hk : (f.env.constants.map₁[n]? == some (.thmInfo v)) = true
  · exact .inl hk
  · obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp
      (List.mem_filterMap.mpr ⟨(m, n, .thmInfo v), hx, by simp [hk]⟩ : v ∈ f.copies)
    exact .inr ⟨k, (replayConstants_env hl _ _).mpr
      (.inr (List.mem_map.mpr ⟨(v, k), List.mem_zipIdx_iff_getElem?.mpr hk', rfl⟩))⟩

/-- Each constant of a claimed module is in the cone, so the replay is given it unless it is a quotient's companion. -/
theorem claimed_inCone {n m : Name} {info : ConstantInfo} (hn : f.env.constants.map₁[n]? = some info)
    (hm : f.moduleOf? n = some m) (hc : m ∈ f.claimed) : InCone f n :=
  ⟨n, .inl ⟨info, m, hn, hm, hc⟩, .refl n⟩

end Loader

end RegulaSpecification
