module

public import Lean.Elab.Command
public import Lean.Compiler.Old
public import Lean.Compiler.NoncomputableAttr
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.CSimpAttr
public import Lean.Compiler.IR.EmitUtil
public import Lean.DeclarationRange
public import Lean.Elab.PreDefinition.Structural.Eqns
public import Lean.Elab.PreDefinition.WF.Eqns
public import Lean.Meta.Match.MatcherInfo
public import Lean.Meta.Native
public import RegulaPolicy.NativeAxiom
public import Lean.Meta.Eqns
public import Lean.Meta.RecExt
public import Lean.ProjFns
public import Lean.Util.FoldConsts
public import RegulaPolicy.Domain
public import Regula.Contract

public import Lean.Linter.Util
public import Lean.Linter.EnvLinter.Frontend

/-! # Lean-native observation construction

Shared Lean-native observation construction for local feedback and imported
project inspection. Reuses Lean 4 declaration, axiom and linter inventory APIs.
Snapshot observations omit expensive replay; no observation is a role authorization. -/

public section

namespace Regula.Collect
open Lean Elab Command
open RegulaPolicy (DeclarationKind BoundaryKind Correspondence Safety Reducibility RecursionOrigin
  NativeTactic)

/-- Constant kind of a declaration, as reported by the environment. Public so
the checker self-test can apply `Policy.declarationNeedsTranscript` to raw
module constant records with the identical kind mapping. -/
def kindOf : ConstantInfo → DeclarationKind
  | .axiomInfo _   => .«axiom»
  | .defnInfo _    => .«definition»
  | .thmInfo _     => .«theorem»
  | .opaqueInfo _  => .«opaque»
  | .ctorInfo _    => .«constructor»
  | .inductInfo _  => .«inductive»
  | .recInfo _     => .«recursor»
  | .quotInfo _    => .«quotient»

/-- Compact source position used in declaration-range evidence. -/
private def positionReport (p : Lean.Position) : RegulaPolicy.Position :=
  { line := p.line, column := p.column }

/-- Typed encoding of one exact Lean declaration range. -/
private def rangeReport (r : DeclarationRange) : RegulaPolicy.Range :=
  { start := positionReport r.pos
    «end» := positionReport r.endPos
    startUtf16 := r.charUtf16
    endUtf16 := r.endCharUtf16 }

/-- Typed encoding of full and selection declaration ranges. -/
private def rangesReport (r : DeclarationRanges) : RegulaPolicy.Ranges :=
  { range := rangeReport r.range
    selectionRange := rangeReport r.selectionRange }

private def hintsString : ReducibilityHints → Reducibility
  | .opaque    => .«opaque»
  | .abbrev    => .«abbrev»
  | .regular _ => .«regular»

/-- Kernel value of a definition/theorem/opaque declaration when present. -/
private def valueOf? : ConstantInfo → Option Expr
  | .defnInfo value   => some value.value
  | .thmInfo value    => some value.value
  | .opaqueInfo value => some value.value
  | _                 => none

/-- Retrieve the original built-in recursion predefinition for a safe base. -/
private def recursionPredefinition? (env : Environment) (baseName : Name) :
    Option (RecursionOrigin × List Name × Expr × Array Name) :=
    match Lean.Elab.Structural.eqnInfoExt.find? env baseName with
    | some info => some (.structural, info.levelParams, info.value, info.declNames)
    | none => match Lean.Elab.WF.eqnInfoExt.find? env baseName with
      | some info => some (.wellFounded, info.levelParams, info.value, info.declNames)
      | none => none

/-- Reconstruct the exact executable body transformation used by Lean 4.34.0's
`addAndCompilePartialRec` from the built-in recursion equation metadata. -/
private def unsafeRecExpected? (env : Environment) (baseName : Name) :
    Option (RecursionOrigin × Expr) := do
  let (origin, _, value, group) ← recursionPredefinition? env baseName
  let expected := value.replace fun expr => match expr with
    | .const name levels =>
        if group.contains name then
          some <| mkConst (Lean.Compiler.mkUnsafeRecName name) levels
        else none
    | _ => none
  return (origin, expected)

/-- Whether the head of `e` alone makes it a proof: an application of a theorem. The kernel admits
a theorem only when its type is a proposition (`KernelException.thmTypeIsNotProp`), and applying a
proof of a Π-proposition to arguments yields a proof. -/
private def theoremApplication (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const name _ => (env.find? name).any (·.isTheorem)
  | _ => false

/-- A definitional equality established structurally, without reduction: `t` and `s` are equal up
to metadata, to `let` against `have`, and to proof irrelevance where a proof replaces another. The
predefinition Lean stores for a recursive base has each nested proof abstracted into an
auxiliary theorem (`abstractNestedProofs`), while the compiler helper keeps the proof inline, so
this is the difference the two values show.

`typed` means that the shared context fixes the position's type identically on both sides: an
argument of an identical constant or variable head after congruent arguments, a `let` value, or
the body of a binder at such a position. There a theorem application on either side is a proof of
that proposition, so when both terms are well-typed the other side is a proof of the same
proposition and the two are definitionally equal by proof irrelevance. Everywhere else it compares
by congruence. It recurses structurally on `t`, so no Lean resource limit applies, and it descends
only where the terms are not already equal, visiting a shared subterm once per occurrence. A
`false` result only means that this comparison did not establish the equality. -/
private def congruentUpToProofs (env : Environment) : (typed : Bool) → (t s : Expr) → Bool
  | typed, t, s =>
    let s := s.consumeMData
    if t == s then true
    else if typed && (theoremApplication env t || theoremApplication env s) then true
    else match t with
      | .mdata _ t => congruentUpToProofs env typed t s
      | .app f a => match s with
        | .app g b =>
          congruentUpToProofs env false f g &&
            congruentUpToProofs env (f.getAppFn.isConst || f.getAppFn.isFVar ||
              f.getAppFn.isBVar) a b
        | _ => false
      | .lam _ domain body _ => match s with
        | .lam _ domain' body' _ =>
          congruentUpToProofs env false domain domain' && congruentUpToProofs env typed body body'
        | _ => false
      | .forallE _ domain body _ => match s with
        | .forallE _ domain' body' _ =>
          congruentUpToProofs env false domain domain' && congruentUpToProofs env false body body'
        | _ => false
      | .letE _ type value body _ => match s with
        | .letE _ type' value' body' _ =>
          congruentUpToProofs env false type type' && congruentUpToProofs env true value value' &&
            congruentUpToProofs env typed body body'
        | _ => false
      | .proj structName index struct => match s with
        | .proj structName' index' struct' =>
          structName == structName' && index == index' &&
            congruentUpToProofs env false struct struct'
        | _ => false
      | _ => false

/-- Independently require a kernel-checked unfolding theorem with exactly the
one-step equation reconstructed from the same built-in predefinition. Its definitional comparison
is `congruentUpToProofs`, which does not reduce. A failure to obtain or build the equation,
including a Lean resource limit reached while doing so, leaves both observations `false`. -/
private def unsafeRecEquationEvidence (env : Environment) (name : Name) :
    CommandElabM (Option (Bool × Bool × Array Name)) := do
  let some baseName := Lean.Compiler.isUnsafeRecName? name | return none
  let some (_, levelParams, value, _) := recursionPredefinition? env baseName
    | return none
  liftTermElabM <| withoutModifyingEnv do
    tryCatchRuntimeEx (do
      let some equationName ← Meta.getUnfoldEqnFor? baseName
        | return some (false, false, #[])
      let some equationInfo := (← getEnv).find? equationName
        | return some (false, false, #[])
      let expectedType ← Meta.lambdaTelescope value fun args body => do
        let lhs := mkAppN (mkConst baseName (levelParams.map mkLevelParam)) args
        let equality ← Meta.mkEq lhs body
        Meta.letToHave (← Meta.mkForallFVars args equality)
      let definitional := congruentUpToProofs (← getEnv) false equationInfo.type expectedType
      let axioms ← collectAxioms equationName
      return some (equationInfo.type == expectedType, definitional, axioms))
      fun _ => return some (false, false, #[])

/-- Whether a helper's entire value is the pinned compiler transformation of
the built-in structural/well-founded predefinition stored for its safe base: exactly, and
definitionally by `congruentUpToProofs`. `Meta.isDefEq` is not used: where the values differ
under a recursive call, its lazy delta reduction unfolds the self-referential helper on both sides
before comparing arguments, and each unfolding reproduces the same comparison one call deeper. -/
private def unsafeRecValueEvidence (env : Environment) (name : Name)
    (info : ConstantInfo) : Option (RecursionOrigin × Bool × Bool) := do
  let baseName ← Lean.Compiler.isUnsafeRecName? name
  let (origin, expected) ← unsafeRecExpected? env baseName
  let .defnInfo helper := info | none
  return (origin, helper.value == expected, congruentUpToProofs env false helper.value expected)

/-- The Boolean expression `e` of a type `e = true`. -/
private def assertedBool? (type : Expr) : Option Expr := do
  let args := type.getAppArgs
  guard <| type.getAppFn.isConstOf ``Eq
  guard <| args.size == 3
  guard <| args[0]!.isConstOf ``Bool
  guard <| args[2]!.isConstOf ``Bool.true
  return args[1]!

/-- `Std.Tactic.BVDecide.Reflect.verifyBVExpr`, the check `bv_decide` evaluates natively. -/
private def verifyBVExprName : Name := `Std.Tactic.BVDecide.Reflect.verifyBVExpr

/-- The asserted Boolean expression of a generated native-proof axiom, when it has the exact
shape its tactic produces: `Decidable.decide p inst` (`elabNativeDecideCore`), or
`verifyBVExpr expr cert` over the same run's `_expr_def` and `_cert_def` definitions
(`LratCert.toReflectionProof`). The tactic comes from the name (`nativeAxiomOrigin?`). -/
def nativeAsserted? (name : Name) (type : Expr) : Option (Name × NativeTactic × Expr) := do
  let (parent, tactic) ← RegulaPolicy.nativeAxiomOrigin? name
  let asserted ← assertedBool? type
  match tactic with
  | .nativeDecide | .decideNative => guard <| asserted.isAppOfArity ``Decidable.decide 2
  | .bvDecide =>
      guard <| asserted.isAppOfArity verifyBVExprName 2
      guard <| ([asserted.appFn!.appArg!, asserted.appArg!].zip tactic.auxiliaryInfixes).all
        fun (argument, kind) => argument.isConst &&
          RegulaPolicy.generatedAuxParent? kind argument.constName! == some parent
  return (parent, tactic, asserted)

/-- `Declaration.nativeStatement` and `AddedDeclaration.nativeStatement`: the `repr` of the
asserted expression, naming each auxiliary definition of the same tactic run by its unindexed
base, so a fresh transcript and a build that index generated names differently agree. -/
def nativeStatement? (name : Name) (type : Expr) : Option String := do
  let (parent, tactic, asserted) ← nativeAsserted? name type
  let unindexed := asserted.replace fun
    | .const constant levels => tactic.auxiliaryInfixes.findSome? fun kind =>
        if RegulaPolicy.generatedAuxParent? kind constant == some parent then
          some (mkConst (Name.mkStr parent kind) levels)
        else none
    | _ => none
  return toString (repr unindexed)

/-- Independently replay the Boolean native evaluation without retaining any
declaration it creates. This remains compiler evidence, never a kernel proof. -/
private def replayNative (asserted : Expr) : CommandElabM Bool := do
  try
    let result ← liftTermElabM <| withoutModifyingEnv do
      Meta.nativeEqTrue `audit_native_replay asserted
    return match result with
      | .success _ => true
      | .notTrue   => false
  catch _ =>
    return false

/-- Classify the terminal result after Lean reduction, including aliases of
function types and universes. Runtime roots cannot return erased types. -/
def returnsSort (type : Expr) : MetaM Bool :=
  Meta.withTransparency .all <|
    Meta.forallTelescopeReducing type (fun _ body => pure body.isSort) (whnfType := true)

/-- The part of an environment whose declarations can mention `Regula.ExecutableContract`, with a
memo of constants shown not to reach it. Lean admits a constant only when every constant its type
and value mention is already in the environment, so no constant of a module that is neither
`Regula.Contract` nor a transitive importer of it mentions the contract type, and neither does
any constant such a constant mentions. -/
structure ContractScope where
  /-- For each imported module index: `Regula.Contract` or a module that transitively imports it. -/
  aware : Array Bool
  /-- Whether the current module's own constants can mention it: the current module imports
  every module of the header. -/
  mainAware : Bool
  /-- Constants whose closure under `unfoldReferences` was searched without reaching it. -/
  free : IO.Ref NameSet

/-- The scope of `env`. Awareness is the least fixed point of "is `Regula.Contract` or imports an
aware module": a pass that marks nothing has reached it, and every other pass marks one of the
finitely many modules, so at most one pass per module runs. -/
def ContractScope.new (env : Environment) : BaseIO ContractScope := do
  let names := env.header.moduleNames
  let indices : NameMap Nat :=
    (names.foldl (fun (map, index) name => (map.insert name index, index + 1))
      (({} : NameMap Nat), 0)).1
  let importsAware (aware : Array Bool) (index : Nat) : Bool :=
    match env.header.moduleData[index]? with
    | some data => data.imports.any fun imported =>
        ((indices.find? imported.module).bind (aware[·]?)).getD false
    | none => false
  let mut aware := names.map (· == `Regula.Contract)
  for _ in [:names.size] do
    let mut changed := false
    for index in [:names.size] do
      if !(aware[index]?.getD true) && importsAware aware index then
        aware := aware.set! index true
        changed := true
    if !changed then break
  return { aware, mainAware := names.contains `Regula.Contract || env.mainModule == `Regula.Contract
           free := ← IO.mkRef {} }

/-- Whether `name` belongs to an aware module; a constant whose module index is unknown counts as
aware, so the search expands it. -/
def ContractScope.constantAware (scope : ContractScope) (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index => scope.aware[(index : Nat)]?.getD true
  | none => scope.mainAware

/-- The constants that unfolding `info` can introduce: those its type and value mention (a
theorem's and an opaque constant's too, since reduction at `.all` transparency unfolds theorems),
the constructors of an inductive and of a recursor's rules, and its smart-unfolding definition. -/
private def unfoldReferences (env : Environment) (info : ConstantInfo) : Array Name :=
  let mentioned := info.type.getUsedConstants ++
    ((info.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
  let structural := match info with
    | .inductInfo value => value.ctors.toArray
    | .recInfo value =>
      value.rules.foldl (fun names rule => (names.push rule.ctor) ++ rule.rhs.getUsedConstants) #[]
    | _ => #[]
  let smart := Lean.Meta.mkSmartUnfoldingNameFor info.name
  mentioned ++ structural ++ (if env.contains smart then #[smart] else #[])

/-- Whether reducing `type` can produce `Regula.ExecutableContract`: whether the contract type is
among the constants `type` mentions, closed under `unfoldReferences`. Lean's reduction steps
(delta, iota, beta, zeta, eta, projection, smart unfolding, and literal and native Boolean or
natural-number steps) introduce only constants of that closure or of `Init`, which does not import
`Regula.Contract`. Constants of modules outside the scope are not expanded, and a search that ends
without finding the contract type records every constant it expanded as free. -/
def ContractScope.mayReach (scope : ContractScope) (env : Environment) (type : Expr) :
    BaseIO Bool := do
  let free ← scope.free.get
  let mut pending := type.getUsedConstants
  let mut expanded : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if name == ``Regula.ExecutableContract then return true
    if expanded.contains name || free.contains name || !scope.constantAware env name then continue
    expanded := expanded.insert name
    if let some info := env.find? name then
      pending := pending ++ unfoldReferences env info
  scope.free.modify fun free => expanded.foldl (fun free name => free.insert name) free
  return false

/-- Recognize a closed proof-bearing requirement by its elaborated type. No
annotation, theorem-name inventory, or proposition matcher supplies evidence:
the `ExecutableContract` constructor requires the exact proposition in Lean.
The promised implementation must be a constant, not a partial application or
an existential proof. Its execution closure is inspected even if it is private.
The interface's own constructor is not a registration: `mk` is excluded by kind, and its
definitional twin, the flat constructor Lean generates with the structure
(`Lean.mkFlatCtorOfStructCtorName`), by exact name.
The type is reduced at `.all` transparency only when `ContractScope.mayReach` admits that the
reduction can produce the contract type; otherwise the declaration is not a registration, with no
reduction. Lean's elaboration never reduces a declared type this way, and doing so can exhaust
Lean's resource limits on an ordinary proposition, such as one computed from 64-bit literals.
-/
private def executableContract? (env : Environment) (scope : ContractScope) (info : ConstantInfo) :
    CommandElabM (Option RegulaPolicy.ExecutableContract) := do
  if !#[DeclarationKind.definition, .theorem, .opaque].contains (kindOf info) then return none
  if info.name == Lean.mkFlatCtorOfStructCtorName ``Regula.ExecutableContract.mk then return none
  unless (← scope.mayReach env info.type) do return none
  liftTermElabM <| Meta.withTransparency .all <|
    Meta.forallTelescopeReducing info.type (whnfType := true) fun parameters type => do
    if !type.isAppOfArity ``Regula.ExecutableContract 3 then return none
    let args := type.getAppArgs
    let implementation := args[1]!
    let requirement ← Meta.ppExpr (mkApp args[2]! implementation)
    let root := implementation.constName?
    let failure ← if !parameters.isEmpty then
        pure <| some "registration must be closed; put the implementation's complete domain inside \
          its predicate"
      else match root with
      | none => pure <| some "implementation must be a named constant with its complete domain"
      | some name => do
        let some target := env.find? name
          | pure (some "implementation is missing from the environment")
        if Lean.isNoncomputable env name then
          pure <| some "promised implementation is noncomputable"
        else if target.isUnsafe || target.isPartial then
          pure <| some "promised implementation is unsafe or partial"
        else if !(← Meta.isProp target.type) &&
              (kindOf target == .definition || kindOf target == .opaque) then
          let typeProducing ← returnsSort target.type
          pure <| if typeProducing then
              some "promised implementation returns a type, not runtime data" else none
        else pure <| some "promised implementation is not an executable data/function definition"
    return some {
      root := root.getD .anonymous
      requirement := toString requirement
      failure }

/-- Acquisition stage, independent of whether a subsequent policy check succeeds.
Local snapshots deliberately omit replay and whole-environment parent searches. -/
inductive Stage where
  /-- A local editor snapshot of the current command: the record without the replay-only
  observations. -/
  | snapshot
  /-- A declaration of the trusted environment probe: the record also gathers the
  `unsafe rec` value and equation evidence and the native-decision evidence that replay needs. -/
  | replayCandidate
  deriving DecidableEq, Inhabited

/-- Exact module attribution, including declarations added by the current document.
A missing imported index is not by itself evidence of current-module ownership. -/
def moduleOf (env : Environment) (name : Name) : Except String Name := do
  if let some idx := env.getModuleIdxFor? name then
    let some entry := env.header.modules[(idx : Nat)]?
      | throw "declaration has an invalid imported module index"
    return entry.module
  unless env.constants.map₂.contains name && env.mainModule != .anonymous do
    throw s!"declaration {name} has no established module ownership"
  return env.mainModule

/-- Construct the canonical record from this command's actual environment.
Replay candidates still require the existing fresh transcript and admission guards;
these observations alone never authorize a generated role. A caller recording several declarations
of one environment passes one `ContractScope.new` of it, so its memo is shared; without one, a
fresh scope is built. -/
def declaration (name : Name) (stage : Stage) (scope? : Option ContractScope := none) :
    CommandElabM RegulaPolicy.Declaration := do
  let env ← getEnv
  let scope ← match scope? with
    | some scope => pure scope
    | none => ContractScope.new env
  let some info := env.find? name | throwError "declaration {name} is unavailable"
  let moduleName ← IO.ofExcept (moduleOf env name)
  let axioms ← collectAxioms name
  let isProp ← liftTermElabM <| Meta.isProp info.type
  let prettyType ← liftTermElabM do
    return toString (← Meta.ppExpr info.type)
  let ranges? ← findDeclarationRangesCore? name
  let recursive ← liftTermElabM <| Meta.isRecursiveDefinition name
  let unsafeRecValueEvidence? := if stage == .replayCandidate then
      unsafeRecValueEvidence env name info else none
  let unsafeRecEquationEvidence? ← if stage == .replayCandidate then
      unsafeRecEquationEvidence env name else pure none
  let native? := if stage == .replayCandidate then nativeAsserted? name info.type else none
  let nativeReplay? ← native?.mapM fun (_, _, asserted) => replayNative asserted
  let levelParams : List Name := info.levelParams
  let all : List Name :=
    match info with
    | .defnInfo value   => value.all
    | .thmInfo value    => value.all
    | .opaqueInfo value => value.all
    | _                 => []
  let hints : Option Reducibility :=
    match info with
    | .defnInfo value => some (hintsString value.hints)
    | _               => none
  let valueConstants : Array Name :=
    match valueOf? info with
    | some value => value.getUsedConstants
    | none       => #[]
  return {
    name := name
    «module» := moduleName
    kind := kindOf info
    «type» := toString (repr info.type)
    prettyType
    isProp
    isUnsafe := info.isUnsafe
    isPartial := info.isPartial
    safety := if info.isPartial then some .partial
      else if info.isUnsafe then some .unsafe else none
    «instance» := Lean.Meta.isInstanceCore env name
    «noncomputable» := Lean.isNoncomputable env name
    implementedBy := (Lean.Compiler.getImplementedBy? env name)
    «extern» := Lean.isExtern env name
    internal := name.isInternal
    «private» := Lean.isPrivateName name
    projection := env.isProjectionFn name
    matcher := Lean.Meta.isMatcherCore env name
    recursive
    unsafeRecBase := (Lean.Compiler.isUnsafeRecName? name)
    levelParams := levelParams.toArray
    all := all.toArray
    hints
    valueConstants := RegulaPolicy.canonicalNames valueConstants
    unsafeRecValueOrigin := unsafeRecValueEvidence?.map fun (origin, _, _) => origin
    unsafeRecValueExact := unsafeRecValueEvidence?.map fun (_, exact, _) => exact
    unsafeRecValueDefeq := unsafeRecValueEvidence?.map fun (_, _, value) => value
    unsafeRecEquationExact := unsafeRecEquationEvidence?.map fun (exact, _, _) => exact
    unsafeRecEquationDefeq := unsafeRecEquationEvidence?.map fun (_, value, _) => value
    unsafeRecEquationAxioms := unsafeRecEquationEvidence?.map fun (_, _, values) =>
      RegulaPolicy.canonicalNames values
    nativeStatement := nativeStatement? name info.type
    nativeReplay := nativeReplay?
    ranges := ranges?.map rangesReport
    axioms := RegulaPolicy.canonicalNames axioms
    executableContract := ← executableContract? env scope info
  }

/-- Complete current-module inventory, with no visibility or generated-name filter.
Uses Lean's own local constant map through its environment-linter API. The caller
must separately establish completion of elaboration before claiming completion. -/
def currentModule (stage : Stage := .snapshot) : CommandElabM (Array RegulaPolicy.Declaration) := do
  let scope ← ContractScope.new (← getEnv)
  (← liftCoreM Lean.Linter.EnvLinter.getDeclsInCurrModule).mapM (declaration · stage scope)

/-- Declaration binders recorded in this command's information trees. This is a
local feedback selection, not a complete module census: elaborators can add
constants without binder information. `currentModule` covers those as well. -/
def commandDeclarations : CommandElabM (Array RegulaPolicy.Declaration) := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for tree in (← get).infoState.trees do
    for name in Lean.Linter.getNewDecls tree do
      -- Information trees can retain binders from disposable elaborator
      -- environments (for example run_cmd's temporary evaluator). Intersect
      -- with actual current declarations before constructing observations.
      if (env.getModuleIdxFor? name).isNone && (env.find? name).isSome &&
          !names.contains name then names := names.push name
  let scope ← ContractScope.new env
  names.mapM (declaration · .snapshot scope)

end Regula.Collect
