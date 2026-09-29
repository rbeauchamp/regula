module

public import Lean.Elab.Command
public import Lean.Compiler.Old
public import Lean.Compiler.NoncomputableAttr
public import Lean.Compiler.ImplementedByAttr
public import Lean.Compiler.ExternAttr
public import Lean.Compiler.CSimpAttr
public import Lean.Compiler.IR.EmitUtil
public import Lean.DeclarationRange
public import Lean.Elab.PreDefinition.Structural.Main
public import Lean.Elab.PreDefinition.WF.Main
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

/-- The pinned Lean v4.34.0 renderings (`Kernel.Exception.toMessageData`) of the kernel's resource
limits, which `throwKernelException` throws as untagged errors, each with the limit it names. -/
private def kernelLimits : Array (String × String) := #[
  ("(kernel) deterministic timeout", "kernel heartbeats"),
  ("(kernel) deep recursion detected", "kernel recursion depth"),
  ("(kernel) excessive memory consumption detected", "kernel memory")]

/-- The resource limit of the checker's own Lean process that `ex` reports, if any: an elaborator
limit (`Exception.isRuntime`), or a kernel limit recognized by its pinned rendering, also inside an
elaborator error that wraps it (as `Meta.nativeEqTrue` does). Either is the checker's limit, not
evidence about the inspected source. -/
def checkerLimit? (ex : Exception) : BaseIO (Option String) := do
  if ex.isMaxRecDepth then return some "maximum recursion depth"
  if ex.isMaxHeartbeat then return some "maximum heartbeats"
  let text ← ex.toMessageData.toString
  return kernelLimits.findSome? fun (rendering, limit) =>
    if text.contains rendering then some limit else none

/-- The root under which a regeneration names the definitions it adds. -/
private def regenerationRoot : Name := `_regula_regeneration

/-- The arguments of a well-founded fixpoint application that carry its computation: for
`WellFounded.fix α C r hwf F x…` and `WellFounded.Nat.fix α motive h F x…` (the two combinators
Lean 4.34.0's well-founded recursion uses) the domain, the motive, the functional and the
remaining arguments, without the relation `r`, its well-foundedness proof or the measure `h`. -/
private def fixpointArguments? (e : Expr) : Option (Array Expr) :=
  let args := e.getAppArgs
  if e.isAppOf ``WellFounded.fix && args.size ≥ 5 then
    some (#[args[0]!, args[1]!, args[4]!] ++ args.extract 5 args.size)
  else if e.isAppOf ``WellFounded.Nat.fix && args.size ≥ 4 then
    some (#[args[0]!, args[1]!, args[3]!] ++ args.extract 4 args.size)
  else none

/-- Whether `e` is a proof or a type in the current local context: what Lean's code generator
erases. -/
private def erasedByCompilation (e : Expr) : MetaM Bool := do
  return (← Meta.isProof e) || (← Meta.isType e)

/-- Whether `a` and `b` are equal up to compilation erasure: the same expression after every proof
and every type of each side, decided in that side's own local context, is erased, with the
variables they bind paired and each well-founded fixpoint reduced to `fixpointArguments?`. The two
sides then compile to the same code; their recursion, relations and termination proofs may
differ. `fuel` bounds the depth; exhausting it answers `false`. -/
private def equalErased (fuel : Nat) (pairs : Array (FVarId × FVarId)) (a b : Expr) :
    MetaM Bool := do
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    if a == b && !a.hasFVar && !b.hasFVar then return true
    if (← erasedByCompilation a) && (← erasedByCompilation b) then return true
    let all := fun (xs ys : Array Expr) => do
      if xs.size != ys.size then return false
      for i in [:xs.size] do
        unless ← equalErased fuel pairs xs[i]! ys[i]! do return false
      return true
    match a, b with
    | .mdata _ a', _ => equalErased fuel pairs a' b
    | _, .mdata _ b' => equalErased fuel pairs a b'
    | .fvar x, .fvar y => return x == y || pairs.contains (x, y)
    | .const n us, .const m vs => return n == m && us == vs
    | .lit l, .lit l' => return l == l'
    | .sort u, .sort v => return u == v
    | .proj s i e, .proj s' i' e' => return s == s' && i == i' && (← equalErased fuel pairs e e')
    | .app .., .app .. =>
      match fixpointArguments? a, fixpointArguments? b with
      | some xs, some ys => all xs ys
      | none, none =>
        if ← equalErased fuel pairs a.getAppFn b.getAppFn then all a.getAppArgs b.getAppArgs
        else return false
      | _, _ => return false
    | .lam n t body bi, .lam _ t' body' bi' | .forallE n t body bi, .forallE _ t' body' bi' =>
      unless ← equalErased fuel pairs t t' do return false
      Meta.withLocalDecl n bi t fun x => Meta.withLocalDecl n bi' t' fun y =>
        equalErased fuel (pairs.push (x.fvarId!, y.fvarId!)) (body.instantiate1 x)
          (body'.instantiate1 y)
    | .letE n t v body _, .letE _ t' v' body' _ =>
      unless (← equalErased fuel pairs t t') && (← equalErased fuel pairs v v') do return false
      Meta.withLetDecl n t v fun x => Meta.withLetDecl n t' v' fun y =>
        equalErased fuel (pairs.push (x.fvarId!, y.fvarId!)) (body.instantiate1 x)
          (body'.instantiate1 y)
    | _, _ => return false

/-- The definitions a regeneration added to `before` to reach `after`, those named under
`regenerationRoot`, each with its value and with every constant under the root renamed back. -/
private def regeneratedDefinitions (before after : Environment) : Array (Name × Expr) :=
  let unregenerate := fun (n : Name) => n.replacePrefix regenerationRoot .anonymous
  after.constants.map₂.toList.toArray.filterMap fun (name, info) => do
    guard <| name.getRoot == regenerationRoot && !before.contains name
    let .defnInfo regenerated := info | none
    return (unregenerate name, regenerated.value.replace fun
      | .const n us => if n.getRoot == regenerationRoot then some (mkConst (unregenerate n) us)
        else none
      | _ => none)

/-- Whether each regenerated definition equals up to compilation erasure the observed definition of
its name in the current environment; at least one must have been regenerated. -/
private def regenerationMatches (regenerated : Array (Name × Expr)) : MetaM Bool := do
  if regenerated.isEmpty then return false
  for (name, value) in regenerated do
    let some (.defnInfo observed) := (← getEnv).find? name | return false
    unless ← equalErased 100000 #[] value observed.value do return false
  return true

/-- The `wf_preprocess` rules of the running Lean toolchain: the global entries of the modules Lean
loaded from the toolchain's own library directory, recognized by canonical path, since a module's
name does not establish toolchain ownership. Rules a project or dependency adds are left out. -/
private def toolchainPreprocessRules (env : Environment) : IO Meta.SimpTheorems := do
  let ext := Lean.Elab.WF.wfPreprocessSimpExtension
  let libDir ← Lean.getLibDir (← Lean.findSysroot)
  let mut rules ← ext.descr.mkInitial
  for (moduleName, index) in env.header.moduleNames.zipIdx do
    let entries := ext.ext.getModuleEntries env index
    if entries.isEmpty then continue
    let expected := Lean.modToFilePath libDir moduleName "olean"
    unless ← expected.pathExists do continue
    unless (← IO.FS.realPath (← Lean.findOLean moduleName)) == (← IO.FS.realPath expected) do
      continue
    for entry in entries do
      if let .global rule := entry then rules := ext.descr.addEntry rules rule
  return ext.descr.finalizeImport rules

/-- `env` with `registry` holding only the handlers built into the running executable (its
`tableRef`), none that an imported module registered. -/
private def builtinHandlersOnly {γ : Type} (registry : KeyedDeclsAttribute γ)
    (env : Environment) : IO Environment := do
  let builtin := KeyedDeclsAttribute.mkStateOfTable (← registry.tableRef.get)
  return registry.ext.modifyState env fun _ => builtin

/-- The environment a regeneration runs in: `env` with only the toolchain's `wf_preprocess` rules
and only the executable's built-in macros, tactic and term elaborators, so that no rule or syntax
handler of the audited modules or their dependencies takes part. -/
private def regenerationEnvironment (env : Environment) : IO Environment := do
  let rules ← toolchainPreprocessRules env
  let env := Lean.Elab.WF.wfPreprocessSimpExtension.modifyState env fun _ => rules
  let env ← builtinHandlersOnly macroAttribute env
  let env ← builtinHandlersOnly Lean.Elab.Tactic.tacticElabAttribute env
  builtinHandlersOnly Lean.Elab.Term.termElabAttribute env

/-- `Declaration.unsafeRecRegenerated`: rerun Lean's own recursion compiler on the helper's group,
each helper's value becoming the body of a fresh definition under `regenerationRoot` with its calls
to the group's helpers standing for the recursive calls, and compare what it generates with the
observed base and its auxiliary definitions (`regenerationMatches`). Structural recursion is tried
first, with no hint; then well-founded recursion, with Lean's measure inference and every
decreasing proof elided (`all_goals exact sorry`, on the raw goal), since the comparison erases
proofs and the observed base's own kernel-checked value supplies them. The compiler runs in
`regenerationEnvironment`. A regeneration that reports an error does not count. Every change is
undone before the comparison, which reads the observed definitions and decides erasure in the
inspected environment: whatever code runs during a regeneration, only the definitions it adds are
compared. A `checkerLimit?` reached is rethrown. -/
private def unsafeRecRegeneration (env : Environment) (name : Name) (info : ConstantInfo) :
    CommandElabM (Option RecursionOrigin) := do
  let some _ := Lean.Compiler.isUnsafeRecName? name | return none
  let .defnInfo helper := info | return none
  let group := helper.all.toArray
  let some bases := group.mapM (fun member => do
      let base ← Lean.Compiler.isUnsafeRecName? member
      guard <| (env.find? member).any (· matches ConstantInfo.defnInfo _)
      guard <| (env.find? base).any (· matches ConstantInfo.defnInfo _)
      pure base)
    | return none
  let rename := fun (value : Expr) => value.replace fun
    | .const n us => (group.idxOf? n).map fun i => mkConst (regenerationRoot ++ bases[i]!) us
    | _ => none
  liftTermElabM do
    let preDefs ← group.mapIdxM fun i member => do
      let some (.defnInfo value) := env.find? member | throwError "missing helper {member}"
      return ({ ref := .missing, kind := .def, levelParams := value.levelParams, modifiers := {},
                declName := regenerationRoot ++ bases[i]!, binders := .missing, type := value.type,
                value := rename value.value, termination := .none } : PreDefinition)
    let noMeasures := preDefs.map fun _ => (none : Option TerminationMeasure)
    let regenerating ← regenerationEnvironment (← getEnv)
    let attempt (run : TermElabM Unit) : TermElabM Bool := do
      let saved ← saveState
      let regenerated ← try
          Core.resetMessageLog
          setEnv regenerating
          withOptions (·.setBool `debug.rawDecreasingByGoal true) run
          let failed := (← Core.getMessageLog).hasErrors
          let after ← getEnv
          saved.restore
          pure (if failed then #[] else regeneratedDefinitions regenerating after)
        catch ex =>
          saved.restore
          if (← checkerLimit? ex).isSome then throw ex
          pure #[]
      regenerationMatches regenerated
    let docCtx := (← getLCtx, ← Meta.getLocalInstances)
    if ← attempt (structuralRecursion docCtx preDefs noMeasures) then return some .structural
    let elided ← `(Lean.Parser.Tactic.tacticSeq| all_goals exact sorry)
    let wfDefs := preDefs.map fun (preDef : PreDefinition) =>
      { preDef with termination := { TerminationHints.none with
          decreasingBy? := some ({ ref := .missing, tactic := elided } : DecreasingBy) } }
    if ← attempt (wfRecursion docCtx wfDefs noMeasures) then return some .wellFounded
    return none

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
declaration it creates. This remains compiler evidence, never a kernel proof. A failed replay
is `false`; a `checkerLimit?` reached during it is rethrown. -/
private def replayNative (asserted : Expr) : CommandElabM Bool :=
  liftTermElabM <| withoutModifyingEnv do
    try
      return match ← Meta.nativeEqTrue `audit_native_replay asserted with
        | .success _ => true
        | .notTrue   => false
    catch ex =>
      if (← checkerLimit? ex).isSome then throw ex
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
  let importsAware (aware : Array Bool) (index : Nat) : Bool :=
    match env.header.moduleData[index]? with
    | some data => data.imports.any fun imported =>
        ((env.getModuleIdx? imported.module).bind fun idx => aware[(idx : Nat)]?).getD false
    | none => false
  let mut aware := names.map (· == `Regula.Contract)
  for _ in [:names.size] do
    let mut changed := false
    for index in [:names.size] do
      if !(aware[index]?.getD true) && importsAware aware index then
        aware := aware.set! index true
        changed := true
    if !changed then break
  return { aware
           mainAware := (env.getModuleIdx? `Regula.Contract).isSome ||
             env.mainModule == `Regula.Contract
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
  /-- A declaration of the trusted environment probe: the record also carries the regeneration
  of a recursion helper and the native-decision evidence that replay needs. -/
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
  let unsafeRecRegenerated ← if stage == .replayCandidate then
      unsafeRecRegeneration env name info else pure none
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
    unsafeRecRegenerated
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
  if names.isEmpty then return #[]
  let scope ← ContractScope.new env
  names.mapM (declaration · .snapshot scope)

end Regula.Collect
