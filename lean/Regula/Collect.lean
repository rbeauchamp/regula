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
public import Lean.Meta.Injective
public import Lean.Meta.SameCtorUtils
public import Lean.Meta.Constructions.CtorElim
public import Lean.Class
public import Lean.Elab.PreDefinition.Structural.Eqns
public import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
public import Lean.Server.Rpc.RequestHandling
public import RegulaPolicy.GeneratedFamily
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

/-- Whether `value` mentions a constant of `theorems`. -/
private def mentionsTheorem (theorems : NameMap TheoremVal) (value : Expr) : Bool :=
  (value.find? fun e => e.isConst && theorems.contains e.constName!).isSome

/-- `value` with every constant of `theorems` replaced by that theorem's value at the constant's
universe levels, in at most `passes` passes over it; `none` if it still mentions one after them. A
theorem Lean admitted mentions only theorems admitted before it, so one pass per theorem
suffices. -/
private def unfoldTheorems (theorems : NameMap TheoremVal) (passes : Nat) (value : Expr) :
    Option Expr :=
  if !mentionsTheorem theorems value then some value
  else match passes with
    | 0 => none
    | passes + 1 => unfoldTheorems theorems passes <| value.replace fun
        | .const n us => (theorems.find? n).map fun auxiliary =>
            auxiliary.value.instantiateLevelParams auxiliary.levelParams us
        | _ => none

/-- What `unfoldTheorems` returns mentions no constant of `theorems`, for every map, pass count and
value: the names of the unfolded theorems take no part in whatever reads the result. This states
nothing about `Expr.replace` or about the theorems' values. -/
private theorem unfoldTheorems_free (theorems : NameMap TheoremVal) (passes : Nat)
    (value result : Expr) (unfolded : unfoldTheorems theorems passes value = some result) :
    mentionsTheorem theorems result = false := by
  induction passes generalizing value with
  | zero =>
    unfold unfoldTheorems at unfolded
    split at unfolded <;> simp_all
  | succ passes ih =>
    unfold unfoldTheorems at unfolded
    split at unfolded
    · simp_all
    · exact ih _ unfolded

/-- The definitions a regeneration added to `before` to reach `after`, those named under
`regenerationRoot`, each with its value: every theorem the regeneration added is replaced by its
value (`unfoldTheorems`), and every other constant it added under the root is renamed back; a
constant of `before`, under the root or not, keeps its name. `none` if a theorem is left.

An added theorem is a proof Lean abstracted from a regenerated value. Lean names it from a counter
and from a cache of the propositions already abstracted in the same process, which no `.olean`
stores (`Meta.mkAuxLemma`), and privately where a `module` file does not export the body
(`DeclNameGenerator.mkUniqueName`). The observed declarations therefore need not hold a theorem of
the regenerated name and type: Lean may have reused an earlier declaration's, numbered its own
differently, or named it privately. Replacing each by its value leaves none of these names in the
unfolded value (`unfoldTheorems_free`, which does not cover the renaming that follows), and the
comparison erases the proof itself. -/
private def regeneratedDefinitions (before after : Environment) : Option (Array (Name × Expr)) := do
  let unregenerate := fun (n : Name) => n.replacePrefix regenerationRoot .anonymous
  let added := after.constants.map₂.toList.filter fun (name, _) => !before.contains name
  let theorems : NameMap TheoremVal := added.foldl (init := {}) fun theorems (name, info) =>
    match info with
    | .thmInfo auxiliary => theorems.insert name auxiliary
    | _ => theorems
  let renamed := NameSet.ofList <| added.filterMap fun (name, _) =>
    if name.getRoot == regenerationRoot && !theorems.contains name then some name else none
  added.toArray.filterMapM fun (name, info) => do
    let .defnInfo regenerated := info | return none
    unless renamed.contains name do return none
    let value ← unfoldTheorems theorems theorems.size regenerated.value
    return some (unregenerate name, value.replace fun
      | .const n us => if renamed.contains n then some (mkConst (unregenerate n) us) else none
      | _ => none)

/-- Whether each regenerated definition equals up to compilation erasure the observed definition of
its name in the current environment; at least one must have been regenerated. -/
private def regenerationMatches (regenerated : Array (Name × Expr)) : MetaM Bool := do
  if regenerated.isEmpty then return false
  for (name, value) in regenerated do
    let some (.defnInfo observed) := (← getEnv).find? name | return false
    unless ← equalErased 100000 #[] value observed.value do return false
  return true

/-- The relation of a well-founded fixpoint, as `WF.mkFix` of Lean 4.34.0 takes it: `w` of
`WellFounded.fix α C w.1 hwf F`, and `invImage h Nat.lt_wfRel` of `WellFounded.Nat.fix α motive h
F`, the one form of relation from which `mkFix` builds that fixpoint. -/
private def fixpointRelation? (e : Expr) : Option Expr :=
  let args := e.getAppArgs
  if e.isAppOfArity ``WellFounded.Nat.fix 4 then
    match e.getAppFn with
    | .const _ [u, _] => some <| mkApp4 (.const ``invImage [u, 1]) args[0]! (mkConst ``Nat)
        args[2]! (mkConst ``Nat.lt_wfRel)
    | _ => none
  else if e.isAppOfArity ``WellFounded.fix 5 then
    match args[2]! with
    | .proj ``WellFoundedRelation 0 relation => some relation
    | _ => none
  else none

/-- Lean 4.34.0's `wfRecursion` up to the definitions it adds, with one change: the relation is
the observed base's own. Where `wfRecursion` elaborates a relation from termination measures
(`WF.elabWFRel`, which synthesizes a `WellFoundedRelation` instance in the current environment),
this reads it from the fixpoint of the observed definition that has the name of the unary
definition Lean packs the group into, less `root`, applied to the group's fixed parameters
(`fixpointRelation?`). Every step is Lean's own function, in `wfRecursion`'s order; what
`wfRecursion` does after adding the definitions (helper compilation, equation lemmas, attributes)
is left out. Throws if the observed definition applies no such fixpoint. -/
private def wfRegeneration (root : Name) (docCtx : LocalContext × LocalInstances)
    (preDefs : Array PreDefinition) : TermElabM Unit := do
  let names := preDefs.map (·.declName)
  let preDefs ← preDefs.mapM fun preDef =>
    return { preDef with value := (← WF.floatRecApp preDef.value) }
  let (fixedParamPerms, argsPacker, unaryPreDef) ← withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    let fixedParamPerms ← getFixedParamPerms preDefs
    let varNamess ← preDefs.mapIdxM fun i preDef => WF.varyingVarNames fixedParamPerms i preDef
    for varNames in varNamess, preDef in preDefs do
      if varNames.isEmpty then
        throwError "`{preDef.declName}` does not take any (non-fixed) arguments"
    let argsPacker : Meta.ArgsPacker := { varNamess }
    let numSectionVars := preDefs[0]!.numSectionVars
    let unfolded ← preDefs.mapM fun preDef =>
      return { preDef with
        value := (← Meta.unfoldIfArgIsAppOf names numSectionVars preDef.value) }
    return (fixedParamPerms, argsPacker, ← WF.packMutual fixedParamPerms argsPacker unfolded)
  let processed ← withoutModifyingEnv do
    addAsAxiom unaryPreDef
    return { unaryPreDef with value := (← WF.preprocess unaryPreDef.value).expr }
  let preDefNonRec ← Meta.forallBoundedTelescope unaryPreDef.type fixedParamPerms.numFixed
    fun fixedArgs type => do
      unless (← Meta.whnfForall type).isForall do
        throwError "expected unary function type: {type}"
      let some (.defnInfo observed) :=
          (← getEnv).find? (unaryPreDef.declName.replacePrefix root .anonymous)
        | throwError "no observed definition for {unaryPreDef.declName}"
      unless observed.levelParams == unaryPreDef.levelParams do
        throwError "level parameters of {observed.name} differ"
      let some relation := fixpointRelation? (observed.value.beta fixedArgs)
        | throwError "{observed.name} applies no well-founded fixpoint"
      let (value, added) ← withoutModifyingEnv' do
        addAsAxiom unaryPreDef
        let value ← WF.mkFix processed fixedArgs argsPacker relation names
          (preDefs.map (·.termination.decreasingBy?))
        eraseRecAppSyntaxExpr value
      return { processed with value := (← Meta.unfoldDeclsFrom added value) }
  let preDefsNonRec ← WF.preDefsFromUnaryNonRec fixedParamPerms argsPacker preDefs preDefNonRec
  Mutual.addPreDefsFromUnary (cacheProofs := false) docCtx preDefs preDefsNonRec preDefNonRec

/-- The parameter Lean compiled the structurally recursive definition `base` on, as a function of
the `arity` parameters of the observed type: the position Lean recorded for it
(`Structural.eqnInfoExt`). `none` if Lean recorded none, or `base` is no definition with the level
parameters `levelParams` and that many parameters. -/
private def observedRecursionArgument? (base : Name) (levelParams : List Name) (arity : Nat) :
    MetaM (Option TerminationMeasure) := do
  let some recorded := Structural.eqnInfoExt.find? (← getEnv) base | return none
  let some (.defnInfo observed) := (← getEnv).find? base | return none
  unless observed.levelParams == levelParams do return none
  Meta.forallBoundedTelescope observed.type arity fun params _ => do
    unless params.size == arity do return none
    let some argument := params[recorded.recArgPos]? | return none
    return some { ref := .missing, structural := true, fn := ← Meta.mkLambdaFVars params argument }

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

/-- `toolchainPreprocessRules env`, computed once per `cache`: one inspection shares it across the
helpers of its environment. -/
private def cachedPreprocessRules (cache : IO.Ref (Option Meta.SimpTheorems)) (env : Environment) :
    IO Meta.SimpTheorems := do
  if let some rules ← cache.get then return rules
  let rules ← toolchainPreprocessRules env
  cache.set (some rules)
  return rules

/-- The environment a regeneration runs in: `env` with only the toolchain's `wf_preprocess` rules
`rules` and only the checker executable's built-in macros, tactic and term elaborators, so that no
rule or syntax handler of the audited modules or their dependencies takes part. The built-in tables
are process state: an audited module's initializer, which the report worker runs, could add to them,
a change inside the process boundary the standard leaves out of scope. -/
private def regenerationEnvironment (env : Environment) (rules : Meta.SimpTheorems) :
    IO Environment := do
  let env := Lean.Elab.WF.wfPreprocessSimpExtension.modifyState env fun _ => rules
  let env ← builtinHandlersOnly macroAttribute env
  let env ← builtinHandlersOnly Lean.Elab.Tactic.tacticElabAttribute env
  builtinHandlersOnly Lean.Elab.Term.termElabAttribute env

/-- `Declaration.unsafeRecRegenerated`: rerun Lean's own recursion compiler on the helper's group,
each helper's value becoming the body of a fresh definition under `regenerationRoot` with its calls
to the group's helpers standing for the recursive calls, and compare what it generates with the
observed base and its auxiliary definitions (`regenerationMatches`). Each compiler is given the
termination argument of the observed bases, since the value it generates depends on that argument:
the well-founded compiler passes the recursive-call function through a `match` where that
function's type, which holds the relation and the measure, changes in an alternative. Structural
recursion is tried first, on the argument position Lean recorded for each base
(`observedRecursionArgument?`; a read that throws reads nothing), or Lean's automatic choice for a
base with none; then well-founded recursion, with the relation of the base's own fixpoint
(`wfRegeneration`) and with every decreasing proof elided (`all_goals exact sorry`, on the raw
goal), since the comparison erases proofs and the observed base's own kernel-checked value supplies
them. A termination argument only selects which regeneration runs: whatever is read, a helper is
admitted only when the definitions that regeneration adds match the observed ones. The compiler
runs in `regenerationEnvironment`, with the fresh definitions `noncomputable` so that no code is generated
for them. A regeneration that reports an error does not count. Every change is undone before the
comparison, which reads the observed definitions and decides erasure in the inspected environment:
whatever code runs during a regeneration, only the definitions it adds are compared, each with the
theorems the regeneration abstracted from it put back (`regeneratedDefinitions`), so the result
does not depend on how Lean named or shared those theorems. A comparison that throws does not
count either. A `checkerLimit?` reached is rethrown. -/
private def unsafeRecRegeneration (env : Environment) (name : Name) (info : ConstantInfo)
    (preprocessRules : IO.Ref (Option Meta.SimpTheorems)) :
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
      return ({ ref := .missing, kind := .def, levelParams := value.levelParams,
                modifiers := { computeKind := .noncomputable },
                declName := regenerationRoot ++ bases[i]!, binders := .missing, type := value.type,
                value := rename value.value, termination := .none } : PreDefinition)
    let recursionArguments ← preDefs.mapIdxM fun i (preDef : PreDefinition) => do
      try
        let arity ← Meta.lambdaTelescope preDef.value fun params _ => pure params.size
        observedRecursionArgument? bases[i]! preDef.levelParams arity
      catch ex => if (← checkerLimit? ex).isSome then throw ex else pure none
    let regenerating ← regenerationEnvironment (← getEnv)
      (← cachedPreprocessRules preprocessRules env)
    let attempt (run : TermElabM Unit) : TermElabM Bool := do
      let saved ← saveState
      try
        Core.resetMessageLog
        setEnv regenerating
        withOptions (·.setBool `debug.rawDecreasingByGoal true) run
        let failed := (← Core.getMessageLog).hasErrors
        let after ← getEnv
        saved.restore
        if failed then return false
        let some regenerated := regeneratedDefinitions regenerating after | return false
        regenerationMatches regenerated
      catch ex =>
        saved.restore
        if (← checkerLimit? ex).isSome then throw ex
        return false
      finally
        -- A runtime limit (heartbeats, recursion depth) bypasses `catch`; undo the run anyway.
        saved.restore
    let docCtx := (← getLCtx, ← Meta.getLocalInstances)
    if ← attempt (structuralRecursion docCtx preDefs recursionArguments) then
      return some .structural
    let elided ← `(Lean.Parser.Tactic.tacticSeq| all_goals exact sorry)
    let wfDefs := preDefs.map fun (preDef : PreDefinition) =>
      { preDef with termination := { TerminationHints.none with
          decreasingBy? := some ({ ref := .missing, tactic := elided } : DecreasingBy) } }
    if ← attempt (wfRegeneration regenerationRoot docCtx wfDefs) then return some .wellFounded
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
any constant such a constant mentions. It also memoizes, for the same environment, the toolchain's
`wf_preprocess` rules that recursion-helper regeneration uses. -/
structure ContractScope where
  /-- For each imported module index: `Regula.Contract` or a module that transitively imports it. -/
  aware : Array Bool
  /-- Whether the current module's own constants can mention it: the current module imports
  every module of the header. -/
  mainAware : Bool
  /-- Constants whose closure under `unfoldReferences` was searched without reaching it. -/
  free : IO.Ref NameSet
  /-- The toolchain's `wf_preprocess` rules once a recursion helper's regeneration has computed
  them (`Collect.unsafeRecRegeneration`), shared by every helper of the environment. -/
  preprocessRules : IO.Ref (Option Meta.SimpTheorems)

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
           free := ← IO.mkRef {}
           preprocessRules := ← IO.mkRef none }

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

/-- Whether Lean's injectivity generator (`Meta.mkInjectiveTheorems`, run for every inductive type
it declares) generates `c.inj` and `c.injEq` for the constructor `c`, under Lean's default
options: the type is not a class, not an inductive predicate and not `unsafe`, and `c` has a field
its injectivity theorem equates, one whose type is not a proposition and that its result type
does not mention (the fields `mkInjectiveTheoremType?` keeps). -/
private def injectivityGenerated (ctor : ConstructorVal) : MetaM Bool := do
  if isClass (← getEnv) ctor.induct || ctor.isUnsafe || (← Meta.isInductivePredicate ctor.induct)
  then return false
  let type ← Meta.elimOptParam ctor.type
  Meta.forallBoundedTelescope type ctor.numParams fun _ type =>
    Meta.forallTelescope type fun fields result => do
      let context ← getLCtx
      fields.anyM fun field => do
        return !(← Meta.isProp (← Meta.inferType field)) && !Meta.occursOrInType context field result

/-- Whether Lean's `SizeOf` generator (`Meta.mkSizeOfInstances`, run for every inductive type it
declares) generates `c.sizeOf_spec` for every constructor `c` of `t`, under Lean's default options:
`SizeOf` is declared and `t` is not a class, not an inductive predicate and not `unsafe`. -/
private def sizeOfGenerated (t : InductiveVal) : MetaM Bool := do
  return (← getEnv).contains ``SizeOf && !isClass (← getEnv) t.name && !t.isUnsafe &&
    !(← Meta.isInductivePredicate t.name)

/-- Whether Lean's `ctorIdx` generator (`mkCtorIdx`, run for every inductive type it declares)
generates `t.ctorIdx`, under Lean's default options: `Nat` is declared, `t` is not a family of
propositions, and it eliminates into every universe (its `casesOn` has a universe parameter of its
own). -/
private def ctorIdxGenerated (t : InductiveVal) : MetaM Bool := do
  let some casesOn := (← getEnv).find? (mkCasesOnName t.name) | return false
  return (← getEnv).contains ``Nat && casesOn.levelParams.length > t.levelParams.length &&
    !(← Meta.isPropFormerType t.type)

/-- The declarations `name` is named under, as itself and as its user name
(`privateToUserName`), the two spellings Lean's own `Meta.declFromEqLikeName` tries, and its last
component, both read past the macro scopes that Lean's `Name.append` and `appendIndexAfter` keep
last when they derive a name from a hygienic one (`extractMacroScopes`), and with those scopes
restored on the declaration it is named under. -/
private def namedUnder? (name : Name) : Option (List Name × String) :=
  let view := extractMacroScopes name
  match view.name with
  | .str p s =>
    if p.isAnonymous then none
    else
      let p := { view with name := p }.review
      some ([p, privateToUserName p], s)
  | _ => none

/-- Whether `name` is named under one of `ancestors` at any depth: a proper prefix of it, read
past its macro scopes and with them restored as `namedUnder?` does, is one of them as itself or as
its user name (`privateToUserName`). So `f.go` and `f.go.loop` are named under `f`, in either
privacy. -/
private def namedBelow (ancestors : List Name) (name : Name) : Bool :=
  let view := extractMacroScopes name
  let rec below : Name → Bool
    | .str p _ =>
      let parent := { view with name := p }.review
      ancestors.contains parent || ancestors.contains (privateToUserName parent) || below p
    | .num p _ => below p
    | .anonymous => false
  below view.name

/-- The kinds Lean's `mkAuxDeclName` names the auxiliary declarations it abstracts out of the
declaration it elaborates with, as `kind_N` under that declaration: proofs (`Meta.mkAuxLemma`,
`Meta.abstractNestedProofs`), `simp` and `cbv_eval` rewrite lemmas, `private_decl%`, `grind` and
`impossible` terms, `inferInstanceAs` wrappers, the safe side `unsafe_impl` of an `unsafe` term, and
`bv_decide`'s reflection definitions. -/
private def auxiliaryKinds : List String :=
  ["_proof", "_simp", "_cbv_eval", "_private", "grind", "_impossible", "_aux", "unsafe_impl",
    "_expr_def", "_cert_def", "_reflection_def"]

/-- The kind of a last name component `kind_N`, or `kind_N_M` from a nested elaboration, when
`kind` is one of `auxiliaryKinds`. -/
private def auxiliaryKind? (s : String) : Option String :=
  auxiliaryKinds.find? fun kind =>
    let rest := s.toList.drop (kind.length + 1)
    s.startsWith (kind ++ "_") && !rest.isEmpty && rest.all fun c => c.isDigit || c == '_'

/-- Whether the kernel value of the declaration `f` uses `name`. -/
private def valueUses (env : Environment) (f name : Name) : Bool :=
  ((env.find? f).bind valueOf?).any (·.getUsedConstants.contains name)

/-- Whether `name` is named `kind_N` for one of the `auxiliaryKinds` under another declaration's
name. -/
private def isAuxiliaryName (name : Name) : Bool :=
  (namedUnder? name).any fun (_, s) => (auxiliaryKind? s).isSome

/-- The names of the declarations of `name`'s module: an imported module's, or the current
one's. -/
private def moduleConstants (env : Environment) (name : Name) : Array Name :=
  match env.getModuleIdxFor? name with
  | some idx => (env.header.moduleData[(idx : Nat)]?.map (·.constNames)).getD #[]
  | none => env.constants.map₂.foldl (init := #[]) fun names id _ => names.push id

/-- The constants the type and the kernel value of the declaration `name` use. -/
private def usedConstants (env : Environment) (name : Name) : NameSet :=
  match env.find? name with
  | some info => info.type.getUsedConstantsAsSet ++
      ((valueOf? info).map (·.getUsedConstantsAsSet)).getD {}
  | none => {}

/-- Whether a constituent of the declaration `f` uses `name`, in its type or kernel value
(`usedConstants`): `f` itself, or, when `f` is an inductive type, any type of its mutual block
(`InductiveVal.all`, which holds `f`), one of that type's constructors or, for a structure, the
default of one of its fields (`getEffectiveDefaultFnForField?`). Lean elaborates a whole mutual
block under its first type's name, so that type's auxiliary declarations serve every type of the
block. -/
private def declarationUses (env : Environment) (f name : Name) : Bool :=
  let uses (constituent : Name) := (usedConstants env constituent).contains name
  let typeUses (type : Name) : Bool :=
    uses type || ((env.find? type).any fun
      | .inductInfo t => t.ctors.any uses
      | _ => false) || (isStructure env type &&
        (getStructureFieldsFlattened env type (includeSubobjectFields := false)).any fun field =>
          (getEffectiveDefaultFnForField? env type field).any uses)
  match env.find? f with
  | some (.inductInfo t) => t.all.any typeUses
  | _ => uses f

/-- The declaration whose own use relates the auxiliary declaration `name`, named `kind_N` under
`f`: `f`, when a constituent of its declaration (`declarationUses`), the value its well-founded or
structural equation information records, or the value of the function its well-founded equation
information names uses `name`, or, for a `simp` or `cbv_eval` lemma, when `name` uses `f`;
otherwise the definition of `f.eq_def` when that theorem's statement uses `name`; otherwise
`f._unsafe_rec` when its value uses `name`. -/
private def auxiliaryOwner? (env : Environment) (name : Name) : Option Name := do
  let (spellings, s) ← namedUnder? name
  let kind ← auxiliaryKind? s
  (spellings.find? fun f => declarationUses env f name ||
      (Elab.WF.eqnInfoExt.find? env f).any (fun info =>
        info.value.getUsedConstants.contains name || valueUses env info.declNameNonRec name) ||
      (Elab.Structural.eqnInfoExt.find? env f).any (·.value.getUsedConstants.contains name) ||
      ((kind == "_simp" || kind == "_cbv_eval") && valueUses env name f)) <|>
    (spellings.findSome? fun f =>
      let unfold := f.str Meta.unfoldThmSuffix
      if (env.find? unfold).any (·.type.getUsedConstants.contains name) then
        (Meta.declFromEqLikeName env unfold).map (·.1)
      else none) <|>
    spellings.findSome? fun f =>
      let helper := Compiler.mkUnsafeRecName f
      if valueUses env helper name then some helper else none

/-- A declaration of the module that may use an auxiliary declaration: its name, whether Lean
generated it as an auxiliary declaration itself (it is named as one, `isAuxiliaryName`, and has
no recorded declaration range), and the constants it uses. -/
private abbrev AuxiliaryUser := Name × Bool × Thunk NameSet

/-- Whether `user` uses the auxiliary declaration `name`, named under `parents`, as a declaration
that is not itself a generated auxiliary one: it is named under one of `parents` at any depth
(`namedBelow`), as a `where` or `let rec` helper of the declaration is, and its type or value uses
`name`. The name is tested first, so the constants of a declaration named elsewhere are not
read. -/
private def helperUses (parents : List Name) (name : Name) : AuxiliaryUser → Bool
  | (user, auxiliary, uses) => !auxiliary && namedBelow parents user && uses.get.contains name

/-- Whether the auxiliary declaration `name` is related: by a use of its own (`auxiliaryOwner?`,
or `helperUses` by one of `users`), or by a generated auxiliary one of `users` that uses `name` and
is itself related in the same way. The state holds the auxiliary declarations already examined,
and none is examined twice. That loses nothing: a search that fails has examined every declaration
that uses `name` through any chain of generated auxiliary `users` and found none with a use of its
own, so each of them is unrelated whatever led to it, and a later search may skip them; a search
that succeeds ends the query. The declarations under examination at one time are distinct members
of `users`, so `users.size` steps of fuel never run out before an unexamined one. -/
private def auxiliaryRelated (env : Environment) (users : Array AuxiliaryUser) :
    Nat → Name → StateM NameSet Bool
  | 0, _ => return false
  | fuel + 1, name => do
    if (← get).contains name then return false
    modify (·.insert name)
    if (auxiliaryOwner? env name).isSome then return true
    let parents := ((namedUnder? name).map (·.1)).getD []
    users.anyM fun (user, auxiliary, uses) =>
      if helperUses parents name (user, auxiliary, uses) then return true
      else if auxiliary && uses.get.contains name then auxiliaryRelated env users fuel user
      else return false

/-- The first of the declarations `users` of the module, each with whether Lean generated it as an
auxiliary declaration, that relates the auxiliary declaration `name` by using it in its type or
value: one that is not a generated auxiliary declaration and is named under the declaration `name`
is named under, at any depth (`helperUses`), or a generated auxiliary one that is itself related
(`auxiliaryRelated`), by a use of its own or by another of `users` in the same way, through any
number of them. One query examines each generated auxiliary one of `users` at most once, and reads
the constants each of `users` uses at most once. -/
private def auxiliaryUser? (env : Environment) (users : Array (Name × Bool)) (name : Name) :
    Option Name :=
  let parents := ((namedUnder? name).map (·.1)).getD []
  let users : Array AuxiliaryUser := users.map fun (user, auxiliary) =>
    (user, auxiliary, Thunk.mk fun _ => usedConstants env user)
  let search := users.findM? fun (user, auxiliary, uses) =>
    if helperUses parents name (user, auxiliary, uses) then return true
    else if auxiliary && user != name && uses.get.contains name then
      auxiliaryRelated env users users.size user
    else return false
  (search.run' {}).run.map (·.1)

/-- The declaration Lean generated `name` from, one step, if `name` belongs to `family`, as the
environment records it. Each clause rests on (a) a fact Lean's generator records in the
environment: a mark or extension entry, an equation information, or a use in a declaration's type
or kernel value, in the statement of an `eq_def`, in a helper or in another auxiliary declaration;
or on (c) the generator's own precondition, checked on the environment, for a declaration Lean
generates whenever that precondition holds, so that no other declaration can have its name. None
rests on a name alone; the name only says which declaration a marked one is named under, as
Lean's own `findDeclarationRanges?` reads it. A declaration is related only when an environment
fact shows Lean generated it: each clause that reads the relation from the declaration's name (an
equation lemma, a reserved name, a matcher's equation or splitter, a `brecOn`'s `go` or `eq`, a
structural helper, an auxiliary `kind_N` declaration, a constructor lemma, a type construction, a
field default) applies only to a declaration with no recorded declaration range
(`findDeclarationRangesCore?`), since Lean records one for every declaration an author writes and
none for these generated ones. A declaration left unrelated is reported at its own location,
while one related wrongly would misreport what the author wrote as generated, so a clause is
narrowed rather than widened. The enumeration of the families Lean v4.34.0 generates, with their
generators, is in `docs/guides/proofs-and-boundaries.md#generated-declaration-families`.
- `constructor` (a): its inductive type (`ConstructorVal.induct`);
- `projection` (a): a structure projection's constructor (`ProjectionFunctionInfo.ctorName`), or,
  for a parent projection that is not a subobject (`getAuxParentProjectionInfo?`), the structure it
  is named under;
- `recursor` (a): a recursor (`isRecCore`), an auxiliary recursor (`isAuxRecursor`: `casesOn`,
  `recOn`, `below`, `brecOn`, `ctorElim` and a constructor's `elim`), a `noConfusion`, the type's
  or a constructor's (`isNoConfusion`), or a sparse `casesOn` (`isSparseCasesOn`): the name it is
  named under, whose range Lean's own `findDeclarationRanges?` gives the first three; and the `go`
  and `eq` Lean's `brecOn` generator adds under a marked `brecOn` (`isBRecOnRecursor`): that
  `brecOn`;
- `equationLemma` (a): its definition (`Meta.declFromEqLikeName`);
- `reservedName` (a): a name Lean reserves for a declaration it generates on demand
  (`isReservedName`), which no user declaration can take once it is reserved
  (`checkNotAlreadyDeclared`): the name it is named under;
- `matcher` (a): a matcher (`Meta.isMatcherCore`), or an equation or splitter of one, the names
  Lean's own `isMatchEqName?` gives them: the name it is named under;
- `wellFounded` (a): `f`, when its well-founded or `partial_fixpoint` equation information names
  `name` as the function it is compiled through (`Elab.WF.eqnInfoExt`,
  `Elab.PartialFixpoint.eqnInfoExt`);
- `structural` (a): `f` for `f._sunfold`, when its structural equation information records it
  (`Elab.Structural.eqnInfoExt`), and for `f._f`, when that records it or `f`'s value uses `f._f`;
- `auxiliaryLemma` (a): `f` for a declaration `mkAuxDeclName` names `f.kind_N` for one of the
  `auxiliaryKinds`, when a constituent of `f`'s declaration uses it (`declarationUses`: its type
  or value, or, for an inductive type, the type, a constructor's type or a field's default value of
  any type of its mutual block, which Lean elaborates under its first type's name; where a `module`
  file's header proofs go), or the value its well-founded or structural equation information
  records, or the value of the function its well-founded equation information names uses it, or,
  for a `simp` or `cbv_eval` lemma Lean derives from `f`, when it uses `f`; otherwise the
  definition of `f.eq_def` (`Meta.declFromEqLikeName`) when that theorem's statement uses it, as
  the statement `WF.mkUnfoldEq` gives it from the pre-definition it cleans separately; otherwise
  `f._unsafe_rec` when its value uses it, the recursion helper `addAndCompilePartialRec` compiles
  from `f`'s pre-definition, whose own step to `f` is its admitted authorization
  (`Findings.stepOf`), not its name; otherwise a declaration of its module whose type or value
  uses it (`auxiliaryUser?`): one named under `f` at any depth that is not itself a generated
  auxiliary declaration (it is not auxiliary-named, or it has a recorded declaration range), such
  as a `where` or `let rec` helper `f.go`, whose proofs Lean names under `f` when it runs their
  tactic blocks in the exposed body of a `module` file; or another such auxiliary declaration with
  no recorded range that is itself related, by one of those uses or by a further such declaration
  in the same way; one named under `f` first, then the first in name order: Lean abstracts a proof
  nested in a proof, so the lemma that uses it can be named under another declaration, such as a
  `where` helper's; `f` for the wrapper `f._rpc_wrapped` Lean records for an RPC method `f`
  (`Server.userRpcProcedures`); and `id` for the action of an `initialize id : T ← e` declaration,
  which Lean records on `id` (`getInitFnNameFor?`), among the declarations of the action's own
  module, where the command declares both;
- `constructorLemma` (c): `c` for `c.inj` and `c.injEq` (`injectivityGenerated`) and
  `c.sizeOf_spec` (`sizeOfGenerated`), and for `c._flat_ctor` when `c` constructs a registered
  structure (`isStructure`), which the `structure` command generates with it. Lean's generator runs
  when it declares the type, so a declaration that already had the name would have failed that
  command;
- `typeConstruction` (c): `t` for `t.ctorIdx` (`ctorIdxGenerated`), `t._sizeOf_1`, … and
  `t._sizeOf_inst` (`sizeOfGenerated`), and `t.noConfusionType` and `t.ctorElimType` when
  `t.noConfusion` is marked (`isNoConfusion`) or `t.ctorElim` is marked (`isAuxRecursor`), since
  the one generator run that marks it also generates them;
- `fieldDefault`: the structure `S` for `S.x._default` or `S.x._inherited_default`, when Lean's
  own lookup of the default of `S`'s field `x` (`getEffectiveDefaultFnForField?`) is `name`. That
  lookup goes by name, so a declaration of that name is the field's default to Lean itself;
- `recursionHelper`: none here. The environment ties `f._unsafe_rec` to `f` only by its name, so
  the admitted helper authorization relates it (`Findings.stepOf`). -/
def generatedBy? (family : GeneratedFamily) (name : Name) : MetaM (Option Name) := do
  let env ← getEnv
  let authored := (← findDeclarationRangesCore? name).isSome
  match family with
  | .constructor =>
    let some (.ctorInfo value) := env.find? name | return none
    return some value.induct
  | .projection =>
    if let some info := env.getProjectionFnInfo? name then return some info.ctorName
    let some (p :: _, _) := namedUnder? name | return none
    return if (env.getAuxParentProjectionInfo? name).isSome && isStructure env p then some p
      else none
  | .recursor =>
    let some (spellings@(p :: _), s) := namedUnder? name | return none
    if (s == "go" || s == "eq") && !authored && isBRecOnRecursor env p then return some p
    unless isRecCore env name || isAuxRecursor env name || isNoConfusion env name ||
        isSparseCasesOn env name do return none
    return spellings.find? env.contains
  | .equationLemma =>
    return if authored then none else (Meta.declFromEqLikeName env name).map (·.1)
  | .reservedName =>
    let some (spellings, _) := namedUnder? name | return none
    return if !authored && isReservedName env name then spellings.find? env.contains else none
  | .matcher =>
    let some (spellings, s) := namedUnder? name | return none
    unless Meta.isMatcherCore env name || (!authored &&
        spellings.head?.any (Meta.isMatcherCore env) &&
        (Meta.isEqnReservedNameSuffix s || s == "splitter")) do return none
    return spellings.find? env.contains
  | .wellFounded =>
    let some (spellings, _) := namedUnder? name | return none
    return spellings.find? fun f =>
      (Elab.WF.eqnInfoExt.find? env f).any (·.declNameNonRec == name) ||
        (Elab.PartialFixpoint.eqnInfoExt.find? env f).any (·.declNameNonRec == name)
  | .structural =>
    let some (spellings, s) := namedUnder? name | return none
    unless !authored && (s == "_f" || s == "_sunfold") do return none
    return spellings.find? fun f => (Elab.Structural.eqnInfoExt.find? env f).isSome ||
      (s == "_f" && valueUses env f name)
  | .auxiliaryLemma =>
    if let .str _ "initFn" := privateToUserName name.eraseMacroScopes then
      let initializes (id : Name) := getInitFnNameFor? env id == some name
      return match env.getModuleIdxFor? name with
        | some idx => env.header.moduleData[(idx : Nat)]?.bind (·.constNames.find? initializes)
        | none => env.constants.map₂.foldl (init := none) fun found id _ =>
            found.or (if initializes id then some id else none)
    let some (spellings, s) := namedUnder? name | return none
    if s == "_rpc_wrapped" then
      return spellings.find? fun f => Server.userRpcProcedures.find? env f == some name
    if authored || (auxiliaryKind? s).isNone then return none
    if let some owner := auxiliaryOwner? env name then return some owner
    let (near, far) := (moduleConstants env name).partition (namedBelow spellings)
    let (auxiliaries, others) := far.partition isAuxiliaryName
    let users ← (near.qsort Name.lt ++ auxiliaries.qsort Name.lt ++ others).mapM fun user => do
      if isAuxiliaryName user then return (user, (← findDeclarationRangesCore? user).isNone)
      else return (user, false)
    return auxiliaryUser? env users name
  | .constructorLemma =>
    if authored then return none
    let some (p :: _, s) := namedUnder? name | return none
    let some (.ctorInfo ctor) := env.find? p | return none
    if ((s == "inj" || s == "injEq") && (← injectivityGenerated ctor)) ||
        (s == "_flat_ctor" && isStructure env ctor.induct) then
      return some p
    let some (.inductInfo t) := env.find? ctor.induct | return none
    return if s == "sizeOf_spec" && (← sizeOfGenerated t) then some p else none
  | .typeConstruction =>
    if authored then return none
    let some (p :: _, s) := namedUnder? name | return none
    let some (.inductInfo t) := env.find? p | return none
    if (s == "noConfusionType" && isNoConfusion env (p.str "noConfusion")) ||
        (s == "ctorElimType" && isAuxRecursor env (mkCtorElimName p)) ||
        (s == "ctorIdx" && (← ctorIdxGenerated t)) ||
        ((s == "_sizeOf_inst" || (s.startsWith "_sizeOf_" && (s.drop 8).isNat)) &&
          (← sizeOfGenerated t)) then
      return some p
    return none
  | .fieldDefault =>
    let some (spellings, s) := namedUnder? name | return none
    unless !authored && (s == "_default" || s == "_inherited_default") do return none
    return spellings.findSome? fun projection =>
      match namedUnder? projection with
      | some (struct :: _, field) =>
        if isStructure env struct &&
            getEffectiveDefaultFnForField? env struct (.mkSimple field) == some name then
          some struct
        else none
      | _ => none
  | .recursionHelper =>
    -- The environment ties `f._unsafe_rec` to `f` by its name alone
    -- (`Compiler.isUnsafeRecName?`); the relation is the admitted authorization of the helper,
    -- which observed Lean's recursion compiler regenerate it (`Findings.stepOf`,
    -- `Findings.helperStep_base`).
    return none

/-- The declaration Lean generated `name` from, one step, as the environment records it: the one
the first family of `GeneratedFamily.all` that `name` belongs to relates it to (`generatedBy?`),
kept only when the environment contains a declaration of that name, and `none` when no family
relates it to one, whatever its name. So it never names a declaration that does not exist, and an
elaborator or macro Lean names `«_aux_…»` inside a namespace, a derived instance, or a declaration
a deriving handler adds such as an enumeration's `ofNat` is not related. A declaration a
metaprogram adds is related only when a family's clause holds of it, which a clause that reads
the name allows only for one with no declaration range that is named like a generated one
(`generatedBy?`). -/
def generatedFrom? (name : Name) : MetaM (Option Name) := do
  let env ← getEnv
  GeneratedFamily.all.findSomeM? fun family =>
    return (← generatedBy? family name).filter env.contains

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
      unsafeRecRegeneration env name info scope.preprocessRules else pure none
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
    recordedRanges := ranges?.map rangesReport
    generatedFrom := ← liftTermElabM (generatedFrom? name)
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
