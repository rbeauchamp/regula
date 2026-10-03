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
public import Lean.Meta.Tactic.Split
public import Lean.Meta.Tactic.Refl
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

/-- Run `act` with Lean's smart unfolding off. With it on, `Meta` unfolds an application of `g`
through a declaration named `g._sunfold` (`Meta.unfoldDefinition?`), which it finds by that name
alone and whose type it does not compare with `g`'s. Lean generates one for a structurally
recursive definition, but an audited module can declare one for any function, with another body,
and the kernel checks it as the ordinary definition it is. Every answer the checker takes from
`Meta` reduction (what is a proposition, a type or a proof, which parameters a recursion compiler
finds fixed, what a type reduces to) would then rest on that name. With the option off, Lean 4.34.0
reads no such declaration: each unfolding is of the constant's own kernel-checked value. -/
def withoutSmartUnfolding {α : Type} (act : CommandElabM α) : CommandElabM α :=
  withScope (fun scope => { scope with opts := Meta.smartUnfolding.set scope.opts false }) act

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

/-- The axioms a theorem the checker has Lean's kernel check may rest on: Standard-Logical. -/
private def checkedAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Whether Lean's kernel, in the current environment, accepts `value` as a proof of the closed
statement `type` (`Environment.addDeclCore` on a theorem of a fresh name) and that theorem uses no
axiom outside `checkedAxioms`. A statement or a proof with a free variable or a metavariable
answers `false`. The theorem stays in the environment, which the caller restores. What the kernel
refuses with is thrown, a rejected proof and a resource limit alike (its deterministic timeout,
deep recursion or excessive memory), and the caller tells the two apart by `checkerLimit?`. -/
private def kernelChecked (type value : Expr) : MetaM Bool := do
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar then return false
  let name ← mkFreshUserName `_regula_checked
  let levelParams := (collectLevelParams (collectLevelParams {} type) value).params.toList
  let options ← getOptions
  match (← getEnv).addDeclCore (Core.getMaxHeartbeats options).toUSize
      (maxRecDepth.get options).toUSize
      (.thmDecl { name, levelParams, type, value }) none with
  | .error rejected => throwKernelException rejected
  | .ok checked =>
    setEnv checked
    return (← collectAxioms name).all checkedAxioms.contains

/-- Whether Lean's kernel checks the threading law of the application `threaded`, the fact the
comparison needs before it takes a `match` that passes a variable through as the `match` that uses
the variable directly. With `M`, the parameters `ps` and the motive `fun ds => A ds → R ds` of
`threaded`, the law is the theorem, over every variable of the local context,

`∀ ds alts (w : A ds), M ps (fun ds => A ds → R ds) ds alts w = M ps R ds (fun xs => altsᵢ xs w)`

where the right-hand side gives each alternative `w` after the `altNumParams` pattern variables
the left-hand side's alternative binds. The statement is built from the constant `M` itself and
the positions the comparison reads; what Lean records about `M` (that it is a matcher or a
`casesOn`, how many pattern variables an alternative binds) only says where to look and how to
search for a proof (`Split.splitMatch`, or `cases` on the major premise, then `rfl`). Admission
rests on the kernel alone: `Environment.addDeclCore` must accept the theorem, whose proof may use
no axiom outside `checkedAxioms` (`kernelChecked`). The right-hand side is well typed only where
`A ds` and each `A (pᵢ xs)` are definitionally equal, which the kernel decides whatever is
irreducible. Nothing is kept: the theorem, and every constant the search realizes, is discarded. A
search that fails, or a theorem the kernel rejects, answers `false`. A `checkerLimit?` reached is
rethrown, in the search or in the kernel (its deterministic timeout, deep recursion or excessive
memory): the helper is then undecided, not rejected. -/
private def threadingLawChecked (threaded : Meta.MatcherApp) : MetaM Bool := do
  let ambient := (← getLCtx).getFVars
  let numDiscrs := threaded.discrs.size
  let search : MetaM Bool := Meta.withTransparency .all do
    Meta.lambdaBoundedTelescope threaded.motive numDiscrs fun ds body => do
      unless ds.size == numDiscrs do return false
      let .forallE _ argument result _ := body | return false
      if result.hasLooseBVars then return false
      let levels ← match threaded.uElimPos? with
        | some position => pure <| threaded.matcherLevels.set! position (← Meta.getLevel result)
        | none => pure threaded.matcherLevels
      let head := mkAppN (mkApp (mkAppN (mkConst threaded.matcherName
        threaded.matcherLevels.toList) threaded.params) threaded.motive) ds
      let directHead := mkAppN (mkApp (mkAppN (mkConst threaded.matcherName levels.toList)
        threaded.params) (← Meta.mkLambdaFVars ds result)) ds
      unless ← Meta.isTypeCorrect head do return false
      Meta.forallBoundedTelescope (← Meta.inferType head) threaded.alts.size fun alts _ => do
        unless alts.size == threaded.alts.size do return false
        let matched := mkAppN head alts
        let some law ← Meta.withLocalDeclD `w argument fun w => do
            let mut direct := directHead
            for alt in alts, numParams in threaded.altNumParams do
              let some directAlt ← Meta.forallBoundedTelescope (← Meta.inferType alt) numParams
                  fun xs _ => do
                    if xs.size != numParams then return none
                    return some (← Meta.mkLambdaFVars xs (mkApp (mkAppN alt xs) w))
                | return none
              direct := mkApp direct directAlt
            return some (← Meta.mkForallFVars #[w] (← Meta.mkEq (mkApp matched w) direct))
          | return false
        -- The goal is created outside the scope of `w`, so that no proof can mention it.
        let goal ← Meta.mkFreshExprSyntheticOpaqueMVar law
        let cases ← if ← Meta.isMatcherApp matched then
            Meta.Split.splitMatch goal.mvarId! matched
          else
            let some major := ds.back? | return false
            pure <| (← goal.mvarId!.cases major.fvarId!).toList.map (·.mvarId)
        for case in cases do
          let (_, case) ← case.intro1
          case.refl
        let binders := ambient ++ ds ++ alts
        let type ← instantiateMVars (← Meta.mkForallFVars binders law)
        let value ← Meta.mkLambdaFVars binders (← instantiateMVars goal)
        -- A kernel refusal is thrown, not answered: a resource limit of the kernel is the
        -- checker's, and `catch` below tells it from a rejected proof by `checkerLimit?`.
        kernelChecked type value
  let saved ← Meta.saveState
  try
    search
  catch ex =>
    if (← checkerLimit? ex).isSome then throw ex
    return false
  finally
    saved.restore

/-- `threaded` and `direct` as the two forms of one `match` that Lean's recursion compilers choose
between (`MatcherApp.addArg`): applications of the same constant, which Lean records as a matcher
or a `casesOn` (`Meta.matchMatcherApp?`), where `threaded` passes a variable as one more argument
after the alternatives and binds it once more, after the pattern variables, in every alternative,
and where the kernel checks the threading law of `threaded` (`threadingLawChecked`), so that what
Lean records decides nothing by itself. Returns the two applications and that variable. The
matcher's universe levels must agree except the motive's, which the added binder changes. -/
private def threadedMatch? (threaded direct : Expr) :
    MetaM (Option (Meta.MatcherApp × Meta.MatcherApp × FVarId)) := do
  unless threaded.getAppNumArgs == direct.getAppNumArgs + 1 do return none
  let some threaded ← Meta.matchMatcherApp? (alsoCasesOn := true) threaded | return none
  let some direct ← Meta.matchMatcherApp? (alsoCasesOn := true) direct | return none
  let levels := fun (app : Meta.MatcherApp) => match app.uElimPos? with
    | some motiveLevel => app.matcherLevels.eraseIdxIfInBounds motiveLevel
    | none => app.matcherLevels
  unless threaded.matcherName == direct.matcherName && threaded.uElimPos? == direct.uElimPos?
      && levels threaded == levels direct do return none
  let some (Expr.fvar passed) := threaded.remaining[0]? | return none
  unless ← threadingLawChecked threaded do return none
  return some (threaded, direct, passed)

/-- The pairs under which `bound`, a variable the threaded side has just bound, stands for
`passed`, a variable of the same side: `bound` with every variable of the other side that `passed`
is paired with. The threaded side is the left one when `left`. -/
private def standingFor (left : Bool) (pairs : Array (FVarId × FVarId)) (passed bound : FVarId) :
    Array (FVarId × FVarId) :=
  pairs.filterMap fun (x, y) =>
    if left then (if x.name == passed.name then some (bound, y) else none)
    else (if y.name == passed.name then some (x, bound) else none)

/-- With the threaded side on the left, `standingFor` pairs `bound` alone, and with exactly the
variables `passed` is paired with: it relates no two variables that `pairs` does not, other than
through `bound`. This states nothing about the comparison that uses the pairs. -/
private theorem mem_standingFor_left (pairs : Array (FVarId × FVarId))
    (passed bound x y : FVarId) :
    (x, y) ∈ standingFor true pairs passed bound ↔ x = bound ∧ (passed, y) ∈ pairs := by
  cases passed
  simp only [standingFor, Array.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨⟨a⟩, b, member, selected⟩
    split at selected <;> simp_all
  · rintro ⟨rfl, member⟩
    exact ⟨_, _, member, by simp⟩

/-- `mem_standingFor_left` with the threaded side on the right. -/
private theorem mem_standingFor_right (pairs : Array (FVarId × FVarId))
    (passed bound x y : FVarId) :
    (x, y) ∈ standingFor false pairs passed bound ↔ y = bound ∧ (x, passed) ∈ pairs := by
  cases passed
  simp only [standingFor, Array.mem_filterMap, Prod.exists]
  constructor
  · rintro ⟨a, ⟨b⟩, member, selected⟩
    split at selected <;> simp_all
  · rintro ⟨rfl, member⟩
    exact ⟨_, _, member, by simp⟩

/-- Whether `a` and `b` are equal up to compilation erasure: the same expression after every proof
and every type of each side, decided in that side's own local context, is erased, with the
variables they bind paired, each well-founded fixpoint reduced to `fixpointArguments?`, and a
`match` that passes a variable through (`threadedMatch?`) taken as the `match` that uses the
variable directly: `(match d with | pᵢ => fun w => bᵢ) v` against `match d with | pᵢ => bᵢ'`
compares each `bᵢ` with `bᵢ'`, `w` standing for `v`. That step is taken only where the kernel
checks the threading law (`threadingLawChecked`), by which the first side equals the `match` whose
alternatives are `fun w => bᵢ` applied to `v`; comparing `bᵢ` with `w` standing for `v` compares
those alternatives, reduced, with the other side's. The two sides then compile to code that
computes the same; their recursion, relations and termination proofs may differ. A pair
`(x, y)` of `pairs` reads: `x` on the left and `y` on the right are the same variable. `fuel`
bounds the depth; exhausting it answers `false`. -/
private def equalErased (fuel : Nat) (pairs : Array (FVarId × FVarId)) (a b : Expr) :
    MetaM Bool := do
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    if a == b && !a.hasFVar && !b.hasFVar then return true
    if (← erasedByCompilation a) && (← erasedByCompilation b) then return true
    let all := fun (pairs : Array (FVarId × FVarId)) (xs ys : Array Expr) => do
      if xs.size != ys.size then return false
      for i in [:xs.size] do
        unless ← equalErased fuel pairs xs[i]! ys[i]! do return false
      return true
    -- `threaded` on the left when `left`, on the right otherwise.
    let threadedEqual := fun (left : Bool) (threaded direct : Meta.MatcherApp)
        (passed : FVarId) => do
      let sides := fun (pairs : Array (FVarId × FVarId)) (xs ys : Array Expr) =>
        if left then all pairs xs ys else all pairs ys xs
      unless ← sides pairs (threaded.params.push threaded.motive ++ threaded.discrs
          ++ threaded.remaining.extract 1)
          (direct.params.push direct.motive ++ direct.discrs ++ direct.remaining) do
        return false
      for i in [:threaded.alts.size] do
        let numParams := threaded.altNumParams[i]!
        let equal ← Meta.lambdaBoundedTelescope threaded.alts[i]! numParams fun xs body =>
          Meta.lambdaBoundedTelescope direct.alts[i]! numParams fun ys body' => do
            unless xs.size == numParams && ys.size == numParams do return false
            let .lam name type body info := body | return false
            Meta.withLocalDecl name info type fun bound => do
              let pair := fun (x y : FVarId) => if left then (x, y) else (y, x)
              let params := (xs.zip ys).map fun (x, y) => pair x.fvarId! y.fvarId!
              sides (pairs ++ params ++ standingFor left pairs passed bound.fvarId!)
                #[body.instantiate1 bound] #[body']
        unless equal do return false
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
      | some xs, some ys => all pairs xs ys
      | none, none =>
        if let some (threaded, direct, passed) ← threadedMatch? a b then
          threadedEqual true threaded direct passed
        else if let some (threaded, direct, passed) ← threadedMatch? b a then
          threadedEqual false threaded direct passed
        else if ← equalErased fuel pairs a.getAppFn b.getAppFn then
          all pairs a.getAppArgs b.getAppArgs
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
the parameters `value`, its helper's value, binds: the position Lean recorded for it
(`Structural.eqnInfoExt`). The parameters are read from the leading binders of `value`, not from
the observed type, which need not show them where the type is a definition that does not unfold.
`none` if Lean recorded none, `base` is no definition with the level parameters `levelParams`, or
`value` binds no parameter at that position. -/
private def observedRecursionArgument? (base : Name) (levelParams : List Name) (value : Expr) :
    MetaM (Option TerminationMeasure) := do
  let some recorded := Structural.eqnInfoExt.find? (← getEnv) base | return none
  let some (.defnInfo observed) := (← getEnv).find? base | return none
  unless observed.levelParams == levelParams do return none
  Meta.lambdaTelescope value fun params _ => do
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

/-- `env` with no definition irreducible: each name that an imported module's reducibility entries,
the current file's, or the scoped ones in force mark irreducible, and that is irreducible in `env`,
is given the status its declaration shows instead, `reducible` for an `abbrev` (the kernel's
reducibility hint, fixed when the definition was admitted) and semireducible otherwise.
Reducibility guides elaboration and is no part of a declaration: nothing records which definitions
were irreducible where a definition was elaborated, and whatever the assignment, a recursion
compiler's result is a definition the kernel checks. A definition that was `@[reducible]` without
being an `abbrev`, `instance_reducible` or `implicit_reducible` before it was made irreducible is
not told apart from an ordinary one here; `unsafeRecRegeneration` then searches those statuses for
the definitions of the helper's module (`earlierStatuses`). -/
private def withoutIrreducible (env : Environment) : Environment :=
  let marked := fun (names : Array Name) (name : Name) (status : ReducibilityStatus) =>
    if status matches .irreducible then names.push name else names
  let recorded := (Array.range env.header.moduleNames.size).foldl (init := #[]) fun names index =>
    (reducibilityCoreExt.getModuleEntries env index).foldl (init := names) fun names entry =>
      marked names entry.1 entry.2
  let recorded := (reducibilityCoreExt.getState env).foldl marked recorded
  let recorded := (reducibilityExtraExt.getState env).fold marked recorded
  let irreducible := recorded.filter (getReducibilityStatusCore env · matches .irreducible)
  let declared := fun (name : Name) => match env.find? name with
    | some (.defnInfo definition) =>
      if definition.hints matches .abbrev then ReducibilityStatus.reducible else .semireducible
    | _ => .semireducible
  reducibilityExtraExt.modifyState env fun statuses =>
    irreducible.foldl (fun statuses name => statuses.insert name (declared name)) statuses

/-- The constants that unfolding `info` can introduce in the checker's own reduction: those its
type and value mention (a theorem's and an opaque constant's too, though Lean 4.34.0's `Meta`
unfolds neither at any transparency, `getUnfoldableConst?`, so following them only adds constants),
and the constructors of an inductive and of a recursor's rules. A
declaration named `info.name ++ `_sunfold`, which Lean's smart unfolding would take for the
unfolding of `info`, is not among them: every observation runs with smart unfolding off
(`withoutSmartUnfolding`), and such a declaration can be authored with any body. -/
private def unfoldReferences (info : ConstantInfo) : Array Name :=
  let mentioned := info.type.getUsedConstants ++
    ((info.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]
  let structural := match info with
    | .inductInfo value => value.ctors.toArray
    | .recInfo value =>
      value.rules.foldl (fun names rule => (names.push rule.ctor) ++ rule.rhs.getUsedConstants) #[]
    | _ => #[]
  mentioned ++ structural

/-- The constants whose reducibility status can decide what Lean's recursion compilers make of
`info` once they reach it: those its type mentions, those its value mentions where it is a
definition, and the constructors of an inductive and of a recursor's rules (`unfoldReferences`). A
theorem's value and an opaque constant's are not followed: Lean 4.34.0's `Meta` unfolds neither, at
any transparency (`getUnfoldableConst?`). The compilers read a theorem's value only where
`Meta.unfoldIfArgIsAppOf` replaces a theorem applied to a bare function of the group they compile,
in the value of a member of that group, and `earlierStatusOptions` takes those values after that
step. -/
private def statusReferences (info : ConstantInfo) : Array Name :=
  match info with
  | .thmInfo _ | .opaqueInfo _ => info.type.getUsedConstants
  | _ => unfoldReferences info

/-- The statuses a definition that has `status` at the end of the audit can have had before a
global attribute gave it `status`: Lean 4.34.0's validation of a global reducibility attribute
(`ReducibilityAttrs.validate`) admits `reducible` and `instance_reducible` on a semireducible
definition, `implicit_reducible` on a semireducible or `instance_reducible` one, and `irreducible`
on any of those three, and under `set_option allowUnsafeReducibility true`, where it checks
nothing, the one further change taken here is `irreducible` on a `reducible` definition. The
semireducible status an irreducible definition can have had is `withoutIrreducible`'s, and is left
out. Nothing is listed for a semireducible definition: the validation admits no global attribute
that gives that status. -/
private def earlierStatuses : ReducibilityStatus → List ReducibilityStatus
  | .reducible => [.semireducible]
  | .instanceReducible => [.semireducible]
  | .implicitReducible => [.semireducible, .instanceReducible]
  | .irreducible => [.reducible, .instanceReducible, .implicitReducible]
  | .semireducible => []

/-- For each definition of `name`'s module that `roots` reach and that a global attribute given
after its declaration can have changed, the statuses it can have had before
(`earlierStatuses` of its status in `env`), paired with its name. `roots` pairs each member of the
helper's group with its value as Lean's recursion compilers work on it: after
`Meta.unfoldIfArgIsAppOf` (Lean 4.34.0's `Meta/Transform.lean:266-288`), which replaces each theorem
applied to a bare function of the group with the theorem's value, the step the structural compiler
takes before it finds the fixed parameters (`Structural/Preprocess.lean:47`) and the well-founded
one before its preprocessing (`WF/Main.lean:38`). The definitions reached are those the members'
types and those values mention, closed under `statusReferences` through the constants of that
module: a constant of an imported module mentions none of this module's. An `abbrev`, which
the kernel's reducibility hint shows, is `reducible` from its declaration, so it is left out
unless it is irreducible in `env`: `withoutIrreducible` gives such an `abbrev` back as
`reducible`, and the status paired with it here keeps it irreducible in that environment too.
Every other definition is taken, because nothing tells a status given at the declaration
(`@[reducible] def`, `instance`) from one a later attribute gave. `none` if the search stops before
it has visited every constant reached, which the bound, one step per constant of `env`, does not
allow: a step visits a constant of the module that no earlier step visited. -/
private def earlierStatusOptions (env : Environment) (name : Name) (roots : Array (Name × Expr)) :
    Option (List (List (Name × ReducibilityStatus))) := Id.run do
  let home := env.getModuleIdxFor? name
  let mut seen : NameSet := roots.foldl (fun seen (root, _) => seen.insert root) {}
  let mut pending := roots.map (·.1)
  let mut options : Array (List (Name × ReducibilityStatus)) := #[]
  for _ in [:env.constants.fold (fun count _ _ => count + 1) 0] do
    let some reached := pending.back? | break
    pending := pending.pop
    let some info := env.find? reached | continue
    let references := match roots.find? (·.1 == reached) with
      | some (_, value) => info.type.getUsedConstants ++ value.getUsedConstants
      | none => statusReferences info
    for mentioned in references do
      if !seen.contains mentioned && env.contains mentioned
          && env.getModuleIdxFor? mentioned == home then
        seen := seen.insert mentioned
        pending := pending.push mentioned
    if let .defnInfo definition := info then
      let status := getReducibilityStatusCore env reached
      let earlier := match definition.hints with
        | .regular _ => earlierStatuses status
        | .abbrev => if status matches .irreducible then [.irreducible] else []
        | .opaque => []
      unless earlier.isEmpty do
        options := options.push (earlier.map fun status => (reached, status))
  return if pending.isEmpty then some options.toList else none

/-- `picked` takes, for some of the lists of `options` and in their order, one member each. -/
private inductive Picks {α : Type} : List α → List (List α) → Prop
  /-- Nothing is taken from no list. -/
  | nil : Picks [] []
  /-- The first list is passed over. -/
  | skip {picked : List α} {alternatives : List α} {rest : List (List α)} :
      Picks picked rest → Picks picked (alternatives :: rest)
  /-- A member of the first list is taken. -/
  | pick {a : α} {picked : List α} {alternatives : List α} {rest : List (List α)} :
      a ∈ alternatives → Picks picked rest → Picks (a :: picked) (alternatives :: rest)

/-- Every list that takes, for some of the lists of `options` and in their order, one member each,
the empty one first; `none` once there are more than `limit + 1` of them, which is decided list by
list from the last one, so that no more than `limit + 1` times the longest list's length plus one
are ever built. -/
private def assignments? {α : Type} (limit : Nat) : List (List α) → Option (List (List α))
  | [] => some [[]]
  | alternatives :: rest =>
    match assignments? limit rest with
    | none => none
    | some tail =>
      let all := tail ++ alternatives.flatMap fun a => tail.map (a :: ·)
      if all.length ≤ limit + 1 then some all else none

/-- What `assignments?` returns begins with the empty list, holds at most `limit + 1` lists, and
holds every list that `Picks` relates to `options`. This states nothing about what the lists of
`options` are. -/
private theorem assignments?_spec {α : Type} (limit : Nat) (options : List (List α))
    (all : List (List α)) (returned : assignments? limit options = some all) :
    (∃ others, all = [] :: others) ∧ all.length ≤ limit + 1 ∧
      ∀ picked, Picks picked options → picked ∈ all := by
  induction options generalizing all with
  | nil =>
    simp only [assignments?, Option.some.injEq] at returned
    subst returned
    refine ⟨⟨[], rfl⟩, by simp, ?_⟩
    intro picked picks
    cases picks
    simp
  | cons alternatives rest ih =>
    unfold assignments? at returned
    split at returned
    · cases returned
    · rename_i tail found
      dsimp only at returned
      split at returned
      · rename_i bounded
        cases returned
        obtain ⟨⟨others, shape⟩, _, complete⟩ := ih tail found
        refine ⟨⟨others ++ alternatives.flatMap fun a => tail.map (a :: ·), by simp [shape]⟩,
          bounded, ?_⟩
        intro picked picks
        cases picks with
        | skip picks => exact List.mem_append_left _ (complete _ picks)
        | pick member picks =>
          refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, member, ?_⟩)
          exact List.mem_map.mpr ⟨_, complete _ picks, rfl⟩
      · cases returned

/-- The candidate assignments searched for `options`, and whether they are all of them: every
nonempty list that takes one member each from some of the lists of `options` when there are at most
`limit` (`assignments?`), and otherwise the first `limit` single members. -/
private def candidates {α : Type} (limit : Nat) (options : List (List α)) :
    List (List α) × Bool :=
  match assignments? limit options with
  | some all => (all.tail, true)
  | none => ((options.flatten.take limit).map fun a => [a], false)

/-- `candidates` returns at most `limit` assignments, whatever `options` holds: the bound on the
search. -/
private theorem candidates_length_le {α : Type} (limit : Nat) (options : List (List α)) :
    (candidates limit options).1.length ≤ limit := by
  unfold candidates
  split
  · rename_i all found
    have bounded := (assignments?_spec limit options all found).2.1
    simp only [List.length_tail]
    omega
  · simp only [List.length_map, List.length_take]
    omega

/-- Where `candidates` answers that its assignments are all of them, they hold every nonempty
list that `Picks` relates to `options`: the search over them is exhaustive. This states nothing
about what a regeneration does with an assignment. -/
private theorem mem_candidates {α : Type} (limit : Nat) (options : List (List α))
    (picked : List α) (exhaustive : (candidates limit options).2 = true)
    (picks : Picks picked options) (nonempty : picked ≠ []) :
    picked ∈ (candidates limit options).1 := by
  unfold candidates at exhaustive ⊢
  split at exhaustive
  · rename_i all found
    obtain ⟨⟨others, shape⟩, _, complete⟩ := assignments?_spec limit options all found
    have member := complete picked picks
    subst shape
    simpa [nonempty] using member
  · simp at exhaustive

/-- The candidate assignments one helper's search tries at most: with the two regenerations before
the search and two per assignment, at most `2 + 2 * candidateLimit` regenerations, 128, of at most
three compiler runs each. -/
private def candidateLimit : Nat := 63

/-- `env` with each definition of `statuses` given the status paired with it. -/
private def withStatuses (env : Environment) (statuses : List (Name × ReducibilityStatus)) :
    Environment :=
  reducibilityExtraExt.modifyState env fun recorded =>
    statuses.foldl (fun recorded (name, status) => recorded.insert name status) recorded

/-- Whether `value` mentions a constant that `inspected` does not hold. -/
private def mentionsAbsent (inspected : Environment) (value : Expr) : Bool :=
  (value.find? fun e => e.isConst && !inspected.contains e.constName!).isSome

/-- `value` with every constant that `inspected` does not hold replaced by the value `searched`
gives that constant, at the constant's universe levels, in at most `passes` passes over it; `none`
if it still mentions such a constant after them, as it does when one has no value. A proof search
adds constants to its own environment (a theorem Lean realizes, a regenerated definition); this
puts each back as the term it abbreviates, so that the proof can be given to the kernel of the
inspected environment. -/
private def closedOver (inspected searched : Environment) (passes : Nat) (value : Expr) :
    Option Expr :=
  if !mentionsAbsent inspected value then some value
  else match passes with
    | 0 => none
    | passes + 1 => closedOver inspected searched passes <| value.replace fun
        | .const n us =>
          if inspected.contains n then none
          else match searched.find? n with
            | some (.defnInfo added) => added.value.instantiateLevelParams added.levelParams us
            | some (.thmInfo added) => added.value.instantiateLevelParams added.levelParams us
            | _ => none
        | _ => none

/-- What `closedOver` returns mentions only constants `inspected` holds, for every searched
environment, pass count and value. This states nothing about `Expr.replace`, about the values put
back, or about what the kernel makes of the result: a term that mentioned another constant would be
rejected by the kernel of `inspected` as well. -/
private theorem closedOver_closed (inspected searched : Environment) (passes : Nat)
    (value result : Expr) (closed : closedOver inspected searched passes value = some result) :
    mentionsAbsent inspected result = false := by
  induction passes generalizing value with
  | zero =>
    unfold closedOver at closed
    split at closed <;> simp_all
  | succ passes ih =>
    unfold closedOver at closed
    split at closed
    · simp_all
    · exact ih _ closed

/-- The passes `closedOver` makes at most: the depth to which the constants a proof search adds
mention one another (an unfolding theorem, the regenerated definition it is about, that
definition's auxiliary definitions, a matcher's equations and splitter). A proof that needs more is
not used. -/
private def closurePasses : Nat := 64

/-- Whether `statement` is the recursion equation of `base` for `value`: with `value` the function
`fun xs => body`, exactly `∀ xs, base xs = body`, with the binder types and the body of `value`
itself (`Expr` equality), every leading binder of `value` taken, and `base` applied to the bound
variables in their order. `depth` counts the binders passed. The type and universe level of the
equality are not compared: the kernel checks that the statement is well typed before it checks a
proof, which leaves the equality only the type of `base xs`, up to definitional equality. -/
private def isRecursionEquation (base : Expr) : Expr → Expr → Nat → Bool
  | .lam _ type body _, .forallE _ type' statement _, depth =>
    type == type' && isRecursionEquation base body statement (depth + 1)
  | body, statement, depth =>
    !body.isLambda && statement.isAppOfArity ``Eq 3
      && statement.getArg! 1 == mkAppN base ((Array.range depth).reverse.map Expr.bvar)
      && statement.getArg! 2 == body

/-- The names Lean gives the unfolding theorem of `base`: `base.eq_def`, and that name private to
the module of `base`, which Lean uses where a `module` file does not export the body. -/
private def unfoldingTheoremNames (env : Environment) (base : Name) : Array Name :=
  let name := Name.str base Meta.unfoldThmSuffix
  match env.getModuleIdxFor? base with
  | some index =>
    #[name, mkPrivateNameCore env.header.moduleNames[index.toNat]! (privateToUserName name)]
  | none => #[name]

/-- Lean's unfolding theorem of `name` in the current environment (`Meta.getUnfoldEqnFor?`, which
realizes it where the environment does not hold it) at `levels`, as a term closed over `inspected`
(`closedOver`); `none` where Lean gives none or the term cannot be closed. A proof to try, nothing
more: Lean finds the theorem by name and from what it records about the definition, and realizes
it without the kernel. The current environment keeps what the search adds; the caller restores it.
A `checkerLimit?` reached is rethrown. -/
private def unfoldingProof? (inspected : Environment) (name : Name) (levels : List Level) :
    MetaM (Option Expr) := do
  try
    let some unfolding ← Meta.getUnfoldEqnFor? name | return none
    return closedOver inspected (← getEnv) closurePasses (mkConst unfolding levels)
  catch ex =>
    if (← checkerLimit? ex).isSome then throw ex
    return none

/-- Whether Lean's kernel checks, in the inspected environment (the current one), the recursion
equation of the definition `base` for `value`, its helper's value with every helper of the group
replaced by its base: the theorem, with `value` the function `fun xs => body`,

`∀ xs, base xs = body`

by a proof that uses no axiom outside `checkedAxioms`. The checker builds the statement from the
constant `base` and from `value` alone and gives that statement itself to the kernel as the type
of a theorem (`kernelChecked`), after `isRecursionEquation` has confirmed its form by `Expr`
equality. No theorem is taken on its name and no statement is compared with another: whatever
proof is found, the kernel checks it against this statement, in the environment the audit
inspects. What the search reads only proposes proofs, tried in this order, each closed over the
inspected environment before it is submitted (`closedOver`), so that the kernel checks every step
that is not a constant of that environment:

- `Eq.refl (base xs)`, where `body` is a proof (`Meta.isProof`): Lean states no unfolding theorem
  for a definition whose type is a proposition, and the kernel accepts this one by proof
  irrelevance;
- the constants of `unfoldingTheoremNames` the environment holds: Lean's `base.eq_def`, which its
  well-founded compiler adds with the definition;
- the theorem Lean realizes for `base` (`unfoldingProof?`); and
- the theorem Lean realizes for the definition `regenerated?` names in the environment given with
  it, the one a regeneration that reproduced `base` left: the regenerated definition, under the
  reducibility in which Lean's compiler reproduces `base`.

A statement no candidate proves answers `false`, as does one the search cannot build. Nothing is
kept: the theorem and every constant the search adds are discarded. A `checkerLimit?` reached is
rethrown, in the search or in the kernel: the helper is then undecided, not rejected. -/
private def recursionEquationChecked (base : Name) (levelParams : List Name) (value : Expr)
    (regenerated? : Option (Environment × Name)) : MetaM Bool := do
  let inspected ← getEnv
  let levels := levelParams.map mkLevelParam
  let function := mkConst base levels
  let saved ← Meta.saveState
  let accepted := fun (statement : Expr) (proof? : Option Expr) => do
    let some proof := proof? | return false
    try
      -- Whatever a search added is gone before the kernel is asked.
      saved.restore
      kernelChecked statement proof
    catch ex =>
      if (← checkerLimit? ex).isSome then throw ex
      return false
    finally
      saved.restore
  try
    let (statement, irrelevant?) ← Meta.lambdaTelescope value fun xs body => do
      let applied := mkAppN function xs
      -- The type is read from `body`: that of `base xs` need not show where the type of `base` is
      -- a definition that does not unfold.
      let type ← Meta.inferType body
      let level ← Meta.getLevel type
      let statement ← Meta.mkForallFVars xs (mkApp3 (mkConst ``Eq [level]) type applied body)
      unless ← Meta.isProof body do return (statement, none)
      let reflexivity := mkApp2 (mkConst ``Eq.refl [level]) type applied
      return (statement, some (← Meta.mkLambdaFVars xs reflexivity))
    unless isRecursionEquation function value statement 0 do return false
    if ← accepted statement irrelevant? then return true
    for name in unfoldingTheoremNames inspected base do
      if inspected.contains name then
        if ← accepted statement (mkConst name levels) then return true
    let realized? ← unfoldingProof? inspected base levels
    saved.restore
    if ← accepted statement realized? then return true
    let some (regeneration, name) := regenerated? | return false
    -- The regeneration's environment differs in what unfolds, and `saveState` does not cover
    -- Lean's elaboration caches.
    setEnv regeneration
    Meta.resetCache
    let regenerated? ← unfoldingProof? inspected name levels
    saved.restore
    Meta.resetCache
    accepted statement regenerated?
  catch ex =>
    if (← checkerLimit? ex).isSome then throw ex
    return false
  finally
    saved.restore
    Meta.resetCache

/-- `Declaration.unsafeRecRegenerated`: rerun Lean's own recursion compiler on the helper's group,
each helper's value becoming the body of a fresh definition under `regenerationRoot` with its calls
to the group's helpers standing for the recursive calls, and compare what it generates with the
observed base and its auxiliary definitions (`regenerationMatches`). A helper whose base a
regeneration reproduces is admitted only where Lean's kernel then checks, for each helper of the
group, the recursion equation of its base for the helper's value (`recursionEquationChecked`).
The regeneration selects the base and the route recorded; that the helper computes the base rests
on the kernel-checked equation, not on the regeneration or on what Lean's compilers read while it
runs (matcher metadata, the `below` and `brecOn` declarations of an inductive type, reducibility
statuses), all of which the audited source can write. The first regeneration that reproduces the
base decides: where an equation is then not checked, the helper is not admitted and no further
regeneration is tried. The regeneration reads the
termination argument of the observed bases, since the value a compiler generates depends on it:
the well-founded compiler passes the recursive-call function through a `match` where that
function's type, which holds the relation and the measure, changes in an alternative. Structural
recursion is tried first with Lean's automatic choice, then, where that does not match and Lean
recorded an argument position for a base, on the recorded positions (`observedRecursionArgument?`;
a read that throws reads nothing), which admits a definition recursing on an argument
`termination_by structural` selects. A recorded position alone does not determine Lean's structural
compilation: the automatic choice can reach the same position through another argument's inductive
group. Well-founded recursion is tried last, with the relation of the base's own fixpoint
(`wfRegeneration`) and with every decreasing proof elided (`all_goals exact sorry`, on the raw
goal), since the comparison erases proofs and the observed base's own kernel-checked value supplies
them. A termination argument only selects which regeneration runs: whatever is read, a helper is
admitted only when the definitions that regeneration adds match the observed ones. The compiler
runs in `regenerationEnvironment`, with the fresh definitions `noncomputable` so that no code is
generated for them. Where none of these attempts matches, all run once more in that environment
with no definition irreducible, each given the status its declaration shows (`withoutIrreducible`):
Lean does not record which definitions were irreducible where the base was compiled, and what it
unfolds decides which argument its structural compiler finds and where the function is passed
through a `match`. That, too, only selects which regeneration runs. Where neither environment
reproduces the base, the regeneration searches the statuses a later global attribute can have
replaced: Lean's fixed-parameter analysis and its `wf_preprocess` simplification unfold at
reducible transparency, and at implicit transparency where they compare an instance-implicit
argument, so a definition that is `reducible`, `instance_reducible` or `implicit_reducible` at only
one of the two points changes which parameters the compilers pack and which toolchain rule
rewrites the body. Each candidate assignment (`candidates` of `earlierStatusOptions`) gives some
of the definitions of the helper's module that its group reaches an earlier status
(`earlierStatuses`), and all attempts run under it in the inspected environment and in the one
with no definition irreducible, each run with the heartbeat budget of one declaration. An
assignment is read from statuses, kernel hints and module membership, all of which the audited
source can write; like the termination argument it only selects which regeneration runs, is never
an argument of the comparison, and is undone with the rest of the run before the comparison. The
search is exhaustive over those assignments when there are at most `candidateLimit` of them
(`mem_candidates`), and then a helper no attempt reproduces is not regenerated. Otherwise only the
first `candidateLimit` single changes are tried (`candidates_length_le`), and a helper none of them
reproduces is undecided, as is one whose reached definitions were not all visited: the
regeneration throws, so the audit is incomplete and the helper is neither admitted nor rejected.
Lean's elaboration caches
are emptied on entering and leaving each attempt, since the environments differ in what unfolds
and `saveState` does not cover the caches. A regeneration that reports an error does not count.
Every change is undone before the comparison, which reads the observed definitions and decides
erasure in the inspected environment: whatever code runs during a regeneration, only the
definitions it adds are compared. The regeneration and the comparison run with smart unfolding off
(`withoutSmartUnfolding`, which `declaration` applies), so no `_sunfold` declaration is read for
another constant's unfolding; the `_sunfold` definition the structural compiler adds for a
regenerated base is compared with the observed one like every definition it adds,
each with the theorems the regeneration abstracted from it put back (`regeneratedDefinitions`), so
the result does not depend on how Lean named or shared those theorems. A comparison that throws
does not count either. A `checkerLimit?` reached is rethrown. -/
private def unsafeRecRegeneration (env : Environment) (name : Name) (info : ConstantInfo)
    (preprocessRules : IO.Ref (Option Meta.SimpTheorems)) :
    CommandElabM (Option RecursionOrigin) := do
  let some _ := Lean.Compiler.isUnsafeRecName? name | return none
  let .defnInfo helper := info | return none
  let group := helper.all.toArray
  -- The equations checked are those of the group's members, so the helper has to be one.
  unless group.contains name do return none
  let some bases := group.mapM (fun member => do
      let base ← Lean.Compiler.isUnsafeRecName? member
      guard <| (env.find? member).any (· matches ConstantInfo.defnInfo _)
      guard <| (env.find? base).any (· matches ConstantInfo.defnInfo _)
      pure base)
    | return none
  let rename := fun (value : Expr) => value.replace fun
    | .const n us => (group.idxOf? n).map fun i => mkConst (regenerationRoot ++ bases[i]!) us
    | _ => none
  let toBases := fun (value : Expr) => value.replace fun
    | .const n us => (group.idxOf? n).map fun i => mkConst bases[i]! us
    | _ => none
  liftTermElabM do
    let preDefs ← group.mapIdxM fun i member => do
      let some (.defnInfo value) := env.find? member | throwError "missing helper {member}"
      return ({ ref := .missing, kind := .def, levelParams := value.levelParams,
                modifiers := { computeKind := .noncomputable },
                declName := regenerationRoot ++ bases[i]!, binders := .missing, type := value.type,
                value := rename value.value, termination := .none } : PreDefinition)
    let regenerating ← regenerationEnvironment (← getEnv)
      (← cachedPreprocessRules preprocessRules env)
    -- The environment a regeneration that reproduces the base leaves; `none` where it does not.
    let attempt (environment : Environment) (run : TermElabM Unit) :
        TermElabM (Option Environment) := do
      let saved ← saveState
      try
        Core.resetMessageLog
        setEnv environment
        Meta.resetCache
        withOptions (·.setBool `debug.rawDecreasingByGoal true) run
        let failed := (← Core.getMessageLog).hasErrors
        let after ← getEnv
        saved.restore
        Meta.resetCache
        if failed then return none
        let some regenerated := regeneratedDefinitions environment after | return none
        return if ← regenerationMatches regenerated then some after else none
      catch ex =>
        saved.restore
        Meta.resetCache
        if (← checkerLimit? ex).isSome then throw ex
        return none
      finally
        -- A runtime limit (heartbeats, recursion depth) bypasses `catch`; undo the run anyway.
        saved.restore
        Meta.resetCache
    let docCtx := (← getLCtx, ← Meta.getLocalInstances)
    let noMeasures := preDefs.map fun _ => (none : Option TerminationMeasure)
    let elided ← `(Lean.Parser.Tactic.tacticSeq| all_goals exact sorry)
    let wfDefs := preDefs.map fun (preDef : PreDefinition) =>
      { preDef with termination := { TerminationHints.none with
          decreasingBy? := some ({ ref := .missing, tactic := elided } : DecreasingBy) } }
    let regenerate (environment : Environment) :
        TermElabM (Option (RecursionOrigin × Environment)) := do
      if let some after ← attempt environment (structuralRecursion docCtx preDefs noMeasures) then
        return some (.structural, after)
      let recursionArguments ← preDefs.mapIdxM fun i (preDef : PreDefinition) => do
        try
          observedRecursionArgument? bases[i]! preDef.levelParams preDef.value
        catch ex => if (← checkerLimit? ex).isSome then throw ex else pure none
      if recursionArguments.any (·.isSome) then
        if let some after ← attempt environment
            (structuralRecursion docCtx preDefs recursionArguments) then
          return some (.structural, after)
      if let some after ← attempt environment (wfRegeneration regenerationRoot docCtx wfDefs) then
        return some (.wellFounded, after)
      return none
    -- The regeneration selected the base; the kernel decides, for each member of the group.
    let admitted (origin : RecursionOrigin) (after : Environment) :
        TermElabM (Option RecursionOrigin) := do
      for i in [:group.size] do
        let some (.defnInfo member) := env.find? group[i]! | return none
        unless ← recursionEquationChecked bases[i]! member.levelParams (toBases member.value)
            (some (after, regenerationRoot ++ bases[i]!)) do
          return none
      return some origin
    if let some (origin, after) ← regenerate regenerating then return ← admitted origin after
    let unsealed := withoutIrreducible regenerating
    if let some (origin, after) ← regenerate unsealed then return ← admitted origin after
    let undecided := m!"no regeneration of {name} reproduced its base, and the helper is \
      undecided, neither admitted nor rejected: "
    let fnNames := preDefs.map (·.declName)
    let numSectionVars := preDefs[0]!.numSectionVars
    let roots ← preDefs.mapIdxM fun i (preDef : PreDefinition) => do
      return (group[i]!, ← Meta.unfoldIfArgIsAppOf fnNames numSectionVars preDef.value)
    let some options := earlierStatusOptions env name roots
      | throwError "{undecided}the definitions of its module that it reaches were not all visited."
    let (assignments, exhaustive) := candidates candidateLimit options
    for assignment in assignments do
      for environment in [regenerating, unsealed] do
        if let some (origin, after) ← withCurrHeartbeats <|
            regenerate (withStatuses environment assignment) then
          return ← admitted origin after
    unless exhaustive do
      throwError "{undecided}the definitions of its module that it reaches allow more than \
        {candidateLimit} assignments of an earlier reducibility status, of which only the first \
        {candidateLimit} single changes were tried. Give each function it calls its reducibility \
        where the function is declared."
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

/-- Whether reducing `type` can produce `Regula.ExecutableContract`: whether the contract type is
among the constants `type` mentions, closed under `unfoldReferences`. Lean's reduction steps
(delta, iota, beta, zeta, eta, projection, and literal and native Boolean or natural-number steps)
introduce only constants of that closure or of `Init`, which does not import `Regula.Contract`;
the reduction this guards runs inside `declaration`, with smart unfolding off. Constants of modules
outside the scope are not expanded, and a search that ends without finding the contract type
records every constant it expanded as free. -/
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
      pending := pending ++ unfoldReferences info
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
fresh scope is built. Every observation runs with smart unfolding off (`withoutSmartUnfolding`). -/
def declaration (name : Name) (stage : Stage) (scope? : Option ContractScope := none) :
    CommandElabM RegulaPolicy.Declaration := withoutSmartUnfolding do
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
