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
public import Regula.CompilerObservation
public import Lean.Meta.Eqns
public import Lean.Meta.Injective
public import Lean.Meta.SameCtorUtils
public import Lean.Meta.Constructions.CtorElim
public import Lean.Meta.Constructions.CasesOn
public import Lean.Compiler.LCNF.Util
public import Lean.Class
public import Lean.Elab.PreDefinition.Structural.Eqns
public import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
public import Lean.Server.Rpc.RequestHandling
public import RegulaPolicy.GeneratedFamily
public import RegulaPolicy.StatementReading
public import Lean.Meta.RecExt
public import Lean.Meta.DiscrTree.Util
public import Lean.ProjFns
public import Lean.Util.FoldConsts
public import RegulaPolicy.Domain
public import RegulaPolicy.Erasure
public import RegulaPolicy.NativeStatement
public import RegulaPolicy.MentionSearch
public import Regula.Contract
public import Regula.Decision
public import RegulaPolicy.KernelAxioms

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
open RegulaPolicy.Erasure (fixpointArguments?)

private initialize capabilityCache : IO.Ref (Option RegulaPolicy.Compiler.LegacyCompilerTrust) ←
  IO.mkRef none

private initialize toolchainLibrary : IO.Ref (Option System.FilePath) ← IO.mkRef none

/-- The library directory of the running Lean toolchain, found once for the process. -/
private def toolchainLibraryDirectory : IO System.FilePath := do
  if let some directory ← toolchainLibrary.get then return directory
  let directory ← Lean.getLibDir (← Lean.findSysroot)
  toolchainLibrary.set (some directory)
  return directory

/-- Whether Lean loaded the module `moduleName` from the toolchain library directory `library`:
its `.olean` file is that module's file in `library`, by canonical path. A module's name does not
establish this, since a project or a dependency can supply a module under `Init`, `Std` or
`Lean`. That the path identifies the toolchain's own artifact is a filesystem observation. -/
private def loadedFromLibrary (library : System.FilePath) (moduleName : Name) : IO Bool := do
  let expected := Lean.modToFilePath library moduleName "olean"
  unless ← expected.pathExists do return false
  return (← IO.FS.realPath (← Lean.findOLean moduleName)) == (← IO.FS.realPath expected)

/-- Memoize the Core capability after independently confirming the resolved compiler's
identity. Installation contents and process execution remain trusted. -/
def compilerCapability : IO RegulaPolicy.Compiler.LegacyCompilerTrust := do
  if let some capability ← capabilityCache.get then return capability
  let root ← Lean.findSysroot
  let output ← IO.Process.output {
    cmd := (root / "bin/lean").toString, args := #["--stdin"]
    env := #[("LEAN_PATH", none), ("LEAN_SRC_PATH", none), ("LEAN_SYSROOT", none)] }
    (some "#eval IO.println Lean.versionString\n#eval IO.println Lean.githash\n")
  unless output.exitCode == 0 && output.stdout ==
      s!"{RegulaPolicy.Compiler.version}\n{RegulaPolicy.Compiler.commit}\n" do
    throw <| IO.userError "compiler capability: resolved compiler identity differs from this Regula build"
  let capability := if ← Regula.CompilerObservation.legacyPresent (← Lean.getLibDir root)
    then .present else .absent
  let _ ← IO.ofExcept (RegulaPolicy.Compiler.admitCapability capability)
  capabilityCache.set (some capability)
  return capability

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

/-- The Lean v4.34.0 source renderings (`Kernel.Exception.toMessageData`) of the kernel's resource
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

/-- Whether `e` is a proof or a type in the current local context: what Lean's code generator
erases. -/
private def erasedByCompilation (e : Expr) : MetaM Bool := do
  return (← Meta.isProof e) || (← Meta.isType e)

/-- A bound on the names a search in `env` expands: one for each constant of its modules and of
the current module, and `extra` more. Every name a constant of a kernel environment uses is a
constant of it. -/
def fuelFor (env : Environment) (extra : Nat) : Nat :=
  env.header.moduleData.foldl (fun total data => total + data.constants.size) 0 +
    env.constants.map₂.foldl (fun total _ _ => total + 1) 0 + extra

/-- Whether Lean's kernel, in the current environment, accepts `value` as a proof of the closed
statement `type` (`Environment.addDeclCore` on a theorem of a fresh name) and that theorem uses
only axioms that the Standard-Logical profile permits (`RegulaPolicy.standardLogicalAxiom`, the
definition the profile check reads). The theorem's axioms are those it reaches in the kernel
environment that holds it (`KernelAxioms.axiomsWith`): the search stops at each name of
`cached`, the table that admission computed in the replayed kernel for the owned declarations'
closure, and reads its entry there. A statement or a proof with a free variable or a metavariable
answers `false`, and so does a search that runs out of fuel. The theorem stays in the environment,
which the caller restores. What the kernel refuses with is thrown, a rejected proof and a resource
limit alike (its deterministic timeout, deep recursion or excessive memory), and the caller tells
the two apart by `checkerLimit?`. -/
private def kernelChecked (cached : Std.HashMap Name (Array Name)) (type value : Expr) :
    MetaM Bool := do
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
    let some axioms := RegulaPolicy.KernelAxioms.axiomsWith checked.toKernelEnv.find? cached
        (fuelFor checked 1) name | return false
    return axioms.all RegulaPolicy.standardLogicalAxiom

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
only Standard-Logical axioms (`kernelChecked`). The right-hand side is well typed only where `A ds`
and each `A (pᵢ xs)` are definitionally equal, which the kernel decides whatever is irreducible.
Nothing is kept: the theorem, and every constant the search realizes, is discarded. A search that
fails, or a theorem the kernel rejects, answers `false`. A `checkerLimit?` reached is rethrown, in
the search or in the kernel (its deterministic timeout, deep recursion or excessive memory): the
helper is then undecided, not rejected. -/
private def threadingLawChecked (cached : Std.HashMap Name (Array Name))
    (threaded : Meta.MatcherApp) : MetaM Bool := do
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
        kernelChecked cached type value
  let saved ← Meta.saveState
  try
    search
  catch ex =>
    if (← checkerLimit? ex).isSome then throw ex
    return false
  finally
    saved.restore

/-- What the observing pass has recorded of the terms of one side: each table holds the answers
given so far, by term. `Expr` equality and hashing identify terms that differ only in binder
names and annotations, on which no observation depends. -/
private structure SideObserved where
  /-- Whether a term is a proof or a type in its own context (`erasedByCompilation`). -/
  erased : Std.HashMap Expr Bool := {}
  /-- The variable a binder's body is read with. -/
  bound : Std.HashMap Expr FVarId := {}
  /-- The decomposition of an application for which the kernel checked the threading law, or that
  the pass found none. -/
  threading : Std.HashMap Expr (Option RegulaPolicy.Erasure.Threading) := {}

/-- The recorded observations as the pure comparison reads them: a term the pass was not asked
about has none. -/
private def SideObserved.observations (seen : SideObserved) : RegulaPolicy.Erasure.Observations :=
  { erased := (seen.erased[·]?), bound := (seen.bound[·]?), threading := (seen.threading[·]?) }

/-- The state of the observing pass of one regeneration: what it has recorded of each side, and
the local context that declares every variable it has bound, of both sides, with the local
instances among them. A variable is declared once, with its binder's own type, so a term names the
variables it is read under and one context serves every term. -/
private structure Observing where
  /-- The observations of the regenerated values' terms. -/
  left : SideObserved := {}
  /-- The observations of the observed values' terms. -/
  right : SideObserved := {}
  /-- The variables bound so far, in the order bound. -/
  context : LocalContext
  /-- The local instances among those variables. -/
  instances : LocalInstances
  /-- The axioms of the names the kernel walk of a threading law can stop at (`kernelChecked`). -/
  cached : Std.HashMap Name (Array Name) := {}

/-- The part of `context` that declares the variables `e` mentions and, in turn, the variables
their declarations mention: the least context `e` is well typed in. A declaration mentions only
variables declared before it, so one pass from the last declaration to the first finds them. -/
private def scopeOf (context : LocalContext) (e : Expr) : LocalContext :=
  let mentioned := Id.run <| context.foldrM (init := (collectFVars {} e).fvarSet)
    fun declaration mentioned =>
      if mentioned.contains declaration.fvarId then
        let found := collectFVars {} declaration.type
        let found := match declaration.value? (allowNondep := true) with
          | some value => collectFVars found value
          | none => found
        return found.fvarIds.foldl (fun mentioned used => mentioned.insert used) mentioned
      else return mentioned
  context.foldl (init := {}) fun scope declaration =>
    if mentioned.contains declaration.fvarId then scope.addDecl declaration else scope

/-- Record the observation `need` names: the one step of the observing pass. It reads only the
term of `need`, in the context of the variables the pass bound, and never the other side's term.

- `erased`: whether the term is a proof or a type (`erasedByCompilation`).
- `bound`: a fresh variable, declared with the binder's own type (and, for a `let`, its value).
- `threading`: where Lean records the application as a matcher or `casesOn` application
  (`Meta.matchMatcherApp?`) that passes a variable as its first argument after the alternatives,
  and Lean's kernel checks the threading law of that application (`threadingLawChecked`, over the
  variables the application's own terms mention, `scopeOf`), the decomposition the law was checked
  for; otherwise that there is none. What Lean records only proposes the decomposition: the
  recorded answer is that the kernel checked the law for it.

A `checkerLimit?` reached is thrown, as is any other failure of an observation. -/
private def observe (need : RegulaPolicy.Erasure.Need) : StateRefT Observing MetaM Unit := do
  -- Only the context and the instances are read before the observation. Each table is then
  -- updated inside `modify`, where the state is not shared, so an insert does not copy the table.
  let context := (← get).context
  let known := (← get).instances
  match need with
  | .erased side term =>
    let erased ← Meta.withLCtx context known (erasedByCompilation term)
    modify fun state =>
      match side with
      | .left => { state with left := { state.left with
          erased := state.left.erased.insert term erased } }
      | .right => { state with right := { state.right with
          erased := state.right.erased.insert term erased } }
  | .bound side binder =>
    let fresh ← mkFreshFVarId
    let (context, type?) := match binder with
      | .lam name type _ info | .forallE name type _ info =>
        (context.mkLocalDecl fresh name type info, some type)
      | .letE name type value _ _ => (context.mkLetDecl fresh name type value, some type)
      | _ => (context, none)
    let instances ← match type? with
      | some type => Meta.withLCtx context known do
          match ← Meta.isClass? type with
          | some className => pure (known.push { className, fvar := mkFVar fresh })
          | none => pure known
      | none => pure known
    modify fun state =>
      match side with
      | .left => { state with context, instances, left := { state.left with
          bound := state.left.bound.insert binder fresh } }
      | .right => { state with context, instances, right := { state.right with
          bound := state.right.bound.insert binder fresh } }
  | .threading side application =>
    let scope := scopeOf context application
    let instances := known.filter fun (inScope : LocalInstance) =>
      scope.contains inScope.fvar.fvarId!
    let shape? ← Meta.withLCtx scope instances do
      let some matched ← Meta.matchMatcherApp? (alsoCasesOn := true) application | return none
      let some (Expr.fvar _) := matched.remaining[0]? | return none
      unless ← threadingLawChecked (← get).cached matched do return none
      return some ({ params := matched.params.size, discriminants := matched.discrs.size,
                     alternatives := matched.altNumParams, motiveLevel := matched.uElimPos? } :
        RegulaPolicy.Erasure.Threading)
    modify fun state =>
      match side with
      | .left => { state with left := { state.left with
          threading := state.left.threading.insert application shape? } }
      | .right => { state with right := { state.right with
          threading := state.right.threading.insert application shape? } }

/-- The budget of observations for one step of the comparison. A step asks for the erasure of
its two terms, one decomposition, and one variable for each binder of the alternatives of a
`match`, so a `match` with enough binders needs more than the budget. A step that still needs an
observation after the budget is left as it is: the pass stops and reports that it did not finish,
which `RegulaPolicy.Erasure.reproduces` refuses (`reproduces_eq_false_of_unfinished`). -/
private def stepNeeds : Nat := 1000000

/-- One step of the pure comparison of `a` with `b` (`RegulaPolicy.Erasure.step`), with each
observation it asks for recorded (`observe`), at most `needs` of them. What is returned is always
the pure step's own answer over what the pass has recorded: where the step still needs an
observation after `needs` of them, that answer is the refusal that names the need, and the pass
records nothing more for it. -/
private def stepObserved (pairs : RegulaPolicy.Erasure.Pairs) (a b : Expr) :
    Nat → StateRefT Observing MetaM RegulaPolicy.Erasure.Step
  | 0 => do
    let state ← get
    return RegulaPolicy.Erasure.step state.left.observations state.right.observations pairs a b
  | needs + 1 => do
    let state ← get
    match RegulaPolicy.Erasure.step state.left.observations state.right.observations pairs a b with
    | .error (.unobserved need) =>
      observe need
      stepObserved pairs a b needs
    | settled => return settled

/-- The observing pass over two terms: record every observation the pure comparison of `a` with
`b` asks for, to depth `fuel`, by taking the comparison's own steps (`stepObserved`) part by part
in its order, and stopping at the first part it refuses. So the pass asks Lean what the
comparison reads and nothing else, and carries no comparison rule of its own. The answer returned
says whether the pass finished: `false` where it stopped at a part the comparison refuses, at
exhausted depth or at `stepNeeds`. The verdict is `RegulaPolicy.Erasure.reproduces` over what was
recorded and that answer: it refuses whatever was left unobserved, and it refuses a pass that did
not finish (`RegulaPolicy.Erasure.reproduces_eq_false_of_unfinished`).

The pass binds each binder a fresh variable (`observe`), and a term cannot hold itself as a part,
so the variables of one path are different and the comparison's test that they are new
(`RegulaPolicy.Erasure.newVariables`) holds for them. The two values the pass is given have no
free variable, so each free variable of a part is the variable of a binder the comparison opened,
which a pair holds: the comparison's test that a pair holds the variable passed to a threaded
`match` (`RegulaPolicy.Erasure.alternative`) holds too. Both are arguments, and the second rests
on what `Expr.instantiate1` does to the free variables of a term, which has no specification.
The tests, not these arguments, are what the verdict rests on. -/
private def observeEqual : Nat → RegulaPolicy.Erasure.Pairs → Expr → Expr →
    StateRefT Observing MetaM Bool
  | 0, _, _, _ => return false
  | fuel + 1, pairs, a, b => do
    match ← stepObserved pairs a b stepNeeds with
    | .ok parts => parts.allM fun part => observeEqual fuel part.pairs part.left part.right
    | .error _ => return false

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
its name in the current environment; at least one must have been regenerated. The observing pass
(`observeEqual`) records what the comparison asks about each pair of values, in order, and stops at
the first pair it refuses or at its bound. The verdict is then the pure decision
`RegulaPolicy.Erasure.reproduces`, run through its registered contract, over the regenerated and
the observed values, those observations and whether the pass finished
(`RegulaPolicy.Erasure.reproduces_iff`): nothing else of the environment, and nothing that selected
the regeneration, is an argument of it. A pass that did not finish is refused by the decision
itself (`RegulaPolicy.Erasure.reproduces_eq_false_of_unfinished`). -/
private def regenerationMatches (cached : Std.HashMap Name (Array Name))
    (regenerated : Array (Name × Expr)) : MetaM Bool := do
  let env ← getEnv
  let definitions := regenerated.toList.map fun (name, value) =>
    (value, match env.find? name with
      | some (.defnInfo observed) => some observed.value
      | _ => none)
  let observing := definitions.allM fun
    | (value, some observed) => observeEqual RegulaPolicy.Erasure.depthLimit #[] value observed
    | (_, none) => pure false
  let (finished, seen) ← observing.run
    { context := ← getLCtx, instances := ← Meta.getLocalInstances, cached }
  return RegulaPolicy.Erasure.checked_reproduces.run
    { regenerated := seen.left.observations, observed := seen.right.observations, definitions,
      finished }

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

/-- The first steps of Lean 4.34.0's `wfRecursion`, each Lean's own function in its order: the
recursive applications floated (`WF.floatRecApp`), the fixed parameters found
(`getFixedParamPerms`), and the group packed into one unary definition (`WF.packMutual`). Returns
the floated definitions, the fixed parameters, the packing and that unary definition. Throws if a
definition has no varying argument. -/
private def wfPacked (preDefs : Array PreDefinition) :
    TermElabM (Array PreDefinition × FixedParamPerms × Meta.ArgsPacker × PreDefinition) := do
  let names := preDefs.map (·.declName)
  let preDefs ← preDefs.mapM fun preDef =>
    return { preDef with value := (← WF.floatRecApp preDef.value) }
  withoutModifyingEnv do
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
    return (preDefs, fixedParamPerms, argsPacker,
      ← WF.packMutual fixedParamPerms argsPacker unfolded)

/-- Lean 4.34.0's `wfRecursion` up to the definitions it adds, with one change: the relation is
the observed base's own. Where `wfRecursion` elaborates a relation from termination measures
(`WF.elabWFRel`, which synthesizes a `WellFoundedRelation` instance in the current environment),
this reads it from the fixpoint of the observed definition that has the name of the unary
definition Lean packs the group into, less `root`, applied to the group's fixed parameters
(`fixpointRelation?`). Every step is Lean's own function, in `wfRecursion`'s order (`wfPacked`
holds the first of them); what `wfRecursion` does after adding the definitions (helper
compilation, equation lemmas, attributes) is left out. Throws if the observed definition applies
no such fixpoint. -/
private def wfRegeneration (root : Name) (docCtx : LocalContext × LocalInstances)
    (preDefs : Array PreDefinition) : TermElabM Unit := do
  let names := preDefs.map (·.declName)
  let (preDefs, fixedParamPerms, argsPacker, unaryPreDef) ← wfPacked preDefs
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
loaded from the toolchain's own library directory, recognized by canonical path
(`loadedFromLibrary`). Rules a project or dependency adds are left out. -/
private def toolchainPreprocessRules (env : Environment) : IO Meta.SimpTheorems := do
  let ext := Lean.Elab.WF.wfPreprocessSimpExtension
  let library ← toolchainLibraryDirectory
  let mut rules ← ext.descr.mkInitial
  for (moduleName, index) in env.header.moduleNames.zipIdx do
    let entries := ext.ext.getModuleEntries env index
    if entries.isEmpty then continue
    unless ← loadedFromLibrary library moduleName do continue
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

/-- The names whose reducibility status in `env` (`getReducibilityStatusCore`) satisfies `wanted`,
among those an imported module's reducibility entries, the current file's, or the scoped and local
ones in force give a status that does. A name no entry mentions is semireducible, so every name
with another status is among them where `wanted` rejects semireducible. A name can be listed more
than once. -/
private def namesWithStatus (env : Environment) (wanted : ReducibilityStatus → Bool) :
    Array Name :=
  let marked := fun (names : Array Name) (name : Name) (status : ReducibilityStatus) =>
    if wanted status then names.push name else names
  let recorded := (Array.range env.header.moduleNames.size).foldl (init := #[]) fun names index =>
    (reducibilityCoreExt.getModuleEntries env index).foldl (init := names) fun names entry =>
      marked names entry.1 entry.2
  let recorded := (reducibilityCoreExt.getState env).foldl marked recorded
  let recorded := (reducibilityExtraExt.getState env).fold marked recorded
  recorded.filter fun name => wanted (getReducibilityStatusCore env name)

/-- `env` with no definition irreducible: each name that an imported module's reducibility entries,
the current file's, or the scoped ones in force mark irreducible, and that is irreducible in `env`,
is given the status its declaration shows instead, `reducible` for an `abbrev` (the kernel's
reducibility hint, fixed when the definition was admitted) and semireducible otherwise.
Reducibility guides elaboration and is no part of a declaration: nothing records which definitions
were irreducible where a definition was elaborated, and whatever the assignment, a recursion
compiler's result is a definition the kernel checks. A definition that was `@[reducible]` without
being an `abbrev`, `instance_reducible` or `implicit_reducible` before it was made irreducible is
not told apart from an ordinary one here; `unsafeRecRegeneration` then searches the statuses of
the definitions Lean's compilers ask about (`statusCandidates`). -/
private def withoutIrreducible (env : Environment) : Environment :=
  let irreducible := namesWithStatus env (· matches .irreducible)
  let declared := fun (name : Name) => match env.find? name with
    | some (.defnInfo definition) =>
      if definition.hints matches .abbrev then ReducibilityStatus.reducible else .semireducible
    | _ => .semireducible
  reducibilityExtraExt.modifyState env fun statuses =>
    irreducible.foldl (fun statuses name => statuses.insert name (declared name)) statuses

/-- `env` with no definition `reducible`, `instance_reducible` or `implicit_reducible`: each name
with one of those statuses in `env` (`namesWithStatus`) is made semireducible, and an irreducible
one is left as it is. Below default transparency Lean 4.34.0 then unfolds no definition for its
status, so the discriminant of a `match`, which Lean reduces with its unfolding predicate put aside
(`Meta.whnfMatcher`), reduces there only through the definitions it unfolds whatever their status
(`Meta.canUnfoldAtMatcher`). A run in this environment decides nothing: it only shows which
definitions a run asks about (`recordConsults`). -/
private def withoutReducible (env : Environment) : Environment :=
  let unfolding := namesWithStatus env
    (· matches .reducible | .instanceReducible | .implicitReducible)
  reducibilityExtraExt.modifyState env fun statuses =>
    unfolding.foldl (fun statuses name => statuses.insert name .semireducible) statuses

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
(`earlierStatuses` of its status in `env`), paired with its name: what `unsafeRecRegeneration`
tries where the statuses Lean's compilers were recorded asking about reproduce nothing, since a
status Lean reads without asking its unfolding predicate, outside the discriminant of a `match`,
is not recorded (`recordConsults`). `roots` pairs each member of the helper's group with its
value as Lean's recursion compilers work on it: after
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

/-- The statuses the search gives a definition, the one that unfolds least first. Irreducible is
not among them: below default transparency Lean 4.34.0 answers for it as for semireducible
(`Meta.canUnfoldDefault`, `Meta/GetUnfoldableConst.lean:17-31`, read from its source). -/
private def triedStatuses : List ReducibilityStatus :=
  [.semireducible, .implicitReducible, .instanceReducible, .reducible]

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

/-- The candidate assignments one enumeration holds at most. One helper's search makes three: one
in each of its two environments, and one of the definitions of its module that it reaches
(`earlierStatusOptions`), tried in both. With the two regenerations before the search and, in each
environment, the one the observed base selects, that is at most
`2 + 2 * (1 + candidateLimit) + 2 * candidateLimit` regenerations, 256, of at most three compiler
runs each. -/
private def candidateLimit : Nat := 63

/-- `env` with each definition of `statuses` given the status paired with it. -/
private def withStatuses (env : Environment) (statuses : List (Name × ReducibilityStatus)) :
    Environment :=
  reducibilityExtraExt.modifyState env fun recorded =>
    statuses.foldl (fun recorded (name, status) => recorded.insert name status) recorded

/-- A status assignment: definitions, each with the status it is given. -/
private abbrev Statuses := List (Name × ReducibilityStatus)

/-- Whether a definition with `status` unfolds at `transparency`, for the three transparencies
below default: a `reducible` one at each, an `instance_reducible` one at instance and implicit
transparency, an `implicit_reducible` one at implicit transparency, and no other. This restates
what Lean 4.34.0's `Meta.canUnfoldDefault` answers there (`Meta/GetUnfoldableConst.lean:17-31`,
read from its source); `false` at another transparency, where a status answers otherwise. -/
private def unfoldsBelowDefault (status : ReducibilityStatus) : Meta.TransparencyMode → Bool
  | .reducible => (status matches .reducible)
  | .instances => (status matches .reducible | .instanceReducible)
  | .implicit => (status matches .reducible | .instanceReducible | .implicitReducible)
  | _ => false

/-- A status that unfolds at reducible transparency unfolds at instance transparency, and one
that unfolds there unfolds at implicit transparency: a status that answers a question at the
lowest of the transparencies it was asked at answers it at the others too (`newlyStuck`). This is
about `unfoldsBelowDefault` alone, not about Lean's `Meta.canUnfoldDefault`, which it restates. -/
private theorem unfoldsBelowDefault_mono (status : ReducibilityStatus) :
    (unfoldsBelowDefault status .reducible → unfoldsBelowDefault status .instances) ∧
      (unfoldsBelowDefault status .instances → unfoldsBelowDefault status .implicit) := by
  cases status <;> simp [unfoldsBelowDefault]

/-- What a run's questions about one definition below default transparency came to: whether the
answer recorded was, each time, that it unfolds, and how often it was that it does not, at
reducible, at instance and at implicit transparency. -/
private structure Consults where
  /-- The answer recorded was each time that the definition unfolds. -/
  unfolds : Bool := true
  /-- The questions at reducible transparency answered that it does not unfold. -/
  reducible : Nat := 0
  /-- The questions at instance transparency answered that it does not unfold. -/
  instances : Nat := 0
  /-- The questions at implicit transparency answered that it does not unfold. -/
  implicit : Nat := 0

/-- `asked` with one more question about a definition, at `transparency`, answered `unfolds`. -/
private def Consults.record (asked : Consults) (transparency : Meta.TransparencyMode)
    (unfolds : Bool) : Consults :=
  if unfolds then asked else
    match transparency with
    | .reducible => { asked with unfolds := false, reducible := asked.reducible + 1 }
    | .instances => { asked with unfolds := false, instances := asked.instances + 1 }
    | .implicit => { asked with unfolds := false, implicit := asked.implicit + 1 }
    | _ => { asked with unfolds := false }

/-- How a recorded run's questions below default transparency are answered. -/
private inductive Reading where
  /-- Lean's own answer in the environment the run is in. -/
  | own
  /-- Every definition asked about unfolds. -/
  | all
  /-- The answer the status in `inspected` gives (`unfoldsBelowDefault`), and a matcher unfolds:
  for a run in `withoutReducible inspected`, where the discriminant of a `match` does not reduce
  for a status, so that the `match` is unfolded and its discriminant asked about here. -/
  | discriminants (inspected : Environment)

/-- The unfolding predicate under which a run's questions are recorded: for each definition Lean
asks about at reducible, instance or implicit transparency, `consulted` holds what the answers
came to (`Consults`). The answer recorded and returned is Lean's own (`Meta.canUnfoldDefault`),
except that with `Reading.all` every definition asked about at those transparencies unfolds, and
with `Reading.discriminants` the answer is the one the inspected environment's status gives, which
is recorded, and a matcher (`Meta.Match.Extension`, which the audited source can write) unfolds
besides. A question at another transparency is answered by Lean and not recorded: Lean 4.34.0
answers it alike for every status the search gives (`triedStatuses`), read from its source.

Lean 4.34.0 puts this predicate aside while it reduces the discriminant of a `match` below default
transparency (`Meta.whnfMatcher`, through `Meta.withCanUnfoldAtMatcherPred`) and reads the status
itself, so a definition it asks about only there is not recorded in an environment where the
discriminant reduces. In `withoutReducible` no discriminant reduces for a status: the `match` is
stuck, and a run that goes on to unfold the matcher asks about the discriminant again under this
predicate, which records it. Lean's fixed-parameter analysis does so where every definition
unfolds (`Reading.all`), and its preprocessing where matchers do (`Reading.discriminants`). -/
private def recordConsults (consulted : IO.Ref (NameMap Consults)) (reading : Reading)
    (config : Meta.Config) (info : ConstantInfo) : CoreM Bool := do
  let own ← Meta.canUnfoldDefault config info
  unless config.transparency matches .reducible | .instances | .implicit do return own
  let unfolds := match reading with
    | .discriminants inspected =>
      unfoldsBelowDefault (getReducibilityStatusCore inspected info.name) config.transparency
    | _ => own
  consulted.modify fun asked =>
    asked.insert info.name
      (((asked.find? info.name).getD {}).record config.transparency unfolds)
  match reading with
  | .own => return unfolds
  | .all => return true
  | .discriminants _ => return unfolds || Meta.isMatcherCore (← getEnv) info.name

/-- `run` under `recordConsults` where `consulted?` is given, and as it is otherwise. -/
private def recording {α : Type} (consulted? : Option (IO.Ref (NameMap Consults) × Reading))
    (run : MetaM α) : MetaM α :=
  match consulted? with
  | some (consulted, reading) => Meta.withCanUnfoldPred (recordConsults consulted reading) run
  | none => run

/-- The definitions `consulted` holds, in name order, each with what the questions about it came
to. -/
private def consultedDefinitions (consulted : IO.Ref (NameMap Consults)) :
    BaseIO (Array (Name × Consults)) :=
  return (← consulted.get).foldl (fun all name asked => all.push (name, asked)) #[]

/-- What `run` answers in `environment`, with the heartbeat budget of one declaration, every change
it makes undone and Lean's elaboration caches emptied on entering and leaving; `none` if it
throws. A `checkerLimit?` reached is rethrown. The search for a status assignment asks its
questions through this: an answer only proposes an assignment, and decides no admission. -/
private def decisionIn {α : Type} (environment : Environment) (run : TermElabM α) :
    TermElabM (Option α) := do
  let saved ← saveState
  try
    setEnv environment
    Meta.resetCache
    return some (← withCurrHeartbeats run)
  catch ex =>
    if (← checkerLimit? ex).isSome then throw ex
    return none
  finally
    saved.restore
    Meta.resetCache

/-- Which parameters Lean's fixed-parameter analysis (`getFixedParamPerms`) finds fixed for
`preDefs` in the current environment: for each definition, one answer for each parameter. -/
private def fixedParameters (consulted? : Option (IO.Ref (NameMap Consults) × Reading))
    (preDefs : Array PreDefinition) : TermElabM (Array (Array Bool)) :=
  withoutModifyingEnv do
    for preDef in preDefs do
      addAsAxiom preDef
    return (← recording consulted? (getFixedParamPerms preDefs)).perms.map (·.map Option.isSome)

/-- Whether `found` fixes every parameter `observed` does, for the same definitions and
parameters. -/
private def keepsFixed (found observed : Array (Array Bool)) : Bool :=
  found.size == observed.size && (observed.zip found).all fun (wanted, fixed) =>
    wanted.size == fixed.size && (wanted.zip fixed).all fun (wanted, fixed) => !wanted || fixed

/-- The statuses that change which parameters Lean finds fixed for `input`, the group as one of
Lean's compilers gives it to the fixed-parameter analysis, and the assignment `observed?` selects.

The definitions are those the analysis asks about when every definition it asks about unfolds
(`recordConsults` with `Reading.all`): under that reading each comparison of a recursive call's
argument with a parameter runs to its end, so the definitions any of them unfolds are asked about.
The analysis is recorded in `environment` and again in `stripped`, which is
`withoutReducible environment`: there the discriminant of a `match` does not reduce for a status
with the predicate put aside, so the comparison unfolds the matcher and asks about the discriminant
under the predicate, whatever the discriminant's status in `environment` and whichever module
declares it.
Each is then given each status of `triedStatuses`, and its own in `environment` where that is not
one of them, with every other one `reducible`, and the analysis is rerun. Returned first: each
definition for which another status than its own in `environment` changes the result, with one
status, the one that unfolds least, for each such result. Returned second, where `observed?` gives
the parameters the observed bases keep fixed: each definition given the status that unfolds least
among those under which the analysis still fixes all of them, where that changes the result. A
parameter is fixed when every comparison for it succeeds, and a comparison succeeds when the
definitions on its way unfold, so that assignment unfolds what the observed fixed parameters need
and nothing else the analysis asks about. Everything here is read from Lean's analysis and from
statuses the audited source can write; it only proposes assignments. -/
private def fixedParameterStatuses (environment stripped : Environment)
    (input : Array PreDefinition) (observed? : Option (Array (Array Bool))) :
    TermElabM (Array (Name × List ReducibilityStatus) × Statuses) := do
  let consulted ← IO.mkRef ({} : NameMap Consults)
  let some _ ← decisionIn environment (fixedParameters (some (consulted, .all)) input)
    | return (#[], [])
  discard <| decisionIn stripped (fixedParameters (some (consulted, .all)) input)
  let consulted ← consultedDefinitions consulted
  let unfolded :=
    withStatuses environment (consulted.toList.map fun (name, _) => (name, .reducible))
  let mut options := #[]
  let mut directed := #[]
  for (name, _) in consulted do
    let current := getReducibilityStatusCore environment name
    let mut outcomes := #[]
    for status in if triedStatuses.contains current then triedStatuses
        else triedStatuses ++ [current] do
      if let some fixed ← decisionIn (withStatuses unfolded [(name, status)])
          (fixedParameters none input) then
        outcomes := outcomes.push (status, fixed)
    let some (_, kept) := outcomes.find? (·.1 == current) | continue
    let others := outcomes.foldl (fun others (status, fixed) =>
      if fixed == kept || others.any (·.2 == fixed) then others
      else others.push (status, fixed)) #[]
    unless others.isEmpty do
      options := options.push (name, others.toList.map (·.1))
    if let some observed := observed? then
      if let some (status, fixed) := outcomes.find? fun (_, fixed) => keepsFixed fixed observed then
        if fixed != kept then directed := directed.push (name, status)
  return (options, directed.toList)

/-- The number of mentions of the constant `name` in `e` that compilation keeps: those outside
every proof and every type, decided in the term's own local context (`erasedByCompilation`), and
outside the relation, measure and well-foundedness proof of a well-founded fixpoint
(`fixpointArguments?`); a binder's type is not counted. `fuel` bounds the depth; exhausting it
counts nothing. A count only proposes an assignment. -/
private def survivingMentions (name : Name) (fuel : Nat) (e : Expr) : MetaM Nat := do
  match fuel with
  | 0 => return 0
  | fuel + 1 =>
    if (e.find? (·.isConstOf name)).isNone then return 0
    if ← erasedByCompilation e then return 0
    match e with
    | .const .. => return 1
    | .mdata _ e => survivingMentions name fuel e
    | .proj _ _ e => survivingMentions name fuel e
    | .app .. =>
      let parts := (fixpointArguments? e).getD (#[e.getAppFn] ++ e.getAppArgs)
      parts.foldlM (fun count part => return count + (← survivingMentions name fuel part)) 0
    | .lam n t body bi | .forallE n t body bi =>
      Meta.withLocalDecl n bi t fun x => survivingMentions name fuel (body.instantiate1 x)
    | .letE n t v body _ =>
      return (← survivingMentions name fuel v)
        + (← Meta.withLetDecl n t v fun x => survivingMentions name fuel (body.instantiate1 x))
    | _ => return 0

/-- What Lean's well-founded preprocessing (`WF.preprocess`) makes of the unary definition Lean
packs `preDefs` into (`wfPacked`), in the current environment, with the mentions of each constant
of `counted` that compilation keeps in it (`survivingMentions`); where the result is `unchanged?`
nothing is counted, and no counts are returned. Only the preprocessing is recorded. -/
private def preprocessed (consulted? : Option (IO.Ref (NameMap Consults) × Reading))
    (preDefs : Array PreDefinition) (counted : Array Name) (unchanged? : Option Expr) :
    TermElabM (Expr × Array Nat) := do
  let (_, _, _, unaryPreDef) ← wfPacked preDefs
  withoutModifyingEnv do
    addAsAxiom unaryPreDef
    let processed := (← recording consulted? (WF.preprocess unaryPreDef.value)).expr
    if unchanged? == some processed then return (processed, #[])
    return (processed, ← counted.mapM (survivingMentions · 100000 processed))

/-- The definitions that `after` records more questions about, answered that they do not unfold,
than `before` does, and that `change` gives no status: each with the lowest of the three
transparencies at which that number rose. With `before` what the preprocessing asks before any
change and `after` what it asks under `change`, they are what `change` makes it newly ask about
without their unfolding, and depend on `change` alone, not on the changes it was reached
through. -/
private def newlyStuck (before after : NameMap Consults) (change : Statuses) :
    Array (Name × Meta.TransparencyMode) :=
  after.foldl (init := #[]) fun found name asked =>
    if change.any (·.1 == name) then found else
      let earlier := (before.find? name).getD {}
      if asked.reducible > earlier.reducible then found.push (name, .reducible)
      else if asked.instances > earlier.instances then found.push (name, .instances)
      else if asked.implicit > earlier.implicit then found.push (name, .implicit)
      else found

/-- The statuses that answer a question at `transparency` with an unfolding, the one that unfolds
least first: what a definition asked about there, without its unfolding, can be given. -/
private def unfoldingStatuses (transparency : Meta.TransparencyMode) : List ReducibilityStatus :=
  triedStatuses.filter (unfoldsBelowDefault · transparency)

/-- `change` with its definitions in name order: two changes that give the same definitions the
same statuses have the same one. -/
private def inNameOrder (change : Statuses) : Statuses :=
  (change.toArray.qsort fun a b => a.1.lt b.1).toList

/-- The constants the left-hand sides of `rules` mention: those among the discrimination-tree
keys Lean indexes each rule under. A rule matches a term through these constants as they are, so
a status under which one of them unfolds can only keep that rule from matching. -/
private def patternConstants (rules : Meta.SimpTheorems) : NameSet :=
  let mentioned := fun (found : NameSet) (rule : Meta.SimpTheorem) =>
    rule.keys.foldl (init := found) fun found key =>
      match key with
      | .const name _ => found.insert name
      | _ => found
  rules.post.foldValues mentioned (rules.pre.foldValues mentioned {})

/-- The state of one helper's search of the preprocessing in one environment (`followChange`). -/
private structure Followed where
  /-- The changes run so far (`inNameOrder`). -/
  tried : Array Statuses := #[]
  /-- The changes that changed the result, each with the result and its counts, as found. -/
  changed : Array (Statuses × Expr × Array Nat) := #[]
  /-- The changes that left the result as it was (`inNameOrder`), each with what its run asked. -/
  kept : Array (Statuses × NameMap Consults) := #[]
  /-- The runs left off the first path of the change being followed. -/
  runs : Nat := 0
  /-- The changes not run because those runs were used up (`inNameOrder`), less those run since. -/
  unrun : Array Statuses := #[]
  /-- Whether a change was not run because the depth given was used up. -/
  deep : Bool := false

/-- The runs one change is followed through at most off its first path (`followChange`). -/
private def followLimit : Nat := 64

/-- Run the preprocessing of `preDefs` in `environment` under `change`, once, and follow the change
through the definitions it makes the preprocessing newly ask about. Where the run changes the
result, `unchanged`, the change is added to `state` with the result and its counts. Where it
leaves the result as it was, what it asked is kept in `state`, and the definitions it asks about,
without their unfolding, more often than `baseline` records (`newlyStuck`; `baseline` is what the
preprocessing asks before any change) are given a status that answers the question, and each
extended change is followed in turn:

- the first path: all of them that no toolchain rule's left-hand side mentions (`patterns`,
  `patternConstants`) at once, each made `reducible`;
- those same definitions at once, each given the status that unfolds least among those that
  answer its question (`unfoldingStatuses`), where that is another assignment; and
- all of them at once, each made `reducible`, where a rule's left-hand side mentions one.

A `wf_preprocess` rule matches through a function only where the function unfolds; with it
unfolded, Lean's matching goes further and stops at the next function that does not unfold, which
is asked about once more than before. Following those questions reaches a rule that applies only
where several functions unfold together, whether the helpers' values mention them or one unfolds
to another. A constant a rule's left-hand side mentions (`List.map` itself, once a function
unfolds to it) has to stay as it is for that rule to match, so the first path leaves it alone.

What a change is extended with depends on the change alone, so a change is run and extended once
(`Followed.tried`), whichever change it was reached from, and every change that extends it is
reached from it. `first` says that the run is on the first path of the change being followed: the
change itself, and from a change on that path the first extension above. Each run on it gives at
least one more definition a status, so there are fewer of them than `environment` has constants.
Any other run takes one of the runs `state` holds; with none left the change is not run and is
recorded (`Followed.unrun`), so that the caller does not take the search for complete. The same
holds for `depth`, which a caller that gives one above the number of constants never uses up. -/
private def followChange (environment : Environment) (preDefs : Array PreDefinition)
    (counted : Array Name) (unchanged : Expr) (patterns : NameSet) (baseline : NameMap Consults)
    (state : IO.Ref Followed) (change : Statuses) (first : Bool) : Nat → TermElabM Unit
  | 0 => state.modify ({ · with deep := true })
  | depth + 1 => do
    let key := inNameOrder change
    let current ← state.get
    if current.tried.contains key then return
    if !first && current.runs == 0 then
      unless current.unrun.contains key do
        state.set { current with unrun := current.unrun.push key }
      return
    state.set { current with
      tried := current.tried.push key, unrun := current.unrun.erase key
      runs := if first then current.runs else current.runs - 1 }
    let consulted ← IO.mkRef ({} : NameMap Consults)
    let some (processed, counts) ← decisionIn (withStatuses environment change)
        (preprocessed (some (consulted, .own)) preDefs counted (some unchanged))
      | return
    if processed != unchanged then
      state.modify fun found =>
        { found with changed := found.changed.push (change, processed, counts) }
      return
    let asked ← consulted.get
    state.modify fun found => { found with kept := found.kept.push (key, asked) }
    let further := newlyStuck baseline asked change
    let through := further.filter (!patterns.contains ·.1)
    let extended (names : Array (Name × Meta.TransparencyMode))
        (status : Meta.TransparencyMode → ReducibilityStatus) : Statuses :=
      change ++ names.toList.map fun (name, transparency) => (name, status transparency)
    let least (transparency : Meta.TransparencyMode) : ReducibilityStatus :=
      (unfoldingStatuses transparency).headD .reducible
    unless through.isEmpty do
      followChange environment preDefs counted unchanged patterns baseline state
        (extended through fun _ => .reducible) first depth
      followChange environment preDefs counted unchanged patterns baseline state
        (extended through least) false depth
    if through.size < further.size then
      followChange environment preDefs counted unchanged patterns baseline state
        (extended further fun _ => .reducible) false depth

/-- The status changes that change what Lean's well-founded preprocessing makes of `preDefs` in
`environment`, the change the observed bases select, and whether every change was decided.

The definitions are those the preprocessing asks about at reducible, instance or implicit
transparency (`recordConsults`), whether the helpers' values mention them or another definition
unfolds to them: those it asks about in `environment`, with Lean's own answers, and those it asks
about in `stripped`, which is `withoutReducible environment`, with the answers of `environment`
and matchers unfolding (`Reading.discriminants`), which adds the definitions Lean asks about only
while it reduces the discriminant of a `match`. Returned first: for each, the changes that change
the result when it is given another status of `triedStatuses` than its own, one for each result.
Such a change is followed through the definitions it newly asks about (`followChange`). One that
leaves the result unchanged is then paired with each other definition its run asked about without
that definition's unfolding, given each status that answers the question (`unfoldingStatuses`),
and the pair is followed in the same way; a change found that way is returned, with the
definition whose status was changed first, where its result is one that no change found before it
gives: a pair whose result one of its two changes gives alone says nothing about the other. A
change that only adds statuses to another one with the same result is dropped. The
observed definitions only order the changes: `wanted` counts the mentions of
a constant they keep (`survivingMentions`), and the changes after which the result keeps the
observed number of most of the constants counted come first. The constants counted are the
definitions asked about in `environment` and the constants the helpers' values mention, less the
functions of `preDefs`
themselves: an observed base calls itself through its fixpoint's argument and never mentions
them, while the preprocessed body keeps its calls to them where Lean packs nothing (one function
with one varying argument, `WF.packMutual`). A toolchain rule that matches through
a function replaces the application it matches, and a parameter Lean finds fixed is dropped from
the recursive calls, so those numbers tell the readings of a status apart. Returned second, where
the result keeps another number for some constant: a change after which it keeps the observed
number of each. Tried first for that is one change for all the functions concerned, each made
`reducible` where the result mentions it more often than the observed definitions do and
semireducible where it mentions it less often, since a rule can need several functions to unfold
together, followed and paired in the same way; then the changes returned first, in the order they
were found. Returned third: `false` if a change was not run because the runs a change is followed
through off its first path were used up (`followLimit`, `Followed.unrun`), so that what was
returned is not all there is. Everything here only proposes assignments. -/
private def preprocessingStatuses (environment stripped : Environment)
    (preDefs : Array PreDefinition) (wanted : Name → MetaM Nat) :
    TermElabM (Array (Name × List Statuses) × Statuses × Bool) := do
  let consulted ← IO.mkRef ({} : NameMap Consults)
  let some _ ← decisionIn environment (preprocessed (some (consulted, .own)) preDefs #[] none)
    | return (#[], [], true)
  let baseline ← consulted.get
  let known := baseline.foldl (fun known name _ => known.insert name) ({} : NameSet)
  discard <| decisionIn stripped
    (preprocessed (some (consulted, .discriminants environment)) preDefs #[] none)
  let asked := (← consultedDefinitions consulted).map (·.1)
  let own := preDefs.map (·.declName)
  let counted := (preDefs.foldl (fun names preDef =>
    preDef.value.getUsedConstants.foldl NameSet.insert names) known).toArray.filter
      (!own.contains ·)
  let some (unchanged, counts) ← decisionIn environment (preprocessed none preDefs counted none)
    | return (#[], [], true)
  let observed ← counted.mapM fun name => withCurrHeartbeats <| wanted name
  let distance (counts : Array Nat) : Nat :=
    (Array.range observed.size).countP fun index => counts[index]? != observed[index]?
  let patterns := patternConstants (WF.wfPreprocessSimpExtension.getState environment)
  let depth := environment.constants.fold (fun depth _ _ => depth + 1) 1
  let state ← IO.mkRef ({} : Followed)
  let complete : TermElabM Bool := do
    let followed ← state.get
    return followed.unrun.isEmpty && !followed.deep
  -- The changes found by following `change`, and what its own run asked where it left the result
  -- unchanged. A change run before returns what was found for every change that extends it:
  -- those are the changes following it reaches.
  let follow (change : Statuses) :
      TermElabM (Array (Statuses × Expr × Array Nat) × Option (NameMap Consults)) := do
    let key := inNameOrder change
    let earlier ← state.get
    let found ←
      if earlier.tried.contains key then
        pure (earlier.changed.filter fun (other, _, _) => key.all other.contains)
      else
        state.set { earlier with runs := followLimit }
        followChange environment preDefs counted unchanged patterns baseline state change true
          depth
        pure ((← state.get).changed.extract earlier.changed.size)
    return (found, ((← state.get).kept.find? (·.1 == key)).map (·.2))
  let paired (change : Statuses) (run : NameMap Consults) :
      TermElabM (Array (Statuses × Expr × Array Nat)) := do
    let mut found := #[]
    for (partner, asked) in run.foldl (fun all name asked => all.push (name, asked)) #[] do
      if asked.unfolds || change.any (·.1 == partner) then continue
      let transparency : Meta.TransparencyMode :=
        if asked.reducible > 0 then .reducible
        else if asked.instances > 0 then .instances else .implicit
      for status in unfoldingStatuses transparency do
        found := found ++ (← follow (change ++ [(partner, status)])).1
    return found
  let mut found : Array (Name × Nat × Statuses × Expr) := #[]
  let mut pending : Array (Name × Statuses × NameMap Consults) := #[]
  let mut together : Statuses := []
  for name in asked do
    let current := getReducibilityStatusCore environment name
    for status in triedStatuses do
      if status == current then continue
      let (changes, unchanged?) ← follow [(name, status)]
      for (change, processed, counts) in changes do
        unless found.any fun (other, _, _, result) => other == name && result == processed do
          found := found.push (name, distance counts, change, processed)
      if let some run := unchanged? then pending := pending.push (name, [(name, status)], run)
    let some index := counted.idxOf? name | continue
    let (some kept, some wanted) := (counts[index]?, observed[index]?) | continue
    let status := if kept > wanted then ReducibilityStatus.reducible else .semireducible
    if kept != wanted && status != current then
      together := together ++ [(name, status)]
  for (name, change, run) in pending do
    for (change, processed, counts) in ← paired change run do
      unless found.any (·.2.2.2 == processed) do
        found := found.push (name, distance counts, change, processed)
  -- A change that only adds statuses to another one with the same result says nothing more.
  let within (smaller larger : Statuses) : Bool :=
    smaller.length < larger.length && smaller.all larger.contains
  found := found.filter fun (_, _, change, processed) =>
    !found.any fun (_, _, other, result) => result == processed && within other change
  let options := asked.filterMap fun name =>
    let changes := found.filter (·.1 == name)
    if changes.isEmpty then none else
      some (changes.foldl (fun closest (_, far, _, _) => min closest far) (distance #[]), name,
        changes.toList.map (·.2.2.1))
  let ordered := (options.qsort fun a b => a.1 < b.1).map fun (_, name, changes) => (name, changes)
  if distance counts == 0 then return (ordered, [], ← complete)
  unless together.isEmpty do
    let (changes, unchanged?) ← follow together
    let changes ← match unchanged? with
      | some run => pure (changes ++ (← paired together run))
      | none => pure changes
    if let some (change, _, _) := changes.find? fun (_, _, counts) => distance counts == 0 then
      return (ordered, change, ← complete)
  let directed := (found.find? (·.2.1 == 0)).map (·.2.2.1)
  return (ordered, directed.getD [], ← complete)

/-- The head of `e` and its arguments, with the projections around the head taken off: the
arguments under each projection first, then those applied to it. `fuel` bounds the projections
taken off. -/
private def spineUnderProjections : Nat → Expr → Expr × Array Expr
  | 0, e => (e.getAppFn, e.getAppArgs)
  | fuel + 1, e =>
    match e.getAppFn with
    | .proj _ _ inner =>
      let (head, args) := spineUnderProjections fuel inner
      (head, args ++ e.getAppArgs)
    | head => (head, e.getAppArgs)

/-- The variables `e` passes to the `brecOn` of an inductive type after that type's parameters,
where `e` applies one (`T.brecOn`, or `T.brecOn_1` and so on for a nested or mutual group),
through the projections Lean puts around it where several functions recurse over one type; `none`
where it applies none. Lean 4.34.0's structural compiler applies `brecOn` to the indices and the
major premise, then to the functionals, and the result to the other parameters that vary
(`Structural.mkBRecOnApp`, read from its source), so these variables are the parameters it does
not keep fixed. A functional is a function, not a variable, where Lean writes it in place, as it
does for recursion over an inductive predicate. -/
private def belowRecursionArguments? (env : Environment) (e : Expr) : Option (Array Expr) := do
  let (.const (.str type suffix) _, args) := spineUnderProjections 64 e | none
  guard <| suffix.startsWith brecOnSuffix
  let .inductInfo info ← env.find? type | none
  return (args.extract info.numParams args.size).filter (·.isFVar)

/-- The parameters the observed bases keep outside their recursion, with whether that recursion
is well-founded, read from the shape Lean 4.34.0's compilers give a base: with the leading binders
of its value its parameters, the ones passed, as they are, to the unary definition Lean packs a
well-founded group into (`_unary`, `_mutual`; all arguments but the last, which packs the others),
the ones bound before the fixpoint where the base is that unary definition itself, the ones
passed to the functional of a structural definition (`_f`), or, where the base applies `brecOn`
itself, as a definition by structural recursion over an inductive predicate does, the ones it
does not pass to it (`belowRecursionArguments?`). `arities` gives each helper's
parameter count. `none` where a base has none of these shapes, or the bases differ in kind. What
is read only directs the search (`fixedParameterStatuses`). -/
private def observedFixedParameters? (bases : Array Name) (arities : Array Nat) :
    MetaM (Option (Bool × Array (Array Bool))) := do
  let env ← getEnv
  let some first := bases[0]? | return none
  let packed := #[first ++ `_unary, first ++ `_mutual].filter env.contains
  let functionals := bases.map (· ++ `_f)
  let headed (names : Array Name) (e : Expr) : Bool :=
    e.getAppFn.isConst && names.contains e.getAppFn.constName!
  let observed ← (bases.zip arities).mapM fun (base, arity) => do
    let some (.defnInfo definition) := env.find? base | return none
    Meta.lambdaBoundedTelescope definition.value arity fun params body => do
      let marked (fixed : Array Expr) : Array Bool :=
        (Array.range arity).map fun i => params[i]?.any fixed.contains
      if let some core := body.find? (headed packed) then
        return some (true, marked core.getAppArgs.pop)
      if packed.isEmpty then
        if let some arguments := fixpointArguments? body then
          return some (true, marked (params.extract 0 (params.size + 3 - arguments.size)))
      if let some core := body.find? (headed functionals) then
        return some (false, marked core.getAppArgs)
      if let some core := body.find? fun e => (belowRecursionArguments? env e).isSome then
        let varying := (belowRecursionArguments? env core).getD #[]
        return some (false, (Array.range arity).map fun i => params[i]?.any (!varying.contains ·))
      return none
  let some observed := observed.mapM id | return none
  let some (wellFounded, _) := observed[0]? | return none
  unless observed.all (·.1 == wellFounded) do return none
  return some (wellFounded, observed.map (·.2))

/-- The status assignments to regenerate `preDefs` under in `environment`: the one the observed
bases select, and for each definition whose status changes a decision, its other statuses.
`stripped` is `withoutReducible environment`, in which the questions Lean asks while it reduces
the discriminant of a `match` are recorded.
`inputs` holds the group as Lean's compilers give it to the fixed-parameter analysis, `observed?`
what `observedFixedParameters?` read, and `wanted` counts a constant's mentions in the observed
definitions. The fixed parameters are analysed first (`fixedParameterStatuses`), and the
preprocessing, where the recursion can be well-founded, under the assignment that analysis
selects (`preprocessingStatuses`); a change that only restores a status of `environment` is
dropped. The assignment returned first joins the two selections. Returned last: `false` if
the preprocessing left a change unfollowed (`Followed.unrun`), so that the candidates are
not all there are. -/
private def statusCandidates (environment stripped : Environment)
    (preDefs : Array PreDefinition)
    (inputs : List (Array PreDefinition)) (observed? : Option (Bool × Array (Array Bool)))
    (wanted : Name → MetaM Nat) : TermElabM (Statuses × List (List Statuses) × Bool) := do
  let mut options : Array (Name × List Statuses) := #[]
  let mut directed : Statuses := []
  let mut complete := true
  for input in inputs do
    let (found, selected) ←
      fixedParameterStatuses environment stripped input (observed?.map (·.2))
    options := options ++ found.map fun (name, statuses) =>
      (name, statuses.map fun status => [(name, status)])
    directed := directed ++ selected
  if observed?.all (·.1) then
    let (found, selected, decided) ← preprocessingStatuses (withStatuses environment directed)
      (withStatuses stripped (directed.map fun (name, _) => (name, .semireducible))) preDefs wanted
    complete := decided
    let restores (change : Statuses) : Bool := change.all fun (name, status) =>
      getReducibilityStatusCore environment name == status
    options := options ++ found.map fun (name, changes) => (name, changes.filter (!restores ·))
    directed := directed ++ selected
  let merged := options.foldl (fun merged (name, changes) =>
    match merged.findIdx? (·.1 == name) with
    | some index => merged.modify index fun (name, known) =>
        (name, changes.foldl (fun known change =>
          if known.contains change then known else known ++ [change]) known)
    | none => merged.push (name, changes.eraseDups)) (#[] : Array (Name × List Statuses))
  return (directed, (merged.toList.map (·.2)).filter (!·.isEmpty), complete)

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

by a proof that uses only Standard-Logical axioms. The checker builds the statement from the
constant `base` and from `value` alone and gives that statement itself to the kernel as the type
of a theorem (`kernelChecked`), after `isRecursionEquation` has confirmed its form by `Expr`
equality. No theorem is trusted for its name and no statement is compared with another: whatever
proof is found, the kernel checks it against this statement, in the environment the audit
inspects. A name only selects a candidate, and who declared a candidate is not consulted. The
candidates are tried in this order, each closed over the inspected environment before it is
submitted (`closedOver`), so that the kernel checks every step that is not a constant of that
environment:

- `Eq.refl (base xs)`, where `body` is a proof (`Meta.isProof`): Lean states no unfolding theorem
  for a definition whose type is a proposition, and the kernel accepts this one by proof
  irrelevance;
- each constant of `unfoldingTheoremNames` the environment holds, whoever declared it: the name is
  that of Lean's `base.eq_def`, which its well-founded compiler adds with the definition and which
  a module can also declare itself;
- what `Meta.getUnfoldEqnFor?` returns for `base` (`unfoldingProof?`): a constant of that name
  where the environment holds one, and otherwise the theorem Lean realizes; and
- the theorem Lean realizes for the definition `regenerated?` names in the environment given with
  it, the one a regeneration that reproduced `base` left: the regenerated definition, under the
  reducibility in which Lean's compiler reproduces `base`.

A statement no candidate proves answers `false`, as does one the search cannot build. Nothing is
kept: the theorem and every constant the search adds are discarded. A `checkerLimit?` reached is
rethrown, in the search or in the kernel: the helper is then undecided, not rejected. -/
private def recursionEquationChecked (cached : Std.HashMap Name (Array Name)) (base : Name)
    (levelParams : List Name) (value : Expr) (regenerated? : Option (Environment × Name)) :
    MetaM Bool := do
  let inspected ← getEnv
  let levels := levelParams.map mkLevelParam
  let function := mkConst base levels
  let saved ← Meta.saveState
  let accepted := fun (statement : Expr) (proof? : Option Expr) => do
    let some proof := proof? | return false
    try
      -- Whatever a search added is gone before the kernel is asked.
      saved.restore
      kernelChecked cached statement proof
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
Each equation check runs with the heartbeat budget of one declaration (`withCurrHeartbeats`),
whatever regenerations ran before it.
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
reproduces the base, the regeneration searches the statuses of the definitions Lean's compilers
ask about: Lean's fixed-parameter analysis and its `wf_preprocess` simplification unfold at
reducible transparency, and at implicit transparency where they compare an instance-implicit
argument, so a definition that is `reducible`, `instance_reducible` or `implicit_reducible` at only
one of the two points changes which parameters the compilers pack and which toolchain rule
rewrites the body. The search runs those two decisions alone, as Lean's own functions, and records
through `Meta`'s unfolding predicate which definitions they ask about below default transparency,
and for each what the answers came to (`recordConsults`): definitions of
any module, and whatever attribute, global or `local`, gave a status. Lean puts that predicate
aside while it reduces the discriminant of a `match`, so each decision is recorded a second time
in the environment with no definition unfolding for its status (`withoutReducible`), where such a
`match` is stuck, the matcher is unfolded and the discriminant is asked about under the predicate.
For
each such definition it finds the statuses under which a decision comes out differently
(`statusCandidates`); for the preprocessing, a change that leaves the result as it was is followed
through the definitions it makes the preprocessing newly ask about without their unfolding: all
at once, less the constants a toolchain rule's left-hand side mentions, each made `reducible`,
which is its first path, then those with the status that unfolds least, and then all with those
constants (`followChange`). It is then paired with each
other definition its run asked about in that way, so that
a rule that matches only where several functions unfold together is reached from the first of
them. What a change is extended with depends on the change alone, so each is run once. From the
observed bases
it reads which parameters they keep fixed
(`observedFixedParameters?`) and how many mentions of a function they keep, which select one
assignment directly. The search runs in the inspected environment and then in the one with no
definition irreducible: in each, that assignment is tried first, and then every assignment that
gives one or more of those definitions another status (`candidates`), each regeneration with the
heartbeat budget of one declaration. An assignment is read from Lean's analysis, from statuses
and from the observed definitions, all of which the audited source can write; like the
termination argument it only selects which regeneration runs, is never an argument of the
comparison, and is undone with the rest of the run before the comparison. The enumeration is
exhaustive over those assignments when there are at most `candidateLimit` of them
(`mem_candidates`), and then a helper no attempt reproduces is not regenerated. Otherwise only
the first `candidateLimit` single candidate changes are tried (`candidates_length_le`), each of
which can give several definitions a status, and a helper none of them reproduces is undecided:
the regeneration throws, so the audit is incomplete and the helper is neither admitted nor
rejected. The same holds where a change of status was followed through `followLimit` runs of the
preprocessing off its first path with a change that extends it still not run (`Followed.unrun`).
Where none of those assignments reproduces the base, the regeneration tries the assignments of
the search this one replaces (`earlierStatusOptions`, `candidates`): each gives some of the
definitions of the helper's module that its group reaches an earlier status (`earlierStatuses`),
and all attempts run under it in both environments. They are that search's assignments, in its
order, so every assignment it tried is tried here. They are read from statuses, kernel hints and
module membership, all of which the audited source can write, and like the others only select
which regeneration runs. They reach a status Lean reads without asking its unfolding predicate
and outside a `match`, which nothing above records: Lean 4.34.0 does so where it tests whether a
type is a class (`Meta.isClassQuickConst?`) and where instance resolution meets a `reducible`
head it did not unfold in a term with a metavariable (`DiscrTree.getKeyArgs`), read from its
source and not observed to decide either decision. The enumeration is exhaustive over those
assignments when there are at most `candidateLimit`
of them. Otherwise only the first `candidateLimit` single changes are tried, and a helper none of
them reproduces is undecided, as is one whose reached definitions were not all visited. Every
bound the search stops at ends in an incomplete audit, never in a rejection, and the error names
the bound.
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
    (preprocessRules : IO.Ref (Option Meta.SimpTheorems))
    (cached : Std.HashMap Name (Array Name)) :
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
        return if ← regenerationMatches cached regenerated then some after else none
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
        unless ← withCurrHeartbeats <| recursionEquationChecked cached bases[i]!
            member.levelParams (toBases member.value) (some (after, regenerationRoot ++ bases[i]!)) do
          return none
      return some origin
    if let some (origin, after) ← regenerate regenerating then return ← admitted origin after
    let unsealed := withoutIrreducible regenerating
    if let some (origin, after) ← regenerate unsealed then return ← admitted origin after
    let fnNames := preDefs.map (·.declName)
    let numSectionVars := preDefs[0]!.numSectionVars
    let observed? := (← decisionIn regenerating <|
      observedFixedParameters? bases (preDefs.map (·.value.getNumHeadLambdas))).join
    let structural ← decisionIn regenerating <| withoutModifyingEnv do
      for preDef in preDefs do
        addAsAxiom preDef
      preDefs.mapM fun (preDef : PreDefinition) => do
        let value ← Structural.preprocess preDef.value fnNames numSectionVars
        return { preDef with value }
    let wellFounded ← decisionIn regenerating <| preDefs.mapM fun (preDef : PreDefinition) =>
      return { preDef with value := (← WF.floatRecApp preDef.value) }
    let inputs := match observed? with
      | some (true, _) => wellFounded.toList
      | some (false, _) => structural.toList
      | none => structural.toList ++ wellFounded.toList
    let observedNames :=
      (bases ++ #[bases[0]! ++ `_unary, bases[0]! ++ `_mutual]).filter env.contains
    let wanted (constant : Name) : MetaM Nat :=
      observedNames.foldlM (init := 0) fun count observed => do
        let some (.defnInfo definition) := env.find? observed | return count
        return count + (← survivingMentions constant 100000 definition.value)
    let roots ← preDefs.mapIdxM fun i (preDef : PreDefinition) => do
      return (group[i]!, ← Meta.unfoldIfArgIsAppOf fnNames numSectionVars preDef.value)
    let reached? := earlierStatusOptions env name roots
    let mut enumerated := true
    let mut followed := true
    for environment in [regenerating, unsealed] do
      let (directed, options, complete) ← statusCandidates environment
        (withoutReducible environment) preDefs inputs observed? wanted
      let (assignments, all) := candidates candidateLimit options
      enumerated := enumerated && all
      followed := followed && complete
      for assignment in directed :: (assignments.map List.flatten).filter (· != directed) do
        if assignment.isEmpty then continue
        if let some (origin, after) ← withCurrHeartbeats <|
            regenerate (withStatuses environment assignment) then
          return ← admitted origin after
    let (earlier, exhaustive) := candidates candidateLimit (reached?.getD [])
    for assignment in earlier do
      for environment in [regenerating, unsealed] do
        if let some (origin, after) ← withCurrHeartbeats <|
            regenerate (withStatuses environment assignment) then
          return ← admitted origin after
    let bounds :=
      (if enumerated then [] else [m!"the definitions whose status changes what Lean's \
        recursion compilers generate for it allow more than {candidateLimit} assignments of \
        another status, of which only the one its observed base selects and the first \
        {candidateLimit} single candidate changes were tried"]) ++
      (if followed then [] else [m!"a change of status was followed through {followLimit} \
        runs of Lean's preprocessing beside those of its first path, and a change that extends \
        it was still not run"]) ++
      (if reached?.isSome then [] else [m!"the definitions of its module that it reaches were \
        not all visited"]) ++
      (if exhaustive then [] else [m!"the definitions of its module that it reaches allow more \
        than {candidateLimit} assignments of an earlier reducibility status, of which only the \
        first {candidateLimit} single changes were tried"])
    unless bounds.isEmpty do
      throwError "no regeneration of {name} reproduced its base, and the helper is undecided, \
        neither admitted nor rejected: the search for the reducibility statuses its definition \
        was compiled under stopped at a bound: {MessageData.joinSep bounds "; and "}. Give each \
        function it calls its reducibility where the function is declared."
    return none

/-- The candidate of a generated native-proof axiom with its recognition: the owning prefix and
the tactic, which `RegulaPolicy.nativeAxiomOrigin?` reads from the name, with the kernel-checked
type, and the Boolean expression that the type asserts in the exact shape its tactic produces.
The pure decision `RegulaPolicy.NativeStatement.recognize?` decides the shape, through its
registered contract (`RegulaPolicy.NativeStatement.checked_recognize`). It reads the tactic, the
prefix and the type, and nothing else. A recognition is indexed by its candidate and holds the
proof that the decision returns its expression for that candidate
(`RegulaPolicy.NativeStatement.Recognition`). -/
def nativeRecognition? (name : Name) (type : Expr) :
    Option ((candidate : RegulaPolicy.NativeStatement.Candidate) ×
      RegulaPolicy.NativeStatement.Recognition candidate) := do
  let (parent, tactic) ← RegulaPolicy.nativeAxiomOrigin? name
  let candidate : RegulaPolicy.NativeStatement.Candidate := { tactic, parent, type }
  let recognition ← RegulaPolicy.NativeStatement.checked_recognize.run candidate
  return ⟨candidate, recognition⟩

/-- The `repr` of the asserted expression of a recognition, naming each auxiliary definition of
the same tactic run by its unindexed base, so a fresh transcript and a build that index generated
names differently agree. -/
def nativeStatementText {candidate : RegulaPolicy.NativeStatement.Candidate}
    (recognition : RegulaPolicy.NativeStatement.Recognition candidate) : String :=
  let unindexed := recognition.asserted.replace fun
    | .const constant levels => candidate.tactic.auxiliaryInfixes.findSome? fun kind =>
        if RegulaPolicy.generatedAuxParent? kind constant == some candidate.parent then
          some (mkConst (Name.mkStr candidate.parent kind) levels)
        else none
    | _ => none
  toString (repr unindexed)

/-- `Declaration.nativeStatement` and `AddedDeclaration.nativeStatement`: the text of the
recognized statement of the axiom (`nativeRecognition?`, `nativeStatementText`), and `none` for a
constant with no recognized statement. -/
def nativeStatement? (name : Name) (type : Expr) : Option String :=
  (nativeRecognition? name type).map fun found => nativeStatementText found.2

/-- The observing pass of the native-axiom replay: independently replay the Boolean native
evaluation of the expression of a recognition, without retaining any declaration it creates. The
pass takes a recognition of a candidate. Each value of that type is the result of the pure
decision for that candidate (`RegulaPolicy.NativeStatement.recognize?_eq_some`), so the expression
it evaluates is the one that the decision returned for that tactic, prefix and type, and no
other. This remains compiler evidence, never a kernel proof. A failed replay is `false`; a
`checkerLimit?` reached during it is rethrown. -/
private def replayNative {candidate : RegulaPolicy.NativeStatement.Candidate}
    (recognition : RegulaPolicy.NativeStatement.Recognition candidate) : CommandElabM Bool :=
  liftTermElabM <| withoutModifyingEnv do
    try
      return match ← Meta.nativeEqTrue `audit_native_replay recognition.asserted with
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

/-- Whether the result type of `type` is `Decidable _`: `type`, with every leading binder opened
and the remaining type reduced to weak head normal form at the ambient transparency, is an
application of `Decidable` to one argument. So a `DecidablePred`, `DecidableRel` or
`DecidableEq` instance has such a result type, and so does a definition whose result type unfolds
to one. A result type that the reduction does not unfold to `Decidable _`, such as an irreducible
alias of it, is not one: the function then needs a decision contract. -/
def returnsDecidable (type : Expr) : MetaM Bool :=
  Meta.forallTelescopeReducing type (fun _ body => pure (body.isAppOfArity ``Decidable 1))
    (whnfType := true)

/-- The decision registration of a constant: `none` unless `@[regula_decision]` registers it
(`registered`, the environment's `Regula.decisionRegistrations`: the registrations of every
module it loaded, so of the constant's own module or of one that imports it), and otherwise
whether its result type is `Decidable _` (`returnsDecidable`). The registrations are environment
state an audited project writes; a registration only adds the RG1008 requirement, and its absence
adds none. -/
def decisionResult? (registered : NameSet) (info : ConstantInfo) :
    MetaM (Option RegulaPolicy.DecisionResult) := do
  unless registered.contains info.name do return none
  return some (if ← returnsDecidable info.type then .decidable else .other)

/-- Refuses the first `@[regula_decision]` registration that one of the loaded `modules` writes
for a declaration none of them declares, naming the registering module and the declaration. An
inventory of `modules` records no declaration for it, so its RG1008 requirement would go
undecided; a caller that builds such an inventory stops on the refusal. A registered name that
no loaded module declares is refused too. -/
def ownedDecisionRegistrations (env : Environment) (modules : List Name) : Except String Unit :=
  let foreign := env.header.moduleNames.zipIdx.findSome? fun (moduleName, index) =>
    if modules.contains moduleName then
      (decisionExtension.getModuleEntries env index).findSome? fun declaration =>
        let owned := (env.getModuleIdxFor? declaration).any fun home =>
          (env.header.moduleNames[home.toNat]?).any modules.contains
        if owned then none else some (moduleName, declaration)
    else none
  match foreign with
  | none => .ok ()
  | some (moduleName, declaration) => .error
      s!"module {moduleName} registers {declaration} with `@[regula_decision]`, and no module \
        of this inventory declares {declaration}: a registration is a requirement of the \
        inventory that owns the function, so register it in a module of the library that \
        declares it"

/-- For each imported module index: whether the module is `target` or transitively imports it.
This is the least fixed point of "is `target` or imports a marked module": a pass that marks
nothing has reached it, and every other pass marks one of the finitely many modules, so at most
one pass per module runs. Lean admits a constant only when every constant its type and value
mention is already in the environment, so no constant of an unmarked module mentions a constant
of `target`, and neither does any constant such a constant mentions. -/
private def importersOf (env : Environment) (target : Name) : Array Bool := Id.run do
  let names := env.header.moduleNames
  let importsAware (aware : Array Bool) (index : Nat) : Bool :=
    match env.header.moduleData[index]? with
    | some data => data.imports.any fun imported =>
        ((env.getModuleIdx? imported.module).bind fun idx => aware[(idx : Nat)]?).getD false
    | none => false
  let mut aware := names.map (· == target)
  for _ in [:names.size] do
    let mut changed := false
    for index in [:names.size] do
      if !(aware[index]?.getD true) && importsAware aware index then
        aware := aware.set! index true
        changed := true
    if !changed then break
  return aware

/-- The part of an environment whose declarations can mention `Regula.ExecutableContract`, with a
memo of constants shown not to reach it. No constant of a module that is neither
`Regula.Contract` nor a transitive importer of it mentions the contract type or a decision kind,
which `Regula.Contract` also declares, and neither does any constant such a constant mentions
(`importersOf`). It also holds, for the same environment, the declarations registered as
decisions and a memo of the toolchain's `wf_preprocess` rules that recursion-helper regeneration
uses. -/
structure ContractScope where
  /-- For each imported module index: `Regula.Contract` or a module that transitively imports it. -/
  aware : Array Bool
  /-- Whether the current module's own constants can mention it: the current module imports
  every module of the header. -/
  mainAware : Bool
  /-- Constants whose closure under `unfoldReferences` was searched without reaching it. -/
  free : IO.Ref NameSet
  /-- Constants whose closure under `unfoldReferences` was searched without reaching a decision
  kind (`Regula.DecidesSoundly`, `Regula.DecidesCompletely` or `Regula.Decides`). -/
  decisionFree : IO.Ref NameSet
  /-- Every declaration `@[regula_decision]` registers in the environment
  (`Regula.decisionRegistrations`), computed once for all of its declarations. -/
  decisions : NameSet
  /-- The toolchain's `wf_preprocess` rules once a recursion helper's regeneration has computed
  them (`Collect.unsafeRecRegeneration`), shared by every helper of the environment. -/
  preprocessRules : IO.Ref (Option Meta.SimpTheorems)
  /-- For each imported module index that the search for shared definitions asked about: whether
  Lean loaded the module from the toolchain's own library directory
  (`ContractScope.fromToolchain`). -/
  toolchain : IO.Ref (Std.HashMap Nat Bool)
  /-- The result form of each constant that the search for shared definitions read
  (`ContractScope.resultForm`). -/
  forms : IO.Ref (NameMap RegulaPolicy.ResultForm)
  /-- The axioms that each name of the owned declarations' closure reaches in the kernel that
  replayed the owned modules (`Replayed.axioms`), where admission computed them; empty for an
  environment no admission replayed. The kernel walks of the proofs that the checker builds stop at
  these names (`kernelChecked`). -/
  axioms : Std.HashMap Name (Array Name) := {}

/-- The scope of `env`, with awareness as `importersOf` computes it for `Regula.Contract`, and the
axioms admission computed for the owned declarations' closure (`axioms`). -/
def ContractScope.new (env : Environment) (axioms : Std.HashMap Name (Array Name) := {}) :
    BaseIO ContractScope := do
  return { aware := importersOf env `Regula.Contract
           mainAware := (env.getModuleIdx? `Regula.Contract).isSome ||
             env.mainModule == `Regula.Contract
           free := ← IO.mkRef {}
           decisionFree := ← IO.mkRef {}
           decisions := decisionRegistrations env
           preprocessRules := ← IO.mkRef none
           toolchain := ← IO.mkRef {}
           forms := ← IO.mkRef {}
           axioms }

/-- Whether `name` belongs to an aware module; a constant whose module index is unknown counts as
aware, so the search expands it. -/
def ContractScope.constantAware (scope : ContractScope) (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some index => scope.aware[(index : Nat)]?.getD true
  | none => scope.mainAware

/-- The observing pass of a search of a mentioned constant (`RegulaPolicy.MentionSearch`): the
record of each constant that the search takes before it takes a target, for each such constant
that `lookup` reads. `lookup` gives the constants that a constant mentions, or `none` for a
constant that the search does not expand. The pass takes the constants in the order of the
search: a stack of pushed constants, the constants of `start` pushed first, each constant pushed
one time. The search over these records takes the same constants in the same order, so it
returns at the same target, or `none` when the pass read each constant that the search reaches.
That `lookup` reads the environment truly is this pass's, not a theorem. -/
private def mentionRecords (lookup : Name → Option (Array Name)) (start targets : Array Name) :
    RegulaPolicy.MentionSearch.Records := Id.run do
  let mut marked : Std.HashSet Name := {}
  let mut pending : Array Name := #[]
  for name in start do
    unless marked.contains name do
      marked := marked.insert name
      pending := pending.push name
  let mut records : RegulaPolicy.MentionSearch.Records := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if targets.contains name then break
    if let some mentioned := lookup name then
      records := records.insert name ⟨mentioned⟩
      for next in mentioned do
        unless marked.contains next do
          marked := marked.insert next
          pending := pending.push next
  return records

/-- The route by which a constant of `start` leads to one of `targets`, through the constants
that `lookup` gives: the observing pass (`mentionRecords`) and the registered decision
`RegulaPolicy.MentionSearch.search`, which returns a route exactly when such a route exists in
the records (`checked_search`). -/
private def mentionRoute? (lookup : Name → Option (Array Name)) (start targets : Array Name) :
    Option (Array Name) :=
  RegulaPolicy.MentionSearch.checked_search.run
    { records := mentionRecords lookup start targets, start, targets }

/-- Whether one of `targets` is among the constants `type` mentions, closed under
`unfoldReferences`, for `targets` that are constants of `Regula.Contract`: the observing pass
(`mentionRecords`) and the registered decision `RegulaPolicy.MentionSearch.search`. Constants of
modules outside the scope and constants of the memo `free` of those same `targets` are not
expanded. A search that ends without a target records each constant
it expanded in `free`: by the search's kind no expanded constant leads to a target in the records,
and a constant that it did not expand leads to none in the environment, so none of them does. -/
private def ContractScope.reaches (scope : ContractScope) (env : Environment)
    (targets : Array Name) (free : IO.Ref NameSet) (type : Expr) : BaseIO Bool := do
  let known ← free.get
  let lookup (name : Name) : Option (Array Name) :=
    if known.contains name || !scope.constantAware env name then none
    else (env.find? name).map unfoldReferences
  let start := type.getUsedConstants
  let records := mentionRecords lookup start targets
  if (RegulaPolicy.MentionSearch.checked_search.run { records, start, targets }).isSome then
    return true
  free.modify fun free => records.fold (fun free name _ => free.insert name) free
  return false

/-- Whether reducing `type` can produce `Regula.ExecutableContract`: whether the contract type is
among the constants `type` mentions, closed under `unfoldReferences`. Lean's reduction steps
(delta, iota, beta, zeta, eta, projection, and literal and native Boolean or natural-number steps)
introduce only constants of that closure or of `Init`, which does not import `Regula.Contract`;
the reduction this guards runs inside `declaration`, with smart unfolding off. Constants of modules
outside the scope are not expanded, and a search that ends without finding the contract type
records every constant it expanded as free. -/
def ContractScope.mayReach (scope : ContractScope) (env : Environment) (type : Expr) :
    BaseIO Bool :=
  scope.reaches env #[``Regula.ExecutableContract] scope.free type

/-- Whether reducing `requirement` can produce a decision kind: whether `Regula.DecidesSoundly`,
`Regula.DecidesCompletely` or `Regula.Decides` is among the constants it mentions, closed under
`unfoldReferences`, by the argument of `ContractScope.mayReach`. The targets are the structure of
each kind (`RegulaPolicy.DecisionKind.structureNames`), which lists a name exactly when the name
is read as a kind (`RegulaPolicy.DecisionKind.mem_structureNames_iff`). -/
def ContractScope.mayReachDecision (scope : ContractScope) (env : Environment)
    (requirement : Expr) : BaseIO Bool :=
  scope.reaches env RegulaPolicy.DecisionKind.structureNames scope.decisionFree requirement

/-- The constants by which `e` mentions `target`, closed under unfolding: the first is a constant
`e` mentions, each is mentioned by the type or the unfoldable value of the one before
(`statusReferences`), and the last is `target`; `none` when `e` does not mention it. A theorem's
proof and an opaque constant's value are not followed: Lean's reduction unfolds neither, and a
proposition does not depend on which proof of a statement a proof term is. Only a constant that
can mention `target` is expanded: one of its module, of a module that transitively imports it
(`importersOf`), or of the current module; an imported constant never mentions a constant of the
current module. The search is `mentionRoute?`: the observing pass reads `statusReferences` of each
constant that can mention `target`, and the registered decision returns the route. -/
private def mentionChain? (env : Environment) (target : Name) (e : Expr) :
    Option (Array Name) :=
  let targetModule := env.getModuleIdxFor? target
  let importers := targetModule.bind fun index =>
    env.header.moduleNames[(index : Nat)]?.map (importersOf env)
  let canMention (name : Name) : Bool :=
    match env.getModuleIdxFor? name with
    | none => true
    | some index =>
      match targetModule, importers with
      | none, _ => false
      | some _, some aware => aware[(index : Nat)]?.getD true
      | some _, none => true
  let lookup (name : Name) : Option (Array Name) :=
    if canMention name then (env.find? name).map statusReferences else none
  mentionRoute? lookup e.getUsedConstants #[target]

/-- The structure, the position of the field and the number of the structure's parameters when
`value`, under `binders` binders already opened, is a field's projection function: one binder
for each parameter, one for the structure's value, and the primitive projection of that value. -/
private def projectionBody? : Expr → Nat → Option (Name × Nat × Nat)
  | .lam _ _ body _, binders => projectionBody? body (binders + 1)
  | .proj structureName index (.bvar 0), binders + 1 => some (structureName, index, binders)
  | _, _ => none

/-- The structure and the position of the field when `argument` is a field of the variable that
the innermost binder binds: the primitive projection of that variable, or a constant whose value
is a field's projection function (`projectionBody?`) applied to the structure's parameters and
that variable. The constant is a definition, or a theorem for a field that is a proof. `none`
for every other term, a field of a field among them. Whether a constant is a projection function
is read from its kernel-checked value, not from Lean's record of projection functions, which is
environment state an audited project can write. -/
private def boundField? (env : Environment) (argument : Expr) : Option (Name × Nat) :=
  match argument.consumeMData with
  | .proj structureName index (.bvar 0) => some (structureName, index)
  | .app function (.bvar 0) => do
      let .const projection _ := function.getAppFn | none
      let value ← match ← env.find? projection with
        | .defnInfo definition => some definition.value
        | .thmInfo proof => some proof.value
        | _ => none
      let (structureName, index, parameters) ← projectionBody? value 0
      guard (function.getAppNumArgs == parameters)
      some (structureName, index)
  | _ => none

/-- What the kernel-checked declarations say of a term that, under one binder, applies a constant
to `arguments`: the shape of the inductive type of whose value the first argument is a field,
and for each argument the field of the bound variable in that type that it is (`boundField?`).
`none` when the first argument is no field or its type has no constructor. -/
private def fieldPacking? (env : Environment) (arguments : Array Expr) :
    Option RegulaPolicy.FieldPacking := do
  let (typeName, _) ← boundField? env (← arguments[0]?)
  let .inductInfo type ← env.find? typeName | none
  let .ctorInfo first ← env.find? (← type.ctors.head?) | none
  some {
    constructors := type.ctors.length
    indices := type.numIndices
    fields := first.numFields
    arguments := arguments.toList.map fun argument =>
      (boundField? env argument).bind fun (name, index) =>
        if name == typeName then some index else none }

/-- The universe levels at which `body` names the constant `implementation`, with what the
kernel-checked declarations say of its arguments (`fieldPacking?`), when `body`, under one
binder, is that constant applied to arguments of which the first is a field of the bound
variable. `none` for every other term. Whether the arguments are the fields of the bound
variable, each once and in the order of the fields, in a type with one constructor and no index,
is decided with the rest of the reading (`RegulaPolicy.DecidedFunction.covers`). A field left
out, given twice or out of order, a field the constant does not take, and a type with an index,
whose values are only some of the tuples of its fields, each fail that decision. -/
private def fieldApplication? (env : Environment) (implementation : Name) (body : Expr) :
    Option (List Level × RegulaPolicy.FieldPacking) := do
  let .const name levels := body.getAppFn | none
  guard (name == implementation)
  let packing ← fieldPacking? env body.getAppArgs
  some (levels, packing)

/-- Whether `function`, applied to one more argument, packs or erases that argument, a function,
without changing which inputs it is defined on: `Function.uncurry` at its three implicit
arguments, which packs two arguments into a pair, or one of the two erasures of
`Regula.Contract` at its implicit arguments (`Regula.Dependent.isSome`, `Regula.Dependent.isOk`),
each of which forgets the part of the result whose type depends on the input. These three
constants are read by name and no other function is. -/
private def packsOrErases (function : Expr) : Bool :=
  function.isAppOfArity ``Function.uncurry 3 ||
    function.isAppOfArity ``Regula.Dependent.isSome 2 ||
    function.isAppOfArity ``Regula.Dependent.isOk 3

/-- The universe levels at which `decided` names the constant `implementation`, with the field
application at its core when it has one, when `decided` has one of the forms that are read: the
constant itself; the constant applied to fields of the variable of one binder
(`fieldApplication?`); or `Function.uncurry` or an erasure of `Regula.Contract` (`packsOrErases`)
applied any number of times to one of the two. `none` for every other term, so no other way of
supplying the arguments is read as a packing, and no other function of the result as an erasure.
Whether a term of these forms is the implementation on every argument is decided afterwards
(`RegulaPolicy.DecidedFunction.covers`). -/
private def decidedReading? (env : Environment) (implementation : Name) :
    Expr → Option (List Level × Option RegulaPolicy.FieldPacking)
  | .const name levels => if name == implementation then some (levels, none) else none
  | .mdata _ decided => decidedReading? env implementation decided
  | .lam _ _ body _ =>
      (fieldApplication? env implementation body).map fun (levels, packing) =>
        (levels, some packing)
  | .app function decided =>
      if packsOrErases function then decidedReading? env implementation decided else none
  | _ => none

/-- The constant that `argument` applies to the variable of the innermost binder, in the place
of a field's projection function (`boundField?`), when `env` is the environment of a file with a
`module` header and has that constant as an axiom. Lean gives such a file a theorem of an
imported module, and a definition or an opaque constant that the module does not export with
its value, as an axiom. The projection function of a proof field is such a theorem, so that
environment cannot say whether the constant is a projection function. `none` for every other
argument, and for every argument in an environment with no `module` header, where every imported
constant has its own declaration and an axiom is no field. -/
private def hiddenProjection? (env : Environment) (argument : Expr) : Option Name := do
  guard env.header.isModule
  let .app function (.bvar 0) := argument.consumeMData | none
  let .const projection _ := function.getAppFn | none
  let .axiomInfo _ ← env.find? projection | none
  some projection

/-- The constant that keeps `env` from saying whether `decided` is a field application of
`implementation`: under `Function.uncurry` and the erasures (`packsOrErases`), as
`decidedReading?` reads them, `decided` is the constant `implementation` applied under one
binder, and an argument applies to the bound variable a constant that `env` has only as an axiom
(`hiddenProjection?`). `none` for every other term. -/
private def hiddenField? (env : Environment) (implementation : Name) : Expr → Option Name
  | .mdata _ decided => hiddenField? env implementation decided
  | .lam _ _ body _ =>
      if body.getAppFn.isConstOf implementation then
        body.getAppArgs.findSome? (hiddenProjection? env)
      else none
  | .app function decided =>
      if packsOrErases function then hiddenField? env implementation decided else none
  | _ => none

/-- The number of arguments that a value of `type` takes: the leading binders of `type`, with
every definition unfolded. A term can be applied only when its type reduces to a function type,
so a value of a type with no leading binder takes no argument. For the result type of the
function that a decision kind is stated about, a number above zero says that the function is the
implementation with arguments left. -/
private def unsuppliedArguments (type : Expr) : MetaM Nat :=
  Meta.withTransparency .all <| Meta.forallTelescopeReducing type fun arguments _ =>
    pure arguments.size

/-- Whether `levels` are universe parameters, no two of them the same. A registration is stated
for every value of its own universe parameters, so a kind about a constant at such levels holds
of every universe instance of the constant. At any other levels, such as a literal level or one
parameter twice, it holds only of some instances. -/
private def ownParameters (levels : List Level) : Bool :=
  levels.all (·.isParam) && levels.eraseDups.length == levels.length

/-- The decision kind of a registration's requirement, with the result type, the acceptance
predicate, the specification and the decided function it states: `requirement` reduced to weak
head normal form at the ambient transparency is an application of the kind's structure
(`RegulaPolicy.DecisionKind.ofStructureName?`) to its two type arguments, of which the result
type is the second, and those three. `none` for every other requirement. The requirement is
reduced only when `ContractScope.mayReachDecision` admits that the reduction can produce a kind,
as a declared type is in `executableContract?`. -/
private def decisionRequirement? (env : Environment) (scope : ContractScope) (requirement : Expr) :
    MetaM (Option (RegulaPolicy.DecisionKind × Expr × Expr × Expr × Expr)) := do
  unless (← scope.mayReachDecision env requirement) do return none
  let reduced ← Meta.whnf requirement
  let some kind := reduced.getAppFn.constName?.bind RegulaPolicy.DecisionKind.ofStructureName?
    | return none
  let args := reduced.getAppArgs
  let (some result, some accepts, some spec, some decided) :=
    (args[1]?, args[2]?, args[3]?, args[4]?) | return none
  unless args.size == 5 do return none
  return some (kind, result, accepts, spec, decided)

/-- Why a decision registration of `implementation` is refused: the kind is stated about a
function that is not one of the forms that are read (`decidedReading?`), or that is not the
implementation on every argument (`RegulaPolicy.DecidedFunction.covers`, proved exact in
`DecidedFunction.covers_iff`), so it can say nothing of the registered constant, or nothing of a
part of its domain; it is stated about the implementation at universe levels other than its own
parameters (`ownParameters`), so it says nothing of the other universe instances; or the
acceptance predicate or the specification mentions the implementation (`mentionChain?`), as the
tautology `spec := fun x => f x = true` does. `none` when none of these holds. `result` is the
result type of the kind: a function that is the implementation with an argument left has a
result that is itself a function (`unsuppliedArguments`). Every such kind is refused, without a
reading of its acceptance predicate: one that reads the result at one fixed value of the
argument is the kind of one slice of the implementation (`Regula.Decides.iff_slice`), and one
that quantifies over the argument is refused too, which is conservative. The search for a
mention establishes only that the acceptance predicate and the specification are stated without
the implementation's constant; whether the specification is the intended one remains review. A
registration that this function does not refuse is then searched for the functions that its two
sides share (`sharedReading`). That search names them in the record and refuses nothing itself:
the pure decision `RegulaPolicy.sharedTestFailure` refuses a registration whose record names a
function with a result of `Bool` or `BEq`. -/
private def decisionFailure? (env : Environment) (implementation : Name)
    (result accepts spec decided : Expr) : MetaM (Option String) := do
  let mention (part : String) (chain : Array Name) : String :=
    let route := chain.pop.toList.map (s!"`{·}`")
    let through := if route.isEmpty then "" else s!" through {", then ".intercalate route}"
    s!"decision contract's {part} mentions its implementation `{implementation}`{through}; \
      state it without the implementation"
  let shown ← Meta.ppExpr decided
  let other := s!"decision contract decides `{shown}`, not its implementation \
    `{implementation}`; state the kind about the implementation, about `Function.uncurry` of \
    it, or about it applied to every field of one structure with no index, in order, and for \
    a result type that depends on the input about `Regula.Dependent.isSome` or `isOk` of that \
    function"
  let some (levels, packing) := decidedReading? env implementation decided.eta
    | return some other
  let reading : RegulaPolicy.DecidedFunction :=
    { packing, unsupplied := ← unsuppliedArguments result }
  unless reading.covers do
    -- The decision is `reading.covers`; this only selects which of its two conditions to name.
    unless packing.all RegulaPolicy.FieldPacking.covers do return some other
    return some s!"decision contract decides `{shown}`, whose result is a function of \
      {reading.unsupplied} more argument(s); a kind is read only about a result that is not a \
      function, so state it about the implementation `{implementation}` applied to every \
      argument, with one more `Function.uncurry` or one more field of the structure for each \
      of them"
  unless ownParameters levels do
    return some s!"decision contract decides its implementation `{implementation}` at the \
      universe levels {levels}, not at its own universe parameters; state the kind for every \
      universe level"
  if let some chain := mentionChain? env implementation accepts then
    return some (mention "acceptance predicate" chain)
  if let some chain := mentionChain? env implementation spec then
    return some (mention "specification" chain)
  return none

/-- The statement of a decision registration that `decisionFailure?` did not refuse: the
implementation's constant, the acceptance predicate and the specification of its kind. The
registration is closed, so the two terms have no free variable. -/
structure DecisionStatement where
  /-- The registered implementation. -/
  implementation : Name
  /-- The acceptance predicate of the kind. -/
  accepts : Expr
  /-- The specification of the kind. -/
  spec : Expr

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
The record's decision kind is read from the head constant of the requirement, reduced the same
way (`decisionRequirement?`), so an alias of a kind is recognized and no theorem text is
matched. A registration that is eligible and states a kind is refused when the kind is not about
the implementation on every argument and at its own universe parameters, or when its acceptance
predicate or specification mentions the implementation (`decisionFailure?`); an eligibility
refusal is reported first, so a registration that states no kind has the record it had before
kinds existed, with no kind.
At the `snapshot` stage, a kind is not read when the environment cannot say whether its decided
function is a field application (`hiddenField?`): the record then has no failure of the kind,
and the constant that the environment has only as an axiom is returned with it, so that the
caller can report the reading as unavailable. Every other stage reads every kind, and the second
component is `none`.
The third component is the statement of a decision registration that was read and not refused
(`DecisionStatement`): the caller searches it for the functions that its two sides share
(`sharedReading`), and the record names them.
-/
private def executableContract? (env : Environment) (scope : ContractScope) (stage : Stage)
    (info : ConstantInfo) :
    CommandElabM (Option (RegulaPolicy.ExecutableContract × Option Name ×
      Option DecisionStatement)) := do
  if !#[DeclarationKind.definition, .theorem, .opaque].contains (kindOf info) then return none
  if info.name == Lean.mkFlatCtorOfStructCtorName ``Regula.ExecutableContract.mk then return none
  unless (← scope.mayReach env info.type) do return none
  liftTermElabM <| Meta.withTransparency .all <|
    Meta.forallTelescopeReducing info.type (whnfType := true) fun parameters type => do
    if !type.isAppOfArity ``Regula.ExecutableContract 3 then return none
    let args := type.getAppArgs
    let implementation := args[1]!
    let applied := mkApp args[2]! implementation
    let requirement ← Meta.ppExpr applied
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
    let decision ← decisionRequirement? env scope applied
    let hidden := match stage, failure, root, decision with
      | .snapshot, none, some name, some (_, _, _, _, decided) =>
          hiddenField? env name decided.eta
      | _, _, _, _ => none
    let failure ← match hidden, failure, root, decision with
      | none, none, some name, some (_, result, accepts, spec, decided) =>
          decisionFailure? env name result accepts spec decided
      | _, _, _, _ => pure failure
    -- A registration with no failure is closed, so its acceptance predicate and its
    -- specification have no free variable and can leave this telescope.
    let statement := match hidden, failure, root, decision with
      | none, none, some implementation, some (_, _, accepts, spec, _) =>
          some { implementation, accepts, spec : DecisionStatement }
      | _, _, _, _ => none
    return some ({
      root := root.getD .anonymous
      requirement := toString requirement
      failure
      kind := decision.map (·.1) }, hidden, statement)

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

/-- Whether Lean loaded the imported module of index `index` from the toolchain's own library
directory: its `.olean` file is that module's file in the library directory of the running
toolchain, by canonical path (`loadedFromLibrary`). The answer is kept in the scope. -/
def ContractScope.fromToolchain (scope : ContractScope) (env : Environment) (index : Nat) :
    IO Bool := do
  if let some known := (← scope.toolchain.get)[index]? then return known
  let answer ← match env.header.moduleNames[index]? with
    | none => pure false
    | some moduleName => loadedFromLibrary (← toolchainLibraryDirectory) moduleName
  scope.toolchain.modify (·.insert index answer)
  return answer

/-- Whether `name` is declared outside Lean's own library: in the current module, or in an
imported module that Lean did not load from the toolchain's library directory
(`ContractScope.fromToolchain`). The search for shared definitions reads only such constants. A
module of the toolchain imports no module of a project or of a dependency, so no constant of the
toolchain mentions a constant of one, and the search loses nothing when it does not follow
them. -/
def ContractScope.outsideToolchain (scope : ContractScope) (env : Environment) (name : Name) :
    IO Bool :=
  match env.getModuleIdxFor? name with
  | none => pure true
  | some index => return !(← scope.fromToolchain env index.toNat)

/-- What the fields of a structure type say of its values, read at the arguments of the type. -/
private structure FieldReading where
  /-- Every field is a proof or has a sort as its result, as the one field of `LT α` has: a
  value is a record of statements. A structure with no field is read so too. -/
  statements : Bool
  /-- Some field that is no proof and has no sort as its result takes an argument: a value
  carries a function, as a value of `BEq α` or of `Ord α` does. -/
  function : Bool

/-- The reading of the fields of `result`, when it is a structure type applied to its
parameters: an inductive type with one constructor and no index. The fields are the binders of
the constructor's type at the universe levels and the parameters of `result`. So a field whose
type is a parameter is read at the actual argument: the field of `Box Prop` is a statement, and
the field of `Box Nat` is not. The numbers of constructors, of indices, of parameters and of
fields are read from the kernel-checked declarations. `none` for every other type. A field is
read one level deep: a field whose type is itself a structure is no statement and no function
here. -/
private def readFields (env : Environment) (result : Expr) : MetaM (Option FieldReading) := do
  let .const head levels := result.getAppFn | return none
  let some (.inductInfo type) := env.find? head | return none
  let [constructorName] := type.ctors | return none
  unless type.numIndices == 0 do return none
  let some (.ctorInfo constructor) := env.find? constructorName | return none
  let parameters := result.getAppArgs
  unless parameters.size == constructor.numParams do return none
  unless levels.length == constructor.levelParams.length do return none
  let fieldsType ← Meta.instantiateForall
    (constructor.type.instantiateLevelParams constructor.levelParams levels) parameters
  Meta.forallBoundedTelescope fieldsType (some constructor.numFields) fun fields _ => do
    unless fields.size == constructor.numFields do return none
    let mut statements := true
    let mut function := false
    for field in fields do
      let fieldType ← Meta.inferType field
      if ← Meta.isProp fieldType then continue
      let (sort, takesArgument) ← Meta.forallTelescopeReducing fieldType (whnfType := true)
        fun arguments fieldResult => pure (fieldResult.isSort, !arguments.isEmpty)
      if sort then continue
      statements := false
      if takesArgument then function := true
    return some { statements, function }

/-- The result form of a constant of type `type` (`RegulaPolicy.ResultForm`): `proof` when
`type` is a proposition, and otherwise the form of `type` with every leading binder opened and
every definition unfolded. `Decidable`, `Bool` and `BEq` are read by name, at their own numbers
of arguments. A structure type is a statement when each of its fields, at the arguments of that
type, is a proof or has a sort as its result (`readFields`). -/
private def readResultForm (env : Environment) (type : Expr) :
    MetaM RegulaPolicy.ResultForm :=
  Meta.withTransparency .all do
    if ← Meta.isProp type then return .«proof»
    Meta.forallTelescopeReducing type (whnfType := true) fun _ result => do
      if result.isSort then return .«statement»
      if result.isAppOfArity ``Decidable 1 then return .«decidable»
      if result.isConstOf ``Bool then return .«bool»
      if result.isAppOfArity ``BEq 1 then return .«beq»
      if let some reading ← readFields env result then
        if reading.statements then return .«statement»
      return .«other»

/-- The result form of the constant `info` (`readResultForm`), kept in the scope. -/
def ContractScope.resultForm (scope : ContractScope) (env : Environment) (info : ConstantInfo) :
    MetaM RegulaPolicy.ResultForm := do
  if let some known := (← scope.forms.get).find? info.name then return known
  let form ← readResultForm env info.type
  scope.forms.modify (·.insert info.name form)
  return form

/-- What the search for shared definitions reads of the constant `info`
(`RegulaPolicy.SharedDefinition`). Its kind is the kind of its `ConstantInfo`. Whether it is a
projection function is read from its kernel-checked value (`projectionBody?`), as `boundField?`
reads it: no type tells a field's projection function from a function that computes, and Lean's
record of projection functions is environment state that a project can write.

Whether it is a function is read from its type alone, with every definition unfolded: the type
has a leading binder, or its result is a structure type with a field that takes an argument and
is neither a proof nor a statement, at the arguments of that type (`readFields`), as `BEq α` and
`Ord α` are. The form of its value has no part: a closed list whose value has a function
abstraction is no function, and a record of functions is one whether its value is a constructor
application or a name for one.

Its result form is read from its type (`ContractScope.resultForm`). Whether Lean generated it
for an inductive type or as a matcher is what `generatedBy?` says for the families of a
projection, a recursor, a matcher, a constructor lemma and a type construction; those clauses
read Lean's records, which a project can write, and the pure classification uses the answer
only to take a definition out of the class `other`
(`RegulaPolicy.SharedDefinition.class`).

A constant that the environment has as an axiom is read in the same way, from its type and its
name: the environment of a file with a `module` header has an imported definition as an axiom
when its module does not export the value (`hiddenValue?`), and the type of such a constant
still says whether it is a function and what the form of its result is. -/
private def sharedDefinition (env : Environment) (scope : ContractScope) (info : ConstantInfo) :
    MetaM RegulaPolicy.SharedDefinition := do
  let projection := match info with
    | .defnInfo definition => (projectionBody? definition.value 0).isSome
    | _ => false
  let generated ← match info with
    | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
      [GeneratedFamily.projection, .recursor, .matcher, .constructorLemma,
        .typeConstruction].anyM fun family =>
          return (← generatedBy? family info.name).isSome
    | _ => pure false
  let function ← Meta.withTransparency .all <|
    Meta.forallTelescopeReducing info.type (whnfType := true) fun arguments result => do
      if !arguments.isEmpty then return true
      return ((← readFields env result).map (·.function)).getD false
  return { name := info.name, kind := kindOf info, projection, function, generated
           result := ← scope.resultForm env info }

/-- The constants that the search for shared definitions follows from `info` by the rule of a
function: the rule by which it reads the implementation (`sharedReading`).

The rule follows the type of a definition, of a theorem, of an opaque constant and of an axiom.
It follows the value of a definition when the pure decision says that the value is read
(`RegulaPolicy.ResultForm.ValueRead`): not the value of a proof, and not the value of a
statement, which a function does not run. A function runs a `Decidable` value, so its value is
read. The constants of a value are all the constants that it mentions: in `decide p`, those of
the proposition `p` and those of the instance term, which names the same functions. The rule
does not follow the value of a theorem or of an opaque constant: Lean's kernel unfolds neither.
From an inductive type, a constructor and a recursor it follows nothing, not their types
either: a function depends on the declaration of its data, which is not a shared definition,
and not on what a field's type mentions. The acceptance predicate is read by the rule of a
statement (`statementRecords`), and the specification by the reading of a statement
(`readStatement`). -/
private def functionReferences (env : Environment) (scope : ContractScope) (info : ConstantInfo) :
    MetaM (Array Name) := do
  match info with
  | .defnInfo definition =>
    let form ← scope.resultForm env info
    return if decide (form.ValueRead false) then
      info.type.getUsedConstants ++ definition.value.getUsedConstants
    else info.type.getUsedConstants
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => return #[]
  | _ => return info.type.getUsedConstants

/-- The constants outside Lean's own library that the implementation `root` reaches by the rule
of a function (`functionReferences`): the root itself and, closed under that rule, the constants
that it mentions. A constant of Lean's own library is not followed
(`ContractScope.outsideToolchain`). -/
private def implementationReach (env : Environment) (scope : ContractScope) (root : Name) :
    MetaM NameSet := do
  let mut reached : NameSet := {}
  let mut seen : NameSet := {}
  let mut pending := #[root]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    unless ← scope.outsideToolchain env name do continue
    let some info := env.find? name | continue
    reached := reached.insert name
    pending := pending ++ (← functionReferences env scope info)
  return reached

/-- What the observing pass reads of the constant `info` for the rule of a statement
(`RegulaPolicy.StatementReading.Observed`): its kind, its result form
(`ContractScope.resultForm`), the constants of its type, of the value of a definition and of the
declaration of an inductive type and of a recursor, as `unfoldReferences` reads them, and the
structure of a field's projection function, read from its kernel-checked value
(`projectionBody?`), as `sharedDefinition` reads it. -/
private def observeStatement (env : Environment) (scope : ContractScope) (info : ConstantInfo) :
    MetaM RegulaPolicy.StatementReading.Observed := do
  let value := match info with
    | .defnInfo definition => definition.value.getUsedConstants
    | _ => #[]
  let declaration := match info with
    | .inductInfo value => value.ctors.toArray
    | .recInfo value =>
      value.rules.foldl (fun names rule => (names.push rule.ctor) ++ rule.rhs.getUsedConstants) #[]
    | _ => #[]
  let projection := match info with
    | .defnInfo definition => (projectionBody? definition.value 0).map (·.1)
    | _ => none
  return { kind := kindOf info, result := ← scope.resultForm env info
           type := info.type.getUsedConstants, value, declaration, projection }

/-- The record of each constant outside Lean's own library (`ContractScope.outsideToolchain`) that
`roots` reach by the rule of a statement (`RegulaPolicy.StatementReading.Observed.references`), as
`observeStatement` reads it: the reading of a statement before it left out the declaration of the
input type. A constant of `skip` gets no record, and the closure does not follow it. -/
private def statementRecords (env : Environment) (scope : ContractScope) (skip : NameSet)
    (roots : Array Name) : MetaM (Std.HashMap Name RegulaPolicy.StatementReading.Observed) := do
  let mut records : Std.HashMap Name RegulaPolicy.StatementReading.Observed := {}
  let mut seen := skip
  let mut pending := roots
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    unless ← scope.outsideToolchain env name do continue
    let some info := env.find? name | continue
    let observed ← observeStatement env scope info
    records := records.insert name observed
    pending := pending ++ observed.references
  return records

/-- What the observing pass reads of a specification, with the pure reading of it
(`RegulaPolicy.StatementReading.reading`). -/
private structure StatementRead where
  /-- The record of each constant that the pass read. -/
  records : Std.HashMap Name RegulaPolicy.StatementReading.Observed
  /-- The constants of the input type of the kind, as `readStatement` reads them. -/
  domain : Array Name
  /-- The constants of the body of the term under its variable, as `readStatement` reads them. -/
  body : Array Name
  /-- The definition that the specification is, alone or applied to its variable alone, when the
  snapshot of a file with a `module` header has it only as an imported axiom: the reading does not
  follow it (`readStatement`). -/
  unread : Option Name
  /-- The two readings of the term. -/
  reading : RegulaPolicy.StatementReading.Reading

/-- The reading of `term`, the specification of a decision registration, by the rule of a
statement with the exception of its input type: the observing pass and the pure search
`RegulaPolicy.StatementReading.reading`. The acceptance predicate has no such reading:
`sharedReading` reads it by the rule of a statement alone (`statementRecords`).

The term is a function of the input of the kind. The request
(`RegulaPolicy.StatementReading.Request`) has the constants of an input type `α` as its `domain`
and the constants of a body `b` as its `body`, in three forms:

* For `fun x : α => b`, the binder type and the body of the term.
* When the term is a definition `C`, alone or applied to its variable alone (`fun x => C x`,
  `Lean.Expr.eta`), and the kernel-checked value of `C`, at the universe levels of the term, is
  `fun x : α => b`: the binder type and the body of that value. `C x` is `b` by the unfolding of
  `C`, so the body is what the term states, and a `∀ y : α` in `b` still names `α` in the body.
* For every other term, the domain of its type as `α`, and the term as `b`.

The domain also has the constants of `α` with its reducible definitions unfolded at its head
(`Meta.whnfR`), so the input type of an `abbrev` is the structure that its projections name. The
pass reads each constant that the constants of the domain and of the body reach by the rule of a
statement (`statementRecords`). That closure holds each constant that the reading reaches too
(`RegulaPolicy.StatementReading.read_subset_withTypes`). The pure search then gives the two
readings over those records (`RegulaPolicy.StatementReading.reading_some`); its bound of steps
covers every record, and the reading refuses with an error should it run out.
`RegulaPolicy.StatementReading.through_input` holds of the request in each form, since it holds
of every request. That the pass reads the environment truly is this function's, not a theorem.

`hides` says that the environment is the snapshot of a file with a `module` header, which has an
imported definition as an axiom when its module does not export the value. There, when the term
is such a constant `C`, alone or applied to its variable alone, the pass cannot read the body of
`C`, and it does not read `C` through its type: `C` gets no record, so neither reading follows it,
and `unread` names it. The project check, which has the value of `C`, reads its body. In every
other environment, an axiom `C` keeps its record. -/
private def readStatement (env : Environment) (scope : ContractScope) (hides : Bool) (term : Expr) :
    MetaM StatementRead := do
  let term := term.consumeMData
  let unread := match hides, term.eta with
    | true, .const name _ => match env.getModuleIdxFor? name, env.find? name with
      | some _, some (.axiomInfo _) => some name
      | _, _ => none
    | _, _ => none
  let named := match term.eta with
    | .const name levels => match env.find? name with
      | some info@(.defnInfo _) => match (info.instantiateValueLevelParams! levels).consumeMData with
        | value@(.lam ..) => some value
        | _ => none
      | _ => none
    | _ => none
  let (input, body) ← match named.getD term with
    | .lam _ type body _ => pure (some type, body.getUsedConstants)
    | _ => do
      let input := match ← Meta.whnf (← Meta.inferType term) with
        | .forallE _ type _ _ => some type
        | _ => none
      pure (input, term.getUsedConstants)
  let domain ← match input with
    | some type => pure (type.getUsedConstants ++ (← Meta.whnfR type).getUsedConstants)
    | none => pure #[]
  let records ← statementRecords env scope (unread.elim {} ({} : NameSet).insert) (domain ++ body)
  let some reading := RegulaPolicy.StatementReading.reading { records, domain, body }
    | throwError "the reading of a decision statement ran out of its bound of steps"
  return { records, domain, body, unread, reading }

/-- The first shared functions of a specification: each constant outside Lean's own library
that the body of `spec` reaches by the reading of a statement
(`RegulaPolicy.StatementReading.Observed.read`, over the records of `read`), that `other` also
holds of, and that the pure classification counts (`RegulaPolicy.SharedDefinition.Counted`: its
class is `boolean` or `other`).

The search starts at the constants of the body of the specification. It does not follow a
counted constant that `other` holds of, so a constant below one is found only when `spec` also
reaches it on a path with no such constant. Which constants it finds does not depend on the order
of the search: they are the counted constants of `other` that are reachable when the edges out of
those constants are removed. Each constant that it reaches has a record exactly when it is
outside Lean's own library, in the environment and not the unread constant of the term
(`StatementRead.unread`), since the records are the closure of the rule of a statement, which
holds that of the reading. The unread constant is a specification that the snapshot of a file
with a `module` header has only as an imported axiom: it has no record, and `sharedReading`
reports it (`Unread.shared`) where a shared test could be below it. -/
private def sharedFrontier (env : Environment) (scope : ContractScope) (other : Name → Bool)
    (read : StatementRead) : MetaM (Array RegulaPolicy.SharedDefinition) := do
  let mut seen : NameSet := {}
  let mut pending : Array Name := #[]
  for name in read.body do
    unless seen.contains name do
      seen := seen.insert name
      pending := pending.push name
  let mut found : Array RegulaPolicy.SharedDefinition := #[]
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    let some observed := read.records[name]? | continue
    let some info := env.find? name | continue
    if other name then
      let definition ← sharedDefinition env scope info
      if decide definition.Counted then
        found := found.push definition
        continue
    for next in observed.read read.domain do
      unless seen.contains next do
        seen := seen.insert next
        pending := pending.push next
  return found

/-- What the snapshot of a file with a `module` header did not read of a decision registration,
with the imported constant that its environment has only as an axiom. The project check, whose
environment has the value of each constant, reads both. -/
inductive Unread where
  /-- The kind: whether the constant is a field of the argument of the decided function is
  unknown (`executableContract?`). The record has no failure of the kind. -/
  | kind (constant : Name)
  /-- The shared functions: a function with a result of `Bool` or `BEq` that the two sides share
  only below the constant is not found (`sharedReading`). The record names no such function. -/
  | shared (constant : Name)
  deriving Repr, DecidableEq, Inhabited

/-- A constant of `reach` whose value the search would read and the environment does not have:
an imported constant that `env` has as an axiom, with a result form whose value the rule of the
side reads (`RegulaPolicy.ResultForm.ValueRead`; `specification` selects the rule of a statement).
The environment of a file with a `module` header has an imported definition or opaque constant as
an axiom when its module does not export the value, so the search cannot follow it. An axiom that
a project declares is such a constant too: it has no value in any environment, and the notice of
the caller is then more than is needed. -/
private def hiddenValue? (env : Environment) (scope : ContractScope) (specification : Bool)
    (reach : NameSet) : MetaM (Option Name) := do
  for name in reach do
    if (env.getModuleIdxFor? name).isNone then continue
    let some info := env.find? name | continue
    let .axiomInfo _ := info | continue
    if decide ((← scope.resultForm env info).ValueRead specification) then return some name
  return none

/-- Whether `reach` has a constant of the class `boolean`
(`RegulaPolicy.SharedDefinition.class`). -/
private def reachesTest (env : Environment) (scope : ContractScope) (reach : NameSet) :
    MetaM Bool := do
  for name in reach do
    let some info := env.find? name | continue
    if decide ((← sharedDefinition env scope info).class = .boolean) then return true
  return false

/-- The functions that the two sides of a decision registration share, as its record names
them (`RegulaPolicy.SharedNames`), and the constant that keeps a snapshot from reading them all,
when there is one.

One side is the specification. The other side is the implementation with the acceptance
predicate: a kind states `accepts (f x)` against `spec x`, so a definition that the acceptance
predicate and the specification share enters both sides of that statement as one that the
implementation and the specification share does. The search reads the implementation by the
rule of a function (`functionReferences`), and the acceptance predicate by the rule of a
statement from all of its constants, the type of its variable included (`statementRecords`), as
before #270: the value of a definition of a proposition that it names is read, and the value of
a `Decidable` instance that it names is not. A value of the result type occurs on one side of the
kind only, in `accepts (f x)`, so a test that the declaration of the result type names can be a
part of that side, and the search reads that declaration.

The search reads the specification by the reading of a statement (`readStatement`, the registered
decision `RegulaPolicy.StatementReading.reads`), which leaves out the declaration of the input type
entered from the input: the two sides range over the same inputs. The reading starts at the body
of the specification's function abstraction. When the specification is a definition, alone or
applied to its variable alone, the reading starts at the body of that definition's value. From a
field's projection function of a structure of the input type it does not follow the edge back to
that structure. A definition that the body names among other terms, or that the value of a named
specification names, has its type read: where that type names the input type, the reading enters
the declaration of the input type there. The reading follows everything else as the rule of a
statement does. The search reads kernel-checked values only. A runtime replacement
(`implemented_by`, `extern`, `csimp`) is in no such value: a kind is a theorem about the
definition that Lean's kernel reads, and the execution closure accounts for the code that runs in
its place.

The record has three lists, from three readings of the specification against the same other
side. The first reading stops at each counted constant that the other side reaches
(`sharedFrontier`), and the functions of the class `other` are named from it. The second reading
stops nowhere: it has each constant that the specification reaches by the reading of a statement
and that the other side reaches too, also below a counted one. The functions of the class
`boolean` are named from the second reading, so a record that names none has none at any depth,
a function of that class below a function of the class `other` included. The third reading is the
rule of a statement from the whole specification, its input type included
(`RegulaPolicy.StatementReading.Observed.references`): the functions of the class `boolean` that
it has and the second does not are named apart (`RegulaPolicy.SharedNames.throughTypes`), and no
registration is refused for them. The specification reaches each only through a constant of the
input type that the reading does not reach (`RegulaPolicy.StatementReading.through_input`).

`RegulaPolicy.sharedNames` gives the names by class over what the readings read
(`RegulaPolicy.mem_sharedNames_booleans`, `RegulaPolicy.mem_sharedNames_others`,
`RegulaPolicy.mem_sharedNames_throughTypes`), and the shared constants of the second and third
readings are `RegulaPolicy.StatementReading.sharedConstants`: a registration whose record names
no function of the class `boolean` has no such function that the reading of the specification
reaches and that the implementation or the acceptance predicate reaches
(`RegulaPolicy.StatementReading.no_shared_test`). The search itself is operational apart from the
reading of a statement, and it refuses no registration: the pure decision
`RegulaPolicy.sharedTestFailure` refuses a registration whose record names a function of the
class `boolean`. The search names the functions that the two sides share by name. It does not
establish that the specification is the intended one, and a copy of a definition under a second
name is a different constant, which it does not find.

The second component is for the `snapshot` stage in the environment of a file with a `module`
header, where a side can reach a constant with no value (`hiddenValue?`). The search does not
read below such a constant, so a function of the class `boolean` that the two sides share only
below it is not found. A specification that is such a definition, alone or applied to its
variable alone, is such a constant of its side (`StatementRead.unread`): the reading does not
follow it, not through its type either, since the project check reads its body and not its type.
An acceptance predicate that is such a definition is read through its type, by the rule of a
statement. That can be only in three cases, and the component is the constant of
the first that holds, of the other side where the two sides have one. Each side has such a
constant. Or the other side has one, and the
specification reaches a function of the class `boolean`, which the other side could reach below
that constant. Or the specification has one, and the other side reaches a function of that
class. In every other case each shared function of the class is one that the readings have,
so the list is complete. The component is `none` when the record names a function of the class,
since the registration is then refused whatever is below, and at every other stage, whose
environment has the value of each constant. -/
private def sharedReading (env : Environment) (scope : ContractScope) (stage : Stage)
    (statement : DecisionStatement) : MetaM (RegulaPolicy.SharedNames × Option Name) := do
  let hides := stage == .snapshot && env.header.isModule
  let implementation ← implementationReach env scope statement.implementation
  let acceptance := (← statementRecords env scope {} statement.accepts.getUsedConstants).fold
    (fun reach name _ => reach.insert name) ({} : NameSet)
  let other := fun name => implementation.contains name || acceptance.contains name
  let specificationRead ← readStatement env scope hides statement.spec
  let specificationReading := specificationRead.reading
  let first ← sharedFrontier env scope other specificationRead
  let mut definitions : Std.HashMap Name RegulaPolicy.SharedDefinition := {}
  for name in specificationReading.withTypes do
    if other name then
      let some info := env.find? name | continue
      definitions := definitions.insert name (← sharedDefinition env scope info)
  let shared (widen : Bool) := RegulaPolicy.StatementReading.sharedConstants widen
    specificationReading implementation.contains acceptance.contains (definitions[·]?)
  let names := RegulaPolicy.sharedNames first.toList (shared false) (shared true)
  unless hides && names.booleans.isEmpty do
    return (names, none)
  let specification := specificationReading.read.foldl NameSet.insert {}
  let hiddenOther ← match ← hiddenValue? env scope false implementation with
    | some constant => pure (some constant)
    | none => hiddenValue? env scope true acceptance
  let unread := specificationRead.unread.elim specification specification.insert
  match ← hiddenValue? env scope true unread, hiddenOther with
  | none, none => return (names, none)
  | some _, some constant => return (names, some constant)
  | none, some constant =>
    return (names, if ← reachesTest env scope specification then some constant else none)
  | some constant, none =>
    let tested ← reachesTest env scope implementation <||> reachesTest env scope acceptance
    return (names, if tested then some constant else none)

/-- What admission computed in the kernel that replayed the owned modules (`Admission.validate`): the
axioms that each name of the owned declarations' closure reaches there, and for each owned
declaration for which Lean's `collectAxioms` omits some of them, those omissions. -/
structure Replayed where
  /-- The axioms each name of the closure reaches in the replayed kernel, by name. -/
  axioms : Std.HashMap Name (Array Name)
  /-- The axioms that `collectAxioms` omits for an owned declaration, by its name. -/
  omissions : Std.HashMap Name (Array Name)

/-- The record of `declaration`, with what a snapshot did not read of the declaration's decision
registration, when there is such a part (`Unread`): its kind (`executableContract?`), or the
functions that its two sides share (`sharedReading`). The record of a decision registration that
was read and not refused holds the names of the functions that its two sides share. Its axioms are
those `replayed` holds for the declaration, the axioms it reaches in the kernel that replayed it
(`Admission.validate`), with the axioms `collectAxioms` omits of them, or, with no `replayed`,
those Lean's `collectAxioms` reports. -/
private def declarationReading (name : Name) (stage : Stage) (scope? : Option ContractScope)
    (replayed : Option Replayed) :
    CommandElabM (RegulaPolicy.Declaration × Option Unread) := withoutSmartUnfolding do
  let env ← getEnv
  let scope ← match scope? with
    | some scope => pure scope
    | none => ContractScope.new env
  let some info := env.find? name | throwError "declaration {name} is unavailable"
  let moduleName ← IO.ofExcept (moduleOf env name)
  let axioms ← match replayed with
    | some table => match table.axioms[name]? with
      | some axioms => pure axioms
      | none => throwError "declaration {name} has no axioms from the replayed kernel"
    | none => collectAxioms name
  let tableOmissions := (replayed.bind (·.omissions[name]?)).getD #[]
  let isProp ← liftTermElabM <| Meta.isProp info.type
  let prettyType ← liftTermElabM do
    return toString (← Meta.ppExpr info.type)
  let ranges? ← findDeclarationRangesCore? name
  let recursive ← liftTermElabM <| Meta.isRecursiveDefinition name
  let unsafeRecRegenerated ← if stage == .replayCandidate then
      unsafeRecRegeneration env name info scope.preprocessRules scope.axioms else pure none
  -- One recognition gives the recorded statement and the replayed expression: a replay is
  -- recorded only for an axiom with a recognized statement.
  let native? := nativeRecognition? name info.type
  let nativeReplay? ← if stage == .replayCandidate then
      native?.mapM fun found => replayNative found.2
    else pure none
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
  let generatedFrom ← liftTermElabM (generatedFrom? name)
  let contract? ← (← executableContract? env scope stage info).mapM
    fun (record, hidden, statement) => do
      let some statement := statement | return (record, hidden.map Unread.kind)
      let (shared, unread) ← liftTermElabM <| sharedReading env scope stage statement
      return ({ record with shared }, unread.map Unread.shared)
  return ({
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
    nativeStatement := native?.map fun found => nativeStatementText found.2
    nativeReplay := nativeReplay?
    recordedRanges := ranges?.map rangesReport
    generatedFrom
    axioms := RegulaPolicy.canonicalNames axioms
    executableContract := contract?.map (·.1)
    decisionResult := ← liftTermElabM (decisionResult? scope.decisions info)
    tableOmissions
  }, contract?.bind (·.2))

/-- Construct the canonical record from this command's actual environment.
Replay candidates still require the existing fresh transcript and admission guards;
these observations alone never authorize a generated role. A caller recording several declarations
of one environment passes one `ContractScope.new` of it, so its memo is shared; without one, a
fresh scope is built. Every observation runs with smart unfolding off (`withoutSmartUnfolding`).
At the `snapshot` stage, in the environment of a file with a `module` header, the record of a
decision registration has no failure of its kind when that environment cannot read the kind, and
it names no shared function below a constant that the environment has no value of;
`commandDeclarations` returns those registrations. The record's axioms are those `replayed`
holds for the declaration, the axioms it reaches in the kernel that replayed it
(`Admission.validate`), and its `tableOmissions` are those `replayed` holds for it; a caller with
no replayed kernel, such as the editor, passes none, and the record has the axioms Lean's
`collectAxioms` reports. -/
def declaration (name : Name) (stage : Stage) (scope? : Option ContractScope := none)
    (replayed : Option Replayed := none) :
    CommandElabM RegulaPolicy.Declaration :=
  (·.1) <$> declarationReading name stage scope? replayed

/-- Complete current-module inventory, with no visibility or generated-name filter.
Uses Lean's own local constant map through its environment-linter API. The caller
must separately establish completion of elaboration before claiming completion. -/
def currentModule (stage : Stage := .snapshot) : CommandElabM (Array RegulaPolicy.Declaration) := do
  let scope ← ContractScope.new (← getEnv)
  (← liftCoreM Lean.Linter.EnvLinter.getDeclsInCurrModule).mapM (declaration · stage scope)

/-- Declaration binders recorded in this command's information trees. This is a
local feedback selection, not a complete module census: elaborators can add
constants without binder information. `currentModule` covers those as well. The second component
is each decision registration of which the snapshot does not read a part, with that part and the
constant that the environment has only as an axiom (`Unread`): its record has no failure for
that part, and the project check reads it. -/
def commandDeclarations :
    CommandElabM (Array RegulaPolicy.Declaration × Array (Name × Unread)) := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for tree in (← get).infoState.trees do
    for name in Lean.Linter.getNewDecls tree do
      -- Information trees can retain binders from disposable elaborator
      -- environments (for example run_cmd's temporary evaluator). Intersect
      -- with actual current declarations before constructing observations.
      if (env.getModuleIdxFor? name).isNone && (env.find? name).isSome &&
          !names.contains name then names := names.push name
  if names.isEmpty then return (#[], #[])
  let scope ← ContractScope.new env
  let readings ← names.mapM (declarationReading · .snapshot scope none)
  return (readings.map (·.1), readings.filterMap fun (record, unread) =>
    unread.map (record.name, ·))

end Regula.Collect
