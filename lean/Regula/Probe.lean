import Std.Data.DHashMap.Lemmas
import Regula.Collect
import Regula.StructuralName
import Lean.Elab.Command
import Lean.Compiler.Old
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.IR.EmitUtil
import Lean.DeclarationRange
import Lean.Elab.PreDefinition.Structural.Eqns
import Lean.Elab.PreDefinition.WF.Eqns
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Native
import Lean.Meta.Eqns
import Lean.Meta.RecExt
import Lean.ProjFns
import Lean.Util.FoldConsts
import Std.Internal.UV.System
import Regula.Report
import Regula.Contract
import Regula.MaterialClaim

/-!
# Machine-audit environment probe

Machine-audit support consumed directly by the repository's Lean checker
executables.

The trusted runner calls `environmentReport` on a Lean-imported elaborated
environment — never on source text. The `audit_dump_json` command remains only
as an interactive compatibility entrypoint. For every declaration whose exact
module index is requested, the report records:

- the declaration's module and constant kind (axiom, theorem, def, opaque,
  constructor, inductive, recursor, quotient);
- the exact elaborated type, whether that type is a proposition, and
  `ConstantInfo.isUnsafe` / `ConstantInfo.isPartial` for every constant kind;
- instance / `noncomputable` / `@[implemented_by]` / `@[extern]` flags;
- the exact transitive axiom set (`Lean.collectAxioms`), which is what
  `#print axioms` reports; and
- Lean-native reporting metadata (internal/private spelling, projection,
  matcher, recursor kind, unsafe-recursion relationship, and source range).

The report additionally carries an execution-coverage account, distinct from
the logical axiom audit: for every owned executable root (computable,
non-proposition, safe, non-partial, non-internal definitions and opaque
constants, including claimed executable `main`s) it computes the transitive
conservative closure over value-level dependencies, retained compiler IR,
constant-equality simplification candidates, historical `@[implemented_by]`
targets, and partial helpers. `@[extern]` constants are boundary leaves for
their Lean bodies. The report distinguishes possible replacements from actual
retained compiler edges and records every boundary in this closure:
compiler simplifications, `@[implemented_by]` replacements, `@[extern]` declarations split into
toolchain native-runtime primitives and other external code, unsafe/partial/opaque
computation, and compiler-trusting proof axioms. A replacement, `extern`, or unsafe or partial
computation declared in an origin-checked `Init`, `Std` or `Lean` module carries that
module's toolchain origin: it is the toolchain's trusted base, and a toolchain replacement is
followed through its current target without source history or correspondence. An unsafe
constant whose type Lean's `Meta.isProp` finds to be a proposition, such as `lcProof`, is a
proof the compiler erases and is no boundary. Each
boundary is marked `checked` (kernel-definitional equality, a standard-logical
correspondence theorem, or a kernel-checked opaque body), `trusted`, or
`unresolved`; unresolved paths are listed per root. Imported boundary
declarations are reported by this account without becoming owned.

Generated-role metadata is descriptive, not provenance. The checker policy
combines these semantic fields with a fresh exact-source frontend transcript
before it recognizes Lean's range-less internal code-generation helper for a
safe recursive base or a native-proof axiom. Names, ranges, and extension tags
alone never waive a rule. Every declaration is still emitted and checked.

The full list of imported module names and each module's Lean-resolved `.olean`
path are emitted as well, so drivers can reconcile the queried Lake inventory,
identify root-package ownership through Lake's actual output directory, and
detect fixture contamination. The trusted checker runner invokes the reporter
directly without parsing observer syntax in the audited module's frontend
extension environment.

This module is checker infrastructure shipped inside the `Regula`
library so that any adopting project can probe its own modules; it is not part
of this repository's audited positive surface.
-/

namespace Regula.Probe

open Lean Elab Command
open RegulaPolicy (DeclarationKind BoundaryKind Correspondence DefeqComparison Safety Reducibility
  RecursionOrigin)

/-- Compatibility name for the shared closed constant-kind mapping. -/
abbrev kindOf := Regula.Collect.kindOf

/-- Select the intersection of current kernel constants and Lean's exact
import ownership map, which attributes a name several modules declare to the first of them
while the kernel entry is the copy Lean's import kept. Reporting uses it; kernel admission
reads each module's own constants instead (`Admission.validate`). Enumerating ownership
first avoids an ownership hash
lookup for every dependency constant; IR-only names without constants are
ignored, and the current kernel entry retains subsumption semantics. -/
def ownedConstants (env : Environment) (modules : List Name) :
    Array (Name × ConstantInfo) := Id.run do
  let kernel := env.toKernelEnv
  let selected := env.header.modules.map fun imported => modules.contains imported.module
  let mut own := #[]
  for (name, idx) in kernel.const2ModIdx do
    if selected[(idx : Nat)]! then
      if let some info := kernel.find? name then
        own := own.push (name, info)
  return own

/-- The name, canonical `.olean` path and direct imports of every module loaded in `env`, in
header order. -/
def loadedModuleOrigins (env : Environment) : IO (Array Regula.Report.ModuleOrigin) :=
  env.header.moduleNames.zip env.header.moduleData |>.mapM fun (moduleName, data) => do
    let path ← IO.FS.realPath (← Lean.findOLean moduleName)
    return { name := moduleName, olean := path.toString, imports := data.imports.map (·.module) }

/-- Declarations attributed by Lean to one of the exact requested modules. -/
private def ownedDecls (env : Environment) (modules : List Name) :
    CommandElabM (Array (Name × ConstantInfo)) :=
  pure (ownedConstants env modules)

/-- Run one observation of the declaration `name`, so that its failure names the declaration's
module, the declaration and the observation. `CommandElabM`'s `try`/`catch` also catches Lean's
runtime resource exceptions (recursion depth, heartbeats), which the Core-based monads rethrow.
Such a limit, or a kernel limit (`Collect.checkerLimit?`), is the checker's own, so its message
replaces Lean's advice to raise it in the source. -/
private def observing {α : Type} (env : Environment) (name : Name) (observation : String)
    (act : CommandElabM α) : CommandElabM α := do
  try act
  catch ex =>
    let owner := match Regula.Collect.moduleOf env name with
      | .ok moduleName => m!"{moduleName}"
      | .error _ => m!"<unattributed>"
    if let some limit := (← Regula.Collect.checkerLimit? ex) then
      throwError "module {owner}, declaration {name}: {observation} reached the Regula checker's \
        own resource limit ({limit}); options set in the source, such as `maxRecDepth`, do not \
        apply to the checker. Report this as a Regula issue."
    throwError "module {owner}, declaration {name}: {observation} failed: {ex.toMessageData}"

/-- Kernel heartbeat budget for one correspondence check: Lean's per-declaration default
(`maxHeartbeats` at its default value, in the kernel's raw unit), so a checker-added
correspondence obligation costs no more than a declaration the adopter could write. -/
private def correspondenceHeartbeats : USize := (Core.getMaxHeartbeats {}).toUSize

/-- Resident memory the correspondence checks of one process may add above its peak resident
size at its first check: 1 GiB. The limit is fixed once per process, at that first check, to
that peak plus this allowance. The peak is at least the resident size then, so the first
check never fires on memory the process already held (its imported environment included).
Every later check in the process runs under the same limit, so no number of checks, exhausted
or not, raises the process's resident memory during a check above it. The allowance is shared
by every later check and all other resident growth in the process, so a later check that
starts at or above the limit exhausts at once and fails closed. At most three report workers
run at once, so the checks add at most 3 GiB to their first-check peaks; that increment
does not bound those peaks or memory used outside the checks. -/
private def correspondenceMemoryBytes : Nat := 1024 * 1024 * 1024

/-- This process's correspondence memory limit in bytes, fixed at its first check. -/
private initialize correspondenceLimit : IO.Ref (Option Nat) ← IO.mkRef none

/-- Lean's runtime memory limit in bytes (`lean -M`; `0` disables it). The kernel compares it
with the process's resident memory at its system checks and raises `excessiveMemory`.
`Lean.Shell` keeps its own binding of this runtime symbol private. -/
@[extern "lean_internal_set_max_memory"]
private opaque setMaxMemory (bytes : USize) : BaseIO Unit

/-- Run `action` under this process's correspondence limit, fixing it at the first call from
the peak resident size (libuv reports it in KiB), never above the limit the shell set from
`max_memory`, and restore that limit afterward. The runtime limit is process-wide, and a
process runs its correspondence checks sequentially. -/
private def withCorrespondenceMemory {α : Type} (opts : Options) (action : IO α) : IO α := do
  let outer := (opts.get? `max_memory).getD (0 : Nat) * 1024 * 1024
  let bound ← match ← correspondenceLimit.get with
    | some bound => pure bound
    | none => do
      let peak := (← Std.Internal.UV.System.getrusage).maxRSS.toNat * 1024
      let bound := peak + correspondenceMemoryBytes
      correspondenceLimit.set (some bound)
      pure bound
  let bound := if outer == 0 then bound else min outer bound
  setMaxMemory bound.toUSize
  try action finally setMaxMemory outer.toUSize

/-- Kernel resource exhaustion ends admission without a verdict on the proof. -/
private def kernelExhausted : Kernel.Exception → Bool
  | .deterministicTimeout | .excessiveMemory | .deepRecursion | .interrupted => true
  | _ => false

/-- Admission checks the constructed closed proof against the exact required
proposition in a disposable kernel declaration. Neither metavariable unification
nor a matching theorem statement alone authorizes `checked`. `none` means the
kernel exhausted its resources before deciding; a kernel rejection throws. -/
private def checkCorrespondenceProof (levels : List Name) (required proof : Expr) :
    MetaM (Option String) := do
  let required ← instantiateMVars required
  let proof ← instantiateMVars proof
  if required.hasMVar || proof.hasMVar || required.hasFVar || proof.hasFVar then
    throwError "correspondence has undischarged variables"
  let name ← mkFreshUserName `audit_correspondence
  let declaration := Declaration.thmDecl {
    name := name
    levelParams := levels
    type := required
    value := proof }
  let env ← getEnv
  let result ← withCorrespondenceMemory (← getOptions) <|
    IO.lazyPure fun _ => env.addDeclCore correspondenceHeartbeats 1000 declaration none
  let checked ← match result with
    | .ok checked => pure checked
    | .error e =>
      if kernelExhausted e then return none
      throwError "kernel rejected exact correspondence"
  let axioms ← withEnv checked <| collectAxioms name
  unless axioms.all (fun ax =>
      ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice) do
    throwError "correspondence exceeds standard-logical foundations"
  withOptions (fun opts => opts.setBool `pp.all true |>.setBool `pp.deepTerms true
      |>.set `pp.maxSteps (1000000 : Nat)) do
    return some s!"proof={← Meta.ppExpr proof}; required={← Meta.ppExpr required}"

/-- A theorem mentioning both endpoints is only a search candidate. For every
prefix of the actual dependent domain, instantiate its universes and premises,
match the equality, apply any remaining arguments by congruence, and close over
exactly the actual domain. Unsolved theorem-only premises remain metavariables
and cannot pass kernel admission. Search incompleteness never grants evidence. -/
private def theoremCorrespondence? (levels : List Name) (reference replacement : Expr)
    (domain : Array Expr) (required : Expr) (name : Name) : MetaM (Option String) := do
  for count in List.range (domain.size + 1) do
    for reverse in [false, true] do
      let result ← Meta.withoutModifyingMCtx do
        try
          let candidate ← Meta.mkConstWithFreshMVarLevels name
          let (args, _, conclusion) ← Meta.forallMetaTelescope (← Meta.inferType candidate)
          let lhs := mkAppN reference (domain.extract 0 count)
          let rhs := mkAppN replacement (domain.extract 0 count)
          let target ← if reverse then Meta.mkEq rhs lhs else Meta.mkEq lhs rhs
          unless ← Meta.isDefEq conclusion target do return none
          let mut proof ← instantiateMVars (mkAppN candidate args)
          if reverse then proof ← Meta.mkEqSymm proof
          for arg in domain.extract count domain.size do
            proof ← Meta.mkCongrFun proof arg
          proof ← Meta.mkLambdaFVars domain proof
          let some detail ← checkCorrespondenceProof levels required proof | return none
          return some s!"proved: {name}; {detail}"
        catch _ => return none
      if result.isSome then return result
  return none

/-- Require `∀ xs, reference.{us} xs = replacement.{us} xs`, where `us`
are rigid universal level parameters and `xs` is the complete elaborated
reference domain, including implicit, dependent, and proof parameters. The
compiler's positional universe substitution must type-check at those same
levels. Both definitional and theorem-backed evidence pass the same kernel gate.
Theorem candidates, supplied then discovered, are tried before definitional
unfolding, so a kernel-exhausting unfolding cannot consume the memory limit a
supplied proof needs. The definitional fallback returns
`DefeqComparison.classify` of its outcome, so a comparison the kernel could not complete is
unresolved, never trusted (standard §7.6). An elaborator resource limit reached while
constructing the correspondence is rethrown rather than recorded as unresolved. -/
private def replacementCorrespondence (env : Environment) (reference replacement : Name)
    (proofCandidates : Array Name := #[]) :
    CommandElabM (Correspondence × Option String) :=
  liftTermElabM <| Meta.withoutModifyingMCtx do
    try
      let referenceInfo ← getConstInfo reference
      let replacementInfo ← getConstInfo replacement
      let levels := referenceInfo.levelParams
      unless replacementInfo.levelParams.length == levels.length do
        throwError "unsupported replacement universes"
      let us := levels.map mkLevelParam
      let ref := mkConst reference us
      let impl := mkConst replacement us
      unless ← Meta.isDefEq (← Meta.inferType ref) (← Meta.inferType impl) do
        throwError "replacement types differ"
      Meta.forallTelescopeReducing (← Meta.inferType ref) fun domain _ => do
        let lhs := mkAppN ref domain
        let rhs := mkAppN impl domain
        let required ← Meta.mkForallFVars domain (← Meta.mkEq lhs rhs)
        for name in proofCandidates do
          if let some evidence ← theoremCorrespondence? levels ref impl domain required name then
            return (.checked, some evidence)
        for (name, info) in env.constants.toList do
          let .thmInfo _ := info | continue
          let used := info.type.getUsedConstants
          if !used.contains reference || !used.contains replacement then continue
          if let some evidence ← theoremCorrespondence? levels ref impl domain required name then
            return (.checked, some evidence)
        let comparison ← try
            let proof ← Meta.mkLambdaFVars domain (← Meta.mkEqRefl lhs)
            pure <| match ← checkCorrespondenceProof levels required proof with
              | some detail => DefeqComparison.completed (some detail)
              | none => .incomplete
          catch _ => pure (.completed none)
        return comparison.classify
    catch _ =>
      return (.unresolved,
          some s!"cannot construct exact correspondence for {reference} and {replacement}")

/-- The pinned `CSimp.isConstantReplacement?` shape, indexed independently of
the final scoped attribute state. This conservative candidate set includes
proof-valued definitions, expired local registrations, and overwritten entries.
An equality candidate is not evidence that a compiler selected that edge. -/
private def simplificationCandidates (env : Environment) :
    NameMap (Array Lean.Compiler.CSimp.Entry) :=
  env.constants.fold (init := {}) fun candidates theoremName info => Id.run do
    let some (_, .const reference us, .const target vs) := info.type.eq?
      | return candidates
    let levels := Std.HashSet.ofList us
    if levels.size != us.length || !levels.all Level.isParam || us != vs then
      return candidates
    let entry : Lean.Compiler.CSimp.Entry := ⟨reference, target, theoremName⟩
    return candidates.insert reference ((candidates.find? reference).getD #[] |>.push entry)

/-- Remove sinks from the finite replacement-only graph. The remaining names
are precisely those that can reach a directed cycle. Ordinary body recursion
is not a replacement-only cycle and does not enter this graph. -/
private def cyclicReplacementPaths (edges : Array (Name × Name)) : Array Name := Id.run do
  let mut remaining := edges.foldl (fun names (source, target) =>
    let names := if names.contains source then names else names.push source
    if names.contains target then names else names.push target) #[]
  for _ in [:remaining.size] do
    remaining := remaining.filter fun source =>
      edges.any fun (left, right) => left == source && remaining.contains right
  return remaining

/-- Identify the uncompiled helper produced for an actual kernel inductive by
Lean's pinned `mkBRecOnFromRec`. Names come from the inductive/recursor records,
then must agree with the tagged parent's actual projection and helper body.
This does not waive execution coverage: the helper remains a root, and all
source, attribute, historical replacement and retained IR edges are inspected. -/
private def brecOnHelpers (env : Environment) (own : Array (Name × ConstantInfo)) :
    Array Name := Id.run do
  let mut helpers := #[]
  for (indName, info) in own do
    let .inductInfo ind := info | continue
    if !ind.isRec then continue
    let base := (Lean.mkRecName indName, Lean.mkBRecOnName indName)
    let nested := if ind.all.head? == some indName then
      (List.range ind.numNested).toArray.map fun i =>
        (base.1.appendIndexAfter (i + 1), base.2.appendIndexAfter (i + 1))
      else #[]
    for (recName, parent) in #[base] ++ nested do
      let some (.recInfo _) := env.find? recName | continue
      if !Lean.isBRecOnRecursor env parent then continue
      let some (.defnInfo parentInfo) := env.find? parent | continue
      let .proj ``PProd 0 argument := parentInfo.value.getLambdaBody.consumeMData | continue
      let some helper := argument.getAppFn.constName? | continue
      if helper != parent.str "go" then continue
      let some (.defnInfo helperInfo) := env.find? helper | continue
      if helperInfo.hints != .abbrev then continue
      if env.getModuleIdxFor? helper != env.getModuleIdxFor? indName then continue
      if env.getModuleIdxFor? parent != env.getModuleIdxFor? indName then continue
      if !helperInfo.value.getUsedConstants.contains recName then continue
      helpers := helpers.push helper
  return helpers

/-- The exact pinned compiler derivation, including initializer references and real
self edges. Absence of IR is distinct from an existing body with no dependencies.
The partial collector's existing trust boundary is unchanged. -/
private def compilerDependencies (env : Environment) (name : Name) : Option (Array Name) :=
  (Lean.IR.findEnvDecl env name).map fun compiled =>
    ((Lean.IR.CollectUsedDecls.collectDecl compiled env).run {}).snd.order

/-- Each payload is tied to both the captured environment and its exact key.
This cache is invocation-local operational state, never worker evidence. -/
private abbrev CompilerDependenciesCache (env : Environment) :=
  Std.DHashMap Name (fun name => { dependencies : Option (Array Name) //
    dependencies = compilerDependencies env name })

/-- A hit returns the stored witness without evaluating the collector. A miss
computes the same pure expression once, retains its reflexive witness, and inserts
it. The returned map is threaded through the invocation's reference. -/
private def compilerDependenciesLookup (env : Environment)
    (name : Name) (cache : CompilerDependenciesCache env) :
    { dependencies : Option (Array Name) // dependencies = compilerDependencies env name } ×
      CompilerDependenciesCache env :=
  match cache.get? name with
  | some dependencies => (dependencies, cache)
  | none =>
      let dependencies := compilerDependencies env name
      let checked := (⟨dependencies, rfl⟩ :
        { dependencies : Option (Array Name) // dependencies = compilerDependencies env name })
      (checked, cache.insert name checked)

/-- Output identity for every cache, covering both hit and miss. Substitution of
this equality preserves the existing consumer's ordered-array transition. -/
private theorem compilerDependenciesLookup_exact (env : Environment) (name : Name)
    (cache : CompilerDependenciesCache env) :
    (compilerDependenciesLookup env name cache).1.val = compilerDependencies env name :=
  (compilerDependenciesLookup env name cache).1.property

/-- Hits preserve the stored value and entire map. -/
private theorem compilerDependenciesLookup_hit (env : Environment) (name : Name)
    (cache : CompilerDependenciesCache env) (value)
    (hit : cache.get? name = some value) :
    compilerDependenciesLookup env name cache = (value, cache) := by
  simp [compilerDependenciesLookup, hit]

/-- Misses insert precisely the original derivation and its reflexive witness. -/
private theorem compilerDependenciesLookup_miss (env : Environment) (name : Name)
    (cache : CompilerDependenciesCache env) (miss : cache.get? name = none) :
    compilerDependenciesLookup env name cache =
      (⟨compilerDependencies env name, rfl⟩,
        cache.insert name ⟨compilerDependencies env name, rfl⟩) := by
  simp [compilerDependenciesLookup, miss]

/-- The queried key is present after either branch, with exactly the returned witness. -/
private theorem compilerDependenciesLookup_stored (env : Environment) (name : Name)
    (cache : CompilerDependenciesCache env) :
    (compilerDependenciesLookup env name cache).2.get? name =
      some (compilerDependenciesLookup env name cache).1 := by
  cases h : cache.get? name <;> simp [compilerDependenciesLookup, h]

/-- Lookup cannot alter another key's payload; DHashMap's lawful dependent
lookup supplies the key transport and collision handling. -/
private theorem compilerDependenciesLookup_frame (env : Environment) (name other : Name)
    (cache : CompilerDependenciesCache env) (different : name ≠ other) :
    (compilerDependenciesLookup env name cache).2.get? other = cache.get? other := by
  cases h : cache.get? name <;>
    simp [compilerDependenciesLookup, h, Std.DHashMap.get?_insert, different]

/-- Finite conservative execution closure: source values, retained compiler IR,
all supported equality candidates, and observed implementation choices.
Compiler metadata supplements source dependencies; neither alone retains all
earlier replacements after inlining. Equality candidates are not a claim that
the compiler selected them. Extern reference bodies remain boundary leaves. -/
private def executionWalk (env : Environment) (ownedModules : List Name)
    (toolchainModules : NameMap RegulaPolicy.ToolchainOrigin)
    (loadReplacementHistory : Name → IO (Except String (Array (Name × Name))))
    (candidates : NameMap (Array Lean.Compiler.CSimp.Entry))
    (proofCache : IO.Ref (Std.HashMap (Name × Name) (Correspondence × Option String)))
    (dependencyCache : IO.Ref (CompilerDependenciesCache env))
    (recursorHelpers : Array Name) (root : Name) : CommandElabM
    (Array Regula.Report.ExecutionBoundary ×
      Array String × Array (Name × Name) × RegulaPolicy.ExecutionClosure) := do
  let mut visited : Std.HashSet Name := {}
  let mut queue : Array (Name × Option Nat) := #[(root, none)]
  let mut visits : Array RegulaPolicy.ExecutionVisit := #[]
  let mut boundaries : Array Regula.Report.ExecutionBoundary := #[]
  let mut unresolved : Array String := #[]
  let mut replacementEdges : Array (Name × Name) := #[]
  let mut compilerEdges : Array (Name × Name) := #[]
  let mut logicalEdges : Array (Name × Name) := #[]
  let mut candidateEdges : Array (Name × Name) := #[]
  let mut historyEdges : Array (Name × Name) := #[]
  let mut currentReplacementEdges : Array (Name × Name) := #[]
  let mut activeSimplificationEdges : Array (Name × Name) := #[]
  let mut helperEdges : Array (Name × Name) := #[]
  let mut compiledNames : Std.HashSet Name := {}
  -- Logical recursor machinery may be installed without standalone IR;
  -- matcher/noConfusion/projection uses are handled directly by the compiler.
  -- These tags relax only this initial IR obligation, never root membership,
  -- body/boundary traversal, or the obligation for a retained compiler call.
  -- This conservative account does not attest independent compilation of
  -- every logical machinery root or authenticate its generation.
  if (Lean.Compiler.getImplementedBy? env root).isNone &&
      !Lean.Compiler.hasMacroInlineAttribute env root && !env.isProjectionFn root &&
      !((Lean.IR.findEnvDecl env root).isNone &&
        (Lean.isAuxRecursor env root || Lean.isNoConfusion env root ||
          Lean.Meta.isMatcherCore env root)) &&
      !(recursorHelpers.contains root && (Lean.IR.findEnvDecl env root).isNone) then
    compiledNames := compiledNames.insert root
  let moduleOf (name : Name) : Option Name :=
    (env.getModuleIdxFor? name).map fun idx => env.header.modules[(idx : Nat)]!.module
  let correspondence (reference target : Name) := do
    if let some result := (← liftIO proofCache.get)[(reference, target)]? then return result
    let proofs := ((candidates.find? reference).getD #[]).filterMap fun candidate =>
      if candidate.toDeclName == target then some candidate.thmName else none
    let result ← replacementCorrespondence env reference target proofs
    liftIO <| proofCache.modify (·.insert (reference, target) result)
    return result
  while !queue.isEmpty do
    let (name, parent) := queue.back!
    queue := queue.pop
    if visited.contains name then continue
    visited := visited.insert name
    let visitIndex := visits.size
    visits := visits.push { name, moduleName := moduleOf name, parent }
    -- Queued names are in the order of `canonicalNames`, so the visit order and each visit's
    -- parent are a function of the closure's edge sets: a reader of the result file's shared
    -- execution account derives them (`SharedExecution.walkLoop`) instead of reading them.
    let enqueue (names : Array Name) :=
      (RegulaPolicy.canonicalNames names).map (·, some visitIndex)
    -- Persisted compiler IR records replacements at the time each imported
    -- declaration was compiled, including scoped simplification and inlining.
    -- Keep source edges too: optimization may erase an unsafe/replacement step.
    let dependencies ← liftIO <| dependencyCache.modifyGet (compilerDependenciesLookup env name)
    if let some dependencies := dependencies.val then
      for dependency in dependencies do
        compilerEdges := compilerEdges.push (name, dependency)
        compiledNames := compiledNames.insert dependency
      queue := queue ++ enqueue dependencies
    let some info := env.find? name
    | if (Lean.IR.findEnvDecl env name).isNone then
        unresolved := unresolved.push s!"{name}: constant used by {root} is not in the environment"
      continue
    let some moduleName := moduleOf name
    | unresolved := unresolved.push s!"{name}: module attribution is unavailable"
      continue
    let owned := ownedModules.contains moduleName
    -- The admitted origin of the constant's module when it is the toolchain's own compiled
    -- `Init`, `Std` or `Lean` module. A trusted boundary of an ownable kind there belongs to
    -- the toolchain's trusted base; `implemented_by` and `extern` data can only be set in the
    -- declaring module, so the declaration's module decides who owns the boundary.
    let toolchain := toolchainModules.find? moduleName
    let entry (boundary : BoundaryKind) (correspondence : Correspondence)
        (replacement : Option Name) (evidence : Option String) :
        CommandElabM Regula.Report.ExecutionBoundary := do
      let account ← match RegulaPolicy.admitBoundaryEvidence boundary correspondence evidence
          (if boundary.toolchainOwnable && correspondence == .trusted then toolchain
            else none) with
        | .ok account => pure account
        | .error error => throwError "{error}"
      return {
        occurrence := boundaries.size
        name := name
        «module» := moduleName
        boundary := boundary
        account := account
        owned := owned
        replacement := replacement }
    if let some active := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
      replacementEdges := replacementEdges.push (name, active.toDeclName)
      activeSimplificationEdges := activeSimplificationEdges.push (name, active.toDeclName)
    for simplification in (candidates.find? name).getD #[] do
      let target := simplification.toDeclName
      candidateEdges := candidateEdges.push (name, target)
      let (correspondence, evidence) ← correspondence name target
      boundaries := boundaries.push <|
        (← entry .compilerSimplification correspondence (some target)
          (some
              s!"conservative constant-equality \
                candidate={simplification.thmName}; {evidence.getD ""}"))
    queue := queue ++ enqueue (((candidates.find? name).getD #[]).map (·.toDeclName))
    if Lean.isExtern env name then
      boundaries := boundaries.push <|
        (← entry (if toolchain.isSome then .nativeRuntime else .external) .trusted none none)
      continue
    if let some target := Lean.Compiler.getImplementedBy? env name then
      currentReplacementEdges := currentReplacementEdges.push (name, target)
      -- Which implementation a toolchain replacement runs is part of the toolchain's trusted
      -- base: it needs neither source history nor correspondence. Its current target is still
      -- followed, so every boundary it reaches is classified in its own module.
      if toolchain.isSome then
        replacementEdges := replacementEdges.push (name, target)
        boundaries := boundaries.push <|
          (← entry .runtimeReplacement .trusted (some target) none)
        queue := queue ++ enqueue #[target]
        continue
      let history ← liftIO <| loadReplacementHistory moduleName
      let (recorded, targets) ← match history with
        | .error error =>
            unresolved := unresolved.push s!"{name}: replacement history unavailable: {error}"
            pure (#[], #[target])
        | .ok edges =>
            let targets := edges.filterMap fun (reference, target) =>
              if reference == name then some target else none
            historyEdges := historyEdges ++ targets.map (name, ·)
            if !targets.contains target then
              unresolved :=
                  unresolved.push
                      s!"{name}: fresh replacement history omits current target {target}"
            pure (targets, if targets.contains target then targets else targets.push target)
      for target in targets do
        replacementEdges := replacementEdges.push (name, target)
        let (correspondence, evidence) ← correspondence name target
        boundaries := boundaries.push <|
          (← entry .runtimeReplacement correspondence (some target) evidence)
      -- The recorded targets, then the current one: the order of the closure's history edges
      -- and its current replacement edge.
      queue := queue ++ enqueue recorded ++ enqueue #[target]
      continue
    if info.isPartial then
      boundaries := boundaries.push <| (← entry .partialComputation .trusted none none)
      if let some value := info.value? then
        let dependencies := value.getUsedConstants
        logicalEdges := logicalEdges ++ dependencies.map (name, ·)
        queue := queue ++ enqueue dependencies
      continue
    if info.isUnsafe then
      -- A constant whose type is a proposition is a proof: the compiler erases it, so it never
      -- runs. `lcProof`, the placeholder for erased proofs in unsafe code, is such an axiom.
      if ← observing env name "proposition test" <| liftTermElabM <| Meta.isProp info.type then
        continue
      boundaries := boundaries.push <| (← entry .unsafeComputation .trusted none none)
      if let some value := info.value? then
        let dependencies := value.getUsedConstants
        logicalEdges := logicalEdges ++ dependencies.map (name, ·)
        queue := queue ++ enqueue dependencies
      continue
    match info with
    | .defnInfo _ =>
        if !(← observing env name "proposition test" <|
            liftTermElabM <| Meta.isProp info.type) then
          if let some value := info.value? then
            let dependencies := value.getUsedConstants
            logicalEdges := logicalEdges ++ dependencies.map (name, ·)
            queue := queue ++ enqueue dependencies
    | .opaqueInfo _ =>
        let recName := Lean.Compiler.mkUnsafeRecName name
        match env.find? recName with
        | some recInfo =>
            if recInfo.isPartial then
              boundaries := boundaries.push <|
                (← entry .partialComputation .trusted none (some recName.toString))
              helperEdges := helperEdges.push (name, recName)
              queue := queue ++ enqueue #[recName]
            else
              boundaries := boundaries.push <| (← entry .opaqueComputation .unresolved none
                (some s!"compiled helper {recName} is not partial"))
        | none =>
            boundaries := boundaries.push <|
              (← entry .opaqueComputation .checked none (some "kernel-checked-body"))
            if !(← observing env name "proposition test" <|
                liftTermElabM <| Meta.isProp info.type) then
              if let some value := info.value? (allowOpaque := true) then
                let dependencies := value.getUsedConstants
                logicalEdges := logicalEdges ++ dependencies.map (name, ·)
                queue := queue ++ enqueue dependencies
    | .axiomInfo _ =>
        if RegulaPolicy.compilerTrustingAxiomName name then
          boundaries := boundaries.push <| (← entry .compilerTrustedProof .trusted none none)
    | .thmInfo _ | .ctorInfo _ | .inductInfo _ | .recInfo _ | .quotInfo _ => pure ()
  let cycles := cyclicReplacementPaths replacementEdges
  if !cycles.isEmpty then
    unresolved := unresolved.push s!"replacement-only cycle reachable from {cycles}"
  let mut unavailableCode : Array Name := #[]
  for name in compiledNames do
    match Lean.IR.findEnvDecl env name with
    | some (.fdecl ..) => pure ()
    | some (.extern ..) =>
        if !Lean.isExtern env name then
          unavailableCode := unavailableCode.push name
          unresolved := unresolved.push s!"{name}: compiler body is an opaque export placeholder"
    | none =>
        unavailableCode := unavailableCode.push name
        unresolved := unresolved.push s!"{name}: compiled dependency body is unavailable"
  boundaries := boundaries.mapIdx fun occurrence boundary =>
    { boundary with occurrence, compilerCallers := compilerEdges.filterMap fun (caller, callee) =>
        if callee == boundary.name then some caller else none }
  let closure : RegulaPolicy.ExecutionClosure := {
    nodes := RegulaPolicy.canonicalNames visited.toArray
    visits
    logicalEdges := RegulaPolicy.canonicalEdges logicalEdges
    candidateEdges := RegulaPolicy.canonicalEdges candidateEdges
    historyEdges := RegulaPolicy.canonicalEdges historyEdges
    currentReplacementEdges := RegulaPolicy.canonicalEdges currentReplacementEdges
    activeSimplificationEdges := RegulaPolicy.canonicalEdges activeSimplificationEdges
    helperEdges := RegulaPolicy.canonicalEdges helperEdges
    requiredCode := RegulaPolicy.canonicalNames compiledNames.toArray
    unavailableCode := RegulaPolicy.canonicalNames unavailableCode
  }
  return (boundaries, unresolved, RegulaPolicy.canonicalEdges compilerEdges, closure)

/-- Owned executable roots: computable, non-proposition, safe, non-partial,
non-internal definitions and opaque constants whose result is not a `Sort`
(types are erased before execution, like propositions). Role metadata never
removes an otherwise eligible root, including unused tagged declarations. -/
private def executableRoots (env : Environment) (own : Array (Name × ConstantInfo)) :
    CommandElabM (Array Name) := do
  let mut roots : Array Name := #[]
  for (name, info) in own do
    match info with
    | .defnInfo _ | .opaqueInfo _ =>
        if name.isInternal || info.isUnsafe || info.isPartial
            || Lean.isNoncomputable env name then continue
        let eligible ← observing env name "executable-root classification" do
          if ← liftTermElabM <| Meta.isProp info.type then return false
          return !(← liftTermElabM <| Regula.Collect.returnsSort info.type)
        if !eligible then continue
        roots := roots.push name
    | _ => continue
  return roots

/-- Build the complete report for exact requested module names. The trusted
runner calls this function directly, without parsing a command in the audited
module's frontend extension environment. -/
def environmentReport (modules : List Name)
    (loadReplacementHistory : Name → IO (Except String (Array (Name × Name))) :=
      fun _ => pure (.error "trusted source-history loader was not supplied"))
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    CommandElabM Regula.Report.Collected := do
  if modules.isEmpty then
    throwError "environmentReport: no owned module names were supplied"
  unless RegulaPolicy.Compiler.accepts Lean.versionString Lean.githash do
    throwError "unsupported compiler identity {Lean.versionString} ({Lean.githash})"
  let env ← getEnv
  -- Execution trust checks always need canonical origins. Logical-only
  -- documentation inspection may omit this otherwise unused report payload.
  let moduleOrigins ← if includeExecution || includeModuleOrigins then
      liftIO <| loadedModuleOrigins env
    else pure #[]
  let own ← ownedDecls env modules
  let declarationKeys ← own.mapM fun (name, _) => do
    let some idx := env.getModuleIdxFor? name
      | throwError "declaration census has no owner for {name}"
    return (env.header.modules[(idx : Nat)]!.module, name)
  let scope ← Regula.Collect.ContractScope.new env
  let entries ← own.mapM fun (name, _) =>
    observing env name "declaration record" (Regula.Collect.declaration name .replayCandidate scope)
  let roots ← if includeExecution then do
    let mut roots ← executableRoots env own
    for entry in entries do
      if let some contract := entry.executableContract then
        if contract.failure.isNone && !roots.contains contract.root then
          roots := roots.push contract.root
    roots.mapM fun root => do
      let some idx := env.getModuleIdxFor? root
        | throwError "executable root census has no owner for {root}"
      return (env.header.modules[(idx : Nat)]!.module, root)
    else pure #[]
  -- Documentation consumes only `declarations`; avoid constructing unused
  -- execution graphs. The full gate and all other callers retain them.
  let historyRequests ← liftIO <| IO.mkRef (#[] : Array (Name × Name))
  let execution ← if includeExecution then do
    -- Names alone do not establish toolchain ownership: an adopter or dependency
    -- can supply Init.*, Std.* or Lean.* modules. Resolve each candidate once, and require
    -- the exact canonical artifact path in the pinned toolchain's library directory.
    -- Missing origin evidence leaves the module's boundaries owned by the project or a
    -- dependency rather than granting a toolchain exemption.
    let toolchainLib ← liftIO <| Lean.getLibDir (← Lean.findSysroot)
    let mut toolchainModules : NameMap RegulaPolicy.ToolchainOrigin := {}
    for (moduleName, origin) in env.header.moduleNames.zip moduleOrigins do
      if RegulaPolicy.ToolchainRoot moduleName.getRoot then
        let actual ← liftIO <| IO.FS.realPath origin.olean
        let expected := Lean.modToFilePath toolchainLib moduleName "olean"
        if ← liftIO expected.pathExists then
          if actual == (← liftIO <| IO.FS.realPath expected) then
            let receipt ← match RegulaPolicy.admitToolchainOrigin moduleName actual.toString
                (← liftIO <| IO.FS.realPath expected).toString with
              | .ok receipt => pure receipt
              | .error error => throwError "{error}"
            toolchainModules := toolchainModules.insert origin.name receipt
    let recursorHelpers := brecOnHelpers env own
    let candidates := simplificationCandidates env
    let proofCache ← liftIO <| IO.mkRef
        ({} : Std.HashMap (Name × Name) (Correspondence × Option String))
    let dependencyCache ← liftIO <| IO.mkRef ({} : CompilerDependenciesCache env)
    roots.mapM fun (moduleName, root) => do
      let (boundaries, unresolved, compilerEdges, closure) ←
        observing env root "execution walk" <|
          executionWalk env modules toolchainModules (fun name => do
            historyRequests.modify fun requests =>
              if requests.contains (root, name) then requests else requests.push (root, name)
            loadReplacementHistory name) candidates proofCache dependencyCache recursorHelpers root
      return ({
        name := root
        «module» := moduleName
        boundaries, unresolved, compilerEdges, closure } :
        Regula.Report.ExecutionRoot)
    else pure #[]
  return {
    toolchain := Lean.versionString
    modules := RegulaPolicy.canonicalNames env.header.moduleNames
    moduleOrigins
    declarations := entries
    execution
    census := { modules := modules.toArray, declarations := declarationKeys
                executionRoots := if includeExecution then some roots else none
                historyRequests := ← liftIO historyRequests.get }
  }

/-- `audit_dump_json`: compatibility command for direct interactive use. The
Lean-native checker calls `environmentReport` directly. -/
elab (name := auditDumpJsonCmd) "audit_dump_json" : command => do
  let some pathStr := ← liftIO (IO.getEnv "AUDIT_DUMP_PATH")
    | throwError "audit_dump_json: AUDIT_DUMP_PATH is not set"
  let some modulesRaw := ← liftIO (IO.getEnv "AUDIT_OWN_MODULES")
    | throwError "audit_dump_json: AUDIT_OWN_MODULES is not set"
  let modules := (modulesRaw.split (· == ',')).toList
    |>.filterMap fun t =>
      let t := t.trimAscii.toString
      if t.isEmpty then none else some t.toName
  let report ← environmentReport modules
  liftIO <| IO.FS.writeFile (System.FilePath.mk pathStr) (Json.pretty (toJson report.toEnvironment))

end Regula.Probe
