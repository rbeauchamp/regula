import Std.Data.DHashMap.Lemmas
import Regula.Collect
import Regula.StructuralName
import Lean.Elab.Command
import Lean.Compiler.Old
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.InitAttr
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
import Regula.Report
import Regula.Contract
import Regula.MaterialClaim
import Regula.Decision
import Regula.Assumption
import RegulaPolicy.ExecutionWalk

/-!
# Machine-audit environment probe

Machine-audit support consumed directly by the repository's Lean checker
executables.

The trusted runner calls `environmentReport` on a Lean-imported elaborated
environment — never on source text. For every declaration whose exact
module index is requested, the report records:

- the declaration's module and constant kind (axiom, theorem, def, opaque,
  constructor, inductive, recursor, quotient);
- the elaborated type, as the `repr` of its kernel expression (`type`) and as Lean prints it
  (`prettyType`), whether that type is a proposition, and
  `ConstantInfo.isUnsafe` / `ConstantInfo.isPartial` for every constant kind;
- instance / `noncomputable` / `@[implemented_by]` / `@[extern]` flags;
- the exact transitive axiom set: the axioms the declaration reaches in the kernel that replayed
  it (`Admission.validate`, `KernelAxioms.axiomTable`), or, for a caller with no replayed kernel,
  those it reaches in the environment that holds it (`KernelAxioms.reachedAxioms`); and
- Lean-native reporting metadata (internal/private spelling, projection,
  matcher, recursor kind, unsafe-recursion relationship, and source range).

The report additionally carries an execution-coverage account, distinct from
the logical axiom audit: for every owned executable root (computable,
non-proposition, safe, non-partial, non-internal definitions and opaque
constants, each program entry point `main` with a compiled body, `unsafe` or not, and the
action of each initializer that an owned module records) it computes the transitive
conservative closure over value-level dependencies, retained compiler IR,
constant-equality simplification candidates, historical `@[implemented_by]`
targets, and partial helpers. `@[extern]` constants are boundary leaves for
their Lean bodies. The report distinguishes possible replacements from actual
retained compiler edges and records every boundary in this closure:
compiler simplifications, `@[implemented_by]` replacements, `@[extern]` declarations split into
toolchain native-runtime primitives and other external code, unsafe/partial/opaque
computation, compiler-trusting proof axioms, and initialized values. A replacement, `extern`,
unsafe or partial computation, or initialized value declared in an origin-checked `Init`, `Std`,
`Lean`, `Lake` or `LeanExport` module carries that module's toolchain origin: it is the
toolchain's trusted base, and a toolchain replacement is followed through its current target
without source history or correspondence. A module's origin is checked by the file where Lean's
search path finds it after the import, under the hypotheses of `loadedModuleOrigins`. An unsafe
constant whose type Lean's `Meta.isProp` finds to be a proposition, such as `lcProof`, is a proof
the compiler erases and is no boundary. Each
boundary is marked `checked` (kernel-definitional equality, a standard-logical
correspondence theorem of a module that the audit replays or of the toolchain, or a
kernel-checked opaque body), `trusted`, or
`unresolved`; unresolved paths are listed per root. Imported boundary
declarations are reported by this account without becoming owned.

Generated-role metadata is descriptive, not provenance. A recursion helper requires
regeneration by the pinned recursion compiler and the kernel's check of its base's
recursion equation; no unsafe constructor-index wrapper is admitted. A native-proof axiom requires
native replay and, for one of an owned module, fresh exact-source frontend provenance. Names,
ranges, and extension tags alone never waive a rule. Every declaration is still emitted and checked.

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
open RegulaPolicy (DeclarationKind BoundaryKind Correspondence CorrespondenceTerms DefeqComparison
  KernelAnswer Safety Reducibility RecursionOrigin)

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
header order. The path is the file where Lean's search path finds the module now
(`Lean.findOLean`), not a record of the file that Lean read, which Lean 4.35.0 keeps nowhere in the
environment.

Assumes:
- `env` was imported in this process by `importModules` with no artifacts supplied, as
  `Regula.Checker.Environment.importReportEnvironment` imports the environment of each caller.
  Lean then read each module from the file that `Lean.findOLean` gave at the import
  (`loadData`, `Lean/Environment.lean:2232-2239`, and `readModuleDataPartsOfMod`, `:2079-2083`).
- Between the import and this lookup, nothing changed that the lookup reads: the search path, and
  in each of its directories the directory or `.olean` file of the module's root, the module's
  `.olean` and the symbolic links on their paths. `Lean.SearchPath.findWithExt` reads the
  filesystem anew at each call (`Lean/Util/Path.lean:61-65`), so a file made in an earlier
  directory after the import would be reported in place of the one that Lean read. So the path is
  that file's.

Every origin that a caller derives from this path rests on these hypotheses: the toolchain origin
of a module (`RegulaPolicy.ToolchainOrigin`), the origin of an infrastructure module
(`Regula.Checker.Environment.infrastructureOrigins`) and the package that a loaded module is
attributed to (`Regula.Checker.Environment.ModuleGraph`). -/
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
replaces Lean's advice to raise it in the source. The observation runs with smart unfolding off
(`Collect.withoutSmartUnfolding`), so no answer rests on a declaration found by the name
`_sunfold`. -/
private def observing {α : Type} (env : Environment) (name : Name) (observation : String)
    (act : CommandElabM α) : CommandElabM α := do
  try Regula.Collect.withoutSmartUnfolding act
  catch ex =>
    let owner := match Regula.Collect.moduleOf env name with
      | .ok moduleName => m!"{moduleName}"
      | .error _ => m!"<unattributed>"
    if let some limit := (← Regula.Collect.checkerLimit? ex) then
      throwError "module {owner}, declaration {name}: {observation} reached the Regula checker's \
        own resource limit ({limit}); options set in the source, such as `maxRecDepth`, do not \
        apply to the checker. Report this as a Regula issue."
    throwError "module {owner}, declaration {name}: {observation} failed: {ex.toMessageData}"

/-- Emit flushed timing spans inside the trusted command observation when requested by the
runner. Elapsed times describe the run, not the collected declarations or execution account. -/
private def reportPhase {α : Type} (enabled : Bool) (label : String)
    (action : CommandElabM α) : CommandElabM α := do
  if !enabled then return ← action
  let label := s!"worker {← IO.Process.getPID} {label}"
  IO.println s!"verification phase {label}: start"
  (← IO.getStdout).flush
  let started ← IO.monoNanosNow
  try action finally
    IO.println s!"verification phase {label}: {((← IO.monoNanosNow) - started) / 1000000}ms (finished)"
    (← IO.getStdout).flush

/-- Kernel heartbeat budget for one correspondence check: Lean's per-declaration default
(`maxHeartbeats` at its default value, in the kernel's raw unit), so a checker-added
correspondence obligation costs no more than a declaration the adopter could write. The kernel
counts it over all kernel admissions of one check (`runCheck`). -/
private def correspondenceHeartbeats : USize := (Core.getMaxHeartbeats {}).toUSize

/-- The options of every correspondence check: Lean's defaults with smart unfolding off, as in the
walk (`Collect.withoutSmartUnfolding`), so no answer rests on a declaration found by the name
`_sunfold`. They are the same for every check, so the elaborator's heartbeat budget
(`maxHeartbeats`) and recursion limit (`maxRecDepth`) are its defaults. -/
private def checkOptions : Options := Meta.smartUnfolding.set {} false

/-- Kernel resource exhaustion ends admission without a verdict on the proof. -/
private def kernelExhausted : Kernel.Exception → Bool
  | .deterministicTimeout | .excessiveMemory | .deepRecursion | .interrupted => true
  | _ => false

/-- The kernel's answer to the constructed closed proof, checked against the required proposition
in a disposable kernel declaration (`RegulaPolicy.KernelAnswer`). Neither
metavariable unification nor a matching theorem statement alone authorizes `checked`. Only the
kernel's result selects the answer: its admission, with the declaration's transitive axioms and
the proof and proposition the kernel checked, each as its exact term (`Collect.exactTerm`) beside
its display, printed with `pp.all` requested: explicit settings of the caller can still hide
implicit arguments and universe levels, and Lean's printer can abbreviate, so only the exact term
is complete; the axioms are those the declaration reaches in the kernel
environment that holds it (`KernelAxioms.axiomsWith`), the search stopping at each name of
`cached`, the table admission computed in the replayed kernel for the owned declarations' closure,
and an exhausted search is the kernel's exhaustion; its resource exhaustion or interruption
(`kernelExhausted`); or any other refusal. A runtime memory limit that ends the admission
(`excessiveMemory`) also sets `memoryExhausted`, so the check gives no verdict
(`publishCheck`). A proof or proposition with an undischarged variable, and an error while the
answer is read, raise an error and record no answer. -/
private def kernelAnswer (cached : Std.HashMap Name (Array Name)) (memoryExhausted : IO.Ref Bool)
    (levels : List Name) (required proof : Expr) : MetaM KernelAnswer := do
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
  match ← IO.lazyPure fun _ => env.addDeclCore correspondenceHeartbeats 1000 declaration none with
  | .error e =>
    if e matches .excessiveMemory then memoryExhausted.set true
    return if kernelExhausted e then .exhausted else .refused
  | .ok checked =>
    let some axioms := RegulaPolicy.KernelAxioms.axiomsWith checked.toKernelEnv.find? cached
        (RegulaPolicy.KernelAxioms.fuelFor checked 1) name | return .exhausted
    withOptions (fun opts => opts.setBool `pp.all true |>.setBool `pp.deepTerms true
        |>.set `pp.maxSteps (1000000 : Nat)) do
      return .admitted axioms
        { proof := ← Regula.Collect.shownTerm proof
          required := ← Regula.Collect.shownTerm required }

/-- The comparison that one attempt at the kernel's answer records
(`RegulaPolicy.DefeqComparison.ofAttempt`). `observing` keeps an error that the attempt raises as
its result, so an attempt that raised an error records no answer and its comparison is
incomplete, whatever the error (`DefeqComparison.ofAttempt_error`). Lean's Core-based monads
rethrow a runtime resource exception (heartbeats, recursion depth) or an interruption instead of
catching it, so such an exception records no comparison and ends the check (`runCheck`). -/
private def comparison (attempt : MetaM KernelAnswer) : MetaM DefeqComparison := do
  let attempt ← match ← _root_.observing attempt with
    | .ok answer => pure (.ok answer)
    | .error error => pure (.error (← error.toMessageData.toString))
  return DefeqComparison.ofAttempt attempt

/-- A theorem mentioning both endpoints is only a search candidate. For every
prefix of the actual dependent domain, instantiate its universes and premises,
match the equality, apply any remaining arguments by congruence, and close over
exactly the actual domain. Unsolved theorem-only premises remain metavariables
and cannot pass kernel admission. Search incompleteness never grants evidence. -/
private def theoremCorrespondence? (cached : Std.HashMap Name (Array Name))
    (memoryExhausted : IO.Ref Bool) (levels : List Name)
    (reference replacement : Expr) (domain : Array Expr) (required : Expr) (name : Name) :
    MetaM (Option (String × CorrespondenceTerms)) := do
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
          let .completed (some terms) ←
              comparison (kernelAnswer cached memoryExhausted levels required proof)
            | return none
          return some (s!"proved: {name}; {terms.text}", terms)
        catch _ => return none
      if result.isSome then return result
  return none

/-- The exact theorem entries of a captured constant list, in its original order: each theorem
with the constants its type uses. The walk builds it once for an environment, before the first
correspondence check (`observeNode`), so no check pays for it. -/
private def theoremDependencies (constants : List (Name × ConstantInfo)) :
    List (Name × Array Name) :=
  constants.filterMap fun (name, info) =>
    match info with
    | .thmInfo _ => some (name, info.type.getUsedConstants)
    | _ => none

/-- A theorem enters fallback search exactly when its type mentions both endpoints. -/
private def correspondenceCandidate (reference replacement : Name)
    (entry : Name × Array Name) : Option Name :=
  if !entry.2.contains reference || !entry.2.contains replacement then none else some entry.1

/-- Require `∀ xs, reference.{us} xs = replacement.{us} xs`, where `us`
are rigid universal level parameters and `xs` is the complete elaborated
reference domain, including implicit, dependent, and proof parameters. The
compiler's positional universe substitution must type-check at those same
levels. Both definitional and theorem-backed evidence pass the same kernel gate.
Theorem candidates, supplied then discovered in `theorems` (`theoremDependencies` of the
environment), are tried before definitional unfolding. A theorem is
tried only when `admits` accepts it, which `environmentReport`
gives for a theorem of a module that the environment's admission replayed or reused, or of an
origin-checked module of the toolchain: the kernel then checked the theorem itself in this audit,
or it is part of the toolchain's trusted base. A theorem of a dependency that the audit does not
own is never tried, since only that dependency's build vouches for it. The definitional fallback
returns
`DefeqComparison.classify` of the comparison its attempt records (`comparison`): the kernel's
answer completes it, and an attempt the kernel did not decide, or one that raised an error while
it built the reflexivity proof or read the answer, is unresolved, never trusted (standard §7.6).
An elaborator resource limit reached while constructing the correspondence is rethrown rather
than recorded as unresolved. -/
private def replacementCorrespondence (cached : Std.HashMap Name (Array Name))
    (theorems : List (Name × Array Name)) (admits : Name → Bool) (memoryExhausted : IO.Ref Bool)
    (reference replacement : Name) (proofCandidates : Array Name) :
    MetaM (Correspondence × Option String × Option CorrespondenceTerms) :=
  Meta.withoutModifyingMCtx do
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
          if !admits name then continue
          let evidence? ←
            theoremCorrespondence? cached memoryExhausted levels ref impl domain required name
          if let some (evidence, terms) := evidence? then
            return (.checked, some evidence, some terms)
        for entry in theorems do
          let some name := correspondenceCandidate reference replacement entry | continue
          if !admits name then continue
          let evidence? ←
            theoremCorrespondence? cached memoryExhausted levels ref impl domain required name
          if let some (evidence, terms) := evidence? then
            return (.checked, some evidence, some terms)
        let outcome ← comparison do
          kernelAnswer cached memoryExhausted levels required
            (← Meta.mkLambdaFVars domain (← Meta.mkEqRefl lhs))
        return (outcome.classify.1, outcome.classify.2, outcome.terms?)
    catch _ =>
      return (.unresolved,
          some s!"cannot construct exact correspondence for {reference} and {replacement}", none)

/-- The verdict of one correspondence check: whether it is checked, trusted or unresolved, its
evidence text and the terms the kernel checked. -/
abbrev CheckVerdict := Correspondence × Option String × Option CorrespondenceTerms

/-- What the task of one correspondence check returns (`runCheck`): the thread it ran on, whether
a runtime memory limit ended one of its kernel admissions, and the check's own result, or the
message of the elaborator resource limit that ended it. -/
structure CheckRun where
  /-- The identifier of the thread the check ran on. -/
  thread : UInt64
  /-- Whether a runtime memory limit ended a kernel admission of the check. -/
  memoryExhausted : Bool
  /-- The check's result, or the message of the elaborator limit that ended it. -/
  result : Except String CheckVerdict

/-- The verdict of a check's own result: the result itself, or, when an elaborator resource limit
(heartbeats or recursion depth) ended the check, `unresolved` with that limit's message. It reads
the result alone. -/
def checkVerdict : Except String CheckVerdict → CheckVerdict
  | .ok verdict => verdict
  | .error message => (.unresolved, some s!"the check reached an elaborator limit: {message}", none)

/-- The verdict the walk publishes for a check of `reference` and `replacement` that ran as `run`,
from a caller on thread `caller`: no verdict, and the error that ends the report, when the check
ran on the caller's thread or a runtime memory limit ended one of its kernel admissions; otherwise
`checkVerdict` of its own result (`publishCheck_ok_iff`, `publishCheck_error_iff`). -/
def publishCheck (caller : UInt64) (reference replacement : Name) (run : CheckRun) :
    Except String CheckVerdict :=
  if run.thread = caller then
    .error s!"the correspondence check of {reference} and {replacement} ran on the report's \
      thread, so its heartbeat count did not start at zero: Lean has no task manager"
  else if run.memoryExhausted then
    .error s!"a runtime memory limit ended a kernel admission of the correspondence check of \
      {reference} and {replacement}"
  else .ok (checkVerdict run.result)

/-- The walk publishes a verdict exactly when the check ran on a thread of its own and no runtime
memory limit ended one of its kernel admissions, and the verdict is then the one its own result
gives. -/
theorem publishCheck_ok_iff (caller : UInt64) (reference replacement : Name) (run : CheckRun)
    (verdict : CheckVerdict) :
    publishCheck caller reference replacement run = .ok verdict ↔
      run.thread ≠ caller ∧ run.memoryExhausted = false ∧ verdict = checkVerdict run.result := by
  unfold publishCheck
  by_cases thread : run.thread = caller <;> cases exhausted : run.memoryExhausted <;>
    simp [thread, eq_comm]

/-- The walk publishes no verdict exactly when the check ran on the caller's thread or a runtime
memory limit ended one of its kernel admissions. -/
theorem publishCheck_error_iff (caller : UInt64) (reference replacement : Name) (run : CheckRun) :
    (∃ message, publishCheck caller reference replacement run = .error message) ↔
      run.thread = caller ∨ run.memoryExhausted = true := by
  unfold publishCheck
  by_cases thread : run.thread = caller <;> cases exhausted : run.memoryExhausted <;>
    simp [thread]

/-- Run one correspondence check of `reference` and `replacement`, with the supplied theorems
`proofs` tried first, on a task of its own (`Task.Priority.dedicated`), and return what it gives
(`CheckRun`). Its inputs are the environment and the report's data about it (`cached`, `theorems`
and `admits`), the check itself, and the fixed options and heartbeat budgets (`checkOptions`,
`correspondenceHeartbeats`): the task starts its own Core and Meta states on `env`, and no state of
an earlier check reaches it. An elaborator resource limit that ends the check is its result's
error message (`checkVerdict`).

Assumes: Lean 4.35.0 counts the kernel's heartbeats in a counter of the thread, one at each system
check, and ends an admission when the count exceeds the budget (`check_heartbeat`,
`src/runtime/interrupt.cpp:18`, `51-55`); `addDeclCore` sets the budget and not the count
(`lean_add_decl`, `src/kernel/environment.cpp:287-295`); a task of priority above
`LEAN_MAX_PRIO` runs on a new thread, which sets that count to zero before it runs the task
(`enqueue`, `spawn_dedicated_worker` and `run_task`, `src/runtime/object.cpp:792-794`,
`868-887`); without a task manager, Lean runs a task on the caller's thread
(`lean_task_spawn_core`, `src/runtime/object.cpp:1184-1190`), which `publishCheck` refuses; the
elaborator's heartbeats are counted from the value at the start of the check (`CoreM.toIO`,
`src/Lean/CoreM.lean:454-463`); and elaboration and kernel admission, under fixed options, are
functions of the environment and the check. Trusted: the operating system's scheduling and memory;
a process that runs out of memory ends, and the run's deadline ends a check that runs too long. -/
def runCheck (env : Environment) (cached : Std.HashMap Name (Array Name))
    (theorems : List (Name × Array Name)) (admits : Name → Bool)
    (reference replacement : Name) (proofs : Array Name) : IO CheckRun := do
  let task ← IO.asTask (prio := .dedicated) do
    let thread ← IO.getTID
    let memoryExhausted ← IO.mkRef false
    let context : Core.Context := {
      fileName := "<correspondence>"
      fileMap := default
      options := checkOptions
      maxRecDepth := maxRecDepth.get checkOptions }
    let result ← try
        let (verdict, _, _) ← (replacementCorrespondence cached theorems admits memoryExhausted
          reference replacement proofs).toIO context { env }
        pure (.ok verdict)
      catch error => pure (.error error.toString)
    return { thread, memoryExhausted := ← memoryExhausted.get, result : CheckRun }
  IO.ofExcept (← IO.wait task)

/-- The reason that `taskManagerMissing` gives for a process without Lean's task manager. -/
def taskManagerMissingReason : String :=
  "Lean's task manager is not running in this process: a task of priority \
    `Task.Priority.dedicated` ran on the thread that started it (Lean starts none when \
    LEAN_NUM_THREADS is 0)"

/-- Why this process has no Lean task manager, or `none` when it has one. It runs one task of
priority `Task.Priority.dedicated` and compares the thread the task ran on with the thread of the
caller: the same thread means that Lean has no task manager. It observes Lean's own scheduling of a
task, not the value of `LEAN_NUM_THREADS`, and it needs no task manager itself. The check of a
report (`requireDedicatedThreads`) and the guard of each program of the package
(`Regula.TaskManager.guard`) use it. The observation of the process is a trusted boundary, and
nothing here proves it.

Assumes: Lean 4.35.0 gives `Task.Priority.dedicated` the value 9 (`src/Init/Core.lean:677`), above
`LEAN_MAX_PRIO`, 8, and below `LEAN_SYNC_PRIO`, the largest `unsigned`
(`src/runtime/object.cpp:71-72`); the task manager runs a task of such a priority on a new thread
that it starts for that task (`enqueue_core` and `spawn_dedicated_worker`,
`src/runtime/object.cpp:792-795` and `868-877`), while `LEAN_SYNC_PRIO` would run it on the
caller's thread (`788-791`). Without a task manager, Lean runs the task on the caller's thread
before it returns (`lean_task_spawn_core`, `src/runtime/object.cpp:1184-1190`), which `IO.asTask`
calls (`lean_io_as_task`, `src/runtime/io.cpp:1551-1554`). Assumes: two threads that run at once
have different identifiers (`lean_io_get_tid`, `src/runtime/process.cpp:340-352`,
`pthread_threadid_np` on macOS and `gettid` on Linux); the caller's thread runs until the task has
ended, because it waits for it. -/
def taskManagerMissing : IO (Option String) := do
  let caller ← IO.getTID
  let thread ← IO.ofExcept (← IO.wait (← IO.asTask (prio := .dedicated) IO.getTID))
  return if thread == caller then some taskManagerMissingReason else none

/-- Refuse, before any correspondence check, a process in which a task of priority
`Task.Priority.dedicated` runs on the caller's thread (`taskManagerMissing`): Lean
then has no task manager, and a check's heartbeat count would not start at zero (`runCheck`). The
report then ends with this error. A program that starts through `Regula.TaskManager.guard` is
refused before it reaches a report, so this refusal holds for a report that another program runs. -/
def requireDedicatedThreads : IO Unit := do
  if let some reason ← taskManagerMissing then
    throw <| IO.userError s!"{reason}, so no correspondence check can count its heartbeats from \
      zero"

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

/-- Every `@[export]` entry of `env`, a declaration with its export name: the entries of each
imported module, then those of the current one.

Assumes: Lean 4.35.0 stores the `@[export]` name of a declaration of an imported module among the
entries of that module, and of a declaration of the current module in the attribute's state
(`getParamFromExt?`, `src/Lean/Attributes.lean:306-318`). -/
private def exportEntries (env : Environment) : List (Name × Name) :=
  ((List.range env.header.moduleNames.size).flatMap fun idx =>
      (Lean.exportAttr.ext.getModuleEntries env idx).toList) ++
    (Lean.exportAttr.ext.getState env).2.toList

/-- The declarations among `entries` whose export name is the C symbol `symbol`, each once: the
export name `.str .anonymous s` is the C name `s`, and Lean refuses to emit code for any other
export name (`toCName`, `src/Lean/Compiler/LCNF/EmitC.lean:244-250`). The match reads the
attribute names alone: it does not decide which body, if any, runs under that symbol
(`mem_exportersOf_iff`). -/
def exportersOf (entries : List (Name × Name)) (symbol : String) : List Name :=
  (entries.filterMap fun (declaration, exportName) =>
    if exportName == .str .anonymous symbol then some declaration else none).eraseDups

/-- A declaration is listed exactly when one of the entries gives it the export name of the
symbol. -/
theorem mem_exportersOf_iff (entries : List (Name × Name)) (symbol : String) (declaration : Name) :
    declaration ∈ exportersOf entries symbol ↔
      (declaration, Name.str .anonymous symbol) ∈ entries := by
  simp only [exportersOf, List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨⟨found, exportName⟩, member, matched⟩
    by_cases same : exportName = .str .anonymous symbol
    · simp only [same, beq_self_eq_true, ite_true, Option.some.injEq] at matched
      exact matched ▸ same ▸ member
    · simp [same] at matched
  · intro member
    exact ⟨_, member, by simp⟩

/-- What the compiler runs for a constant, as the walk classifies it before its value: external
code (`extern`), the value an initializer returned (`initialized`), or neither (`ordinary`). -/
inductive Lowering where
  /-- An `extern`. -/
  | extern
  /-- A constant whose compiled code reads the value initializer `action` returned. -/
  | initialized (action : Name)
  /-- Neither. -/
  | ordinary
  deriving DecidableEq

/-- The classification of a constant from what Lean records of it: whether it is an `extern`
(`isExtern`), whether it has an `implemented_by` target (`implemented`), whether Lean holds
compiled IR for it (`compiled`), and its initializer (`initializer`). A constant with an
initializer is an initialized value unless it has an `implemented_by` target and no IR: Lean
generated no code for it, so no initializer of it runs, and every call of it calls the target. A
constant with an initializer, a target and IR, whose target was added after it was compiled, is
an initialized value too, since a call compiled before the target was added, the target's own
included, still reads the initializer's value (`lowering_initialized_iff`). -/
def lowering (isExtern implemented compiled : Bool) (initializer : Option Name) : Lowering :=
  if isExtern then .extern
  else if implemented && !compiled then .ordinary
  else match initializer with
    | some action => .initialized action
    | none => .ordinary

/-- A constant is classified as an initialized value exactly when it is not an `extern`, has no
`implemented_by` target or has compiled IR, and Lean records an initializer for it. -/
theorem lowering_initialized_iff (isExtern implemented compiled : Bool)
    (initializer : Option Name) (action : Name) :
    lowering isExtern implemented compiled initializer = .initialized action ↔
      isExtern = false ∧ (implemented = false ∨ compiled = true) ∧
        initializer = some action := by
  unfold lowering
  cases isExtern <;> cases implemented <;> cases compiled <;> cases initializer <;> simp


/-- What a walk observes of one name `name`: the targets of the edges from the name, its
boundaries and unresolved paths, and its retained compiler body
(`RegulaPolicy.ExecutionWalk.NodeRecord`). It does not receive the walk's root, so the record is
the same for every root; the walk adds the one note that names its root, for a name with neither
a constant nor compiled code. The names that the walk queues after it are a
definition of the targets (`NodeRecord.successors`). The record reads source values, retained
compiler IR, all supported equality candidates, and observed implementation choices. Compiler
metadata supplements source dependencies; neither alone retains all earlier replacements after
inlining. Equality candidates are not a claim that the compiler selected them. Extern reference
bodies remain boundary leaves. Every `extern` is a trusted boundary. One of a project or
dependency names the declarations whose `@[export]` name is its C symbol (`exportersOf`), with no
claim that they run; that match adds no edge, and the extern's simplification candidates stay
edges, as for any constant. A constant with an `implemented_by` target is a runtime replacement,
an `extern` included, and a constant with an initializer is an initialized value unless it has
such a target and no compiled IR (`lowering`); one with an initializer, a target and IR is both.

An opaque constant gets a helper edge to the constant `Lean.Compiler.mkUnsafeRecName` names for it
when the environment has that constant and it is `partial`. The edge is how the policy pairs a
`partial def`, the project's or the toolchain's, with its helper
(`RegulaPolicy.ExecutionRoot.carries`); no name is parsed.

Assumes:
- Lean v4.35.0 compiles an opaque constant through the constant `mkUnsafeRecName` names for it,
  when the environment has one: the code generator looks that name up before the constant itself
  (`getDeclInfo?`, `src/lean/Lean/Compiler/LCNF/ToDecl.lean:25-27`; `declIsNotUnsafe`, lines
  29-38).
- Lean v4.35.0 elaborates a `partial def` by adding the opaque constant and then its helper under
  that name with `partial` definition safety, in one command (`addAndCompilePartial`,
  `src/lean/Lean/Elab/PreDefinition/Main.lean:20-36`; `addAndCompilePartialRec`,
  `src/lean/Lean/Elab/PreDefinition/Basic.lean:280-294`), so the two share a declaring module and
  so a toolchain origin.
- Lean 4.35.0 compiles a constant with an `extern` attribute from that attribute alone, and any
  other constant with an initializer (`getInitFnNameFor?`) to an extern declaration with no
  entries (`toDecl`, `src/Lean/Compiler/LCNF/ToDecl.lean:68-75`), which its IR replaces with a
  body that is `unreachable` (`lowerDecl`, `src/Lean/Compiler/IR/ToIR.lean:194-200`;
  `mkDummyExternDecl`, `src/Lean/Compiler/IR/Basic.lean:386-388`); the module's initialization
  sets the constant to the value its initializer returned (`emitDeclInit`,
  `src/Lean/Compiler/LCNF/EmitC.lean:986-1004`), and the initializer is a retained call of the
  constant's IR (`collectDecl`, `src/Lean/Compiler/IR/EmitUtil.lean:52-60`).
- Lean 4.35.0 generates code for every `extern`, and for no other constant that has an
  `implemented_by` target when it is compiled (`shouldGenerateCode`,
  `src/lean/Lean/Compiler/LCNF/Main.lean:34`, `:40`); a target added after the constant was
  compiled, as `attribute [implemented_by]` after `initialize` adds one, leaves its IR and
  initializer in place, and Lean's IR environment extension still holds that IR (`findEnvDecl`,
  `src/lean/Lean/Compiler/IR/CompilerM.lean:142`). The module's initialization runs the
  initializers of its IR declarations alone (`emitInitFn`,
  `src/lean/Lean/Compiler/LCNF/EmitC.lean:1047-1049`). Its simplifier replaces a call of any
  constant with an `implemented_by` target, an `extern` included, by a call of the target
  (`applyImplementedBy?`, `src/lean/Lean/Compiler/LCNF/Simp/SimpValue.lean:55-59`, enabled at
  `src/lean/Lean/Compiler/LCNF/Passes.lean:107`), so a call compiled after the target was added
  never reads the constant's value, and a call compiled before still does. -/
private def observeNode (env : Environment) (ownedModules : List Name)
    (toolchainModules : NameMap RegulaPolicy.ToolchainOrigin)
    (cached : Std.HashMap Name (Array Name))
    (loadReplacementHistory : Name → IO (Except String (Array (Name × Name))))
    (candidates : NameMap (Array Lean.Compiler.CSimp.Entry))
    (proofCache : IO.Ref
      (Std.HashMap (Name × Name) (Correspondence × Option String × Option CorrespondenceTerms)))
    (dependencyCache : IO.Ref (CompilerDependenciesCache env))
    (theorems : IO.Ref (Option (List (Name × Array Name)))) (admits : Name → Bool)
    (timing : Bool)
    (name : Name) : CommandElabM (RegulaPolicy.ExecutionWalk.NodeRecord name) := do
  let moduleOf (name : Name) : Option Name :=
    (env.getModuleIdxFor? name).map fun idx => env.header.modules[(idx : Nat)]!.module
  let correspondence (reference target : Name) := do
    if let some result := (← liftIO proofCache.get)[(reference, target)]? then return result
    let proofs := ((candidates.find? reference).getD #[]).filterMap fun candidate =>
      if candidate.toDeclName == target then some candidate.thmName else none
    -- The theorem index is built here, before the first check, so no check pays for it.
    let index ← match ← liftIO theorems.get with
      | some index => pure index
      | none => do
        let index ← IO.lazyPure fun _ => theoremDependencies env.constants.toList
        liftIO <| theorems.set (some index)
        pure index
    let caller ← IO.getTID
    let run ← reportPhase timing s!"correspondence {reference} -> {target}" <| liftIO <|
      runCheck env cached index admits reference target proofs
    -- A check that ran on this thread or met a runtime memory limit ends the report: no verdict.
    match publishCheck caller reference target run with
    | .ok result =>
      liftIO <| proofCache.modify (·.insert (reference, target) result)
      return result
    | .error message => throwError message
  let code : RegulaPolicy.ExecutionWalk.CodeStatus := match Lean.IR.findEnvDecl env name with
    | some (.fdecl ..) => .function
    | some (.extern ..) => if Lean.isExtern env name then .externBody else .placeholder
    | none => .missing
  let mut record : RegulaPolicy.ExecutionWalk.NodeRecord name :=
    { moduleName := moduleOf name, code }
  let note (record : RegulaPolicy.ExecutionWalk.NodeRecord name) (message : String) :
      RegulaPolicy.ExecutionWalk.NodeRecord name :=
    { record with unresolved := record.unresolved.push message }
  -- Persisted compiler IR records replacements at the time each imported
  -- declaration was compiled, including scoped simplification and inlining.
  -- Keep source edges too: optimization may erase an unsafe/replacement step.
  let dependencies ← liftIO <| dependencyCache.modifyGet (compilerDependenciesLookup env name)
  if let some dependencies := dependencies.val then
    record := { record with compilerDependencies := dependencies }
  -- A name with neither a constant nor compiled code gets its note from the walk, which names
  -- the root (`executionWalk`).
  let some info := env.find? name
  | return record
  let some moduleName := moduleOf name
  | return note record s!"{name}: module attribution is unavailable"
  let owned := ownedModules.contains moduleName
  -- The admitted origin of the constant's module when it is the toolchain's own compiled
  -- `Init`, `Std`, `Lean`, `Lake` or `LeanExport` module. A trusted boundary of an ownable kind
  -- there belongs to the toolchain's trusted base; `implemented_by` and `extern` data can only be
  -- set in the declaring module, so the declaration's module decides who owns the boundary.
  let toolchain := toolchainModules.find? moduleName
  -- The occurrence of a boundary is its position in the root's list, which `assemble` gives.
  let entry (boundary : BoundaryKind) (correspondence : Correspondence)
      (replacement : Option Name) (evidence : Option String)
      (terms : Option CorrespondenceTerms := none) :
      CommandElabM Regula.Report.ExecutionBoundary := do
    let account ← match RegulaPolicy.admitBoundaryEvidence boundary correspondence evidence
        (if boundary.toolchainOwnable && correspondence == .trusted then toolchain
          else none) terms with
      | .ok account => pure account
      | .error error => throwError "{error}"
    return {
      occurrence := 0
      name := name
      «module» := moduleName
      boundary := boundary
      account := account
      owned := owned
      replacement := replacement }
  if let some active := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
    record := { record with
      replacementTargets := record.replacementTargets.push active.toDeclName
      activeSimplificationTargets := record.activeSimplificationTargets.push active.toDeclName }
  for simplification in (candidates.find? name).getD #[] do
    let target := simplification.toDeclName
    record := { record with candidateTargets := record.candidateTargets.push target }
    let (correspondence, evidence, terms) ← correspondence name target
    let boundary ← entry .compilerSimplification correspondence (some target)
      (some s!"conservative constant-equality candidate={simplification.thmName}; \
        {evidence.getD ""}") terms
    record := { record with boundaries := record.boundaries.push boundary }
  let implemented := Lean.Compiler.getImplementedBy? env name
  match lowering (Lean.isExtern env name) implemented.isSome (code != .missing)
      (Lean.getInitFnNameFor? env name) with
  | .extern =>
    -- Every `extern` is a trusted boundary. An `extern` outside the toolchain names the
    -- declarations whose `@[export]` name is its C symbol, read from the attribute names alone:
    -- which body runs under the symbol is not decided, and the match adds no edge. The
    -- simplification candidates above stay edges. Lean calls of an `extern` with an
    -- `implemented_by` target call the target, so it is a runtime replacement too.
    let exporters := match toolchain, Lean.getExternNameFor env `c name with
      | none, some symbol => (symbol, exportersOf (exportEntries env) symbol)
      | _, _ => ("", [])
    let evidence := if exporters.2.isEmpty then none else
      some s!"the symbol {exporters.1} is also exported by \
        {", ".intercalate (exporters.2.map (·.toString))}"
    let boundary ←
      entry (if toolchain.isSome then .nativeRuntime else .external) .trusted none evidence
    record := { record with boundaries := record.boundaries.push boundary }
    if implemented.isNone then return record
  | .initialized action =>
    -- A constant with an initializer and compiled IR, or with no `implemented_by` target, is
    -- compiled to a stub that is never run, and compiled code reads the value its initializer
    -- action returned at module initialization. The action is a retained compiler call of the
    -- record (`compilerDependencies`), so the walk follows it. Calls compiled after an
    -- `implemented_by` target was added call the target, so it is a runtime replacement too.
    let boundary ← entry .initializedValue .trusted none
      (some s!"compiled code reads the value that initializer {action} returned")
    record := { record with boundaries := record.boundaries.push boundary }
    if implemented.isNone then return record
  | .ordinary => pure ()
  if let some target := implemented then
    record := { record with
      currentReplacementTargets := record.currentReplacementTargets.push target }
    -- Which implementation a toolchain replacement runs is part of the toolchain's trusted
    -- base: it needs neither source history nor correspondence. Its current target is still
    -- followed, so every boundary it reaches is classified in its own module.
    if toolchain.isSome then
      let boundary ← entry .runtimeReplacement .trusted (some target) none
      return { record with
        replacementTargets := record.replacementTargets.push target
        boundaries := record.boundaries.push boundary }
    let history ← liftIO <| loadReplacementHistory moduleName
    let targets ← match history with
      | .error error =>
          record := note record s!"{name}: replacement history unavailable: {error}"
          pure #[target]
      | .ok edges =>
          let targets := edges.filterMap fun (reference, target) =>
            if reference == name then some target else none
          record := { record with historyTargets := record.historyTargets ++ targets }
          if !targets.contains target then
            record := note record
              s!"{name}: fresh replacement history omits current target {target}"
          pure (if targets.contains target then targets else targets.push target)
    for target in targets do
      record := { record with replacementTargets := record.replacementTargets.push target }
      let (correspondence, evidence, terms) ← correspondence name target
      let boundary ← entry .runtimeReplacement correspondence (some target) evidence terms
      record := { record with boundaries := record.boundaries.push boundary }
    return record
  -- The value of the name, followed as logical edges.
  let follow (record : RegulaPolicy.ExecutionWalk.NodeRecord name) (dependencies : Array Name) :
      RegulaPolicy.ExecutionWalk.NodeRecord name :=
    { record with logicalTargets := record.logicalTargets ++ dependencies }
  if info.isPartial then
    let boundary ← entry .partialComputation .trusted none none
    record := { record with boundaries := record.boundaries.push boundary }
    if let some value := info.value? then
      record := follow record value.getUsedConstants
    return record
  if info.isUnsafe then
    -- A constant whose type is a proposition is a proof: the compiler erases it, so it never
    -- runs. `lcProof`, the placeholder for erased proofs in unsafe code, is such an axiom.
    if ← observing env name "proposition test" <| liftTermElabM <| Meta.isProp info.type then
      return record
    let boundary ← entry .unsafeComputation .trusted none none
    record := { record with boundaries := record.boundaries.push boundary }
    if let some value := info.value? then
      record := follow record value.getUsedConstants
    return record
  match info with
  | .defnInfo _ =>
      if !(← observing env name "proposition test" <|
          liftTermElabM <| Meta.isProp info.type) then
        if let some value := info.value? then
          record := follow record value.getUsedConstants
      return record
  | .opaqueInfo _ =>
      let recName := Lean.Compiler.mkUnsafeRecName name
      match env.find? recName with
      | some recInfo =>
          if recInfo.isPartial then
            let boundary ← entry .partialComputation .trusted none (some recName.toString)
            return { record with
              boundaries := record.boundaries.push boundary
              helperTargets := record.helperTargets.push recName }
          else
            let boundary ← entry .opaqueComputation .unresolved none
              (some s!"compiled helper {recName} is not partial")
            return { record with boundaries := record.boundaries.push boundary }
      | none =>
          let boundary ← entry .opaqueComputation .checked none (some "kernel-checked-body")
          record := { record with boundaries := record.boundaries.push boundary }
          if !(← observing env name "proposition test" <|
              liftTermElabM <| Meta.isProp info.type) then
            if let some value := info.value? (allowOpaque := true) then
              record := follow record value.getUsedConstants
          return record
  | .axiomInfo _ =>
      if RegulaPolicy.compilerTrustingAxiomName name then
        let boundary ← entry .compilerTrustedProof .trusted none none
        return { record with boundaries := record.boundaries.push boundary }
      return record
  | .thmInfo _ | .ctorInfo _ | .inductInfo _ | .recInfo _ | .quotInfo _ => return record

/-- The record `observeNode` made of each name an earlier root's walk reached, with the modules
whose replacement history it loaded, in order. `observeNode` does not receive the root, and the
walk adds the root's note after the cache, so a kept record never holds a root. Each later root
loads the same histories again, so it records the same history requests, and `environmentReport`
answers each module's history request once for each report, so every request gets the answer the
kept record was made from, whatever the loader. This cache is invocation-local operational state,
never worker evidence. -/
private abbrev NodeRecordCache :=
  Std.DHashMap Name fun name => RegulaPolicy.ExecutionWalk.NodeRecord name × Array Name

/-- The account of one executable root: the observing pass reads each name that the walk reaches
(`observeNode`), in the order of the walk, and the decision `RegulaPolicy.ExecutionWalk.walk`
gives the visits from those records (`walk_sound`, `walk_complete`).
`RegulaPolicy.ExecutionWalk.assemble` takes the visits with the proof that the walk returned them
(`Walked`) and builds the boundaries, the unresolved paths, the compiler edges and the closure from
the record of each visit. -/
private def executionWalk (env : Environment) (ownedModules : List Name)
    (toolchainModules : NameMap RegulaPolicy.ToolchainOrigin)
    (cached : Std.HashMap Name (Array Name))
    (loadReplacementHistory : Name → IO (Except String (Array (Name × Name))))
    (candidates : NameMap (Array Lean.Compiler.CSimp.Entry))
    (proofCache : IO.Ref
      (Std.HashMap (Name × Name) (Correspondence × Option String × Option CorrespondenceTerms)))
    (dependencyCache : IO.Ref (CompilerDependenciesCache env))
    (recordCache : IO.Ref NodeRecordCache)
    (theorems : IO.Ref (Option (List (Name × Array Name)))) (admits : Name → Bool)
    (recursorHelpers : Array Name) (root : Name) (timing : Bool) : CommandElabM
    (Array Regula.Report.ExecutionBoundary ×
      Array String × Array (Name × Name) × RegulaPolicy.ExecutionClosure) := do
  -- Logical recursor machinery may be installed without standalone IR;
  -- matcher/noConfusion/projection uses are handled directly by the compiler.
  -- These tags relax only this initial IR obligation, never root membership,
  -- body/boundary traversal, or the obligation for a retained compiler call.
  -- This conservative account does not attest independent compilation of
  -- every logical machinery root or authenticate its generation.
  let rootCompiled := (Lean.Compiler.getImplementedBy? env root).isNone &&
      !Lean.Compiler.hasMacroInlineAttribute env root && !env.isProjectionFn root &&
      !((Lean.IR.findEnvDecl env root).isNone &&
        (Lean.isAuxRecursor env root || Lean.isNoConfusion env root ||
          Lean.Meta.isMatcherCore env root)) &&
      !(recursorHelpers.contains root && (Lean.IR.findEnvDecl env root).isNone)
  -- The pass: each name that the walk reaches is observed one time, in the order of the walk:
  -- a stack of queued names, the name queued last first.
  let mut records : RegulaPolicy.ExecutionWalk.Records := {}
  let mut queue : Array Name := #[root]
  while !queue.isEmpty do
    let name := queue.back!
    queue := queue.pop
    if records.contains name then continue
    -- A kept record equals the record the pass would make again: the loader `environmentReport`
    -- passes gives one answer for each module in a report, so these requests get the answers
    -- the record was made from.
    let observed ← match (← liftIO recordCache.get).get? name with
      | some (record, histories) =>
          for moduleName in histories do
            discard <| liftIO <| loadReplacementHistory moduleName
          pure record
      | none =>
          let loaded ← liftIO <| IO.mkRef (#[] : Array Name)
          let load (moduleName : Name) := do
            loaded.modify (·.push moduleName)
            loadReplacementHistory moduleName
          let record ← observeNode env ownedModules toolchainModules cached load
            candidates proofCache dependencyCache theorems admits timing name
          let histories ← liftIO loaded.get
          liftIO <| recordCache.modify (·.insert name (record, histories))
          pure record
    -- The one part of a record that names the root, added after the cache: a name with neither a
    -- constant nor compiled code. `observeNode` returns that record with no other unresolved path.
    let record := if (env.find? name).isNone && (Lean.IR.findEnvDecl env name).isNone then
        { observed with unresolved := observed.unresolved.push <|
            s!"{name}: constant used by {root} is not in the environment" }
      else observed
    records := records.insert name record
    queue := queue ++ record.successors
  let request : RegulaPolicy.ExecutionWalk.WalkRequest := { records, root }
  match walked : RegulaPolicy.ExecutionWalk.checked_walk.run request with
  | .ok visits =>
      return RegulaPolicy.ExecutionWalk.assemble rootCompiled { request, visits, walked }
  | .error failure => throwError "the walk of {root} over its records failed: {repr failure}"

/-- The action Lean runs for each initializer that one of `modules` records, in the order of the
module's entries: its `[init]` entries (`initialize`), then its `[builtin_init]` entries
(`builtin_initialize`). An entry is a declaration and the name of its action. A named block
`initialize x : T ← e` records its action `initFn` for `x`, and Lean runs that action. An
anonymous block `initialize e`, and a declaration of type `IO Unit` that has the attribute
itself, record the anonymous name for the declaration, and Lean runs the declaration
(`Lean.runInitAttrForMod`, `Lean.Compiler.LCNF.emitDeclInit`). The entries are those of the module's
imported data and of its IR data, as `runInitAttrForMod` reads them; the name of a declaration
does not select it. An anonymous block elaborates to a private `initFn` with a hygienic name that
no other declaration references, so its entry is the only record that it runs. -/
private def initializerActions (env : Environment) (modules : List Name) : Array Name := Id.run do
  let mut actions : Array Name := #[]
  for (imported, idx) in env.header.modules.zipIdx do
    unless modules.contains imported.module do continue
    for initAttribute in [regularInitAttr, builtinInitAttr] do
      let entries := initAttribute.ext.getModuleEntries env idx
      let entries := entries ++
        (initAttribute.ext.getModuleIREntries env idx).filter (!entries.contains ·)
      for (declaration, action) in entries do
        let action := if action.isAnonymous then declaration else action
        unless actions.contains action do
          actions := actions.push action
  return actions

/-- Owned executable roots: the definitions and opaque constants that
`RegulaPolicy.ExecutionWalk.RootFacts.root` admits, and the action of each initializer that an
owned module records (`initializerActions`), whatever its name, safety or computability: Lean
runs that action at startup or import, where no other root need reference it. A constant is a
root when it is the program's entry point, whatever its safety, or when it is computable, safe,
non-partial and non-internal and execution does not erase it (its type is no proposition and its
result is no `Sort`). Role metadata never removes an otherwise eligible root, including unused
tagged declarations. Erasure is read only where it decides the answer
(`RootFacts.root_erased`).

Assumes: Lean 4.35.0 emits the C `main` function of a module from the compiled function body
named `main` that the module itself holds, whatever the declaration's safety
(`emitMainFnIfNeeded`, `src/Lean/Compiler/LCNF/EmitC.lean:1084-1092`); an imported module's
compiled bodies are the ones `Lean.IR.findEnvDecl` returns. -/
private def executableRoots (env : Environment) (modules : List Name)
    (own : Array (Name × ConstantInfo)) : CommandElabM (Array Name) := do
  let mut roots : Array Name := #[]
  for (name, info) in own do
    match info with
    | .defnInfo _ | .opaqueInfo _ =>
        let facts : RegulaPolicy.ExecutionWalk.RootFacts := {
          entryPoint := name == `main &&
            (match Lean.IR.findEnvDecl env name with | some (.fdecl ..) => true | _ => false)
          internal := name.isInternal, isUnsafe := info.isUnsafe, isPartial := info.isPartial
          isNoncomputable := Lean.isNoncomputable env name, erased := false }
        let facts ← if facts.entryPoint || !facts.root then pure facts else do
          let erased ← observing env name "executable-root classification" do
            if ← liftTermElabM <| Meta.isProp info.type then return true
            liftTermElabM <| Regula.Collect.returnsSort info.type
          pure { facts with erased }
        if facts.root then roots := roots.push name
    | _ => continue
  for action in initializerActions env modules do
    unless roots.contains action do
      roots := roots.push action
  return roots

/-- The records of the imported native-proof axioms that `entries` rest on. They are the axioms an
entry lists whose name the `nativeEqTrue` scheme generates (`RegulaPolicy.nativeAxiomOrigin?`) and
whose module `inspected` does not contain, each once. Each is followed by the record of each
kernel constant of the axiom's own module that its generated prefix names, unless that constant
already has a record: the prefix itself or, for a module-private prefix, the public name it
hides. A constant of another module that a prefix names gets no record, so it cannot displace the
declaration of the axiom's module, and neither does a name that only the code generator has. The
axiom's record is a replay candidate, so its statement is replayed (`Collect.declaration`); the
prefix's record is a snapshot, which has no replay and so is never a native role. A name recorded
as a prefix and then reached as an axiom has its snapshot replaced by a replay candidate, so
whichever of the two is reached first, every reached axiom is replayed. Records are in the order
of their first insertion, prefix snapshots included: a replaced snapshot keeps its position. The
axioms of both are those it reaches in the environment (`KernelAxioms.reachedAxioms`), since no
kernel of this audit replayed an imported module.

Assumes:
- Lean v4.35.0 maps each imported constant to the module that declares it
  (`Environment.getModuleIdxFor?`, `src/lean/Lean/Environment.lean:1196-1198`).
  That map also holds auxiliary names of the code generator that are not kernel constants
  (`src/lean/Lean/Environment.lean:241-243`), so a prefix is recorded only when the environment
  contains it.
- The audited environment is imported at `OLeanLevel.private`, the default of `importModules`
  (`src/lean/Lean/Environment.lean:2434-2441`), which treats every import as `import all`
  (line 2182). So the constants that a `module` file keeps private, its generated native-proof
  axioms among them, are in the environment.
- Lean v4.35.0 gives a generated name the private form of its module while a `module` file
  elaborates without exporting (`DeclNameGenerator.mkUniqueName.curr`,
  `src/lean/Lean/CoreM.lean:121-125`), and `privateToUserName` removes that form
  (`src/lean/Lean/PrivateName.lean:29-30`, `:32-35`, `:62-64`). -/
private def importedNativeRecords (env : Environment) (inspected : List Name)
    (entries : Array Regula.Report.Declaration) (scope : Regula.Collect.ContractScope) :
    CommandElabM (Array Regula.Report.Declaration) := do
  let moduleOf? (name : Name) : Option Name :=
    (env.getModuleIdxFor? name).map fun idx => env.header.modules[(idx : Nat)]!.module
  let mut reached : NameSet := {}
  let mut index : Std.HashMap Name Nat := {}
  let mut records := #[]
  for entry in entries do
    for name in entry.axioms do
      if reached.contains name then continue
      reached := reached.insert name
      let some (pfx, _) := RegulaPolicy.nativeAxiomOrigin? name | continue
      let some axiomModule := moduleOf? name | continue
      if inspected.contains axiomModule then continue
      let record ← observing env name "imported native axiom record"
        (Regula.Collect.declaration name .replayCandidate scope)
      match index[name]? with
      | some i => records := records.set! i record
      | none =>
        index := index.insert name records.size
        records := records.push record
      let named := if Lean.isPrivateName pfx then #[pfx, Lean.privateToUserName pfx] else #[pfx]
      for parent in named do
        if env.contains parent && moduleOf? parent == some axiomModule
            && !index.contains parent then
          index := index.insert parent records.size
          records := records.push (← observing env parent "imported native prefix record"
            (Regula.Collect.declaration parent .snapshot scope))
  return records

/-- Build the complete report for exact requested module names. The trusted
runner calls this function directly, without parsing a command in the audited
module's frontend extension environment. Each declaration record has the axioms `replayed` holds
for it, those it reaches in the kernel that replayed it (`Admission.validate`), with the axioms
Lean's `collectAxioms` omits of them, or, with no `replayed`, those it reaches in the environment
(`KernelAxioms.reachedAxioms`). The
kernel walks of the correspondence proofs the execution account builds stop at the names
`replayed` holds (`kernelAnswer`). `replayedModules` names the modules whose declarations the
kernel checked in this audit, those the environment's admission replayed or reused: the execution
account accepts a correspondence theorem only from one of them or from an origin-checked toolchain
module (`replacementCorrespondence`). `dependencies` names the modules of owned dependencies that
`modules` import: the report records their declarations and executable roots too, and its census
lists them apart (`Census.dependencyModules`). The report also records the imported native-proof
axioms its declarations rest on, outside those modules (`importedNativeRecords`). One report keeps
the first answer that `loadReplacementHistory` returns for each module and gives it to every later
history request of the report, from any root, so a node record kept for a later root is the record
its pass would make again. A loader that throws returns no answer, and no record is kept from that
request. The report refuses an environment whose `propext`, `Quot.sound` or `Classical.choice` is
not the toolchain's (`Collect.authenticateFoundation`). Each correspondence check runs on a task
of its own (`runCheck`), and a report whose process cannot run one there ends with an error before
any check (`requireDedicatedThreads`). -/
def environmentReport (modules : List Name)
    (loadReplacementHistory : Name → IO (Except String (Array (Name × Name))) :=
      fun _ => pure (.error "trusted source-history loader was not supplied"))
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (replayed : Option Regula.Collect.Replayed := none) (replayedModules : NameSet := {})
    (dependencies : List Name := []) :
    CommandElabM Regula.Report.Collected := do
  let timing := (← IO.getEnv "REGULA_TIMING") == some "1"
  let label := String.intercalate ", " (modules.map toString)
  if modules.isEmpty then
    throwError "environmentReport: no owned module names were supplied"
  unless RegulaPolicy.Compiler.accepts Lean.versionString Lean.githash do
    throwError "unsupported compiler identity {Lean.versionString} ({Lean.githash})"
  let compilerCapability ← liftIO Regula.Collect.compilerCapability
  let _ ← IO.ofExcept (RegulaPolicy.Compiler.admitCapability compilerCapability)
  let env ← getEnv
  -- The profiles permit `propext`, `Quot.sound` and `Classical.choice` by name: refuse an
  -- environment whose constants of those names are not the toolchain's.
  liftIO <| Regula.Collect.authenticateFoundation env
  -- Execution trust checks always need canonical origins. Logical-only
  -- documentation inspection may omit this otherwise unused report payload.
  let moduleOrigins ← if includeExecution || includeModuleOrigins then
      liftIO <| loadedModuleOrigins env
    else pure #[]
  -- The modules of owned dependencies that `modules` import are inspected with them.
  let inspected := modules ++ dependencies
  IO.ofExcept (Regula.Collect.ownedDecisionRegistrations env inspected)
  let own ← ownedDecls env inspected
  let declarationKeys ← own.mapM fun (name, _) => do
    let some idx := env.getModuleIdxFor? name
      | throwError "declaration census has no owner for {name}"
    return (env.header.modules[(idx : Nat)]!.module, name)
  let cached := (replayed.map (·.axioms)).getD {}
  let scope ← Regula.Collect.ContractScope.new env cached
  let entries ← reportPhase timing s!"declaration records [{label}]" <| own.mapM fun (name, _) =>
    observing env name "declaration record"
      (Regula.Collect.declaration name .replayCandidate scope replayed)
  let imported ← reportPhase timing s!"imported native axiom records [{label}]" <|
    importedNativeRecords env inspected entries scope
  let roots ← reportPhase timing s!"execution root census [{label}]" <| if includeExecution then do
    let mut roots ← executableRoots env inspected own
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
  let execution ← reportPhase timing s!"execution walks [{label}]" <| if includeExecution then do
    -- Names alone do not establish toolchain ownership: an adopter or dependency
    -- can supply Init.*, Std.* or Lean.* modules. Resolve each candidate once, and require
    -- the exact canonical artifact path, under the hypotheses of `loadedModuleOrigins`, in the
    -- pinned toolchain's library directory.
    -- Missing origin evidence leaves the module's boundaries owned by the project or a
    -- dependency rather than granting a toolchain exemption.
    let toolchainLib ← liftIO <| Lean.getLibDir (← Regula.CompilerObservation.findSysroot)
    let mut toolchainModules : NameMap RegulaPolicy.ToolchainOrigin := {}
    for (moduleName, origin) in env.header.moduleNames.zip moduleOrigins do
      if RegulaPolicy.ToolchainRoot moduleName.getRoot then
        let actual ← liftIO <| IO.FS.realPath origin.olean
        let expected := Lean.modToFilePath toolchainLib moduleName "olean"
        if ← liftIO (Regula.Collect.isPresent expected) then
          if actual == (← liftIO <| IO.FS.realPath expected) then
            let receipt ← match RegulaPolicy.admitToolchainOrigin moduleName actual.toString
                (← liftIO <| IO.FS.realPath expected).toString with
              | .ok receipt => pure receipt
              | .error error => throwError "{error}"
            toolchainModules := toolchainModules.insert origin.name receipt
    let recursorHelpers := brecOnHelpers env own
    let candidates := simplificationCandidates env
    let proofCache ← liftIO <| IO.mkRef
        ({} : Std.HashMap (Name × Name)
          (Correspondence × Option String × Option CorrespondenceTerms))
    let dependencyCache ← liftIO <| IO.mkRef ({} : CompilerDependenciesCache env)
    let recordCache ← liftIO <| IO.mkRef ({} : NodeRecordCache)
    -- One answer for each module in this report: every history request, from any root's walk
    -- and from a kept record (`NodeRecordCache`), gets the loader's first answer for the module.
    let historyAnswers ← liftIO <| IO.mkRef
        ({} : Std.HashMap Name (Except String (Array (Name × Name))))
    let loadHistoryOnce (name : Name) : IO (Except String (Array (Name × Name))) := do
      if let some answer := (← historyAnswers.get)[name]? then return answer
      let answer ← loadReplacementHistory name
      historyAnswers.modify (·.insert name answer)
      return answer
    let theorems ← liftIO <| IO.mkRef (none : Option (List (Name × Array Name)))
    -- A correspondence theorem counts only from a module whose declarations the kernel checked
    -- in this audit (`replayedModules`) or from an origin-checked toolchain module.
    let admits (candidate : Name) : Bool := match env.getModuleIdxFor? candidate with
      | some idx =>
          let moduleName := env.header.modules[(idx : Nat)]!.module
          replayedModules.contains moduleName || toolchainModules.contains moduleName
      | none => false
    unless roots.isEmpty do liftIO requireDedicatedThreads
    roots.mapM fun (moduleName, root) => do
      let (boundaries, unresolved, compilerEdges, closure) ←
        reportPhase timing s!"execution walk {root}" <| observing env root "execution walk" <|
          executionWalk env inspected toolchainModules cached (fun name => do
            historyRequests.modify fun requests =>
              if requests.contains (root, name) then requests else requests.push (root, name)
            loadHistoryOnce name) candidates proofCache dependencyCache recordCache
            theorems admits recursorHelpers root timing
      return ({
        name := root
        «module» := moduleName
        boundaries, unresolved, compilerEdges, closure } :
        Regula.Report.ExecutionRoot)
    else pure #[]
  return {
    toolchain := Lean.versionString
    compilerCapability
    modules := RegulaPolicy.canonicalNames env.header.moduleNames
    moduleOrigins
    declarations := entries
    execution
    imported
    census := { modules := modules.toArray, dependencyModules := dependencies.toArray
                declarations := declarationKeys
                executionRoots := if includeExecution then some roots else none
                historyRequests := ← liftIO historyRequests.get }
  }

end Regula.Probe
