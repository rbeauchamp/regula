import Regula.Checker.ProducerReport
import Lean.Replay
import Regula.Probe

/-!
# Checked logical admission

Checked logical admission before report construction. The replay base contains
only imported modules outside the replayed inventory. Unsafe and partial entries
remain subject to generated-role policy; they cannot supply logical evidence.
An owned module that an earlier environment of the same audit admitted over the
identical import closure is reused instead of replayed again (`reusedModules`).
-/

namespace Regula.Checker.Admission

open Lean

/-- An earlier environment's completed admission in the same audit, as the coordinator offers it
to a later environment: the owned modules it replayed and offers for reuse, and the origin of
every module it loaded (`Probe.loadedModuleOrigins`). -/
structure PriorAdmission where
  /-- Owned modules the earlier environment replayed and admitted, offered for reuse. -/
  modules : Array Name
  /-- The name, canonical `.olean` path and direct imports of every module it loaded. -/
  origins : Array RegulaPolicy.ModuleOrigin
  deriving ToJson

instance : FromJson PriorAdmission := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["modules", "origins"]
  return { modules := ← j.getObjValAs? _ "modules", origins := ← j.getObjValAs? _ "origins" }⟩

/-- One environment's module origins, by module name. -/
def originIndex (origins : Array RegulaPolicy.ModuleOrigin) :
    Std.HashMap Name RegulaPolicy.ModuleOrigin :=
  origins.foldl (fun index origin => index.insert origin.name origin) {}

/-- The import closure of `m` in one environment: the origin of `m` and of every module it
transitively imports, ordered by name, or `none` when a reached module has no origin. Two
environments have equal closures of `m` exactly when they loaded `m` and every module below it
under the same names, from the same canonical `.olean` files, with the same import edges. -/
def importClosure (origins : Std.HashMap Name RegulaPolicy.ModuleOrigin) (m : Name) :
    Option (Array RegulaPolicy.ModuleOrigin) := Id.run do
  let mut pending := #[m]
  let mut seen : NameSet := ({} : NameSet).insert m
  let mut closure := #[]
  -- Each step settles one name and each name is pushed once, so a closure whose every module
  -- has an origin is settled within `origins.size` steps.
  for _ in [:origins.size] do
    let some name := pending.back? | break
    pending := pending.pop
    let some origin := origins[name]? | return none
    closure := closure.push origin
    for imported in origin.imports do
      unless seen.contains imported do
        seen := seen.insert imported
        pending := pending.push imported
  unless pending.isEmpty do return none
  return some (closure.qsort fun a b => Name.quickLt a.name b.name)

/-- Whether every constant a declaration of `m` refers to (`ConstantInfo.getUsedConstantsAsSet`,
the dependencies `Kernel.Environment.replay` replays first) is declared in a module of
`closure`. -/
private def referencesWithin (env : Environment) (m : Name)
    (closure : Array RegulaPolicy.ModuleOrigin) : Bool := Id.run do
  let some owner := env.getModuleIdx? m | return false
  let allowed := closure.foldl (fun names origin => names.insert origin.name) ({} : NameSet)
  for info in env.header.moduleData[(owner : Nat)]!.constants do
    for used in info.getUsedConstantsAsSet do
      let some idx := env.getModuleIdxFor? used | return false
      unless allowed.contains env.header.modules[(idx : Nat)]!.module do return false
  return true

/-- The priors' offered modules, each with its admission's origins indexed by module name. -/
private def indexPriors (priors : Array PriorAdmission) :
    Array (Array Name × Std.HashMap Name RegulaPolicy.ModuleOrigin) :=
  priors.map fun prior => (prior.modules, originIndex prior.origins)

/-- The import closure of `m` in the environment whose origins are `here`, when `m` is not
`requested` there and an `earlier` admission offers `m` over the identical closure. -/
private def offeredClosure
    (earlier : Array (Array Name × Std.HashMap Name RegulaPolicy.ModuleOrigin))
    (here : Std.HashMap Name RegulaPolicy.ModuleOrigin) (requested : Array Name) (m : Name) :
    Option (Array RegulaPolicy.ModuleOrigin) := do
  guard !requested.contains m
  let closure ← importClosure here m
  guard <| earlier.any fun (modules, index) =>
    modules.contains m && importClosure index m == some closure
  return closure

/-- The owned modules of `env` outside `requested` whose kernel admission this environment
reuses instead of replaying: an earlier environment of the same audit replayed and offers each
one over the identical import closure (`offeredClosure`), every declaration of every owned
module in that closure refers only to constants of its own closure, and every owned module the
closure contains is reused too, so no reused module imports a replayed one. Every other owned
module is replayed. -/
def reusedModules (env : Environment) (origins : Array RegulaPolicy.ModuleOrigin)
    (requested owned : Array Name) (priors : Array PriorAdmission) : Array Name := Id.run do
  if priors.isEmpty then return #[]
  let here := originIndex origins
  let earlier := indexPriors priors
  let mut settled : Array (Name × Array RegulaPolicy.ModuleOrigin) := #[]
  for m in owned do
    let some closure := offeredClosure earlier here requested m | continue
    if referencesWithin env m closure then settled := settled.push (m, closure)
  let ownedSet := NameSet.ofArray owned
  let settledSet := NameSet.ofArray (settled.map (·.1))
  return settled.filterMap fun (m, closure) =>
    if closure.all (fun origin => !ownedSet.contains origin.name ||
        settledSet.contains origin.name) then some m else none

/-- Whether a report's admission reused only what `priors` offered (`offeredClosure`, over the
import closures the report's own module origins give). -/
def reuseJustified (priors : Array PriorAdmission) (report : ProducerReport.Environment) :
    Bool :=
  let here := originIndex report.moduleOrigins
  let earlier := indexPriors priors
  ((report.admission.map (·.reused)).getD #[]).all fun m =>
    (offeredClosure earlier here report.census.modules m).isSome

/-- Replay the completed owned logical declarations against trusted imports, except those of
the `reused` modules, which stay in the replay base with the trusted imports. The original
environment is retained for compiler metadata only after replay succeeds. This is not a fresh
replay of the imported dependency graph. -/
unsafe def validate (env : Environment) (ownedModules : Array Name) (reused : Array Name := #[]) :
    IO (Except ProducerReport.AdmissionFailure ProducerReport.AdmissionReceipt) := do
  let mut replayModules := ownedModules.filter (!reused.contains ·)
  -- The force-loaded reporter now depends on the positive policy library.
  -- Replay these exact checker implementation modules too; importing them into
  -- the base would reintroduce unchecked owned policy declarations. They do not
  -- become claimed surfaces, and arbitrary reverse imports remain forbidden.
  let reporterModules := #[`Regula.Probe, `Regula.Report,
    `Regula.Checker.PolicyCodec, `Regula.StructuralName]
  for _ in [:reporterModules.size] do
    for (name, data) in env.header.moduleNames.zip env.header.moduleData do
      if reporterModules.contains name && !replayModules.contains name &&
          data.imports.any (fun imp => replayModules.contains imp.module) then
        replayModules := replayModules.push name
  let owned := replayModules.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut declarations : Std.HashMap Name ConstantInfo := {}
  let own := Regula.Probe.ownedConstants env replayModules.toList
  let mut required := #[]
  for (name, info) in own do
    declarations := declarations.insert name info
    if !info.isUnsafe && !info.isPartial then
      let some idx := env.getModuleIdxFor? name
        | return .error ⟨s!"[VIOLATION[kernel-admission]] missing owner for {name}"⟩
      required := required.push (env.header.modules[(idx : Nat)]!.module, name)
  let mut imports : Array Import := #[]
  for (name, data) in env.header.moduleNames.zip env.header.moduleData do
    if owned.contains name then continue
    -- Importing such a module would put unchecked owned declarations back in
    -- the trusted base. Ownership must be expanded or the claim rejected.
    if data.imports.any (fun imp => owned.contains imp.module) then
      return .error
          ⟨s!"[VIOLATION[kernel-admission]] unreplayed module {name} imports a replayed module"⟩
    imports := imports.push { module := name, importAll := true }
  let base ← importModules imports {} 0 (loadExts := false) (level := .private)
  try
    for (name, _) in declarations do
      if (base.toKernelEnv.find? name).isSome then
        throw <| IO.userError s!"owned declaration {name} already exists in replay base"
    let checked ← Lean.Kernel.Environment.replay declarations base.toKernelEnv
    let mut admitted := #[]
    for key in required do
      let name := key.2
      if (checked.find? name).isNone then
        throw <| IO.userError s!"missing replayed declaration {name}"
      admitted := admitted.push key
    return .ok { modules := RegulaPolicy.canonicalNames replayModules, required, admitted,
                 reused := RegulaPolicy.canonicalNames reused }
  catch error =>
    return .error ⟨s!"[VIOLATION[kernel-admission]] {error}"⟩
  finally
    -- No replay environment escapes this function. Release its separately
    -- imported regions, as Lean's bundled replay checker does.
    base.freeRegions

end Regula.Checker.Admission
