import RegulaPolicy.Plan
import Regula.Checker.PolicyCodec
import Regula.Probe
import Regula.Checker.Common
import Regula.Checker.Admission
import Regula.Checker.SourceBinding
import Regula.Linter.Documentation

/-!
# Trusted environment loading

Trusted environment loading for checker policy. The fully qualified reporter
is called directly; audited syntax extensions cannot replace the observation.
-/

namespace Regula.Checker.Environment

open Lean System
open scoped Regula.Report

/-- The checker-owned probe modules force-imported into every report so the
trusted reporter is always available: the probe and its transitive imports
inside the checker library. They are never part of an audited surface, so
their presence in an environment is not evidence about the claimed modules.

The force import loads the whole import closure of `Regula.Probe` into the audited
environment, and the gate's excluded-module scan (`AxiomGate.auditSurfaceAt`) exempts only
`RegulaPolicy.infrastructureModuleNames`. So every module of that closure outside the
toolchain (roots `Init`, `Std`, `Lean` and `Lake`) is a `RegulaPolicy` module or one of
`RegulaPolicy.infrastructureModuleNames`: in a project that hosts this package and claims
`RegulaPolicy`, the scan then reports no module that only the probe loaded. The command
below refuses to elaborate this module otherwise. It walks the imports recorded in the module
data this module loaded, starting at `Regula.Probe`, so it is a fact about this package's
modules as built here. `infrastructureOrigins` authenticates the infrastructure modules'
artifacts in an audited environment; what the `RegulaPolicy` names resolve to there is the
audited project's own build, which this command does not see. -/
def probeModuleNames : Array String :=
  RegulaPolicy.reporterModuleNames.map (·.toString)

run_cmd do
  let env ← getEnv
  let mut pending := [`Regula.Probe]
  let mut closure : NameSet := {}
  repeat
    let name :: rest := pending | break
    pending := rest
    if closure.contains name then continue
    closure := closure.insert name
    let some data := (env.getModuleIdx? name).bind fun index =>
        env.header.moduleData[(index : Nat)]?
      | throwError "probe import closure: module {name} is not loaded"
    pending := data.imports.toList.map (·.module) ++ pending
  for name in closure do
    unless #[`Init, `Std, `Lean, `Lake, `RegulaPolicy].contains name.getRoot ||
        RegulaPolicy.infrastructureModuleNames.contains name do
      throwError "probe import closure: {name} is neither a RegulaPolicy module nor one of \
        RegulaPolicy.infrastructureModuleNames, so a project that hosts this package and \
        excludes its library would import an excluded module through the force-loaded probe; \
        move what the probe needs from it into RegulaPolicy"

/-- The probe modules no claimed module may import. `Regula.Contract` (the
executable-contract interface, standard §7.11), `Regula.MaterialClaim` (the
`@[regula_material]` registration, §5.2) and `Regula.Decision` (the `@[regula_decision]`
registration, §7.11) are the published interfaces a claimed surface
imports by design (§7.10); the probe and its report records are
checker tooling that reach an audited environment only through the force
import, never through a claimed module's own imports. -/
def probeOnlyModuleNames : Array String :=
  RegulaPolicy.reporterOnlyModuleNames.map (·.toString)

/-- The checker-owned probe module force-imported into every report so the
trusted reporter is always available. It is never part of an audited surface. -/
def probeModuleName : String := "Regula.Probe"

/-- Imported module metadata, before any declaration admission or policy inspection. A clear
graph permits inspection to continue; this observation grants no acceptance authority. -/
structure ModuleGraph where
  /-- Every loaded module, in the complete report's canonical name order. -/
  modules : Array Name
  /-- The canonical artifact and recorded direct imports of every loaded module. -/
  moduleOrigins : Array Regula.Report.ModuleOrigin
  deriving ToJson

instance : FromJson ModuleGraph := ⟨fun j => do
  Regula.Checker.PolicyCodec.exactFields j ["modules", "moduleOrigins"]
  return { modules := ← j.getObjValAs? _ "modules"
           moduleOrigins := ← j.getObjValAs? _ "moduleOrigins" }⟩

/-- The same module metadata carried by a completed report, without its policy observations. -/
def ModuleGraph.ofReport (report : ProducerReport.Environment) : ModuleGraph :=
  ⟨report.modules, report.moduleOrigins⟩

/-- The reporter also force-loads this public, neutral name codec. Its presence is
not a source import of excluded policy machinery. Validate the exact durable artifact
before distinguishing it from a claimed module's ordinary imports. -/
private def forcedPublicModule (moduleOrigins : Array Regula.Report.ModuleOrigin) (name : Name)
    (description : String) : IO Name := do
  let origins := moduleOrigins.filter (·.name == name)
  let some origin := origins[0]? | throw <| IO.userError s!"missing {description} origin"
  unless origins.size == 1 do throw <| IO.userError s!"ambiguous {description} origin"
  let some lib ← checkerPackageLibDir | throw <| IO.userError "checker library path unavailable"
  let expected ← IO.FS.realPath (Lean.modToFilePath lib name "olean")
  unless (← IO.FS.realPath origin.olean) == expected do
    throw <| IO.userError s!"{description} origin mismatch"
  return name

/-- Returns `Regula.StructuralName` after checking that the report records exactly one origin
for it and that its `.olean` is the running checker's own artifact; throws otherwise. -/
def forcedStructuralName (report : Regula.Checker.ProducerReport.Environment) : IO Name :=
  forcedPublicModule report.moduleOrigins `Regula.StructuralName "structural-name codec"

private def forcedCollectorFrom (origins : Array Regula.Report.ModuleOrigin) :
    IO (Option Name) := do
  let name ← forcedPublicModule origins `Regula.Collect "shared collector"
  if origins.any (fun origin =>
      !probeModuleNames.contains origin.name.toString && origin.imports.contains name) then
    return none
  return some name

private def forcedCompilerObserverFrom (origins : Array Regula.Report.ModuleOrigin) :
    IO (Option Name) := do
  let name ← forcedPublicModule origins `Regula.CompilerObservation "compiler capability observer"
  let collector ← forcedCollectorFrom origins
  if origins.any (fun origin => origin.imports.contains name &&
      !(RegulaPolicy.reporterModuleNames.contains origin.name || some origin.name == collector)) then
    return none
  return some name

/-- The extracted constructor is also force-loaded by Probe. Its artifact must
be the checker's exact artifact. Unlike the neutral name codec, it remains in
the excluded-library scan whenever another module actually imports it. -/
def forcedCollectorOnly (report : Regula.Checker.ProducerReport.Environment) : IO
    (Option Name) := forcedCollectorFrom report.moduleOrigins

/-- The compiler observer is infrastructure only through authenticated reporters or an
already force-only collector. A claimed import of either module keeps it in the owned scan. -/
def forcedCompilerObserverOnly (report : Regula.Checker.ProducerReport.Environment) : IO
    (Option Name) := forcedCompilerObserverFrom report.moduleOrigins

/-- The ordinary loaded modules after authenticating the existing force-only exemptions. -/
def ModuleGraph.ordinaryModules (graph : ModuleGraph) : IO (Array Name) := do
  let codec ← forcedPublicModule graph.moduleOrigins `Regula.StructuralName "structural-name codec"
  let collector ← forcedCollectorFrom graph.moduleOrigins
  let observer ← forcedCompilerObserverFrom graph.moduleOrigins
  return graph.modules.filter fun name =>
    !(probeModuleNames.map String.toName).contains name && name != codec &&
      some name != collector && some name != observer

/-- Bind this environment's requested roots and every other positively assigned module it
loads before using the graph for violations. Excluded modules remain scope observations. -/
def ModuleGraph.scopeRequests (graph : ModuleGraph) (requested assigned : Array Name) :
    Array Name :=
  requested ++ assigned.filter (fun name => graph.modules.contains name && !requested.contains name)

/-- The early binding domain always retains every requested root. -/
theorem ModuleGraph.scopeRequests_requested (graph : ModuleGraph) (requested assigned : Array Name)
    (name : Name) (present : name ∈ requested) : name ∈ graph.scopeRequests requested assigned := by
  simp [scopeRequests, present]

/-- Every positively assigned module loaded in this environment receives the same origin
guard as its requested roots, including positive dependencies owned by another environment. -/
theorem ModuleGraph.scopeRequests_loaded (graph : ModuleGraph) (requested assigned : Array Name)
    (name : Name) (positive : name ∈ assigned) (loaded : name ∈ graph.modules) :
    name ∈ graph.scopeRequests requested assigned := by
  by_cases present : name ∈ requested
  · exact graph.scopeRequests_requested requested assigned name present
  · simp [scopeRequests, positive, loaded, present]

/-- Bind every requested module to a unique origin under the Lake output directory before
using its graph for scope findings. The completed-report check uses this same predicate. -/
def ModuleGraph.requestedFailures (graph : ModuleGraph) (ordinary requested : Array Name)
    (ownedOutput : FilePath) : IO (Array String) := do
  let mut failures := #[]
  for name in requested do
    unless ordinary.contains name do
      failures := failures.push s!"surface-omission: Lake module {name} was not elaborated"
    let origins := graph.moduleOrigins.filter (·.name == name)
    let fresh ← match origins[0]? with
      | some origin => pathWithin (FilePath.mk origin.olean) ownedOutput
      | none => pure false
    if origins.size != 1 || !fresh then
      failures := failures.push
        s!"surface-not-fresh: {name} did not resolve from the fresh Lake output"
  return failures

/-- The modules that the import closure of a requested module contains in one environment, by
its module origins (`Admission.importClosure`), or `none` when one of those closures cannot be
built because a module it reaches has no origin. -/
def claimedClosure (origins : Array Regula.Report.ModuleOrigin) (requested : Array Name) :
    Option NameSet :=
  let index := Admission.originIndex origins
  requested.foldlM (init := {}) fun closure m =>
    (Admission.importClosure index m).map fun reached =>
      reached.foldl (fun closure origin => closure.insert origin.name) closure

/-- Whether `m` is one of the checker's infrastructure modules
(`RegulaPolicy.infrastructureModuleNames`): the force-loaded reporter, its published interfaces
and its observers. `infrastructureOrigins` authenticates each one loaded as the running
checker's own artifact, so an environment never owns one, whichever package holds its source;
`Admission.replaySet` replays one that imports a replayed module. -/
def isInfrastructure (m : Name) : Bool :=
  RegulaPolicy.infrastructureModuleNames.contains m

/-- One pass over an environment's module origins, in their order, adding to `owned` each module
of `dependencies` outside the infrastructure modules that imports a module of `owned`. -/
def ownImporters (origins : Array Regula.Report.ModuleOrigin) (dependencies : Array Name)
    (owned : Std.HashSet Name) : Std.HashSet Name :=
  origins.foldl (fun owned origin =>
    if !owned.contains origin.name && dependencies.contains origin.name &&
        !isInfrastructure origin.name && origin.imports.any owned.contains then
      owned.insert origin.name
    else owned) owned

/-- `ownImporters` until a pass adds nothing, for at most `fuel` passes. Lean records a module's
imports before the module, so in that order one pass adds every importer and the next adds none.
That this reaches every importer is not proved: `Admission.validate` refuses a module it does not
replay that imports one it replays, so a missed importer leaves the audit incomplete. -/
def ownImportersUpTo (origins : Array Regula.Report.ModuleOrigin) (dependencies : Array Name) :
    Nat → Std.HashSet Name → Std.HashSet Name
  | 0, owned => owned
  | fuel + 1, owned =>
    let next := ownImporters origins dependencies owned
    if next.size == owned.size then owned else ownImportersUpTo origins dependencies fuel next

/-- The modules an environment owns, from its module origins, its requested modules, its source
bindings `bound` and the modules `dependencies` of the owned dependencies, none of them an
infrastructure module (`isInfrastructure`): each requested module and each source binding outside
`dependencies`; each module of `dependencies` that the import closure of a requested module
contains (`claimedClosure`); and each module of `dependencies` that imports a module the
environment owns, since `Admission.validate` refuses a module it does not replay that imports one
it replays. When a requested module's closure cannot be built, every module of `dependencies` is
owned. -/
def ownedModuleSet (origins : Array Regula.Report.ModuleOrigin)
    (requested bound dependencies : Array Name) : Std.HashSet Name :=
  let listed := requested ++ bound ++ dependencies
  match claimedClosure origins requested with
  | none => listed.foldl (fun owned m =>
      if isInfrastructure m then owned else owned.insert m) {}
  | some closure =>
    let roots := listed.foldl (fun owned m =>
      if isInfrastructure m || (dependencies.contains m && !closure.contains m)
      then owned else owned.insert m) {}
    ownImportersUpTo origins dependencies (origins.size + 1) roots

/-- A pass of `ownImporters` keeps every module already owned. -/
private theorem contains_ownImporters {origins : Array Regula.Report.ModuleOrigin}
    {dependencies : Array Name} {owned : Std.HashSet Name} {m : Name}
    (h : owned.contains m = true) : (ownImporters origins dependencies owned).contains m = true := by
  unfold ownImporters
  rw [← Array.foldl_toList]
  generalize origins.toList = rest at *
  induction rest generalizing owned with
  | nil => exact h
  | cons origin rest ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · simp [Std.HashSet.contains_insert, h]
    · exact h

/-- `ownImportersUpTo` keeps every module already owned. -/
private theorem contains_ownImportersUpTo {origins : Array Regula.Report.ModuleOrigin}
    {dependencies : Array Name} :
    ∀ (fuel : Nat) {owned : Std.HashSet Name} {m : Name}, owned.contains m = true →
      (ownImportersUpTo origins dependencies fuel owned).contains m = true
  | 0, _, _, h => h
  | fuel + 1, owned, m, h => by
    simp only [ownImportersUpTo]
    split
    · exact h
    · exact contains_ownImportersUpTo fuel (contains_ownImporters h)

/-- Inserting each listed module that `skip` rejects keeps every module already present and adds
each listed module that `skip` does not reject. -/
private theorem contains_foldl_insert {skip : Name → Bool} {m : Name} :
    ∀ (listed : List Name) (owned : Std.HashSet Name),
      ((m ∈ listed ∧ skip m = false) ∨ owned.contains m = true) →
      (listed.foldl (fun owned x => if skip x then owned else owned.insert x) owned).contains m =
        true
  | [], _, h => by simpa using h
  | x :: rest, owned, h => by
    simp only [List.foldl_cons]
    apply contains_foldl_insert rest
    rcases h with ⟨hm, hs⟩ | h
    · rcases List.mem_cons.mp hm with rfl | hm
      · right
        simp [hs, Std.HashSet.contains_insert]
      · left
        exact ⟨hm, hs⟩
    · right
      split
      · exact h
      · simp [Std.HashSet.contains_insert, h]

/-- An environment owns each requested module and source binding that is not an infrastructure
module and either is not a module of an owned dependency, such as a module of the root package, or
is one that the import closure of a requested module contains, or the environment's closures
cannot be built. So the root package's modules are owned wherever they are loaded, as before owned
dependencies, and owning a dependency never replays less. -/
theorem contains_ownedModuleSet {origins : Array Regula.Report.ModuleOrigin}
    {requested bound dependencies : Array Name} {m : Name} (listed : m ∈ requested ++ bound)
    (infrastructure : m ∉ RegulaPolicy.infrastructureModuleNames)
    (claimed : m ∉ dependencies ∨
      ∀ reached, claimedClosure origins requested = some reached → reached.contains m = true) :
    (ownedModuleSet origins requested bound dependencies).contains m = true := by
  have notInfrastructure : isInfrastructure m = false := by
    simpa [isInfrastructure, Array.contains_eq_mem] using infrastructure
  have inListed : m ∈ (requested ++ bound ++ dependencies).toList := by
    rcases Array.mem_append.mp listed with h | h <;> simp [h]
  unfold ownedModuleSet
  split
  · rw [← Array.foldl_toList]
    exact contains_foldl_insert _ _ (.inl ⟨inListed, notInfrastructure⟩)
  · rename_i closure hclosure
    apply contains_ownImportersUpTo
    rw [← Array.foldl_toList]
    refine contains_foldl_insert _ _ (.inl ⟨inListed, ?_⟩)
    rcases claimed with outside | inside
    · simp [Array.contains_eq_mem, outside, notInfrastructure]
    · simp [inside closure hclosure, notInfrastructure]

/-- What one environment owns, computed once from its module origins, its requested modules, its
source bindings and the modules of the owned dependencies (`EnvironmentOwnership.of`, from
`ownedModuleSet`). Every per-module job takes its modules from this one value, so no job selects
another set: kernel admission replays `modules`, and of `reporterOnly` each module under the
checker's reserved prefixes that imports a replayed module; the unowned-output refusal exempts
`reporterOnly`; declaration and root inspection, documentation, the census sources and the
transcripts cover the requested modules and then `dependencies`; and under `--fresh` each loaded
module of `modules` must resolve inside the copy (`ModuleGraph.outsideCopy`). The project
coordinator computes it from its module-graph pass and each worker from its loaded environment,
from the same inputs. -/
structure EnvironmentOwnership where
  /-- The modules the environment owns (`ownedModuleSet`), in the order of the requested modules,
  the source bindings and the owned dependency modules. -/
  modules : Array Name
  /-- The modules of the owned dependencies that the environment owns and loads, other than the
  requested ones, in the order of the dependency modules: it inspects them with the requested
  modules. -/
  dependencies : Array Name
  /-- The modules of the owned dependencies that the environment does not own: the checker's own
  modules under its reserved prefixes (`projectModules`), and those that no requested module
  imports and that import no owned module. Kernel admission replays each of them under the
  reserved prefixes that imports a replayed module (`Admission.replaySet`), and refuses any other
  that imports one (`Admission.validate`). -/
  reporterOnly : Array Name
  deriving Repr

/-- The modules of the owned dependencies `dependencies` that an environment can own: those
outside the checker's reserved prefixes (`reservedModule`). A module under them in a package other
than the root package is the checker's own code, whose source is the checker's own text
(`Lake.checkReservedModules`), and the checker's own audit inspects it with its whole library; no
environment of another project owns it, as none owns an infrastructure module. -/
def projectModules (dependencies : Array Name) : Array Name :=
  dependencies.filter (!reservedModule ·)

/-- The ownership of the environment with module origins `origins`, requested modules
`requested`, source bindings `bound` and owned dependency modules `dependencies`, of which it can
own the `projectModules`. -/
def EnvironmentOwnership.of (origins : Array Regula.Report.ModuleOrigin)
    (requested bound dependencies : Array Name) : EnvironmentOwnership :=
  let project := projectModules dependencies
  let owned := ownedModuleSet origins requested bound project
  let loaded := origins.map (·.name)
  { modules := (requested ++ bound ++ project).filter owned.contains
    dependencies := project.filter fun m =>
      owned.contains m && loaded.contains m && !requested.contains m
    reporterOnly := dependencies.filter (!owned.contains ·) }

/-- The inspected dependency modules are exactly the loaded dependency modules outside the
checker's reserved prefixes that the environment owns (`ownedModuleSet`, with its importers) and
does not request. -/
theorem EnvironmentOwnership.mem_dependencies {origins : Array Regula.Report.ModuleOrigin}
    {requested bound dependencies : Array Name} {m : Name} :
    m ∈ (EnvironmentOwnership.of origins requested bound dependencies).dependencies ↔
      m ∈ projectModules dependencies ∧
        (ownedModuleSet origins requested bound (projectModules dependencies)).contains m ∧
        m ∈ origins.map (·.name) ∧ m ∉ requested := by
  simp [EnvironmentOwnership.of, Array.mem_filter, Array.contains_eq_mem, and_assoc]

/-- No environment owns a module of an owned dependency under the checker's reserved prefixes
unless it requests it or binds its source, which only the root package's modules are. -/
theorem EnvironmentOwnership.reserved_not_owned {origins : Array Regula.Report.ModuleOrigin}
    {requested bound dependencies : Array Name} {m : Name} (reserved : reservedModule m = true)
    (outside : m ∉ requested ++ bound) :
    m ∉ (EnvironmentOwnership.of origins requested bound dependencies).modules := by
  simp only [EnvironmentOwnership.of, projectModules, Array.mem_filter, Array.mem_append]
  rintro ⟨(listed | ⟨-, hm⟩), -⟩
  · exact outside (Array.mem_append.mpr listed)
  · simp [reserved] at hm

/-- Every inspected dependency module is one of the modules the environment owns and replays. -/
theorem EnvironmentOwnership.dependencies_replayed {origins : Array Regula.Report.ModuleOrigin}
    {requested bound dependencies : Array Name} {m : Name}
    (h : m ∈ (EnvironmentOwnership.of origins requested bound dependencies).dependencies) :
    m ∈ (EnvironmentOwnership.of origins requested bound dependencies).modules := by
  obtain ⟨dependency, owned, -, -⟩ := EnvironmentOwnership.mem_dependencies.mp h
  simp only [EnvironmentOwnership.of, Array.mem_filter, Array.mem_append]
  exact ⟨.inr dependency, owned⟩

/-- Modules loaded from an owned package's output (`Ownership.outputs`: the root package's, then
each owned dependency's) that the environment neither owns (`EnvironmentOwnership.modules`) nor
exempts (`EnvironmentOwnership.reporterOnly` and the infrastructure modules), retaining every
direct importer in header order. An output directory that does not exist holds no loaded module. The
metadata phase and full loader share this refusal. -/
def ModuleGraph.unownedModules (graph : ModuleGraph) (ownership : EnvironmentOwnership)
    (outputs : Array FilePath) : IO (Array ProducerReport.UnownedModule) := do
  let outputs ← outputs.filterM (·.pathExists)
  let mut unowned := #[]
  for origin in graph.moduleOrigins do
    if !ownership.modules.contains origin.name && !ownership.reporterOnly.contains origin.name &&
        !isInfrastructure origin.name then
      if ← outputs.anyM (pathWithin (FilePath.mk origin.olean)) then
        unowned := unowned.push origin.name
  return unowned.map fun name => {
    «module» := name
    importers := graph.moduleOrigins.filterMap fun origin =>
      if origin.imports.any (· == name) then some origin.name else none }

/-- Under `--fresh`, each module the environment owns (`EnvironmentOwnership.modules`) that it
loaded from outside the copy at `copy`, with the `.olean` it was loaded from: one whose `.olean`,
on real paths, does not lie below `copy`. The copy is made with no compiled module
(`copyProject`), so an owned module that resolves below it was compiled by the copy's own build;
one that resolves elsewhere, such as an artifact of the original checkout, a configured build
directory outside the copy or the reporter's overlay of the checker's library, was not. An
`.olean` that cannot be resolved counts as outside. -/
def ModuleGraph.outsideCopy (graph : ModuleGraph) (ownership : EnvironmentOwnership)
    (copy : FilePath) : IO (Array (Name × String)) := do
  let mut outside := #[]
  for origin in graph.moduleOrigins do
    if ownership.modules.contains origin.name then
      let inside ← try pathWithin (FilePath.mk origin.olean) copy catch _ => pure false
      unless inside do outside := outside.push (origin.name, origin.olean)
  return outside

/-- The text of the refusal of an owned module that a fresh audit loaded from outside its copy
(`ModuleGraph.outsideCopy`). -/
def outsideCopyDetail (copy : FilePath) (entry : Name × String) : String :=
  s!"surface-not-fresh: owned module {entry.1} resolved from {entry.2}, outside the copy {copy}, \
    so the copy's build did not produce it"

/-- The owned package that each module an environment loaded belongs to, by its artifact. Each
loaded module whose name `safeModuleComponents?` does not admit is refused first, whoever provides
it: Lake builds a module of any name under a library's root or glob, such as one that only an
import names, and `Lean.modToFilePath` places its source and artifact outside the package's
directories for an absolute component or a `..` segment, where no output check sees them. The
owned packages are the root package and the owned dependencies (`Ownership.root`,
`Ownership.dependencies`); each keeps Lake's default layout (`Lake.checkDefaultLayout`), so its
artifact of module `m` is `m`'s `.olean` below its output directory. A loaded module, other than an
infrastructure module (`isInfrastructure`), belongs to an owned package when the package provides it
by its own module resolution and the `.olean` the environment loaded is, on real paths, exactly that
package's artifact of it. The module is refused when an owned package provides it and it is no such
package's artifact, or the artifact of more than one, except a module under the checker's reserved
prefixes (`reservedModule`) that is the checker's own artifact, which the reporter's overlay serves
from the checker's library and whose source in any package is the checker's own text
(`Lake.checkReservedModules`). Such a module belongs to the owned dependency that alone provides it;
one that the root package provides belongs to none, since the root package's modules are owned
through their source bindings. No environment owns a module under those prefixes that belongs to
an owned dependency (`EnvironmentOwnership.of`, `projectModules`): it is the checker's own code. A
module that no owned package provides belongs to none. The result
lists each loaded module that belongs to an owned dependency, in the order of the module origins,
with its index in `Ownership.dependencies`, so dependency membership and each source bound for a
module follow the artifact the environment loaded, not the name. -/
def attributeLoaded (origins : Array Regula.Report.ModuleOrigin) (ownership : Ownership) :
    IO (Except String (Array (Name × Nat))) := do
  let packages := ownership.root.toArray ++ ownership.dependencies
  let offset := ownership.root.toArray.size
  let provided := packages.map fun package => NameSet.ofArray package.modules
  -- An artifact is placed by `modulePath?` alone, for a name that the loop below has admitted.
  let artifact (output : FilePath) (name : Name) : IO (Option FilePath) := do
    let some path := modulePath? output name "olean" | return none
    try some <$> IO.FS.realPath path catch _ => pure none
  let checker ← do
    let some lib ← checkerPackageLibDir | pure none
    try some <$> IO.FS.realPath lib catch _ => pure none
  let mut attributed := #[]
  for origin in origins do
    if (safeModuleComponents? origin.name).isNone then
      return .error s!"surface-attribution: module {origin.name} was loaded from {origin.olean}, \
        and its name has a component that is an absolute path, has an empty, `.` or `..` segment \
        between path separators, or is a number, so a path built from it can leave its directory"
    if isInfrastructure origin.name then continue
    let providers := (List.range packages.size).filter fun index =>
      (provided[index]?.map (·.contains origin.name)).getD false
    if providers.isEmpty then continue
    let loaded := FilePath.mk origin.olean
    let mut matched : Array Nat := #[]
    for index in providers do
      if let some package := packages[index]? then
        if (← artifact package.output origin.name) == some loaded then
          matched := matched.push index
    let named := ", ".intercalate (providers.filterMap fun index =>
      packages[index]?.map fun package => s!"'{package.package}'")
    match matched with
    | #[index] =>
      if index ≥ offset then attributed := attributed.push (origin.name, index - offset)
    | #[] =>
      if reservedModule origin.name then
        if let some lib := checker then
          if (← artifact lib origin.name) == some loaded then
            if let [index] := providers then
              if index ≥ offset then attributed := attributed.push (origin.name, index - offset)
            continue
      return .error s!"surface-attribution: module {origin.name}, which the owned package {named} \
        provides, was loaded from {loaded}, which is not that package's artifact of it"
    | _ =>
      return .error s!"surface-attribution: module {origin.name} was loaded from {loaded}, which \
        is the artifact of more than one owned package: {named}"
  return .ok attributed

/-- The source bindings of the owned dependency modules that an environment inspects
(`EnvironmentOwnership.dependencies`), each from the package that the environment loaded it from
(`attributeLoaded`): `packages` gives the bindings of each owned package's own sources, in
the order of `Ownership.dependencies`. The second component lists each inspected module that has
no binding in its package. -/
def dependencyBindings (ownership : EnvironmentOwnership) (loaded : Array (Name × Nat))
    (packages : Array (Array ProducerReport.SourceBinding)) :
    Array ProducerReport.SourceBinding × Array Name := Id.run do
  let mut bindings := #[]
  let mut unbound := #[]
  for name in ownership.dependencies do
    let binding := (loaded.find? (·.1 == name)).bind fun (_, index) =>
      (packages[index]?).bind fun sources => sources.find? (·.moduleName == name)
    match binding with
    | some binding => bindings := bindings.push binding
    | none => unbound := unbound.push name
  return (bindings, unbound)

/-- A forbidden edge retained with its exact membership in the observed import graph. -/
private structure ReporterImport (origins : Array Regula.Report.ModuleOrigin) where
  origin : Regula.Report.ModuleOrigin
  present : origin ∈ origins
  imported : Name
  direct : imported ∈ origin.imports
  outside : origin.name ∉ RegulaPolicy.reporterModuleNames
  forbidden : imported ∈ RegulaPolicy.reporterOnlyModuleNames

/-- Each retained edge contradicts the actual infrastructure predicate on the same origins. -/
private theorem ReporterImport.incompatible (claim : RegulaPolicy.Claim)
    (census : RegulaPolicy.EnvironmentCensus) (edge : ReporterImport census.origins) :
    ¬ RegulaPolicy.InfrastructureOK claim census := by
  intro valid
  exact edge.outside
    ((valid.2.2.2.2.1 edge.origin edge.present edge.imported edge.direct edge.forbidden).1)

/-- Collect direct reporter imports in their original order, carrying the rejection witness. -/
private def reporterImports (origins : Array Regula.Report.ModuleOrigin) :
    Array (ReporterImport origins) := Id.run do
  let mut result := #[]
  for present : origin in origins do
    if outside : origin.name ∉ RegulaPolicy.reporterModuleNames then
      for direct : imported in origin.imports do
        if forbidden : imported ∈ RegulaPolicy.reporterOnlyModuleNames then
          result := result.push ⟨origin, present, imported, direct, outside, forbidden⟩
  return result

/-- The scope violations witnessed by imported metadata. Callers first authenticate the
force-only exemptions with `ordinaryModules`; the early path also requires `requestedFailures`
to be empty. Both paths use the same Lake-owned scope and graph fields here. -/
def ModuleGraph.importDetails (graph : ModuleGraph) (ordinary excluded configured : Array Name)
    (ownedOutput : FilePath) (library : String) : IO (Array String) := do
  let mut details := #[]
  for name in ordinary do
    if excluded.contains name then
      details := details.push s!"unexpected-project-module: excluded module \
        {name} was imported into positive library {library}"
  for edge in reporterImports graph.moduleOrigins do
    details := details.push s!"unexpected-project-module: checker probe \
      module {edge.imported} was imported into positive library {library} \
      by {edge.origin.name}"
  for origin in graph.moduleOrigins do
    if (probeModuleNames.map String.toName).contains origin.name then continue
    if ← pathWithin (FilePath.mk origin.olean) ownedOutput then
      if !configured.contains origin.name then
        details := details.push s!"unexpected-project-module: root-owned \
          module {origin.name} is outside every manifested Lake library"
  return details

/-- Authenticate the narrow infrastructure partition against the running checker's
canonical artifacts, retaining the request snapshot. Import restrictions are subsequently
rechecked over the complete census by `InfrastructureOK`; these receipts alone do not
allow a source import of a reporter or change any replay ownership. -/
def infrastructureOrigins (snapshot : RegulaPolicy.AdmittedSnapshot)
    (report : ProducerReport.Environment) : IO (Array RegulaPolicy.InfrastructureOrigin) := do
  let some lib ← checkerPackageLibDir
    | throw <| IO.userError "checker library path unavailable"
  let collector ← forcedCollectorOnly report
  let observer ← forcedCompilerObserverOnly report
  let mut receipts := #[]
  for name in RegulaPolicy.infrastructureModuleNames do
    if name == `Regula.Collect && collector.isNone then continue
    if name == `Regula.CompilerObservation && observer.isNone then continue
    let origins := report.moduleOrigins.filter (·.name == name)
    let some origin := origins[0]?
      | throw <| IO.userError s!"missing infrastructure origin: {name}"
    unless origins.size == 1 do
      throw <| IO.userError s!"ambiguous infrastructure origin: {name}"
    let expected ← IO.FS.realPath (Lean.modToFilePath lib name "olean")
    let actual ← IO.FS.realPath origin.olean
    unless origin.olean == actual.toString do
      throw <| IO.userError s!"noncanonical infrastructure origin: {name}"
    let key : RegulaPolicy.ModuleKey := ⟨snapshot, ← IO.ofExcept (RegulaPolicy.admitIdentity name)⟩
    receipts := receipts.push (← IO.ofExcept <|
      RegulaPolicy.admitInfrastructureOrigin key actual.toString expected.toString)
  return receipts

/-- One memoized replacement-history worker run: its complete inputs and the exact bytes
it wrote. A record is used only when every input is equal to the requester's own. -/
private structure HistoryMemo where
  moduleName : String
  source : String
  sourceBefore : String
  searchIdentity : String
  binary : String
  output : String
  deriving ToJson, FromJson, BEq

/-- The history worker's output bytes for exactly these inputs, shared by the surface
workers of one audit through `memo` (a directory the coordinator owns for the audit).
Trusted assumption (the §7.5 supported-process boundary): the worker's output is a
deterministic function of the module source, the effective search path (`searchIdentity`,
see `loadReportCore`) and the pinned binary, with the audit's inherited environment and
unchanged imported artifacts. Every field is compared exactly before a record is used, so
under that assumption a reused record carries the bytes this worker would have produced;
the requester still validates the packet and its own before/after source comparison. The first
worker
to claim a key (an exclusive-create lock) runs the subprocess; the others wait for its
record, and run the subprocess themselves if the record does not appear or does not match.
Without `memo`, or on any memo failure, the worker runs as before; a failure to publish a
record never changes the returned output. -/
private def historyWorkerOutput (memo : Option FilePath) (inputs : HistoryMemo)
    (run : IO String) : IO String := do
  let some directory := memo | run
  let key := toString (hash (inputs.moduleName, inputs.source, inputs.sourceBefore,
    inputs.searchIdentity, inputs.binary))
  let record := directory / s!"{key}.json"
  let lock := directory / s!"{key}.lock"
  let reuse : IO (Option String) := do
    unless ← record.pathExists do return none
    let stored : HistoryMemo ← IO.ofExcept <| (Json.parse (← IO.FS.readFile record)).bind fromJson?
    return if { stored with output := "" } == inputs then some stored.output else none
  if let some output ← (reuse <|> pure none) then return output
  let claimed ← (do discard <| IO.FS.Handle.mk lock .writeNew; pure true) <|> pure false
  if claimed then
    try
      -- Another worker may have published while this one claimed the key.
      if let some output ← (reuse <|> pure none) then return output
      let output ← run
      try
        let staged := directory / s!"{key}.staged"
        IO.FS.writeFile staged (toJson { inputs with output }).compress
        IO.FS.rename staged record
      catch _ => pure ()
      return output
    finally
      try IO.FS.removeFile lock catch _ => pure ()
  -- Another worker holds the key: wait while it does, for at most ten minutes (beyond the
  -- audit's own deadline), then compute here.
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) - start < 600000 do
    if let some output ← (reuse <|> pure none) then return output
    unless ← lock.pathExists do
      if let some output ← (reuse <|> pure none) then return output
      break
    IO.sleep 50
  run

/-- Re-elaboration recovers overwritten `implemented_by` choices that neither
the final attribute map nor optimized IR preserves. Isolate the frontend's
initializers, memoize once per module in one worker, and share the worker output across
the audit's workers through `historyWorkerOutput`. -/
private def replacementHistory (sourceRoots : Array FilePath)
    (moduleSources : Array (Name × FilePath)) (moduleName : Name)
    (memo : Option (FilePath × String) := none) :
    IO ProducerReport.HistoryOutcome := do
  try
    let olean ← Lean.findOLean moduleName
    let alongside := olean.withExtension "lean"
    -- Owned modules use their exact Lake-resolved source. Prefix-based source
    -- search can otherwise stop at an unrelated dependency directory such as
    -- proofwidgets/Widget before reaching the adopter's actual Widget.lean.
    let source ← if let some (_, source) := moduleSources.find? (·.1 == moduleName) then
        pure source
      else if ← alongside.pathExists then pure alongside else
        Lean.findLean (sourceRoots.toList ++ (← Lean.getSrcSearchPath) ++
          [(← Lean.findSysroot) / "src" / "lean"])
          moduleName
    let some bin := (← IO.appPath).parent
      | throw <| IO.userError "checker binary directory unavailable"
    withScratch (← IO.currentDir) "replacement-history" fun scratch => do
      let output := scratch / "history.json"
      let sourceBefore ← IO.FS.readFile source
      let request := sourceWorkerRequest "history" moduleName source sourceBefore
      let searchPath := System.SearchPath.toString (← Lean.searchPathRef.get)
      let inputs : HistoryMemo := {
        moduleName := (Regula.RegistryCodec.nameJson moduleName).compress, source := source.toString
        sourceBefore, searchIdentity := (memo.map (·.2)).getD searchPath
        binary := (bin / "axiomGate").toString, output := "" }
      let written ← historyWorkerOutput (memo.map (·.1)) inputs do
        let result ← IO.Process.output {
          cmd := (bin / "axiomGate").toString
          args :=
              #["--replacement-history-worker", (Regula.RegistryCodec.nameJson moduleName).compress,
                  source.toString,
            output.toString]
          env := #[("LEAN_PATH", some searchPath)] }
        if result.exitCode != 0 then
          throw <| IO.userError s!"{result.stdout}{result.stderr}"
        IO.FS.readFile output
      let json ← IO.ofExcept <| Regula.Checker.PolicyCodec.parse written
      let payload ← IO.ofExcept <| readWorkerPacket request json
      let sourceAfter ← IO.FS.readFile source
      unless sourceAfter == sourceBefore do
        throw <| IO.userError "replacement history source changed"
      let edges : Array (Name × Name) ← IO.ofExcept <| fromJson? payload
      return .completed source.toString sourceBefore sourceAfter edges
  catch error => return .unavailable error.toString

/-- The import operation shared by metadata refusal and full declaration reporting: every audit
worker loads its environment through it. Two entries of module names: the requested modules, and
every module of the loaded environment (the requested ones and all their imports, from the import
lines the toolchain resolved). Each must pass `safeModuleComponents?` (`requireSafeModuleNames`)
before the audit builds a path from it or attributes it. -/
private unsafe def importReportEnvironment (modules : Array Name) : IO Lean.Environment := do
  if modules.isEmpty || modules.toList.eraseDups.length != modules.size then
    throw <| IO.userError "environment report requires unique nonempty modules"
  requireSafeModuleNames "the requested modules" modules
  Lean.enableInitializersExecution
  let importNames :=
    if modules.contains probeModuleName.toName then modules
    else modules.push probeModuleName.toName
  let imports := importNames.map fun module => ({ module, importAll := true } : Import)
  let env ← timedPhase "environment imports" <| importModules imports {} 0 (loadExts := true)
    (level := .private)
  requireSafeModuleNames "the loaded environment" env.header.moduleNames
  return env

private unsafe def loadReportCoreAtSearchPath (modules : Array Name)
    (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownership : Ownership := {})
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (validateReport : Bool := true) (historyMemo : Option (FilePath × String) := none)
    (priors : Array Admission.PriorAdmission := #[])
    (publish : Option FilePath := none) (inspectDependencies : Bool := false) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) := do
  if modules.isEmpty || modules.toList.eraseDups.length != modules.size then
    throw <| IO.userError "environment report requires unique nonempty modules"
  -- No source is looked up for a name before it is admitted (`importReportEnvironment`).
  requireSafeModuleNames "the requested modules" (modules ++ moduleSources.map (·.1))
  let mut resolvedSources := moduleSources
  for name in modules do
    if !resolvedSources.any (·.1 == name) then
      -- Compiled verbatim snippets live alongside their exact isolated source.
      -- Ordinary project modules already have authoritative Lake source entries.
      let source := (← Lean.findOLean name).withExtension "lean"
      resolvedSources := resolvedSources.push (name, source)
  let sourceBindings ← SourceBinding.capture resolvedSources
  return (← SourceBinding.withUnchanged
      (α := Except ProducerReport.Refusal ProducerReport.Environment) sourceBindings #[] do
    let requested := modules
    let env ← importReportEnvironment requested
    let loadedOrigins ← Regula.Probe.loadedModuleOrigins env
    let graph : ModuleGraph := ⟨RegulaPolicy.canonicalNames env.header.moduleNames, loadedOrigins⟩
    -- What this environment owns, computed once (`EnvironmentOwnership.of`); every per-module job
    -- below takes its modules from it.
    let bound := moduleSources.map (·.1)
    -- Each loaded module of an owned package is that package's artifact (`attributeLoaded`).
    let mut dependencyModules : Array (Name × Nat) := #[]
    match ← attributeLoaded loadedOrigins ownership with
    | .ok attributed => dependencyModules := attributed
    | .error detail => return .error (.admission ⟨detail⟩)
    let owned := EnvironmentOwnership.of loadedOrigins requested bound
      (dependencyModules.map Prod.fst)
    let ownedModules := owned.modules
    -- Kernel admission cannot classify a module loaded from an owned output that no requested
    -- module or source binding owns, so the environment is refused with those modules and their
    -- direct importers: a coverage violation, not a failed inspection.
    unless ownership.outputs.isEmpty do
      let unowned ← graph.unownedModules owned ownership.outputs
      unless unowned.isEmpty do
        return .error (.unowned unowned)
    -- In a copy, every owned module must come from the copy's own build.
    if let some copy := ownership.copy then
      let outside ← graph.outsideCopy owned copy
      unless outside.isEmpty do
        return .error (.admission ⟨"; ".intercalate (outside.map (outsideCopyDetail copy)).toList⟩)
    let origins := if priors.isEmpty && publish.isNone then #[] else loadedOrigins
    let reused := if priors.isEmpty then #[] else
      Admission.reusedModules env origins ownedModules priors
    let admissionResult ← timedPhase "kernel admission" <|
      Admission.validate env ownedModules reused requested
        (owned.reporterOnly.filter reservedModule)
    if let .error failure := admissionResult then return .error (.admission failure)
    let .ok admitted := admissionResult
      | throw <| IO.userError "unreachable admission outcome"
    let admission := admitted.receipt
    -- Later environments of the audit may start from this admission while the report below is
    -- still being built; the coordinator compares it with the finished report
    -- (`Inspection.inspect`). The rename makes the file appear complete or not at all.
    if let some path := publish then
      let staged := path.addExtension "staged"
      IO.FS.writeFile staged
        (toJson ({ receipt := admission, origins } : Admission.Completed)).compress
      IO.FS.rename staged path
    -- In a project audit, the modules of owned dependencies that the environment owns are
    -- inspected with the requested ones (`EnvironmentOwnership.dependencies`), each of them owned
    -- and so replayed above: their declarations, roots, documentation and sources.
    let dependencies := if inspectDependencies then owned.dependencies else #[]
    let inspected := requested ++ dependencies
    -- Freeze the selector from the completed environment before reading docstrings.
    -- Loading server/private data above is necessary for both Lean doc formats.
    let own := Regula.Probe.ownedConstants env inspected.toList
    let mut selected := #[]
    for (name, _) in own do
      if Regula.Linter.Documentation.selected env name then
        let some idx := env.getModuleIdxFor? name
          | throw <| IO.userError s!"material declaration has no module: {name}"
        selected := selected.push (env.header.modules[(idx : Nat)]!.module, name)
    let documentation : Regula.Checker.ProducerReport.DocumentationObservation := {
      -- RG5001 reads each module's header from the exact bound source text.
      modules := ← inspected.mapM fun name => do
        let some binding := sourceBindings.find? (·.moduleName == name)
          | throw <| IO.userError s!"module-header: no bound source for {name}"
        return (name, ← Regula.Linter.Documentation.moduleObservation env name binding.content
          binding.path)
      materialDeclarations := selected
      declarations := ← selected.mapM fun key => do
        return (key, ← Lean.findDocString? env key.2)
    }
    let histories ← IO.mkRef ({} : NameMap ProducerReport.HistoryOutcome)
    let loadHistory (moduleName : Name) := do
      if let some result := (← histories.get).find? moduleName then return result.edges
      let result ← replacementHistory sourceRoots resolvedSources moduleName historyMemo
      histories.modify (·.insert moduleName result)
      return result.edges
    let ctx : Elab.Command.Context := {
      fileName := "<trusted-environment-probe>"
      fileMap := FileMap.ofString ""
      snap? := none
      cancelTk? := none
    }
    let state := Elab.Command.mkState env
    -- The modules whose declarations this audit checked with the kernel: those this admission
    -- replayed and those it reused from an earlier environment's. A correspondence theorem is
    -- accepted only from one of them or from the toolchain's own library.
    let replayedModules := NameSet.ofArray (admission.modules ++ admission.reused)
    match ← timedPhase "declaration report" <| EIO.toIO' <|
        (Regula.Probe.environmentReport requested.toList loadHistory includeExecution
            includeModuleOrigins (some admitted.replayed) replayedModules dependencies.toList).run
            ctx |>.run state with
    | .error ex => throw <| IO.userError (← ex.toMessageData.toString)
    | .ok (report, _) =>
      let historyTable ← histories.get
      let historyKeys := RegulaPolicy.canonicalNames (historyTable.toArray.map (·.1))
      let historyRecords ← historyKeys.mapM fun name => do
        let some outcome := historyTable.find? name
          | throw <| IO.userError "producer-history: missing recorded lookup"
        pure (name, outcome)
      let report : ProducerReport.Environment := {
        toCollected := report
        admission := some admission
        documentation := some documentation
        histories := historyRecords
        sourceBindings := sourceBindings.filter (fun s => report.modules.contains s.moduleName)
      }
      SourceBinding.unchanged report.sourceBindings
      if let .error failure := report.validateSourceEvidence then return .error (.admission failure)
      -- The project coordinator's decoder runs this exact check once and keeps its success as a
      -- `ProducerReport.Admitted` proof for `Acceptance.freezeEnvironment`; only that caller opts
      -- out.
      if validateReport then IO.ofExcept (ProducerReport.checked_validate.run report)
      return .ok report
  ).mapError ProducerReport.Refusal.admission |>.bind id

/-- The module prefixes of the force-imported reporter's import closure outside the toolchain: the
checker's own `Regula` modules and the policy library (the command at the top of this module
refuses any other). -/
def probePrefixes : Array String := reservedPrefixes

/-- The compiled modules of the prefix `pre` in `dir`: the module `pre` itself, at `dir`, and those
below `dir / pre`, each by its path components below `dir` without the `.olean` extension. -/
private def compiledModules (dir : FilePath) (pre : String) : IO (Array (List String)) := do
  let root := if ← ((dir / pre).addExtension "olean").pathExists then #[[pre]] else #[]
  unless ← (dir / pre).isDir do return root
  let base := dir.normalize.components.length
  return root ++ (← (dir / pre).walkDir).filterMap fun path =>
    if path.extension == some "olean" then
      some (((path.withExtension "").normalize.components.drop base))
    else none

/-- Lean resolves a whole module prefix at the first search-path directory that has it, so a
fresh project that builds only `Contract`, or a copy that builds part of an owned package of the
checker's prefixes, must not hide the checker's other modules. The overlay merges, module by
module, the modules of `probePrefixes`: the infrastructure modules
(`RegulaPolicy.infrastructureModuleNames`) are linked from the checker's library `selfLib`, and
every other module from the first directory of `searchPath` that holds its `.olean`, else from
`selfLib`. Each module's parts all come from one directory. Returns the identity of that mapping:
each module with the directory it is linked from, in order. -/
private def linkProbeOverlay (overlay selfLib : FilePath) (searchPath : List FilePath) :
    IO String := do
  let mut sources : Std.HashMap (List String) FilePath := {}
  let mut order : Array (List String) := #[]
  for pre in probePrefixes do
    for dir in searchPath ++ [selfLib] do
      for module in ← compiledModules dir pre do
        if sources.contains module then continue
        let name := module.foldl (fun name part => Name.mkStr name part) .anonymous
        let pinned := RegulaPolicy.infrastructureModuleNames.contains name
        let source := if pinned then selfLib else dir
        if pinned && !(← (selfLib / System.mkFilePath module).addExtension "olean" |>.pathExists)
        then continue
        sources := sources.insert module source
        order := order.push module
  -- One `ln` for each destination directory links every part there.
  let mut byDirectory : Std.HashMap FilePath (Array String) := {}
  for module in order do
    let some source := sources[module]? | continue
    let relative := System.mkFilePath module
    for part in moduleParts do
      let file := (source / relative).addExtension part
      if ← file.pathExists then
        let some parent := (overlay / relative).parent | continue
        byDirectory := byDirectory.insert parent
          ((byDirectory.getD parent #[]).push file.toString)
  for (directory, files) in byDirectory.toArray do
    IO.FS.createDirAll directory
    let linked ← runProcess overlay "ln" (#["-s"] ++ files ++ #[directory.toString])
    if !linked.succeeded then
      throw <| IO.userError s!"could not expose trusted probe modules: {linked.output}"
  let canonical := (order.map fun module =>
    s!"{".".intercalate module}={(sources.getD module selfLib)}").qsort (· < ·)
  return ";".intercalate canonical.toList

/-- Search through the overlay of the reporter's modules (`linkProbeOverlay`) ahead of the
current search path, restored afterwards. -/
private def withProbeSearch {α : Type} (action : String → IO α) : IO α := do
  let some selfLib ← checkerPackageLibDir
    | throw <| IO.userError "trusted checker library directory unavailable"
  let selfLib ← IO.FS.realPath selfLib
  withScratch (← IO.currentDir) "probe-search" fun overlay => do
    let oldSearchPath ← Lean.searchPathRef.get
    let mapping ← linkProbeOverlay overlay selfLib oldSearchPath
    Lean.searchPathRef.set (overlay :: oldSearchPath)
    -- The overlay holds only links whose targets `mapping` names, so the effective search path
    -- is determined by that mapping and the search path below it. Shared history worker output
    -- is keyed on this identity, not on the per-worker overlay name.
    let searchIdentity :=
      s!"probe={selfLib};modules={mapping};path={System.SearchPath.toString oldSearchPath}"
    try action searchIdentity
    finally Lean.searchPathRef.set oldSearchPath

private unsafe def loadReportCore (modules : Array Name) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownership : Ownership := {})
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (validateReport : Bool := true) (historyMemo : Option FilePath := none)
    (priors : Array Admission.PriorAdmission := #[]) (publish : Option FilePath := none)
    (inspectDependencies : Bool := false) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) :=
  withProbeSearch fun searchIdentity =>
    loadReportCoreAtSearchPath modules sourceRoots moduleSources ownership includeExecution
      includeModuleOrigins validateReport (historyMemo.map (·, searchIdentity)) priors publish
      inspectDependencies

private def withReportSearchRoots {α : Type} (extraSearchRoots : Array FilePath)
    (action : IO α) : IO α := do
  let selfLib ← checkerPackageLibDir
  let oldSearchPath ← Lean.searchPathRef.get
  Lean.searchPathRef.set (extraSearchRoots.toList ++ selfLib.toList ++ oldSearchPath)
  try action finally Lean.searchPathRef.set oldSearchPath

/-- Read only the loaded module graph through the full reporter's import and search setup.
The caller binds source bytes; the result has no declaration, admission, or success fields. -/
unsafe def loadModuleGraph (modules : Array Name) (searchRoots : Array FilePath) :
    IO ModuleGraph :=
  withReportSearchRoots searchRoots <| withProbeSearch fun _ => do
    let env ← importReportEnvironment modules
    return { modules := RegulaPolicy.canonicalNames env.header.moduleNames
             moduleOrigins := ← Regula.Probe.loadedModuleOrigins env }

/-- Load exact modules using the already configured search path. This variant
supports bounded parallel, read-only imports while a caller owns the global
search-path scope. -/
unsafe def loadReportCurrentSearchPathOutcome (modules : Array Name)
    (moduleSources : Array (Name × FilePath) := #[]) (ownership : Ownership := {})
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) :=
  loadReportCore modules #[] moduleSources ownership includeExecution includeModuleOrigins

/-- Load exact modules through Lean's import semantics and return their typed
declaration report. Extra search roots are temporary and restored afterward. Kernel admission
reuses the admission `priors` completed for owned modules (`Admission.reusedModules`), and its
receipt and module origins are written to `publish` (`Admission.Completed`) as soon as it
succeeds. -/
unsafe def loadReportOutcome (modules : Array Name)
    (extraSearchRoots : Array FilePath := #[]) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownership : Ownership := {})
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true)
    (validateReport : Bool := true) (historyMemo : Option FilePath := none)
    (priors : Array Admission.PriorAdmission := #[]) (publish : Option FilePath := none)
    (inspectDependencies : Bool := false) :
    IO (Except ProducerReport.Refusal ProducerReport.Environment) :=
  withReportSearchRoots extraSearchRoots <|
    loadReportCore modules sourceRoots moduleSources ownership includeExecution
      includeModuleOrigins validateReport historyMemo priors publish
      inspectDependencies

/-- Compatibility wrapper for callers that report every refusal as an inspection failure at their
own stage. Public rule adapters use the typed outcome variant above. -/
unsafe def loadReportCurrentSearchPath (modules : Array Name)
    (moduleSources : Array (Name × FilePath) := #[]) (ownership : Ownership := {})
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    IO ProducerReport.Environment := do
  IO.ofExcept <| (← loadReportCurrentSearchPathOutcome modules moduleSources ownership
    includeExecution includeModuleOrigins).mapError (·.detail)

/-- `loadReportOutcome` with any refusal raised as an `IO` error carrying its detail. -/
unsafe def loadReport (modules : Array Name)
    (extraSearchRoots : Array FilePath := #[]) (sourceRoots : Array FilePath := #[])
    (moduleSources : Array (Name × FilePath) := #[]) (ownership : Ownership := {})
    (includeExecution : Bool := true) (includeModuleOrigins : Bool := true) :
    IO ProducerReport.Environment := do
  IO.ofExcept <| (← loadReportOutcome modules extraSearchRoots sourceRoots moduleSources ownership
    includeExecution includeModuleOrigins).mapError (·.detail)

end Regula.Checker.Environment
