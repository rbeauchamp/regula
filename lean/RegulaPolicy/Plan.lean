import RegulaPolicy.Claim
import RegulaPolicy.Decision
import RegulaPolicy.Execution
import Regula.Decision

/-! # Census and required-job plan

A frozen data census and a concrete required-job relation. The required jobs are
computed before result admission from the claim and census, never from returned successes.
The IO adapter is responsible for faithfully obtaining configuration, Lake and source data. -/
namespace RegulaPolicy
open Lean (Name)

/-- The kind of a Lake target of the root package. -/
inductive TargetKind where
  /-- A `lean_lib` target. -/
  | library
  /-- A `lean_exe` target. -/
  | executable
  deriving Repr, DecidableEq

/-- Actual Lake target observation, retaining its semantic module array. -/
structure DiscoveredTarget where
  /-- Whether the target is a library or an executable. -/
  kind : TargetKind
  /-- The target's Lake name. -/
  name : String
  /-- The target's modules as Lake resolves them; an executable's root module alone. -/
  modules : Array Name
  deriving Repr, DecidableEq

/-- Parsed target classification: none excludes, some names the owning positive surface. -/
structure TargetAssignment where
  /-- Whether the classified target is a library or an executable. -/
  kind : TargetKind
  /-- The classified target's Lake name. -/
  name : String
  /-- The claimed surface that owns the target, or `none` when the manifest excludes it. -/
  surface : Option String
  deriving Repr, DecidableEq

/-- These implementation imports remain forbidden through ordinary dependencies. -/
def reporterOnlyModuleNames : Array Name :=
  #[`Regula.Probe, `Regula.Report, `Regula.Checker.PolicyCodec]

/-- The published checker interfaces a claimed module may import by design (standard §7.10):
the executable-contract type, the material-claim registration attribute and the decision
registration attribute. The probe force-loads all three, so they are authenticated like the
reporter and are never owned. -/
def publishedInterfaceModuleNames : Array Name :=
  #[`Regula.Contract, `Regula.MaterialClaim, `Regula.Decision]

/-- Exact reporter identities used only to select authentication obligations. Membership
alone never grants an exemption. -/
def reporterModuleNames : Array Name :=
  reporterOnlyModuleNames ++ publishedInterfaceModuleNames

/-- A published interface is never a reporter-only module, so admitting it as a claimed
import leaves every reporter-only import restriction unchanged. -/
theorem publishedInterface_not_reporterOnly :
    ∀ n ∈ publishedInterfaceModuleNames, n ∉ reporterOnlyModuleNames := by decide +kernel

/-- Exact reporter and observation modules eligible for authenticated infrastructure.
The collector and compiler observer additionally require their force-only import conditions. -/
def infrastructureModuleNames : Array Name :=
  reporterModuleNames ++ #[`Regula.StructuralName, `Regula.Collect, `Regula.CompilerObservation]

/-- Canonical-artifact equality for one exact infrastructure module and snapshot. The
adapter obtains both paths independently from actual resolution and the checker library;
this type proves equality of those observations, not filesystem or compiler authenticity. -/
structure InfrastructureOrigin where
  /-- The infrastructure module this receipt is for. -/
  moduleKey : ModuleKey
  /-- The canonical path of the `.olean` the probed environment loaded the module from. -/
  actual : String
  /-- The canonical path of the module's `.olean` in the checker package's own library. -/
  expected : String
  /-- Proof that the module is one of `infrastructureModuleNames`. -/
  eligible : moduleKey.name.name ∈ infrastructureModuleNames
  /-- Proof that the observed path is nonempty. -/
  nonempty : actual ≠ ""
  /-- Proof that the observed and expected paths are equal. -/
  agrees : actual = expected
  deriving DecidableEq

/-- Refuse unsupported identities, absent origins and mismatched canonical artifacts. -/
@[regula_decision]
def admitInfrastructureOrigin (key : ModuleKey) (actual expected : String) :
    Except String InfrastructureOrigin :=
  if hn : key.name.name ∈ infrastructureModuleNames then
    if hp : actual ≠ "" then
      if he : actual = expected then .ok ⟨key, actual, expected, hn, hp, he⟩
      else .error "infrastructure artifact origin mismatch"
    else .error "empty infrastructure artifact origin"
  else .error "unsupported infrastructure module"

/-- Every authenticated candidate is retained unchanged; no arbitrary fallback module
or artifact is substituted. Incoming-import checks remain a whole-census obligation. -/
theorem admitInfrastructureOrigin_exact (origin : InfrastructureOrigin) :
    admitInfrastructureOrigin origin.moduleKey origin.actual origin.expected = .ok origin := by
  unfold admitInfrastructureOrigin
  rw [dite_eq_left origin.eligible, dite_eq_left origin.nonempty, dite_eq_left origin.agrees]

/-- Infrastructure-origin admission succeeds exactly for an eligible module with a nonempty
origin equal to the expected one. -/
theorem admitInfrastructureOrigin_isOk_iff (key : ModuleKey) (actual expected : String) :
    (admitInfrastructureOrigin key actual expected).isOk = true ↔
      key.name.name ∈ infrastructureModuleNames ∧ actual ≠ "" ∧ actual = expected := by
  unfold admitInfrastructureOrigin
  by_cases eligible : key.name.name ∈ infrastructureModuleNames
  · by_cases empty : actual = ""
    · simp [eligible, empty, Except.isOk, Except.toBool]
    · by_cases equal : actual = expected
      · subst equal
        simp [eligible, empty, Except.isOk, Except.toBool]
      · simp [eligible, empty, equal, Except.isOk, Except.toBool]
  · simp [eligible, Except.isOk, Except.toBool]

/-- `admitInfrastructureOrigin` accepts exactly an eligible infrastructure module whose
observed origin is nonempty and equal to the expected one: it accepts `Regula.Collect` with
equal origins and refuses an empty origin. Which receipt it returns is
`admitInfrastructureOrigin_exact`. That the two paths are the module's loaded and expected
`.olean` files is the adapter's. -/
theorem checked_admitInfrastructureOrigin :
    Regula.ExecutableContract admitInfrastructureOrigin (fun admit =>
      Regula.Decides (·.isOk = true)
        (fun input : (ModuleKey × String) × String =>
          input.1.1.name.name ∈ infrastructureModuleNames ∧ input.1.2 ≠ "" ∧
            input.1.2 = input.2)
        (Function.uncurry (Function.uncurry admit))) :=
  let key : ModuleKey :=
    ⟨⟨⟨#[], ⟨"lakefile", ""⟩, ⟨"lean", "commit", "revision"⟩, #[]⟩, by decide⟩,
      ⟨`Regula.Collect, by decide +kernel⟩⟩
  ⟨.of_iff (fun input => admitInfrastructureOrigin_isOk_iff input.1.1 input.1.2 input.2)
    ⟨((key, "origin"), "origin"),
      (admitInfrastructureOrigin_isOk_iff key "origin" "origin").mpr
        ⟨by decide +kernel, by decide, rfl⟩⟩
    ⟨((key, ""), ""),
      fun accepted => ((admitInfrastructureOrigin_isOk_iff key "" "").mp accepted).2.1 rfl⟩⟩

/-- A standalone file is compiled in an isolated module. Retain both identities and
exact byte equality; this does not authenticate either filesystem read. -/
structure FileSourceBinding where
  /-- The snapshot of the file the audit was asked to check. -/
  requested : SourceSnapshot
  /-- The snapshot of the isolated copy that was compiled. -/
  compiled : SourceSnapshot
  /-- Proof that both snapshots hold the same source text. -/
  sameBytes : requested.source = compiled.source
  deriving DecidableEq

/-- Bind the requested file to its compiled copy when their source texts are equal, and
refuse otherwise. -/
def admitFileSourceBinding (requested compiled : SourceSnapshot) :
    Except String FileSourceBinding :=
  if h : requested.source = compiled.source then .ok ⟨requested, compiled, h⟩
  else .error "standalone source copy differs from requested file"

theorem fileSourceBinding_bytes (binding : FileSourceBinding) :
    binding.requested.source = binding.compiled.source := binding.sameBytes

/-- Frozen observations and independently collected keys. No field records policy success.
Material declarations are the explicit public evidence-registration census; its adequacy
remains semantic review. Imported modules are separate from claimed owned modules. -/
structure EnvironmentCensus where
  /-- The request this environment answers: its key and positive module assignment. -/
  request : EnvironmentRequest
  /-- The admitted declaration inventory of the environment's owned modules. -/
  policy : Inventory
  /-- The admitted execution roots and their closure accounts. -/
  execution : ExecutionInventory
  /-- The positive (owned) modules the request assigns to this environment. -/
  modules : Array ModuleKey
  /-- The modules of the owned dependencies that this environment's positive modules import
  (`EnvironmentRequest.dependencies`); their declarations are inspected here too. -/
  dependencyModules : Array ModuleKey := #[]
  /-- Loaded modules that are neither owned nor infrastructure: the import closure. -/
  importedModules : Array ModuleKey
  /-- Origin receipts of the loaded checker infrastructure modules. -/
  infrastructure : Array InfrastructureOrigin := #[]
  /-- The name, `.olean` path and direct imports of every loaded module. -/
  origins : Array ModuleOrigin := #[]
  /-- Captured source snapshots of infrastructure modules, where a source was captured. -/
  infrastructureSources : Array (ModuleKey × SourceSnapshot) := #[]
  /-- The captured source snapshot of each inspected module, in `inspectedModules` order. -/
  moduleSources : Array (ModuleKey × SourceSnapshot)
  /-- For a single-file audit, the binding of the requested file to its compiled copy. -/
  fileSource : Option FileSourceBinding := none
  /-- Captured source snapshots of imported modules, where a source was captured. -/
  importedSources : Array (ModuleKey × SourceSnapshot)
  /-- Loaded modules built into the project's own output that no Lake target configures and
  that are neither owned nor infrastructure; `EnvironmentCensusOK` requires none. -/
  unclassifiedRootImports : Array ModuleKey
  /-- The modules whose declarations the kernel-admission replay covered. -/
  admissionModules : Array ModuleKey := #[]
  /-- The declarations the replay had to admit: every owned one that is neither `unsafe` nor
  `partial`. -/
  admissionDeclarations : Array DeclarationKey
  /-- The keys of the policy inventory's declarations, in inventory order. -/
  declarations : Array DeclarationKey
  /-- The keys of the admitted execution roots, in root order. -/
  roots : Array RootKey
  /-- The declarations registered as material evidence (`@[regula_material]`). -/
  materialDeclarations : Array DeclarationKey
  deriving DecidableEq

/-- The module keys of the environment's infrastructure receipts. -/
def EnvironmentCensus.infrastructureModules (i : EnvironmentCensus) : Array ModuleKey :=
    i.infrastructure.map (·.moduleKey)

/-- The modules whose declarations, executable roots, sources and documentation the environment
inspects: its positive modules, then the modules of owned dependencies that it owns
(`EnvironmentRequest.dependencies`). Every per-module job of the plan takes its modules from here:
the captured sources (`EnvironmentCensusOK`), the declarations, the transcripts and the
documentation (`localStageSubjects`). -/
def EnvironmentCensus.inspectedModules (i : EnvironmentCensus) : Array ModuleKey :=
  i.modules ++ i.dependencyModules

/-- Every module of the environment: owned, then of owned dependencies, then imported, then
infrastructure. -/
def EnvironmentCensus.allModules (i : EnvironmentCensus) : Array ModuleKey :=
  i.modules ++ i.dependencyModules ++ i.importedModules ++ i.infrastructureModules

/-- Every captured source of the environment: owned, then imported, then infrastructure. -/
def EnvironmentCensus.allModuleSources (i : EnvironmentCensus) : Array
    (ModuleKey × SourceSnapshot) :=
  i.moduleSources ++ i.importedSources ++ i.infrastructureSources

/-- One complete original request with separately admitted Lean environments. -/
structure Census where
  /-- The environment requests of the run, in coordinator order. -/
  requests : Array EnvironmentRequest
  /-- One environment census per request, in the same order. -/
  environments : Array EnvironmentCensus
  /-- Every positive (owned) module of the run, over all environments. -/
  modules : Array ModuleKey
  /-- The captured source of every inspected module, over all environments. -/
  moduleSources : Array (ModuleKey × SourceSnapshot)
  /-- The manifest's classification of each Lake target. -/
  configuredTargets : Array TargetAssignment
  /-- The Lake targets of the root package as Lake resolves them. -/
  discoveredTargets : Array DiscoveredTarget
  /-- The documentation fences a documentation audit checks. -/
  fences : Array FenceKey := #[]
  /-- In the serialized-graph mode, the root modules the serialized-graph checker runs on. -/
  graphRoots : Array ModuleKey := #[]
  /-- In the serialized-graph mode, the positive modules each graph root's check covers. -/
  graphCoverage : Array (ModuleKey × Array ModuleKey) := #[]
  deriving DecidableEq

/-- Every module of every environment of the census. -/
def Census.allModules (i : Census) : Array ModuleKey := i.environments.flatMap (·.allModules)

/-- A generated-role receipt (`Roles`) for the policy inventory of every environment. -/
abbrev CensusRoles (i : Census) := (slot : Fin i.environments.size) →
    Roles i.environments[slot].policy

/-- The claim's source snapshots: its own sources, then every dependency's files. -/
def snapshotSources (c : Claim) : Array SourceSnapshot :=
  c.val.snapshot.sources ++ c.val.snapshot.dependencies.flatMap (·.files)

/-- The Lean module names of the keys, in order. -/
def moduleNames (ms : Array ModuleKey) : Array Name := ms.map (·.name.name)

/-- The (module, declaration) name pairs of the keys, in order. -/
def declarationNames (ds : Array DeclarationKey) : Array (Name × Name) :=
  ds.map (fun d => (d.moduleKey.name.name, d.name.name))

/-- The claimed surface among `surfaces` that owns module `m`: the first whose modules include
it. -/
def surfaceOwning (surfaces : Array SurfaceAssignment) (m : Name) : Option SurfaceAssignment :=
  surfaces.find? fun s => s.modules.any (·.name == m)

/-- The claimed surface, by its target, that owns the first of an environment's `modules`; `none`
when it has none or no claimed surface owns it. A project census assigns each environment the
modules of one surface (`census_project_partition`). -/
def environmentTarget (surfaces : Array SurfaceAssignment) (modules : Array ModuleKey) :
    Option String :=
  (modules[0]?.bind fun m => surfaceOwning surfaces m.name.name).map (·.target)

/-- The recorded contracts that count toward the registered decisions of the environment whose
own declarations are `owned`, whose loaded modules have the origins `origins` and whose surface
is `target`. `environments` gives, for each environment, its policy declarations and the origins
of the modules it loaded. A contract counts when it is the recorded contract of a declaration of
one of them, the claimed surface that owns that declaration's module names `target` among the
surfaces it decides (`SurfaceAssignment.decides`), and its implementation is an owned
declaration of a module of the surface `target` itself, not of an owned dependency, whose module
that environment loaded with an origin, `.olean` path and imports, equal to one of `origins`. Lean refuses an environment that holds two declarations of one name, so the
implementation that contract names is the owned declaration. Each counted contract carries the
surface, the declaration and the module that record it, in the order of `environments` and of
their declarations. -/
def countedContracts (surfaces : Array SurfaceAssignment)
    (environments : Array (Array Declaration × Array ModuleOrigin)) (target : String)
    (owned : Array Declaration) (origins : Array ModuleOrigin) : Array CountedContract :=
  environments.flatMap fun (declarations, loaded) => declarations.filterMap fun d =>
    d.executableContract.bind fun k =>
      (surfaceOwning surfaces d.module).bind fun s =>
        if s.decides.contains target && owned.any (fun o => o.name == k.root &&
            (surfaceOwning surfaces o.module).any (·.target == target) &&
            loaded.any fun m => m.name == o.module && origins.contains m)
        then some ⟨s.target, d.name, d.module, k⟩ else none

/-- A contract counts toward an environment's registered decisions exactly when it is the recorded
contract of a declaration of one of `environments` whose module a claimed surface owns that names
`target` among those it decides, and it names an owned declaration of a module of the surface
`target` whose module that environment loaded with an origin of `origins`; it carries that surface,
declaration and module. -/
theorem mem_countedContracts {surfaces : Array SurfaceAssignment}
    {environments : Array (Array Declaration × Array ModuleOrigin)} {target : String}
    {owned : Array Declaration} {origins : Array ModuleOrigin} {c : CountedContract} :
    c ∈ countedContracts surfaces environments target owned origins ↔
      ∃ e ∈ environments, ∃ d ∈ e.1, ∃ k, d.executableContract = some k ∧
        ∃ s, surfaceOwning surfaces d.module = some s ∧ target ∈ s.decides ∧
          (∃ o ∈ owned, o.name = k.root ∧
            (∃ so, surfaceOwning surfaces o.module = some so ∧ so.target = target) ∧
            ∃ m ∈ e.2, m.name = o.module ∧ m ∈ origins) ∧
          c = ⟨s.target, d.name, d.module, k⟩ := by
  simp only [countedContracts, Array.mem_flatMap, Array.mem_filterMap, Option.bind_eq_some_iff,
    Bool.and_eq_true, Array.contains_iff_mem, Array.any_eq_true', beq_iff_eq,
    Option.ite_none_right_eq_some, Option.some.injEq, Option.any_eq_true]
  constructor
  · rintro ⟨⟨declarations, loaded⟩, he, d, hd, k, hk, s, hs, ⟨hdecides, o, ho, ⟨hname, so, hso,
      htarget⟩, m, hm, hmodule, horigin⟩, rfl⟩
    exact ⟨_, he, d, hd, k, hk, s, hs, hdecides,
      ⟨o, ho, hname, ⟨so, hso, htarget⟩, m, hm, hmodule, horigin⟩, rfl⟩
  · rintro ⟨⟨declarations, loaded⟩, he, d, hd, k, hk, s, hs, hdecides, ⟨o, ho, hname,
      ⟨so, hso, htarget⟩, m, hm, hmodule, horigin⟩, rfl⟩
    exact ⟨_, he, d, hd, k, hk, s, hs,
      ⟨hdecides, o, ho, ⟨hname, so, hso, htarget⟩, m, hm, hmodule, horigin⟩, rfl⟩

/-- The recorded contracts that the census `environments` count toward the registered decisions
of environment `i` under the claim `c` (`countedContracts`): for the surface that owns `i`'s
modules (`environmentTarget`), over the policy declarations and module origins of every
environment, and none for an environment that no claimed surface owns, such as every environment
of a file, editor or documentation claim. -/
def countedFor (c : Claim) (environments : Array EnvironmentCensus) (i : EnvironmentCensus) :
    Array CountedContract :=
  match environmentTarget c.val.surfaces i.modules with
  | some target => countedContracts c.val.surfaces
      (environments.map fun e => (e.policy.declarations, e.origins)) target
      i.policy.declarations i.origins
  | none => #[]

/-- The complete loaded import census binds every infrastructure receipt. Direct import
edges are inspected for every loaded module, including ordinary dependencies. Collect
is infrastructure only in its existing force-only case. Positive ownership is disjoint. -/
def InfrastructureOK (c : Claim) (i : EnvironmentCensus) : Prop :=
  (∀ m ∈ i.infrastructureModules, m ∉ i.modules ∧ m ∉ i.importedModules ∧
    m.snapshot.val = c.val.snapshot) ∧
  UniqueNames (i.origins.map (·.name)) ∧
  canonicalNames (i.origins.map (·.name)) = canonicalNames (moduleNames i.allModules) ∧
  (∀ receipt ∈ i.infrastructure, ∃ origin ∈ i.origins,
    origin.name = receipt.moduleKey.name.name ∧ origin.olean = receipt.actual) ∧
  (∀ origin ∈ i.origins, ∀ imported ∈ origin.imports,
    imported ∈ reporterOnlyModuleNames → origin.name ∈ reporterModuleNames ∧
      ∃ receipt ∈ i.infrastructure, receipt.moduleKey.name.name = origin.name) ∧
  (∀ receipt ∈ i.infrastructure, receipt.moduleKey.name.name = `Regula.Collect →
    ∀ origin ∈ i.origins, `Regula.Collect ∈ origin.imports → origin.name ∈ reporterModuleNames) ∧
  (∀ receipt ∈ i.infrastructure, receipt.moduleKey.name.name = `Regula.CompilerObservation →
    ∀ origin ∈ i.origins, `Regula.CompilerObservation ∈ origin.imports →
      (origin.name ∈ reporterModuleNames ∨ origin.name = `Regula.Collect) ∧
        ∃ importer ∈ i.infrastructure, importer.moduleKey.name.name = origin.name) ∧
  i.infrastructureSources.toList.Pairwise (fun a b => a.1 ≠ b.1) ∧
  (∀ entry ∈ i.infrastructureSources,
    entry.1 ∈ i.infrastructureModules ∧ entry.2 ∈ snapshotSources c)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : EnvironmentCensus) : Decidable (InfrastructureOK c i) := by
  unfold InfrastructureOK; infer_instance

/-- The admitted partition never supplies positive ownership or an ordinary import. -/
theorem infrastructure_disjoint (c : Claim) (i : EnvironmentCensus) (h : InfrastructureOK c i)
    (m : ModuleKey) (hm : m ∈ i.infrastructureModules) : m ∉ i.modules ∧ m ∉ i.importedModules :=
  ⟨(h.1 m hm).1, (h.1 m hm).2.1⟩

/-- An executable's root module lies in a library only when the manifest classifies the two
alike: the executable is claimed with that library's surface, or both are excluded. A claimed
root inside a claimed library therefore keeps that library's claim, and no root is claimed with
one surface while a library containing it is excluded or claimed with another, or excluded while
such a library is claimed. -/
def RootsClassifiedAlike (configured : Array TargetAssignment)
    (discovered : Array DiscoveredTarget) : Prop :=
  ∀ a ∈ configured, a.kind = .executable →
    ∀ t ∈ discovered, t.kind = .executable → t.name = a.name →
      ∀ n ∈ t.modules, ∀ lib ∈ discovered, lib.kind = .library → n ∈ lib.modules →
        ∀ l ∈ configured, l.kind = .library → l.name = lib.name → l.surface = a.surface
set_option synthInstance.maxSize 1024 in
instance (configured : Array TargetAssignment) (discovered : Array DiscoveredTarget) :
    Decidable (RootsClassifiedAlike configured discovered) := by
  unfold RootsClassifiedAlike; infer_instance

/-- Exact target partition, including excluded targets and executable roots classified alike
with every library containing them (`RootsClassifiedAlike`). Each positive surface owns its
library's modules and its claimed executables' root modules, a root inside the library once. -/
def TargetPartitionOK (c : Claim) (i : Census) : Prop :=
  i.configuredTargets.toList.Pairwise (fun a b => (a.kind, a.name) ≠ (b.kind, b.name)) ∧
  i.discoveredTargets.toList.Pairwise (fun a b => (a.kind, a.name) ≠ (b.kind, b.name)) ∧
  (∀ a ∈ i.configuredTargets, ∃ t ∈ i.discoveredTargets, a.kind = t.kind ∧ a.name = t.name) ∧
  (∀ t ∈ i.discoveredTargets, t.name ≠ "" ∧ t.modules ≠ #[] ∧
    (t.kind = .executable → t.modules.size = 1) ∧
    ∃ a ∈ i.configuredTargets, a.kind = t.kind ∧ a.name = t.name) ∧
  (∀ a ∈ i.configuredTargets, ∀ owner ∈ a.surface, ∃ s ∈ c.val.surfaces, s.target = owner) ∧
  (∀ s ∈ c.val.surfaces,
    (∃ a ∈ i.configuredTargets, a.kind = .library ∧ a.name = s.target ∧ a.surface = some s.target) ∧
    canonicalNames (s.modules.map (·.name)) = canonicalNames
      ((i.discoveredTargets.filter (fun t => i.configuredTargets.any (fun a =>
        a.kind == t.kind && a.name == t.name && a.surface == some s.target))).flatMap (·.modules)))
            ∧
  (∀ a ∈ i.configuredTargets, a.kind = .library → ∀ owner ∈ a.surface, a.name = owner) ∧
  RootsClassifiedAlike i.configuredTargets i.discoveredTargets
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : Census) : Decidable (TargetPartitionOK c i) := by
  unfold TargetPartitionOK; infer_instance

/-- Optional graph selection and import coverage are frozen before checker processes.
The relation proves exact accounting of supplied coverage, not Lean import extraction. -/
def GraphPlanOK (c : Claim) (i : Census) : Prop :=
  if c.val.mode = .serializedGraph then
    i.graphRoots ≠ #[] ∧ i.graphRoots.toList.Pairwise (· ≠ ·) ∧
    i.graphCoverage.map (·.1) = i.graphRoots ∧
    (∀ root ∈ i.graphRoots, root ∈ i.modules) ∧
    (∀ entry ∈ i.graphCoverage, entry.1 ∈ entry.2 ∧ ∀ m ∈ entry.2, m ∈ i.modules) ∧
    ∀ m ∈ i.modules, ∃ entry ∈ i.graphCoverage, m ∈ entry.2
  else i.graphRoots = #[] ∧ i.graphCoverage = #[]
instance (c : Claim) (i : Census) : Decidable (GraphPlanOK c i) := by
  unfold GraphPlanOK; infer_instance

/-- Bucket keys by their names only. Hits and collisions are resolved by full structural
equality, including the admitted snapshot, so membership still compares every field. -/
instance : Hashable ModuleKey := ⟨fun k => hash k.name.name⟩
instance : LawfulHashable ModuleKey where
  hash_eq _ _ h := eq_of_beq h ▸ rfl
instance : Hashable DeclarationKey :=
    ⟨fun k => mixHash (hash k.moduleKey.name.name) (hash k.name.name)⟩
instance : LawfulHashable DeclarationKey where
  hash_eq _ _ h := eq_of_beq h ▸ rfl

/-- Exact admitted key/data reconciliation and claim bindings. These checks cannot establish
that the external environment traversal or source scan omitted nothing; that is the collector
boundary. They do prevent a returned policy table from defining its own required census. The
contracts the inventory counts from other surfaces are exactly those the claim relates to it
among the census's own environments (`countedFor`), so no contract counts that this run did not
record. -/
def EnvironmentCensusOK (c : Claim) (global : Census) (i : EnvironmentCensus) : Prop :=
  i.request.modules = i.modules ∧ i.request.key.snapshot.val = c.val.snapshot ∧
  i.policy.counted = countedFor c global.environments i ∧
  InfrastructureOK c i ∧
  UniqueNames (moduleNames i.allModules) ∧
  (∀ m ∈ i.allModules, m.snapshot.val = c.val.snapshot) ∧
  i.moduleSources.map (·.1) = i.inspectedModules ∧
  (∀ entry ∈ i.moduleSources, entry.2 ∈ c.val.snapshot.sources) ∧
  i.importedSources.toList.Pairwise (fun a b => a.1 ≠ b.1) ∧
  (∀ entry ∈ i.importedSources, entry.1 ∈ i.importedModules ∧ entry.2 ∈ snapshotSources c) ∧
  i.unclassifiedRootImports = #[] ∧
  (∀ m ∈ i.importedModules, ∀ target ∈ global.discoveredTargets, m.name.name ∈ target.modules →
    ∃ assignment ∈ global.configuredTargets, assignment.kind = target.kind ∧
      assignment.name = target.name ∧ assignment.surface.isSome = true) ∧
  UniqueNames (moduleNames i.admissionModules) ∧
  (∀ m ∈ i.admissionModules, m.snapshot.val = c.val.snapshot) ∧
  (∀ d ∈ i.admissionDeclarations, d.moduleKey ∈ i.allModules ∧ d.moduleKey ∈ i.admissionModules) ∧
  i.admissionDeclarations.toList.Pairwise (· ≠ ·) ∧
  (∀ d ∈ i.policy.declarations, d.isUnsafe = false → d.isPartial = false →
    (d.module, d.name) ∈ declarationNames i.admissionDeclarations) ∧
  declarationNames i.declarations = i.policy.declarations.map (fun d => (d.module, d.name)) ∧
  declarationNames i.roots = i.execution.roots.map (fun r => (r.module, r.name)) ∧
  (∀ d ∈ i.declarations, d.moduleKey ∈ i.inspectedModules) ∧
  (∀ r ∈ i.roots, r.moduleKey ∈ i.allModules) ∧
  (∀ d ∈ i.materialDeclarations, d ∈ i.declarations) ∧
  i.materialDeclarations.toList.Pairwise (· ≠ ·) ∧
  (∀ r ∈ i.execution.roots, ∀ b ∈ r.boundaries, b.module ∈ moduleNames i.allModules) ∧
  (match c.val.scope with
   | .project => True
   | .file source .. => i.modules.size = 1 ∧
       ∃ binding ∈ i.fileSource, binding.requested = source ∧ i.moduleSources.map (·.2) =
           #[binding.compiled]
   | .editor n source .. => moduleNames i.modules = #[n.name] ∧
       i.moduleSources.map (·.2) = #[source]
   | .documentation _ => False) ∧
  i.request.dependencies = i.dependencyModules ∧
  (∀ m ∈ i.dependencyModules, m.name ∈ c.val.dependencies)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (global : Census) (i : EnvironmentCensus) : Decidable
    (EnvironmentCensusOK c global i) := by
  unfold EnvironmentCensusOK
  -- Index each repeatedly queried array once; membership and distinctness equivalences
  -- supply decisions for the unchanged predicate, without a second validity definition.
  let allModules := Std.ExtHashSet.ofList i.allModules.toList
  let admissionModules := Std.ExtHashSet.ofList i.admissionModules.toList
  let modules := Std.ExtHashSet.ofList i.modules.toList
  let declarations := Std.ExtHashSet.ofList i.declarations.toList
  let allNames := Std.ExtHashSet.ofList (moduleNames i.allModules).toList
  let admissionNames := Std.ExtHashSet.ofList (declarationNames i.admissionDeclarations).toList
  letI (m : ModuleKey) : Decidable (m ∈ i.allModules) :=
    decidable_of_iff (m ∈ allModules) (by simp [allModules, Std.ExtHashSet.mem_ofList])
  letI (m : ModuleKey) : Decidable (m ∈ i.admissionModules) :=
    decidable_of_iff (m ∈ admissionModules) (by simp [admissionModules, Std.ExtHashSet.mem_ofList])
  letI (m : ModuleKey) : Decidable (m ∈ i.modules) :=
    decidable_of_iff (m ∈ modules) (by simp [modules, Std.ExtHashSet.mem_ofList])
  letI (d : DeclarationKey) : Decidable (d ∈ i.declarations) :=
    decidable_of_iff (d ∈ declarations) (by simp [declarations, Std.ExtHashSet.mem_ofList])
  letI (n : Name) : Decidable (n ∈ moduleNames i.allModules) :=
    decidable_of_iff (n ∈ allNames) (by simp [allNames, Std.ExtHashSet.mem_ofList])
  letI (k : Name × Name) : Decidable (k ∈ declarationNames i.admissionDeclarations) :=
    decidable_of_iff (k ∈ admissionNames) (by simp [admissionNames, Std.ExtHashSet.mem_ofList])
  letI : Decidable (i.admissionDeclarations.toList.Pairwise (· ≠ ·)) := distinctDecidable _
  letI : Decidable (i.materialDeclarations.toList.Pairwise (· ≠ ·)) := distinctDecidable _
  cases c.val.scope <;> infer_instance

set_option synthInstance.maxSize 1024 in
/-- The indexed implementation decides the same proposition as the prior finite scan. -/
theorem environmentCensusOK_decide_eq_previous (c : Claim) (global : Census)
    (i : EnvironmentCensus) :
    decide (EnvironmentCensusOK c global i) = @decide (EnvironmentCensusOK c global i)
      (by unfold EnvironmentCensusOK; cases c.val.scope <;> infer_instance) := by
  congr

/-- Exact request occurrences and positive partition precede admission of any results.
Environment position is identity; no producer may select or deduplicate this domain. -/
def CensusOK (c : Claim) (i : Census) : Prop :=
  i.environments.map (·.request) = i.requests ∧
  (∀ n : Fin i.requests.size, i.requests[n].key.index = n.val) ∧
  (∀ e ∈ i.environments, EnvironmentCensusOK c i e) ∧
  i.modules = i.environments.flatMap (·.modules) ∧
  UniqueNames (moduleNames i.modules) ∧
  i.moduleSources = i.environments.flatMap (·.moduleSources) ∧
  GraphPlanOK c i ∧
  i.fences.toList.Pairwise (· ≠ ·) ∧
  (∀ f ∈ i.fences, f.document ∈ c.val.snapshot.sources) ∧
  (match c.val.scope with
   | .project => TargetPartitionOK c i ∧
       canonicalNames (moduleNames i.modules) = canonicalNames
         (c.val.surfaces.flatMap (fun s => s.modules.map (·.name))) ∧ i.fences = #[] ∧
       (if c.val.mode = .serializedGraph then i.requests.size = 1 else
         i.requests.map (fun r => moduleNames r.modules) =
           c.val.surfaces.flatMap (·.environmentNames))
   | .file .. | .editor .. => i.requests.size = 1 ∧ i.fences = #[]
   | .documentation docs => i.requests = #[] ∧ ∀ f ∈ i.fences, f.document ∈ docs)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : Census) : Decidable (CensusOK c i) := by
  unfold CensusOK
  cases c.val.scope <;> infer_instance

/-- Admission preserves the exact ordered request occurrences, without normalization. -/
theorem census_exact_requests (c : Claim) (i : Census) (h : CensusOK c i) :
    i.environments.map (·.request) = i.requests := h.1

/-- The complete original positive module domain is partitioned across environments. -/
theorem census_exact_modules (c : Claim) (i : Census) (h : CensusOK c i) :
    i.modules = i.environments.flatMap (·.modules) ∧ UniqueNames (moduleNames i.modules) :=
  ⟨h.2.2.2.1, h.2.2.2.2.1⟩

theorem census_request_index (c : Claim) (i : Census) (h : CensusOK c i)
    (slot : Fin i.requests.size) : i.requests[slot].key.index = slot.val := h.2.1 slot

theorem census_environment_index (c : Claim) (i : Census) (h : CensusOK c i)
    (slot : Fin i.environments.size) : i.environments[slot].request.key.index = slot.val := by
  have bound : slot.val < i.requests.size := by simp [← h.1]
  have position := h.2.1 ⟨slot.val, bound⟩
  simpa [← h.1] using position

/-- Two distinct response occurrences cannot be normalized into one request identity. -/
theorem census_environment_unique (c : Claim) (i : Census) (h : CensusOK c i)
    (left right : Fin i.environments.size)
    (same : i.environments[left].request.key = i.environments[right].request.key) : left =
        right := by
  apply Fin.ext
  rw [← census_environment_index c i h left, ← census_environment_index c i h right]
  exact congrArg (·.index) same

/-- Each requested occurrence has its unchanged environment data and local obligations. -/
theorem census_requested_environment (c : Claim) (i : Census) (h : CensusOK c i)
    (request : EnvironmentRequest) (hr : request ∈ i.requests) :
    ∃ e ∈ i.environments, e.request = request ∧ EnvironmentCensusOK c i e := by
  rw [← h.1] at hr
  obtain ⟨e, he, eq⟩ := Array.mem_map.mp hr
  exact ⟨e, he, eq, h.2.2.1 e he⟩

/-- In a valid census, the contracts each environment counts from other surfaces are exactly
those the claim relates to it among the census's own environments (`countedFor`). -/
theorem census_counted (c : Claim) (i : Census) (h : CensusOK c i) {e : EnvironmentCensus}
    (he : e ∈ i.environments) : e.policy.counted = countedFor c i.environments e :=
  (h.2.2.1 e he).2.2.1

/-- The decision requirement (RG1008) of a valid census reads exactly the recorded contracts of
the surfaces the claim relates. A name is among an environment's decided implementations exactly
when a decision contract of the environment's own declarations decides it, or when an
environment of the same census has a declaration whose recorded contract states a decision kind,
was not refused and names it as its implementation, where the claimed surface that owns that
declaration's module names the environment's surface among those it decides
(`SurfaceAssignment.decides`), and the name is an owned declaration of a module of the
environment's surface, which the other environment loaded with an origin equal to one the
environment loaded. The
records are those the census holds, so no contract of another run or of an environment the census
does not hold counts. -/
theorem census_decided_iff (c : Claim) (i : Census) (h : CensusOK c i) {e : EnvironmentCensus}
    (he : e ∈ i.environments) (roles : Roles e.policy) (n : Name) :
    n ∈ roles.decided ↔
      DecisionRegistered (recordedContracts e.policy.declarations) n ∨
      ∃ target, environmentTarget c.val.surfaces e.modules = some target ∧
        ∃ e' ∈ i.environments, ∃ d ∈ e'.policy.declarations, ∃ k,
          d.executableContract = some k ∧
          (∃ s, surfaceOwning c.val.surfaces d.module = some s ∧ target ∈ s.decides) ∧
          (∃ o ∈ e.policy.declarations, o.name = n ∧
            (∃ so, surfaceOwning c.val.surfaces o.module = some so ∧ so.target = target) ∧
            ∃ m ∈ e'.origins, m.name = o.module ∧ m ∈ e.origins) ∧
          k.root = n ∧ k.kind.isSome = true ∧ k.failure = none := by
  rw [roles.decided_iff, Inventory.decisionContracts_iff, census_counted c i h he]
  apply or_congr Iff.rfl
  unfold countedFor
  cases environmentTarget c.val.surfaces e.modules with
  | none => simp
  | some target =>
    simp only [mem_countedContracts, Array.mem_map, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨_, ⟨_, ⟨e', he', rfl⟩, d, hd, k, hk, s, hs, hdecides, ⟨o, ho, hname, hsurface, m,
        hm, hmodule, horigin⟩, rfl⟩, hroot, hkind, hfailure⟩
      exact ⟨e', he', d, hd, k, hk, ⟨s, hs, hdecides⟩,
        ⟨o, ho, hname.trans hroot, hsurface, m, hm, hmodule, horigin⟩, hroot, hkind, hfailure⟩
    · rintro ⟨e', he', d, hd, k, hk, ⟨s, hs, hdecides⟩, ⟨o, ho, hname, hsurface, m, hm, hmodule,
        horigin⟩, hroot, hkind, hfailure⟩
      exact ⟨_, ⟨_, ⟨e', he', rfl⟩, d, hd, k, hk, s, hs, hdecides,
        ⟨o, ho, hname.trans hroot.symm, hsurface, m, hm, hmodule, horigin⟩, rfl⟩, hroot, hkind,
        hfailure⟩

/-- Where no claimed surface names an environment's surface among those it decides, such as in a
claim whose surfaces decide none, the decision requirement of a valid census reads the recorded
contracts of the environment's own declarations alone: exactly what it reads without the
relation. -/
theorem census_decided_iff_of_unrelated (c : Claim) (i : Census) (h : CensusOK c i)
    {e : EnvironmentCensus} (he : e ∈ i.environments) (roles : Roles e.policy)
    (unrelated : ∀ s ∈ c.val.surfaces, ∀ t ∈ s.decides,
      environmentTarget c.val.surfaces e.modules ≠ some t) (n : Name) :
    n ∈ roles.decided ↔ DecisionRegistered (recordedContracts e.policy.declarations) n := by
  rw [census_decided_iff c i h he roles n]
  refine or_iff_left ?_
  rintro ⟨target, htarget, -, -, d, -, -, -, ⟨s, hs, hdecides⟩, -⟩
  have member : s ∈ c.val.surfaces := Array.mem_of_find?_eq_some hs
  exact unrelated s member target hdecides htarget

/-- Ordinary project requests are the claim's surface environments, in order: each surface's
library, then each of its executable roots alone (`SurfaceAssignment.environments`). -/
theorem census_project_partition (c : Claim) (i : Census) (h : CensusOK c i)
    (scope : c.val.scope = .project) (mode : c.val.mode ≠ .serializedGraph) :
    i.requests.map (fun r => moduleNames r.modules) =
      c.val.surfaces.flatMap (·.environmentNames) := by
  have hs := h.2.2.2.2.2.2.2.2.2
  rw [scope] at hs
  simpa [mode] using hs.2.2.2

/-- In an ordinary project census, every claimed executable's root module is requested in an
environment whose only positive module it is, so no other executable root or library module is
assigned beside it. -/
theorem census_executable_alone (c : Claim) (i : Census) (h : CensusOK c i)
    (scope : c.val.scope = .project) (mode : c.val.mode ≠ .serializedGraph)
    (s : SurfaceAssignment) (hs : s ∈ c.val.surfaces) (root : Identity)
    (hr : root ∈ s.executables) :
    ∃ r ∈ i.requests, moduleNames r.modules = #[root.name] := by
  have hin : #[root.name] ∈ c.val.surfaces.flatMap (·.environmentNames) := by
    refine Array.mem_flatMap.mpr ⟨s, hs, Array.mem_map.mpr ⟨#[root], ?_, by simp⟩⟩
    exact (s.mem_environments _).mpr (.inr ⟨root, hr, rfl⟩)
  rw [← census_project_partition c i h scope mode] at hin
  obtain ⟨r, hr', eq⟩ := Array.mem_map.mp hin
  exact ⟨r, hr', eq⟩

/-- No module of a claimed Lake target escapes a valid project census: every module of a
discovered library or executable that the manifest assigns to a surface is a positive module of
the census (`Census.modules`, which `CensusOK` requires to be exactly its environments' modules),
by `TargetPartitionOK`'s surface-module equality and `CensusOK`'s equality of the census modules
with the surfaces' modules. This includes an executable root inside its surface's library. -/
theorem census_covers_claimed_targets (c : Claim) (i : Census) (h : CensusOK c i)
    (scope : c.val.scope = .project) (t : DiscoveredTarget) (ht : t ∈ i.discoveredTargets)
    (a : TargetAssignment) (ha : a ∈ i.configuredTargets) (kind : a.kind = t.kind)
    (name : a.name = t.name) (claimed : a.surface.isSome = true) :
    ∀ m ∈ t.modules, m ∈ moduleNames i.modules := by
  have hs := h.2.2.2.2.2.2.2.2.2
  rw [scope] at hs
  obtain ⟨tp, hmodules, -, -⟩ := hs
  obtain ⟨owner, hown⟩ := Option.isSome_iff_exists.mp claimed
  obtain ⟨s, hs, htarget⟩ := tp.2.2.2.2.1 a ha owner hown
  intro m hm
  have hsurface : m ∈ s.modules.map (·.name) := by
    rw [← mem_canonicalNames, (tp.2.2.2.2.2.1 s hs).2, mem_canonicalNames]
    refine Array.mem_flatMap.mpr ⟨t, Array.mem_filter.mpr ⟨ht, ?_⟩, hm⟩
    exact Array.any_eq_true'.mpr ⟨a, ha, by simp [kind, name, hown, htarget]⟩
  rw [← mem_canonicalNames, hmodules, mem_canonicalNames]
  exact Array.mem_flatMap.mpr ⟨s, hs, hsurface⟩

/-- A project module's profile, from the claimed surfaces and the modules of the owned
dependencies of a project claim (`ClaimCandidate.surfaces`, `ClaimCandidate.dependencies`):
that of the surface owning the module, or Standard-Logical for a module of an owned dependency,
none for any other module. The coordinator gives each declaration's findings this profile from
the same values it admits as the claim, so they agree with `profileForModule`
(`profileForModule_project`). -/
def projectProfile (surfaces : Array SurfaceAssignment) (dependencies : Array Identity)
    (m : Name) : Option ConformingProfile :=
  ((surfaces.find? (fun s => s.modules.any (fun n => n.name == m))).map (·.profile)).or
    (if dependencies.any (·.name == m) then some .standardLogical else none)

/-- A project module's execution claim, from the same values as `projectProfile`: that of the
surface owning the module, report for a module of an owned dependency, none for any other
module. -/
def projectExecution (surfaces : Array SurfaceAssignment) (dependencies : Array Identity)
    (m : Name) : Option ExecutionClaim :=
  ((surfaces.find? (fun s => s.modules.any (fun n => n.name == m))).map (·.execution)).or
    (if dependencies.any (·.name == m) then some .report else none)

/-- A module's profile is derived from its positive assignment, never a result payload: in a
project, `projectProfile` of the claim's surfaces and owned dependencies. -/
def profileForModule (c : Claim) (m : Name) : Option ConformingProfile :=
  match c.val.scope with
  | .project => projectProfile c.val.surfaces c.val.dependencies m
  | .file _ p _ | .editor _ _ p _ => some p
  | .documentation _ => some .standardLogical

/-- A module's execution claim, derived from the claim: in a project, `projectExecution` of the
claim's surfaces and owned dependencies; in a file or editor audit, the requested one; none for
documentation. -/
def executionForModule (c : Claim) (m : Name) : Option ExecutionClaim :=
  match c.val.scope with
  | .project => projectExecution c.val.surfaces c.val.dependencies m
  | .file _ _ e | .editor _ _ _ e => some e
  | .documentation _ => none

/-- In a project claim, a module's profile is `projectProfile` of the claim's own surfaces and
owned dependencies. -/
theorem profileForModule_project {c : Claim} (h : c.val.scope = .project) (m : Name) :
    profileForModule c m = projectProfile c.val.surfaces c.val.dependencies m := by
  simp [profileForModule, h]

/-- In a project claim, a module's execution claim is `projectExecution` of the claim's own
surfaces and owned dependencies. -/
theorem executionForModule_project {c : Claim} (h : c.val.scope = .project) (m : Name) :
    executionForModule c m = projectExecution c.val.surfaces c.val.dependencies m := by
  simp [executionForModule, h]

/-- The execution claims that `declarations` request of the root `root` under the module
assignment `execution`: that of the module of each declaration named `root` or registering an
executable contract whose root is `root`, in order. -/
def rootRequestsAmong (execution : Name → Option ExecutionClaim) (declarations : Array Declaration)
    (root : Name) : Array ExecutionClaim :=
  (declarations.filter (fun d => d.name == root ||
    d.executableContract.any (fun contract => contract.root == root))).filterMap
      (fun d => execution d.module)

/-- A shared root must meet each requesting surface's execution obligation. The requests
come from the owned ordinary declaration or each retained executable-contract registration. -/
def rootRequests (c : Claim) (i : EnvironmentCensus) (root : Name) : Array ExecutionClaim :=
  rootRequestsAmong (executionForModule c) i.policy.declarations root

/-- Jobs use the existing stage/subject vocabulary; this pair is a projection of JobKey,
not a second identity scheme. Fixed array order supplies deterministic result slots. -/
def localStageSubjects (i : EnvironmentCensus) : Stage → Array LocalJobSubject
  | .admission => #[.scope]
  | .declarationPolicy => i.declarations.map .declaration
  | .execution => i.roots.map .root
  | .transcript => (i.inspectedModules.filter (fun m =>
      i.policy.declarations.any (fun d =>
      d.module == m.name.name && decide (NeedsTranscript d.kind d.name)))).map .module
  | .history => (i.allModules.filter (fun m => i.execution.roots.any (fun r => r.boundaries.any
      (fun b => b.module == m.name.name && decide b.NeedsHistory)))).map .module
  | .origin => (i.allModules.filter (fun m => i.execution.roots.any (fun r => r.boundaries.any
      (fun b => b.module == m.name.name && decide b.ClaimsToolchain)))).map .module
  | .documentationPresence => i.inspectedModules.map .module ++
      i.materialDeclarations.map .declaration
  | _ => #[]

/-- The subjects of a stage's jobs over the whole census: the scope for a whole-run stage, each
fence for `example`, and otherwise every environment's local subjects under its request key. -/
def stageSubjects (i : Census) : Stage → Array JobSubject
  | .configuration | .discovery | .build | .documentScan | .graph => #[.scope]
  | .example => i.fences.map .fence
  | stage => i.environments.flatMap fun e =>
      (localStageSubjects e stage).map (JobSubject.environment e.request.key)

/-- Required jobs are derived from mandatory mode stages and census subjects before results. -/
def requiredJobs (c : Claim) (i : Census) : Array (Stage × JobSubject) :=
  (requiredStages c).toArray.flatMap (fun stage => (stageSubjects i stage).map (stage, ·))

/-- Every local derived job of every requested environment remains in the whole plan. -/
theorem stageSubjects_environment (i : Census) (e : EnvironmentCensus) (he : e ∈ i.environments)
    (stage : Stage) (subject : LocalJobSubject) (hs : subject ∈ localStageSubjects e stage) :
    JobSubject.environment e.request.key subject ∈ stageSubjects i stage := by
  cases stage <;> first
    | solve | simp [localStageSubjects] at hs
    | (simp only [stageSubjects, Array.mem_flatMap, Array.mem_map]
       exact ⟨e, he, subject, hs, rfl⟩)

theorem requiredJobs_environment_coverage (c : Claim) (i : Census) (h : CensusOK c i)
    (request : EnvironmentRequest) (hr : request ∈ i.requests)
    (stage : Stage) (hs : stage ∈ requiredStages c) :
    ∃ e ∈ i.environments, e.request = request ∧
      ∀ subject ∈ localStageSubjects e stage,
        (stage, JobSubject.environment request.key subject) ∈ requiredJobs c i := by
  obtain ⟨e, he, eq, _⟩ := census_requested_environment c i h request hr
  refine ⟨e, he, eq, ?_⟩
  intro subject hsubject
  have hin := stageSubjects_environment i e he stage subject hsubject
  rw [eq] at hin
  simp only [requiredJobs, Array.mem_flatMap, List.mem_toArray, Array.mem_map]
  exact ⟨stage, hs, JobSubject.environment request.key subject, hin, rfl⟩

/-- Bucket selection only: collisions are resolved by full structural stage/subject
equality, including snapshots, source bytes and every constructor field. Omitting these
fields from the hash does not omit them from the original uniqueness relation. -/
private def localJobSubjectBucket : LocalJobSubject → UInt64
  | .scope => 0
  | .module k => hash k.name.name
  | .declaration k | .root k => hash (k.moduleKey.name.name, k.name.name)
  | .boundary k => hash (k.root.name.name, k.occurrence)

private def jobSubjectBucket : JobSubject → UInt64
  | .scope => 0
  | .environment key subject => mixHash (hash key.index) (localJobSubjectBucket subject)
  | .fence k => hash (k.document.uri, k.body.start)

local instance : BEq (Stage × JobSubject) := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq (Stage × JobSubject) where
  eq_of_beq h := of_decide_eq_true h
  rfl {a} := by change decide (a = a) = true; exact decide_eq_true rfl
local instance : Hashable (Stage × JobSubject) := ⟨fun key => jobSubjectBucket key.2⟩
local instance : LawfulHashable (Stage × JobSubject) where
  hash_eq _ _ h := eq_of_beq h ▸ rfl

/-- The index decides the exact stage/subject relation required by PlanOK, not full
JobKey uniqueness (which would be weaker when claims differ). Ordered jobs are untouched. -/
theorem requiredJobs_distinct_iff (c : Claim) (i : Census) :
    (Std.ExtHashSet.ofList (requiredJobs c i).toList).size = (requiredJobs c i).toList.length ↔
      (requiredJobs c i).toList.Pairwise (· ≠ ·) :=
  distinct_iff _

/-- Concrete plan validity checks the census, derived keys, profile assignments and root
request coverage. Unknown module ownership cannot default to a permissive profile. -/
def PlanOK (c : Claim) (i : Census) : Prop :=
  c.val.snapshot.toolchain.leanVersion = Compiler.version ∧
  c.val.snapshot.toolchain.compilerCommit = Compiler.commit ∧
  CensusOK c i ∧ (requiredJobs c i).toList.Pairwise (· ≠ ·) ∧
  (∀ job ∈ requiredJobs c i, StageSubjectCompatible job.1 job.2) ∧
  (∀ e ∈ i.environments, ∀ d ∈ e.declarations,
      (profileForModule c d.moduleKey.name.name).isSome = true) ∧
  (∀ e ∈ i.environments, ∀ r ∈ e.roots, rootRequests c e r.name.name ≠ #[]) ∧
  (.execution ∈ requiredStages c → ∀ e ∈ i.environments, ∀ d ∈ e.policy.declarations,
    ∀ contract ∈ d.executableContract, contract.failure = none →
      ∃ root ∈ e.roots, root.name.name = contract.root)
set_option synthInstance.maxSize 1024 in
instance (c : Claim) (i : Census) : Decidable (PlanOK c i) := by
  letI : Decidable ((requiredJobs c i).toList.Pairwise (· ≠ ·)) :=
    decidable_of_iff _ (requiredJobs_distinct_iff c i)
  unfold PlanOK
  infer_instance

/-- The indexed implementation decides the same proposition as the prior finite scan. -/
theorem planOK_decide_eq_previous (c : Claim) (i : Census) :
    decide (PlanOK c i) = @decide (PlanOK c i) (by unfold PlanOK; infer_instance) := by
  congr

/-- An admitted transcript and valid plan share both compiler identity fields; a shared
development version string cannot connect observations from different commits. -/
theorem transcript_plan_compiler {decls : Array Declaration}
    {transcripts : Array Frontend.Transcript} {t : Frontend.Transcript} {c : Claim} {i : Census}
    (inventory : InventoryValid decls transcripts) (member : t ∈ transcripts)
    (plan : PlanOK c i) :
    t.leanVersion = c.val.snapshot.toolchain.leanVersion ∧
      t.leanGitHash = c.val.snapshot.toolchain.compilerCommit := by
  have transcript := inventory.2.2.2 t member
  exact Compiler.unique ⟨transcript.2.2.2.1, transcript.2.2.2.2.1⟩ ⟨plan.1, plan.2.1⟩

/-- The fixed JobKeys exactly realize the independently derived plan. Admission cannot
accept a caller-selected shorter list, duplicates, or another claim's keys. -/
structure Plan (c : Claim) (i : Census) where
  /-- The job keys, one per required job, in the order of `requiredJobs`. -/
  jobs : Array JobKey
  /-- Proof that the census and its derived plan satisfy `PlanOK`. -/
  valid : PlanOK c i
  /-- Proof that the jobs' stages and subjects are exactly `requiredJobs c i`, in order. -/
  exactJobs : jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i
  /-- Proof that every job key belongs to the claim `c`. -/
  exactClaim : ∀ k ∈ jobs, k.claim = c

/-- Validate the proposed keyed realization without dropping any record. -/
@[regula_decision]
def admitPlan (c : Claim) (i : Census) (jobs : Array JobKey) : Except String (Plan c i) :=
  if hp : PlanOK c i then
    if hj : jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i then
      if hc : ∀ k ∈ jobs, k.claim = c then .ok ⟨jobs, hp, hj, hc⟩
      else .error "job belongs to a different claim"
    else .error "jobs do not exactly realize the required plan"
  else .error "invalid census or plan"

theorem admitPlan_invalid_census (c : Claim) (i : Census) (jobs : Array JobKey)
    (invalid : ¬ CensusOK c i) : admitPlan c i jobs = .error "invalid census or plan" := by
  have hp : ¬ PlanOK c i := fun h => invalid h.2.2.1
  simp [admitPlan, hp]

theorem admitPlan_request_mismatch (c : Claim) (i : Census) (jobs : Array JobKey)
    (mismatch : i.environments.map (·.request) ≠ i.requests) :
    admitPlan c i jobs = .error "invalid census or plan" :=
  admitPlan_invalid_census c i jobs (fun h => mismatch h.1)

/-- Any decision of the identical plan predicate preserves every admission outcome,
including ordered realization, exact claim equality and the original refusal precedence. -/
theorem admitPlan_decision_eq (c : Claim) (i : Census) (jobs : Array JobKey)
    (decision : Decidable (PlanOK c i)) :
    admitPlan c i jobs = @dite (Except String (Plan c i)) (PlanOK c i) decision
      (fun hp =>
        if hj : jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i then
          if hc : ∀ k ∈ jobs, k.claim = c then .ok ⟨jobs, hp, hj, hc⟩
          else .error "job belongs to a different claim"
        else .error "jobs do not exactly realize the required plan")
      (fun _ => .error "invalid census or plan") := by
  by_cases hp : PlanOK c i <;> simp [admitPlan, hp]

/-- Every valid keyed realization is admitted with its exact projections. -/
theorem admitPlan_exact (c : Claim) (i : Census) (p : Plan c i) :
    admitPlan c i p.jobs = .ok p := by
  unfold admitPlan
  rw [dite_eq_left p.valid, dite_eq_left p.exactJobs, dite_eq_left p.exactClaim]
/-- Realize all independently derived jobs; mapM refuses rather than discarding an
unsupported subject. The existing plan admission checks the complete resulting array. -/
def buildPlan (c : Claim) (i : Census) : Except String (Plan c i) := do
  let jobs ← (requiredJobs c i).mapM fun (stage, subject) => admitJobKey c stage subject
  admitPlan c i jobs

/-- The jobs `admitPlan` admits for a claim and census: the census and its derived plan are
valid, and the jobs are exactly the required jobs, in order, each for this claim. These are the
proof fields of `Plan`, stated without `admitPlan`. -/
def PlanJobsOK (c : Claim) (i : Census) (jobs : Array JobKey) : Prop :=
  PlanOK c i ∧ jobs.map (fun k => (k.stage, k.subject)) = requiredJobs c i ∧
    ∀ k ∈ jobs, k.claim = c

/-- Plan admission succeeds exactly for the jobs `PlanJobsOK` admits. -/
theorem admitPlan_isOk_iff (c : Claim) (i : Census) (jobs : Array JobKey) :
    (admitPlan c i jobs).isOk = true ↔ PlanJobsOK c i jobs := by
  constructor
  · intro accepted
    cases admitted : admitPlan c i jobs with
    | ok p =>
      have same : p.jobs = jobs := by
        unfold admitPlan at admitted
        split at admitted
        · split at admitted
          · split at admitted
            · cases admitted; rfl
            · cases admitted
          · cases admitted
        · cases admitted
      exact same ▸ ⟨p.valid, p.exactJobs, p.exactClaim⟩
    | error _ => rw [admitted] at accepted; cases accepted
  · rintro ⟨valid, exact, claim⟩
    show (admitPlan c i (⟨jobs, valid, exact, claim⟩ : Plan c i).jobs).isOk = true
    rw [admitPlan_exact]
    rfl

/-- A documentation claim over one document of its snapshot, with the compiler identity of this
compiled policy: the claim of the witnesses of `checked_admitPlan`, `checked_accept` and
`checked_finalize`. -/
def witnessClaim : Claim :=
  ⟨⟨.documentation #[⟨"README.md", ""⟩], .documentationExample,
      ⟨#[⟨"README.md", ""⟩], ⟨"lakefile", ""⟩, ⟨Compiler.version, Compiler.commit, "revision"⟩,
        #[]⟩, #[], #[]⟩,
    by decide +kernel⟩

/-- The census of no environment and no fence, whose plan for `witnessClaim` is valid
(`witness_planOK`). -/
def witnessCensus : Census :=
  { requests := #[], environments := #[], modules := #[], moduleSources := #[],
    configuredTargets := #[], discoveredTargets := #[] }

/-- The required jobs of the witness claim and census: discovery, build and document scan, each
of the whole scope. -/
theorem witness_requiredJobs :
    requiredJobs witnessClaim witnessCensus =
      #[(.discovery, .scope), (.build, .scope), (.documentScan, .scope)] := by
  simp [requiredJobs, requiredStages, stageSubjects, witnessClaim, witnessCensus]

/-- The plan of the witness claim and census is valid. -/
theorem witness_planOK : PlanOK witnessClaim witnessCensus := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CensusOK, witnessCensus, witnessClaim, GraphPlanOK, UniqueNames, moduleNames]
    exact fun slot => slot.elim0
  · rw [witness_requiredJobs]; decide
  · rw [witness_requiredJobs]; decide
  · simp [witnessCensus]
  · simp [witnessCensus]
  · simp [witnessCensus]

/-- The plan of the witness claim and census: its three required jobs. -/
def witnessPlan : Plan witnessClaim witnessCensus :=
  { jobs := #[⟨witnessClaim, .discovery, .scope, by decide, trivial, trivial⟩,
      ⟨witnessClaim, .build, .scope, by decide, trivial, trivial⟩,
      ⟨witnessClaim, .documentScan, .scope, by decide, trivial, trivial⟩]
    valid := witness_planOK
    exactJobs := by rw [witness_requiredJobs]; simp
    exactClaim := by simp }

/-- The arguments of `admitPlan`, as the fields of one structure, in the order of the
arguments. -/
structure PlanInput where
  /-- The claim the plan serves. -/
  claim : Claim
  /-- The census the plan is derived from. -/
  census : Census
  /-- The proposed job keys. -/
  jobs : Array JobKey

/-- `admitPlan` accepts exactly the jobs `PlanJobsOK` admits (`admitPlan_isOk_iff`): for the
witness claim and census it accepts the three required jobs and refuses no jobs. The result type
depends on the claim and the census, so the decision is of whether the result is a success
(`Regula.Dependent.isOk`), on the structure of the three arguments; that the admitted plan has
the supplied jobs is `admitPlan_exact`. -/
theorem checked_admitPlan : Regula.ExecutableContract admitPlan (fun admit =>
    Regula.Decides (· = true)
      (fun input : PlanInput => PlanJobsOK input.claim input.census input.jobs)
      (Regula.Dependent.isOk fun input => admit input.claim input.census input.jobs)) :=
  ⟨.of_iff (fun input => admitPlan_isOk_iff input.claim input.census input.jobs)
    ⟨⟨witnessClaim, witnessCensus, witnessPlan.jobs⟩,
      (admitPlan_isOk_iff witnessClaim witnessCensus witnessPlan.jobs).mpr
        ⟨witness_planOK, witnessPlan.exactJobs, witnessPlan.exactClaim⟩⟩
    ⟨⟨witnessClaim, witnessCensus, #[]⟩, fun accepted => by
      have exact := ((admitPlan_isOk_iff witnessClaim witnessCensus #[]).mp accepted).2.1
      rw [witness_requiredJobs] at exact
      simp at exact⟩⟩

end RegulaPolicy
